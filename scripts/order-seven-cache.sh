#!/usr/bin/env bash
set -euo pipefail

usage() {
  echo "usage: $0 {probe|pull|push} SHARD" >&2
  exit 2
}

if [[ $# -ne 2 ]]; then
  usage
fi

command_name=$1
shard=$2
reference=$(python3 scripts/order_seven_cache.py reference "$shard")

case "$command_name" in
  probe)
    cache_dir=$(mktemp -d "${RUNNER_TEMP:?}/order-seven-${shard}.XXXXXX")
    trap 'rm -rf "$cache_dir"' EXIT
    manifest="$cache_dir/manifest.json"
    oras manifest fetch "$reference" > "$manifest" 2>/dev/null
    python3 scripts/order_seven_cache.py layers "$shard" "$manifest" >/dev/null
    ;;
  pull)
    cache_dir=$(mktemp -d "${RUNNER_TEMP:?}/order-seven-${shard}.XXXXXX")
    trap 'rm -rf "$cache_dir"' EXIT
    manifest="$cache_dir/manifest.json"
    staging_root="$cache_dir/staging"
    mkdir "$staging_root"
    if ! oras manifest fetch "$reference" > "$manifest" 2>/dev/null; then
      exit 1
    fi
    repository=${reference%:*}
    fetch_layers() {
      while IFS= read -r digest_value; do
        oras blob fetch --output - "$repository@$digest_value"
      done < <(python3 scripts/order_seven_cache.py layers "$shard" "$manifest")
    }
    fetch_layers \
      | zstd --decompress --stdout \
      | tar --extract --file - --directory "$staging_root" \
          --no-same-owner --no-same-permissions
    python3 scripts/order_seven_cache.py install "$shard" "$staging_root"
    python3 scripts/order_seven_cache.py paths "$shard" >/dev/null
    ;;
  push)
    cache_dir=$(mktemp -d "${RUNNER_TEMP:?}/order-seven-${shard}.XXXXXX")
    trap 'rm -rf "$cache_dir"' EXIT
    manifest="$cache_dir/${shard}.paths"
    python3 scripts/order_seven_cache.py paths "$shard" > "$manifest"
    # GHCR limits each layer to 10 GB and each layer upload to ten minutes.
    # Stream fixed 512 MiB pieces so every upload stays comfortably bounded
    # without materializing a second full archive on the runner.
    tar --create --file - --files-from "$manifest" --hard-dereference \
        --sort=name --mtime='UTC 1970-01-01' --owner=0 --group=0 --numeric-owner \
      | zstd --compress --stdout -3 \
      | split --bytes=512M --numeric-suffixes=0 --suffix-length=4 - \
          "$cache_dir/${shard}.tar.zst.part-"
    (
      cd "$cache_dir"
      layers=()
      for part in "${shard}.tar.zst.part-"*; do
        layers+=("${part}:application/vnd.mazurtheorem.lean-cache.layer.v1+zstd")
      done
      push_layers() {
        oras push "$reference" \
          --artifact-type application/vnd.mazurtheorem.lean-cache.v1 \
          --annotation \
            "org.opencontainers.image.source=${GITHUB_SERVER_URL}/${GITHUB_REPOSITORY}" \
          "${layers[@]}"
      }
      if ! push_layers; then
        echo "::warning::Retrying the interrupted Order Seven cache upload."
        push_layers
      fi
    )
    ;;
  *)
    usage
    ;;
esac

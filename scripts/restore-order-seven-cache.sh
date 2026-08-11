#!/usr/bin/env bash
set -euo pipefail

if [[ $# -gt 1 || (${1:-} != "" && ${1:-} != "--require-all") ]]; then
  echo "usage: $0 [--require-all]" >&2
  exit 2
fi

require_all=false
if [[ ${1:-} == "--require-all" ]]; then
  require_all=true
fi

failure_dir=$(mktemp -d "${RUNNER_TEMP:?}/order-seven-restore.XXXXXX")
trap 'rm -rf "$failure_dir"' EXIT
export failure_dir

restore_order_seven_shard() {
  local shard=$1
  if scripts/order-seven-cache.sh pull "$shard"; then
    echo "Restored Order Seven shard: $shard"
  else
    : > "$failure_dir/$shard"
  fi
}
export -f restore_order_seven_shard

# The shard paths are machine-checked to be disjoint. Bounded parallel pulls
# overlap registry transfer and decompression without saturating runner I/O.
python3 scripts/order_seven_cache.py lanes \
  | xargs -P "${ORDER_SEVEN_CACHE_PULL_JOBS:-3}" -n 1 \
      bash -c "restore_order_seven_shard \"\$1\"" _

mapfile -t failures < <(find "$failure_dir" -type f -maxdepth 1 -print \
  | sed 's#.*/##' | sort)
if [[ ${#failures[@]} -eq 0 ]]; then
  exit 0
fi

if [[ $require_all == true ]]; then
  printf '::error::The main cache producer did not publish shard %s.\n' \
    "${failures[@]}"
  exit 1
fi

printf '::notice::No exact Order Seven cache for %s; Lake will rebuild it.\n' \
  "${failures[@]}"

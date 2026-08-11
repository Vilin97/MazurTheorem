#!/usr/bin/env bash
set -euo pipefail

# Dependency downloads occasionally fail on hosted runners because of a
# transient Git/TLS or CDN error.  Lake's cache operation is idempotent, so a
# bounded retry resumes safely without weakening any build or proof check.
for attempt in 1 2 3; do
  if lake exe cache get; then
    exit 0
  fi
  if [[ $attempt -eq 3 ]]; then
    echo "::error::Mathlib cache installation failed after $attempt attempts."
    exit 1
  fi
  delay=$((attempt * 10))
  echo "::warning::Mathlib cache installation failed; retrying in ${delay}s."
  sleep "$delay"
done

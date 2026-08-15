# Repository instructions for coding agents

This is a public Lean 4 research formalization. Preserve mathematical
honesty, provenance, and the dependency graph.

- Never introduce `sorry`, `admit`, custom axioms, `unsafe`, `partial`,
  `native_decide`, linter suppressions, or proof-strengthening options in
  checked code.
- Unsolved open declarations belong only in registered `Challenge/` files and
  must be exactly `:= sorry`; a solved contract remains as a checked bridge.
- Do not weaken a challenge statement or edit roadmap weights to make progress
  look larger.
- Build the smallest touched module with `LEAN_NUM_THREADS=1`; do not run a
  cold whole-library or documentation build on a contributor's laptop unless
  explicitly requested.
- Use `python3 scripts/quality.py` before handoff.
- Do not mix content changes with CI/site/coordination changes unless the task
  explicitly spans them.
- Preserve the Apache-2.0 license, per-file headers, upstream attribution,
  co-author trailers, `THIRD_PARTY_NOTICES.md`, `PORTING.md`, and
  `docs/PRIOR_ART.md`.
- Tau Ceti work uses its separate exact-pin package under
  `upstream/tauceti/`; never mix its Lean/Mathlib pin into the core package.
- A new interface needs an explicit design boundary and a named downstream
  consumer.

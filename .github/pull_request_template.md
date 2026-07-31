## Scope

Describe the bounded work package and link its issue or roadmap node.

Closes #

## Mathematical and Lean changes

Name the statements, definitions, and modules changed. Explain any new interface
and identify its downstream consumer.

## Provenance

List mathematical sources and any code reused or adapted from Mathlib, Lean Pool,
Tau Ceti, FLT, or another repository. Record substantial AI assistance.

## Verification

Give the exact smallest-module build and checks run.

```text
LEAN_NUM_THREADS=1 lake build MazurTorsion.Path.To.Module
python3 scripts/quality.py
```

## Checklist

- [ ] The formal statement matches the cited mathematics.
- [ ] Checked code contains no `sorry`, `admit`, custom axioms, `unsafe`,
      `partial`, `native_decide`, linter suppression, or option backdoor.
- [ ] I built the smallest touched module with `LEAN_NUM_THREADS=1`.
- [ ] I preserved attribution, licensing, and co-author information.
- [ ] I updated the dependency metadata or blueprint if readiness changed.
- [ ] I did not change roadmap weights merely to increase reported progress.
- [ ] The change is focused; content and infrastructure are not mixed.

# Contributing

Mazur's theorem is a research formalization. Contributions are welcome at
every level, but all work must attach to an explicit roadmap node or improve
the project infrastructure.

## Before writing Lean

1. Read [`docs/CLAIMING.md`](docs/CLAIMING.md).
2. Choose a claimable node in
   [`coordination/program.json`](coordination/program.json).
3. For an `open` node, submit “Claim a work package” and wait for maintainer
   confirmation. For a `research_open` node, register a nonexclusive research
   approach; parallel teams are welcome.
4. Confirm the exact declaration, imports, downstream consumer, dependency
   pin, and license.

Do not begin a large interface behind an unreviewed API. For a
`draft_interface` or `blocked` node, open a design issue instead.

## Development setup

Install [elan](https://leanprover-community.github.io/install/) and
[uv](https://docs.astral.sh/uv/) or Python 3.13+.

```sh
lake exe cache get
python3 scripts/quality.py
LEAN_NUM_THREADS=1 lake build MazurTorsion.Path.To.TouchedModule
```

The cache requires roughly 8 GB. A complete build can use several gigabytes
of memory, so use a module target locally and leave the cold aggregate build
to CI.

## Challenge solutions

A challenge is an immutable contract. Do not weaken it and do not import a
challenge from checked implementation code.

1. Put the proof in the destination module named by the registry.
2. Replace the challenge's `sorry` with a one-line bridge to that public
   declaration.
3. Change only the node lifecycle fields allowed by the registry schema.
4. Compile the named consumer module.
5. Include the claim issue with `Closes #…`.

A solution must not introduce `sorry`, `admit`, custom axioms,
`native_decide`, `unsafe`, `partial`, linter suppressions, or proof-strengthening
options. `#print axioms` must report no axioms outside `propext`,
`Quot.sound`, and `Classical.choice`.

## Interface and upstream work

Mathlib and Tau Ceti tasks should be developed upstream when their maintainers
agree. This repository records an exact commit and an integration adapter;
it does not maintain silent forks. Dependency updates are standalone PRs.

An interface node is complete only when:

- the definitions compile at the exact pin;
- its acceptance lemmas or sanity tests pass;
- at least one real downstream consumer uses it;
- provenance and license are recorded.

Definitions without a consumer receive at most partial readiness credit and
no theorem-completion credit.

## Pull requests

Keep PRs narrow. A challenge solution should not also reformat the site or
update CI. The PR template asks for:

- roadmap node and claim issue;
- mathematical source and provenance;
- declarations and consumer modules;
- exact tests run;
- axiom output;
- remaining assumptions or follow-up work.

CI is the minimum standard, not a substitute for mathematical review.
Maintainers may ask for API changes, a smaller dependency cone, or a more
stable proof even when the kernel accepts the term.

## Style

- Use full words in names.
- Give every Lean file the standard copyright/license/authors header.
- Write module documentation explaining the mathematical boundary.
- Prefer small public lemmas with stable statement shapes.
- Comment why a proof is organized unusually; do not narrate tactics.
- Preserve all upstream author headers and co-author trailers.

By contributing, you agree that your contribution is licensed under
Apache-2.0 and that its provenance is accurately recorded.

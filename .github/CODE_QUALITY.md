# Code quality policy

This repository combines checked Lean, immutable challenge contracts,
attributed ports, generated certificates, and public programme projections.
The trust and accounting boundaries must remain explicit.

## Source classes

- `MazurTorsion/`, `EllipticCurves/`, and their root modules are checked
  implementation and must be placeholder-free.
- `Challenge/` and `upstream/tauceti/MazurTauCetiChallenge/` contain registered
  contracts. An unsolved declaration may use exactly one whole-body
  `:= sorry`; supporting declarations may not be open. A solved contract
  remains as a checked bridge.
- `archive/drafts/` is historical text, excluded from Lake libraries,
  documentation extraction, proof claims, and progress credit.

Checked implementation must not contain `sorry`, `admit`, custom axioms,
`native_decide`, `unsafe`, `partial`, linter suppressions, or local options that
weaken checking. A proof must never import a challenge module.

## Lean interfaces and provenance

Every Lean file starts with its copyright, Apache-2.0 license, complete author
header, imports, and module docstring. Preserve upstream authorship and record
ports in `THIRD_PARTY_NOTICES.md` and `docs/PRIOR_ART.md`.

Use narrow imports. Public declarations should:

- have descriptive names in the owning namespace;
- state a stable mathematical interface rather than a proof encoding;
- expose exactly the hypotheses consumed;
- explain their mathematical role in a docstring; and
- have a named downstream consumer before receiving integrated credit.

Large generated certificates are acceptable when the mathematics is genuinely
computational. Split them at semantic boundaries, keep expensive terms out of
public theorem types, and document their source and checking strategy.
Generated volume alone is not evidence of progress.

## Kernel and build discipline

Completed declarations may depend only on `propext`, `Quot.sound`, and
`Classical.choice`. CI audits transitive axiom dependencies; source scanning is
not a substitute. The audit loads Lean's persistent transitive-axiom index at
private import level, so private declarations remain in scope without walking
every imported proof body repeatedly.

Build the smallest affected module locally with one Lean worker. A pull request
must compile both the changed declaration and its named consumer without
warnings. Full cold builds and documentation builds belong in CI. Never weaken
a check to accommodate a contribution.

## Canonical coordination data

[`coordination/program.json`](../coordination/program.json) is the sole source
of truth for stable nodes and weights, dependencies, readiness, challenge
lifecycle, schema-v4 work packages, execution selection, and release endpoints.
The canonical endpoint is the full
`MazurTorsion.rationalTorsion_hasMazurClassification` theorem;
`Challenge.Mazur.torsion_ncard_le` is its sibling challenge corollary, not a
substitute project definition.

Top-level node weights form the fixed 1,000-point programme. Work-package
weights only partition their parent node: packages award zero independent
credit and never complete a parent by status alone. The execution object has a
WIP limit of three and names one `current_work_package` in each active lane;
it need not fill that limit. Other `active` packages are ready, not selected.

A paused challenge remains immutable and compiled, but it must be unclaimable
and receive no maintainer proof volume. A lifecycle change may not weaken or
replace the published statement.

The following are projections, not canonical data:

- six generated Blueprint chapters for the top-level mathematical DAG;
- the byte-identical `site/generated/program.json` copy and site views;
- `coordination/OWNER_QUEUE.md` for current selection; and
- narrative architecture, status, progress, and claiming documents.

After an authorized ledger edit, synchronize and check the projections:

```bash
python3 scripts/sync_roadmap_docs.py
python3 scripts/sync_roadmap_docs.py --check
python3 scripts/quality.py
```

Changes to mathematical scope, stable IDs or weights, dependency pins, public
interfaces, or the release route require explicit pull-request justification.
Do not mix dependency-pin or coordination changes with unrelated proof work.

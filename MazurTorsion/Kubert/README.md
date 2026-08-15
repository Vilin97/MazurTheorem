# Kubert normal forms and fixed-order certificates

This directory contains the Tate/Kubert normal-form calculations and
fixed-order algebraic certificates already checked by the project. It is not
the canonical modular-curve layer: a point-level parametrization or polynomial
certificate does not construct a represented `X₁(N)` or `X₀(N)`, its integral
model, its Jacobian, or its Néron model.

File presence also does not mean that a roadmap node is selected. Consult the
compact [owner queue](../../coordination/OWNER_QUEUE.md), then the canonical
[`program.json`](../../coordination/program.json), before adding proof volume.
Paused contracts remain present and compiled but are not claimable.

## Start at semantic modules

Most contributors should start at one of these boundaries and follow its
imports only as needed:

| Purpose | Entry module |
|---|---|
| Tate normal form and multiples | [`TateNormalForm.lean`](TateNormalForm.lean), [`TateNormalFormMultiples.lean`](TateNormalFormMultiples.lean) |
| Three-normal-form calculations | [`ThreeNormalForm.lean`](ThreeNormalForm.lean) |
| Orders 9, 11, 13, 14, 15, 16, and 18 | the corresponding `Order*Reduction.lean`, `Order*Model.lean`, or final `Order*.lean` module at this directory level |
| Order-seven parametrization and isogeny geometry | [`OrderSevenParametrization.lean`](OrderSevenParametrization.lean), [`OrderSevenCorrespondence.lean`](OrderSevenCorrespondence.lean), [`OrderSevenIsogeny.lean`](OrderSevenIsogeny.lean) |
| Order-seven backtracking conclusion | [`OrderSevenBacktrackingResultantObstruction.lean`](OrderSevenBacktrackingResultantObstruction.lean); the semantic certificate assembly is [`OrderSevenBacktrackingResultantCertificate.lean`](OrderSevenBacktrackingResultantCertificate.lean) |
| Order-seven dual-kernel consumers | [`OrderSevenDualKernelPullback.lean`](OrderSevenDualKernelPullback.lean), [`OrderSevenIsogenyDoubling.lean`](OrderSevenIsogenyDoubling.lean) |
| Orders 21, 25, 27, and 35 | [`OrderTwentyOne.lean`](OrderTwentyOne.lean), [`OrderTwentyFive.lean`](OrderTwentyFive.lean), [`OrderTwentySeven.lean`](OrderTwentySeven.lean), [`OrderThirtyFive.lean`](OrderThirtyFive.lean) |

The generated [source exposition](https://vilin97.github.io/MazurTheorem/exposition/)
is the searchable declaration and import inventory. It is more reliable than
guessing an API from a long filename.

## Heavy certificate envelopes

At this revision, 1,306 of the directory's 1,375 Lean modules belong to two
large split envelopes:

| Envelope | Modules | Lean lines | Semantic boundary |
|---|---:|---:|---|
| top-level paths beginning `OrderSevenBacktracking` | 1,226 | 1,522,004 | `OrderSevenBacktrackingResultantCertificate` and `OrderSevenBacktrackingResultantObstruction` |
| top-level paths beginning `OrderTwentySevenLeg` | 80 | 43,457 | `OrderTwentySevenThirdLeg` and `OrderTwentySeven` |
| all other Kubert modules | 69 | 18,604 | the order-specific modules listed above |

These labels describe dependency and build topology. They do not assert that
every file was produced by a generator, nor do they change copyright or
authorship. Exact mathematical provenance belongs in
[`docs/PRIOR_ART.md`](../../docs/PRIOR_ART.md); adapted-source provenance
belongs in [`PORTING.md`](../../PORTING.md) and
[`THIRD_PARTY_NOTICES.md`](../../THIRD_PARTY_NOTICES.md).

The small files below certificate subdirectories are kernel-checked source,
but they are normally implementation leaves rather than APIs. Compatibility
umbrellas collect those leaves so consumers need not depend on the physical
split. Avoid importing a `Coefficients*`, `Rows*`, `Bands*`, `Part*`, or
`Steps*` leaf from unrelated code.

## Build discipline

Build the smallest edited leaf with one Lean worker, then the semantic
consumer:

```sh
LEAN_NUM_THREADS=1 lake build MazurTorsion.Kubert.Path.To.EditedLeaf
LEAN_NUM_THREADS=1 lake build MazurTorsion.Kubert.SemanticConsumer
```

Do not use `lake build MazurTorsion` merely to check a Kubert edit. The
order-seven artifact partition is defined by
[`scripts/order_seven_cache.py`](../../scripts/order_seven_cache.py), and the
order-twenty-seven CI stages are listed in
[`scripts/build-order-twenty-seven-stages.sh`](../../scripts/build-order-twenty-seven-stages.sh).
“Cache-owned” means that those manifests assign compiled artifacts to a build
lane; it does not mean that CI owns the source or its mathematical interface.
Moving or renaming a heavy leaf therefore requires an explicit import-graph
and cache-manifest review, not a directory-only refactor.

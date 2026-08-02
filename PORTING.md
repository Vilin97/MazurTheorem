# Exact-pin ports

## Elliptic-curve reduction

## Provenance and license

The 29 retained implementation files identified as “upstream” below are derived from Michael Stoll’s
[`EllipticCurves`](https://github.com/MichaelStollBayreuth/EllipticCurves) repository at the
immutable commit
`3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f`.

That work is licensed under Apache License 2.0. The unmodified upstream `LICENSE` is retained at
the package root and must accompany any distribution of the port. The historical
`EllipticCurves.VariableChange` module is a compatibility import of the pre-existing port
of the same pinned upstream file, avoiding duplicate declarations in the shared namespace. No
source from another elliptic-curve repository is included in this port. The exceptional-cubic
harness `EllipticCurves/Examples/ExceptionalCubicReduction.lean` is a new, separable integration
test.

The compatibility target is exactly:

- Lean `4.33.0-rc1`;
- mathlib tag `v4.33.0-rc1`, resolved by the manifest to
  `79d0395a1825a6264ad5d269e35e60537518955e`.

## Source-to-destination manifest

In this standalone repository, upstream modules retain their module names and
live under `EllipticCurves/`. “Modified” means changed only for the exact-pin
port as described in the next section. Older paths in the manifest retain the
historical `mazur-torsion/` prefix to document where the original port lived;
remove that prefix to obtain the current repository path.

| Upstream source at the pinned commit | Historical port destination | State |
|---|---|---|
| `EllipticCurves/IntegralModel.lean` | `mazur-torsion/EllipticCurves/IntegralModel.lean` | modified |
| `EllipticCurves/Mathlib/AdicCompletionExtension.lean` | `mazur-torsion/EllipticCurves/Mathlib/AdicCompletionExtension.lean` | modified |
| `EllipticCurves/Mathlib/AdicFormalGroupLog.lean` | `mazur-torsion/EllipticCurves/Mathlib/AdicFormalGroupLog.lean` | unchanged |
| `EllipticCurves/Mathlib/AdicValuation.lean` | `mazur-torsion/EllipticCurves/Mathlib/AdicValuation.lean` | unchanged |
| `EllipticCurves/Mathlib/Basic.lean` | `mazur-torsion/EllipticCurves/Mathlib/Basic.lean` | modified |
| `EllipticCurves/Mathlib/Chabauty/AdicTopology.lean` | `mazur-torsion/EllipticCurves/Mathlib/Chabauty/AdicTopology.lean` | unchanged |
| `EllipticCurves/Mathlib/Chabauty/ExpConverge.lean` | `mazur-torsion/EllipticCurves/Mathlib/Chabauty/ExpConverge.lean` | unchanged |
| `EllipticCurves/Mathlib/Chabauty/FormalGroupLaw.lean` | `mazur-torsion/EllipticCurves/Mathlib/Chabauty/FormalGroupLaw.lean` | unchanged |
| `EllipticCurves/Mathlib/Chabauty/FormalGroupLaw/Basic.lean` | `mazur-torsion/EllipticCurves/Mathlib/Chabauty/FormalGroupLaw/Basic.lean` | unchanged |
| `EllipticCurves/Mathlib/Chabauty/FormalGroupLaw/Invariance.lean` | `mazur-torsion/EllipticCurves/Mathlib/Chabauty/FormalGroupLaw/Invariance.lean` | modified |
| `EllipticCurves/Mathlib/Chabauty/FormalGroupLaw/Log.lean` | `mazur-torsion/EllipticCurves/Mathlib/Chabauty/FormalGroupLaw/Log.lean` | unchanged |
| `EllipticCurves/Mathlib/Chabauty/FormalGroupLaw/Points.lean` | `mazur-torsion/EllipticCurves/Mathlib/Chabauty/FormalGroupLaw/Points.lean` | unchanged |
| `EllipticCurves/Mathlib/Chabauty/LocalRing.lean` | `mazur-torsion/EllipticCurves/Mathlib/Chabauty/LocalRing.lean` | unchanged |
| `EllipticCurves/Mathlib/Chabauty/LogIso.lean` | `mazur-torsion/EllipticCurves/Mathlib/Chabauty/LogIso.lean` | modified |
| `EllipticCurves/Mathlib/Chabauty/MvPSeries.lean` | `mazur-torsion/EllipticCurves/Mathlib/Chabauty/MvPSeries.lean` | modified |
| `EllipticCurves/Mathlib/Chabauty/MvPowerSeriesComp.lean` | `mazur-torsion/EllipticCurves/Mathlib/Chabauty/MvPowerSeriesComp.lean` | unchanged |
| `EllipticCurves/Mathlib/Chabauty/MvPowerSeriesPDeriv.lean` | `mazur-torsion/EllipticCurves/Mathlib/Chabauty/MvPowerSeriesPDeriv.lean` | modified |
| `EllipticCurves/Mathlib/Chabauty/PSeries.lean` | `mazur-torsion/EllipticCurves/Mathlib/Chabauty/PSeries.lean` | unchanged |
| `EllipticCurves/Mathlib/Chabauty/PadicInt.lean` | `mazur-torsion/EllipticCurves/Mathlib/Chabauty/PadicInt.lean` | unchanged |
| `EllipticCurves/Mathlib/Chabauty/PadicValNat.lean` | `mazur-torsion/EllipticCurves/Mathlib/Chabauty/PadicValNat.lean` | unchanged |
| `EllipticCurves/Mathlib/EllipticCurvePoint.lean` | `mazur-torsion/EllipticCurves/Mathlib/EllipticCurvePoint.lean` | modified |
| `EllipticCurves/ReductionAtPrime.lean` | `mazur-torsion/EllipticCurves/ReductionAtPrime.lean` | modified |
| `EllipticCurves/VariableChange.lean` | `mazur-torsion/EllipticCurves/VariableChange.lean` | compatibility import |
| `EllipticCurves/WeierstrassFormalGroup/Chord.lean` | `mazur-torsion/EllipticCurves/WeierstrassFormalGroup/Chord.lean` | modified |
| `EllipticCurves/WeierstrassFormalGroup/Eval.lean` | `mazur-torsion/EllipticCurves/WeierstrassFormalGroup/Eval.lean` | unchanged |
| `EllipticCurves/WeierstrassFormalGroup/Filtration.lean` | `mazur-torsion/EllipticCurves/WeierstrassFormalGroup/Filtration.lean` | modified |
| `EllipticCurves/WeierstrassFormalGroup/Foundations.lean` | `mazur-torsion/EllipticCurves/WeierstrassFormalGroup/Foundations.lean` | modified |
| `EllipticCurves/WeierstrassFormalGroup/GroupLaw.lean` | `mazur-torsion/EllipticCurves/WeierstrassFormalGroup/GroupLaw.lean` | modified |
| `EllipticCurves/WeierstrassFormalGroup/Reduction.lean` | `mazur-torsion/EllipticCurves/WeierstrassFormalGroup/Reduction.lean` | modified |
| `EllipticCurves/WeierstrassFormalGroup/ThirdPoint.lean` | `mazur-torsion/EllipticCurves/WeierstrassFormalGroup/ThirdPoint.lean` | unchanged |
| new `EllipticCurves/Examples/ExceptionalCubicReduction.lean` | `mazur-torsion/EllipticCurves/Examples/ExceptionalCubicReduction.lean` | new harness |

The new harness is deliberately self-contained. The project-level bridge
`MazurTorsion/NumberTheory/ExceptionalCubicReduction.lean`, outside this 31-file cone, identifies
its model with `MazurTorsion.ExceptionalCubic.curve.toAffine` and supplies
`MazurTorsion.ExceptionalCubic.point_finite` to its final cardinality theorem.

## Exact-pin modifications

- `Mathlib/AdicCompletionExtension.lean`: retained lines 1–384 of the upstream mathematical
  source (369 lines after updating the now-accurate module documentation); removed the unused
  completion-extension tail, which belongs to the Selmer cone rather than reduction.
- `IntegralModel.lean:94–106`: used `change` for five intended goal conversions, as required by
  the exact-pin standard style linter.
- `Mathlib/Basic.lean`: selected the current `ramificationIdx'` API, made the
  valuation-quotient rewrite transparent with `erw`, and transported integral-basis
  coordinates through an explicit ring-of-integers element; the earlier `omit`-binder and
  goal-conversion cleanups remain in place.
- `Mathlib/Chabauty/FormalGroupLaw/Invariance.lean:65–86`: supplied the missing
  zero-family substitution identity from coefficient extensionality.
- `Mathlib/Chabauty/LogIso.lean:72–523`: replaced linter-option wrappers with explicit
  `omit` binders; weakened two proof-only `Fintype` assumptions to `Finite` and constructed
  `Fintype.ofFinite` locally; made proof-local decidable equality classical; removed a simp
  lemma that became redundant at 4.33.
- `Mathlib/Chabauty/MvPSeries.lean:239`: used the 4.33 namespace
  `Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd`.
- `Mathlib/Chabauty/MvPowerSeriesPDeriv.lean:114–140`: proved the coefficient formula for
  multivariate polynomial partial derivatives, absent at this pin.
- `Mathlib/EllipticCurvePoint.lean:51–108`: moved the narrow curve-equality and field
  base-change point-map API out of the unrelated Selmer module and exposed an explicit
  nonsingularity transport to the canonical base-changed affine curve.
- `ReductionAtPrime.lean:10–11,246–297,395–458`: replaced the transitive Selmer import with the
  narrow point helper; split one expensive residue-compatibility proof into three lemmas so it
  elaborates within default heartbeat limits; removed two proof-only residue-field
  `DecidableEq` assumptions.
- `VariableChange.lean`: replaced the duplicate implementation with a public compatibility
  import of `MazurTorsion.EllipticCurve.VariableChange`, which is already the same pinned Stoll
  port and exports the required `Point.equivVariableChange` API.
- `WeierstrassFormalGroup/Chord.lean:590–638`: supplied the missing zero-family substitution
  lemma.
- `WeierstrassFormalGroup/Foundations.lean`: made quotient-map arguments and subtype
  coercions explicit, avoiding a default typeclass-search timeout; named a proof-local formal
  point so 4.33 can see the parameter equality without relying on reducibility.
- `WeierstrassFormalGroup/GroupLaw.lean:53–54,412–742`: removed the recursion-depth wrapper;
  the proof builds at default limits after using the compatibility substitution lemma.
- `WeierstrassFormalGroup/Filtration.lean`: used `change` for an intended goal conversion,
  made a proof-only field `DecidableEq` classical, and named a formal point plus its parameter
  equality for the stricter 4.33 elaborator.
- `WeierstrassFormalGroup/Reduction.lean`: applied the exact-pin notation whitespace, removed
  two proof-only residue-field `DecidableEq` assumptions, and now transports valuation bounds
  explicitly through `mem_adicCompletionIntegers` where 4.33 no longer unfolds the subtype
  membership automatically.
- `Examples/ExceptionalCubicReduction.lean`: rewrote the integer-quotient algebra equivalence
  proof using `Int.quotientSpanNatEquivZMod_comp_Quotient_mk`, the supported 4.33 API.

The 4.33 migration also touched downstream project files outside the 31-file reduction cone:
`Foundations/NaiveHeightDescent.lean` now reuses Mathlib's upstream `Point.sym2x` API and supplies
the new `Filter.TendstoCofinite` instance expected by `Northcott.comp_of_finite_fibers`; the five
`XOne*Reduction`/`XZero*Reduction` modules with integer-quotient maps use the same supported
`Int.quotientSpanNatEquivZMod_comp_Quotient_mk` proof as the harness.

No proof-strengthening option is used.

## Mathlib Dedekind-zeta finite-fibre adaptation

`MazurTorsion/NumberTheory/WeakChebotarev.lean` adapts the finite-fibre
counting rewrite in Xavier Roblot's Apache-2.0
`Mathlib/NumberTheory/NumberField/DedekindZeta.lean` at the exact pinned
Mathlib commit `79d0395a1825a6264ad5d269e35e60537518955e`. The file retains
the upstream copyright and author credit. Its norm-product ideal embedding,
zeta-square domination, and nonsplitting theorem are new local work.

## AINTLIB geometry substrate

Three file-level Apache-2.0 modules were selected from the AINTLIB
`dev/modular-curves` snapshot at
`7ecbba9dbb7fee076a1b77a6cd516fc6de46d684` and placed below
`MazurTorsion/Upstream/AINTLIB/`:

| Upstream source below `projects/ModularCurves/ModularCurves/` | Local destination |
|---|---|
| `ForMathlib/CartierDual.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/CartierDual.lean` |
| `ForMathlib/SheafOfModulesMonoidal.lean` | `MazurTorsion/Upstream/AINTLIB/ForMathlib/SheafOfModulesMonoidal.lean` |
| `Picard/Pic.lean` | `MazurTorsion/Upstream/AINTLIB/Picard/Pic.lean` |

Each file retains Chris Birkbeck's copyright, authorship, and Apache-2.0
header. The port preserves declarations and namespaces. Local changes are
limited to repointing the one internal import, removing source-level
`set_option` commands, replacing linter-reported goal conversions with
`change`, explicitly omitting unused section variables, and using `erw` at
one semireducible sheaf-map rewrite required by the immutable Mathlib pin.

The larger relative-Picard cone was tested but not retained: at this pin its
essential elaboration depends on source-level backward-compatibility options,
which this repository forbids. `MuN.lean` was also not copied because the
audited file lacks an explicit license header. Files with placeholders or an
unclean transitive cone remain prior art only. This is why AINTLIB is a
selective attributed port rather than a Lake dependency.

`MazurTorsion.Upstream.Geometry` is the reviewed boundary and
`MazurTorsion.lean` is its named checked consumer. It also imports Tau Ceti's
line-bundle and Abel--Jacobi layers from the root package's exact dependency.

## AINTLIB Hilbert 92 and Hilbert 94

Six Apache-2.0 modules were selected from AINTLIB's `main` snapshot at
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b` and placed below
`MazurTorsion/Upstream/AINTLIB/FltRegular/NumberTheory/`:

| Upstream source below `projects/FltRegular/FltRegular/NumberTheory/` | Local destination |
|---|---|
| `CyclotomicRing.lean` | `CyclotomicRing.lean` |
| `SystemOfUnits.lean` | `SystemOfUnits.lean` |
| `Hilbert92.lean` | `Hilbert92.lean` |
| `Unramified.lean` | `Unramified.lean` |
| the class-group power lemma from `RegularPrimes.lean` | `RegularPrimes.lean` |
| `Hilbert94.lean` | `Hilbert94.lean` |

The 1,499-line local cone adds attribution headers naming Chris Birkbeck,
based on the upstream authorship/history and repository-wide Apache-2.0
license; the selected upstream files themselves had no per-file headers. It
proves the generic theorem that an unramified cyclic number-field extension
of odd prime degree has degree dividing the base class number. The source used
Lean `v4.33.0-rc1` and Mathlib commit
`3edb3c0658f69f197b1e501b1f7623f3f7b3898c`; the local port compiles against
the immutable Mazur Mathlib commit
`79d0395a1825a6264ad5d269e35e60537518955e`.

The port removes every source-level transparency option. Pure type aliases
for relative units are `abbrev`s locally, quotient finiteness and finrank
comparisons are supplied through explicit quotient maps and equalities, and
the system-of-units argument uses an explicit restrict-scalars linear
equivalence. The cyclotomic-integer module uses the equivalent theorem names
available at the older pin. `RegularPrimes.lean` is intentionally pruned to
the one class-group lemma used by Hilbert 94. Because the pinned Mathlib
cohomological Hilbert-90 endpoint fixes its extension field in `Type`, the
local `Hilbert94.lean` adds an option-free `Shrink` transfer for finite
extensions. Thus the checked Hilbert-94 theorem remains universe-polymorphic
in the extension field over its small number-field base. No theorem statement
is weakened. That file also names Vasily Ilin for this local universe-polymorphic
adaptation.

`MazurTorsion.NumberTheory.CyclotomicHilbert94` is the reviewed specialization
boundary. It proves only that an everywhere finite-place unramified
`InverseExtension` forces `p` to divide the full cyclotomic class number.
`MazurTorsion.PrimeOrder.CyclotomicObstruction` is its named downstream
consumer. This result is explicitly non-equivariant: it does not select the
inverse-character class-group component and therefore does not replace the
remaining reciprocity/reflection theorem.

The checked target is:

```text
LEAN_NUM_THREADS=1 lake build MazurTorsion.NumberTheory.CyclotomicHilbert94
```

`#print axioms dvd_card_classGroup_of_unramified_isCyclic` reports exactly
`[propext, Classical.choice, Quot.sound]`.

## Build and audit

From this standalone package:

```text
lake build EllipticCurves.ReductionAtPrime EllipticCurves.Mathlib.EllipticCurvePoint
lake build EllipticCurves.Examples.ExceptionalCubicReduction
lake build
```

For aggregate integration, the package has a local `lean_lib` named `EllipticCurves` with globs
`["EllipticCurves", "EllipticCurves.+"]`; the existing `MazurTorsion` library imports these modules without
introducing a second mathlib version.

The selected production cone is 31 Lean files and 14,142 lines. On the current pin,
`MazurTorsion.Arithmetic.CardinalityReduction` builds successfully across 8,713 jobs and the
standalone challenge library builds successfully across 8,725 jobs.

A source scan of the 31 files has no proof placeholders, no option-setting command, no
native evaluator invocation, and no custom logical declaration. `#print axioms` reports exactly
`[propext, Classical.choice, Quot.sound]` for the reduction kernel theorem, `redHom`, the
finite-field count, torsion injectivity, finite-group injectivity, and the final cardinal bound.

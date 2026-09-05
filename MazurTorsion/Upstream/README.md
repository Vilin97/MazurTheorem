# Reviewed ports and integration adapters

This directory is the boundary between project code and selected external
developments. It is intentionally not a vendor dump. At this revision its 173
Lean modules divide into three layout groups:

| Tree | Modules | Meaning |
|---|---:|---|
| [`AINTLIB/`](AINTLIB/) | 101 | reviewed exact-pin ports and narrow adaptations: 91 `ForMathlib`, four `Picard`, and six `FltRegular` modules |
| [`LeanPool/`](LeanPool/) | 15 | the attributed Grothendieck-vanishing cone migrated to the project pin |
| files directly in `Upstream/` | 57 | project-facing adapters, comparisons, consumers, and semantic facades over selected upstream APIs |

Directory placement records dependency direction, not authorship. Neither a
top-level path nor an AINTLIB path by itself determines whether a file is an
original adapter, a close port, or a narrow adaptation. An AINTLIB path is not
necessarily a byte-for-byte copy. [`PORTING.md`](../../PORTING.md) is the
authoritative source-to-destination and modification manifest;
[`THIRD_PARTY_NOTICES.md`](../../THIRD_PARTY_NOTICES.md) records license and
attribution evidence; [`docs/PRIOR_ART.md`](../../docs/PRIOR_ART.md) records
material that was studied but not admitted to the dependency graph.

## Semantic entry modules

Downstream project code should prefer the narrowest applicable boundary:

| Boundary | Role |
|---|---|
| [`Geometry.lean`](Geometry.lean) | broad checked divisor, line-bundle, Picard, and curve-cohomology integration boundary |
| [`SchemeModuleCohomologyHZero.lean`](SchemeModuleCohomologyHZero.lean) | canonical global-functions action and genuine degree-zero sheaf cohomology |
| [`SchemeModuleBaseCechHOneComparison.lean`](SchemeModuleBaseCechHOneComparison.lean) | native Čech-to-genuine-sheaf `H¹` comparison |
| [`SchemeModuleBaseCechHOneModule.lean`](SchemeModuleBaseCechHOneModule.lean) | explicit global-functions-linear `H¹` comparison |
| [`ProjectiveLineCechHOneFinite.lean`](ProjectiveLineCechHOneFinite.lean) | finite-dimensional two-chart `H¹` calculation on the projective line |
| [`ProperCurveCohomologyFinite.lean`](ProperCurveCohomologyFinite.lean) | canonical field-linear exact-sequence transfers and pointed smooth-proper-curve finite-dimensional `H¹` |
| [`SchemeModuleComparisonSupportEpi.lean`](SchemeModuleComparisonSupportEpi.lean) | strict cokernel-support drop and dense-open source-support propagation for restricted epimorphisms |
| [`ProperHZeroFinite.lean`](ProperHZeroFinite.lean) | proper degree-zero finiteness for finite free sheaves and their subobjects |
| [`SchemeModuleAffineOpenPresentation.lean`](SchemeModuleAffineOpenPresentation.lean) | coherent pullback presentations from finite generators on an affine open, monic toward a finite free sheaf and epic toward the target locally |
| [`SchemeModuleAffinePullbackSections.lean`](SchemeModuleAffinePullbackSections.lean) | canonical affine Cartesian pullback on quasicoherent sections as extension of scalars; consumed termwise by the Cech base-change layer |
| [`SchemeModuleBaseChangeCech.lean`](SchemeModuleBaseChangeCech.lean) | termwise Cartesian base-Cech map, scalar-extended complex and homology isomorphisms, and genuine `H⁰`/`H¹` field-extension base change from a supplied finite affine cover |
| [`ProperCurveFiniteSupportCech.lean`](ProperCurveFiniteSupportCech.lean) | strict-support transfers and unconditional canonical `H⁰` finite-dimensionality for coherent modules on pointed proper curves |
| [`CurveCohomologyGrothendieckVanishing.lean`](CurveCohomologyGrothendieckVanishing.lean) | curve specialization of the retained LeanPool vanishing theorem |

Import a file below `AINTLIB/` or `LeanPool/` directly only when extending or
auditing that retained interface. Ordinary theorem development should consume
one of the project-facing boundaries above, or the narrower module that owns
the exact declaration. The generated
[source exposition](https://vilin97.github.io/MazurTheorem/exposition/) maps
declarations and import edges; `MazurTorsion.lean` is a whole-library audit
consumer and is not a substitute for choosing a boundary.

## What the retained cones do not prove

The relative Picard presheaf under `AINTLIB/Picard/` is not a represented
degree-zero Picard scheme or a Jacobian. The cohomology ports are not a full
proper coherent-cohomology/base-change theory. The finite-group-scheme
substrate is not an integral represented modular curve. Keep those missing
canonical objects visible in interfaces and roadmap dependencies rather than
wrapping them in supplied-object assumptions.

For exact pins, admitted slices, modifications, and named consumers, read
[`docs/UPSTREAM.md`](../../docs/UPSTREAM.md) and
[`PORTING.md`](../../PORTING.md) before editing this tree.

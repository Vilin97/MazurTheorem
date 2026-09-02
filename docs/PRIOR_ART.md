# Lean prior-art audit for Mazur's torsion theorem

This audit records what was inspected, at which revision, what can be reused,
and what remains unproved. A declaration is counted as reusable only when its
dependency cone is free of unproved axioms and it is compatible with the
project's source restrictions.

## 1. Lean Pool challenge and project target

Lean Pool publishes the numerical `ncard ≤ 16` contract below. This project
keeps that statement as an immutable release endpoint, but its canonical goal
is the stronger group-structure theorem
`MazurTorsion.rationalTorsion_hasMazurClassification`. The distinction matters:
the challenge's `Set.ncard` expression is zero on an infinite set and therefore
does not by itself assert rational-torsion finiteness or an isomorphism with one
of Mazur's fifteen groups.

The upstream repository was inspected at
[`c2223fd6be2a245929bf777c01df1577f724d3f3`](https://github.com/Vilin97/lean-pool/commit/c2223fd6be2a245929bf777c01df1577f724d3f3).
The exact challenge is
[`Challenge/Mazur.lean`](https://github.com/Vilin97/lean-pool/blob/main/Challenge/Mazur.lean).
It is still marked open and estimates roughly 50,000 lines.

The challenge pin is:

* Lean `v4.33.0-rc1`;
* mathlib tag `v4.33.0-rc1`;
* resolved mathlib commit
  `79d0395a1825a6264ad5d269e35e60537518955e`.

No `Solution/Mazur.lean` exists on upstream `main`, and a repository-wide
search found no second proof of the exact declaration.  The
[official Lean formalization leaderboard](https://lean-lang.org/eval/problems/mazur_torsion/)
also still labels the problem “Not yet solved”; its displayed candidate
contains the original placeholder rather than a proof.

The required solution theorem is:

```lean
theorem torsion_ncard_le (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (AddCommGroup.torsion (E⁄ℚ).Point :
      Set (E⁄ℚ).Point).ncard ≤ 16
```

LeanPool's solution comparator permits only the usual foundational axioms
`propext`, `Quot.sound`, and `Classical.choice`. Importing the challenge file
or hiding an assumption behind another declaration is therefore not a valid
solution.

### LeanPool Grothendieck-vanishing development

LeanPool's separate Apache-2.0 `GrothendieckVanishing` project was inspected
at source commit
[`4eef1ffb3b643d606665e3b5585aa69454e137d1`](https://github.com/Vilin97/lean-pool/commit/4eef1ffb3b643d606665e3b5585aa69454e137d1)
and at its upstream Lean 4.33 migration
[`cc54a3adb51cb00b78cbe025818a24b676aeada7`](https://github.com/Vilin97/lean-pool/commit/cc54a3adb51cb00b78cbe025818a24b676aeada7).
The source headers name Vasily Ilin and Brian Nugent. Its 15-module proof
formalizes Hartshorne III.2.7: closed-immersion cohomology, flasque
acyclicity, filtered-colimit compatibility, reduction to finitely generated
subsheaves, the irreducible positive-dimensional step, and the final
Noetherian-space induction.

All 15 modules are retained locally with their source headers. The exact-pin
port removes the upstream `implicit_reducible` commands, uses canonical
abelian images, and names opaque sheaf objects at categorical boundaries. The public
endpoint `GrothendieckVanishing` and the main intermediate declarations audit
to only `propext`, `Classical.choice`, and `Quot.sound`.

The named downstream consumer
`SchemeModuleCohomology.smoothProperCurve_H_subsingleton` applies the theorem
to the actual underlying additive sheaf of a scheme module. Tau Ceti's
codimension-one result gives the dimension bound for a smooth integral
relative curve, while smooth finite type and proper quasi-compactness give
the Noetherian hypothesis. This closes vanishing in degrees at least two.
It does not prove proper coherent cohomology finite-dimensional or finite in
degree one; those remain separate requirements of roadmap node
`MT-TC-B1-COHERENT-COHOMOLOGY`.

## 2. mathlib at the exact challenge pin

### Reusable now

| Area | File or declaration | Use |
|---|---|---|
| Affine group law | `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point` | Defines `(E⁄K).Point`, its additive commutative group structure, coordinate formulas, base-change maps, and injectivity of point maps along injective field maps. |
| Division polynomials | `EllipticCurve.DivisionPolynomial.Basic` and `.Degree` | Defines `ΨSq`, `Ψ`, `Φ`, `ψ`, and `φ`, their base-change identities, and degree/leading-coefficient/nonvanishing theorems. Useful for torsion dictionaries and root counts. |
| Reduction | `EllipticCurve.Reduction` | Supplies integral/minimal models and equation-level reduction types. It does not supply the point-specialization homomorphism required by Mazur. |
| Abstract torsion | `Mathlib.GroupTheory.Torsion` | Defines `AddCommGroup.torsion`, membership lemmas, primary components, and functoriality. |
| Finite abelian groups | `Mathlib.GroupTheory.FiniteAbelian.Basic` | `AddCommGroup.equiv_directSum_zmod_of_finite` and its variant with nontrivial cyclic factors. |
| Cardinality | `Mathlib.SetTheory.Cardinal.NatCard`, `Mathlib.Data.Set.Card` | `Nat.card_coe_set_eq`, `Nat.card_zmod`, product cardinalities, and `Set.Infinite.ncard`. |
| Polynomial roots | `Mathlib.Algebra.Polynomial.Roots` | Bounds root sets by polynomial degree; used by the imported two- and three-torsion arguments. |

### Absent at this pin

The audit found no mathlib declaration for any of the following:

* Mazur's point-order theorem or fifteen-group classification;
* a ready-made elliptic-curve theorem asserting finiteness of `E(ℚ)ₜₒᵣₛ`
  (the generic finite-torsion descent helper is available separately);
* the general theorem `#E[n](K̄)=n²`;
* a complete multiplication-by-`n`/division-polynomial torsion dictionary;
* the Weil pairing for elliptic curves;
* the rank-at-most-two theorem for finite elliptic-curve subgroups;
* the Hasse bound and point specialization in the forms needed here;
* modular curves `X₀(N)` or `X₁(N)`, their compactifications, or cusps;
* modular-curve Jacobians, Hecke operators, Eisenstein ideals or quotients;
* Néron models and the finite-flat group-scheme results used by Mazur.

Current mathlib documentation may contain later work, but this project is
deliberately evaluated against the immutable LeanPool pin.

A refresh at current mathlib commit
[`ccedd504126da4c77960a5c726b90ef554156fdd`](https://github.com/leanprover-community/mathlib4/commit/ccedd504126da4c77960a5c726b90ef554156fdd)
found no later Mazur theorem, `X₁(13)` specialization, or rational
prime-torsion classification either.

## 3. Victor Aguiar's LeanPool foundation branch

The public branch
[`vaguiarl/mazur-foundations`](https://github.com/vaguiarl/lean-pool/tree/vaguiarl/mazur-foundations/LeanPool/MazurTorsionFoundations)
was inspected at commit
[`60bec1602de9e747b67ad69641bcfb4265849123`](https://github.com/vaguiarl/lean-pool/commit/60bec1602de9e747b67ad69641bcfb4265849123).
Its five relevant commits are:

* `9241899` — elementary Mazur torsion foundations;
* `521e43c` — exclude full rational three-torsion;
* `bc22770` — exact three-torsion dictionary;
* `2790130` — bound rational three-torsion by nine;
* `60bec16` — bound four-torsion by sixteen.

The branch itself had already moved to Lean 4.33.0-rc1, but all three files
were compiled separately, unchanged, against the exact LeanPool
4.32.0-rc1/mathlib pin. They all passed.

The work was proposed as
[LeanPool PR #304](https://github.com/Vilin97/lean-pool/pull/304). It was
closed because the repository did not want partial challenge developments,
not because of a correctness failure. The PR's axiom audit found only
`propext`, `Classical.choice`, and `Quot.sound`.

The files are Apache-2.0 and carry Victor Aguiar's copyright and authorship
headers. They have been ported here with those headers intact. Besides the
namespace and destination path, the generic two-torsion file exposes
`[DecidableEq F]` rather than baking a private classical decider into its
public theorem types; the source proof is unchanged:

| Local file | Main proved declarations |
|---|---|
| `Foundations/TwoTorsion.lean` | `finite_two_torsion`, `ncard_two_torsion_le_four`, `ncard_four_torsion_le_sixteen`, `not_injective_zmod_two_cube` |
| `Foundations/ThreeTorsion.lean` | `three_nsmul_some_eq_zero_iff`, `ncard_three_torsion_le_nine`, `not_injective_zmod_three_square` |
| `Foundations/FullFourTorsion.lean` | `not_injective_zmod_four_square` |

These are genuine arithmetic results. They use affine addition and
duplication formulas, division polynomials, polynomial root counts, and
explicit rational algebra. They contain none of the prohibited source
constructs and introduce no extra axioms.

Related mathlib work is tracked in
[mathlib PR #42219](https://github.com/leanprover-community/mathlib4/pull/42219)
and PR #42160. The LeanPool branch remains the correct pinned source for this
project until such work is available at the challenge revision.

## 4. Imperial College London's FLT repository

The repository was inspected at
[`c6ed6c236fc1ddcb9b35b37a41a414637f4a895b`](https://github.com/ImperialCollegeLondon/FLT/commit/c6ed6c236fc1ddcb9b35b37a41a414637f4a895b).
It is Apache-2.0, using Lean 4.33.0-rc1 and a later mathlib pin.

The FLT project contains the exact desired mathematical statement at
[`FLT/Assumptions/Mazur.lean`](https://github.com/ImperialCollegeLondon/FLT/blob/main/FLT/Assumptions/Mazur.lean),
but it is declared as `axiom Mazur_statement`. It cannot be used as proof.

The repository does supply useful API design:

* `FLT/EllipticCurve/Torsion.lean` defines `E.nTorsion n` and a
  `ZMod n`-module instance;
* it states the desired finiteness, cardinality, and rank-two facts;
* `FLT/KnownIn1980s/EllipticCurves/PointReduction.lean` develops point
  reduction;
* neighboring files develop good-reduction infrastructure.

At the inspected revision, the general `n`-torsion finiteness/cardinality
and rank-two declarations still depend on unfinished proofs. They are useful
as interface guidance, not as dischargeable dependencies.

## 5. DE0CH/flt-lean

The active repository
[`DE0CH/flt-lean`](https://github.com/DE0CH/flt-lean)
was inspected at
[`0015a7d849cb2d7a9619e138fd75509887e79b09`](https://github.com/DE0CH/flt-lean/commit/0015a7d849cb2d7a9619e138fd75509887e79b09).
It uses Lean 4.32.0-rc1 and a nearby but newer mathlib commit
`a3364fa…`.

This is by far the largest body of directly relevant experimental work:

* `Fermat/FLT/FreyCurve/MazurTorsion.lean` is about 75,374 lines and states
  `mazur_point_order`, `torsion_finite_rat`, `mazur_classification`, and
  `mazur_torsion_bound`;
* `Fermat/FLT/EllipticCurve/TorsionCard.lean` (2,039 lines) develops the
  multiplication formulas and division-polynomial torsion dictionary;
* `TorsionCardSep.lean` (1,026 lines) proves separability and the geometric
  prime-torsion count;
* `TorsionCounting.lean` (362 lines) is a pure finite-abelian-group counting
  argument;
* `TorsionReduction.lean` (2,198 lines) develops rational-adic reduction,
  tame potentially good models, and torsion survival;
* `TateNormalForm.lean` contains extensive Kubert/Tate-normal-form work.

The important limitation is dependency closure. At this snapshot,
`MazurTorsion.lean` itself has 43 direct unfinished declarations. Its
checked-in progress tree reported 74 dependencies at an older commit, but
that tree is stale and must not be presented as a current exact count.
A current source audit still finds a large, definitely nonempty frontier:
modular compactification and cusps, Jacobians, isogenies, Néron models,
finite-flat descent, the Eisenstein quotient, inertia and semistability,
Weil pairing, CM/isogeny cases, level-125 `L`-function/Atkin--Lehner work,
and level-37 explicit geometry. Thus the named final theorems are a progress
scaffold, not a kernel-clean solution.

Representative direct frontier declarations include
`exists_eisensteinQuotientCert_of_jNeronDatum`,
`formalImmersion_of_cuspFormalImmersionCert`,
`eq_of_comp_open_x0JNeronModel`,
`exists_weilPairing_mu_nondeg_of_coprime`, `concordant_one`, and
`concordant_seventeen`.

The strongest low-level files are valuable research maps, but they are not
copied here:

* the monolithic `MazurTorsion.lean` contains 123 `set_option` commands;
  `TorsionCard.lean` contains 41 and `TorsionCardSep.lean` contains 12,
  contrary to this project's source restrictions;
* the repository had no license file at the inspected revision, so its
  original source cannot safely be redistributed;
* its mathlib pin is not identical to the challenge pin.

Mathematical ideas and dependency boundaries from this work inform the
blueprint, but any implementation here must be independently written or
come from an explicitly compatible licensed source.

That policy applies in particular to the zeta-function route to finite-prime
nonsplitting. `MazurTorsion/NumberTheory/WeakChebotarev.lean` independently
implements the ideal-pair injection and pole-order contradiction at the
project's exact pin. Its only adapted proof fragment is the finite-fibre
rewrite from Xavier Roblot's Apache-2.0 Mathlib `DedekindZeta.lean`, recorded
separately in `PORTING.md` and `THIRD_PARTY_NOTICES.md`.

Two smaller files are especially useful as designs. `TorsionCounting.lean`
has no source placeholder or option override and gives a clean
finite-abelian counting argument. `TorsionReduction.lean` likewise has no
source placeholder or option override and develops substantial tame
reduction machinery. They still lack an explicit license grant at this
snapshot, so their source is not copied.

The most concrete independently reproducible prime-order boundary is order
thirteen.  The source contains compiled algebraic declarations
`MazurX1Plane.eval_thirteen` and
`WeierstrassCurve.x1Thirteen_kubert_cleared`.  They motivate, but are not
copied into, the local definitions

\[
\begin{aligned}
G_{13}(r,s)={}&r^3+
(-s^4+5s^3-9s^2+4s-2)r^2\\
&+(-s^3+6s^2-3s+1)r-s^3
\end{aligned}
\]

under `r=b/c`, `s=c²/(b-c)`, and the genus-two model

\[
y^2=x^6+2x^5+x^4+2x^3+6x^2+4x+1.
\]

The same reconnaissance identified the useful level-21 arithmetic boundary
in `MazurLevel21.rank_zero_x0TwentyOne`: after transforming the conductor-21
curve to `W²=V(V-9)(V+7)`, its two genuine global leaves are the quartics

\[
c^2=m^4-2m^2n^2-63n^4,\qquad
c^2=-3m^4-2m^2n^2+21n^4.
\]

No comparable `X₀(21)`/21a1 development was found in the pinned mathlib,
LeanPool, AINTLIB, or Tau Ceti trees.  Because DE0CH/flt-lean has no license
grant at the inspected snapshot, no proof text or source was copied.  The
local `XZeroTwentyOneDescent.lean` rederives the model change, denominator
squareclass calculation, mod-16 eliminations, involution, and conditional
point enumeration independently; the prior tree was used only to identify
the two mathematical leaves worth isolating.

The decisive rational-point theorem is not compiled: in
`HyperellipticJacobian.lean`, `X13.two_divisible_pic` is an explicit
`sorry`, alongside fifteen further placeholders in its place/Picard,
reduction, and finite-generation cone.  Its separability, six
finite-field points at three, and cusp calculations are useful finite
certificates but do not imply the rational-point classification.

## 6. Tau Ceti

The
[`TauCetiProject/TauCeti`](https://github.com/TauCetiProject/TauCeti)
repository was inspected at base commit
[`a3913fd9111b851af857f720b4ce6721e6634183`](https://github.com/TauCetiProject/TauCeti/commit/a3913fd9111b851af857f720b4ce6721e6634183).
The exact dependency is reviewed feature commit
[`a74dfee78f800df63f085a19006f7d502eee365e`](https://github.com/Vilin97/TauCeti/commit/a74dfee78f800df63f085a19006f7d502eee365e)
on the integration fork.
It is Apache-2.0 and
contains general algebraic-geometry work,
including abelian varieties and their products, a broad Weil-divisor API,
abstract divisor class groups and `Pic⁰`, and point-level Abel-Jacobi
classes. It is pursuing a Jacobian roadmap and is the most promising shared
upstream for that part of Mazur's dependency cone.

The reviewed feature commit additionally proves finite support of the
scheme-theoretic orders of a rational function and packages them as the
permanent `SchemeWeilDivisor.orderSystem`. It also proves Krull-dimension
invariance for faithful integral extensions, tensor-product dimension
additivity via Noether normalization, the corresponding product theorem for
nonempty finite-type schemes, and
`TauCeti.AlgebraicGeometry.AbelianVariety.prod_dim`. The same reviewed
descendant extends rational functions on smooth curves to finite flat maps to
the projective line, identifies zero and infinity fibre multiplicities, and
proves `SchemeWeilDivisor.divisorProductFormula` with a checked Picard-zero
consumer. At the inspected base it
did not contain:

* elliptic-curve torsion or Weil pairings;
* modular curves or their integral models;
* the functorial Picard scheme or Jacobian variety needed for `J₀(N)`;
* Hecke/Eisenstein infrastructure;
* a product-dimension theorem for schemes or abelian varieties.

The root package now depends directly on this exact Tau Ceti feature commit, with
`MazurTorsion.Upstream.Geometry` compiling the line-bundle and Abel--Jacobi
layers as an acceptance boundary. The finite-support challenge is now a checked
thin bridge to its permanent theorem and `OrderSystem` consumer. Additivity of
abelian-variety dimension under products remains the open separately resolved
Tau Ceti contract. Larger roadmap nodes build from
Tau Ceti's existing divisor-class and Abel-Jacobi scaffolding but receive no
theorem-completion credit until their contracts are proved and consumed.

The local
`MazurTorsion/Upstream/ProjectiveLineCechHOneFinite.lean` proof reuses the
standard-chart API from this exact dependency and repeats/adapts several
private coordinate calculations from
`TauCeti/AlgebraicGeometry/ProjectiveLine/Basic.lean`. In particular, these
calculations identify the affine and inverse affine coordinates under the
two `Proj` chart isomorphisms and their overlap relation. They are recorded
locally because private upstream theorems cannot be referenced across the
package boundary. The subsequent coherent principal-parts argument, exact
two-chart Cech differential, and assembly with the separately attributed
finite-pushforward and sheaf-cohomology comparisons are local formalization
work. The finite hyperelliptic map on the projective order-thirteen curve is
now a checked consumer, both for finite generation over the global functions
of `Spec K` and, after restriction through the canonical affine-spectrum
isomorphism, for finite dimensionality over `K`.

Its present value is therefore both concrete and prospective: it supplies
usable lower layers, but it does not yet discharge a finite-order obstruction
or the prime-level argument.

## 7. Michael Stoll's elliptic-curves project

The Apache-2.0 repository
[`MichaelStollBayreuth/EllipticCurves`](https://github.com/MichaelStollBayreuth/EllipticCurves)
was inspected at
[`3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f`](https://github.com/MichaelStollBayreuth/EllipticCurves/commit/3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f).
It uses Lean 4.32.1 and a later mathlib commit, and its checked-in
development is sorry-free. This is the strongest newly discovered licensed
source for several dependencies adjacent to the Mazur proof:

* `MordellWeil.lean` proves
  `WeierstrassCurve.Affine.fg_point_of_numberField` and
  `finite_torsion`;
* `VariableChange.lean` gives the additive equivalence on point groups
  induced by a Weierstrass variable change;
* `WeierstrassFormalGroup/Reduction.lean` and `ReductionAtPrime.lean`
  construct the point reduction homomorphism and prove torsion injection,
  preservation of torsion order, and finite-field point-count divisibility;
* `WeakMordellWeil.lean` proves finiteness of
  `E(K)/2E(K)` through the `x-T` descent map;
* `SelmerGroup.lean` proves `card_range_μ`,
  `pow_rank_le_card_of_range_μ_le`, and
  `finite_selmerGroup₂`, together with the local image calculations needed
  for explicit rank bounds.

An isolated compatibility test replaced the repository's toolchain and
mathlib revision by the exact LeanPool pin. `SelmerGroup.lean` and
`WeakMordellWeil.lean` then compiled after only two mechanical rewrites
around the renamed ramification-index API. The remaining source-level import
gap is explicit: the old `sym2x` declaration now comes from
`Affine/AddSubMap.lean`. At the current exact pin, Mathlib does provide
`AddCommGroup.finite_torsion_of_descent'`; the earlier claim that this helper
was absent was stale.

The rational specialization is completed locally.
`NumberTheory/RatNorthcott.lean` supplies Northcott's property for rational
logarithmic height, while `Foundations/NaiveHeightDescent.lean` supplies the
approximate parallelogram law. Together with Mathlib's descent helper these
now prove `MazurTorsion.rationalTorsion_finite` directly, without weak
Mordell--Weil, finite index of doubling, or finite generation. The same height
file also turns finite index of doubling or tripling into finite generation for
the separate rank calculations. The pure finitely-generated-group formula
from Stoll's `Mathlib/SelmerGroup.lean`,

\[
[G:nG]=n^{\operatorname{rank}G}\#G[n],
\]

is separately ported as `GroupTheory/IndexNSmulFG.lean`. Both ports compile
at the challenge pin and their public endpoints depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

For the `X₁(18)` lane, two further slices are now retained at the same
immutable commit. `EllipticCurves/X18WeakMordellWeil.lean` stops honestly
after Step 6: it proves the `x-T` map is a homomorphism, identifies its kernel
with doubling, and puts its image in the explicit Selmer group. It does not
import or claim the generic Step-7 finiteness theorem.
`EllipticCurves/X18SelmerLocal.lean` retains only base change and the
finite-place local-image cardinality calculation from upstream
`SelmerGroup.lean`. The remaining class-number, square-class, and
dyadic-intersection facts for the concrete degree-nine algebra are required
as kernel-checked X18 certificates downstream.

Together with the local explicit two-descent, these ports now prove rank
zero and finiteness for the selected `X₀(24)` cubic.  A provenance-marked,
31-file dependency cone from Stoll's reduction stack has now also been
ported under `EllipticCurves/` at the exact challenge pin.  Its specialized
integration harness proves good reduction at `p=5`, injectivity on rational
torsion, a reduced point count of eight, and—after importing the local
finiteness theorem—`#E(ℚ)≤8`.  The pre-existing local variable-change
module and Stoll's version exported the same public declarations, so the
vendored module is deliberately a compatibility re-export rather than a
second copy.

A controlled Lake experiment also established an important reproducibility
constraint. Adding commit `3f8c39c` directly caused the dependency to
upgrade the entire test workspace to Lean 4.32.1 while root mathlib remained
at 4.32.0-rc1, after which the cache step failed for the mixed toolchains.
Moreover, the current reduction source uses post-pin ramification-index
names. Therefore the repository cannot be imported raw. The selected route
is an exact-pin compatibility port with the unnecessarily broad
`SelmerGroup` import removed, not a silent toolchain upgrade.

## 8. Dormant division-polynomial scalar-multiplication branch

The dormant mathlib branch `DivisionPolynomial_smul` was inspected at
[`3d6da3dc779ad9a87bb94300bdc06f793e122d4e`](https://github.com/leanprover-community/mathlib4/commit/3d6da3dc779ad9a87bb94300bdc06f793e122d4e).
Its Apache-2.0 file
[`DivisionPolynomial/ZSMul.lean`](https://github.com/leanprover-community/mathlib4/blob/3d6da3dc779ad9a87bb94300bdc06f793e122d4e/Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/ZSMul.lean),
authored by Junyan Xu, proves

```lean
WeierstrassCurve.zsmul_eq_smulEval
```

which expresses every integer multiple of an affine point in Jacobian
coordinates using `φₙ`, `ωₙ`, and `ψₙ`. This is directly relevant to the
forward implication

```lean
n • P = 0 → Polynomial.eval P.x (W.preΨ' n) = 0
```

left open in `Foundations/OddPrimeFullTorsion.lean`.

The branch uses Lean 4.9.0-rc1 and a substantially older universal-curve
and Jacobian-coordinate stack. Its 497-line endpoint depends on the
branch's `Universal.lean`, bivariate `ω`, and APIs no longer present in the
pinned `DivisionPolynomial.Basic`; the current file explicitly leaves `ω`
as a TODO. It therefore cannot be cherry-picked.

The local project has since proved the required `n=5` and `n=7` forward
criteria independently in
`Foundations/DivisionPolynomialRootCriterion.lean`. That proof uses only
the pinned affine group law, the already licensed three-torsion tangent
identity, and finitely many low-level polynomial identities. No source was
copied from the dormant branch; its generic Jacobian approach confirmed
the overall division-polynomial architecture but is no longer a blocker.

## 9. Birkbeck--Angdinata Lutz--Nagell formalization

David Kurniadi Angdinata's 26 March 2026 talk
[*Torsion subgroups of elliptic curves in Lean*](https://multramate.github.io/talks/tsoecil.pdf)
reports a one-day formalization with Chris Birkbeck of a number-field
Lutz--Nagell theorem. A commit search located its exact public source in
[`CBirkbeck/LutzNagell`](https://github.com/CBirkbeck/LutzNagell), inspected
at
[`c58fbfabb725e156e6c74790d8e0c3c7af856cee`](https://github.com/CBirkbeck/LutzNagell/commit/c58fbfabb725e156e6c74790d8e0c3c7af856cee).
The number-field generalization first appears in commit
[`0440306cf3d6bc9a05d8a45dbfcc454bcb0e2939`](https://github.com/CBirkbeck/LutzNagell/commit/0440306cf3d6bc9a05d8a45dbfcc454bcb0e2939),
two days before the talk.

The repository uses Lean `v4.29.0-rc7` and mathlib commit
`c5edb8d3738a5abd7da7f34d5bcb27f632a1ecca`. Its checked source has no
`sorry`, `admit`, or declared axiom. The main results in
`LutzNagellTheorem/PIDMain.lean` include:

* `lutz_nagell_integrality_pid`, for a PID whose rational primes dividing
  the torsion order are squarefree;
* `lutz_nagell_number_field`, for class-number-one number fields;
* `lutz_nagell_pid_discriminant_of_torsion`;
* `lutz_nagell_cubicDisc_discriminant` and its number-field specialization,
  giving the precise cubic-discriminant divisibility when `a₁ = a₃ = 0`.

This exactly corroborates the theorem stated in the talk. It also contains
the classical `ℤ/ℚ` specialization and denominator lemmas. It is useful for
enumerating the torsion of a *fixed* integral curve once one already knows
that all its rational points are torsion. The local explicit descent now
establishes precisely that hypothesis for the selected `X₀(24)` model, so
Lutz--Nagell would be mathematically sufficient for the remaining finite
enumeration; it was not used to prove rank zero.

There are two reuse blockers. First, GitHub detects no repository license
and there is no checked-in `LICENSE` or `COPYING` file; the new
Lutz--Nagell generalization files themselves have no copyright/license
headers. Secondly, its inherited division-polynomial multiplication stack
contains several `set_option` overrides, including recursion,
heartbeat, transparency, and unsafe-reducibility overrides. Those are
forbidden in this project. The mathematical proof and theorem interfaces
are therefore retained as independent design references, not copied.

## 10. AINTLIB modular-curve and Weil-pairing work

The Lutz--Nagell development has since been incorporated into
[`CBirkbeck/AINTLIB`](https://github.com/CBirkbeck/AINTLIB), inspected at
[`7ecbba9dbb7fee076a1b77a6cd516fc6de46d684`](https://github.com/CBirkbeck/AINTLIB/commit/7ecbba9dbb7fee076a1b77a6cd516fc6de46d684)
on the `dev/modular-curves` branch. That snapshot uses Lean
`v4.33.0-rc1` and mathlib commit
`3edb3c0658f69f197b1e501b1f7623f3f7b3898c`.
The compiler therefore matches this project, but AINTLIB's mathlib pin is
266 commits newer than the immutable Mazur pin.

### Hilbert 92 and Hilbert 94

A later AINTLIB `main` snapshot at
[`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`](https://github.com/CBirkbeck/AINTLIB/commit/1c1c74664e40071c2c2165bc55ca2616a67ccd6b)
contains a complete, placeholder-free proof of
[`Hilbert92`](https://github.com/CBirkbeck/AINTLIB/blob/1c1c74664e40071c2c2165bc55ca2616a67ccd6b/projects/FltRegular/FltRegular/NumberTheory/Hilbert92.lean)
and both parts of
[`Hilbert94`](https://github.com/CBirkbeck/AINTLIB/blob/1c1c74664e40071c2c2165bc55ca2616a67ccd6b/projects/FltRegular/FltRegular/NumberTheory/Hilbert94.lean).
For an unramified cyclic extension of odd prime degree, the checked endpoint
proves that the degree divides the base class number. Its proof uses systems
of units, Hilbert 92, integral Hilbert 90, capitulation, and the relative norm
of ideals; it does not construct a Hilbert class field or an Artin map.

The minimal 1,499-line cone has now been ported under
`MazurTorsion/Upstream/AINTLIB/FltRegular/NumberTheory/` and checked at the
immutable Mazur pin without source-level options or placeholders. The
port includes an option-free `Shrink` transfer around the pinned Mathlib
Hilbert-90 universe restriction, so the extension field in the final
Hilbert-94 theorem remains universe-polymorphic over the small base. The
Mazur-facing specialization shows that an everywhere finite-place unramified
inverse extension forces `p` to divide the full class number. This is useful
class-field obstruction infrastructure, but class-number divisibility alone
does not determine the Galois-character eigenspace of the resulting class.
The inverse-character equivariance/reflection step therefore remains a
separate honest dependency.

### Cyclotomic reciprocity boundary

The same AINTLIB snapshot contains
[`oneSidedKummerPrincipalReciprocity_canonical`](https://github.com/CBirkbeck/AINTLIB/blob/7ecbba9dbb7fee076a1b77a6cd516fc6de46d684/projects/FltRegularBernoulli/BernoulliRegular/Reflection/ResidueSymbol/Furtwaengler/OneSidedKummerReciprocity.lean),
whose statement is the integral locally-primary pseudo-unit reciprocity input
isolated by the Mazur development. Its proof is still a single `sorry` leaf;
the file's subsequent principal-symbol and bad-set reductions are checked over
that leaf. Independently,
[`DE0CH/flt-lean`'s cyclic modulus-one Artin reciprocity theorem](https://github.com/DE0CH/flt-lean/blob/fe5131cab3d7109f1efb1e0772df0d89c04e3338/Fermat/FLT/NumberField/ArtinSymbol.lean)
is also an explicit `sorry` leaf after construction of the ideal Artin map.
Neither source therefore supplies an axiom-clean theorem that can be ported.

The local implementation audits two tempting substitutes. Hilbert 94 gives
only a non-equivariant order-`p` class-group quotient. Relative ideal norms are
killed by the checked Artin map, but the relative norm homomorphism is proved
not surjective for a nontrivial inverse extension. Likewise, the ordinary
cyclotomic orbit norm annihilates the inverse-character line because the sum
of the inverse cyclotomic character is zero. Isolating an arbitrary principal
denominator requires the weighted orbit operator, and vanishing for that
operator is precisely the remaining one-sided reciprocity theorem rather than
a consequence of the available norm formulas.

The integrated local cone now sharpens that boundary substantially. Its
finite-field power-residue exponent and multiplicative-character packaging
are attributed adaptations of AINTLIB's Apache-2.0 `ResidueSymbol/Basic.lean`
and `Furtwaengler/Character.lean` at
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`; exact source blobs and the local
port are recorded in `THIRD_PARTY_NOTICES.md` and `PORTING.md`. The diagonal
Jacobi sum then specializes Mathlib's Apache-2.0
`NumberTheory.JacobiSum.Basic` implementation by Michael Stoll, following
Ireland--Rosen, Section 8.3. New checked proofs establish Galois covariance,
the corrected `b = 2` Stickelberger scalar, the faithful-orbit ideal
factorization of the conjugate Jacobi sum, and triviality on nonfaithful prime
orbits. The final consumer reduces the integral Kummer product to one explicit
power-residue-symbol value on that principal Jacobi ideal at every faithful
denominator prime. It deliberately retains the assertion that those values
equal one as a pointwise hypothesis: that assertion is the remaining
reciprocity theorem, not an imported or hidden assumption.

This is substantial prior art: 827 Lean files and 360,084 lines under
`projects/ModularCurves/ModularCurves`. It is not a completed dependency.
A source scan found 212 `sorry` tokens in 72 files, including roughly 100
obvious proof bodies in 34 files, and 1,662 source-level `set_option` lines.
The umbrella module does not reach every frontier file, and there were no
GitHub check runs at the audited revision. A source-clean leaf must therefore
still be checked through its complete import cone and with `#print axioms`.

The strongest concrete reuse candidates are:

* [`Scheme.Pic`](https://github.com/CBirkbeck/AINTLIB/blob/7ecbba9dbb7fee076a1b77a6cd516fc6de46d684/projects/ModularCurves/ModularCurves/Picard/Pic.lean#L118),
  pullback on Picard groups, and the relative definitions
  [`picRel`](https://github.com/CBirkbeck/AINTLIB/blob/7ecbba9dbb7fee076a1b77a6cd516fc6de46d684/projects/ModularCurves/ModularCurves/Picard/RelativePic.lean#L57) and
  [`picRelFunctor`](https://github.com/CBirkbeck/AINTLIB/blob/7ecbba9dbb7fee076a1b77a6cd516fc6de46d684/projects/ModularCurves/ModularCurves/Picard/RelativePic.lean#L203).
  The seven-module, 3,507-line transitive cone for these declarations was
  compiled manually against this project's exact Lean and mathlib pin. The
  option-free monoidal-sheaf foundation, `Scheme.Pic`, general pullback map,
  and all-degree `picRelFunctor` are now retained as attributed local ports.
  The option-dependent proof obligations in the latter two files were replaced
  by explicit mapped-open comparisons and default-budget calculations. A
  checked downstream theorem proves zero-section normalization natural under
  the actual functor map. The source explicitly defers fppf sheafification,
  the degree-zero subfunctor, the Poincare bundle, and Abel's isomorphism; the
  local port does not claim any of those endpoints.
  The same exact snapshot contains
  [`PresheafPullbackCompMonoidal.lean`](https://github.com/CBirkbeck/AINTLIB/blob/7ecbba9dbb7fee076a1b77a6cd516fc6de46d684/projects/ModularCurves/ModularCurves/ForMathlib/PresheafPullbackCompMonoidal.lean)
  and
  [`PullbackCompMonoidal.lean`](https://github.com/CBirkbeck/AINTLIB/blob/7ecbba9dbb7fee076a1b77a6cd516fc6de46d684/projects/ModularCurves/ModularCurves/ForMathlib/PullbackCompMonoidal.lean),
  which prove that the canonical pullback-composition comparisons are
  monoidal first for presheaves of modules and then for scheme modules. Their
  exact-pin local ports redirect imports to the retained pullback foundation,
  add only local elaboration instances, and inline one private mate proof from
  the exact `Picard/DualPullback/RestrictComp.lean` blob recorded in
  `PORTING.md`. They are infrastructure for a checked local overlap-tensor
  comparison consumer; by themselves they neither construct descent data nor
  identify the tensor product of separately descended factor cocycles.
  A further 836-line selective port from
  [`PoleSheaf.lean`](https://github.com/CBirkbeck/AINTLIB/blob/7ecbba9dbb7fee076a1b77a6cd516fc6de46d684/projects/ModularCurves/ModularCurves/EllipticCurve/PoleSheaf.lean)
  and
  [`PullbackTensorSection.lean`](https://github.com/CBirkbeck/AINTLIB/blob/7ecbba9dbb7fee076a1b77a6cd516fc6de46d684/projects/ModularCurves/ModularCurves/EllipticCurve/PullbackTensorSection.lean)
  retains the pure tensor-section constructor, its two-factor map theorem,
  and the canonical pullback-cotensorator evaluator. Its comparison machinery
  remains private, and no separate sheafified tensor-object API is restored.
  The retained
  [`AffineModuleBaseChange.lean`](https://github.com/CBirkbeck/AINTLIB/blob/7ecbba9dbb7fee076a1b77a6cd516fc6de46d684/projects/ModularCurves/ModularCurves/ForMathlib/AffineModuleBaseChange.lean)
  supplies the private global-sections mate and affine tilde/base-change
  isomorphism. The named `tildePullbackGenerator`,
  `tildePullbackGenerator_eq_pullbackUnit_toOpen_top`, and
  `tildePullbackIsoExtendScalars_hom_generator` are project-original
  packaging, pullback-unit transport, and evaluation specializations of that
  mate at top-section generators.
* [`affine_subsingleton_H`](https://github.com/CBirkbeck/AINTLIB/blob/7ecbba9dbb7fee076a1b77a6cd516fc6de46d684/projects/ModularCurves/ModularCurves/ForMathlib/AffineVanishing.lean#L307),
  Cech comparison machinery, exact sequences, and
  [`orderedBaseCechHomologyFinite_of_isProper`](https://github.com/CBirkbeck/AINTLIB/blob/7ecbba9dbb7fee076a1b77a6cd516fc6de46d684/projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleProperLowDegreeCechFinite.lean#L149).
  The option-free long exact sequence and exact additive-sheaf forgetful
  functor are now retained as attributed ports. A checked local consumer
  proves that an affine-cover inclusion is injective on `H^(n + 1)` whenever
  `H^n` of its actual cokernel vanishes; the project now discharges the
  resulting affine-acyclicity induction independently. The option-free
  base-Cech and ordered degree-one comparison slices are also retained. The
  checked project
  consumer `nativeBaseCechHOne_finite_of_ordered` transfers `Module.Finite`
  from ordered degree-one homology to native all-tuples degree-one homology.
  The separately checked comparison
  `nativeBaseCechHOneForgetIsoOfAffineOpenCover` identifies the underlying
  additive group of native base-Cech `H¹` with genuine Ext-based sheaf `H¹`;
  its elementwise preimage theorem is a compiled downstream consumer. The
  global-functions action is now transported explicitly to genuine sheaf
  `H¹`, and a checked linear equivalence carries `Module.Finite` through the
  comparison. The canonical-support extension has also been ported through
  finite affine support annihilation, ideal-power reconstruction, the
  open-local pullback unit, full support of the canonical model, and strict
  support decrease of comparison residuals. The inverse-image-cover
  pushforward comparison is now checked for both native and ordered Čech
  complexes, and its degree-zero/degree-one finiteness equivalence has a
  finite-morphism consumer: finite pushforward preserves finite-type
  quasicoherence, so any target-side coherent low-degree theorem descends.
  This is still only the input to
  the Chow/projective low-degree comodel. An audit of historical AINTLIB
  commit `d78d10a74577e28840d21eb4e07395d87c44370f` found the preferable direct
  degree-zero/degree-one support induction before the later all-degree
  rewrite; that is the route being ported. The proper ordered input and final
  proper-curve `H¹` facade remain open. Nor does this prior art provide the
  relative base-change or semicontinuity APIs required by the roadmap.
* elliptic finite-flat subgroups, the quotient-scheme universal property,
  constant groups, `muN`, and the Hopf-algebraic theorem
  [`deligne_point_pow_eq_one`](https://github.com/CBirkbeck/AINTLIB/blob/7ecbba9dbb7fee076a1b77a6cd516fc6de46d684/projects/ModularCurves/ModularCurves/ForMathlib/CartierDual.lean#L724).
  `CartierDual.lean` and `MuN.lean` both compiled manually against the Mazur
  pin. The explicitly Apache-2.0 `CartierDual.lean` is now retained as an
  attributed, warning-free local port; `MuN.lean` remains excluded because
  the audited file lacks an explicit license header.
* [`GammaZeroStructure`](https://github.com/CBirkbeck/AINTLIB/blob/7ecbba9dbb7fee076a1b77a6cd516fc6de46d684/projects/ModularCurves/ModularCurves/GroupScheme/CyclicSubgroup.lean#L151)
  and the coarse open scheme
  [`YZeroCoarse`](https://github.com/CBirkbeck/AINTLIB/blob/7ecbba9dbb7fee076a1b77a6cd516fc6de46d684/projects/ModularCurves/ModularCurves/Moduli/CoarseSpace.lean#L248)
  over a fixed base where `N` is invertible. This is useful moduli
  scaffolding, not compactified `X₀(N)`, an integral model over `ℤ`, or cusp
  theory.

An exact transitive-import scan, with nested comments and string literals
removed before counting proof holes, sharpens that boundary. Starting from
`CyclicSubgroup`, `SubgroupQuotient`, `NIsogSpace`, and `CoarseSpace` reaches
respectively 215, 250, 265, and 363 local AINTLIB modules. Their closures
contain respectively 7, 7, 10, and 20 files with actual `sorry`, `admit`, or
`axiom` occurrences in code. In particular, `YZeroCoarse` occurs only as the
quotient scheme definition in `CoarseSpace.lean`; the audited tree contains
no map from `GammaZeroStructure` to its points. The older geometric-point
statement `exists_coarse_gammaH` in `Moduli/Coarse.lean` is itself an explicit `sorry`,
as is the non-record-parametric `EllipticCurve.exists_gammaZeroSpace` in
`GroupScheme/NIsogeny.lean`. The sorry-free
`NIsogModuli.exists_gammaZeroSpace` merely assembles a classifier from an
already supplied `NIsogModuli` record and does not construct that record.
Thus none of these names supplies the checked rational `Y₀(N)` classifying
map needed by the direct order-49 consumer.

The central gates remain open. `NIsogeny.lean` leaves the quotient's
smoothness, properness, Weierstrass structure, finiteness, flatness, degree,
and Gamma-zero classifying space as proof holes. `WeilPairing/Basic.lean`
leaves the global scheme-valued pairing and its laws open. No Neron-model,
component-group, Jacobian-variety, Hecke, Eisenstein-ideal, or Eisenstein-
quotient layer was found. AINTLIB's own plan targets open `Y₁(N)`, `Y(N)`,
and twisted `Y(ρ)` and treats the integral `X₀(N)/ℤ` needed by Mazur as a
black box.

The node-by-node estimates recorded in `coordination/program.json` put the
de-duplicated, realistically bankable saving at about **50--75 of the 1,000
effort points**, or **5--7.5 percentage points of total work**. Closing
AINTLIB's quotient, global Weil-pairing, and Gamma-zero representability gates
could raise that to roughly **9--12.5 points**. This is mostly shared-geometry
and moduli substrate; it does not touch the 100-point prime argument or most of
the 400-point prime-level infrastructure.

The audited branch has no root `LICENSE`. The default branch acquired an
Apache-2.0 license only after the development branch diverged, and 599 of the
827 inspected files carry an explicit Apache header. The integration policy is
therefore selective: use named, file-level licensed leaves or obtain license
clarification; converge the mathlib pin; remove option workarounds; preserve
provenance; and add checked integration boundaries plus real consumers. The
admissible Picard and Cartier-duality leaves are now consumed through
`MazurTorsion.Upstream.Geometry`. Thirteen file-level licensed finite-action
leaves are also retained, and the local split-constant translation route now
constructs the corresponding quotient without resolving AINTLIB's general
`NIsogeny` or classifying-space holes. Its elementary translation proof
skeletons come from `GroupScheme/TranslationBySection.lean`, exact blob
`6223d2904bc6f2162d4ee4e77ed684a40396ef18`; because the audited branch copy
has no header, the license evidence is the identical blob at commit
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b` under that commit's root
Apache-2.0 license. The whole AINTLIB project is neither vendored nor treated
as a Lean Pool-ready dependency.

## 11. Route-specific formal-immersion API audit

The August 2026 route review searched the exact project pin, the refreshed
mathlib tree, Tau Ceti, AINTLIB, Imperial FLT, DE0CH/flt-lean, and the public
LeanPool branches for the objects needed by Mazur's 1978 proof. No checked
implementation of a modular-curve formal immersion, a Néron model, a modular
Jacobian, a Hecke action on it, or an Eisenstein/winding quotient was found.
In particular, no upstream theorem currently turns a nonvanishing modular
abelian-variety L-value into finiteness of its rational points.

### Modern expository refresh — 2026-08-15

This source refresh changes the cost comparison, not the checked reuse
inventory above.

* [Merel 2024, *Mazur's work with the Eisenstein ideal*](https://celebratio.org/Mazur_BC/article/1148/)
  isolates the theorem-level requirement as a nonzero quotient of `J₀(N)`
  with finite rational points for `N = 11` or `N > 13`; it does not require a
  public classification of all rational points on that quotient.
* The [MIT Fall 2023 STAGE programme](https://math.mit.edu/nt/old/stage_f23.html)
  and Snowden's Math 679 lectures
  [11](https://public.websites.umich.edu/~asnowden/teaching/2013/679/L11.html),
  [18](https://public.websites.umich.edu/~asnowden/teaching/2013/679/L18.html),
  [20](https://public.websites.umich.edu/~asnowden/teaching/2013/679/L20.html),
  and
  [21](https://public.websites.umich.edu/~asnowden/teaching/2013/679/L21.html)
  independently expose the same integral modular-curve, Jacobian, Néron,
  finite-flat, Eisenstein, and formal-immersion layers. They are useful
  specifications but contribute no exact-pin Lean implementation.
* [Darmon's account in *Arithmetic Geometry*, pages 38--39](https://www.claymath.org/wp-content/uploads/2022/03/cmip08c.pdf)
  describes the winding element in relative homology and the use of Heegner
  points, Gross--Zagier, Kolyvagin, and analytic nonvanishing to prove the
  quotient finite. This is the source that makes the winding alternative's
  additional arithmetic dependency cost explicit.
* The revised
  [Balakrishnan--Mazur 2024 survey](https://arxiv.org/html/2307.04752)
  corroborates the optimal-quotient/formal-immersion architecture. Its
  Chabauty variants address bounded levels, so they do not replace the
  uniform prime-level input.
* [Baker 2026, *Elliptic matroids and modular curves*](https://arxiv.org/abs/2608.05299)
  identifies an elliptic-matroid realization space with the irreducible open
  `X₁(n)°` over `ℤ[1/n]`. This is secondary geometric prior art, not a proof
  shortcut: the open omits the rational cusps used by Mazur's collision, the
  construction assumes the compactified generalized-elliptic moduli object,
  and its nonrepresentability formulation is equivalent to the prime-torsion
  theorem.

None of these expository sources proves that the retained route is globally
minimal. Together they support it as the smallest currently credible route
aligned with the checked reduction argument and the available exact-pin APIs.

There is useful lower-level vocabulary. Mathlib has local rings, stalk and
residue-field maps, cotangent modules, completions, formal-unramifiedness
lemmas, elliptic integral models, and equation-level reduction. Tau Ceti has
abstract abelian varieties, divisor classes, and point-level Abel--Jacobi
classes, but not the relative Picard scheme or Jacobian morphism required to
construct `J₀(N)`. AINTLIB's `GammaZeroStructure` and `YZeroCoarse` live over
bases where the level is invertible; they do not provide the compactified
integral `X₀(N)`, cusps, Néron models, or modular quotient. These are adapters
and foundations, not a discharge of the hard core.

The project now supplies the first checked adapter on top of that vocabulary:
the local map of a scheme morphism induces a canonical `ℤ`-linear map on
stalk cotangent spaces, with a representative formula and a proof that a
surjective stalk map makes it surjective. Its canonical semilinear form uses
the actual induced residue-field homomorphism. A separate modular-curve
boundary packages the residue-field isomorphism, canonical source-residue
dimension one, and the nonzero-vector input expected from the first
q-coefficient calculation. This adapter is not prior art for, or a proof of,
formal immersion itself: no completed-stalk comparison or modular cusp
collision is claimed.

For API design, this evidence supports the following boundary:

- define formal immersion once for locally Noetherian schemes, with both the
  completed-local-ring and cotangent criteria connected by checked lemmas;
- construct only the cusp neighbourhoods at auxiliary characteristics `5`
  and `11` used by real downstream collisions;
- package Mazur's degree-one theorem for a nontrivial optimal new quotient,
  avoiding the symmetric-power Hecke-independence generalization;
- retain precisely the finite-flat and Néron results consumed by the
  Eisenstein rank-zero proof and tame torsion specialization; and
- require the prime-five potentially-good-reduction theorem to compile before
  accepting any of those interfaces.

The route-neutral argument boundary itself is already checked as
`MazurTorsion.PrimeOrder.rationalPoint_primeOrder_ne_of_formalImmersionAtFive`.
The proposed `DegreeOneFormalImmersionWitness` is a future package for
constructing its inputs, not a declaration supplied by the audited prior art
or by current checked source.

The literature comparison and mathematical proof are recorded in
[`ROUTE_AUDIT.md`](ROUTE_AUDIT.md). The decisive observation is that the
winding quotient is geometrically larger but formally more expensive at the
current pin: it trades Mazur's algebraic rank-zero calculation for modular
symbols, analytic L-functions, nonvanishing, and Kolyvagin--Logachev. The
post-`R=T` reinterpretation similarly adds deformation theory without
removing the modular Jacobian or local formal-immersion layer. Neither is
treated as an available shortcut.

The same review found two endpoint savings. Exact order `35` can reuse the
squarefree-level formal-immersion engine at auxiliary prime `11` with the
explicit rank-zero quotient `X₀(35)/w₅`; it need not classify every rational
point on the genus-three curve. Exact order `49` maps its rational cyclic
subgroup directly to the already checked two-cusp classification of
`X₀(49)(ℚ)`; the explicit Vélu additivity and nonbacktracking isogeny tower
are retained as prior work but removed from the endpoint's dependency cone.

For the order-35 model, Bryden Cais's
[*Mazur's torsion theorem* seminar notes, pp. 9--10](https://math.arizona.edu/~cais/Papers/Expos/elltors.pdf)
derive the equation
`y² + y = x³ + x² + 9x + 1` for `X₀(35)/w₅`, list its three rational
torsion points, and state rank zero; the notes explicitly omit the descent
that proves the rank assertion.  The
[LMFDB isogeny class 35.a](https://www.lmfdb.org/EllipticCurve/Q/35/a/)
records `[0,1,1,9,1]` as the Γ₀(35)-optimal curve 35.a3 and
`[0,1,1,-131,-650]` as the torsion-free curve 35.a1 in the same isogeny
class.  Cais also records on pp. 8--10 the degree-eight hyperelliptic model,
the formulas `(x,y) ↦ (-1/x,y/x⁴)` for `w₅`, the invariant coordinates
`u=x-1/x` and `v=y(1+1/x⁴)`, and the birational change to the displayed
elliptic quotient.  These sources are used only as specification and
provenance; the Lean polynomial identities and denominator arguments are
proved locally.  `OrderThirtyFiveQuotientMap` checks the involution and
invariant equation, constructs an actual affine point on the already proved
finite quotient model, and consumes its three-point classification to show
that the displayed hyperelliptic affine model has exactly `(0,1)` and
`(0,-1)` as rational points.  This is an equation-level quotient consumer,
not a represented modular-curve identification.
`OrderThirtyFiveInfinityChartScheme` makes the reciprocal substitution in
the checked source equation, verifies the quotient identity again over an
arbitrary commutative ring, and constructs the resulting affine `Spec` map,
integral cusp section, and first-order coordinate identity.  No additional
literature formula is imported by that construction; the quotient coordinate
remains the one already derived from the audited Cais invariant formulas.
`OrderThirtyFiveInfinityChartCuspAtEleven` identifies the selected cusp ideal
after reduction modulo eleven, proves that its localization has maximal ideal
generated by `t`, detects the nonzero cotangent class with an explicit
dual-number tangent, and transports `W-1=(-7/d)t` through the actual local and
stalk maps.  It therefore proves formal immersion for this represented affine
quotient morphism at the cusp.  This is still an equation-level chart result:
it does not identify that chart with the special fibre of represented
`X₀(35)`.

The local checked declarations also verify arithmetic on the fixed equation, its
rational torsion, the equation landing and zero fibre of a Vélu
point-function candidate, trivial torsion on the candidate target, a total
opposite candidate, and the composite identity with multiplication by three.
The checked rational cover, visible-coset translations, and reduced
numerator-denominator calculation prove the source `1`, `7`, `49` cube-class
alternatives.  The target-candidate surjectivity and the fixed target model's
Mordell--Weil rank-zero theorem are now unconditional.  The modular quotient
identification is not yet proved, so this does not by itself identify the
model with the required modular quotient.

Henri Cohen and Fabien Pazuki's
[*Elementary 3-descent with a 3-isogeny*](https://arxiv.org/abs/0903.4963),
Theorem 4.1 and Corollary 4.3, supply the mathematical specification for the
target descent.  After the checked coordinate change the target is
`v² = u³ - 3(12u+1500)²`.  Here the only rational primes in the possible
common-prime support are `2`, `3`, and `5`: Lean proves that `2` and `5` are
inert prime elements and that `√-3` generates the ramified prime over `3`.
Coordinate conjugation then identifies the two factor valuations at every
exceptional prime, and unique factorization makes the negative factor an
associated cube.  The two nontrivial homogeneous cubics were instantiated
locally from the published general formula, and Lean proves by a mod-seven
infinite descent that each has only the zero integral solution.  Lean also
clears the target denominators primitively, checks the conjugate norm
factorization, applies the complete six-unit classification, and derives the
explicit fibre root `-42d/(c+8d)` in the trivial unit class.  The paper is used
as mathematical specification and provenance; the denominator normalization,
prime-support, valuation, unique-factorization, and rank-zero deductions are
all checked declarations, with no paper claim, database rank, or
computer-algebra transcript imported as proof.

## 12. Multiplication-polynomial discriminants and executable resultants

Harry Schmidt's paper
[*Resultants and discriminants of multiplication polynomials for elliptic
curves*](https://doi.org/10.1016/j.jnt.2014.10.007) proves the exact
universal formula needed by the fixed-level route. In the paper's short
model `y²=x³+ax+b`, let `Aₙ/Bₙ` be the normalized rational function giving
the abscissa of `[n]P`, and let `Bₙ*` be the squarefree factor of `Bₙ`.
Theorems 1.1 and 1.2 state

\[
\operatorname{Res}(A_n,B_n)
 =(16\Delta)^{n^2(n^2-1)/6}
\]

and, for odd `n`,

\[
\operatorname{disc}(B_n^*)
 =(-1)^{(n-1)/2}
   n^{(n^2-3)/2}
   (16\Delta)^{(n^2-1)(n^2-3)/24}.
\]

Section 8 transports the formula to a general Tate Weierstrass equation,
where the powers of `16` are absorbed by the standard normalization. At
`n=5,7` this is exactly

\[
\operatorname{disc}(\operatorname{pre}\Psi'_5)=5^{11}\Delta^{22},
\qquad
\operatorname{disc}(\operatorname{pre}\Psi'_7)=-7^{23}\Delta^{92}.
\]

Both displayed specializations are now implemented locally as
`discr_preΨ_five` and `discr_preΨ_seven`. Their option-free proofs use
sparse polynomial identities, cubic resultants, and elliptic-divisibility
syzygies; the resulting theorem dependency cones contain only the three
foundational axioms allowed by LeanPool.

The paper also gives a useful algebraic reduction. Lemma 6.1 expresses
`Aₙ` in terms of `Bₙ`, the short cubic, and two derivatives; the proof of
Theorem 1.2 then reduces the fourth power of the discriminant to two
resultants. The paper proves the universal resultant and its sign using
complex Fourier expansions, so importing that whole proof would require
far more analysis than the two fixed levels. Its formula and resultant
organization nevertheless led to the compact local syzygy certificates
recorded in `INFORMAL_PROOF.md`.

The Apache-2.0 repository
[`kim-em/hex-dev`](https://github.com/kim-em/hex-dev), inspected at
[`1910b223f4b1223eb939a40205af577abfd7dcbd`](https://github.com/kim-em/hex-dev/commit/1910b223f4b1223eb939a40205af577abfd7dcbd),
contains an executable Brown subresultant implementation and a bridge
theorem `HexResultantMathlib.toPolynomial_disc` identifying its computed
discriminant with `Polynomial.discr`. It is excellent evidence that large
fixed polynomial certificates can be checked through fraction-free
subresultants. Direct reuse is not appropriate here: the snapshot has a
different mathlib pin, and its multivariate/dense-polynomial dependency
cone contains option overrides forbidden by this project. More
importantly, a naive subresultant chain for the degree-24 seventh-division
polynomial has enormous intermediate coefficients. The elliptic
divisibility syzygies reduce that calculation to a handful of small
resultants and are therefore the selected implementation.

## 13. Other formalizations and branches

The classification-to-cardinality pattern also appears in
[`AwesomeTheorems/Stage1/S1_M_088.lean`](https://github.com/weiyangzen/awesome_theorems/blob/9c299dbabd34878a420db46ca66d687886fe2b04/Formalizations/Lean/AwesomeTheorems/Stage1/S1_M_088.lean).
It defines predicates for the cyclic and bicyclic lists and proves the tiny
counting bridge, but assumes rather than proves classification. Our local
bridge was adapted independently to the exact LeanPool type.

Several other apparent hits are not reusable proofs:

* Facebook Research's Atlas has an admitted
  `WeierstrassCurve.Affine.Point.mazur_torsion`;
* HautevilleHouse's elliptic-curve branch admits torsion finiteness and
  Mazur's theorem;
* the stale Tate-normal-form PR #25218 supplies conceptual normalization
  work but no classification.

Later mathlib work should be monitored but is outside the pin. In
particular, PR #41439 adds abstract finiteness of torsion from descent data,
PR #42160 adds a two-torsion polynomial dictionary, and
[PR #42219](https://github.com/leanprover-community/mathlib4/pull/42219)
contains the two-torsion bound. None closes the sharp classification.

For the newly compiled order-fourteen Tate certificate, the external
algebraic model was checked against F. Patrick Rabarison,
[“Structure de torsion des courbes elliptiques sur les corps quadratiques”](https://doi.org/10.4064/aa144-1-3),
§4.2.  After the sign change between the two Tate conventions, its plane
equation agrees term for term with `orderFourteenPolynomial`.  The paper
identifies the resulting curve with
`s²+st+s=t³-t` and lists its six rational cusps.  The
[LMFDB entry 14.a5](https://www.lmfdb.org/EllipticCurve/Q/14/a/5)
independently records the same model, rank zero, and torsion group
`ℤ/6ℤ`.  These database and computer-algebra assertions are specifications,
not imported proofs.  The local development now proves the rank-zero and
finiteness assertions independently by an explicit two-isogeny descent,
constructs six distinct visible points, and uses the exact-pin reduction
port only for the remaining sharp six-point upper bound.

The same paper's §§4.4--4.5 provide independent checks of the small
hyperelliptic models

\[
X_1(16):y^2=x(x^2+1)(x^2+2x-1)
\]

and

\[
X_1(18):y^2=x^6+2x^5+5x^4+10x^3+10x^2+4x+1.
\]

The local order-sixteen development derives its sextic directly from the
duplication chain and proves its noncuspidal rational locus empty; it does
not import Rabarison's computer algebra.  The local order-eighteen
parameterization gives the equivalent reciprocal-and-sign-changed sextic
`Y²=X⁶-4X⁵+10X⁴-10X³+5X²-2X+1` and stops honestly before the genus-two
rational-point classification.

For the direct `X₀(49)` route, Kilford and McMurdy,
[*Slopes of the U7 operator acting on a space of overconvergent modular
forms*](https://doi.org/10.1112/S1461157012000095), §2, supply the affine
eta-quotient equation used as the target specification.  The local module
`XZeroFortyNineEtaModel.lean` independently checks the displayed coordinate
change to `Y² = X(X² + 21X + 112)`, proves its rational denominator is
nonzero, and consumes the checked two-cusp classification to empty the open
rational eta locus.  No source code or computer-algebra transcript is
imported.  This target-side calculation does not construct the still-missing
coarse classifying map from a rational cyclic subgroup of order `49`.

Andrew Sutherland's public
[`X₁(m,n)` equation tables](https://math.mit.edu/~drew/X1mn.html)
were used as a specification check for the low-level modular curves.  In
particular, they corroborate the standard order-eleven model

\[
v^2+v=u^3-u^2
\]

and the order-eighteen sextic.  No table code or computer-algebra transcript
is imported.  The local order-eleven bridge is independently derived from
the checked Tate multiples: `6P=-5P` gives the raw plane equation, and Lean
verifies every denominator and every identity in the rational map

\[
(r,q)\longmapsto
\left(
\frac{q^2-q-r+1}{rq-2r+1},
\frac{(q-r)(q^2-q-r+1)}{(rq-2r+1)^2}-1
\right).
\]

The inverse rational functions and singular-discriminant eliminant in
`Kubert/OrderElevenModelInverse.lean` were derived locally rather than copied
from Sutherland's tables.  A scratch SymPy calculation was used to discover
the compact Bézout coefficients for the raw modular equation and the remaining
discriminant factor.  No generated source or transcript is imported: Lean's
`ring` tactic checks the full polynomial identity, and Mathlib's integral-root
theorem plus direct evaluation at `±1` checks that the monic degree-five
eliminant has no rational root.  The reverse round trip, every denominator,
the Tate discriminant, and the exact-order consumer are all kernel-checked.

For order twenty-five, Sutherland's separate
[`X₁(N)` raw-equation index](https://math.mit.edu/~drew/X1_rawcurves.html)
identifies its entries as plane equations `F(r,s)=0` in the Tate parameters
used in *Constructing elliptic curves over finite fields with prescribed
torsion*.  The exact coefficient source used here is the public
[`F25.txt`](https://math.mit.edu/~drew/F25.txt), retrieved 2026-08-08 with
SHA256
`37bf29e86705adba268493d8967670327f4c97975e65436b3139899c36b42db0`.
The coefficients are retained only in private staged definitions.  Lean
checks, in six denominator-clearing pieces, that the substitution
`r=b/c`, `s=c²/(b-c)` gives the existing degree-40 normalized collision
factor; the table is therefore a specification and coefficient source, not
a trusted computer-algebra proof.

The modular-unit convention was checked against three primary sources.
Odile Lecacheux's
[*Unités d'une famille de corps liés à la courbe X₁(25)*](https://doi.org/10.5802/aif.1212),
especially pp. 239--243, gives the division-value cross-ratios and the
diamond action.  Its public NUMDAM PDF was retrieved 2026-08-08 with SHA256
`f8d247188a9f272335c46e15305025d157a855263c6ce916f8a6582e07f74ccc`.
Henri Darmon's
[*Note on a polynomial of Emma Lehmer*](https://www.math.mcgill.ca/darmon/pub/Articles/Research/03.Lehmer/paper.pdf),
pp. 4--5, records the Klein-form products and their leading signs; that PDF
was retrieved 2026-08-08 with SHA256
`a560e9a795cbc0cf20342fa6eead478f9de3f362d7ee7e003cc40b9c5af7a0a3`.
Finally, François Brunault's
[*On the Mahler measure associated to X₁(13)*](https://perso.ens-lyon.fr/francois.brunault/recherche/m13.pdf),
§6.3, prints the `N=25` product expansions and the genus-four polynomial;
that PDF was retrieved 2026-08-08 with SHA256
`87ab945c1d43e722d92280f1a07f7d597add089babaac301cdd8b74daa376d04`.
Together these fix the signs used by the local bridge:
`u = y₄ y₇` and `v = -(y₉ y₃)`.  Exact-order separation proves
all six denominators and both coordinates nonzero.  The characteristic-zero
polynomial identity remains a kernel-checked algebraic step; no `q`-expansion
or external symbolic remainder is imported as proof.  In particular,
nonzero rational modular units do not by themselves have nonzero reduction
modulo three: a later rational-point exclusion still needs an integral,
valuation-zero specialization theorem for the open chart.

Lécacheux's pp. 241--243 also give the five cyclic difference relations,
the norm-one relation, the invariant identity `R + Q - S = 5(1 - n)`, and
Lehmer's quintic.  `OrderTwentyFiveBrunaultOrbitExclusion.lean` uses that
identity to recover `n` from the orbit coordinates.  Lean's checked polynomial
normalization proves that, away from the exceptional value `x₀ = 1`, the
six orbit equations force the elementary symmetric coefficients printed in
the source and hence make `x₀` and `x₂` roots of the quintic.  The proof
imports no external Gröbner certificate.  Exact-order separation now proves
the exceptional value is avoided, and an exact coefficientwise polynomial
certificate proves two cyclic relations for the explicit Tate cross-ratios.
The remaining bridge consists of the other three cyclic
relations, the norm-one relation, and Fricke transport when `5/n`, rather than
`n`, is the parameter integral at three.

William Stein and Andrew Snowden's public
[`X₁(N)` lecture notes](https://public.websites.umich.edu/~asnowden/teaching/2013/679/L23.html)
also identify the remaining arithmetic character of these cases:
`X₁(11)` requires a genuine rank-zero argument (classically a
five-isogeny descent), while the genus-two levels require Jacobian descent
rather than finite-field point counts alone.  The local modules follow that
boundary strictly.  Their mod-three certificate for level thirteen and
mod-five certificate for level eighteen prove separability and enumerate
six reduced point directions.  Subsequent checked chart-gluing work now
identifies the level-thirteen base-field certificate with literal points of
the proper glued projective scheme, but still makes no Jacobian-rank or
rational-reduction claim.

The local `X₁(13)` descent identities were independently derived rather
than copied from a repository or coefficient table.  In particular, the
degree-`(19,16)` polynomial Pell solution was found by a short local
standard-library-only computation: hand-written rational polynomial
arithmetic ran the continued-fraction algorithm for the square root of the
sextic, and convergent twelve first produced constant remainder `-4`.
Only the resulting integer coefficient arrays were transcribed into Lean;
`ring` then kernel-checks both the affine and reciprocal identities.  No
external source code or coefficient list was used.  Snowden's
[`X₁(13)` lecture](https://websites.umich.edu/~asnowden/teaching/2013/679/L22.html)
and Mazur--Tate's published argument are used only to identify the
subsequent mathematical dependency shape: divisor interpretation,
`19`-isogeny surjectivity on the Jacobian, rational Jacobian torsion, and
the Abel--Jacobi cusp intersection.

The primary paper was re-audited directly as B. Mazur and J. Tate,
*Points of Order 13 on Elliptic Curves*, Invent. Math. 22 (1973), 41--49,
[doi:10.1007/BF01425572](https://doi.org/10.1007/BF01425572); the reviewed
PDF has SHA-256
`a451c978b1557e7f1f95e34bf62f51f8ee98d5e29b100a5e46345a69653e49c1`.
The paper proves `#J₁(13)(ℚ)=19` by a finite-flat `19`-isogeny descent
and then invokes Ogg's determination of the curve's intersection with the
rational cusp subgroup.  S. Kamienny and B. Newman's later paper of the
same title, [arXiv:1608.08672](https://arxiv.org/abs/1608.08672), was also
checked (reviewed PDF SHA-256
`5d7d5412bf1bcdf2162eb0b1320af1d159eca62c1f9f6e0e8fb36789820ee22d`).
Its bielliptic route over `ℚ(ζ₁₃)⁺` does not remove the rational
Jacobian descent needed here.  The exact local-cover failure and the new
two-prime finite divisor enumeration are documented in
`docs/XONE_THIRTEEN_JACOBIAN_AUDIT.md`.

The Apache-2.0 repository
[`vaca22/riemann-roch-function-fields`](https://github.com/vaca22/riemann-roch-function-fields)
was also inspected at
[`dbca5beed1da77e2ecd1eec207d0451fa57e8aa6`](https://github.com/vaca22/riemann-roch-function-fields/commit/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6).
It has axiom-clean genus-one and Picard-torsor results, including
`FunctionField.genus_eq_one`, `picTorsor`, and
`picTorsor_compat_groupLaw` for Weierstrass curves. It has no elliptic
isogeny, dual-isogeny, or quotient declarations, so it is useful future
infrastructure rather than a present discharge of the `X₀(20)` or
`X₀(24)` work.

## 14. Mazur's bad-level elementary factors

The integral scope and notation for the quasi-finite elementary factors were
checked directly against Barry Mazur's
[*Modular curves and the Eisenstein ideal*](https://www.numdam.org/item/PMIHES_1977__47__33_0.pdf),
Chapter I §1, printed pp. 43--49, and the modern seminar exposition
[*Admissible group schemes*](https://www.dpmms.cam.ac.uk/~jcsl5/mazur/4.Admissiblegroups.pdf),
slides 14--20. These sources distinguish the coefficient prime `p` from the
bad level `N` and identify the minimal extension as `j_!` from
`Spec ℤ[1/N]`. They also show that the page-49 quotient terms are fppf
sheaves supported on the fibre at `N`, not quasi-finite flat quotient group
schemes.

The local `constantFlat` Hopf localization is an independent Lean
implementation of the componentwise principal open; no source code or
computer-algebra transcript was copied. The former one-parameter
specialization was repaired to `mazurConstantFlat coeffPrime level` before a
downstream cohomology interface was accepted. The multiplicative-flat design
is likewise being derived directly from the group-algebra trace element and
will not use an unsupported Cartier-dual shortcut. The checked route therefore
keeps quasi-finite admissible-filtration quotients separate from supported
sheaf localization sequences.

## 15. Tate's tame local algorithm

The coefficient-depth cases were checked against John Tate,
[*Algorithm for determining the type of a singular fiber in an elliptic
pencil*](https://doi.org/10.1007/BFb0097582), LNM 476 (1975). The public
Antwerp scans used for the exact sequence are the
[normalization and opening cases](https://wstein.org/Tables/antwerp/tate/47.jpg),
[types II and III](https://wstein.org/Tables/antwerp/tate/48.jpg),
[type IV and the star cubic](https://wstein.org/Tables/antwerp/tate/49.jpg),
[the star branches](https://wstein.org/Tables/antwerp/tate/50.jpg),
[the dual branches](https://wstein.org/Tables/antwerp/tate/51.jpg), and the
[terminal minimality case](https://wstein.org/Tables/antwerp/tate/52.jpg).

No source code or formal proof was copied. The local Lean development derives
the displayed polynomial identities directly by ring normalization and proves
only the pointwise consequences needed by Mazur's torsion argument. In
particular, `TateFirstBlowup.lean` calls its formulas total-transform quotient
identities: it does not claim scheme-theoretic strict transforms, coverage of
a blowup, regularity, Kodaira symbols, or component intersection graphs. The
first checked coefficient-depth branch proves that nonzero exceptional `b₆`
puts every local point in canonical nonsingular reduction. The selected
five- and eleven-adic consumers then rule out that branch for the marked
torsion point and force `a₆` into the square of the maximal ideal. The later
`b₄` branch is also checked pointwise: the tangent-slope valuation split puts
the marked double in canonical nonsingular reduction, and the two selected
consumers force `a₄` into the square of the maximal ideal. The formalization
does not import Tate's component labels from the paper and still makes no
strict-transform, regular-model, Kodaira-symbol, or component-incidence
claim. The exact-depth-two `a₆` branch now likewise follows only the affine
tangent and secant formulas: it puts the marked triple in canonical
nonsingular reduction, so the selected consumers force `a₆` into the cube of
the maximal ideal. The exceptional star cubic and deeper weighted branches
remain separate work.

## 16. Global code search

Exact searches for `torsion_ncard_le`, `mazur_classification`,
`torsion_finite_rat`, and Lean versions of Merel's theorem found no completed
proof outside the projects above. In particular:

* LeanPool `main` has no submitted Mazur solution;
* Imperial FLT assumes the theorem;
* DE0CH/flt-lean has the broadest scaffold but a large unfinished dependency
  cone;
* Victor Aguiar's branch supplies the clean pinned low-torsion foundations
  already ported here;
* Michael Stoll's project supplies a clean licensed Mordell--Weil,
  reduction, and 2-descent stack, but not Mazur's classification; the
  height, finite-group index, and exact-pin point-reduction slices are now
  ported locally;
* the dormant mathlib scalar-multiplication branch supplies a licensed
  generic design, while the two exact fixed-level root criteria needed here
  are now proved locally;
* Birkbeck's Lutz--Nagell repository proves strong integrality and
  discriminant-divisibility statements, but does not prove the needed
  rank-zero modular-curve certificates and is not source-compatible with
  this project's licensing and option restrictions;
* AINTLIB now contains substantial general `Y₁(N)` and Weil-pairing
  infrastructure, but no completed low-level rational-point calculation
  for the `C₂ × C₁₂` cubic; the local proof instead closes that curve by
  combining its direct two-descent with the exact-pin good-reduction port;
* Schmidt proves the exact universal multiplication-polynomial
  discriminant formula, while the local implementation specializes its
  resultant architecture to small kernel-checked certificates;
* `hex-dev` supplies a licensed executable-resultant design, but the local
  elliptic syzygies avoid its incompatible option-bearing dependency cone.

## 17. Reuse decision

The implementation policy following this audit is:

1. Use mathlib's pinned affine point, torsion, division-polynomial,
   finite-abelian, polynomial, and cardinality APIs directly.
2. Retain the attributed Apache-2.0 low-torsion files from Victor Aguiar.
3. Treat Imperial FLT declarations as API references only where their proof
   cones remain unfinished.
4. Treat DE0CH/flt-lean as a dependency map and experiment log, not as
   importable proof code.
5. Port narrowly selected Apache-2.0 declarations from Michael Stoll's
   project when they shorten the explicit `X₀(20)` and `X₀(24)` certificates.
6. Retain the dormant mathlib `ZSMul` audit as a generic design reference;
   use the completed local fixed-level criteria on the critical path.
7. Use the attributed, checked AINTLIB Picard and Cartier-duality ports through
   `MazurTorsion.Upstream.Geometry`, and the Hilbert-94 port through
   `MazurTorsion.NumberTheory.CyclotomicHilbert94`; do not interpret the latter's
   class-number divisibility as an inverse-character quotient.
8. Use Schmidt's formulas as the mathematical specification for the local
   fixed-level resultant certificates; do not import the analytic proof.
9. Treat `hex-dev` as licensed algorithmic design evidence, while retaining
   the smaller option-free syzygy proof at the exact pin.
10. Continue the exact-pin Tau Ceti dependency, while monitoring the genus-one
   Picard work, AINTLIB, and relevant mathlib PRs. Pin updates must keep the
   root and separate Tau Ceti contract workspaces synchronized.

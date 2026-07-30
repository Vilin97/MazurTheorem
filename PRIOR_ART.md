# Lean prior-art audit for Mazur's torsion theorem

This audit records what was inspected, at which revision, what can be reused,
and what remains unproved. A declaration is counted as reusable only when its
dependency cone is free of unproved axioms and it is compatible with the
project's source restrictions.

## 1. LeanPool target and pin

The upstream repository was inspected at
[`c2223fd6be2a245929bf777c01df1577f724d3f3`](https://github.com/Vilin97/lean-pool/commit/c2223fd6be2a245929bf777c01df1577f724d3f3).
The exact challenge is
[`Challenge/Mazur.lean`](https://github.com/Vilin97/lean-pool/blob/main/Challenge/Mazur.lean).
It is still marked open and estimates roughly 50,000 lines.

The challenge pin is:

* Lean `v4.32.0-rc1`;
* mathlib tag `v4.32.0-rc1`;
* resolved mathlib commit
  `360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`.

No `Solution/Mazur.lean` exists on upstream `main`, and a repository-wide
search found no second proof of the exact declaration.

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
* finiteness of `E(ℚ)ₜₒᵣₛ`;
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
[`9a2ca10d4c0f195d73b8da58f94e5ddffd96cb1e`](https://github.com/DE0CH/flt-lean/commit/9a2ca10d4c0f195d73b8da58f94e5ddffd96cb1e).
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

* `TorsionCard.lean` and `TorsionCardSep.lean` rely on many local option
  overrides, contrary to this project's restrictions;
* the repository had no license file at the inspected revision, so its
  original source cannot safely be redistributed;
* its mathlib pin is not identical to the challenge pin.

Mathematical ideas and dependency boundaries from this work inform the
blueprint, but any implementation here must be independently written or
come from an explicitly compatible licensed source.

Two smaller files are especially useful as designs. `TorsionCounting.lean`
has no source placeholder or option override and gives a clean
finite-abelian counting argument. `TorsionReduction.lean` likewise has no
source placeholder or option override and develops substantial tame
reduction machinery. They still lack an explicit license grant at this
snapshot, so their source is not copied.

## 6. Tau Ceti

The current
[`TauCetiProject/TauCeti`](https://github.com/TauCetiProject/TauCeti)
repository was inspected near commit `fa8d836…`. It is Apache-2.0 and
contains general algebraic-geometry work,
including an abelian-variety shell and morphism groups. It is pursuing a
Jacobian roadmap and is worth monitoring.

At the inspected snapshot it did not contain:

* elliptic-curve torsion or Weil pairings;
* modular curves or their integral models;
* the Jacobian construction needed for `J₀(N)`;
* Hecke/Eisenstein infrastructure;
* a theorem that closes any current Mazur dependency.

Its present value is architectural and prospective rather than an immediate
import.

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
around the renamed ramification-index API. The final
`MordellWeil.lean` file has three pin-specific blockers:

1. its import closure no longer brings in the old `sym2x` declaration
   automatically, although the repository already has the needed
   `Affine/AddSubMap.lean` source;
2. the post-pin helper
   `AddCommGroup.finite_torsion_of_descent'` is absent;
3. the challenge pin predates the number-field Northcott instance used for
   `logHeight₁`.

The latter is the substantive port: upstream's later Northcott support is
about 224 lines, while a rational-only specialization should be smaller.
Mordell--Weil finiteness is not required by the literal `Set.ncard`
challenge, so this port is not on the final theorem's critical path.
However, the variable-change, reduction, and explicit 2-descent layers are
high-value licensed substrates for certifying the rank-zero models of
`X₀(20)` and `X₀(24)`. The selected strategy is to port the smallest
dependency cone needed for those two curves rather than vendor the entire
project.

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

## 9. Other formalizations and branches

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

## 10. Global code search

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
  reduction, and 2-descent stack, but not Mazur's classification;
* the dormant mathlib scalar-multiplication branch supplies a licensed
  generic design, while the two exact fixed-level root criteria needed here
  are now proved locally.

## 11. Reuse decision

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
7. Monitor Tau Ceti, the genus-one Picard work, and relevant mathlib PRs,
   while keeping the project self-contained at the LeanPool pin.

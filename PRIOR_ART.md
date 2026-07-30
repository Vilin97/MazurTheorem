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

The current
[`TauCetiProject/TauCeti`](https://github.com/TauCetiProject/TauCeti)
repository was refreshed at commit
[`6987c24c92f9fd3f4fa2facd21a30bd76ae771f3`](https://github.com/TauCetiProject/TauCeti/commit/6987c24c92f9fd3f4fa2facd21a30bd76ae771f3).
It is Apache-2.0 and
contains general algebraic-geometry work,
including an abelian-variety shell and morphism groups. It is pursuing a
Jacobian roadmap and is worth monitoring.

At the inspected snapshot it did not contain:

* elliptic-curve torsion or Weil pairings;
* modular curves or their integral models;
* the Jacobian construction needed for `J₀(N)`;
* Hecke/Eisenstein infrastructure;
* a theorem that closes any current Mazur dependency.

The newest relevant addition is the endomorphism ring of an abelian
variety. Its source explicitly notes that multiplication-isogeny dimension
and torsion theory are still future layers, so it does not yet shorten the
prime-level Mazur argument.

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
The rational specialization has now been completed locally:
`NumberTheory/RatNorthcott.lean` supplies the exact-pin Northcott instance,
and the height portion of Stoll's `MordellWeil.lean` is narrowly ported as
`Foundations/NaiveHeightDescent.lean`. Its endpoint turns finite index of
doubling into finite generation. The pure finitely-generated-group formula
from Stoll's `Mathlib/SelmerGroup.lean`,

\[
[G:nG]=n^{\operatorname{rank}G}\#G[n],
\]

is separately ported as `GroupTheory/IndexNSmulFG.lean`. Both ports compile
at the challenge pin and their public endpoints depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

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
[`fa3c5e6ee266ce3060bf9964fa3a592c9f8fcd8e`](https://github.com/CBirkbeck/AINTLIB/commit/fa3c5e6ee266ce3060bf9964fa3a592c9f8fcd8e).
That snapshot uses Lean `v4.33.0-rc1` and mathlib commit
`3edb3c0658f69f197b1e501b1f7623f3f7b3898c`.

Two projects are directly relevant:

* `projects/ModularCurves` develops Katz--Mazur style torsion subgroup
  schemes, Drinfeld and full level structures, the Tate normal form
  `Y² + AXY + BY = X³ + BX²`, and a general construction of `Y₁(N)`.
  A source search found no specialization to levels `10`, `12`, `20`, or
  `24`, and no computation of the rational points of `X₁(10)`,
  `X₁(12)`, `X₀(20)`, or `X₀(24)`. At this revision the project has 809
  Lean files; 215 `sorry` occurrences remain in 72 files, together with
  many local and global option overrides. It is valuable architectural
  prior art, not a closed arithmetic proof of either exceptional subgroup
  obstruction.
* `projects/HasseWeil/HasseWeil/HasseBound/WeilPairing` contains a much
  later explicit Weil-pairing construction. The core files define the
  pairing, prove bilinearity, alternation and nondegeneracy over an
  algebraically closed field, and develop Frobenius equivariance. The
  directly inspected pairing core files contain no `sorry`; their
  docstrings report foundational-axiom-only audits. The full directory is
  nevertheless a large function-field, divisor, isogeny, and geometric
  torsion stack, has nine remaining `sorry` occurrences elsewhere, and
  uses forty `set_option` occurrences in 26 files. Porting it merely to
  exclude full rational `5`- and `7`-torsion would be far larger and less
  pin-stable than the local fixed-prime division-polynomial route.

GitHub again detects no root repository license file. Many individual
AINTLIB files carry an Apache-2.0 header, while others, including the
new Lutz--Nagell generalization files, do not. Nothing from an ambiguous or
unfinished dependency cone is copied here. The Tate-normal-form equation
and the Weil-pairing interfaces serve as independent corroboration of the
local blueprint.

## 11. Multiplication-polynomial discriminants and executable resultants

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

## 12. Other formalizations and branches

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

William Stein and Andrew Snowden's public
[`X₁(N)` lecture notes](https://public.websites.umich.edu/~asnowden/teaching/2013/679/L23.html)
also identify the remaining arithmetic character of these cases:
`X₁(11)` requires a genuine rank-zero argument (classically a
five-isogeny descent), while the genus-two levels require Jacobian descent
rather than finite-field point counts alone.  The local modules follow that
boundary strictly.  Their mod-three certificate for level thirteen and
mod-five certificate for level eighteen prove separability and enumerate
six reduced point directions, but explicitly make no projective,
Jacobian-rank, or rational-reduction claim.

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

## 13. Global code search

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

## 14. Reuse decision

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
7. Use the Birkbeck--Angdinata Lutz--Nagell and AINTLIB developments as
   theorem-interface and dependency-boundary references only.
8. Use Schmidt's formulas as the mathematical specification for the local
   fixed-level resultant certificates; do not import the analytic proof.
9. Treat `hex-dev` as licensed algorithmic design evidence, while retaining
   the smaller option-free syzygy proof at the exact pin.
10. Monitor Tau Ceti, the genus-one Picard work, AINTLIB, and relevant
   mathlib PRs, while keeping the project self-contained at the LeanPool
   pin.

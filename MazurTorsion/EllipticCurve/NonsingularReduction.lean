/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Vasily Ilin
-/

import MazurTorsion.EllipticCurve.TameAdditiveReductionData

/-!
# The canonical nonsingular-reduction domain of a local Weierstrass equation

For a singular special Weierstrass cubic, coordinatewise reduction is not defined on every local
point with values in the group of nonsingular points: some local points reduce to the singular
point.  It is, however, defined on a canonical predicate.  A point in the formal kernel reduces to
infinity; a point outside the formal kernel has integral coordinates, and belongs to the predicate
exactly when their residues form a nonsingular point of the special cubic.

This file constructs that predicate and the actual coordinatewise reduction function.  Its kernel
is proved to be the exact-pinned formal filtration without any good-reduction hypothesis.  One
remaining local compatibility statement, `NonsingularReductionIsAdditive`, says precisely that
this canonical predicate is closed under addition and that coordinatewise reduction respects the
group law.  From this single statement we construct the canonical identity subgroup and its
reduction homomorphism.

At five and eleven, an additive-special-fibre classification
`(adicRedCurve W₀).Point ≃+ ResidueField 𝒪` and the genuine component bound then produce
`TameAdditiveReductionDataAtFive` or `TameAdditiveReductionDataAtEleven`.  Thus downstream code no
longer accepts an arbitrary identity subgroup or an arbitrary map to the additive residue group.
The three remaining inputs name the actual group law, special-fibre classification, and component
geometry rather than hiding them.

The pointwise reduction, kernel, and negation arguments are a singular-fibre
adaptation of Michael Stoll's good-reduction construction in
`EllipticCurves.WeierstrassFormalGroup.Reduction`, pinned at commit
`3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f` under Apache-2.0. Unlike that
source, this file does not assume the reduced cubic is elliptic and restricts
the map to the canonical nonsingular-reduction domain.
-/

noncomputable section

open IsLocalRing

namespace WeierstrassCurve.Affine

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

universe u v

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
  {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
  {v : HeightOneSpectrum R} {W : Affine (v.adicCompletion K)}
  {W₀ : WeierstrassCurve (v.adicCompletionIntegers K)}
  (hW : W₀.map
    (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) = W)

local notation:max "res" x:max =>
  IsLocalRing.residue (v.adicCompletionIntegers K) x

/-- A local point has nonsingular reduction when it lies in the formal kernel, or, outside that
kernel, its integral coordinates reduce to a nonsingular point of the special Weierstrass cubic.

The universal quantifier over `hx` makes the formal-kernel case propositionally automatic and
keeps this definition independent of a chosen decision procedure. -/
def HasNonsingularReduction [W.IsElliptic] [DecidableEq (v.adicCompletion K)] :
    W.Point → Prop
  | .zero => True
  | .some x y h => ∀ hx : ¬ exp (2 : ℤ) ≤ Valued.v x,
      (adicRedCurve W₀).Nonsingular
        (res ⟨x, (integral_of_not_mem hW h.left hx).1⟩)
        (res ⟨y, (integral_of_not_mem hW h.left hx).2⟩)

variable [W.IsElliptic] [DecidableEq (v.adicCompletion K)]

local instance : DecidableEq (ResidueField (v.adicCompletionIntegers K)) :=
  Classical.decEq _

@[simp]
theorem hasNonsingularReduction_zero :
    HasNonsingularReduction hW (0 : W.Point) :=
  trivial

/-- Every point of the exact-pinned formal kernel belongs to the nonsingular-reduction domain. -/
theorem hasNonsingularReduction_of_mem_filtration
    [CharZero K]
    {P : W.Point} (hP : P ∈ filtration hW 0) :
    HasNonsingularReduction hW P := by
  rcases P with _ | ⟨x, y, h⟩
  · trivial
  · intro hx
    exact (hx ((some_mem_filtration (hW := hW) (n := 0)).mp hP)).elim

/-- Coordinatewise reduction on the canonical nonsingular-reduction domain.  Formal-kernel
points reduce to infinity; all other points reduce using the integral coordinates supplied by
`integral_of_not_mem`. -/
def nonsingularReduction
    (P : {P : W.Point // HasNonsingularReduction hW P}) :
    (adicRedCurve W₀).Point := by
  rcases P with ⟨_ | ⟨x, y, h⟩, hred⟩
  · exact 0
  · by_cases hx : exp (2 : ℤ) ≤ Valued.v x
    · exact 0
    · exact .some
        (res ⟨x, (integral_of_not_mem hW h.left hx).1⟩)
        (res ⟨y, (integral_of_not_mem hW h.left hx).2⟩)
        (hred hx)

@[simp]
theorem nonsingularReduction_zero :
    nonsingularReduction hW ⟨0, hasNonsingularReduction_zero hW⟩ = 0 :=
  rfl

theorem nonsingularReduction_some_of_mem
    {x y : v.adicCompletion K} {h : W.Nonsingular x y}
    (hred : HasNonsingularReduction hW (.some x y h))
    (hx : exp (2 : ℤ) ≤ Valued.v x) :
    nonsingularReduction hW ⟨.some x y h, hred⟩ = 0 := by
  simp only [nonsingularReduction, dif_pos hx]

theorem nonsingularReduction_some_of_not_mem
    {x y : v.adicCompletion K} {h : W.Nonsingular x y}
    (hred : HasNonsingularReduction hW (.some x y h))
    (hx : ¬ exp (2 : ℤ) ≤ Valued.v x) :
    nonsingularReduction hW ⟨.some x y h, hred⟩ =
      .some
        (res ⟨x, (integral_of_not_mem hW h.left hx).1⟩)
        (res ⟨y, (integral_of_not_mem hW h.left hx).2⟩)
        (hred hx) := by
  simp only [nonsingularReduction, dif_neg hx]

/-- The actual coordinatewise nonsingular reduction has exactly the formal filtration as its
zero fibre.  This statement does not assume good reduction or any Néron-model result. -/
theorem nonsingularReduction_eq_zero_iff
    [CharZero K]
    (P : W.Point) (hP : HasNonsingularReduction hW P) :
    nonsingularReduction hW ⟨P, hP⟩ = 0 ↔ P ∈ filtration hW 0 := by
  rcases P with _ | ⟨x, y, h⟩
  · exact iff_of_true rfl (zero_mem_filtration (hW := hW) (n := 0))
  · rw [some_mem_filtration]
    by_cases hx : exp (2 : ℤ) ≤ Valued.v x
    · exact iff_of_true (nonsingularReduction_some_of_mem hW hP hx) hx
    · refine iff_of_false ?_ hx
      rw [nonsingularReduction_some_of_not_mem hW hP hx]
      exact Point.some_ne_zero _

/-- The one group-law compatibility still needed to turn canonical coordinatewise reduction into
the identity-component reduction homomorphism.  It asserts both closure of the canonical domain
and additivity of the already-defined reduction function; no subgroup or map is supplied by the
hypothesis. -/
def NonsingularReductionIsAdditive : Prop :=
  ∀ (P Q : W.Point)
    (hP : HasNonsingularReduction hW P)
    (hQ : HasNonsingularReduction hW Q),
      ∃ hPQ : HasNonsingularReduction hW (P + Q),
        nonsingularReduction hW ⟨P + Q, hPQ⟩ =
          nonsingularReduction hW ⟨P, hP⟩ +
            nonsingularReduction hW ⟨Q, hQ⟩

omit [W.IsElliptic] [DecidableEq (v.adicCompletion K)] in
include hW in
private theorem residue_negY
    {x y : v.adicCompletion K}
    (hx : Valued.v x ≤ 1) (hy : Valued.v y ≤ 1)
    (hneg : Valued.v (W.negY x y) ≤ 1) :
    res ⟨W.negY x y, hneg⟩ =
      (adicRedCurve W₀).negY (res ⟨x, hx⟩) (res ⟨y, hy⟩) := by
  have hcoe : W.negY x y =
      ((W₀.toAffine).negY
        (⟨x, hx⟩ : v.adicCompletionIntegers K) ⟨y, hy⟩ :
          v.adicCompletion K) := by
    conv_lhs => rw [← hW]
    exact (W₀.toAffine).map_negY
      (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) ⟨x, hx⟩ ⟨y, hy⟩
  have hsub : (⟨W.negY x y, hneg⟩ : v.adicCompletionIntegers K) =
      (W₀.toAffine).negY ⟨x, hx⟩ ⟨y, hy⟩ :=
    Subtype.ext hcoe
  rw [hsub]
  exact ((W₀.toAffine).map_negY
    (IsLocalRing.residue (v.adicCompletionIntegers K)) ⟨x, hx⟩ ⟨y, hy⟩).symm

/-- The canonical nonsingular-reduction predicate is stable under negation. -/
theorem hasNonsingularReduction_neg
    {P : W.Point} (hP : HasNonsingularReduction hW P) :
    HasNonsingularReduction hW (-P) := by
  rcases P with _ | ⟨x, y, h⟩
  · exact hP
  · rw [Point.neg_some]
    intro hx
    have hxy := integral_of_not_mem hW h.left hx
    have hnegxy := integral_of_not_mem hW ((W.nonsingular_neg x y).mpr h).left hx
    rw [residue_negY hW hxy.1 hxy.2 hnegxy.2]
    exact (nonsingular_neg _ _).mpr (hP hx)

/-- The canonical subgroup of local points reducing to the nonsingular locus of the special
Weierstrass cubic.  Closure under addition is the sole content imported from
`NonsingularReductionIsAdditive`; zero, inverses, and containment of the formal kernel are
checked directly. -/
def nonsingularReductionSubgroup
    (hadd : NonsingularReductionIsAdditive hW) : AddSubgroup W.Point where
  carrier := {P | HasNonsingularReduction hW P}
  zero_mem' := hasNonsingularReduction_zero hW
  neg_mem' := hasNonsingularReduction_neg hW
  add_mem' {P Q} hP hQ := (hadd P Q hP hQ).choose

theorem filtration_le_nonsingularReductionSubgroup
    [CharZero K]
    (hadd : NonsingularReductionIsAdditive hW) :
    filtration hW 0 ≤ nonsingularReductionSubgroup hW hadd :=
  fun _ hP ↦ hasNonsingularReduction_of_mem_filtration hW hP

/-- Coordinatewise reduction as a homomorphism on its canonical nonsingular-reduction subgroup. -/
def nonsingularReductionHom
    (hadd : NonsingularReductionIsAdditive hW) :
    nonsingularReductionSubgroup hW hadd →+ (adicRedCurve W₀).Point where
  toFun P := nonsingularReduction hW ⟨P, P.property⟩
  map_zero' := rfl
  map_add' P Q := by
    exact (hadd P Q P.property Q.property).choose_spec

/-- The kernel of canonical nonsingular reduction is exactly the formal filtration, viewed in the
canonical identity subgroup. -/
theorem nonsingularReductionHom_ker
    [CharZero K]
    (hadd : NonsingularReductionIsAdditive hW) :
    (nonsingularReductionHom hW hadd).ker =
      (filtration hW 0).comap (nonsingularReductionSubgroup hW hadd).subtype := by
  ext P
  exact nonsingularReduction_eq_zero_iff hW P P.property

end WeierstrassCurve.Affine

namespace MazurTorsion.EllipticCurve

open MazurTorsion.IntegerPrimeSpecialization
open WeierstrassCurve WeierstrassCurve.Affine
open IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing

/-- Additive reduction forces the discriminant of Mathlib's actual reduced minimal equation to
vanish.  This is the first checked invariant needed to identify its singular cubic. -/
theorem reduction_Δ_eq_zero_of_hasAdditiveReduction
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {W : WeierstrassCurve K} [W.IsElliptic] [W.IsMinimal R]
    (hA : W.HasAdditiveReduction R) :
    (W.reduction R).Δ = 0 := by
  rw [WeierstrassCurve.reduction, WeierstrassCurve.map_Δ]
  rw [IsLocalRing.residue_eq_zero_iff]
  exact (valuation_lt_one_iff_mem (K := K) (maximalIdeal R) _).mp (by
    change valuation K (maximalIdeal R)
      (algebraMap R K (W.integralModel R).Δ) < 1
    rw [W.integralModel_Δ_eq R]
    exact hA.badReduction)

/-- Additive reduction also forces `c₄` of the actual reduced minimal equation to vanish.  In
residue characteristic different from two and three, this distinguishes the cuspidal additive
cubic from the nodal multiplicative cubic. -/
theorem reduction_c₄_eq_zero_of_hasAdditiveReduction
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {W : WeierstrassCurve K} [W.IsElliptic] [W.IsMinimal R]
    (hA : W.HasAdditiveReduction R) :
    (W.reduction R).c₄ = 0 := by
  rw [WeierstrassCurve.reduction, WeierstrassCurve.map_c₄]
  rw [IsLocalRing.residue_eq_zero_iff]
  exact (valuation_lt_one_iff_mem (K := K) (maximalIdeal R) _).mp (by
    change valuation K (maximalIdeal R)
      (algebraMap R K (W.integralModel R).c₄) < 1
    rw [W.integralModel_c₄_eq R]
    exact hA.additiveReduction)

local instance : DecidableEq
    (ResidueField (atFive.adicCompletionIntegers ℚ)) :=
  Classical.decEq _

local instance : DecidableEq
    (ResidueField (atEleven.adicCompletionIntegers ℚ)) :=
  Classical.decEq _

/-- Build the five-adic tame-additive reduction handoff from the canonical nonsingular-reduction
domain, actual coordinatewise reduction, an additive classification of the group of nonsingular
points of the singular special cubic, and the genuine component bound. -/
def TameAdditiveReductionDataAtFive.ofNonsingularReduction
    {W : Affine (atFive.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atFive.adicCompletionIntegers ℚ)}
    {hW : W₀.map
      (algebraMap (atFive.adicCompletionIntegers ℚ) (atFive.adicCompletion ℚ)) = W}
    [W.IsElliptic] [DecidableEq (atFive.adicCompletion ℚ)]
    (hadd : NonsingularReductionIsAdditive hW)
    (especial : (adicRedCurve W₀).Point ≃+
      ResidueField (atFive.adicCompletionIntegers ℚ))
    (hcomponent : Nat.card
      (W.Point ⧸ nonsingularReductionSubgroup hW hadd) ≤ 4) :
    TameAdditiveReductionDataAtFive hW where
  identitySubgroup := nonsingularReductionSubgroup hW hadd
  formalKernel_le_identity := filtration_le_nonsingularReductionSubgroup hW hadd
  identityReduction := especial.toAddMonoidHom.comp (nonsingularReductionHom hW hadd)
  identityReduction_ker := by
    ext P
    change especial (nonsingularReductionHom hW hadd P) = 0 ↔ _
    rw [← map_zero especial, especial.injective.eq_iff]
    exact nonsingularReduction_eq_zero_iff hW P P.property
  component_card_le_four := hcomponent

/-- The identical canonical construction at eleven, used by the order-35 route. -/
def TameAdditiveReductionDataAtEleven.ofNonsingularReduction
    {W : Affine (atEleven.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atEleven.adicCompletionIntegers ℚ)}
    {hW : W₀.map
      (algebraMap (atEleven.adicCompletionIntegers ℚ) (atEleven.adicCompletion ℚ)) = W}
    [W.IsElliptic] [DecidableEq (atEleven.adicCompletion ℚ)]
    (hadd : NonsingularReductionIsAdditive hW)
    (especial : (adicRedCurve W₀).Point ≃+
      ResidueField (atEleven.adicCompletionIntegers ℚ))
    (hcomponent : Nat.card
      (W.Point ⧸ nonsingularReductionSubgroup hW hadd) ≤ 4) :
    TameAdditiveReductionDataAtEleven hW where
  identitySubgroup := nonsingularReductionSubgroup hW hadd
  formalKernel_le_identity := filtration_le_nonsingularReductionSubgroup hW hadd
  identityReduction := especial.toAddMonoidHom.comp (nonsingularReductionHom hW hadd)
  identityReduction_ker := by
    ext P
    change especial (nonsingularReductionHom hW hadd P) = 0 ↔ _
    rw [← map_zero especial, especial.injective.eq_iff]
    exact nonsingularReduction_eq_zero_iff hW P P.property
  component_card_le_four := hcomponent

end MazurTorsion.EllipticCurve

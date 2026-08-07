/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.EllipticCurve.NonsingularReductionAdditive
import MazurTorsion.EllipticCurve.MinimalModelScaling
import MazurTorsion.EllipticCurve.TameAdditiveFiltration
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import Mathlib.Tactic.NormNum

/-!
# The tame additive contradiction at residue characteristic five

This is the prime-route consumer of the algebraic Néron filtration boundary.
It remains conditional on construction of that filtration from the actual
local elliptic curve.
-/

namespace MazurTorsion.PrimeOrder

open MazurTorsion.EllipticCurve
open MazurTorsion.IntegerPrimeSpecialization
open IsDiscreteValuationRing
open IsDedekindDomain.HeightOneSpectrum

universe u v

noncomputable local instance : DecidableEq
    (IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ)) :=
  Classical.decEq _

section ReductionType

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- **Named additive-reduction consumer for the tame Tate algorithm.** Additive reduction and
integral `j` give the three valuation inequalities available from the exact-pin reduction API:
positive discriminant valuation, positive `c₄` valuation, and the potentially-good comparison
`v(c₄)³ ≤ v(Δ)`.  This package does not determine a Kodaira symbol or component order. -/
theorem tateAlgorithm_valuationInput_of_hasAdditiveReduction
    {W : WeierstrassCurve K} [W.IsElliptic]
    (hA : W.HasAdditiveReduction R)
    (hj : valuation K (maximalIdeal R) W.j ≤ 1) :
    valuation K (maximalIdeal R) W.Δ < 1 ∧
      valuation K (maximalIdeal R) W.c₄ < 1 ∧
      valuation K (maximalIdeal R) W.c₄ ^ 3 ≤
        valuation K (maximalIdeal R) W.Δ :=
  ⟨hA.badReduction, hA.additiveReduction,
    valuation_c₄_pow_three_le_valuation_Δ_of_valuation_j_le_one hj⟩

/-- **Named minimality consumer for the tame Tate algorithm.** In the additive branch, the
minimal equation cannot have all five coefficients remain integral after a further weighted
scaling by `u⁻¹` with `v(u) < 1`.  Completing the marked component theorem still requires the
subsequent translation, blowup, Kodaira classification, and component-incidence steps. -/
theorem tateAlgorithm_coefficientObstruction_of_hasAdditiveReduction
    {W : WeierstrassCurve K} [W.IsElliptic]
    (hA : W.HasAdditiveReduction R)
    (u : Kˣ)
    (hu : valuation K (maximalIdeal R) (u : K) < 1) :
    ¬ WeightedCoefficientsIntegralAfterScale (R := R) W u := by
  letI : W.IsMinimal R := hA.toIsMinimal
  exact tateAlgorithm_minimalityCoefficientObstruction u hu

/-- Multiplicative reduction forces the `j`-invariant to have valuation strictly greater than
one.  This is the elementary bridge from the integral-`j` formulation of potentially good
reduction to the reduction-type trichotomy. -/
theorem valuation_j_gt_one_of_hasMultiplicativeReduction
    {W : WeierstrassCurve K} [W.IsElliptic]
    (hW : W.HasMultiplicativeReduction R) :
    1 < valuation K (maximalIdeal R) W.j := by
  rw [WeierstrassCurve.j]
  simp only [Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_pow,
    WeierstrassCurve.coe_Δ',
    hW.multiplicativeReduction, one_pow, mul_one]
  exact one_lt_inv_iff₀.mpr
    ⟨(valuation K (maximalIdeal R)).pos_iff.mpr (by
        simpa only [WeierstrassCurve.coe_Δ'] using W.Δ'.ne_zero),
      hW.badReduction⟩

/-- An integral `j`-invariant excludes multiplicative reduction of a minimal equation. -/
theorem not_hasMultiplicativeReduction_of_valuation_j_le_one
    {W : WeierstrassCurve K} [W.IsElliptic]
    (hj : valuation K (maximalIdeal R) W.j ≤ 1) :
    ¬ W.HasMultiplicativeReduction R := by
  intro hW
  exact (not_lt_of_ge hj) (valuation_j_gt_one_of_hasMultiplicativeReduction hW)

end ReductionType

/-- Integral `j` upgrades a minimal equation to good reduction whenever the
marked point's exact order is impossible in the additive branch.

This is the shared reduction-type engine behind the prime route at five and
the order-35 route at eleven.  It isolates the only residue-characteristic
dependent input as an exact-order obstruction under additive reduction. -/
theorem hasGoodReduction_of_valuation_j_le_one_of_additiveOrderObstruction
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {W : WeierstrassCurve K} [W.IsElliptic] [W.IsMinimal R]
    (hj : valuation K (maximalIdeal R) W.j ≤ 1)
    {G : Type u} [AddCommGroup G]
    (P : G) (N : ℕ)
    (hadditive : W.HasAdditiveReduction R → addOrderOf P ≠ N)
    (horder : addOrderOf P = N) :
    W.HasGoodReduction R := by
  rcases W.hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction R with
    hgood | hmultiplicative | hA
  · exact hgood
  · exact (not_hasMultiplicativeReduction_of_valuation_j_le_one
      hj hmultiplicative).elim
  · exact (hadditive hA horder).elim

/-- A tame additive filtration with five-element residue group has no point
of prime exact order at least eleven. -/
theorem addOrderOf_ne_prime_ge_eleven_of_tameAdditiveFiltrationAtFive
    {G : Type u} [AddCommGroup G]
    (F : TameAdditiveFiltrationData.{u, v} G)
    (hresidue : Nat.card F.ResidueAdditive = 5)
    (P : G) (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  letI : AddCommGroup F.Component := F.componentAddCommGroup
  letI : Finite F.Component := F.componentFinite
  letI : AddCommGroup F.ResidueAdditive := F.residueAddCommGroup
  letI : Finite F.ResidueAdditive := F.residueFinite
  intro horder
  have hcomponentCoprime : N.Coprime (Nat.card F.Component) :=
    Nat.coprime_of_lt_prime Nat.card_pos.ne'
      (lt_of_le_of_lt F.component_card_le_four (by omega)) hprime
  have hresidueCoprime : N.Coprime (Nat.card F.ResidueAdditive) := by
    rw [hresidue]
    exact Nat.coprime_of_lt_prime (by norm_num) (by omega) hprime
  have hzero := F.point_eq_zero_of_coprime_card hprime.ne_zero
    hcomponentCoprime hresidueCoprime horder
  rw [hzero] at horder
  simp at horder
  omega

/-- The prime-five additive contradiction needs only a component exponent, not a cardinality
bound for a separately constructed component group.  The tame universal exponent `12` is coprime
to every prime order at least eleven, while the identity-component residue group has cardinality
five. -/
theorem addOrderOf_ne_prime_ge_eleven_of_componentExponentTwelveAtFive
    {G : Type u} [AddCommGroup G]
    (identitySubgroup : AddSubgroup G)
    {ResidueAdditive : Type v} [AddCommGroup ResidueAdditive]
    [Finite ResidueAdditive]
    (identityReduction : identitySubgroup →+ ResidueAdditive)
    (formalKernel : AddSubgroup identitySubgroup)
    (identityReduction_ker : identityReduction.ker = formalKernel)
    (formalKernel_torsionFree :
      ∀ Q : formalKernel, IsOfFinAddOrder Q → Q = 0)
    (hresidue : Nat.card ResidueAdditive = 5)
    (P : G) (hcomponent : 12 • P ∈ identitySubgroup)
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  intro horder
  have hcomponentCoprime : N.Coprime 12 := by
    rw [hprime.coprime_iff_not_dvd]
    intro hdvd
    have hle : N ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
    have hcases : N = 11 ∨ N = 12 := by omega
    rcases hcases with rfl | rfl
    · norm_num at hdvd
    · exact (by decide : ¬ Nat.Prime 12) hprime
  have hresidueCoprime : N.Coprime (Nat.card ResidueAdditive) := by
    rw [hresidue]
    exact Nat.coprime_of_lt_prime (by norm_num) (by omega) hprime
  have hzero := point_eq_zero_of_coprime_component_exponent
    identitySubgroup identityReduction formalKernel identityReduction_ker
    formalKernel_torsionFree hprime.ne_zero hcomponentCoprime
    hresidueCoprime hcomponent horder
  rw [hzero] at horder
  simp at horder
  omega

/-- The canonical five-adic prime-order contradiction through the component-exponent handoff.

Coordinatewise nonsingular reduction fixes the identity subgroup and reduction homomorphism, and
the exact-pinned unramified theorem proves torsion-freeness of the formal kernel.  Consequently the
only component geometry required for the marked point is `12 • P ∈ E₀`; neither finiteness nor a
cardinality bound for the full component quotient appears in this interface. -/
theorem
    addOrderOf_ne_prime_ge_eleven_of_nonsingularReduction_of_componentExponentTwelveAtFive
    {W : WeierstrassCurve.Affine (atFive.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atFive.adicCompletionIntegers ℚ)}
    (hW : W₀.map
      (algebraMap (atFive.adicCompletionIntegers ℚ)
        (atFive.adicCompletion ℚ)) = W)
    [W.IsElliptic] [DecidableEq (atFive.adicCompletion ℚ)]
    (especial : (WeierstrassCurve.Affine.adicRedCurve W₀).Point ≃+
      IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ))
    (P : W.Point)
    (hcomponent : 12 • P ∈
      WeierstrassCurve.Affine.nonsingularReductionSubgroup hW
        (WeierstrassCurve.Affine.nonsingularReduction_isAdditive hW))
    (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  let residueEquivZMod :
      IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ) ≃ ZMod 5 :=
    ((atFive.residueFieldEquivAdicCompletionIntegers (K := ℚ)).symm.trans
      MazurTorsion.IntegerPrimeSpecialization.residueFiveAlgEquiv.toRingEquiv).toEquiv
  letI : Finite
      (IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ)) :=
    Finite.of_equiv (ZMod 5) residueEquivZMod.symm
  let identitySubgroup : AddSubgroup W.Point :=
    WeierstrassCurve.Affine.nonsingularReductionSubgroup hW
      (WeierstrassCurve.Affine.nonsingularReduction_isAdditive hW)
  let identityReduction : identitySubgroup →+
      IsLocalRing.ResidueField (atFive.adicCompletionIntegers ℚ) :=
    especial.toAddMonoidHom.comp
      (WeierstrassCurve.Affine.nonsingularReductionHom hW
        (WeierstrassCurve.Affine.nonsingularReduction_isAdditive hW))
  let formalKernel : AddSubgroup identitySubgroup :=
    (WeierstrassCurve.Affine.filtration hW 0).comap identitySubgroup.subtype
  apply addOrderOf_ne_prime_ge_eleven_of_componentExponentTwelveAtFive
    identitySubgroup identityReduction formalKernel
  · ext Q
    change especial
      (WeierstrassCurve.Affine.nonsingularReductionHom hW
        (WeierstrassCurve.Affine.nonsingularReduction_isAdditive hW) Q) = 0 ↔ _
    rw [← map_zero especial, especial.injective.eq_iff]
    exact WeierstrassCurve.Affine.nonsingularReduction_eq_zero_iff hW Q Q.property
  · intro Q hQ
    apply Subtype.ext
    apply Subtype.ext
    exact MazurTorsion.IntegerPrimeSpecialization.torsion_eq_zero_of_mem_formalKernel_atFive
      hW Q.property
      (identitySubgroup.subtype.isOfFinAddOrder
        (formalKernel.subtype.isOfFinAddOrder hQ))
  · exact MazurTorsion.EllipticCurve.TameAdditiveReductionDataAtFive.residue_natCard
  · exact hcomponent
  · exact hprime
  · exact hN

/-- Integral `j`, the actual tame additive Néron filtration, and a marked prime-order point
upgrade a minimal equation to good reduction.  The proof uses Mathlib's exhaustive
good/multiplicative/additive trichotomy: integral `j` excludes the multiplicative branch and the
two finite quotients plus torsion-free formal kernel exclude the additive branch.

This is the checked local consumer expected after the formal-immersion argument supplies
potentially good reduction.  Constructing `F` from the genuine Néron model remains the geometric
input; it is not hidden in this statement. -/
theorem hasGoodReduction_of_valuation_j_le_one_of_tameAdditiveFiltrationAtFive
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {W : WeierstrassCurve K} [W.IsElliptic] [W.IsMinimal R]
    (hj : valuation K (maximalIdeal R) W.j ≤ 1)
    {G : Type u} [AddCommGroup G]
    (F : W.HasAdditiveReduction R → TameAdditiveFiltrationData.{u, v} G)
    (hresidue : ∀ hW, Nat.card (F hW).ResidueAdditive = 5)
    (P : G) (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N)
    (horder : addOrderOf P = N) :
    W.HasGoodReduction R := by
  exact hasGoodReduction_of_valuation_j_le_one_of_additiveOrderObstruction
    hj P N
      (fun hA ↦ addOrderOf_ne_prime_ge_eleven_of_tameAdditiveFiltrationAtFive
        (F hA) (hresidue hA) P N hprime hN)
      horder

end MazurTorsion.PrimeOrder

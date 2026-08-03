/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.PrimeOrder.FiniteFieldFiveOrder
import MazurTorsion.PrimeOrder.TameAdditiveAtFive
import MazurTorsion.PrimeOrder.TorsionSpecialization
import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

/-!
# The prime-order contradiction after good reduction at five

This module joins the unramified formal-kernel specialization theorem to the
checked enumeration of elliptic curves over `F_5`.  It is the downstream
consumer required by the formal-immersion route once the preceding local
argument has supplied an integral model with good reduction at five.
-/

open WeierstrassCurve

namespace MazurTorsion.PrimeOrder

open WeierstrassCurve.Affine
open MazurTorsion.IntegerPrimeSpecialization
open IsDiscreteValuationRing
open IsDedekindDomain.HeightOneSpectrum

/-- If an integral model has good reduction at five, none of its rational
torsion points has exact order at least eleven. -/
theorem rationalPoint_addOrderOf_ne_of_eleven_le_of_goodReductionAtFive
    {E : Affine ℚ} {W₀ : WeierstrassCurve ℤ}
    (hE : W₀.map (algebraMap ℤ ℚ) = E)
    [E.IsElliptic] [(redCurve atFive W₀).IsElliptic]
    {P : E.Point} {N : ℕ} (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  intro horder
  have hP : IsOfFinAddOrder P := addOrderOf_pos_iff.mp (by
    rw [horder]
    omega)
  letI : (reductionCurveAtFive W₀).IsElliptic := reductionCurveAtFive_isElliptic W₀
  apply zmod_five_addOrderOf_ne_of_eleven_le
    (reductionCurveAtFive W₀) (reductionAtFiveToZMod hE P) N hN
  exact (specializedPointZMod_addOrderOf_eq_atFive_of_goodReduction hE hP).trans horder

/-- Coefficientwise base change of a rational Weierstrass equation to the five-adic
completion. -/
noncomputable abbrev completionAtFive (E : WeierstrassCurve ℚ) :
    WeierstrassCurve (atFive.adicCompletion ℚ) :=
  E.toAffine ⁄ (atFive.adicCompletion ℚ)

instance completionAtFive_isElliptic
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (completionAtFive E).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  dsimp only [completionAtFive, WeierstrassCurve.Affine.baseChange,
    WeierstrassCurve.baseChange]
  rw [WeierstrassCurve.map_Δ]
  exact E.isUnit_Δ.map _

/-- The admissible variable change selected by Mathlib's existence proof for a minimal equation
over the five-adic valuation ring. -/
noncomputable def minimalCompletionChangeAtFive (E : WeierstrassCurve ℚ) :
    WeierstrassCurve.VariableChange (atFive.adicCompletion ℚ) :=
  ((completionAtFive E).exists_isMinimal
    (atFive.adicCompletionIntegers ℚ)).choose

/-- The minimal five-adic equation selected by Mathlib after coefficientwise base change from a
rational Weierstrass equation. -/
noncomputable abbrev minimalCompletionAtFive (E : WeierstrassCurve ℚ) :
    WeierstrassCurve (atFive.adicCompletion ℚ) :=
  minimalCompletionChangeAtFive E • completionAtFive E

/-- The named change used here is definitionally the one in Mathlib's `minimal` construction. -/
theorem minimalCompletionAtFive_eq_mathlibMinimal (E : WeierstrassCurve ℚ) :
    minimalCompletionAtFive E =
      (completionAtFive E).minimal (atFive.adicCompletionIntegers ℚ) :=
  rfl

noncomputable instance minimalCompletionAtFive_isMinimal (E : WeierstrassCurve ℚ) :
    (minimalCompletionAtFive E).IsMinimal (atFive.adicCompletionIntegers ℚ) := by
  exact ((completionAtFive E).exists_isMinimal
    (atFive.adicCompletionIntegers ℚ)).choose_spec

noncomputable instance minimalCompletionAtFive_isElliptic
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (minimalCompletionAtFive E).IsElliptic := by
  dsimp only [minimalCompletionAtFive]
  infer_instance

/-- Transport a rational point first into the five-adic completion and then through the inverse
of the admissible variable change defining Mathlib's selected minimal equation. -/
noncomputable def minimalCompletionPointAtFive
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    [DecidableEq (atFive.adicCompletion ℚ)]
    (P : E.toAffine.Point) :
    (minimalCompletionAtFive E).toAffine.Point :=
  (Point.equivVariableChange (completionAtFive E)
    (minimalCompletionChangeAtFive E)).symm
    (E.toAffine.pointMap (atFive.adicCompletion ℚ) P)

/-- Base change to the five-adic completion and passage to the selected minimal equation preserve
the exact additive order of the marked rational point. -/
theorem minimalCompletionPointAtFive_addOrderOf
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    [DecidableEq (atFive.adicCompletion ℚ)]
    (P : E.toAffine.Point) :
    addOrderOf (minimalCompletionPointAtFive E P) = addOrderOf P := by
  rw [minimalCompletionPointAtFive, AddEquiv.addOrderOf_eq]
  exact addOrderOf_injective _
    (pointMap_injective E.toAffine (atFive.adicCompletion ℚ)) P

/-- A minimal elliptic curve over the completion of `ℚ` at five with good reduction has no
point of exact order at least eleven.

The integral model is Mathlib's `integralModel` over the completed valuation ring.  Good
reduction makes that integral equation elliptic, so the exact-pinned `adicRed` theorem preserves
the order of torsion.  Finally, the canonical residue-field equivalence
`ResidueField 𝒪₅ ≃+* ZMod 5` transports the reduced point to the checked finite enumeration.

This theorem starts after good reduction has been established.  It does not construct a minimal
model, prove integral `j`, or build the additive Néron filtration used to reach good reduction. -/
theorem completionPoint_addOrderOf_ne_of_eleven_le_of_hasGoodReductionAtFive
    {W : WeierstrassCurve (atFive.adicCompletion ℚ)}
    [W.IsElliptic] [W.IsMinimal (atFive.adicCompletionIntegers ℚ)]
    [DecidableEq (atFive.adicCompletion ℚ)]
    (hgood : W.HasGoodReduction (atFive.adicCompletionIntegers ℚ))
    (P : W.toAffine.Point) (N : ℕ) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  classical
  let W₀ : WeierstrassCurve (atFive.adicCompletionIntegers ℚ) :=
    W.integralModel (atFive.adicCompletionIntegers ℚ)
  have hW : W₀.map (algebraMap (atFive.adicCompletionIntegers ℚ)
      (atFive.adicCompletion ℚ)) = W := by
    simpa only [W₀, WeierstrassCurve.baseChange] using
      W.baseChange_integralModel_eq (atFive.adicCompletionIntegers ℚ)
  letI : (W.reduction (atFive.adicCompletionIntegers ℚ)).IsElliptic :=
    (W.hasGoodReduction_iff_isElliptic_reduction
      (atFive.adicCompletionIntegers ℚ)).mp hgood
  letI : W₀.IsElliptic := by
    rw [WeierstrassCurve.isElliptic_iff]
    apply (IsLocalRing.residue_ne_zero_iff_isUnit W₀.Δ).mp
    have hΔ := (W.reduction
      (atFive.adicCompletionIntegers ℚ)).isUnit_Δ.ne_zero
    simpa only [WeierstrassCurve.reduction, WeierstrassCurve.map_Δ, W₀] using hΔ
  let e₅ : IsLocalRing.ResidueField
      (atFive.adicCompletionIntegers ℚ) ≃+* ZMod 5 :=
    (atFive.residueFieldEquivAdicCompletionIntegers (K := ℚ)).symm.trans
      residueFiveAlgEquiv.toRingEquiv
  letI : Algebra (atFive.adicCompletionIntegers ℚ) (ZMod 5) :=
    (e₅.toRingHom.comp
      (IsLocalRing.residue (atFive.adicCompletionIntegers ℚ))).toAlgebra
  let e₅Alg : IsLocalRing.ResidueField
      (atFive.adicCompletionIntegers ℚ) ≃ₐ[atFive.adicCompletionIntegers ℚ]
        ZMod 5 :=
    { e₅ with
      commutes' := fun _ ↦ rfl }
  let W₅ : WeierstrassCurve (ZMod 5) :=
    W₀.map (algebraMap (atFive.adicCompletionIntegers ℚ) (ZMod 5))
  letI : W₅.IsElliptic := by
    dsimp only [W₅]
    infer_instance
  let redPointEquiv :
      (adicRedCurve W₀).Point ≃+ W₅.toAffine.Point :=
    Point.mapEquiv (W' := W₀.toAffine) e₅Alg
  intro horder
  have hP : IsOfFinAddOrder P := addOrderOf_pos_iff.mp (by
    rw [horder]
    omega)
  have hredOrder : addOrderOf (adicRed hW P) = addOrderOf P :=
    addOrderOf_adicRed hW (by norm_num)
      five_mem_completion_maximalIdeal
      five_not_mem_completion_maximalIdeal_pow_four hP
  apply zmod_five_addOrderOf_ne_of_eleven_le
    W₅ (redPointEquiv (adicRed hW P)) N hN
  exact (AddEquiv.addOrderOf_eq redPointEquiv (adicRed hW P)).trans
    (hredOrder.trans horder)

/-- The completion-level prime-order endpoint after the integral-`j` and tame
additive-filtration inputs have been supplied.  The reduction trichotomy first upgrades the
minimal equation to good reduction; the preceding completion theorem then specializes the same
marked point to the checked finite field at five.

The filtration argument remains an explicit input: a later Néron-model consumer must instantiate
`F` with the actual component, smooth-residue, and formal-kernel filtration of `W`. -/
theorem
    completionPoint_addOrderOf_ne_of_eleven_le_of_valuation_j_le_one_of_tameAdditiveFiltrationAtFive
    {W : WeierstrassCurve (atFive.adicCompletion ℚ)}
    [W.IsElliptic] [W.IsMinimal (atFive.adicCompletionIntegers ℚ)]
    [DecidableEq (atFive.adicCompletion ℚ)]
    (hj : valuation (atFive.adicCompletion ℚ)
      (IsDiscreteValuationRing.maximalIdeal (atFive.adicCompletionIntegers ℚ)) W.j ≤ 1)
    (F : W.HasAdditiveReduction (atFive.adicCompletionIntegers ℚ) →
      MazurTorsion.EllipticCurve.TameAdditiveFiltrationData W.toAffine.Point)
    (hresidue : ∀ hW, Nat.card (F hW).ResidueAdditive = 5)
    (P : W.toAffine.Point) (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  intro horder
  have hgood : W.HasGoodReduction (atFive.adicCompletionIntegers ℚ) :=
    hasGoodReduction_of_valuation_j_le_one_of_tameAdditiveFiltrationAtFive
      hj F hresidue P N hprime hN horder
  exact completionPoint_addOrderOf_ne_of_eleven_le_of_hasGoodReductionAtFive
    hgood P N hN horder

/-- The rational-point version of the local completion endpoint.  It transports the marked point
to Mathlib's selected minimal five-adic equation, preserving exact order, before invoking the
integral-`j` and tame-additive-filtration contradiction.

The only remaining local inputs are stated on that concrete minimal equation: `hj` and `F` must
ultimately come from the modular potentially-good theorem and the genuine Néron model. -/
theorem rationalPoint_addOrderOf_ne_of_eleven_le_of_minimalCompletionInputsAtFive
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    [DecidableEq (atFive.adicCompletion ℚ)]
    (hj : valuation (atFive.adicCompletion ℚ)
      (IsDiscreteValuationRing.maximalIdeal (atFive.adicCompletionIntegers ℚ))
        (minimalCompletionAtFive E).j ≤ 1)
    (F : (minimalCompletionAtFive E).HasAdditiveReduction
      (atFive.adicCompletionIntegers ℚ) →
        MazurTorsion.EllipticCurve.TameAdditiveFiltrationData
          (minimalCompletionAtFive E).toAffine.Point)
    (hresidue : ∀ hW, Nat.card (F hW).ResidueAdditive = 5)
    (P : E.toAffine.Point) (N : ℕ) (hprime : N.Prime) (hN : 11 ≤ N) :
    addOrderOf P ≠ N := by
  intro horder
  apply
    completionPoint_addOrderOf_ne_of_eleven_le_of_valuation_j_le_one_of_tameAdditiveFiltrationAtFive
      hj F hresidue (minimalCompletionPointAtFive E P) N hprime hN
  exact (minimalCompletionPointAtFive_addOrderOf E P).trans horder

end MazurTorsion.PrimeOrder

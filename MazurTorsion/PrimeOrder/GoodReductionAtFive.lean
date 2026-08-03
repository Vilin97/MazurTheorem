/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.PrimeOrder.FiniteFieldFiveOrder
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

end MazurTorsion.PrimeOrder

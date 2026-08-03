/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderThirtyFiveFiniteFieldOrder
import MazurTorsion.EllipticCurve.TameAdditiveFiltration
import MazurTorsion.EllipticCurve.NonsingularReduction
import MazurTorsion.PrimeOrder.TorsionSpecialization

/-!
# Rational points of order thirty-five

This module reserves the permanent library destination for the order-35
challenge. A solution belongs here; the published challenge module can then
become a thin, immutable bridge to that theorem.
-/

namespace MazurTorsion.OrderThirtyFive

universe u v

open WeierstrassCurve
open WeierstrassCurve.Affine
open MazurTorsion.IntegerPrimeSpecialization
open MazurTorsion.EllipticCurve

private instance : Fact (Nat.Prime 11) := ⟨by decide⟩

noncomputable local instance : DecidableEq
    (IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ)) :=
  Classical.decEq _

/-- The checked `F_11` enumeration rules out a specialized point of exact
order 35.  The remaining rational theorem must construct this point through
the squarefree-level formal-immersion and Néron-specialization route. -/
theorem reductionAtEleven_addOrderOf_ne_thirtyFive
    (W : WeierstrassCurve (ZMod 11)) [W.IsElliptic]
    (P : W.toAffine.Point) :
    addOrderOf P ≠ 35 :=
  zmod_eleven_addOrderOf_ne_thirtyFive W P

/-- If an integral model has good reduction at eleven, a rational point on
its generic fibre cannot have exact order 35.  This is the checked join
between unramified specialization and the exhaustive `F_11` certificate. -/
theorem rationalPoint_addOrderOf_ne_thirtyFive_of_goodReductionAtEleven
    {E : Affine ℚ} {W₀ : WeierstrassCurve ℤ}
    (hE : W₀.map (algebraMap ℤ ℚ) = E)
    [E.IsElliptic] [(redCurve atEleven W₀).IsElliptic]
    {P : E.Point} :
    addOrderOf P ≠ 35 := by
  intro horder
  have hP : IsOfFinAddOrder P := addOrderOf_pos_iff.mp (by
    rw [horder]
    norm_num)
  letI : (MazurTorsion.PrimeOrder.reductionCurveAtEleven W₀).IsElliptic :=
    MazurTorsion.PrimeOrder.reductionCurveAtEleven_isElliptic W₀
  apply reductionAtEleven_addOrderOf_ne_thirtyFive
    (MazurTorsion.PrimeOrder.reductionCurveAtEleven W₀)
    (MazurTorsion.PrimeOrder.reductionAtElevenToZMod hE P)
  exact
    (MazurTorsion.PrimeOrder.specializedPointZMod_addOrderOf_eq_atEleven_of_goodReduction
      hE hP).trans horder

/-- A tame additive filtration with eleven-element residue group has no
point of exact order 35. This is the local bad-fibre consumer that the future
Néron-model construction must instantiate. -/
theorem addOrderOf_ne_thirtyFive_of_tameAdditiveFiltrationAtEleven
    {G : Type u} [AddCommGroup G]
    (F : TameAdditiveFiltrationData.{u, v} G)
    (hresidue : Nat.card F.ResidueAdditive = 11)
    (P : G) :
    addOrderOf P ≠ 35 := by
  letI : AddCommGroup F.Component := F.componentAddCommGroup
  letI : Finite F.Component := F.componentFinite
  letI : AddCommGroup F.ResidueAdditive := F.residueAddCommGroup
  letI : Finite F.ResidueAdditive := F.residueFinite
  intro horder
  have hcomponentPos : 0 < Nat.card F.Component := Nat.card_pos
  have hcomponentLe : Nat.card F.Component ≤ 4 := F.component_card_le_four
  have hcomponentCoprime : (35 : ℕ).Coprime (Nat.card F.Component) := by
    have hc : Nat.card F.Component = 1 ∨ Nat.card F.Component = 2 ∨
        Nat.card F.Component = 3 ∨ Nat.card F.Component = 4 := by
      omega
    rcases hc with hc | hc | hc | hc <;> rw [hc] <;> norm_num
  have hresidueCoprime : (35 : ℕ).Coprime (Nat.card F.ResidueAdditive) := by
    rw [hresidue]
    norm_num
  have hzero := F.point_eq_zero_of_coprime_card (by norm_num)
    hcomponentCoprime hresidueCoprime horder
  rw [hzero] at horder
  norm_num at horder

/-- The order-35 additive-fibre contradiction from the canonical eleven-adic reduction data.
The component is the quotient by the specified identity subgroup, reduction targets the actual
eleven-adic residue field, and formal-kernel torsion-freeness comes from the checked
unramified formal-group theorem. -/
theorem addOrderOf_ne_thirtyFive_of_tameAdditiveReductionDataAtEleven
    {W : Affine (atEleven.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atEleven.adicCompletionIntegers ℚ)}
    (hW : W₀.map
      (algebraMap (atEleven.adicCompletionIntegers ℚ)
        (atEleven.adicCompletion ℚ)) = W)
    [W.IsElliptic] [DecidableEq (atEleven.adicCompletion ℚ)]
    (D : TameAdditiveReductionDataAtEleven hW) (P : W.Point) :
    addOrderOf P ≠ 35 :=
  addOrderOf_ne_thirtyFive_of_tameAdditiveFiltrationAtEleven
    D.toTameAdditiveFiltrationData
    TameAdditiveReductionDataAtEleven.residue_natCard P

/-- The order-35 additive-fibre contradiction using only canonical coordinatewise nonsingular
reduction.  The identity subgroup and its reduction map are constructed, rather than supplied;
the remaining inputs are the group-law compatibility of that reduction, the additive
classification of the actual special cubic, and the genuine component bound. -/
theorem addOrderOf_ne_thirtyFive_of_nonsingularReductionAtEleven
    {W : Affine (atEleven.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atEleven.adicCompletionIntegers ℚ)}
    (hW : W₀.map
      (algebraMap (atEleven.adicCompletionIntegers ℚ)
        (atEleven.adicCompletion ℚ)) = W)
    [W.IsElliptic] [DecidableEq (atEleven.adicCompletion ℚ)]
    (hadd : NonsingularReductionIsAdditive hW)
    (especial : (adicRedCurve W₀).Point ≃+
      IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ))
    (hcomponent : Nat.card
      (W.Point ⧸ nonsingularReductionSubgroup hW hadd) ≤ 4)
    (P : W.Point) :
    addOrderOf P ≠ 35 :=
  addOrderOf_ne_thirtyFive_of_tameAdditiveReductionDataAtEleven hW
    (TameAdditiveReductionDataAtEleven.ofNonsingularReduction
      hadd especial hcomponent) P

end MazurTorsion.OrderThirtyFive

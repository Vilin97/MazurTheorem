/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.PicardAbelJacobi
import MazurTorsion.Kubert.OrderTwentyFiveCuspDivisorLattice

/-!
# The order-twenty-five cusp divisors in the Picard group

This file connects the explicit determinant-`71` lattice to the checked
Weil-divisor and Picard-group infrastructure.  It defines the five cyclic
cusp divisors, packages the precise principal-divisor witnesses that a
geometric modular-unit construction must provide, and maps those witnesses
through the Abel--Jacobi divisor homomorphism.

No principal-divisor witness is asserted here.  The predicate
`orderTwentyFiveCuspPrincipalDivisorRelations` is the geometric interface;
`orderTwentyFive_picardCuspidalSubgroupZModEquiv` is its named descent
consumer.
-/

namespace MazurTorsion.Kubert

open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open MazurTorsion.AlgebraicGeometry

/-- The first cyclic divisor with cusp-order vector `(3, -1, 1, -2, -1)`. -/
noncomputable def orderTwentyFiveCuspDivisorZero
    {Y : Type*} (c0 c1 c2 c3 c4 : Y) :
    WeilDivisor Y :=
  3 • ofPoint c0 - ofPoint c1 + ofPoint c2 - 2 • ofPoint c3 - ofPoint c4

/-- The first rotation of the order-twenty-five cusp divisor. -/
noncomputable def orderTwentyFiveCuspDivisorOne
    {Y : Type*} (c0 c1 c2 c3 c4 : Y) :
    WeilDivisor Y :=
  3 • ofPoint c1 - ofPoint c2 + ofPoint c3 - 2 • ofPoint c4 - ofPoint c0

/-- The second rotation of the order-twenty-five cusp divisor. -/
noncomputable def orderTwentyFiveCuspDivisorTwo
    {Y : Type*} (c0 c1 c2 c3 c4 : Y) :
    WeilDivisor Y :=
  3 • ofPoint c2 - ofPoint c3 + ofPoint c4 - 2 • ofPoint c0 - ofPoint c1

/-- The third rotation of the order-twenty-five cusp divisor. -/
noncomputable def orderTwentyFiveCuspDivisorThree
    {Y : Type*} (c0 c1 c2 c3 c4 : Y) :
    WeilDivisor Y :=
  3 • ofPoint c3 - ofPoint c4 + ofPoint c0 - 2 • ofPoint c1 - ofPoint c2

/-- The fourth rotation of the order-twenty-five cusp divisor. -/
noncomputable def orderTwentyFiveCuspDivisorFour
    {Y : Type*} (c0 c1 c2 c3 c4 : Y) :
    WeilDivisor Y :=
  3 • ofPoint c4 - ofPoint c0 + ofPoint c1 - 2 • ofPoint c2 - ofPoint c3

/-- Exact geometric input for the cusp-lattice calculation: each of the five
cyclic cusp divisors is the principal divisor of a supplied function. -/
def orderTwentyFiveCuspPrincipalDivisorRelations
    {Y G : Type*} [AddCommGroup G]
    (S : WeilDivisor.OrderSystem Y G) (c0 c1 c2 c3 c4 : Y) : Prop :=
  ∃ g0 g1 g2 g3 g4 : G,
    orderTwentyFiveCuspDivisorZero c0 c1 c2 c3 c4 = S.principalDivisor g0 ∧
    orderTwentyFiveCuspDivisorOne c0 c1 c2 c3 c4 = S.principalDivisor g1 ∧
    orderTwentyFiveCuspDivisorTwo c0 c1 c2 c3 c4 = S.principalDivisor g2 ∧
    orderTwentyFiveCuspDivisorThree c0 c1 c2 c3 c4 = S.principalDivisor g3 ∧
    orderTwentyFiveCuspDivisorFour c0 c1 c2 c3 c4 = S.principalDivisor g4

/-- Any additive divisor map killing the five explicit cusp divisors produces
the abstract cyclic cusp relations. -/
theorem orderTwentyFiveCuspDivisorRelations_of_divisorMap_eq_zero
    {Y A : Type*} [AddCommGroup A] (f : WeilDivisor Y →+ A)
    (c0 c1 c2 c3 c4 : Y)
    (h0 : f (orderTwentyFiveCuspDivisorZero c0 c1 c2 c3 c4) = 0)
    (h1 : f (orderTwentyFiveCuspDivisorOne c0 c1 c2 c3 c4) = 0)
    (h2 : f (orderTwentyFiveCuspDivisorTwo c0 c1 c2 c3 c4) = 0)
    (h3 : f (orderTwentyFiveCuspDivisorThree c0 c1 c2 c3 c4) = 0)
    (h4 : f (orderTwentyFiveCuspDivisorFour c0 c1 c2 c3 c4) = 0) :
    orderTwentyFiveCuspDivisorRelations
      (f (ofPoint c0)) (f (ofPoint c1)) (f (ofPoint c2))
      (f (ofPoint c3)) (f (ofPoint c4)) := by
  exact ⟨
    by simpa [orderTwentyFiveCuspDivisorZero] using h0,
    by simpa [orderTwentyFiveCuspDivisorOne] using h1,
    by simpa [orderTwentyFiveCuspDivisorTwo] using h2,
    by simpa [orderTwentyFiveCuspDivisorThree] using h3,
    by simpa [orderTwentyFiveCuspDivisorFour] using h4⟩

/-- Principal cusp-divisor witnesses yield the determinant-`71` relations
between the corresponding degree-zero Picard classes. -/
theorem orderTwentyFive_picardCuspDivisorRelations_of_principal
    {X : Scheme} {Y G : Type*} [AddCommGroup G]
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (hw : S.IsWeightedDegreeZero w)
    (e : DivisorPicard.ClassEquivalence S X)
    (c0 c1 c2 c3 c4 : Y) (hc0 : w c0 = 1)
    (hprincipal :
      orderTwentyFiveCuspPrincipalDivisorRelations S c0 c1 c2 c3 c4) :
    orderTwentyFiveCuspDivisorRelations
      (PicardGroup.weightedAbelJacobiClass S w hw e hc0 c0)
      (PicardGroup.weightedAbelJacobiClass S w hw e hc0 c1)
      (PicardGroup.weightedAbelJacobiClass S w hw e hc0 c2)
      (PicardGroup.weightedAbelJacobiClass S w hw e hc0 c3)
      (PicardGroup.weightedAbelJacobiClass S w hw e hc0 c4) := by
  rcases hprincipal with ⟨g0, g1, g2, g3, g4, h0, h1, h2, h3, h4⟩
  let f := PicardGroup.weightedAbelJacobiDivisorClass S w hw e hc0
  have hf0 : f (orderTwentyFiveCuspDivisorZero c0 c1 c2 c3 c4) = 0 := by
    rw [h0]
    exact PicardGroup.weightedAbelJacobiDivisorClass_principalDivisor
      S w hw e hc0 g0
  have hf1 : f (orderTwentyFiveCuspDivisorOne c0 c1 c2 c3 c4) = 0 := by
    rw [h1]
    exact PicardGroup.weightedAbelJacobiDivisorClass_principalDivisor
      S w hw e hc0 g1
  have hf2 : f (orderTwentyFiveCuspDivisorTwo c0 c1 c2 c3 c4) = 0 := by
    rw [h2]
    exact PicardGroup.weightedAbelJacobiDivisorClass_principalDivisor
      S w hw e hc0 g2
  have hf3 : f (orderTwentyFiveCuspDivisorThree c0 c1 c2 c3 c4) = 0 := by
    rw [h3]
    exact PicardGroup.weightedAbelJacobiDivisorClass_principalDivisor
      S w hw e hc0 g3
  have hf4 : f (orderTwentyFiveCuspDivisorFour c0 c1 c2 c3 c4) = 0 := by
    rw [h4]
    exact PicardGroup.weightedAbelJacobiDivisorClass_principalDivisor
      S w hw e hc0 g4
  have hrelations :=
    orderTwentyFiveCuspDivisorRelations_of_divisorMap_eq_zero
      f c0 c1 c2 c3 c4 hf0 hf1 hf2 hf3 hf4
  simpa only [f, PicardGroup.weightedAbelJacobiDivisorClass_ofPoint] using
    hrelations

/-- Named Picard-level consumer: principal modular-unit divisors and
distinctness of the first two Abel--Jacobi cusp classes identify the subgroup
generated by all five cusp classes with `ZMod 71`. -/
noncomputable def orderTwentyFive_picardCuspidalSubgroupZModEquiv
    {X : Scheme} {Y G : Type*} [AddCommGroup G]
    (S : WeilDivisor.OrderSystem Y G)
    (w : Y → ℤ) (hw : S.IsWeightedDegreeZero w)
    (e : DivisorPicard.ClassEquivalence S X)
    (c0 c1 c2 c3 c4 : Y) (hc0 : w c0 = 1)
    (hprincipal :
      orderTwentyFiveCuspPrincipalDivisorRelations S c0 c1 c2 c3 c4)
    (hne :
      PicardGroup.weightedAbelJacobiClass S w hw e hc0 c0 ≠
        PicardGroup.weightedAbelJacobiClass S w hw e hc0 c1) :
    ZMod 71 ≃+
      orderTwentyFiveBasedCuspSubgroup
        (PicardGroup.weightedAbelJacobiClass S w hw e hc0 c0)
        (PicardGroup.weightedAbelJacobiClass S w hw e hc0 c1)
        (PicardGroup.weightedAbelJacobiClass S w hw e hc0 c2)
        (PicardGroup.weightedAbelJacobiClass S w hw e hc0 c3)
        (PicardGroup.weightedAbelJacobiClass S w hw e hc0 c4) :=
  orderTwentyFiveCuspidalSubgroupZModEquiv _ _ _ _ _
    (orderTwentyFive_picardCuspDivisorRelations_of_principal
      S w hw e c0 c1 c2 c3 c4 hc0 hprincipal)
    hne

end MazurTorsion.Kubert

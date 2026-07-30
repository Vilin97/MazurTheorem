/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Foundations.DivisionPolynomialRootCriterion
import MazurTorsion.Foundations.DivisionPolynomialDiscriminantFive
import MazurTorsion.Foundations.DivisionPolynomialDiscriminantSeven
import MazurTorsion.GroupTheory.ClassificationCardinality
import MazurTorsion.GroupTheory.ForbiddenEmbeddings

/-!
# Odd-prime forbidden subgroups from fixed discriminant identities

The scalar-multiplication-to-division-polynomial root criteria and universal discriminant
identities at levels five and seven are proved. Consequently, full rational `5`-torsion and full
rational `7`-torsion are both excluded unconditionally.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion

namespace OddPrimeFullTorsion

/-- A fifth-division-polynomial discriminant identity rules out full rational `5`-torsion. -/
theorem forbidsEmbedding_zmod_five_square_of_discr
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (hdiscr :
      (W.preΨ' 5).discr = (5 : ℚ) ^ 11 * W.Δ ^ 22) :
    ForbidsEmbedding (ZMod 5 × ZMod 5) W.toAffine.Point :=
  not_injective_zmod_five_square_of_division_inputs W
    (DivisionPolynomialRootCriterion.hasDivisionPolynomialRootCriterion_five W) hdiscr

/-- Full rational `5`-torsion is impossible. -/
theorem forbidsEmbedding_zmod_five_square
    (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    ForbidsEmbedding (ZMod 5 × ZMod 5) W.toAffine.Point :=
  forbidsEmbedding_zmod_five_square_of_discr W
    (DivisionPolynomialDiscriminantFive.discr_preΨ_five W)

/-- A seventh-division-polynomial discriminant identity rules out full rational `7`-torsion. -/
theorem forbidsEmbedding_zmod_seven_square_of_discr
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (hdiscr :
      (W.preΨ' 7).discr = -((7 : ℚ) ^ 23 * W.Δ ^ 92)) :
    ForbidsEmbedding (ZMod 7 × ZMod 7) W.toAffine.Point :=
  not_injective_zmod_seven_square_of_division_inputs W
    (DivisionPolynomialRootCriterion.hasDivisionPolynomialRootCriterion_seven W) hdiscr

/-- Full rational `7`-torsion is impossible. -/
theorem forbidsEmbedding_zmod_seven_square
    (W : WeierstrassCurve ℚ) [W.IsElliptic] :
    ForbidsEmbedding (ZMod 7 × ZMod 7) W.toAffine.Point :=
  forbidsEmbedding_zmod_seven_square_of_discr W
    (DivisionPolynomialDiscriminantSeven.discr_preΨ_seven W)

end OddPrimeFullTorsion

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- Restrict the fixed-discriminant full-`5`-torsion obstruction to rational torsion. -/
theorem rationalTorsion_forbids_zmod_five_square_of_discr
    (hdiscr :
      (E.preΨ' 5).discr = (5 : ℚ) ^ 11 * E.Δ ^ 22) :
    ForbidsEmbedding (ZMod 5 × ZMod 5) (RationalTorsion E) :=
  (OddPrimeFullTorsion.forbidsEmbedding_zmod_five_square_of_discr E hdiscr).subgroup_target
    (AddCommGroup.torsion (E⁄ℚ).Point)

/-- Restrict the full-`5`-torsion obstruction to rational torsion. -/
theorem rationalTorsion_forbids_zmod_five_square :
    ForbidsEmbedding (ZMod 5 × ZMod 5) (RationalTorsion E) :=
  (OddPrimeFullTorsion.forbidsEmbedding_zmod_five_square E).subgroup_target
    (AddCommGroup.torsion (E⁄ℚ).Point)

/-- Restrict the fixed-discriminant full-`7`-torsion obstruction to rational torsion. -/
theorem rationalTorsion_forbids_zmod_seven_square_of_discr
    (hdiscr :
      (E.preΨ' 7).discr = -((7 : ℚ) ^ 23 * E.Δ ^ 92)) :
    ForbidsEmbedding (ZMod 7 × ZMod 7) (RationalTorsion E) :=
  (OddPrimeFullTorsion.forbidsEmbedding_zmod_seven_square_of_discr E hdiscr).subgroup_target
    (AddCommGroup.torsion (E⁄ℚ).Point)

/-- Restrict the full-`7`-torsion obstruction to rational torsion. -/
theorem rationalTorsion_forbids_zmod_seven_square :
    ForbidsEmbedding (ZMod 7 × ZMod 7) (RationalTorsion E) :=
  (OddPrimeFullTorsion.forbidsEmbedding_zmod_seven_square E).subgroup_target
    (AddCommGroup.torsion (E⁄ℚ).Point)

end MazurTorsion

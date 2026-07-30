/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Foundations.DivisionPolynomialRootCriterion
import MazurTorsion.GroupTheory.ClassificationCardinality
import MazurTorsion.GroupTheory.ForbiddenEmbeddings

/-!
# Odd-prime forbidden subgroups from fixed discriminant identities

The scalar-multiplication-to-division-polynomial root criteria at levels five and seven are now
proved. Combining them with the split-polynomial obstruction leaves only the two classical
fixed-level discriminant identities as explicit inputs.
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

/-- A seventh-division-polynomial discriminant identity rules out full rational `7`-torsion. -/
theorem forbidsEmbedding_zmod_seven_square_of_discr
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (hdiscr :
      (W.preΨ' 7).discr = -((7 : ℚ) ^ 23 * W.Δ ^ 92)) :
    ForbidsEmbedding (ZMod 7 × ZMod 7) W.toAffine.Point :=
  not_injective_zmod_seven_square_of_division_inputs W
    (DivisionPolynomialRootCriterion.hasDivisionPolynomialRootCriterion_seven W) hdiscr

end OddPrimeFullTorsion

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- Restrict the fixed-discriminant full-`5`-torsion obstruction to rational torsion. -/
theorem rationalTorsion_forbids_zmod_five_square_of_discr
    (hdiscr :
      (E.preΨ' 5).discr = (5 : ℚ) ^ 11 * E.Δ ^ 22) :
    ForbidsEmbedding (ZMod 5 × ZMod 5) (RationalTorsion E) :=
  (OddPrimeFullTorsion.forbidsEmbedding_zmod_five_square_of_discr E hdiscr).subgroup_target
    (AddCommGroup.torsion (E⁄ℚ).Point)

/-- Restrict the fixed-discriminant full-`7`-torsion obstruction to rational torsion. -/
theorem rationalTorsion_forbids_zmod_seven_square_of_discr
    (hdiscr :
      (E.preΨ' 7).discr = -((7 : ℚ) ^ 23 * E.Δ ^ 92)) :
    ForbidsEmbedding (ZMod 7 × ZMod 7) (RationalTorsion E) :=
  (OddPrimeFullTorsion.forbidsEmbedding_zmod_seven_square_of_discr E hdiscr).subgroup_target
    (AddCommGroup.torsion (E⁄ℚ).Point)

end MazurTorsion

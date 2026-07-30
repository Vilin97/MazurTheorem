/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import MazurTorsion.Foundations.FullFourTorsion
import MazurTorsion.Foundations.ThreeTorsion
import MazurTorsion.Foundations.TwoTorsion
import MazurTorsion.GroupTheory.ClassificationCardinality
import MazurTorsion.GroupTheory.ForbiddenEmbeddings

/-!
# Low-level forbidden subgroups of rational elliptic-curve points

This file converts the explicit coordinate theorems in `MazurTorsion.Foundations` into the
presentation-independent `ForbidsEmbedding` interface used by the finite-group classification.
It also restricts those obstructions from the full rational point group to its torsion subgroup.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion

variable {F : Type*} [Field F]

noncomputable section

private local instance instDecidableEqMazurTorsion : DecidableEq F :=
  Classical.decEq F

/-- A Weierstrass-curve point group in characteristic different from two has no elementary
abelian subgroup of order eight. -/
theorem forbidsEmbedding_zmod_two_cube (E : WeierstrassCurve F) [NeZero (2 : F)] :
    ForbidsEmbedding (ZMod 2 × ZMod 2 × ZMod 2) (E⁄F).Point :=
  not_injective_zmod_two_cube E

end

/-- A rational Weierstrass-curve point group has no elementary abelian subgroup of order eight. -/
theorem forbidsEmbedding_zmod_two_cube_rat (E : WeierstrassCurve ℚ) :
    ForbidsEmbedding (ZMod 2 × ZMod 2 × ZMod 2) (E⁄ℚ).Point :=
  not_injective_zmod_two_cube E

/-- A rational Weierstrass-curve point group has no full rational three-torsion. -/
theorem forbidsEmbedding_zmod_three_square (E : WeierstrassCurve ℚ) :
    ForbidsEmbedding (ZMod 3 × ZMod 3) (E⁄ℚ).Point :=
  ThreeTorsion.not_injective_zmod_three_square E

/-- A rational Weierstrass-curve point group has no full rational four-torsion. -/
theorem forbidsEmbedding_zmod_four_square (E : WeierstrassCurve ℚ) :
    ForbidsEmbedding (ZMod 4 × ZMod 4) (E⁄ℚ).Point :=
  FullFour.not_injective_zmod_four_square E

variable (E : WeierstrassCurve ℚ)

/-- The rational torsion subgroup has no elementary abelian subgroup of order eight. -/
theorem rationalTorsion_forbids_zmod_two_cube :
    ForbidsEmbedding (ZMod 2 × ZMod 2 × ZMod 2) (RationalTorsion E) :=
  (forbidsEmbedding_zmod_two_cube_rat E).subgroup_target
    (AddCommGroup.torsion (E⁄ℚ).Point)

/-- The rational torsion subgroup has no full three-torsion. -/
theorem rationalTorsion_forbids_zmod_three_square :
    ForbidsEmbedding (ZMod 3 × ZMod 3) (RationalTorsion E) :=
  (forbidsEmbedding_zmod_three_square E).subgroup_target
    (AddCommGroup.torsion (E⁄ℚ).Point)

/-- The rational torsion subgroup has no full four-torsion. -/
theorem rationalTorsion_forbids_zmod_four_square :
    ForbidsEmbedding (ZMod 4 × ZMod 4) (RationalTorsion E) :=
  (forbidsEmbedding_zmod_four_square E).subgroup_target
    (AddCommGroup.torsion (E⁄ℚ).Point)

end MazurTorsion

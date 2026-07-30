/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Arithmetic.ExceptionalTwoTen
import MazurTorsion.Arithmetic.ExceptionalTwoTwelve
import MazurTorsion.Arithmetic.LowTorsionObstructions
import MazurTorsion.NumberTheory.ExceptionalCubicReduction
import MazurTorsion.NumberTheory.ExceptionalQuarticDescent

/-!
# Exceptional product obstructions

This file packages the direct Diophantine reductions for the two product groups that survive the
point-order theorem:

* `ZMod 2 × ZMod 10`, reduced to the quartic
  `e² = X⁴ - 11X²Y² - Y⁴`;
* `ZMod 2 × ZMod 12`, reduced to
  `w² = (t² - 1)(9t² - 1)`, or equivalently to an explicit rank-zero cubic.

The reduction files prove all elliptic-curve and group-theoretic steps. The conductor-twenty
quartic descent closes the first obstruction.  For the second, an explicit two-descent proves
rank zero on the exceptional cubic and good reduction modulo five bounds its rational points
by the eight visible ones.  Thus both product obstructions are unconditional here.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion

variable (E : WeierstrassCurve ℚ)

/-- The conductor-twenty quartic classification rules out the exceptional
`ZMod 2 × ZMod 10` subgroup of rational torsion. -/
theorem rationalTorsion_forbids_zmod_two_prod_ten_of_quartic
    [E.IsElliptic]
    (hquartic : ExceptionalTwoTen.NoExceptionalQuartic) :
    ForbidsEmbedding (ZMod 2 × ZMod 10) (RationalTorsion E) :=
  (ExceptionalTwoTen.forbidsEmbedding_zmod_two_prod_ten_of_quartic hquartic E).subgroup_target
    (AddCommGroup.torsion (E⁄ℚ).Point)

/-- An injective `ZMod 2 × ZMod 10` subgroup of rational points is impossible. -/
theorem forbidsEmbedding_zmod_two_prod_ten
    [E.IsElliptic] :
    ForbidsEmbedding (ZMod 2 × ZMod 10) (E⁄ℚ).Point :=
  ExceptionalTwoTen.forbidsEmbedding_zmod_two_prod_ten_of_quartic
    ExceptionalTwoTen.noExceptionalQuartic E

/-- Restrict the unconditional `ZMod 2 × ZMod 10` obstruction to rational torsion. -/
theorem rationalTorsion_forbids_zmod_two_prod_ten
    [E.IsElliptic] :
    ForbidsEmbedding (ZMod 2 × ZMod 10) (RationalTorsion E) :=
  (forbidsEmbedding_zmod_two_prod_ten E).subgroup_target
    (AddCommGroup.torsion (E⁄ℚ).Point)

/-- The exceptional quartic classification rules out an injective
`ZMod 2 × ZMod 12` subgroup of rational points. -/
theorem forbidsEmbedding_zmod_two_prod_twelve_of_quartic
    (hquartic : ExceptionalQuarticIsTrivial) :
    ForbidsEmbedding (ZMod 2 × ZMod 12) (E⁄ℚ).Point :=
  fun φ => not_injective_zmod_two_twelve_of_quartic hquartic E φ

/-- Restrict the exceptional `ZMod 2 × ZMod 12` obstruction to rational torsion. -/
theorem rationalTorsion_forbids_zmod_two_prod_twelve_of_quartic
    (hquartic : ExceptionalQuarticIsTrivial) :
    ForbidsEmbedding (ZMod 2 × ZMod 12) (RationalTorsion E) :=
  (forbidsEmbedding_zmod_two_prod_twelve_of_quartic E hquartic).subgroup_target
    (AddCommGroup.torsion (E⁄ℚ).Point)

/-- The rational-point classification of the associated cubic rules out an injective
`ZMod 2 × ZMod 12` subgroup of rational points. -/
theorem forbidsEmbedding_zmod_two_prod_twelve_of_cubic
    (hcubic : ExceptionalCubicIsTrivial) :
    ForbidsEmbedding (ZMod 2 × ZMod 12) (E⁄ℚ).Point :=
  fun φ => not_injective_zmod_two_twelve_of_cubic hcubic E φ

/-- Restrict the cubic form of the exceptional `ZMod 2 × ZMod 12` obstruction to rational
torsion. -/
theorem rationalTorsion_forbids_zmod_two_prod_twelve_of_cubic
    (hcubic : ExceptionalCubicIsTrivial) :
    ForbidsEmbedding (ZMod 2 × ZMod 12) (RationalTorsion E) :=
  (forbidsEmbedding_zmod_two_prod_twelve_of_cubic E hcubic).subgroup_target
    (AddCommGroup.torsion (E⁄ℚ).Point)

/-- An injective `ZMod 2 × ZMod 12` subgroup of rational points is
impossible. -/
theorem forbidsEmbedding_zmod_two_prod_twelve :
    ForbidsEmbedding (ZMod 2 × ZMod 12) (E⁄ℚ).Point :=
  forbidsEmbedding_zmod_two_prod_twelve_of_cubic E
    ExceptionalCubic.exceptionalCubicIsTrivial

/-- Restrict the unconditional `ZMod 2 × ZMod 12` obstruction to rational
torsion. -/
theorem rationalTorsion_forbids_zmod_two_prod_twelve :
    ForbidsEmbedding (ZMod 2 × ZMod 12) (RationalTorsion E) :=
  (forbidsEmbedding_zmod_two_prod_twelve E).subgroup_target
    (AddCommGroup.torsion (E⁄ℚ).Point)

end MazurTorsion

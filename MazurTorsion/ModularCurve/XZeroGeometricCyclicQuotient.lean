/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.CommGroupSchemeFppfQuotient
import MazurTorsion.ModularCurve.XZeroFiniteFlatCyclicQuotient

/-!
# Supplied geometric cyclic quotients for `X₀(N)` data

This file specializes the ambient fppf quotient certificate to the actual finite-flat cyclic
subgroup constructed from a rational `Γ₀(N)` datum.  It does not construct the quotient
elliptic curve.  Every declaration below takes a geometric quotient presentation as an explicit
argument, so the missing representability theorem remains visible.

The substantive comparison is with the repository's existing represented-point quotient.  The
pointwise subgroup used by the geometric presentation is exactly the rational-point image of the
finite-flat subgroup already attached to the datum.  Consequently the generic injection into
quotient-scheme points and its `H¹` boundary exactness apply to that same subgroup, without
identifying quotient-scheme rational points with a point-group quotient.
-/

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassGroupSchemeInterface

universe u

open XZeroModuli

variable {K : Type u} [Field K] [DecidableEq K]
  {N : ℕ} [NeZero N]

/-- The type of a supplied geometric quotient presentation for the actual finite-flat subgroup
attached to `x`.  This abbreviation provides no constructor and asserts no existence theorem. -/
abbrev RationalDatumGeometricQuotientPresentation
    (x : RationalDatum K N)
    (M : WeierstrassGroupSchemeInterface x.curve) :=
  CommGroupScheme.FppfQuotientPresentation
    (splitGammaZeroDatumOfRationalDatum x M).subgroup.inclusion

/-- The subgroup of represented rational points used by a supplied geometric quotient is exactly
the subgroup already used by the checked point-quotient construction. -/
theorem rationalDatumGeometricPointKernelRange_toAddSubgroup
    (x : RationalDatum K N)
    (M : WeierstrassGroupSchemeInterface x.curve)
    (Q : RationalDatumGeometricQuotientPresentation x M) :
    (Q.pointKernelRange
      (AffineCommGroupScheme.testObject (R := K) K)).toAddSubgroup =
      finiteFlatSubgroupPointRange x M :=
  rfl

/-- The quotient of represented rational points by the actual finite-flat cyclic subgroup embeds
in the rational points of every supplied geometric quotient scheme. -/
theorem rationalDatumGeometricPointQuotientMap_injective
    (x : RationalDatum K N)
    (M : WeierstrassGroupSchemeInterface x.curve)
    (Q : RationalDatumGeometricQuotientPresentation x M) :
    Function.Injective
      (Q.pointQuotientMap (AffineCommGroupScheme.testObject (R := K) K)) :=
  Q.pointQuotientMap_injective _

/-- For the actual cyclic subgroup attached to `x`, the image of the point quotient is precisely
the zero fibre of the fppf connecting map.  This is the retained `H¹` obstruction to rational
surjectivity. -/
theorem rationalDatumGeometricPointQuotient_boundary_exact
    (x : RationalDatum K N)
    (M : WeierstrassGroupSchemeInterface x.curve)
    (Q : RationalDatumGeometricQuotientPresentation x M) :
    Function.MulExact
      (Q.pointQuotientMap
        (CommGroupScheme.baseObject (Spec (.of K))))
      Q.boundaryHom :=
  Q.exact_pointQuotientMap_boundaryHom

/-- Under extension of the base field, the geometric quotient presentation still has exactly the
base-changed finite-flat cyclic subgroup as its chosen kernel inclusion. -/
theorem rationalDatumGeometricQuotient_baseChange_kernel_inclusion
    (x : RationalDatum K N)
    (M : WeierstrassGroupSchemeInterface x.curve)
    (Q : RationalDatumGeometricQuotientPresentation x M)
    (L : Type u) [Field L] [Algebra K L] :
    (Q.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))).kernelPresentation.inclusion =
      ((splitGammaZeroDatumOfRationalDatum x M).subgroup.baseChange).inclusion :=
  rfl

end WeierstrassGroupSchemeInterface
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli

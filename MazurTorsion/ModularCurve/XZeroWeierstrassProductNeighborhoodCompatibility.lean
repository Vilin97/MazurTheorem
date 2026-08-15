/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProductNeighborhoodAddition

/-!
# Compatibility boundary for the Weierstrass product-neighbourhood chart

This module is the named downstream consumer of the `D(B₁₂)` interface.  It
packages precisely the two compatibility statements needed before any future
gluing step: agreement with secant addition on the exact intersection and
agreement with tangent doubling on the diagonal.  It does not assert that the
charts cover, construct a glued multiplication morphism, or prove group laws.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

/-- The checked `D(B₁₂)` chart simultaneously satisfies its full
scheme-level secant-overlap and diagonal-tangent contracts.  This is the
interface consumed by the next scheme-level gluing slice. -/
theorem productNeighborhoodAddition_secant_and_tangent_compatible
    (W : WeierstrassCurve K) :
    additionSecantIntersectionToProductNeighborhood W ≫
        productNeighborhoodAdditionProjectiveMorphism W =
      additionSecantIntersectionToSecantChart W ≫
        secantAdditionProjectiveMorphism W ∧
    tangentChartToProductNeighborhoodMorphism W ≫
        productNeighborhoodAdditionProjectiveMorphism W =
      tangentDoublingProjectiveMorphism W := by
  exact ⟨additionSecantIntersection_additionProjective_eq W,
    tangentChartToProductNeighborhoodMorphism_comp_additionProjective W⟩

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli

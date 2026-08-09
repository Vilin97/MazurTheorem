/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/

import MazurTorsion.AlgebraicGeometry.FormalImmersionAffineFiber
import MazurTorsion.NumberTheory.OrderThirtyFiveInfinityChartScheme

/-!
# The localized first-order identity on the level-35 infinity chart

The represented infinity-chart quotient map satisfies `W-1=(-7/d)t` in its
coordinate ring.  This file transports that equality through the actual map
on localized special fibres used by the repository's affine formal-immersion
criterion.

Thus the remaining characteristic-eleven calculation no longer receives an
opaque q-expansion equality.  It need only prove that the localized image of
`t` is a cusp uniformizer and that the displayed coefficient is a unit.
-/

noncomputable section

open Algebra TensorProduct

namespace MazurTorsion.OrderThirtyFive.InfinityChartFirstOrder

open InfinityChartScheme

universe u

variable {R : Type u} [CommRing R]

/-- The quotient-side parameter `W-1` in the localized target fibre. -/
def localizedTargetParameter
    (p : Ideal R) [p.IsPrime]
    (q : Ideal (p.Fiber (SourceOpenRing R))) [q.IsPrime] :
    Localization.AtPrime
      (q.comap (Ideal.Fiber.map p (targetToOpenRing R))) :=
  algebraMap (p.Fiber (TargetRing R))
    (Localization.AtPrime
      (q.comap (Ideal.Fiber.map p (targetToOpenRing R))))
    (Algebra.TensorProduct.includeRight (targetW R - 1))

/-- The infinity parameter `t` in the localized source fibre. -/
def localizedCuspParameter
    (p : Ideal R) [p.IsPrime]
    (q : Ideal (p.Fiber (SourceOpenRing R))) [q.IsPrime] :
    Localization.AtPrime q :=
  algebraMap (p.Fiber (SourceOpenRing R)) (Localization.AtPrime q)
    (Algebra.TensorProduct.includeRight (openT R))

/-- The exact linear coefficient `-7/d` in the localized source fibre. -/
def localizedUnitCoefficient
    (p : Ideal R) [p.IsPrime]
    (q : Ideal (p.Fiber (SourceOpenRing R))) [q.IsPrime] :
    Localization.AtPrime q :=
  algebraMap (p.Fiber (SourceOpenRing R)) (Localization.AtPrime q)
    (Algebra.TensorProduct.includeRight
      (-7 * denominatorInverse R))

/-- The actual localized affine-fibre map carries `W-1` to
`(-7/d)t`, with zero remainder. -/
theorem localizedMap_targetParameter_eq_unit_mul_cuspParameter
    (p : Ideal R) [p.IsPrime]
    (q : Ideal (p.Fiber (SourceOpenRing R))) [q.IsPrime] :
    Ideal.Fiber.localizedMap p (targetToOpenRing R) q
        (localizedTargetParameter p q) =
      localizedUnitCoefficient p q * localizedCuspParameter p q := by
  rw [localizedTargetParameter,
    Ideal.Fiber.localizedMap_algebraMap_includeRight]
  rw [show targetToOpenRing R (targetW R - 1) =
      openQuotientW R - 1 by simp]
  rw [openQuotientW_sub_one]
  change
    algebraMap (p.Fiber (SourceOpenRing R)) (Localization.AtPrime q)
        (Algebra.TensorProduct.includeRight
          ((-7 * denominatorInverse R) * openT R)) =
      algebraMap (p.Fiber (SourceOpenRing R)) (Localization.AtPrime q)
          (Algebra.TensorProduct.includeRight
            (-7 * denominatorInverse R)) *
        algebraMap (p.Fiber (SourceOpenRing R)) (Localization.AtPrime q)
          (Algebra.TensorProduct.includeRight (openT R))
  simp only [map_mul]

end MazurTorsion.OrderThirtyFive.InfinityChartFirstOrder

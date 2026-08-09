/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.CommGroupSchemePowerKummerRankZero
import MazurTorsion.AlgebraicGeometry.NeronModel.Basic

/-!
# Transporting power-Kummer rank zero through a Neron model

The power-Kummer rank-zero theorem applies to the integral commutative group scheme in a Neron
model.  The Neron mapping property then identifies its integral base points with rational points
of the prescribed generic fibre, so finite generation and the resulting integer-module finrank
transport across that equivalence.

In particular, the Kummer construction in this file is not applied after base change: all of its
flatness, surjectivity, finite-presentation, kernel-cohomology, and torsion-cardinality inputs are
properties of multiplication on the integral model over `Spec R`.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.NeronModel

open CommGroupScheme

universe u

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  {A : CommGroupScheme (Spec (.of K))}

/-- If multiplication by `p` on the integral Neron model satisfies the checked power-Kummer
rank-zero hypotheses, then the group of rational points of the prescribed generic fibre has
integer-module finrank zero. -/
theorem finrank_genericBasePoint_eq_zero_of_powerKummer
    {p : ℕ} (hp : p.Prime) (N : NeronModel R K A)
    [AddGroup.FG (Additive (BasePoint A))]
    (hflat : Flat (underlyingHom (powerEnd N.model p)))
    (hsurjective : Surjective (underlyingHom (powerEnd N.model p)))
    (hlfp : LocallyOfFinitePresentation (underlyingHom (powerEnd N.model p)))
    (kernelHOneData : FiniteFlatCommGroupScheme.FinitePGroup.BoundedData p
      (CommGroupScheme.kernel (powerEnd N.model p)).FppfHOne.{u})
    (torsionLength : ℕ)
    (hkernel : Nat.card
        (nsmulAddMonoidHom (α := Additive (BasePoint N.model)) p).ker =
      p ^ torsionLength)
    (hbound : kernelHOneData.length ≤ torsionLength) :
    Module.finrank ℤ (Additive (BasePoint A)) = 0 := by
  let e : Additive (BasePoint A) ≃+ Additive (BasePoint N.model) :=
    N.basePointMulEquiv.symm.toAdditive
  letI : AddGroup.FG (Additive (BasePoint N.model)) :=
    AddGroup.fg_of_surjective (f := e.toAddMonoidHom) e.surjective
  have hmodel : Module.finrank ℤ (Additive (BasePoint N.model)) = 0 :=
    FiniteFlatCommGroupScheme.finrank_additive_basePoint_eq_zero_of_powerKummer
      hp N.model hflat hsurjective hlfp kernelHOneData torsionLength hkernel hbound
  calc
    Module.finrank ℤ (Additive (BasePoint A)) =
        Module.finrank ℤ (Additive (BasePoint N.model)) :=
      N.basePointMulEquiv.toAdditive.toIntLinearEquiv.finrank_eq.symm
    _ = 0 := hmodel

end AlgebraicGeometry.NeronModel

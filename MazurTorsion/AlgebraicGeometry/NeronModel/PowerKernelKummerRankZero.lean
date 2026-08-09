/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.CommGroupSchemePowerKummerTorsionRankZero
import MazurTorsion.AlgebraicGeometry.NeronModel.Basic

/-!
# Power-kernel Kummer rank zero for Neron models

An actual finite-`p` certificate on the scheme-theoretic multiplication kernel of a Neron model
supplies the torsion-cardinality law in the checked power-Kummer argument.  The Neron mapping
property then transports the resulting rank-zero statement from integral model points to the
rational points of the prescribed generic fibre.

All geometric fppf hypotheses, the two kernel cohomology certificates, finite generation of the
generic-fibre points, and the comparison of their lengths remain explicit.  In particular, this
file proves no Neron-model existence, Raynaud classification, Mordell--Weil finite generation, or
cohomology bound.
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

noncomputable local instance powerKernelIsCommMonObj
    (G : CommGroupScheme (Spec (.of R))) (p : ℕ) :
    IsCommMonObj (CommGroupScheme.kernelGrp (powerEnd G p)).X :=
  CommGroupScheme.kernelGrp_isComm (powerEnd G p)

noncomputable local instance powerKernelBasePointCommGroup
    (G : CommGroupScheme (Spec (.of R))) (p : ℕ) :
    CommGroup (BasePoint (kernel (powerEnd G p))) :=
  CategoryTheory.Hom.commGroup

/-- The actual multiplication kernel on the integral Neron model supplies the torsion
cardinality required by power-Kummer rank zero.  Thus no independent cardinality equality for
the `p`-torsion of the model's base-point group is assumed. -/
theorem finrank_genericBasePoint_eq_zero_of_powerKummer_kernelData
    {p : ℕ} (hp : p.Prime) (N : NeronModel R K A)
    [AddGroup.FG (Additive (BasePoint A))]
    (hflat : Flat (underlyingHom (powerEnd N.model p)))
    (hsurjective : Surjective (underlyingHom (powerEnd N.model p)))
    (hlfp : LocallyOfFinitePresentation (underlyingHom (powerEnd N.model p)))
    (kernelHZeroData : FiniteFlatCommGroupScheme.FinitePGroup.CertifiedData p
      (BasePoint (kernel (powerEnd N.model p))))
    (kernelHOneData : FiniteFlatCommGroupScheme.FinitePGroup.BoundedData p
      (kernel (powerEnd N.model p)).FppfHOne.{u})
    (hbound : kernelHOneData.length ≤ kernelHZeroData.length) :
    Module.finrank ℤ (Additive (BasePoint A)) = 0 := by
  let e : Additive (BasePoint A) ≃+ Additive (BasePoint N.model) :=
    N.basePointMulEquiv.symm.toAdditive
  letI : AddGroup.FG (Additive (BasePoint N.model)) :=
    AddGroup.fg_of_surjective (f := e.toAddMonoidHom) e.surjective
  have hmodel : Module.finrank ℤ (Additive (BasePoint N.model)) = 0 :=
    FiniteFlatCommGroupScheme.finrank_additive_basePoint_eq_zero_of_powerKummer_kernelData
      hp N.model hflat hsurjective hlfp kernelHZeroData kernelHOneData hbound
  calc
    Module.finrank ℤ (Additive (BasePoint A)) =
        Module.finrank ℤ (Additive (BasePoint N.model)) :=
      N.basePointMulEquiv.toAdditive.toIntLinearEquiv.finrank_eq.symm
    _ = 0 := hmodel

end AlgebraicGeometry.NeronModel

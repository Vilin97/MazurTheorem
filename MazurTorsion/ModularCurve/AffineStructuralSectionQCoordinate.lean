/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.AffineCuspResidueRetraction
import MazurTorsion.ModularCurve.CompleteDVRStalk

/-!
# The completed q-coordinate determined by an affine structural section

An affine section canonically selects a rational point on every special
fibre.  Evaluation at that point extends to its local ring and retracts the
residue-field coefficient embedding.  Consequently a DVR uniformizer at the
point determines a completed power-series coordinate; no separate completion
equivalence is needed.

This is the presentation-independent version of the coordinate construction
for the polynomial cusp chart.  Its level-35 consumer uses the actual section,
special-fibre DVR, and geometric uniformizer supplied by the represented
modular chart.
-/

noncomputable section

open Algebra TensorProduct AlgebraicGeometry Ideal
open MazurTorsion.ModularCurve

namespace Ideal.Fiber.AffineStructuralSection

universe u

variable {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]

/-- The local ring of the special-fibre point selected by the section. -/
abbrev FiberLocalRing
    (C : AffineStructuralSection (R := R) (T := T))
    (p : Ideal R) [p.IsPrime] :=
  Localization.AtPrime (C.fiberPrime p)

/-- Fibre evaluation at the section extends across localization at its
kernel. -/
noncomputable def localizedFiberRetraction
    (C : AffineStructuralSection (R := R) (T := T))
    (p : Ideal R) [p.IsPrime] :
    C.FiberLocalRing p →+* p.ResidueField :=
  IsLocalization.lift
    (M := (C.fiberPrime p).primeCompl)
    (S := C.FiberLocalRing p)
    (g := (C.fiberRetraction p).toRingHom)
    (fun y => by
      apply isUnit_iff_ne_zero.mpr
      intro hy
      exact y.property (by
        change C.fiberRetraction p y = 0
        exact hy))

/-- Localized fibre evaluation fixes the residue-field coefficients. -/
@[simp]
theorem localizedFiberRetraction_algebraMap
    (C : AffineStructuralSection (R := R) (T := T))
    (p : Ideal R) [p.IsPrime] (c : p.ResidueField) :
    C.localizedFiberRetraction p
        (algebraMap p.ResidueField (C.FiberLocalRing p) c) = c := by
  rw [IsScalarTower.algebraMap_apply p.ResidueField (p.Fiber T)
    (C.FiberLocalRing p)]
  rw [localizedFiberRetraction, IsLocalization.lift_eq]
  exact (C.fiberRetraction p).commutes c

/-- Localized fibre evaluation is onto the coefficient field. -/
theorem localizedFiberRetraction_surjective
    (C : AffineStructuralSection (R := R) (T := T))
    (p : Ideal R) [p.IsPrime] :
    Function.Surjective (C.localizedFiberRetraction p) := by
  intro c
  refine ⟨algebraMap p.ResidueField (C.FiberLocalRing p) c, ?_⟩
  exact C.localizedFiberRetraction_algebraMap p c

/-- The localized section evaluation retracts the coefficient embedding. -/
theorem localizedFiberRetraction_comp_algebraMap
    (C : AffineStructuralSection (R := R) (T := T))
    (p : Ideal R) [p.IsPrime] :
    (C.localizedFiberRetraction p).comp
        (algebraMap p.ResidueField (C.FiberLocalRing p)) =
      RingHom.id p.ResidueField := by
  apply RingHom.ext
  intro c
  exact C.localizedFiberRetraction_algebraMap p c

/-- The completed q-coordinate canonically constructed from the section and
an irreducible uniformizer of its special-fibre DVR. -/
noncomputable def qCoordinate
    (C : AffineStructuralSection (R := R) (T := T))
    (p : Ideal R) [p.IsPrime]
    [IsDomain (C.FiberLocalRing p)]
    [IsDiscreteValuationRing (C.FiberLocalRing p)]
    (q : C.FiberLocalRing p) (hq : Irreducible q) :
    LocalCompletion.Ring (C.FiberLocalRing p) ≃+*
      PowerSeries p.ResidueField := by
  letI : IsLocalHom (C.localizedFiberRetraction p) :=
    (C.localizedFiberRetraction_surjective p).isLocalHom
  exact CompleteDVRStalk.stalkCompletionRingEquivOfRetraction
      (C.FiberLocalRing p) p.ResidueField
      (C.localizedFiberRetraction p)
      (C.localizedFiberRetraction_comp_algebraMap p) q hq

/-- The geometric uniformizer is the power-series variable in the
section-determined coordinate. -/
@[simp]
theorem qCoordinate_uniformizer
    (C : AffineStructuralSection (R := R) (T := T))
    (p : Ideal R) [p.IsPrime]
    [IsDomain (C.FiberLocalRing p)]
    [IsDiscreteValuationRing (C.FiberLocalRing p)]
    (q : C.FiberLocalRing p) (hq : Irreducible q) :
    C.qCoordinate p q hq
        (completionRingHom (C.FiberLocalRing p) q) =
      (PowerSeries.X : PowerSeries p.ResidueField) := by
  letI : IsLocalHom (C.localizedFiberRetraction p) :=
    (C.localizedFiberRetraction_surjective p).isLocalHom
  change CompleteDVRStalk.stalkCompletionRingEquiv
      (C.FiberLocalRing p) p.ResidueField q hq
      (CompleteDVRStalk.coefficientField_surjective_of_algebraMap_retraction
          (C.localizedFiberRetraction p)
          (C.localizedFiberRetraction_comp_algebraMap p))
      (algebraMap (C.FiberLocalRing p)
        (LocalCompletion.Ring (C.FiberLocalRing p)) q) = _
  exact CompleteDVRStalk.stalkCompletionRingEquiv_uniformizer
      (C.FiberLocalRing p) p.ResidueField q hq
      (CompleteDVRStalk.coefficientField_surjective_of_algebraMap_retraction
          (C.localizedFiberRetraction p)
          (C.localizedFiberRetraction_comp_algebraMap p))

/-- Residue-field constants become constant power series in the constructed
coordinate. -/
@[simp]
theorem qCoordinate_algebraMap
    (C : AffineStructuralSection (R := R) (T := T))
    (p : Ideal R) [p.IsPrime]
    [IsDomain (C.FiberLocalRing p)]
    [IsDiscreteValuationRing (C.FiberLocalRing p)]
    (q : C.FiberLocalRing p) (hq : Irreducible q)
    (c : p.ResidueField) :
    C.qCoordinate p q hq
        (completionRingHom (C.FiberLocalRing p)
          (algebraMap p.ResidueField (C.FiberLocalRing p) c)) =
      PowerSeries.C c := by
  letI : IsLocalHom (C.localizedFiberRetraction p) :=
    (C.localizedFiberRetraction_surjective p).isLocalHom
  apply (C.qCoordinate p q hq).symm.injective
  simp [qCoordinate, CompleteDVRStalk.stalkCompletionRingEquivOfRetraction,
    CompleteDVRStalk.stalkCompletionRingEquiv,
    CompleteDVRCoordinate.ringEquiv_symm_apply,
    IsScalarTower.algebraMap_apply p.ResidueField (C.FiberLocalRing p)
      (LocalCompletion.Ring (C.FiberLocalRing p))]
  rfl

end Ideal.Fiber.AffineStructuralSection

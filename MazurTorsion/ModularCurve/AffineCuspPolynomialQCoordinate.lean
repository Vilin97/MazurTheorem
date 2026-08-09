/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/

import MazurTorsion.ModularCurve.AffineCuspChartTransport
import MazurTorsion.ModularCurve.CompleteDVRStalk
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# The completed q-coordinate on the represented polynomial cusp

The represented cusp chart has special fibre `k[X]` and cusp prime `(X)`.
This file completes the local algebra already proved for that chart:

* the localization of the special fibre at the cusp is a DVR;
* evaluation at zero extends to a retraction of that local ring onto `k`;
* completion along the cusp is therefore canonically identified with `k⟦X⟧`;
* the localized geometric parameter maps to `X` in this coordinate.

The final two lemmas state the normalization in the differential form used by
Mazur's formal-immersion argument.  If `F` is the function expansion, its
cotangent expansion is represented by `X * dF/dX`.  For the constructed cusp
parameter this is exactly `X`, hence nonzero.  No Hecke action on function
series is asserted here; a modular application must construct the genuine
Hecke action on differentials separately.
-/

noncomputable section

open Algebra TensorProduct AlgebraicGeometry Ideal
open Ideal.Fiber

namespace MazurTorsion.ModularCurve.AffineCuspPolynomialChart

universe u

/-- The local ring of the represented special-fibre cusp. -/
abbrev SpecialFiberCuspLocalRing
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime] :=
  Localization.AtPrime ((zeroSection R).fiberPrime p)

private theorem fiber_isDomain
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime] :
    IsDomain (p.Fiber (CoordinateRing R)) :=
  (fiberCoordinate R p).toRingEquiv.toMulEquiv.isDomain _

private theorem fiber_isPrincipalIdealRing
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime] :
    IsPrincipalIdealRing (p.Fiber (CoordinateRing R)) := by
  exact IsPrincipalIdealRing.of_surjective
    (fiberCoordinate R p).symm.toRingHom
    (fiberCoordinate R p).symm.surjective

/-- The special-fibre cusp local ring is a domain. -/
theorem specialFiberCuspLocalRing_isDomain
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime] :
    IsDomain (SpecialFiberCuspLocalRing R p) := by
  letI : IsDomain (p.Fiber (CoordinateRing R)) := fiber_isDomain R p
  infer_instance

/-- Localizing the polynomial special fibre at the nonzero cusp prime gives a
discrete valuation ring.  The proof transports principality from `k[X]` and
uses the standard localization theorem for Dedekind domains. -/
theorem specialFiberCuspLocalRing_isDiscreteValuationRing
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime] :
    letI : IsDomain (SpecialFiberCuspLocalRing R p) :=
      specialFiberCuspLocalRing_isDomain R p
    IsDiscreteValuationRing (SpecialFiberCuspLocalRing R p) := by
  letI : IsDomain (p.Fiber (CoordinateRing R)) := fiber_isDomain R p
  letI : IsPrincipalIdealRing (p.Fiber (CoordinateRing R)) :=
    fiber_isPrincipalIdealRing R p
  letI : IsDomain (SpecialFiberCuspLocalRing R p) :=
    specialFiberCuspLocalRing_isDomain R p
  have hcuspPrime : (zeroSection R).fiberPrime p ≠ ⊥ := by
    rw [fiberPrime_eq_span]
    exact Ideal.span_singleton_eq_bot.not.mpr (fiberVariable_ne_zero R p)
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    (A := p.Fiber (CoordinateRing R)) hcuspPrime
    (SpecialFiberCuspLocalRing R p)

/-- The constructed localized q-parameter is a uniformizer of the cusp DVR. -/
theorem qParameter_irreducible
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime] :
    letI : IsDomain (SpecialFiberCuspLocalRing R p) :=
      specialFiberCuspLocalRing_isDomain R p
    letI : IsDiscreteValuationRing (SpecialFiberCuspLocalRing R p) :=
      specialFiberCuspLocalRing_isDiscreteValuationRing R p
    Irreducible (qParameter R p) := by
  letI : IsDomain (SpecialFiberCuspLocalRing R p) :=
    specialFiberCuspLocalRing_isDomain R p
  letI : IsDiscreteValuationRing (SpecialFiberCuspLocalRing R p) :=
    specialFiberCuspLocalRing_isDiscreteValuationRing R p
  exact IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal
    (qParameter R p) (qParameter_ne_zero R p)
    (maximalIdeal_eq_span_qParameter R p)

/-- Evaluation at zero on the polynomial fibre extends across localization at
the cusp.  Every inverted polynomial has nonzero value at zero because the
cusp prime is the kernel of the fibre retraction. -/
noncomputable def localizedZeroRetraction
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime] :
    SpecialFiberCuspLocalRing R p →+* p.ResidueField :=
  IsLocalization.lift
    (M := ((zeroSection R).fiberPrime p).primeCompl)
    (S := SpecialFiberCuspLocalRing R p)
    (g := ((zeroSection R).fiberRetraction p).toRingHom)
    (fun y => by
      apply isUnit_iff_ne_zero.mpr
      intro hy
      exact y.property (by
        change (zeroSection R).fiberRetraction p y = 0
        exact hy))

/-- Localized zero evaluation fixes every coefficient. -/
@[simp]
theorem localizedZeroRetraction_algebraMap
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (c : p.ResidueField) :
    localizedZeroRetraction R p
        (algebraMap p.ResidueField (SpecialFiberCuspLocalRing R p) c) = c := by
  rw [IsScalarTower.algebraMap_apply p.ResidueField
    (p.Fiber (CoordinateRing R)) (SpecialFiberCuspLocalRing R p)]
  rw [localizedZeroRetraction, IsLocalization.lift_eq]
  exact ((zeroSection R).fiberRetraction p).commutes c

/-- The localized zero evaluation is onto its coefficient field. -/
theorem localizedZeroRetraction_surjective
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime] :
    Function.Surjective (localizedZeroRetraction R p) := by
  intro c
  refine ⟨algebraMap p.ResidueField (SpecialFiberCuspLocalRing R p) c, ?_⟩
  exact localizedZeroRetraction_algebraMap R p c

/-- Constants followed by localized zero evaluation are unchanged. -/
theorem localizedZeroRetraction_comp_algebraMap
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime] :
    (localizedZeroRetraction R p).comp
        (algebraMap p.ResidueField (SpecialFiberCuspLocalRing R p)) =
      RingHom.id p.ResidueField := by
  apply RingHom.ext
  intro c
  exact localizedZeroRetraction_algebraMap R p c

/-- The completed local q-coordinate constructed from the polynomial
coefficient field, zero retraction, and geometric cusp uniformizer. -/
noncomputable def qCoordinate
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime] :
    LocalCompletion.Ring (SpecialFiberCuspLocalRing R p) ≃+*
      PowerSeries p.ResidueField := by
  letI : IsDomain (SpecialFiberCuspLocalRing R p) :=
    specialFiberCuspLocalRing_isDomain R p
  letI : IsDiscreteValuationRing (SpecialFiberCuspLocalRing R p) :=
    specialFiberCuspLocalRing_isDiscreteValuationRing R p
  letI : IsLocalHom (localizedZeroRetraction R p) :=
    (localizedZeroRetraction_surjective R p).isLocalHom
  exact CompleteDVRStalk.stalkCompletionRingEquivOfRetraction
    (SpecialFiberCuspLocalRing R p) p.ResidueField
    (localizedZeroRetraction R p)
    (localizedZeroRetraction_comp_algebraMap R p)
    (qParameter R p) (qParameter_irreducible R p)

/-- In the constructed completed coordinate, the actual localized geometric
q-parameter is the power-series variable. -/
@[simp]
theorem qCoordinate_qParameter
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime] :
    qCoordinate R p
        (completionRingHom (SpecialFiberCuspLocalRing R p)
          (qParameter R p)) =
      (PowerSeries.X : PowerSeries p.ResidueField) := by
  letI : IsDomain (SpecialFiberCuspLocalRing R p) :=
    specialFiberCuspLocalRing_isDomain R p
  letI : IsDiscreteValuationRing (SpecialFiberCuspLocalRing R p) :=
    specialFiberCuspLocalRing_isDiscreteValuationRing R p
  letI : IsLocalHom (localizedZeroRetraction R p) :=
    (localizedZeroRetraction_surjective R p).isLocalHom
  change CompleteDVRStalk.stalkCompletionRingEquiv
      (SpecialFiberCuspLocalRing R p) p.ResidueField
      (qParameter R p) (qParameter_irreducible R p)
      (CompleteDVRStalk.coefficientField_surjective_of_algebraMap_retraction
        (localizedZeroRetraction R p)
        (localizedZeroRetraction_comp_algebraMap R p))
      (algebraMap (SpecialFiberCuspLocalRing R p)
        (LocalCompletion.Ring (SpecialFiberCuspLocalRing R p))
        (qParameter R p)) = _
  exact CompleteDVRStalk.stalkCompletionRingEquiv_uniformizer
    (SpecialFiberCuspLocalRing R p) p.ResidueField
    (qParameter R p) (qParameter_irreducible R p)
    (CompleteDVRStalk.coefficientField_surjective_of_algebraMap_retraction
      (localizedZeroRetraction R p)
      (localizedZeroRetraction_comp_algebraMap R p))

/-- The logarithmic differential expansion `q d/dq` of the constructed cusp
parameter is normalized to `X`.  This is the form consumed by a Hecke action
on cotangent vectors or regular differentials. -/
@[simp]
theorem qCoordinate_logarithmicDerivative_qParameter
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime] :
    PowerSeries.X * PowerSeries.derivative p.ResidueField
        (qCoordinate R p
          (completionRingHom (SpecialFiberCuspLocalRing R p)
            (qParameter R p))) =
      (PowerSeries.X : PowerSeries p.ResidueField) := by
  calc
    PowerSeries.X * PowerSeries.derivative p.ResidueField
        (qCoordinate R p
          (completionRingHom (SpecialFiberCuspLocalRing R p)
            (qParameter R p))) =
        PowerSeries.X * PowerSeries.derivative p.ResidueField
          (PowerSeries.X : PowerSeries p.ResidueField) := by
            rw [qCoordinate_qParameter]
    _ = PowerSeries.X * 1 := by rw [PowerSeries.derivative_X]
    _ = PowerSeries.X := mul_one _

/-- The differential q-expansion of the geometric cusp parameter is nonzero. -/
theorem qCoordinate_logarithmicDerivative_qParameter_ne_zero
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime] :
    PowerSeries.X * PowerSeries.derivative p.ResidueField
        (qCoordinate R p
          (completionRingHom (SpecialFiberCuspLocalRing R p)
            (qParameter R p))) ≠
      (0 : PowerSeries p.ResidueField) := by
  rw [qCoordinate_logarithmicDerivative_qParameter]
  exact PowerSeries.X_ne_zero

namespace AffinePresentation

variable {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]

/-- The cusp local ring on an arbitrary affine presentation of the polynomial
chart. -/
abbrev CuspLocalRing (C : AffinePresentation R T)
    (p : Ideal R) [p.IsPrime] :=
  Localization.AtPrime (C.zeroSection.fiberPrime p)

private theorem fiber_isDomain
    (C : AffinePresentation R T) (p : Ideal R) [p.IsPrime] :
    IsDomain (p.Fiber T) :=
  (C.fiberCoordinate p).toRingEquiv.toMulEquiv.isDomain _

private theorem fiber_isPrincipalIdealRing
    (C : AffinePresentation R T) (p : Ideal R) [p.IsPrime] :
    IsPrincipalIdealRing (p.Fiber T) := by
  exact IsPrincipalIdealRing.of_surjective
    (C.fiberCoordinate p).symm.toRingHom
    (C.fiberCoordinate p).symm.surjective

/-- The cusp local ring of a transported affine presentation is a domain. -/
theorem cuspLocalRing_isDomain
    (C : AffinePresentation R T) (p : Ideal R) [p.IsPrime] :
    IsDomain (C.CuspLocalRing p) := by
  letI : IsDomain (p.Fiber T) := C.fiber_isDomain p
  infer_instance

/-- The transported cusp local ring is a DVR, derived from its polynomial
coordinate rather than supplied as a caller hypothesis. -/
theorem cuspLocalRing_isDiscreteValuationRing
    (C : AffinePresentation R T) (p : Ideal R) [p.IsPrime] :
    letI : IsDomain (C.CuspLocalRing p) := C.cuspLocalRing_isDomain p
    IsDiscreteValuationRing (C.CuspLocalRing p) := by
  letI : IsDomain (p.Fiber T) := C.fiber_isDomain p
  letI : IsPrincipalIdealRing (p.Fiber T) := C.fiber_isPrincipalIdealRing p
  letI : IsDomain (C.CuspLocalRing p) := C.cuspLocalRing_isDomain p
  have hcuspPrime : C.zeroSection.fiberPrime p ≠ ⊥ := by
    rw [C.fiberPrime_eq_span]
    exact Ideal.span_singleton_eq_bot.not.mpr (C.fiberVariable_ne_zero p)
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    (A := p.Fiber T) hcuspPrime (C.CuspLocalRing p)

/-- The transported q-parameter is a uniformizer of the transported cusp
local ring. -/
theorem qParameter_irreducible
    (C : AffinePresentation R T) (p : Ideal R) [p.IsPrime] :
    letI : IsDomain (C.CuspLocalRing p) := C.cuspLocalRing_isDomain p
    letI : IsDiscreteValuationRing (C.CuspLocalRing p) :=
      C.cuspLocalRing_isDiscreteValuationRing p
    Irreducible (C.qParameter p) := by
  letI : IsDomain (C.CuspLocalRing p) := C.cuspLocalRing_isDomain p
  letI : IsDiscreteValuationRing (C.CuspLocalRing p) :=
    C.cuspLocalRing_isDiscreteValuationRing p
  exact IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal
    (C.qParameter p) (C.qParameter_ne_zero p)
    (C.maximalIdeal_eq_span_qParameter p)

/-- The transported zero section extends to a retraction of the cusp local
ring onto the fibre coefficient field. -/
noncomputable def localizedZeroRetraction
    (C : AffinePresentation R T) (p : Ideal R) [p.IsPrime] :
    C.CuspLocalRing p →+* p.ResidueField :=
  IsLocalization.lift
    (M := (C.zeroSection.fiberPrime p).primeCompl)
    (S := C.CuspLocalRing p)
    (g := (C.zeroSection.fiberRetraction p).toRingHom)
    (fun y => by
      apply isUnit_iff_ne_zero.mpr
      intro hy
      exact y.property (by
        change C.zeroSection.fiberRetraction p y = 0
        exact hy))

/-- The transported localized zero evaluation fixes coefficients. -/
@[simp]
theorem localizedZeroRetraction_algebraMap
    (C : AffinePresentation R T) (p : Ideal R) [p.IsPrime]
    (c : p.ResidueField) :
    C.localizedZeroRetraction p
        (algebraMap p.ResidueField (C.CuspLocalRing p) c) = c := by
  rw [IsScalarTower.algebraMap_apply p.ResidueField (p.Fiber T)
    (C.CuspLocalRing p)]
  rw [localizedZeroRetraction, IsLocalization.lift_eq]
  exact (C.zeroSection.fiberRetraction p).commutes c

/-- The transported localized zero evaluation is surjective. -/
theorem localizedZeroRetraction_surjective
    (C : AffinePresentation R T) (p : Ideal R) [p.IsPrime] :
    Function.Surjective (C.localizedZeroRetraction p) := by
  intro c
  refine ⟨algebraMap p.ResidueField (C.CuspLocalRing p) c, ?_⟩
  exact C.localizedZeroRetraction_algebraMap p c

/-- The transported localized zero evaluation retracts the coefficient
embedding. -/
theorem localizedZeroRetraction_comp_algebraMap
    (C : AffinePresentation R T) (p : Ideal R) [p.IsPrime] :
    (C.localizedZeroRetraction p).comp
        (algebraMap p.ResidueField (C.CuspLocalRing p)) =
      RingHom.id p.ResidueField := by
  apply RingHom.ext
  intro c
  exact C.localizedZeroRetraction_algebraMap p c

/-- The completed q-coordinate on an arbitrary transported affine
presentation. -/
noncomputable def qCoordinate
    (C : AffinePresentation R T) (p : Ideal R) [p.IsPrime] :
    LocalCompletion.Ring (C.CuspLocalRing p) ≃+*
      PowerSeries p.ResidueField := by
  letI : IsDomain (C.CuspLocalRing p) := C.cuspLocalRing_isDomain p
  letI : IsDiscreteValuationRing (C.CuspLocalRing p) :=
    C.cuspLocalRing_isDiscreteValuationRing p
  letI : IsLocalHom (C.localizedZeroRetraction p) :=
    (C.localizedZeroRetraction_surjective p).isLocalHom
  exact CompleteDVRStalk.stalkCompletionRingEquivOfRetraction
    (C.CuspLocalRing p) p.ResidueField
    (C.localizedZeroRetraction p)
    (C.localizedZeroRetraction_comp_algebraMap p)
    (C.qParameter p) (C.qParameter_irreducible p)

/-- The transported geometric q-parameter maps to the power-series variable
in the constructed completed coordinate. -/
@[simp]
theorem qCoordinate_qParameter
    (C : AffinePresentation R T) (p : Ideal R) [p.IsPrime] :
    C.qCoordinate p
        (completionRingHom (C.CuspLocalRing p) (C.qParameter p)) =
      (PowerSeries.X : PowerSeries p.ResidueField) := by
  letI : IsDomain (C.CuspLocalRing p) := C.cuspLocalRing_isDomain p
  letI : IsDiscreteValuationRing (C.CuspLocalRing p) :=
    C.cuspLocalRing_isDiscreteValuationRing p
  letI : IsLocalHom (C.localizedZeroRetraction p) :=
    (C.localizedZeroRetraction_surjective p).isLocalHom
  change CompleteDVRStalk.stalkCompletionRingEquiv
      (C.CuspLocalRing p) p.ResidueField
      (C.qParameter p) (C.qParameter_irreducible p)
      (CompleteDVRStalk.coefficientField_surjective_of_algebraMap_retraction
        (C.localizedZeroRetraction p)
        (C.localizedZeroRetraction_comp_algebraMap p))
      (algebraMap (C.CuspLocalRing p)
        (LocalCompletion.Ring (C.CuspLocalRing p)) (C.qParameter p)) = _
  exact CompleteDVRStalk.stalkCompletionRingEquiv_uniformizer
    (C.CuspLocalRing p) p.ResidueField
    (C.qParameter p) (C.qParameter_irreducible p)
    (CompleteDVRStalk.coefficientField_surjective_of_algebraMap_retraction
      (C.localizedZeroRetraction p)
      (C.localizedZeroRetraction_comp_algebraMap p))

/-- The logarithmic differential expansion of the transported q-parameter is
normalized to `X`. -/
@[simp]
theorem qCoordinate_logarithmicDerivative_qParameter
    (C : AffinePresentation R T) (p : Ideal R) [p.IsPrime] :
    PowerSeries.X * PowerSeries.derivative p.ResidueField
        (C.qCoordinate p
          (completionRingHom (C.CuspLocalRing p) (C.qParameter p))) =
      (PowerSeries.X : PowerSeries p.ResidueField) := by
  calc
    PowerSeries.X * PowerSeries.derivative p.ResidueField
        (C.qCoordinate p
          (completionRingHom (C.CuspLocalRing p) (C.qParameter p))) =
        PowerSeries.X * PowerSeries.derivative p.ResidueField
          (PowerSeries.X : PowerSeries p.ResidueField) := by
            rw [C.qCoordinate_qParameter]
    _ = PowerSeries.X * 1 := by rw [PowerSeries.derivative_X]
    _ = PowerSeries.X := mul_one _

/-- The transported cusp parameter has nonzero differential q-expansion. -/
theorem qCoordinate_logarithmicDerivative_qParameter_ne_zero
    (C : AffinePresentation R T) (p : Ideal R) [p.IsPrime] :
    PowerSeries.X * PowerSeries.derivative p.ResidueField
        (C.qCoordinate p
          (completionRingHom (C.CuspLocalRing p) (C.qParameter p))) ≠
      (0 : PowerSeries p.ResidueField) := by
  rw [C.qCoordinate_logarithmicDerivative_qParameter]
  exact PowerSeries.X_ne_zero

end AffinePresentation

end MazurTorsion.ModularCurve.AffineCuspPolynomialChart

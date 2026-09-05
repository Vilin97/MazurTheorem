/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/

import MazurTorsion.NumberTheory.XZeroFortyNineEtaOpenImmersion

/-!
# Rational points of the eta-equation scheme

This file identifies the earlier coordinate type `EtaAffinePoint` with ring
homomorphisms from the affine eta-equation coordinate ring to `ℚ`.  It then
identifies `EtaOpenPoint`, whose coordinate condition is `x ≠ 0`, with ring
homomorphisms from the scheme-theoretic regularity localization

`D(x (x² + 7x + 7))`.

The second identification uses the checked fact that `x² + 7x + 7` has no
rational zero.  Thus over `ℚ` the localization condition is exactly the
original point-level condition, even though over arbitrary schemes both
factors must be inverted.  Full faithfulness of `Spec` then gives an explicit
equivalence between `EtaOpenPoint` and honest `Spec ℚ` morphisms into the eta
open scheme.

The construction is coordinate-level and does not use the known emptiness of
either point type.  The design boundary still contains no modular eta
function, coarse modular curve, or classifying map.  The named downstream
consumer is `openSchemeRationalPointEquiv`: a future modular construction may
produce a rational eta pair and obtain the corresponding scheme point without
any supplied point-set comparison.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace MazurTorsion.XZeroFortyNine.EtaSchemeModel

private def etaPointEvaluation (P : EtaAffinePoint) :
    MvPolynomial (Fin 2) ℚ →+* ℚ :=
  MvPolynomial.eval₂Hom (RingHom.id ℚ) ![P.x, P.y]

private theorem etaPointEvaluation_polynomial (P : EtaAffinePoint) :
    etaPointEvaluation P polynomial = 0 := by
  simpa [etaPointEvaluation, polynomial, equationExpression,
    etaPlaneEquation] using P.equation

private theorem etaPointEvaluation_eq_zero_of_mem (P : EtaAffinePoint)
    (p : MvPolynomial (Fin 2) ℚ) (hp : p ∈ ideal) :
    etaPointEvaluation P p = 0 := by
  apply (show ideal ≤ RingHom.ker (etaPointEvaluation P) by
    apply Ideal.span_le.mpr
    intro q hq
    rw [Set.mem_singleton_iff.mp hq]
    exact etaPointEvaluation_polynomial P) hp

/-- Evaluate the affine eta-equation coordinate ring at a rational eta
point. -/
def etaAffinePointToCoordinateRingHom (P : EtaAffinePoint) :
    coordinateRing →+* ℚ :=
  Ideal.Quotient.lift ideal (etaPointEvaluation P)
    (etaPointEvaluation_eq_zero_of_mem P)

/-- Evaluation sends the universal eta abscissa to the point's abscissa. -/
@[simp]
theorem etaAffinePointToCoordinateRingHom_x (P : EtaAffinePoint) :
    etaAffinePointToCoordinateRingHom P x = P.x := by
  simp [etaAffinePointToCoordinateRingHom, etaPointEvaluation, x]

/-- Evaluation sends the universal eta ordinate to the point's ordinate. -/
@[simp]
theorem etaAffinePointToCoordinateRingHom_y (P : EtaAffinePoint) :
    etaAffinePointToCoordinateRingHom P y = P.y := by
  simp [etaAffinePointToCoordinateRingHom, etaPointEvaluation, y]

/-- Read the two universal coordinates through a rational ring homomorphism
to recover an affine eta point. -/
def coordinateRingHomToEtaAffinePoint (f : coordinateRing →+* ℚ) :
    EtaAffinePoint where
  x := f x
  y := f y
  equation := etaPlaneEquation_iff_equationExpression _ _ |>.2 <| by
    have h := congrArg f equation
    simpa only [equationExpression, f.map_sub, f.map_add, f.map_mul,
      f.map_pow, map_ofNat f 5, map_ofNat f 7, map_ofNat f 21,
      map_ofNat f 49, map_ofNat f 147, map_ofNat f 343,
      f.map_zero] using h

/-- The recovered affine eta abscissa is evaluation of the universal `x`. -/
@[simp]
theorem coordinateRingHomToEtaAffinePoint_x (f : coordinateRing →+* ℚ) :
    (coordinateRingHomToEtaAffinePoint f).x = f x :=
  rfl

/-- The recovered affine eta ordinate is evaluation of the universal `y`. -/
@[simp]
theorem coordinateRingHomToEtaAffinePoint_y (f : coordinateRing →+* ℚ) :
    (coordinateRingHomToEtaAffinePoint f).y = f y :=
  rfl

private theorem coordinateRingHomToEtaAffinePoint_toHom
    (P : EtaAffinePoint) :
    coordinateRingHomToEtaAffinePoint
        (etaAffinePointToCoordinateRingHom P) = P := by
  cases P
  simp [coordinateRingHomToEtaAffinePoint]

private theorem etaAffinePointToCoordinateRingHom_toPoint
    (f : coordinateRing →+* ℚ) :
    etaAffinePointToCoordinateRingHom
        (coordinateRingHomToEtaAffinePoint f) = f := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, etaAffinePointToCoordinateRingHom,
      Ideal.Quotient.lift_mk, etaPointEvaluation,
      MvPolynomial.eval₂Hom_C]
    change a = f (coefficientHom a)
    exact (DFunLike.congr_fun
      (RingHom.ext_rat (f.comp coefficientHom) (RingHom.id ℚ)) a).symm
  · intro i
    fin_cases i <;>
      simp [etaAffinePointToCoordinateRingHom, etaPointEvaluation,
        coordinateRingHomToEtaAffinePoint, x, y]

/-- Rational affine eta points are exactly ring homomorphisms from the
eta-equation coordinate ring to `ℚ`. -/
def coordinateRingHomEquivEtaAffinePoint :
    (coordinateRing →+* ℚ) ≃ EtaAffinePoint where
  toFun := coordinateRingHomToEtaAffinePoint
  invFun := etaAffinePointToCoordinateRingHom
  left_inv := etaAffinePointToCoordinateRingHom_toPoint
  right_inv := coordinateRingHomToEtaAffinePoint_toHom

private def restrictOpenRingHom (f : openCoordinateRing →+* ℚ) :
    coordinateRing →+* ℚ :=
  f.comp (algebraMap coordinateRing openCoordinateRing)

/-- Restrict a rational point of the localization to its two eta coordinates.
The localized universal `x` is a unit, so the resulting point lies in the
original point-level open locus. -/
def openRingHomToEtaOpenPoint (f : openCoordinateRing →+* ℚ) :
    EtaOpenPoint :=
  ⟨coordinateRingHomToEtaAffinePoint (restrictOpenRingHom f), by
    change f openX ≠ 0
    exact (openX_isUnit.map f).ne_zero⟩

/-- The recovered open eta point has abscissa given by the localized
universal `x`. -/
@[simp]
theorem openRingHomToEtaOpenPoint_x (f : openCoordinateRing →+* ℚ) :
    (openRingHomToEtaOpenPoint f).1.x = f openX :=
  rfl

/-- The recovered open eta point has ordinate given by the localized
universal `y`. -/
@[simp]
theorem openRingHomToEtaOpenPoint_y (f : openCoordinateRing →+* ℚ) :
    (openRingHomToEtaOpenPoint f).1.y = f openY :=
  rfl

private theorem etaAffinePointToCoordinateRingHom_openElement
    (P : EtaOpenPoint) :
    etaAffinePointToCoordinateRingHom P.1 openElement =
      P.1.x * (P.1.x ^ 2 + 7 * P.1.x + 7) := by
  simp only [openElement, denominator,
    (etaAffinePointToCoordinateRingHom P.1).map_mul,
    (etaAffinePointToCoordinateRingHom P.1).map_add,
    (etaAffinePointToCoordinateRingHom P.1).map_pow,
    map_ofNat (etaAffinePointToCoordinateRingHom P.1) 7,
    etaAffinePointToCoordinateRingHom_x]

private theorem etaAffinePointToCoordinateRingHom_openElement_isUnit
    (P : EtaOpenPoint) :
    IsUnit (etaAffinePointToCoordinateRingHom P.1 openElement) := by
  rw [etaAffinePointToCoordinateRingHom_openElement]
  exact isUnit_iff_ne_zero.mpr
    (mul_ne_zero P.2 (etaModelDenominator_ne_zero P.1.x))

/-- Extend evaluation at an open eta point across the full
scheme-theoretic regularity localization. -/
def etaOpenPointToOpenRingHom (P : EtaOpenPoint) :
    openCoordinateRing →+* ℚ :=
  IsLocalization.Away.lift openElement
    (etaAffinePointToCoordinateRingHom_openElement_isUnit P)

/-- The localized evaluation map restricts to ordinary eta-coordinate
evaluation. -/
@[simp]
theorem etaOpenPointToOpenRingHom_algebraMap (P : EtaOpenPoint)
    (a : coordinateRing) :
    etaOpenPointToOpenRingHom P
        (algebraMap coordinateRing openCoordinateRing a) =
      etaAffinePointToCoordinateRingHom P.1 a := by
  exact IsLocalization.Away.lift_eq
    (x := openElement) (g := etaAffinePointToCoordinateRingHom P.1)
    (etaAffinePointToCoordinateRingHom_openElement_isUnit P) a

/-- Localized evaluation recovers the open point's eta abscissa. -/
@[simp]
theorem etaOpenPointToOpenRingHom_openX (P : EtaOpenPoint) :
    etaOpenPointToOpenRingHom P openX = P.1.x := by
  rw [openX, etaOpenPointToOpenRingHom_algebraMap,
    etaAffinePointToCoordinateRingHom_x]

/-- Localized evaluation recovers the open point's eta ordinate. -/
@[simp]
theorem etaOpenPointToOpenRingHom_openY (P : EtaOpenPoint) :
    etaOpenPointToOpenRingHom P openY = P.1.y := by
  rw [openY, etaOpenPointToOpenRingHom_algebraMap,
    etaAffinePointToCoordinateRingHom_y]

private theorem openRingHomToEtaOpenPoint_toHom (P : EtaOpenPoint) :
    openRingHomToEtaOpenPoint (etaOpenPointToOpenRingHom P) = P := by
  apply Subtype.ext
  change coordinateRingHomToEtaAffinePoint
      ((etaOpenPointToOpenRingHom P).comp
        (algebraMap coordinateRing openCoordinateRing)) = P.1
  rw [show (etaOpenPointToOpenRingHom P).comp
      (algebraMap coordinateRing openCoordinateRing) =
        etaAffinePointToCoordinateRingHom P.1 by
    apply RingHom.ext
    intro a
    exact etaOpenPointToOpenRingHom_algebraMap P a]
  exact coordinateRingHomToEtaAffinePoint_toHom P.1

private theorem etaOpenPointToOpenRingHom_toPoint
    (f : openCoordinateRing →+* ℚ) :
    etaOpenPointToOpenRingHom (openRingHomToEtaOpenPoint f) = f := by
  apply IsLocalization.ringHom_ext (Submonoid.powers openElement)
  change (etaOpenPointToOpenRingHom (openRingHomToEtaOpenPoint f)).comp
      (algebraMap coordinateRing openCoordinateRing) =
    f.comp (algebraMap coordinateRing openCoordinateRing)
  rw [show (etaOpenPointToOpenRingHom
      (openRingHomToEtaOpenPoint f)).comp
        (algebraMap coordinateRing openCoordinateRing) =
      etaAffinePointToCoordinateRingHom
        (openRingHomToEtaOpenPoint f).1 by
    apply RingHom.ext
    intro a
    exact etaOpenPointToOpenRingHom_algebraMap
      (openRingHomToEtaOpenPoint f) a]
  exact etaAffinePointToCoordinateRingHom_toPoint
    (f.comp (algebraMap coordinateRing openCoordinateRing))

/-- Rational open eta points are exactly ring homomorphisms from the
regularity localization to `ℚ`. -/
def openRingHomEquivEtaOpenPoint :
    (openCoordinateRing →+* ℚ) ≃ EtaOpenPoint where
  toFun := openRingHomToEtaOpenPoint
  invFun := etaOpenPointToOpenRingHom
  left_inv := etaOpenPointToOpenRingHom_toPoint
  right_inv := openRingHomToEtaOpenPoint_toHom

private def openRingHomEquivCommRingCatHom :
    (openCoordinateRing →+* ℚ) ≃
      (CommRingCat.of openCoordinateRing ⟶ CommRingCat.of ℚ) where
  toFun := CommRingCat.ofHom
  invFun f := f.hom
  left_inv f := rfl
  right_inv f := by
    apply CommRingCat.hom_ext
    rfl

/-- Honest rational points of the eta regularity scheme are exactly the
original rational open eta pairs.  Both directions are defined by explicit
coordinate evaluation and localization. -/
def openSchemeRationalPointEquiv :
    (Spec (.of ℚ) ⟶ openScheme) ≃ EtaOpenPoint :=
  Spec.homEquiv.trans
    (openRingHomEquivCommRingCatHom.symm.trans
      openRingHomEquivEtaOpenPoint)

/-- The `x` coordinate of the eta pair corresponding to a scheme point is
evaluation of the localized universal abscissa. -/
@[simp]
theorem openSchemeRationalPointEquiv_apply_x
    (p : Spec (.of ℚ) ⟶ openScheme) :
    (openSchemeRationalPointEquiv p).1.x =
      (Spec.homEquiv p).hom openX :=
  rfl

/-- The `y` coordinate of the eta pair corresponding to a scheme point is
evaluation of the localized universal ordinate. -/
@[simp]
theorem openSchemeRationalPointEquiv_apply_y
    (p : Spec (.of ℚ) ⟶ openScheme) :
    (openSchemeRationalPointEquiv p).1.y =
      (Spec.homEquiv p).hom openY :=
  rfl

end MazurTorsion.XZeroFortyNine.EtaSchemeModel

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfQuotientEuler
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.QuasiFiniteFppfConnecting

/-!
# Cardinal bounds for quasi-finite fppf quotient presentations

An actual quasi-finite fppf quotient presentation now supplies the entire low-degree exact
sequence through the middle global `H¹` term.  Exactness at that middle term has an additional
finiteness consequence: finite kernel and quotient `H¹` groups force the middle `H¹` group to
be finite.  Thus the Euler bound needs certified cardinal data only for the five endpoints; it
does not ask the caller for either middle-`H¹` finiteness or any exactness assertion.

The final theorem transports a finite-flat quotient through the checked quasi-finite adapter.
It is a concrete downstream consumer and verifies that no map or cohomology carrier changes
under the broader interface.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme

universe u

variable {S : Scheme.{u}}

namespace FppfQuotientPresentation

variable {G : QuasiFiniteFlatCommGroupScheme S}

/-- Finiteness of kernel and quotient `H¹` propagates across a genuine quasi-finite fppf
quotient presentation. -/
theorem middleFppfHOne_finite (D : FppfQuotientPresentation G)
    [Finite D.kernelPresentation.kernel.FppfHOne.{u}]
    [Finite D.quotient.FppfHOne.{u}] :
    Finite G.FppfHOne.{u} :=
  FiniteFlatCommGroupScheme.FppfLowDegreeExactSequence.finite_middle_of_mulExact
    (fppfHOneMap D.kernelPresentation.inclusion)
    (fppfHOneMap D.project)
    D.exact_fppfHOneMap_inclusion_project

end FppfQuotientPresentation

namespace FppfLowDegreeExactSequence

/-- The multiplicative Euler inequality for a quasi-finite fppf quotient.  The five endpoint
certificates supply all endpoint finiteness, and middle-`H¹` finiteness follows from exactness. -/
theorem fppfHOne_card_euler_le_ofFppfQuotientPresentation
    {p : ℕ} {G : QuasiFiniteFlatCommGroupScheme S}
    (D : FppfQuotientPresentation G)
    (kernelHZeroData : FiniteFlatCommGroupScheme.FinitePGroup.CertifiedData p
      (BasePoint D.kernelPresentation.kernel))
    (middleHZeroData : FiniteFlatCommGroupScheme.FinitePGroup.CertifiedData p
      (BasePoint G))
    (quotientHZeroData : FiniteFlatCommGroupScheme.FinitePGroup.CertifiedData p
      (BasePoint D.quotient))
    (kernelHOneData : FiniteFlatCommGroupScheme.FinitePGroup.CertifiedData p
      D.kernelPresentation.kernel.FppfHOne.{u})
    (quotientHOneData : FiniteFlatCommGroupScheme.FinitePGroup.CertifiedData p
      D.quotient.FppfHOne.{u}) :
    Nat.card G.FppfHOne.{u} *
        Nat.card (BasePoint D.kernelPresentation.kernel) *
        Nat.card (BasePoint D.quotient) ≤
      Nat.card (BasePoint G) *
        Nat.card D.kernelPresentation.kernel.FppfHOne.{u} *
        Nat.card D.quotient.FppfHOne.{u} := by
  letI : Finite (BasePoint D.kernelPresentation.kernel) := kernelHZeroData.finite
  letI : Finite (BasePoint G) := middleHZeroData.finite
  letI : Finite (BasePoint D.quotient) := quotientHZeroData.finite
  letI : Finite D.kernelPresentation.kernel.FppfHOne.{u} := kernelHOneData.finite
  letI : Finite D.quotient.FppfHOne.{u} := quotientHOneData.finite
  letI : Finite G.FppfHOne.{u} := D.middleFppfHOne_finite
  exact FiniteFlatCommGroupScheme.FppfLowDegreeExactSequence.card_euler_le_of_exact
    (mapPoint D.kernelPresentation.inclusion (baseObject S))
    (mapPoint D.project (baseObject S)) D.boundaryHom
    (fppfHOneMap D.kernelPresentation.inclusion) (fppfHOneMap D.project)
    (D.kernelPresentation.inclusion_point_injective (baseObject S))
    (D.kernelPresentation.point_mulExact (baseObject S))
    D.exact_project_boundaryHom D.exact_boundaryHom_fppfHOneMap
    D.exact_fppfHOneMap_inclusion_project

/-- Certified endpoint cardinal lengths bound the middle global fppf `H¹` of an actual
quasi-finite quotient presentation.  No middle-cardinality certificate, middle-finiteness
premise, or caller-supplied exactness remains. -/
theorem fppfHOne_natCard_le_pow_ofFppfQuotientPresentation
    {p : ℕ} {G : QuasiFiniteFlatCommGroupScheme S}
    (D : FppfQuotientPresentation G)
    (kernelHZeroData : FiniteFlatCommGroupScheme.FinitePGroup.CertifiedData p
      (BasePoint D.kernelPresentation.kernel))
    (middleHZeroData : FiniteFlatCommGroupScheme.FinitePGroup.CertifiedData p
      (BasePoint G))
    (quotientHZeroData : FiniteFlatCommGroupScheme.FinitePGroup.CertifiedData p
      (BasePoint D.quotient))
    (kernelHOneData : FiniteFlatCommGroupScheme.FinitePGroup.CertifiedData p
      D.kernelPresentation.kernel.FppfHOne.{u})
    (quotientHOneData : FiniteFlatCommGroupScheme.FinitePGroup.CertifiedData p
      D.quotient.FppfHOne.{u})
    (hp : p.Prime) (bound : ℕ)
    (hbound :
      middleHZeroData.length + kernelHOneData.length + quotientHOneData.length ≤
        bound + kernelHZeroData.length + quotientHZeroData.length) :
    Nat.card G.FppfHOne.{u} ≤ p ^ bound := by
  letI : Finite (BasePoint D.kernelPresentation.kernel) := kernelHZeroData.finite
  letI : Finite (BasePoint G) := middleHZeroData.finite
  letI : Finite (BasePoint D.quotient) := quotientHZeroData.finite
  letI : Finite D.kernelPresentation.kernel.FppfHOne.{u} := kernelHOneData.finite
  letI : Finite D.quotient.FppfHOne.{u} := quotientHOneData.finite
  letI : Finite G.FppfHOne.{u} := D.middleFppfHOne_finite
  have hcard := fppfHOne_card_euler_le_ofFppfQuotientPresentation D
    kernelHZeroData middleHZeroData quotientHZeroData
    kernelHOneData quotientHOneData
  rw [kernelHZeroData.card_eq, middleHZeroData.card_eq,
    quotientHZeroData.card_eq, kernelHOneData.card_eq,
    quotientHOneData.card_eq] at hcard
  have hcard' :
      Nat.card G.FppfHOne.{u} *
          p ^ (kernelHZeroData.length + quotientHZeroData.length) ≤
        p ^ (middleHZeroData.length + kernelHOneData.length +
          quotientHOneData.length) := by
    simpa [pow_add, Nat.mul_assoc] using hcard
  have hpowers :
      p ^ (middleHZeroData.length + kernelHOneData.length +
          quotientHOneData.length) ≤
        p ^ (bound + kernelHZeroData.length + quotientHZeroData.length) :=
    (Nat.pow_le_pow_iff_right hp.one_lt).mpr hbound
  have hcancel :
      Nat.card G.FppfHOne.{u} *
          p ^ (kernelHZeroData.length + quotientHZeroData.length) ≤
        p ^ bound * p ^ (kernelHZeroData.length + quotientHZeroData.length) := by
    calc
      Nat.card G.FppfHOne.{u} *
          p ^ (kernelHZeroData.length + quotientHZeroData.length) ≤
          p ^ (middleHZeroData.length + kernelHOneData.length +
            quotientHOneData.length) := hcard'
      _ ≤ p ^ (bound + kernelHZeroData.length + quotientHZeroData.length) := hpowers
      _ = p ^ bound * p ^ (kernelHZeroData.length + quotientHZeroData.length) := by
        rw [add_assoc, pow_add, pow_add]
  exact Nat.le_of_mul_le_mul_right hcancel
    (pow_pos hp.pos (kernelHZeroData.length + quotientHZeroData.length))

/-- A finite-flat fppf quotient consumes the quasi-finite Euler theorem through the checked
adapter.  This compatibility theorem agrees with the repaired finite-flat cardinal API: neither
interface requires a middle-`H¹` finiteness premise. -/
theorem finiteFlat_fppfHOne_natCard_le_pow_viaQuasiFinite
    {p : ℕ} {G : _root_.AlgebraicGeometry.FiniteFlatCommGroupScheme S}
    (D : FiniteFlatCommGroupScheme.FppfQuotientPresentation G)
    [LocallyOfFinitePresentation G.obj.X.hom]
    [LocallyOfFinitePresentation D.quotient.obj.X.hom]
    [LocallyOfFinitePresentation D.kernelPresentation.kernel.obj.X.hom]
    (kernelHZeroData : FiniteFlatCommGroupScheme.FinitePGroup.CertifiedData p
      (FiniteFlatCommGroupScheme.BasePoint D.kernelPresentation.kernel))
    (middleHZeroData : FiniteFlatCommGroupScheme.FinitePGroup.CertifiedData p
      (FiniteFlatCommGroupScheme.BasePoint G))
    (quotientHZeroData : FiniteFlatCommGroupScheme.FinitePGroup.CertifiedData p
      (FiniteFlatCommGroupScheme.BasePoint D.quotient))
    (kernelHOneData : FiniteFlatCommGroupScheme.FinitePGroup.CertifiedData p
      D.kernelPresentation.kernel.FppfHOne.{u})
    (quotientHOneData : FiniteFlatCommGroupScheme.FinitePGroup.CertifiedData p
      D.quotient.FppfHOne.{u})
    (hp : p.Prime) (bound : ℕ)
    (hbound :
      middleHZeroData.length + kernelHOneData.length + quotientHOneData.length ≤
        bound + kernelHZeroData.length + quotientHZeroData.length) :
    Nat.card G.FppfHOne.{u} ≤ p ^ bound :=
  fppfHOne_natCard_le_pow_ofFppfQuotientPresentation
      (FppfQuotientPresentation.ofFiniteFlat D)
      kernelHZeroData middleHZeroData quotientHZeroData
      kernelHOneData quotientHOneData hp bound hbound

end FppfLowDegreeExactSequence

end AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme

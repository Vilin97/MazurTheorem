/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfQuotientConnecting

/-!
# Cardinal bounds from actual fppf quotient presentations

The checked quotient presentation now constructs every exactness proof in its six-term
low-degree sequence.  This file is its first cardinal downstream consumer: five endpoint
finite-cardinality certificates, finiteness of the middle global fppf `H¹`, and the numerical
Euler bound give the desired cardinal bound, with no caller-supplied exactness assertion or
circular certificate of the cardinal being bounded.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

universe u

variable {S : Scheme.{u}}

namespace FppfLowDegreeExactSequence

/-- Certified endpoint cardinal lengths for an actual quotient presentation imply the expected
bound on the middle global fppf `H¹`.  Its finiteness is required, but not a certificate of its
cardinality; all exactness is supplied by the quotient presentation itself. -/
theorem fppfHOne_natCard_le_pow_ofFppfQuotientPresentation
    {p : ℕ} {G : FiniteFlatCommGroupScheme S}
    (D : FppfQuotientPresentation G)
    (kernelHZeroData : FinitePGroup.CertifiedData p
      (BasePoint D.kernelPresentation.kernel))
    (middleHZeroData : FinitePGroup.CertifiedData p (BasePoint G))
    (quotientHZeroData : FinitePGroup.CertifiedData p (BasePoint D.quotient))
    (kernelHOneData : FinitePGroup.CertifiedData p
      D.kernelPresentation.kernel.FppfHOne.{u})
    (middleHOneFinite : Finite G.FppfHOne.{u})
    (quotientHOneData : FinitePGroup.CertifiedData p D.quotient.FppfHOne.{u})
    (hp : p.Prime) (bound : ℕ)
    (hbound :
      middleHZeroData.length + kernelHOneData.length + quotientHOneData.length ≤
        bound + kernelHZeroData.length + quotientHZeroData.length) :
    Nat.card G.FppfHOne.{u} ≤ p ^ bound := by
  letI : Finite (BasePoint D.kernelPresentation.kernel) := kernelHZeroData.finite
  letI : Finite (BasePoint G) := middleHZeroData.finite
  letI : Finite (BasePoint D.quotient) := quotientHZeroData.finite
  letI : Finite D.kernelPresentation.kernel.FppfHOne.{u} := kernelHOneData.finite
  letI : Finite G.FppfHOne.{u} := middleHOneFinite
  letI : Finite D.quotient.FppfHOne.{u} := quotientHOneData.finite
  have hcard := card_euler_le_of_exact
    (mapPoint D.kernelPresentation.inclusion (baseObject S))
    (mapPoint D.project (baseObject S)) D.boundaryHom
    (fppfHOneMap D.kernelPresentation.inclusion) (fppfHOneMap D.project)
    (D.kernelPresentation.inclusion_point_injective (baseObject S))
    (D.kernelPresentation.point_mulExact (baseObject S))
    D.exact_project_boundaryHom D.exact_boundaryHom_fppfHOneMap
    D.exact_fppfHOneMap_inclusion_project
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

end FppfLowDegreeExactSequence

end AlgebraicGeometry.FiniteFlatCommGroupScheme

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfQuotientConnecting

/-!
# Cardinal bounds from actual fppf quotient presentations

The checked quotient presentation now constructs every exactness proof in its six-term
low-degree sequence.  This file is its first cardinal downstream consumer: six finite-cardinality
certificates and the numerical Euler bound give the desired bound on the actual middle global
fppf `H¹`, with no caller-supplied exactness assertion.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

universe u

variable {S : Scheme.{u}}

namespace FppfLowDegreeExactSequence

/-- Certified cardinal lengths for an actual quotient presentation imply the expected bound on
the middle global fppf `H¹`, with all exactness supplied by the quotient presentation itself. -/
theorem fppfHOne_natCard_le_pow_ofFppfQuotientPresentation
    {p : ℕ} {G : FiniteFlatCommGroupScheme S}
    (D : FppfQuotientPresentation G)
    (kernelHZeroData : FinitePGroup.CertifiedData p
      (BasePoint D.kernelPresentation.kernel))
    (middleHZeroData : FinitePGroup.CertifiedData p (BasePoint G))
    (quotientHZeroData : FinitePGroup.CertifiedData p (BasePoint D.quotient))
    (kernelHOneData : FinitePGroup.CertifiedData p
      D.kernelPresentation.kernel.FppfHOne.{u})
    (middleHOneData : FinitePGroup.CertifiedData p G.FppfHOne.{u})
    (quotientHOneData : FinitePGroup.CertifiedData p D.quotient.FppfHOne.{u})
    (hp : p.Prime) (bound : ℕ)
    (hbound :
      middleHZeroData.length + kernelHOneData.length + quotientHOneData.length ≤
        bound + kernelHZeroData.length + quotientHZeroData.length) :
    Nat.card G.FppfHOne.{u} ≤ p ^ bound := by
  let E := ofFppfQuotientPresentation D kernelHZeroData middleHZeroData
    quotientHZeroData kernelHOneData middleHOneData quotientHOneData
  have hE :
      E.middleHZero.length + E.kernelHOne.length + E.quotientHOne.length ≤
        bound + E.kernelHZero.length + E.quotientHZero.length := by
    exact hbound
  exact E.middleHOne_natCard_le_pow hp bound hE

end FppfLowDegreeExactSequence

end AlgebraicGeometry.FiniteFlatCommGroupScheme

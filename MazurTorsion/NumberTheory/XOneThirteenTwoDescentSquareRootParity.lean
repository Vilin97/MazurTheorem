/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenTwoDescentModFourCertificate

/-!
# Parity of square roots in the `X₁(13)` descent order

This leaf records the small finite fact needed to pass from a square in the
dyadic sextic algebra to the existing mod-four Kummer certificate.  If a
coefficient vector has square zero modulo four, then every coefficient is
even.  The proof first uses the algebraic normalization theorem from
`XOneThirteenTwoDescentModFourCertificate`, so the final decision checks only
the 64 binary parity vectors.
-/

namespace MazurTorsion.XOneThirteenTwoDescentSquareRootParity

open XOneThirteenTwoDescentModFourCertificate

/-- The bounded core of the parity certificate.  It ranges over the 64
normalized binary roots, rather than arbitrary vectors modulo four. -/
theorem normalizedRoot_eq_zero_of_square_eq_zero
    (r : V2)
    (hr : quotientMul (normalizedRoot r) (normalizedRoot r) = 0) :
    r = 0 := by
  revert hr
  decide +revert

/-- A square which vanishes in the power-basis order modulo four has an even
root coefficient vector. -/
theorem parityVector_eq_zero_of_quotientMul_self_eq_zero
    (x : V4) (hx : quotientMul x x = 0) :
    parityVector x = 0 := by
  have hnormalized :
      quotientMul (normalizedRoot (parityVector x))
          (normalizedRoot (parityVector x)) = 0 := by
    rw [← quotientMul_self_eq_normalizedRoot x]
    exact hx
  exact normalizedRoot_eq_zero_of_square_eq_zero (parityVector x) hnormalized

end MazurTorsion.XOneThirteenTwoDescentSquareRootParity

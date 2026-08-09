/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultIntegrality
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitCertificate

/-!
# Arithmetic exclusion for a Lécacheux order-twenty-five orbit

This file composes the characteristic-zero orbit certificate with the
three-adic Lehmer-root exclusion.  The cyclic-orbit, Lehmer-root, and
three-integrality hypotheses remain explicit: deriving them from an actual
marked elliptic curve is the remaining geometric and integral-model bridge.
-/

namespace MazurTorsion.Kubert

/-- A five-term Lécacheux orbit cannot simultaneously satisfy its six cyclic
relations and arise from two Lehmer roots at a three-integral parameter.

The orbit relations force Brunault's polynomial to vanish at `(a, -c)`,
whereas the Lehmer-root integrality theorem and the checked `F₃` enumeration
force the same value to be nonzero. -/
theorem no_orderTwentyFiveBrunaultOrbit_of_threeIntegral_lehmerRoots
    (n a b c d e : ℚ)
    (hn : orderTwentyFiveRatIsThreeIntegral n)
    (ha : a ≠ 1)
    (haRoot : orderTwentyFiveLehmerPolynomial n a = 0)
    (hcRoot : orderTwentyFiveLehmerPolynomial n c = 0)
    (h0 : orderTwentyFiveOrbitRelationZero a b c d e = 0)
    (h1 : orderTwentyFiveOrbitRelationOne a b c d e = 0)
    (h2 : orderTwentyFiveOrbitRelationTwo a b c d e = 0)
    (h3 : orderTwentyFiveOrbitRelationThree a b c d e = 0)
    (h4 : orderTwentyFiveOrbitRelationFour a b c d e = 0)
    (h5 : orderTwentyFiveOrbitRelationFive a b c d e = 0) :
    False := by
  exact
    orderTwentyFiveBrunaultPolynomial_ne_zero_of_lehmer_roots
      n a c hn haRoot hcRoot
      (orderTwentyFiveBrunaultPolynomial_eq_zero_of_orbit
        a b c d e ha h0 h1 h2 h3 h4 h5)

end MazurTorsion.Kubert

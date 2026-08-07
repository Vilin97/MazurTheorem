/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassAbelianVarietyTransfer
import MazurTorsion.NumberTheory.OrderThirtyFiveEisensteinIdealSupport

/-!
# Transferring the level-35 rank-zero calculation to an abelian variety

The explicit Weierstrass model expected for `X₀(35)/w₅` already has a checked finite rational
point group.  This file transports that result to the rational points of any supplied abelian
variety whose underlying scheme is isomorphic to the concrete projective cubic.

Constructing the modular quotient and the required scheme isomorphism remain separate geometric
obligations.  No such identification is inferred from rational-point data here.
-/

open CategoryTheory

namespace MazurTorsion.OrderThirtyFive

open ModularCurve.XZeroFiniteFlatModuli

/-- A scheme isomorphism from the explicit rank-zero level-`35` model transfers its checked
rational-point finiteness to the supplied abelian variety. -/
theorem optimalQuotientAbelianVariety_rationalPoint_finite_of_iso
    (A : TauCeti.AlgebraicGeometry.AbelianVariety ℚ)
    (e : WeierstrassProjectiveCubic.toOver optimalQuotientModel ≅ A.toOver) :
    Finite (AbelianVarietyRationalPoint A) :=
  WeierstrassProjectiveCubic.rationalPoint_finite_of_iso
    optimalQuotientModel A e optimalQuotientModel_finite

end MazurTorsion.OrderThirtyFive

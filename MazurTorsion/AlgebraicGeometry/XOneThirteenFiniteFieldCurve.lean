/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.XOneThirteenAffineCurve
import MazurTorsion.NumberTheory.XOneThirteenFiniteField

/-!
# Finite certificates as points of the affine `X₁(13)` scheme

The elementary affine solution types previously used for point counting are
identified here with literal morphisms from `Spec 𝔽₃` and `Spec 𝔽₅` to the
affine order-thirteen curve.  Thus the checked counts `4` and `4` are now
counts of points on an actual affine scheme.

The two normalized infinity directions are not part of this affine scheme.
They will enter only after the reciprocal chart has been glued in; no
projective or Picard identification is asserted in this file.
-/

namespace MazurTorsion.XOneThirteenFiniteFieldCurve

open Polynomial

namespace Curve

abbrev F3 := XOneThirteenFiniteField.F3
abbrev F5 := XOneThirteenFiniteField.F5

/-- The generic sextic specializes to the polynomial used by the `𝔽₃`
certificate calculation. -/
theorem sexticPolynomial_F3 :
    XOneThirteenAffineCurve.sexticPolynomial F3 =
      XOneThirteenFiniteField.sextic := by
  rfl

/-- The generic sextic specializes to the polynomial used by the `𝔽₅`
certificate calculation. -/
theorem sexticPolynomial_F5 :
    XOneThirteenAffineCurve.sexticPolynomial F5 =
      XOneThirteenFiniteField.sexticF5 := by
  rfl

/-- The old affine `𝔽₃` certificate is the elementary point type of the
actual affine curve. -/
noncomputable def affineSolutionEquivCurveSolutionF3 :
    XOneThirteenFiniteField.AffineSolution ≃
      XOneThirteenAffineCurve.Solution F3 F3 where
  toFun p := ⟨p.1, by
    simpa [XOneThirteenAffineCurve.sexticPolynomial,
      XOneThirteenFiniteField.sexticValue,
      Polynomial.aeval_def] using p.2⟩
  invFun p := ⟨p.1, by
    simpa [XOneThirteenAffineCurve.sexticPolynomial,
      XOneThirteenFiniteField.sexticValue,
      Polynomial.aeval_def] using p.2⟩
  left_inv p := rfl
  right_inv p := rfl

/-- The old affine `𝔽₅` certificate is the elementary point type of the
actual affine curve. -/
noncomputable def affineSolutionEquivCurveSolutionF5 :
    XOneThirteenFiniteField.AffineSolutionF5 ≃
      XOneThirteenAffineCurve.Solution F5 F5 where
  toFun p := ⟨p.1, by
    simpa [XOneThirteenAffineCurve.sexticPolynomial,
      XOneThirteenFiniteField.sexticValueF5,
      Polynomial.aeval_def] using p.2⟩
  invFun p := ⟨p.1, by
    simpa [XOneThirteenAffineCurve.sexticPolynomial,
      XOneThirteenFiniteField.sexticValueF5,
      Polynomial.aeval_def] using p.2⟩
  left_inv p := rfl
  right_inv p := rfl

/-- The four affine `𝔽₃` certificates are literal `Spec 𝔽₃`-points of the
affine curve scheme. -/
noncomputable def affineSolutionEquivSchemePointF3 :
    XOneThirteenFiniteField.AffineSolution ≃
      XOneThirteenAffineCurve.SchemePoint F3 :=
  affineSolutionEquivCurveSolutionF3.trans
    (XOneThirteenAffineCurve.solutionEquivSchemePoint F3)

/-- The four affine `𝔽₅` certificates are literal `Spec 𝔽₅`-points of the
affine curve scheme. -/
noncomputable def affineSolutionEquivSchemePointF5 :
    XOneThirteenFiniteField.AffineSolutionF5 ≃
      XOneThirteenAffineCurve.SchemePoint F5 :=
  affineSolutionEquivCurveSolutionF5.trans
    (XOneThirteenAffineCurve.solutionEquivSchemePoint F5)

noncomputable instance :
    Fintype (XOneThirteenAffineCurve.SchemePoint F3) :=
  Fintype.ofEquiv XOneThirteenFiniteField.AffineSolution
    affineSolutionEquivSchemePointF3

noncomputable instance :
    Fintype (XOneThirteenAffineCurve.SchemePoint F5) :=
  Fintype.ofEquiv XOneThirteenFiniteField.AffineSolutionF5
    affineSolutionEquivSchemePointF5

/-- The actual affine curve scheme has four `𝔽₃`-points. -/
theorem card_affineSchemePointF3 :
    Fintype.card (XOneThirteenAffineCurve.SchemePoint F3) = 4 := by
  rw [Fintype.card_congr affineSolutionEquivSchemePointF3.symm]
  exact XOneThirteenFiniteField.card_affineSolution

/-- The actual affine curve scheme has four `𝔽₅`-points. -/
theorem card_affineSchemePointF5 :
    Fintype.card (XOneThirteenAffineCurve.SchemePoint F5) = 4 := by
  rw [Fintype.card_congr affineSolutionEquivSchemePointF5.symm]
  exact XOneThirteenFiniteField.card_affineSolutionF5

end Curve

end MazurTorsion.XOneThirteenFiniteFieldCurve

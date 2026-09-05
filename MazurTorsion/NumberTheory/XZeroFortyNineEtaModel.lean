/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/

import MazurTorsion.NumberTheory.XZeroFortyNineSchemeModel

/-!
# The eta-quotient plane model of `X₀(49)`

Kilford--McMurdy, *Slopes of the U7 operator acting on a space of
overconvergent modular forms*, LMS J. Comput. Math. 15 (2012), Section 2,
use the eta quotients

`x = η(τ) / η(49τ)` and `y = (η(7τ) / η(49τ))⁴`

and give the affine relation formalized below.  Their change of coordinates

`z = (y - (7 / 2) x (x² + 5x + 7)) / (x² + 7x + 7)`

satisfies `z² = x (x² + (21 / 4)x + 7)`.  Thus `X = 4x`, `Y = 8z`
lands on the model `Y² = X(X² + 21X + 112)` whose rational points are
classified in `XZeroFortyNineReduction`.

This file checks only that explicit target-side algebra.  In particular, it
does not construct a modular classifying map from a rational cyclic subgroup,
does not assume noncuspidality of such a map, and does not close the order-49
roadmap node.

Primary source:
<https://doi.org/10.1112/S1461157012000095>.
-/

open WeierstrassCurve

namespace MazurTorsion.XZeroFortyNine

/-- The affine eta-quotient equation used for the explicit `X₀(49)` model. -/
def etaPlaneEquation (x y : ℚ) : Prop :=
  y ^ 2 - 7 * x * y * (x ^ 2 + 5 * x + 7) -
      x * (x ^ 6 + 7 * x ^ 5 + 21 * x ^ 4 + 49 * x ^ 3 +
        147 * x ^ 2 + 343 * x + 343) = 0

/-- A rational affine point on the eta-quotient plane model. -/
structure EtaAffinePoint where
  x : ℚ
  y : ℚ
  equation : etaPlaneEquation x y

/-- The affine eta-quotient locus away from the cusp with `x = 0`. -/
def EtaOpenPoint := {P : EtaAffinePoint // P.x ≠ 0}

private lemma etaQuadratic_mod_two :
    ∀ m n : ZMod 2, (m ≠ 0 ∨ n ≠ 0) →
      m ^ 2 + 7 * m * n + 7 * n ^ 2 ≠ 0 := by
  decide

private lemma intCast_mod_two_ne_zero {m : ℤ} (hm : ¬ (2 : ℤ) ∣ m) :
    (m : ZMod 2) ≠ 0 := by
  intro h
  apply hm
  rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h

/-- The denominator in the Kilford--McMurdy coordinate change has no
rational zero. -/
theorem etaModelDenominator_ne_zero (x : ℚ) :
    x ^ 2 + 7 * x + 7 ≠ 0 := by
  intro hq
  let m : ℤ := x.num
  let n : ℤ := (x.den : ℤ)
  have hn0 : (n : ℚ) ≠ 0 := by
    dsimp [n]
    exact_mod_cast x.den_ne_zero
  have hx : x = (m : ℚ) / n := x.num_div_den.symm
  have hmn : IsCoprime m n := by
    simpa [m, n] using Rat.isCoprime_num_den x
  have hclearedQ :
      ((m ^ 2 + 7 * m * n + 7 * n ^ 2 : ℤ) : ℚ) = 0 := by
    rw [hx] at hq
    field_simp at hq
    push_cast
    linear_combination hq
  have hcleared : m ^ 2 + 7 * m * n + 7 * n ^ 2 = 0 := by
    exact_mod_cast hclearedQ
  have hodd : ¬ (2 : ℤ) ∣ m ∨ ¬ (2 : ℤ) ∣ n := by
    by_contra hcon
    push Not at hcon
    have : IsUnit (2 : ℤ) := hmn.isUnit_of_dvd' hcon.1 hcon.2
    norm_num [Int.isUnit_iff] at this
  apply etaQuadratic_mod_two (m : ZMod 2) (n : ZMod 2)
    (hodd.imp intCast_mod_two_ne_zero intCast_mod_two_ne_zero)
  have hmod := congrArg (fun z : ℤ ↦ (z : ZMod 2)) hcleared
  push_cast at hmod
  linear_combination hmod

private def etaZ (P : EtaAffinePoint) : ℚ :=
  (P.y - (7 / 2) * P.x * (P.x ^ 2 + 5 * P.x + 7)) /
    (P.x ^ 2 + 7 * P.x + 7)

private lemma etaZ_sq (P : EtaAffinePoint) :
    etaZ P ^ 2 = P.x * (P.x ^ 2 + (21 / 4) * P.x + 7) := by
  have hden := etaModelDenominator_ne_zero P.x
  have heta := P.equation
  unfold etaPlaneEquation at heta
  unfold etaZ
  rw [div_pow, div_eq_iff (pow_ne_zero 2 hden)]
  linear_combination heta

/-- The ordinate on the checked Weierstrass model obtained from an affine eta
point. -/
def etaWeierstrassOrdinate (P : EtaAffinePoint) : ℚ :=
  8 * ((P.y - (7 / 2) * P.x * (P.x ^ 2 + 5 * P.x + 7)) /
    (P.x ^ 2 + 7 * P.x + 7))

private lemma etaPoint_nonsingular (P : EtaAffinePoint) :
    curve.toAffine.Nonsingular (4 * P.x) (etaWeierstrassOrdinate P) := by
  rw [show etaWeierstrassOrdinate P = 8 * etaZ P by
    rfl]
  apply curve.toAffine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num [curve]
  nlinarith [etaZ_sq P]

/-- The explicit Kilford--McMurdy change of coordinates from the eta plane
to the checked rational `X₀(49)` curve. -/
noncomputable def etaPointToCurve (P : EtaAffinePoint) :
    curve.toAffine.Point :=
  WeierstrassCurve.Affine.Point.some
    (4 * P.x) (etaWeierstrassOrdinate P) (etaPoint_nonsingular P)

/-- An affine eta-model point never maps to the point at infinity. -/
theorem etaPointToCurve_ne_zero (P : EtaAffinePoint) :
    etaPointToCurve P ≠ 0 := by
  exact WeierstrassCurve.Affine.Point.some_ne_zero (etaPoint_nonsingular P)

/-- If the eta quotient `x` is nonzero, its image is not the finite rational
cusp `T = (0, 0)`. -/
theorem etaPointToCurve_ne_T (P : EtaAffinePoint) (hx : P.x ≠ 0) :
    etaPointToCurve P ≠ T := by
  intro h
  rw [etaPointToCurve, T] at h
  have hxcoord :=
    (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mp h |>.1
  apply hx
  linarith

/-- The open eta locus maps away from both rational cusps on the checked
`X₀(49)` model. -/
theorem etaPointToCurve_ne_cusps (P : EtaOpenPoint) :
    etaPointToCurve P.1 ≠ 0 ∧ etaPointToCurve P.1 ≠ T :=
  ⟨etaPointToCurve_ne_zero P.1, etaPointToCurve_ne_T P.1 P.2⟩

/-- The eta-model coordinate change as an actual rational point of the
represented projective cubic. -/
noncomputable def etaPointToScheme (P : EtaAffinePoint) :
    _root_.AlgebraicGeometry.Spec (.of ℚ) ⟶ SchemeModel.scheme :=
  SchemeModel.rationalPointEquiv (etaPointToCurve P)

/-- The open eta locus maps away from both rational cusp morphisms of the
represented projective cubic. -/
theorem etaPointToScheme_ne_cusps (P : EtaOpenPoint) :
    etaPointToScheme P.1 ≠ SchemeModel.infinityCusp ∧
      etaPointToScheme P.1 ≠ SchemeModel.finiteCusp := by
  constructor
  · intro h
    exact (etaPointToCurve_ne_cusps P).1
      (SchemeModel.rationalPointEquiv.injective h)
  · intro h
    exact (etaPointToCurve_ne_cusps P).2
      (SchemeModel.rationalPointEquiv.injective h)

/-- There is no rational point on the open eta-quotient locus.  This is a
target-side consumer of the checked two-cusp classification, not a modular
classifying-map construction. -/
theorem etaOpenPoint_isEmpty : IsEmpty EtaOpenPoint := by
  constructor
  intro P
  rcases SchemeModel.point_eq_infinityCusp_or_finiteCusp
      (etaPointToScheme P.1) with hzero | hT
  · exact (etaPointToScheme_ne_cusps P).1 hzero
  · exact (etaPointToScheme_ne_cusps P).2 hT

end MazurTorsion.XZeroFortyNine

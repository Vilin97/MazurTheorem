/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.OrderThirtyFiveRankBoundary
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# The rational three-cover attached to the order-35 dual candidate

For the normalized source curve

`y² + 4xy + 7y = x³`,

the fixed three-descent function is the source ordinate `y`.  Pulling this
function back along the checked dual candidate gives the literal cube

`((Y - 28) / (3X + 16))³`.

Conversely, if a nonzero source ordinate is a rational cube `t³`, writing
`x = tu` produces the plane cubic

`u³ = t³ + 4tu + 7`.

This cubic has an explicit map to the candidate target, and the dual
candidate sends the resulting point back to `(x,y)`.  Thus this file proves
the affine, nonexceptional part of the key descent equivalence

`y(P) is a cube ⇔ P lies in the image of the dual candidate`.

The exceptional points with `y = 0` encode the two nontrivial visible cosets
and are deliberately not folded into a multiplicative quotient by an ad hoc
zero convention.
-/

open WeierstrassCurve
open scoped WeierstrassCurve.Affine
open Polynomial

namespace MazurTorsion.OrderThirtyFive

open WeierstrassCurve.Affine

/-- Pullback of the source ordinate along the dual candidate is a literal
rational cube. -/
theorem veluThreeDualCandidateY_eq_cube
    {X Y : ℚ}
    (hP : veluThreeCandidateTarget.toAffine.Nonsingular X Y) :
    veluThreeDualCandidateY X Y =
      ((Y - 28) / veluThreeDualCandidateKernel X) ^ 3 := by
  let K : ℚ := 3 * X + 16
  let A : ℚ := X ^ 3 - 252 * X - 1771
  let B : ℚ := X ^ 3 + 16 * X ^ 2 + 252 * X + 2198
  let Z : ℚ := 2 * Y + 4 * X + 7
  have hkernel := veluThreeDualCandidateKernel_ne_zero hP
  have hK : K ≠ 0 := by
    simpa only [K, veluThreeDualCandidateKernel] using hkernel
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  norm_num [veluThreeCandidateTarget] at hcurve
  change ((Z * (B / K ^ 3) - 4 * (A / K ^ 2) - 7) / 2) =
    ((Y - 28) / K) ^ 3
  field_simp [hK]
  dsimp only [A, B, K, Z]
  linear_combination 2 * (4 * X - Y + 91) * hcurve

/-- The abscissa on the rational three-cover. -/
def threeCoverTargetX (t u : ℚ) : ℚ :=
  3 * t ^ 2 + 3 * t * u - 4 * t + 3 * u ^ 2 + 4 * u

/-- The ordinate on the rational three-cover. -/
def threeCoverTargetY (t u : ℚ) : ℚ :=
  28 + t * (3 * threeCoverTargetX t u + 16)

/-- The covering cubic maps to the candidate target equation. -/
theorem threeCoverTarget_equation
    {t u : ℚ}
    (hcover : u ^ 3 = t ^ 3 + 4 * t * u + 7) :
    veluThreeCandidateTarget.toAffine.Equation
      (threeCoverTargetX t u) (threeCoverTargetY t u) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num [veluThreeCandidateTarget]
  dsimp only [threeCoverTargetX, threeCoverTargetY]
  linear_combination
    -(54 * t ^ 3 + 81 * t ^ 2 * u + 81 * t * u ^ 2 +
      108 * t * u + 27 * u ^ 3 + 108 * u ^ 2 + 144 * u + 253) *
        hcover

/-- The rational point on the candidate target supplied by the covering
cubic. -/
noncomputable def threeCoverTargetPoint
    {t u : ℚ}
    (hcover : u ^ 3 = t ^ 3 + 4 * t * u + 7) :
    veluThreeCandidateTarget.toAffine.Point :=
  .some (threeCoverTargetX t u) (threeCoverTargetY t u)
    (veluThreeCandidateTarget.toAffine.equation_iff_nonsingular.mp
      (threeCoverTarget_equation hcover))

/-- The dual abscissa of a covering point is `tu`. -/
theorem veluThreeDualCandidateX_threeCoverTargetX
    {t u : ℚ}
    (hcover : u ^ 3 = t ^ 3 + 4 * t * u + 7) :
    veluThreeDualCandidateX (threeCoverTargetX t u) = t * u := by
  let X : ℚ := threeCoverTargetX t u
  let K : ℚ := 3 * X + 16
  let A : ℚ := X ^ 3 - 252 * X - 1771
  let htarget : veluThreeCandidateTarget.toAffine.Nonsingular
      (threeCoverTargetX t u) (threeCoverTargetY t u) :=
    veluThreeCandidateTarget.toAffine.equation_iff_nonsingular.mp
      (threeCoverTarget_equation hcover)
  have hkernel := veluThreeDualCandidateKernel_ne_zero htarget
  have hK : K ≠ 0 := by
    simpa only [K, X, veluThreeDualCandidateKernel] using hkernel
  change A / K ^ 2 = t * u
  field_simp [hK]
  dsimp only [A, K, X, threeCoverTargetX] at hcover ⊢
  linear_combination
    -(27 * t ^ 3 - 108 * t ^ 2 + 144 * t - 27 * u ^ 3 -
      108 * u ^ 2 - 144 * u - 253) * hcover

/-- The dual ordinate of a covering point is `t³`. -/
theorem veluThreeDualCandidateY_threeCoverTarget
    {t u : ℚ}
    (hcover : u ^ 3 = t ^ 3 + 4 * t * u + 7) :
    veluThreeDualCandidateY
        (threeCoverTargetX t u) (threeCoverTargetY t u) = t ^ 3 := by
  let htarget : veluThreeCandidateTarget.toAffine.Nonsingular
      (threeCoverTargetX t u) (threeCoverTargetY t u) :=
    veluThreeCandidateTarget.toAffine.equation_iff_nonsingular.mp
      (threeCoverTarget_equation hcover)
  rw [veluThreeDualCandidateY_eq_cube htarget]
  have hkernel := veluThreeDualCandidateKernel_ne_zero htarget
  have hkernel' :
      3 * threeCoverTargetX t u + 16 ≠ 0 := by
    simpa only [veluThreeDualCandidateKernel] using hkernel
  have ht :
      (threeCoverTargetY t u - 28) /
          veluThreeDualCandidateKernel (threeCoverTargetX t u) = t := by
    simp only [threeCoverTargetY, veluThreeDualCandidateKernel]
    field_simp [hkernel']
    ring
  rw [ht]

/-- A nonzero cube source ordinate gives an explicit rational preimage under
the dual candidate. -/
theorem exists_dualCandidate_preimage_of_Y_eq_cube
    {x y t : ℚ}
    (hP : threeTorsionCurve.toAffine.Nonsingular x y)
    (ht : t ≠ 0)
    (hy : y = t ^ 3) :
    ∃ Q : veluThreeCandidateTarget.toAffine.Point,
      veluThreeDualCandidatePointFun Q =
        WeierstrassCurve.Affine.Point.some x y hP := by
  let u : ℚ := x / t
  have hxu : x = t * u := by
    dsimp only [u]
    field_simp [ht]
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  norm_num [threeTorsionCurve] at hcurve
  have hfactor :
      t ^ 3 * (t ^ 3 + 4 * t * u + 7) = t ^ 3 * u ^ 3 := by
    calc
      t ^ 3 * (t ^ 3 + 4 * t * u + 7) =
          y ^ 2 + 4 * x * y + 7 * y := by rw [hy, hxu]; ring
      _ = x ^ 3 := hcurve
      _ = t ^ 3 * u ^ 3 := by rw [hxu]; ring
  have hcover : u ^ 3 = t ^ 3 + 4 * t * u + 7 := by
    exact (mul_left_cancel₀ (pow_ne_zero 3 ht) hfactor).symm
  refine ⟨threeCoverTargetPoint hcover, ?_⟩
  simp only [threeCoverTargetPoint, veluThreeDualCandidatePointFun,
    veluThreeDualCandidatePoint,
    WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · rw [veluThreeDualCandidateX_threeCoverTargetX hcover]
    exact hxu.symm
  · rw [veluThreeDualCandidateY_threeCoverTarget hcover]
    exact hy.symm

/-! ## Translation by the visible kernel -/

/-- Translating by `(0,0)` multiplies the source descent class by `49`:
the new ordinate is `-49y/x³`. -/
theorem addY_threeTorsionOrigin
    {x y : ℚ}
    (hP : threeTorsionCurve.toAffine.Nonsingular x y)
    (hx : x ≠ 0) :
    threeTorsionCurve.toAffine.addY x 0 y
        (threeTorsionCurve.toAffine.slope x 0 y 0) =
      -49 * y / x ^ 3 := by
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  norm_num [threeTorsionCurve] at hcurve
  rw [threeTorsionCurve.toAffine.slope_of_X_ne hx]
  simp only [WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.negY, threeTorsionCurve]
  field_simp [hx]
  linear_combination -x ^ 3 * (4 * x + y - 7) * hcurve

/-- Translating by `(0,-7) = -(0,0)` gives the symmetric raw ordinate
formula. -/
theorem addY_neg_threeTorsionOrigin
    {x y : ℚ}
    (hP : threeTorsionCurve.toAffine.Nonsingular x y)
    (hx : x ≠ 0) :
    threeTorsionCurve.toAffine.addY x 0 y
        (threeTorsionCurve.toAffine.slope x 0 y (-7)) =
      -7 * (y + 4 * x + 7) ^ 2 / x ^ 3 := by
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  norm_num [threeTorsionCurve] at hcurve
  rw [threeTorsionCurve.toAffine.slope_of_X_ne hx]
  simp only [WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.negY, threeTorsionCurve]
  field_simp [hx]
  linear_combination -x ^ 3 * (4 * x + y + 7) * hcurve

/-- Away from the exceptional ordinate zero, translation by `(0,-7)`
multiplies the descent class by `7`, up to the displayed rational cube. -/
theorem addY_neg_threeTorsionOrigin_cubeClass
    {x y : ℚ}
    (hP : threeTorsionCurve.toAffine.Nonsingular x y)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    threeTorsionCurve.toAffine.addY x 0 y
        (threeTorsionCurve.toAffine.slope x 0 y (-7)) =
      -7 * y * (x / y) ^ 3 := by
  rw [addY_neg_threeTorsionOrigin hP hx]
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  norm_num [threeTorsionCurve] at hcurve
  field_simp [hx, hy]
  linear_combination
    -(x ^ 3 + 4 * x * y + y ^ 2 + 7 * y) * hcurve

/-! ## Exact arithmetic inputs and assembly of the three cosets -/

/-- A nonzero factor of a cube whose gcd with the cofactor divides `7` has
one of the three cube classes supported at `7`. -/
private theorem cubeclass_of_gcd_dvd_seven
    {A B C : ℤ}
    (hA : A ≠ 0) (hprod : A * B = C ^ 3)
    (hgcd : GCDMonoid.gcd A B ∣ (7 : ℤ)) :
    ∃ d : ℤ, A = d ^ 3 ∨ A = 7 * d ^ 3 ∨ A = 49 * d ^ 3 := by
  let g : ℤ := GCDMonoid.gcd A B
  have hgA : g ∣ A := GCDMonoid.gcd_dvd_left A B
  have hgB : g ∣ B := GCDMonoid.gcd_dvd_right A B
  have hg0 : g ≠ 0 := by
    intro hz
    rw [hz] at hgA
    exact hA (zero_dvd_iff.mp hgA)
  have hgpos : 0 < g :=
    lt_of_le_of_ne (Int.gcd_nonneg A B) (Ne.symm hg0)
  have hdivNat : g.natAbs ∣ 7 := by
    simpa using Int.natAbs_dvd_natAbs.mpr hgcd
  have hgleNat : g.natAbs ≤ 7 := Nat.le_of_dvd (by norm_num) hdivNat
  have hgle : g ≤ 7 := by
    have : (g.natAbs : ℤ) ≤ 7 := by exact_mod_cast hgleNat
    simpa [Int.natCast_natAbs, abs_of_pos hgpos] using this
  have hgval : g = 1 ∨ g = 7 := by
    interval_cases g <;> norm_num at hdivNat
    all_goals simp
  rcases hgval with hg | hg
  · have hab : IsCoprime A B := by
      apply (gcd_isUnit_iff A B).mp
      rw [← show g = GCDMonoid.gcd A B from rfl, hg]
      exact isUnit_one
    obtain ⟨d, hd⟩ :=
      Int.eq_pow_of_mul_eq_pow_odd_left (k := 3) hab (by norm_num) hprod
    exact ⟨d, Or.inl hd⟩
  · have hsevenA : (7 : ℤ) ∣ A := by simpa [hg] using hgA
    have hsevenB : (7 : ℤ) ∣ B := by simpa [hg] using hgB
    have hsevenC : (7 : ℤ) ∣ C := by
      have hsevenC3 : (7 : ℤ) ∣ C ^ 3 := by
        rw [← hprod]
        exact dvd_mul_of_dvd_left hsevenA B
      have hprime7 : Prime (7 : ℤ) :=
        Int.prime_iff_natAbs_prime.mpr (by norm_num)
      exact hprime7.dvd_of_dvd_pow hsevenC3
    let a : ℤ := A / 7
    let b : ℤ := B / 7
    let c : ℤ := C / 7
    have hga : 7 * a = A := by
      exact EuclideanDomain.mul_div_cancel' (by norm_num) hsevenA
    have hgb : 7 * b = B := by
      exact EuclideanDomain.mul_div_cancel' (by norm_num) hsevenB
    have hgc : 7 * c = C := by
      exact EuclideanDomain.mul_div_cancel' (by norm_num) hsevenC
    have hab : a * b = 7 * c ^ 3 := by
      apply mul_left_cancel₀ (show (49 : ℤ) ≠ 0 by norm_num)
      calc
        49 * (a * b) = A * B := by rw [← hga, ← hgb]; ring
        _ = C ^ 3 := hprod
        _ = 49 * (7 * c ^ 3) := by rw [← hgc]; ring
    have habcop : IsCoprime a b := by
      simpa [g, hg] using
        (isCoprime_div_gcd_div_gcd_of_gcd_ne_zero hg0 :
          IsCoprime (A / g) (B / g))
    have hsevenab : (7 : ℤ) ∣ a * b := by
      rw [hab]
      exact dvd_mul_right 7 (c ^ 3)
    have hprime7 : Prime (7 : ℤ) :=
      Int.prime_iff_natAbs_prime.mpr (by norm_num)
    rcases hprime7.dvd_mul.mp hsevenab with hsevena | hsevenb
    · obtain ⟨a', ha'⟩ := hsevena
      have ha'div : a' ∣ a := ⟨7, by rw [ha']; ring⟩
      have ha'bcube : a' * b = c ^ 3 := by
        apply mul_left_cancel₀ (show (7 : ℤ) ≠ 0 by norm_num)
        calc
          7 * (a' * b) = a * b := by rw [ha']; ring
          _ = 7 * c ^ 3 := hab
      have ha'b : IsCoprime a' b :=
        habcop.of_isCoprime_of_dvd_left ha'div
      obtain ⟨d, hd⟩ :=
        Int.eq_pow_of_mul_eq_pow_odd_left (k := 3) ha'b (by norm_num) ha'bcube
      refine ⟨d, Or.inr (Or.inr ?_)⟩
      rw [← hga, ha', hd]
      ring
    · obtain ⟨b', hb'⟩ := hsevenb
      have hb'div : b' ∣ b := ⟨7, by rw [hb']; ring⟩
      have hab'cube : a * b' = c ^ 3 := by
        apply mul_left_cancel₀ (show (7 : ℤ) ≠ 0 by norm_num)
        calc
          7 * (a * b') = a * b := by rw [hb']; ring
          _ = 7 * c ^ 3 := hab
      have hab' : IsCoprime a b' :=
        habcop.of_isCoprime_of_dvd_right hb'div
      obtain ⟨d, hd⟩ :=
        Int.eq_pow_of_mul_eq_pow_odd_left (k := 3) hab' (by norm_num) hab'cube
      refine ⟨d, Or.inr (Or.inl ?_)⟩
      rw [← hga, hd]

/-- Scaling the abscissa by the reduced denominator of the ordinate gives
an integer.  This is the integral-root step behind the weighted integral
coordinates used in the source descent. -/
private theorem integral_scaled_abscissa
    {x y : ℚ}
    (hP : threeTorsionCurve.toAffine.Nonsingular x y) :
    ∃ U : ℤ, (y.den : ℚ) * x = U := by
  let r : ℤ := y.num
  let s : ℤ := y.den
  let u : ℚ := (s : ℚ) * x
  let p : ℤ[X] :=
    Polynomial.X ^ 3 -
      (Polynomial.C (4 * r * s) * Polynomial.X +
        Polynomial.C (r ^ 2 * s + 7 * r * s ^ 2))
  have hs : (s : ℚ) ≠ 0 := by
    dsimp [s]
    exact_mod_cast y.den_ne_zero
  have hy : y = (r : ℚ) / (s : ℚ) := by
    simpa [r, s] using y.num_div_den.symm
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  norm_num [threeTorsionCurve] at hcurve
  have hu :
      u ^ 3 - (4 * r * s : ℤ) * u -
          (r ^ 2 * s + 7 * r * s ^ 2 : ℤ) = 0 := by
    rw [hy] at hcurve
    dsimp only [u]
    push_cast
    field_simp [hs] at hcurve
    linear_combination -(s : ℚ) * hcurve
  have hp : p.Monic := by
    dsimp only [p]
    apply Polynomial.monic_X_pow_sub
    compute_degree
    norm_num
  have hroot : Polynomial.aeval u p = 0 := by
    dsimp only [p]
    simp only [map_sub, map_add, map_mul, Polynomial.aeval_X,
      Polynomial.aeval_C, map_pow]
    norm_num at hu ⊢
    linear_combination hu
  obtain ⟨U, hU, -⟩ := exists_integer_of_is_root_of_monic hp hroot
  exact ⟨U, by simpa [u, s] using hU⟩

/-- In the reduced integral source equation, any common divisor of the two
descent factors divides `7`.  The exponent-one assertion at `7` is the only
non-radical part of the calculation. -/
private theorem common_divisor_source_dvd_seven
    {r s U T d : ℤ}
    (hrs : IsCoprime r s)
    (hT : T = r + 4 * U + 7 * s)
    (hcurve : r * s * T = U ^ 3)
    (hdr : d ∣ r) (hdT : d ∣ T) :
    d ∣ (7 : ℤ) := by
  have hds : IsCoprime d s :=
    hrs.of_isCoprime_of_dvd_left hdr
  have hdU3 : d ∣ U ^ 3 := by
    rw [← hcurve]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hdr s) T
  have hdlin : d ∣ 4 * U + 7 * s := by
    have hsub : d ∣ T - r := hdT.sub hdr
    convert hsub using 1
    rw [hT]
    ring
  have hd343s3 : d ∣ 343 * s ^ 3 := by
    have hid :
        (4 * U + 7 * s) *
            (16 * U ^ 2 - 28 * U * s + 49 * s ^ 2) =
          64 * U ^ 3 + 343 * s ^ 3 := by ring
    have hdsum : d ∣ 64 * U ^ 3 + 343 * s ^ 3 := by
      rw [← hid]
      exact dvd_mul_of_dvd_left hdlin _
    obtain ⟨a, ha⟩ := hdsum
    obtain ⟨b, hb⟩ : d ∣ 64 * U ^ 3 := by
      simpa [mul_comm] using dvd_mul_of_dvd_right hdU3 64
    refine ⟨a - b, ?_⟩
    linear_combination ha - hb
  have hd343 : d ∣ (343 : ℤ) :=
    hds.pow_right.dvd_of_dvd_mul_right hd343s3
  by_cases hd0 : d = 0
  · subst d
    norm_num at hd343
  have hdabs : d.natAbs ∣ 343 := by
    simpa using Int.natAbs_dvd_natAbs.mpr hd343
  have hdabs' : d.natAbs ∣ 7 ^ 3 := by
    norm_num at hdabs ⊢
    exact hdabs
  obtain ⟨k, hk, hkval⟩ :=
    (Nat.dvd_prime_pow Nat.prime_seven).mp hdabs'
  have hnot49 : ¬ (49 : ℤ) ∣ d := by
    intro h49d
    have h49r : (49 : ℤ) ∣ r := h49d.trans hdr
    have h49T : (49 : ℤ) ∣ T := h49d.trans hdT
    have h2401U3 : (2401 : ℤ) ∣ U ^ 3 := by
      obtain ⟨r', hr'⟩ := h49r
      obtain ⟨T', hT'⟩ := h49T
      refine ⟨r' * s * T', ?_⟩
      rw [← hcurve, hr', hT']
      ring
    have h7U : (7 : ℤ) ∣ U := by
      apply Int.Prime.dvd_pow' Nat.prime_seven
      exact (show (7 : ℤ) ∣ 2401 by norm_num).trans h2401U3
    obtain ⟨u, hu⟩ := h7U
    obtain ⟨q, hq⟩ := h2401U3
    have huCube : u ^ 3 = 7 * q := by
      apply mul_left_cancel₀ (show (343 : ℤ) ≠ 0 by norm_num)
      calc
        343 * u ^ 3 = U ^ 3 := by rw [hu]; ring
        _ = 2401 * q := hq
        _ = 343 * (7 * q) := by ring
    have h7u : (7 : ℤ) ∣ u := by
      apply Int.Prime.dvd_pow' Nat.prime_seven
      exact ⟨q, huCube⟩
    obtain ⟨u', hu'⟩ := h7u
    have h49U : (49 : ℤ) ∣ U := by
      refine ⟨u', ?_⟩
      rw [hu, hu']
      ring
    have h49lin : (49 : ℤ) ∣ 4 * U + 7 * s := by
      have hsub : (49 : ℤ) ∣ T - r := h49T.sub h49r
      convert hsub using 1
      rw [hT]
      ring
    have h49sevenS : (49 : ℤ) ∣ 7 * s := by
      obtain ⟨a, ha⟩ := h49lin
      obtain ⟨b, hb⟩ : (49 : ℤ) ∣ 4 * U := by
        simpa [mul_comm] using dvd_mul_of_dvd_right h49U 4
      refine ⟨a - b, ?_⟩
      linear_combination ha - hb
    obtain ⟨q, hq⟩ := h49sevenS
    have h7s : (7 : ℤ) ∣ s := by
      refine ⟨q, ?_⟩
      apply mul_left_cancel₀ (show (7 : ℤ) ≠ 0 by norm_num)
      calc
        7 * s = 49 * q := hq
        _ = 7 * (7 * q) := by ring
    have h7r : (7 : ℤ) ∣ r :=
      (show (7 : ℤ) ∣ 49 by norm_num).trans h49r
    have hunit : IsUnit (7 : ℤ) :=
      hrs.isUnit_of_dvd' h7r h7s
    rcases Int.isUnit_iff.mp hunit with h | h <;> norm_num at h
  have hklt : k < 2 := by
    by_contra hknot
    have hk2 : 2 ≤ k := by omega
    have h49abs : 49 ∣ d.natAbs := by
      rw [hkval]
      simpa using (pow_dvd_pow (7 : ℕ) hk2)
    apply hnot49
    have h49cast : (49 : ℤ) ∣ (d.natAbs : ℤ) := by
      exact_mod_cast h49abs
    simpa [Int.natCast_natAbs] using h49cast
  have hkcases : k = 0 ∨ k = 1 := by omega
  rcases hkcases with rfl | rfl
  · have hdabs1 : d.natAbs = 1 := by simpa using hkval
    have hdunit : IsUnit d := by
      exact Int.isUnit_iff.mpr (Int.natAbs_eq_iff.mp hdabs1)
    exact hdunit.dvd
  · have hdseven : d.natAbs = 7 := by simpa using hkval
    have hdval : d = 7 ∨ d = -7 := by
      simpa using (Int.natAbs_eq_iff.mp hdseven)
    rcases hdval with rfl | rfl
    · exact dvd_rfl
    · norm_num

/-- The second reduced source factor is coprime to the denominator. -/
private theorem source_factor_coprime_denominator
    {r s U T : ℤ}
    (hrs : IsCoprime r s) (hs0 : s ≠ 0)
    (hT : T = r + 4 * U + 7 * s)
    (hcurve : r * s * T = U ^ 3) :
    IsCoprime T s := by
  apply isCoprime_of_prime_dvd
  · exact fun h ↦ hs0 h.2
  · intro p hp hpT hps
    have hpU3 : p ∣ U ^ 3 := by
      rw [← hcurve]
      exact dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_right hps r) T
    have hpU : p ∣ U := hp.dvd_of_dvd_pow hpU3
    have hp4U : p ∣ 4 * U := by
      simpa [mul_comm] using dvd_mul_of_dvd_right hpU 4
    have hp7s : p ∣ 7 * s :=
      dvd_mul_of_dvd_right hps 7
    have hpr : p ∣ r := by
      obtain ⟨a, ha⟩ := hpT
      obtain ⟨b, hb⟩ := hp4U
      obtain ⟨c, hc⟩ := hp7s
      refine ⟨a - b - c, ?_⟩
      calc
        r = T - 4 * U - 7 * s := by rw [hT]; ring
        _ = p * (a - b - c) := by rw [ha, hb, hc]; ring
    exact hp.not_unit (hrs.isUnit_of_dvd' hpr hps)

/-- The source equation in the reduced integral coordinates
`r = num(y)`, `s = den(y)`, and `U = sx`. -/
private theorem scaled_source_equation
    {x y : ℚ}
    (hP : threeTorsionCurve.toAffine.Nonsingular x y)
    {U : ℤ} (hU : (y.den : ℚ) * x = U) :
    y.num * (y.den : ℤ) *
        (y.num + 4 * U + 7 * (y.den : ℤ)) = U ^ 3 := by
  let r : ℤ := y.num
  let s : ℤ := y.den
  have hs : (s : ℚ) ≠ 0 := by
    dsimp [s]
    exact_mod_cast y.den_ne_zero
  have hy : y = (r : ℚ) / (s : ℚ) := by
    simpa [r, s] using y.num_div_den.symm
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  norm_num [threeTorsionCurve] at hcurve
  have hQ :
      ((r * s * (r + 4 * U + 7 * s) : ℤ) : ℚ) =
        ((U ^ 3 : ℤ) : ℚ) := by
    rw [hy] at hcurve
    have hU' : (s : ℚ) * x = (U : ℚ) := by
      simpa [s] using hU
    push_cast
    field_simp [hs] at hcurve
    rw [← hU']
    linear_combination (s : ℚ) * hcurve
  exact_mod_cast hQ

/-- The source local calculation needed from the fixed three-descent: every
nonexceptional ordinate has one of the three supported cube classes
`1`, `7`, or `49`. -/
def SourceThreeCubeClassBound : Prop :=
  ∀ {x y : ℚ},
    threeTorsionCurve.toAffine.Nonsingular x y → x ≠ 0 →
      ∃ t : ℚ, t ≠ 0 ∧
        (y = t ^ 3 ∨ y = 7 * t ^ 3 ∨ y = 49 * t ^ 3)

/-- The fixed source local calculation: the ordinate of every
nonexceptional rational point has cube class `1`, `7`, or `49`.

The proof uses reduced numerator-denominator coordinates for the ordinate.
The integral-root theorem first shows that `den(y) * x` is integral.  The
resulting two integral descent factors are coprime away from `7`, while a
short exponent calculation rules out a common factor `49`. -/
theorem sourceThreeCubeClassBound : SourceThreeCubeClassBound := by
  intro x y hP hx
  have hy0 : y ≠ 0 := by
    intro hy
    have hcurve := hP.1
    rw [WeierstrassCurve.Affine.equation_iff] at hcurve
    norm_num [threeTorsionCurve, hy] at hcurve
    exact hx (eq_zero_of_pow_eq_zero hcurve.symm)
  obtain ⟨U, hU⟩ := integral_scaled_abscissa hP
  let r : ℤ := y.num
  let s : ℤ := y.den
  let T : ℤ := r + 4 * U + 7 * s
  have hr0 : r ≠ 0 := by
    dsimp only [r]
    exact Rat.num_ne_zero.mpr hy0
  have hs0 : s ≠ 0 := by
    dsimp only [s]
    exact_mod_cast y.den_ne_zero
  have hrs : IsCoprime r s := by
    simpa [r, s] using Rat.isCoprime_num_den y
  have hT : T = r + 4 * U + 7 * s := rfl
  have hcurve : r * s * T = U ^ 3 := by
    simpa [r, s, T] using scaled_source_equation hP hU
  have hTs : IsCoprime T s :=
    source_factor_coprime_denominator hrs hs0 hT hcurve
  have hRTs : IsCoprime (r * T) s := hrs.mul_left hTs
  have hprod : (r * T) * s = U ^ 3 := by
    calc
      (r * T) * s = r * s * T := by ring
      _ = U ^ 3 := hcurve
  obtain ⟨e, he⟩ := Int.eq_pow_of_mul_eq_pow_odd_left (k := 3) hRTs.symm
    (by norm_num) (by simpa [mul_comm] using hprod)
  obtain ⟨w, hw⟩ :=
    Int.eq_pow_of_mul_eq_pow_odd_left (k := 3) hRTs (by norm_num) hprod
  have hgcd : GCDMonoid.gcd r T ∣ (7 : ℤ) :=
    common_divisor_source_dvd_seven hrs hT hcurve
      (GCDMonoid.gcd_dvd_left r T)
      (GCDMonoid.gcd_dvd_right r T)
  have he0 : e ≠ 0 := by
    intro hezero
    rw [hezero] at he
    norm_num at he
    exact hs0 he
  have hy : y = (r : ℚ) / (s : ℚ) := by
    simpa [r, s] using y.num_div_den.symm
  obtain ⟨d, hd | hd | hd⟩ :=
    cubeclass_of_gcd_dvd_seven hr0 hw hgcd
  · have hd0 : d ≠ 0 := by
      intro hdzero
      rw [hdzero] at hd
      norm_num at hd
      exact hr0 hd
    refine ⟨(d : ℚ) / (e : ℚ), div_ne_zero (by exact_mod_cast hd0)
      (by exact_mod_cast he0), Or.inl ?_⟩
    rw [hy, hd, he]
    push_cast
    field_simp [he0]
  · have hd0 : d ≠ 0 := by
      intro hdzero
      rw [hdzero] at hd
      norm_num at hd
      exact hr0 hd
    refine ⟨(d : ℚ) / (e : ℚ), div_ne_zero (by exact_mod_cast hd0)
      (by exact_mod_cast he0), Or.inr (Or.inl ?_)⟩
    rw [hy, hd, he]
    push_cast
    field_simp [he0]
  · have hd0 : d ≠ 0 := by
      intro hdzero
      rw [hdzero] at hd
      norm_num at hd
      exact hr0 hd
    refine ⟨(d : ℚ) / (e : ℚ), div_ne_zero (by exact_mod_cast hd0)
      (by exact_mod_cast he0), Or.inr (Or.inr ?_)⟩
    rw [hy, hd, he]
    push_cast
    field_simp [he0]

/-- The target local calculation needed from the fixed three-descent: every
rational target point is in the image of the first candidate point
function.  No additivity is included in this proposition. -/
def TargetThreeCandidateSurjective : Prop :=
  Function.Surjective veluThreeCandidatePointFun

/-- Under target surjectivity, a nonzero cube source ordinate makes the
source point an actual triple. -/
theorem exists_eq_three_nsmul_of_Y_eq_cube
    (htarget : TargetThreeCandidateSurjective)
    {x y t : ℚ}
    (hP : threeTorsionCurve.toAffine.Nonsingular x y)
    (ht : t ≠ 0) (hy : y = t ^ 3) :
    ∃ R : threeTorsionCurve.toAffine.Point,
      WeierstrassCurve.Affine.Point.some x y hP = (3 : ℕ) • R := by
  obtain ⟨Q, hQ⟩ := exists_dualCandidate_preimage_of_Y_eq_cube hP ht hy
  obtain ⟨R, hR⟩ := htarget Q
  refine ⟨R, ?_⟩
  calc
    WeierstrassCurve.Affine.Point.some x y hP =
        veluThreeDualCandidatePointFun Q := hQ.symm
    _ = veluThreeDualCandidatePointFun
          (veluThreeCandidatePointFun R) := by rw [hR]
    _ = (3 : ℕ) • R :=
      veluThreeDualCandidatePointFun_candidate R

private theorem two_nsmul_threeTorsionOrigin_eq_neg :
    (2 : ℕ) • threeTorsionOrigin = -threeTorsionOrigin := by
  have hthree : (3 : ℕ) • threeTorsionOrigin = 0 := by
    rw [← addOrderOf_threeTorsionOrigin]
    exact addOrderOf_nsmul_eq_zero threeTorsionOrigin
  calc
    (2 : ℕ) • threeTorsionOrigin =
        (3 : ℕ) • threeTorsionOrigin - threeTorsionOrigin := by abel
    _ = -threeTorsionOrigin := by rw [hthree]; simp

/-- The two fixed arithmetic outputs assemble to the exact three-coset
certificate consumed by the rank-zero boundary. -/
theorem threeCosetBound_of_descent_inputs
    (hsource : SourceThreeCubeClassBound)
    (htarget : TargetThreeCandidateSurjective) :
    ThreeCosetBound := by
  intro P
  cases P with
  | zero =>
      refine ⟨⟨0, by norm_num⟩, 0, ?_⟩
      simp [normalizedThreeRepresentative]
      rfl
  | some x y hP =>
      by_cases hx : x = 0
      · have hcandidate :
            veluThreeCandidatePointFun
              (WeierstrassCurve.Affine.Point.some x y hP) = 0 := by
          simp [veluThreeCandidatePointFun, hx]
          rfl
        rcases
            (veluThreeCandidatePointFun_eq_zero_iff
              (WeierstrassCurve.Affine.Point.some x y hP)).mp hcandidate with
          hzero | horigin | hnegOrigin
        · exact (WeierstrassCurve.Affine.Point.some_ne_zero hP hzero).elim
        · refine ⟨⟨1, by norm_num⟩, 0, ?_⟩
          simpa [normalizedThreeRepresentative] using horigin
        · refine ⟨⟨2, by norm_num⟩, 0, ?_⟩
          rw [hnegOrigin, normalizedThreeRepresentative]
          norm_num
          exact two_nsmul_threeTorsionOrigin_eq_neg.symm
      · obtain ⟨t, ht, hy | hy | hy⟩ := hsource hP hx
        · obtain ⟨R, hR⟩ :=
            exists_eq_three_nsmul_of_Y_eq_cube htarget hP ht hy
          refine ⟨⟨0, by norm_num⟩, R, ?_⟩
          simpa [normalizedThreeRepresentative] using hR
        · have hT : threeTorsionCurve.toAffine.Nonsingular 0 0 := by
            apply threeTorsionCurve.toAffine.equation_iff_nonsingular.mp
            norm_num [WeierstrassCurve.Affine.equation_iff,
              threeTorsionCurve]
          let x' : ℚ := threeTorsionCurve.toAffine.addX x 0
            (threeTorsionCurve.toAffine.slope x 0 y 0)
          let y' : ℚ := threeTorsionCurve.toAffine.addY x 0 y
            (threeTorsionCurve.toAffine.slope x 0 y 0)
          have hP' : threeTorsionCurve.toAffine.Nonsingular x' y' :=
            nonsingular_add hP hT (fun hxy => hx hxy.1)
          let t' : ℚ := -7 * t / x
          have ht' : t' ≠ 0 := by
            dsimp only [t']
            exact div_ne_zero (mul_ne_zero (by norm_num) ht) hx
          have hy' : y' = t' ^ 3 := by
            dsimp only [y', t']
            rw [addY_threeTorsionOrigin hP hx, hy]
            field_simp [hx]
            ring
          obtain ⟨R, hR⟩ :=
            exists_eq_three_nsmul_of_Y_eq_cube htarget hP' ht' hy'
          have hsum :
              WeierstrassCurve.Affine.Point.some x y hP +
                  threeTorsionOrigin = (3 : ℕ) • R := by
            calc
              WeierstrassCurve.Affine.Point.some x y hP +
                    threeTorsionOrigin =
                  WeierstrassCurve.Affine.Point.some x' y' hP' := by
                rw [threeTorsionOrigin]
                exact WeierstrassCurve.Affine.Point.add_of_X_ne hx
              _ = (3 : ℕ) • R := hR
          refine ⟨⟨2, by norm_num⟩, R, ?_⟩
          rw [normalizedThreeRepresentative]
          norm_num
          rw [two_nsmul_threeTorsionOrigin_eq_neg]
          calc
            WeierstrassCurve.Affine.Point.some x y hP =
                -threeTorsionOrigin +
                  (WeierstrassCurve.Affine.Point.some x y hP +
                    threeTorsionOrigin) := by abel
            _ = -threeTorsionOrigin + (3 : ℕ) • R := by rw [hsum]
        · have hnegT : threeTorsionCurve.toAffine.Nonsingular 0 (-7) := by
            apply threeTorsionCurve.toAffine.equation_iff_nonsingular.mp
            norm_num [WeierstrassCurve.Affine.equation_iff,
              threeTorsionCurve]
          let x' : ℚ := threeTorsionCurve.toAffine.addX x 0
            (threeTorsionCurve.toAffine.slope x 0 y (-7))
          let y' : ℚ := threeTorsionCurve.toAffine.addY x 0 y
            (threeTorsionCurve.toAffine.slope x 0 y (-7))
          have hP' : threeTorsionCurve.toAffine.Nonsingular x' y' :=
            nonsingular_add hP hnegT (fun hxy => hx hxy.1)
          have hy0 : y ≠ 0 := by rw [hy]; positivity
          let t' : ℚ := -7 * t * x / y
          have ht' : t' ≠ 0 := by
            dsimp only [t']
            exact div_ne_zero
              (mul_ne_zero (mul_ne_zero (by norm_num) ht) hx) hy0
          have hy' : y' = t' ^ 3 := by
            dsimp only [y', t']
            rw [addY_neg_threeTorsionOrigin_cubeClass hP hx hy0, hy]
            field_simp [hy0]
            ring
          obtain ⟨R, hR⟩ :=
            exists_eq_three_nsmul_of_Y_eq_cube htarget hP' ht' hy'
          have hsum :
              WeierstrassCurve.Affine.Point.some x y hP +
                  -threeTorsionOrigin = (3 : ℕ) • R := by
            calc
              WeierstrassCurve.Affine.Point.some x y hP +
                    -threeTorsionOrigin =
                  WeierstrassCurve.Affine.Point.some x' y' hP' := by
                rw [threeTorsionOrigin,
                  WeierstrassCurve.Affine.Point.neg_some]
                norm_num [WeierstrassCurve.Affine.negY,
                  threeTorsionCurve]
                exact WeierstrassCurve.Affine.Point.add_of_X_ne hx
              _ = (3 : ℕ) • R := hR
          refine ⟨⟨1, by norm_num⟩, R, ?_⟩
          rw [normalizedThreeRepresentative]
          norm_num
          calc
            WeierstrassCurve.Affine.Point.some x y hP =
                threeTorsionOrigin +
                  (WeierstrassCurve.Affine.Point.some x y hP +
                    -threeTorsionOrigin) := by abel
            _ = threeTorsionOrigin + (3 : ℕ) • R := by rw [hsum]

/-- Once target surjectivity is supplied, the checked source cube-class
calculation discharges the complete three-coset certificate. -/
theorem threeCosetBound_of_targetCandidateSurjective
    (htarget : TargetThreeCandidateSurjective) :
    ThreeCosetBound :=
  threeCosetBound_of_descent_inputs sourceThreeCubeClassBound htarget

/-- Finiteness of the candidate target is sufficient for the target
surjectivity input, because its checked rational torsion subgroup is
trivial. -/
theorem targetThreeCandidateSurjective_of_finite
    [Finite veluThreeCandidateTarget.toAffine.Point] :
    TargetThreeCandidateSurjective := by
  intro P
  have hPzero : P = 0 :=
    veluThreeCandidateTarget_torsion_eq_zero P
      (isOfFinAddOrder_of_finite P)
  refine ⟨0, ?_⟩
  rw [veluThreeCandidatePointFun_zero, hPzero]

/-- End-to-end rank-zero consumer of the two isolated fixed descent
calculations. -/
theorem optimalQuotientModel_rank_zero_of_three_descent_inputs
    (hsource : SourceThreeCubeClassBound)
    (htarget : TargetThreeCandidateSurjective) :
    Module.finrank ℤ optimalQuotientModel.toAffine.Point = 0 :=
  optimalQuotientModel_point_rank_zero_of_cosetBound
    (threeCosetBound_of_descent_inputs hsource htarget)

/-- End-to-end finiteness consumer of the two isolated fixed descent
calculations. -/
theorem optimalQuotientModel_finite_of_three_descent_inputs
    (hsource : SourceThreeCubeClassBound)
    (htarget : TargetThreeCandidateSurjective) :
    Finite optimalQuotientModel.toAffine.Point :=
  optimalQuotientModel_point_finite_of_cosetBound
    (threeCosetBound_of_descent_inputs hsource htarget)

/-- Rank-zero consumer with the source local calculation fully discharged. -/
theorem optimalQuotientModel_rank_zero_of_targetCandidateSurjective
    (htarget : TargetThreeCandidateSurjective) :
    Module.finrank ℤ optimalQuotientModel.toAffine.Point = 0 :=
  optimalQuotientModel_point_rank_zero_of_cosetBound
    (threeCosetBound_of_targetCandidateSurjective htarget)

/-- Finiteness consumer with the source local calculation fully discharged. -/
theorem optimalQuotientModel_finite_of_targetCandidateSurjective
    (htarget : TargetThreeCandidateSurjective) :
    Finite optimalQuotientModel.toAffine.Point :=
  optimalQuotientModel_point_finite_of_cosetBound
    (threeCosetBound_of_targetCandidateSurjective htarget)

end MazurTorsion.OrderThirtyFive

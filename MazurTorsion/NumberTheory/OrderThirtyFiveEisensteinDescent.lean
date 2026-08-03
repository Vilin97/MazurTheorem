/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.OrderThirtyFiveTargetCubic
import Mathlib.NumberTheory.FLT.Three
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID

/-!
# Eisenstein factor arithmetic for the order-35 target descent

This file clears denominators on the fixed target model

`v² = u³ - 3(12u + 1500)²`

and factors the resulting norm equation in the ring of integers of a third
cyclotomic field.  If the negative factor is associated to a cube, Mathlib's
classification of the six Eisenstein units gives exactly three cases.  The
trivial unit has the explicit rational cubic-fibre root

`t = -42d / (c + 8d)`,

while the other two conjugate pairs produce the homogeneous cubics already
excluded by the checked mod-seven infinite descents.  Consequently the exact
associated-cube statement has a compiled consumer proving target-candidate
surjectivity and rank zero.

The global input is deliberately isolated as
`TargetEisensteinAssociatedCube`: it is the ideal-support calculation from
Cohen--Pazuki, Theorem 4.1 and Corollary 4.3.  It is proved from the primitive
denominator data in `OrderThirtyFiveEisensteinIdealSupport`, rather than being
inferred from class number one alone.
-/

open NumberField
open Polynomial
open WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.OrderThirtyFive

/-- Integral data obtained by clearing a target point's denominators.  Its
last equation is the Eisenstein norm factorization to be descended. -/
structure TargetEisensteinIntegralData (U V : ℚ) where
  d : ℤ
  m : ℤ
  n : ℤ
  b : ℤ
  d_ne_zero : d ≠ 0
  U_eq : U = (m : ℚ) / (d : ℚ) ^ 2
  V_eq : V = (n : ℚ) / (d : ℚ) ^ 3
  b_eq : b = d * (12 * m + 1500 * d ^ 2)
  norm_eq : n ^ 2 + 3 * b ^ 2 = m ^ 3

/-- The denominator presentation used by the ideal-support argument.  The
positive `d` is the square denominator of `U`; both numerators are primitive
with respect to it. -/
structure TargetEisensteinNormalizedIntegralData (U V : ℚ)
    extends TargetEisensteinIntegralData U V where
  d_pos : 0 < d
  m_coprime_d : IsCoprime m d
  n_coprime_d : IsCoprime n d

private theorem targetEisensteinNormalizedIntegralData_of_equation
    {U V : ℚ}
    (hcurve : V ^ 2 = U ^ 3 - 3 * (12 * U + 1500) ^ 2) :
    Nonempty (TargetEisensteinNormalizedIntegralData U V) := by
  let m : ℤ := U.num
  let q : ℕ := U.den
  let A : ℤ := m ^ 3 - 3 * (q : ℤ) * (12 * m + 1500 * q) ^ 2
  have hqpos : 0 < q := by
    dsimp only [q]
    exact U.den_pos
  have hq0Q : (q : ℚ) ≠ 0 := by positivity
  have hU : U = (m : ℚ) / (q : ℚ) := by
    simpa [m, q] using U.num_div_den.symm
  have hcurve' : V ^ 2 = (A : ℚ) / (q : ℚ) ^ 3 := by
    rw [hU] at hcurve
    dsimp only [A]
    push_cast
    field_simp [hq0Q] at hcurve ⊢
    linear_combination hcurve
  have hmq : IsCoprime m (q : ℤ) := by
    simpa [m, q] using Rat.isCoprime_num_den U
  have hAq : IsCoprime A ((q : ℤ) ^ 3) := by
    have hbase : IsCoprime A (q : ℤ) := by
      have hpow : IsCoprime (m ^ 3) (q : ℤ) := hmq.pow_left
      have h := hpow.add_mul_left_left
        (-3 * (12 * m + 1500 * (q : ℤ)) ^ 2)
      have heq : m ^ 3 + (q : ℤ) *
          (-3 * (12 * m + 1500 * (q : ℤ)) ^ 2) = A := by
        dsimp only [A]
        ring
      rw [← heq]
      exact h
    exact hbase.pow_right
  have hdenCast : (((V ^ 2).den : ℤ)) = (q : ℤ) ^ 3 := by
    rw [hcurve']
    exact Rat.den_div_eq_of_coprime (by positivity)
      (Int.isCoprime_iff_nat_coprime.mp hAq)
  have hden : V.den ^ 2 = q ^ 3 := by
    rw [Rat.den_pow] at hdenCast
    exact_mod_cast hdenCast
  have hq_dvd_vden : q ∣ V.den := by
    apply (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd
      (R := ℕ) (n := 2) (by norm_num)).mp
    rw [hden]
    exact ⟨q, by ring⟩
  obtain ⟨d, hd⟩ := hq_dvd_vden
  have hq_sq : q = d ^ 2 := by
    have hmul : q ^ 2 * q = q ^ 2 * d ^ 2 := by
      calc
        q ^ 2 * q = q ^ 3 := by ring
        _ = V.den ^ 2 := hden.symm
        _ = q ^ 2 * d ^ 2 := by rw [hd]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) hmul
  have hdpos : 0 < d := by
    by_contra hd0
    simp only [not_lt, nonpos_iff_eq_zero] at hd0
    subst d
    norm_num at hq_sq
    exact hqpos.ne' hq_sq
  have hd0Z : (d : ℤ) ≠ 0 := by positivity
  have hd0Q : (d : ℚ) ≠ 0 := by positivity
  have hU' : U = (m : ℚ) / (d : ℚ) ^ 2 := by
    rw [hU, hq_sq]
    norm_cast
  let W : ℚ := V * (d : ℚ) ^ 3
  let B : ℤ := m ^ 3 - 3 * (d : ℤ) ^ 2 *
    (12 * m + 1500 * (d : ℤ) ^ 2) ^ 2
  have hWsq : W ^ 2 = (B : ℚ) := by
    dsimp only [W, B]
    rw [hU'] at hcurve
    field_simp [hd0Q] at hcurve
    push_cast
    linear_combination hcurve
  let p : ℤ[X] := Polynomial.X ^ 2 - Polynomial.C B
  have hp : p.Monic := by
    dsimp only [p]
    exact Polynomial.monic_X_pow_sub_C B (by norm_num)
  have hroot : Polynomial.aeval W p = 0 := by
    dsimp only [p]
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    exact sub_eq_zero.mpr hWsq
  obtain ⟨n, hn, -⟩ := exists_integer_of_is_root_of_monic hp hroot
  have hV' : V = (n : ℚ) / (d : ℚ) ^ 3 := by
    dsimp only [W] at hn
    field_simp [hd0Q]
    exact hn
  let b : ℤ := (d : ℤ) * (12 * m + 1500 * (d : ℤ) ^ 2)
  have hnorm : n ^ 2 + 3 * b ^ 2 = m ^ 3 := by
    have hWsq' := hWsq
    rw [hn] at hWsq'
    have hnBcast : ((n ^ 2 : ℤ) : ℚ) = (B : ℚ) := by
      simpa using hWsq'
    have hnB : n ^ 2 = B := by exact_mod_cast hnBcast
    dsimp only [B, b] at hnB ⊢
    linear_combination hnB
  have hmd : IsCoprime m (d : ℤ) := by
    have hm_dsq : IsCoprime m ((d : ℤ) ^ 2) := by
      simpa [hq_sq] using hmq
    exact hm_dsq.of_isCoprime_of_dvd_right ⟨d, by ring⟩
  have hnd : IsCoprime n (d : ℤ) := by
    apply isCoprime_of_prime_dvd
    · rintro ⟨-, hdzero⟩
      exact hd0Z hdzero
    · intro p hp hpn hpd
      have hpb : p ∣ b := by
        exact hpd.trans ⟨12 * m + 1500 * (d : ℤ) ^ 2, rfl⟩
      have hpm3 : p ∣ m ^ 3 := by
        rw [← hnorm]
        have hpn2 : p ∣ n ^ 2 := by
          simpa [pow_two] using hpn.mul_right n
        have hpb2 : p ∣ b ^ 2 := by
          simpa [pow_two] using hpb.mul_right b
        exact dvd_add hpn2 (hpb2.mul_left 3)
      have hpm : p ∣ m := hp.dvd_of_dvd_pow hpm3
      exact hp.not_unit (hmd.isUnit_of_dvd' hpm hpd)
  refine ⟨
    { d := d
      m := m
      n := n
      b := b
      d_ne_zero := hd0Z
      U_eq := hU'
      V_eq := hV'
      b_eq := rfl
      norm_eq := hnorm
      d_pos := by exact_mod_cast hdpos
      m_coprime_d := hmd
      n_coprime_d := hnd }⟩

/-- Every affine target point has a positive primitive denominator
presentation. -/
theorem targetEisensteinNormalizedIntegralData
    {X Y : ℚ}
    (hP : veluThreeCandidateTarget.toAffine.Nonsingular X Y) :
    Nonempty (TargetEisensteinNormalizedIntegralData
      (targetThreeDescentU X) (targetThreeDescentV X Y)) := by
  apply targetEisensteinNormalizedIntegralData_of_equation
  exact targetThreeDescent_equation hP

/-- Forgetting primitivity recovers the original denominator-cleared
interface. -/
theorem targetEisensteinIntegralData
    {X Y : ℚ}
    (hP : veluThreeCandidateTarget.toAffine.Nonsingular X Y) :
    Nonempty (TargetEisensteinIntegralData (targetThreeDescentU X)
      (targetThreeDescentV X Y)) := by
  obtain ⟨D⟩ := targetEisensteinNormalizedIntegralData hP
  exact ⟨D.toTargetEisensteinIntegralData⟩

end MazurTorsion.OrderThirtyFive

namespace MazurTorsion.OrderThirtyFive

open IsCyclotomicExtension.Rat.Three

variable {K : Type*} [Field K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 3)

/-- The element `2ζ₃+1`, whose square is `-3`, in the ring of integers. -/
def eisensteinSqrtNegThree : 𝓞 K :=
  2 * hζ.toInteger + 1

private theorem eisensteinSqrtNegThree_sq :
    eisensteinSqrtNegThree hζ ^ 2 = -3 := by
  have hroot := hζ.toInteger_isPrimitiveRoot.isRoot_cyclotomic
    (by norm_num)
  rw [Polynomial.cyclotomic_three] at hroot
  norm_num [Polynomial.IsRoot] at hroot
  simp only [eisensteinSqrtNegThree]
  linear_combination 4 * hroot

private theorem eisensteinNormFactor (m n : ℤ) :
    ((m : 𝓞 K) - n * eisensteinSqrtNegThree hζ) *
        ((m : 𝓞 K) + n * eisensteinSqrtNegThree hζ) =
      ((m ^ 2 + 3 * n ^ 2 : ℤ) : 𝓞 K) := by
  calc
    _ = (m : 𝓞 K) ^ 2 - (n : 𝓞 K) ^ 2 *
        eisensteinSqrtNegThree hζ ^ 2 := by ring
    _ = ((m ^ 2 + 3 * n ^ 2 : ℤ) : 𝓞 K) := by
      rw [eisensteinSqrtNegThree_sq]
      push_cast
      ring

private theorem eisensteinEtaCoords_zero_field [CharZero K]
    (hζ : IsPrimitiveRoot ζ 3) {a b : ℤ}
    (h : (a : K) + b * ζ = 0) :
    a = 0 ∧ b = 0 := by
  have hroot := hζ.isRoot_cyclotomic (by norm_num)
  rw [Polynomial.cyclotomic_three] at hroot
  norm_num [Polynomial.IsRoot] at hroot
  have hnormK : ((a ^ 2 - a * b + b ^ 2 : ℤ) : K) = 0 := by
    calc
      ((a ^ 2 - a * b + b ^ 2 : ℤ) : K) =
          ((a : K) + b * ζ) * ((a - b : ℤ) - b * ζ) := by
            push_cast
            linear_combination (b : K) ^ 2 * hroot
      _ = 0 := by rw [h]; simp
  have hnormZ : a ^ 2 - a * b + b ^ 2 = 0 := by
    exact_mod_cast hnormK
  have hb : b = 0 := by
    nlinarith [sq_nonneg (2 * a - b), sq_nonneg b]
  subst b
  norm_num at hnormZ
  exact ⟨hnormZ, rfl⟩

private theorem eisensteinEtaCoords_zero [CharZero K] {a b : ℤ}
    (h : (a : 𝓞 K) + b * hζ.toInteger = 0) :
    a = 0 ∧ b = 0 := by
  have hK := congrArg (fun z : 𝓞 K ↦ (z : K)) h
  change (a : K) + b * ζ = 0 at hK
  exact eisensteinEtaCoords_zero_field hζ hK

/-- Equality in the integral basis `(1, ζ₃)` is coordinatewise. -/
theorem eisensteinEtaCoords_injective [CharZero K] {a b c d : ℤ}
    (h : (a : 𝓞 K) + b * hζ.toInteger =
      (c : 𝓞 K) + d * hζ.toInteger) :
    a = c ∧ b = d := by
  have hK := congrArg (fun z : 𝓞 K ↦ (z : K)) h
  change (a : K) + b * ζ = (c : K) + d * ζ at hK
  have hzero' : ((a - c : ℤ) : K) +
      ((b - d : ℤ) : K) * ζ = 0 := by
    push_cast
    linear_combination hK
  obtain ⟨hac, hbd⟩ :=
    eisensteinEtaCoords_zero_field (a := a - c) (b := b - d) hζ hzero'
  exact ⟨sub_eq_zero.mp hac, sub_eq_zero.mp hbd⟩

private def plusUnitReal (a b : ℤ) : ℤ :=
  a ^ 3 - 3 * a ^ 2 * b + b ^ 3

private def plusUnitEta (a b : ℤ) : ℤ :=
  a ^ 3 - 3 * a * b ^ 2 + b ^ 3

private def minusUnitReal (a b : ℤ) : ℤ :=
  3 * a ^ 2 * b - 3 * a * b ^ 2

private def minusUnitEta (a b : ℤ) : ℤ :=
  -a ^ 3 + 3 * a ^ 2 * b - b ^ 3

private theorem plusUnitNorm (a b : ℤ) :
    plusUnitReal a b ^ 2 -
        plusUnitReal a b * plusUnitEta a b +
      plusUnitEta a b ^ 2 = (a ^ 2 - a * b + b ^ 2) ^ 3 := by
  simp only [plusUnitReal, plusUnitEta]
  ring

private theorem minusUnitNorm (a b : ℤ) :
    minusUnitReal a b ^ 2 -
        minusUnitReal a b * minusUnitEta a b +
      minusUnitEta a b ^ 2 = (a ^ 2 - a * b + b ^ 2) ^ 3 := by
  simp only [minusUnitReal, minusUnitEta]
  ring

private theorem TargetEisensteinIntegralData.unitCover_solution_of_plus_coords
    {U V : ℚ} (D : TargetEisensteinIntegralData U V) (a b : ℤ)
    (hreal : D.n - D.b = plusUnitReal a b)
    (heta : -2 * D.b = plusUnitEta a b) :
    targetEisensteinUnitCover (2 * a - b) b (2 * D.d) = 0 ∧
      ¬(2 * a - b = 0 ∧ b = 0 ∧ 2 * D.d = 0) := by
  let q : ℤ := a ^ 2 - a * b + b ^ 2
  have hcubes : D.m ^ 3 = q ^ 3 := by
    calc
      D.m ^ 3 = D.n ^ 2 + 3 * D.b ^ 2 := D.norm_eq.symm
      _ = (D.n - D.b) ^ 2 -
          (D.n - D.b) * (-2 * D.b) + (-2 * D.b) ^ 2 := by ring
      _ = plusUnitReal a b ^ 2 -
          plusUnitReal a b * plusUnitEta a b +
            plusUnitEta a b ^ 2 := by rw [hreal, heta]
      _ = q ^ 3 := plusUnitNorm a b
  have hm : D.m = q :=
    (show Odd 3 by decide).pow_injective hcubes
  have heta' := heta
  rw [D.b_eq, hm] at heta'
  simp only [plusUnitEta] at heta'
  constructor
  · simp only [targetEisensteinUnitCover]
    dsimp only [q] at heta'
    linear_combination -8 * heta'
  · rintro ⟨-, -, hd⟩
    apply D.d_ne_zero
    linarith

private theorem TargetEisensteinIntegralData.conjugateUnitCover_solution_of_minus_coords
    {U V : ℚ} (D : TargetEisensteinIntegralData U V) (a b : ℤ)
    (hreal : D.n - D.b = minusUnitReal a b)
    (heta : -2 * D.b = minusUnitEta a b) :
    targetEisensteinConjugateUnitCover (2 * a - b) b (2 * D.d) = 0 ∧
      ¬(2 * a - b = 0 ∧ b = 0 ∧ 2 * D.d = 0) := by
  let q : ℤ := a ^ 2 - a * b + b ^ 2
  have hcubes : D.m ^ 3 = q ^ 3 := by
    calc
      D.m ^ 3 = D.n ^ 2 + 3 * D.b ^ 2 := D.norm_eq.symm
      _ = (D.n - D.b) ^ 2 -
          (D.n - D.b) * (-2 * D.b) + (-2 * D.b) ^ 2 := by ring
      _ = minusUnitReal a b ^ 2 -
          minusUnitReal a b * minusUnitEta a b +
            minusUnitEta a b ^ 2 := by rw [hreal, heta]
      _ = q ^ 3 := minusUnitNorm a b
  have hm : D.m = q :=
    (show Odd 3 by decide).pow_injective hcubes
  have heta' := heta
  rw [D.b_eq, hm] at heta'
  simp only [minusUnitEta] at heta'
  constructor
  · simp only [targetEisensteinConjugateUnitCover]
    dsimp only [q] at heta'
    linear_combination -8 * heta'
  · rintro ⟨-, -, hd⟩
    apply D.d_ne_zero
    linarith

private theorem oneAddEta_cube (a b : ℤ) :
    (1 + hζ.toInteger) *
        ((a : 𝓞 K) + b * hζ.toInteger) ^ 3 =
      (plusUnitReal a b : 𝓞 K) +
        plusUnitEta a b * hζ.toInteger := by
  have hroot := hζ.toInteger_isPrimitiveRoot.isRoot_cyclotomic
    (by norm_num)
  rw [Polynomial.cyclotomic_three] at hroot
  norm_num [Polynomial.IsRoot] at hroot
  have hcube := hζ.toInteger_isPrimitiveRoot.pow_eq_one
  have hsq : hζ.toInteger ^ 2 = -hζ.toInteger - 1 := by
    linear_combination hroot
  have hfour : hζ.toInteger ^ 4 = hζ.toInteger := by
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, hcube,
      one_mul]
  simp only [plusUnitReal, plusUnitEta]
  push_cast
  ring_nf
  rw [hfour, hcube, hsq]
  ring

private theorem negEta_cube (a b : ℤ) :
    -hζ.toInteger *
        ((a : 𝓞 K) + b * hζ.toInteger) ^ 3 =
      (minusUnitReal a b : 𝓞 K) +
        minusUnitEta a b * hζ.toInteger := by
  have hroot := hζ.toInteger_isPrimitiveRoot.isRoot_cyclotomic
    (by norm_num)
  rw [Polynomial.cyclotomic_three] at hroot
  norm_num [Polynomial.IsRoot] at hroot
  have hcube := hζ.toInteger_isPrimitiveRoot.pow_eq_one
  have hsq : hζ.toInteger ^ 2 = -hζ.toInteger - 1 := by
    linear_combination hroot
  have hfour : hζ.toInteger ^ 4 = hζ.toInteger := by
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, hcube,
      one_mul]
  simp only [minusUnitReal, minusUnitEta]
  push_cast
  ring_nf
  rw [hfour, hcube, hsq]
  ring

private def cubeReal (a b : ℤ) : ℤ :=
  a ^ 3 - 3 * a * b ^ 2 + b ^ 3

private def cubeEta (a b : ℤ) : ℤ :=
  3 * a ^ 2 * b - 3 * a * b ^ 2

private theorem eisensteinCube (a b : ℤ) :
    ((a : 𝓞 K) + b * hζ.toInteger) ^ 3 =
      (cubeReal a b : 𝓞 K) +
        cubeEta a b * hζ.toInteger := by
  have hroot := hζ.toInteger_isPrimitiveRoot.isRoot_cyclotomic
    (by norm_num)
  rw [Polynomial.cyclotomic_three] at hroot
  norm_num [Polynomial.IsRoot] at hroot
  have hcube := hζ.toInteger_isPrimitiveRoot.pow_eq_one
  have hsq : hζ.toInteger ^ 2 = -hζ.toInteger - 1 := by
    linear_combination hroot
  simp only [cubeReal, cubeEta]
  push_cast
  ring_nf
  rw [hcube, hsq]
  ring

/-- The negative Eisenstein factor `n-b√-3` of the cleared norm equation. -/
def TargetEisensteinIntegralData.minusFactor {U V : ℚ}
    (D : TargetEisensteinIntegralData U V) : 𝓞 K :=
  (D.n : 𝓞 K) - D.b * eisensteinSqrtNegThree hζ

/-- The conjugate factor `n+b√-3` of the cleared norm equation. -/
def TargetEisensteinIntegralData.plusFactor {U V : ℚ}
    (D : TargetEisensteinIntegralData U V) : 𝓞 K :=
  (D.n : 𝓞 K) + D.b * eisensteinSqrtNegThree hζ

/-- Coordinates of the negative factor in the integral basis `(1,ζ₃)`. -/
theorem TargetEisensteinIntegralData.minusFactor_coords {U V : ℚ}
    (D : TargetEisensteinIntegralData U V) :
    D.minusFactor hζ =
      ((D.n - D.b : ℤ) : 𝓞 K) +
        (-2 * D.b : ℤ) * hζ.toInteger := by
  simp only [TargetEisensteinIntegralData.minusFactor, eisensteinSqrtNegThree]
  push_cast
  ring

/-- Coordinates of the positive factor in the integral basis `(1,ζ₃)`. -/
theorem TargetEisensteinIntegralData.plusFactor_coords {U V : ℚ}
    (D : TargetEisensteinIntegralData U V) :
    D.plusFactor hζ =
      ((D.n + D.b : ℤ) : 𝓞 K) -
        (-2 * D.b : ℤ) * hζ.toInteger := by
  simp only [TargetEisensteinIntegralData.plusFactor, eisensteinSqrtNegThree]
  push_cast
  ring

/-- The two conjugate Eisenstein factors multiply to the cube `m³`. -/
theorem TargetEisensteinIntegralData.factors_mul {U V : ℚ}
    (D : TargetEisensteinIntegralData U V) :
    D.minusFactor hζ * D.plusFactor hζ = (D.m : 𝓞 K) ^ 3 := by
  rw [TargetEisensteinIntegralData.minusFactor, TargetEisensteinIntegralData.plusFactor,
    eisensteinNormFactor]
  rw [D.norm_eq]
  push_cast
  ring

/-- If the conjugate factors are coprime, unique factorization in the
class-number-one third cyclotomic ring makes the negative factor an
associated cube.  The remaining global support argument must handle the
nonsplit common-prime case as well. -/
theorem TargetEisensteinIntegralData.exists_associated_cube_of_isCoprime
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    {U V : ℚ} (D : TargetEisensteinIntegralData U V)
    (hcoprime : IsCoprime (D.minusFactor hζ) (D.plusFactor hζ)) :
    ∃ z : 𝓞 K, Associated (z ^ 3) (D.minusFactor hζ) := by
  letI : IsPrincipalIdealRing (𝓞 K) :=
    IsCyclotomicExtension.Rat.three_pid K
  exact exists_associated_pow_of_mul_eq_pow' hcoprime (D.factors_mul hζ)

/-- Every Eisenstein integer has coordinates in the integral basis
`(1, ζ₃)`. -/
theorem exists_eisenstein_integer_coords
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    (z : 𝓞 K) :
    ∃ a b : ℤ, z = a + b * hζ.toInteger := by
  let pb := hζ.integralPowerBasis
  have hdim : pb.dim = 2 := by
    dsimp only [pb]
    rw [hζ.integralPowerBasis_dim]
    decide
  obtain ⟨f, hfdeg, hz⟩ := pb.exists_eq_aeval z
  have hfdeg' : f.natDegree < 2 := by simpa [hdim] using hfdeg
  let a : ℤ := f.coeff 0
  let b : ℤ := f.coeff 1
  have hf : f = Polynomial.C a +
      Polynomial.C b * Polynomial.X := by
    have hsum := f.as_sum_range' 2 hfdeg'
    norm_num [Finset.sum_range_succ] at hsum
    calc
      f = Polynomial.C (f.coeff 0) +
          Polynomial.monomial 1 (f.coeff 1) := hsum
      _ = Polynomial.C a + Polynomial.C b * Polynomial.X := by
        rw [Polynomial.C_mul_X_eq_monomial]
  refine ⟨a, b, ?_⟩
  calc
    z = Polynomial.aeval pb.gen f := hz
    _ = a + b * hζ.toInteger := by
      rw [hf]
      simp only [map_add, map_mul, Polynomial.aeval_C,
        Polynomial.aeval_X]
      rw [show pb.gen = hζ.toInteger by
        exact hζ.integralPowerBasis_gen]
      have ha : (algebraMap ℤ (𝓞 K)) a = (a : 𝓞 K) := by
        simp
      have hb : (algebraMap ℤ (𝓞 K)) b = (b : 𝓞 K) := by
        simp
      rw [ha, hb]

private theorem TargetEisensteinIntegralData.exists_unitCover_solution_of_plus_cube
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    {U V : ℚ} (D : TargetEisensteinIntegralData U V) (z : 𝓞 K)
    (hfactor : D.minusFactor hζ =
      (1 + hζ.toInteger) * z ^ 3) :
    ∃ A B C : ℤ,
      targetEisensteinUnitCover A B C = 0 ∧
        ¬(A = 0 ∧ B = 0 ∧ C = 0) := by
  obtain ⟨a, b, hz⟩ := exists_eisenstein_integer_coords hζ z
  have hcoords :
      ((D.n - D.b : ℤ) : 𝓞 K) +
          (-2 * D.b : ℤ) * hζ.toInteger =
        (plusUnitReal a b : 𝓞 K) +
          plusUnitEta a b * hζ.toInteger := by
    calc
      _ = D.minusFactor hζ := (D.minusFactor_coords hζ).symm
      _ = (1 + hζ.toInteger) * z ^ 3 := hfactor
      _ = (1 + hζ.toInteger) *
          ((a : 𝓞 K) + b * hζ.toInteger) ^ 3 := by rw [hz]
      _ = _ := oneAddEta_cube hζ a b
  obtain ⟨hreal, heta⟩ := eisensteinEtaCoords_injective hζ hcoords
  refine ⟨2 * a - b, b, 2 * D.d, ?_⟩
  exact D.unitCover_solution_of_plus_coords a b hreal heta

private theorem TargetEisensteinIntegralData.exists_conjugateUnitCover_solution_of_minus_cube
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    {U V : ℚ} (D : TargetEisensteinIntegralData U V) (z : 𝓞 K)
    (hfactor : D.minusFactor hζ =
      -hζ.toInteger * z ^ 3) :
    ∃ A B C : ℤ,
      targetEisensteinConjugateUnitCover A B C = 0 ∧
        ¬(A = 0 ∧ B = 0 ∧ C = 0) := by
  obtain ⟨a, b, hz⟩ := exists_eisenstein_integer_coords hζ z
  have hcoords :
      ((D.n - D.b : ℤ) : 𝓞 K) +
          (-2 * D.b : ℤ) * hζ.toInteger =
        (minusUnitReal a b : 𝓞 K) +
          minusUnitEta a b * hζ.toInteger := by
    calc
      _ = D.minusFactor hζ := (D.minusFactor_coords hζ).symm
      _ = -hζ.toInteger * z ^ 3 := hfactor
      _ = -hζ.toInteger *
          ((a : 𝓞 K) + b * hζ.toInteger) ^ 3 := by rw [hz]
      _ = _ := negEta_cube hζ a b
  obtain ⟨hreal, heta⟩ := eisensteinEtaCoords_injective hζ hcoords
  refine ⟨2 * a - b, b, 2 * D.d, ?_⟩
  exact D.conjugateUnitCover_solution_of_minus_coords a b hreal heta

/-- A literal cube in the trivial unit class gives the explicit fibre root
`-42d/(c+8d)`. -/
theorem TargetEisensteinIntegralData.exists_targetCubicFibre_root_of_cube
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    {X V : ℚ} (D : TargetEisensteinIntegralData (targetThreeDescentU X) V)
    (z : 𝓞 K) (hfactor : D.minusFactor hζ = z ^ 3) :
    ∃ t : ℚ, targetCubicFibre X t = 0 := by
  obtain ⟨a, c, hz⟩ := exists_eisenstein_integer_coords hζ z
  have hcoords :
      ((D.n - D.b : ℤ) : 𝓞 K) +
          (-2 * D.b : ℤ) * hζ.toInteger =
        (cubeReal a c : 𝓞 K) +
          cubeEta a c * hζ.toInteger := by
    calc
      _ = D.minusFactor hζ := (D.minusFactor_coords hζ).symm
      _ = z ^ 3 := hfactor
      _ = ((a : 𝓞 K) + c * hζ.toInteger) ^ 3 := by rw [hz]
      _ = _ := eisensteinCube hζ a c
  obtain ⟨hreal, heta⟩ := eisensteinEtaCoords_injective hζ hcoords
  let q : ℤ := a ^ 2 - a * c + c ^ 2
  have hcubeNorm : D.m ^ 3 = q ^ 3 := by
    calc
      D.m ^ 3 = D.n ^ 2 + 3 * D.b ^ 2 := D.norm_eq.symm
      _ = (D.n - D.b) ^ 2 -
          (D.n - D.b) * (-2 * D.b) + (-2 * D.b) ^ 2 := by ring
      _ = cubeReal a c ^ 2 -
          cubeReal a c * cubeEta a c +
            cubeEta a c ^ 2 := by rw [hreal, heta]
      _ = q ^ 3 := by
        simp only [cubeReal, cubeEta]
        dsimp only [q]
        ring
  have hm : D.m = q :=
    (show Odd 3 by decide).pow_injective hcubeNorm
  have heta' := heta
  rw [D.b_eq, hm] at heta'
  simp only [cubeEta] at heta'
  have hden : c + 8 * D.d ≠ 0 := by
    intro hzero
    have hc : c = -8 * D.d := by linarith
    dsimp only [q] at heta'
    rw [hc] at heta'
    have hdCube : D.d ^ 3 = 0 := by nlinarith [heta']
    exact (pow_ne_zero 3 D.d_ne_zero) hdCube
  have hdQ : (D.d : ℚ) ≠ 0 := by exact_mod_cast D.d_ne_zero
  have hX :
      36 * (D.d : ℚ) ^ 2 * X - D.m +
          192 * (D.d : ℚ) ^ 2 = 0 := by
    have hU := D.U_eq
    simp only [targetThreeDescentU] at hU
    field_simp [hdQ] at hU
    calc
      _ = (36 * X + 192) * (D.d : ℚ) ^ 2 - D.m := by ring
      _ = 0 := sub_eq_zero.mpr hU
  refine ⟨-42 * (D.d : ℚ) / (c + 8 * D.d : ℤ), ?_⟩
  simp only [targetCubicFibre]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat]
  change
    (-42 * (D.d : ℚ) / ((c : ℚ) + 8 * D.d)) ^ 3 -
        X * (-42 * (D.d : ℚ) / ((c : ℚ) + 8 * D.d)) ^ 2 +
      28 * (-42 * (D.d : ℚ) / ((c : ℚ) + 8 * D.d)) + 49 = 0
  have hdenQ' : (c : ℚ) + 8 * D.d ≠ 0 := by
    exact_mod_cast hden
  have hdenCube :
      (D.d : ℚ) * c ^ 2 * 24 + (D.d : ℚ) ^ 2 * c * 192 +
          (D.d : ℚ) ^ 3 * 512 + (c : ℚ) ^ 3 ≠ 0 := by
    intro hzero
    exact (pow_ne_zero 3 hdenQ') (by
      calc
        ((c : ℚ) + 8 * D.d) ^ 3 =
            (D.d : ℚ) * c ^ 2 * 24 + (D.d : ℚ) ^ 2 * c * 192 +
              (D.d : ℚ) ^ 3 * 512 + (c : ℚ) ^ 3 := by ring
        _ = 0 := hzero)
  rw [hm] at hX
  have hetaQ := congrArg (fun z : ℤ ↦ (z : ℚ)) heta'
  push_cast at hetaQ hX
  dsimp only [q] at hetaQ hX
  push_cast at hetaQ hX
  simp only [div_pow]
  field_simp [hdenQ', hdenCube]
  have hdenQ'' : (c : ℚ) + (D.d : ℚ) * 8 ≠ 0 := by
    intro hzero
    apply hdenQ'
    linarith
  rw [add_eq_zero_iff_eq_neg]
  rw [div_eq_iff (pow_ne_zero 3 hdenQ'')]
  linear_combination
    (-49 * ((c : ℚ) + 8 * D.d)) * hX +
      (49 / 3 : ℚ) * hetaQ

/-- An associated cube factor gives either a rational fibre root or a
nonzero integral point on one of the two nontrivial unit covers. -/
theorem TargetEisensteinIntegralData.descent_alternatives_of_associated
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    {X V : ℚ} (D : TargetEisensteinIntegralData (targetThreeDescentU X) V)
    {z : 𝓞 K} (hassociated : Associated (z ^ 3) (D.minusFactor hζ)) :
    (∃ t : ℚ, targetCubicFibre X t = 0) ∨
      (∃ A B C : ℤ,
        targetEisensteinUnitCover A B C = 0 ∧
          ¬(A = 0 ∧ B = 0 ∧ C = 0)) ∨
      ∃ A B C : ℤ,
        targetEisensteinConjugateUnitCover A B C = 0 ∧
          ¬(A = 0 ∧ B = 0 ∧ C = 0) := by
  obtain ⟨u, hu⟩ := hassociated
  have hfactor : D.minusFactor hζ = (u : 𝓞 K) * z ^ 3 := by
    rw [← hu]
    ring
  let η : (𝓞 K)ˣ :=
    (IsPrimitiveRoot.isUnit hζ.toInteger_isPrimitiveRoot (by decide)).unit
  have hmem := IsCyclotomicExtension.Rat.Three.Units.mem hζ u
  change u ∈ [1, -1, η, -η, η ^ 2, -η ^ 2] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h <;> subst u
  all_goals
    simp only [η, Units.val_one, Units.val_neg,
      Units.val_pow_eq_pow_val,
      IsCyclotomicExtension.Rat.Three.coe_eta] at hfactor
  · left
    exact D.exists_targetCubicFibre_root_of_cube hζ z (by
      simpa only [Units.val_one, one_mul] using hfactor)
  · left
    exact D.exists_targetCubicFibre_root_of_cube hζ (-z) (by
      simpa only [Units.val_neg, Units.val_one, neg_one_mul,
        Odd.neg_pow (by decide : Odd 3)] using hfactor)
  · right; right
    exact D.exists_conjugateUnitCover_solution_of_minus_cube hζ (-z) (by
      calc
        D.minusFactor hζ = hζ.toInteger * z ^ 3 := hfactor
        _ = -hζ.toInteger * (-z) ^ 3 := by
          rw [Odd.neg_pow (by decide : Odd 3)]
          ring)
  · right; right
    exact D.exists_conjugateUnitCover_solution_of_minus_cube hζ z (by
      exact hfactor)
  · right; left
    exact D.exists_unitCover_solution_of_plus_cube hζ (-z) (by
      rw [Odd.neg_pow (by decide : Odd 3)]
      calc
        D.minusFactor hζ = hζ.toInteger ^ 2 * z ^ 3 := by
          exact hfactor
        _ = (1 + hζ.toInteger) * -z ^ 3 := by
          have hetaSq : hζ.toInteger ^ 2 =
              -hζ.toInteger - 1 := by
            simpa only [IsCyclotomicExtension.Rat.Three.coe_eta] using
              IsCyclotomicExtension.Rat.Three.eta_sq hζ
          rw [hetaSq]
          ring)
  · right; left
    exact D.exists_unitCover_solution_of_plus_cube hζ z (by
      calc
        D.minusFactor hζ = -(hζ.toInteger ^ 2) * z ^ 3 := by
          exact hfactor
        _ = (1 + hζ.toInteger) * z ^ 3 := by
          have hetaSq : hζ.toInteger ^ 2 =
              -hζ.toInteger - 1 := by
            simpa only [IsCyclotomicExtension.Rat.Three.coe_eta] using
              IsCyclotomicExtension.Rat.Three.eta_sq hζ
          rw [hetaSq]
          ring)

/-- The exact ideal-support interface: every target point admits
a positive primitive integral presentation whose negative factor is
associated to a cube in `ℤ[ζ₃]`.  The existential presentation is essential:
the rank-zero consumer does not require a claim about every possible common
rescaling of the denominator data. -/
def TargetEisensteinAssociatedCube : Prop :=
  ∀ (K : Type) [Field K] [NumberField K]
      [IsCyclotomicExtension {3} ℚ K]
      {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
      {X Y : ℚ}
      (_hP : veluThreeCandidateTarget.toAffine.Nonsingular X Y),
    ∃ (D : TargetEisensteinNormalizedIntegralData
        (targetThreeDescentU X) (targetThreeDescentV X Y)) (z : 𝓞 K),
      Associated (z ^ 3)
        (D.toTargetEisensteinIntegralData.minusFactor hζ)

/-- The associated-cube input discharges the complete three-class descent
reduction consumed by the checked local obstructions. -/
theorem targetEisensteinDescentReduction_of_associatedCube
    (hfactor : TargetEisensteinAssociatedCube) :
    TargetEisensteinDescentReduction := by
  intro X Y hP
  let K := CyclotomicField 3 ℚ
  letI : IsCyclotomicExtension {3} ℚ K :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  let hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have : NumberField K :=
    IsCyclotomicExtension.numberField {3} ℚ K
  obtain ⟨D, z, hz⟩ := hfactor K hζ hP
  exact D.toTargetEisensteinIntegralData.descent_alternatives_of_associated
    hζ hz

/-- The associated-cube input forces a rational root in every target cubic
fibre. -/
theorem targetCubicFibreRoots_of_associatedCube
    (hfactor : TargetEisensteinAssociatedCube) :
    TargetCubicFibreRoots :=
  targetCubicFibreRoots_of_eisensteinDescentReduction
    (targetEisensteinDescentReduction_of_associatedCube hfactor)

/-- End-to-end rank-zero consumer of the exact remaining ideal-support
statement. -/
theorem optimalQuotientModel_rank_zero_of_associatedCube
    (hfactor : TargetEisensteinAssociatedCube) :
    Module.finrank ℤ optimalQuotientModel.toAffine.Point = 0 :=
  optimalQuotientModel_rank_zero_of_targetCubicFibreRoots
    (targetCubicFibreRoots_of_associatedCube hfactor)

end MazurTorsion.OrderThirtyFive

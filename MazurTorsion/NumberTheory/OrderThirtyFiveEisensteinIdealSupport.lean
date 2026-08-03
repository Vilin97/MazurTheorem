/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.OrderThirtyFiveEisensteinDescent

/-!
# Ideal support for the order-35 Eisenstein descent

This file proves the remaining ideal-support step for the normalized equation

`n² + 3b² = m³`.

A common prime of the two Eisenstein factors is shown to lie over `2`, `3`,
or `5`. The primes `2` and `5` are inert, while `√-3` is the ramified
prime over `3`. Coordinate conjugation identifies the valuations of both
factors at all three exceptional primes. Comparing valuations in
`(n-b√-3)(n+b√-3)=m³` then makes every valuation of the negative factor a
multiple of three. Unique factorization produces an associated cube and
closes the checked order-35 rank-zero descent.
-/

open NumberField Polynomial WeierstrassCurve UniqueFactorizationMonoid
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.OrderThirtyFive

open IsCyclotomicExtension.Rat.Three

variable {K : Type*} [Field K] [NumberField K]
variable [IsCyclotomicExtension {3} ℚ K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 3)


private def eisensteinCoordinateNorm (a b : ℤ) : ℤ := a ^ 2 - a * b + b ^ 2

private lemma eisensteinCoordinateNorm_mul (a b c d : ℤ) :
    eisensteinCoordinateNorm (a * c - b * d) (a * d + b * c - b * d) =
      eisensteinCoordinateNorm a b * eisensteinCoordinateNorm c d := by
  simp only [eisensteinCoordinateNorm]
  ring

private lemma eisensteinCoordinateNorm_pos {a b : ℤ} (h : ¬(a = 0 ∧ b = 0)) :
    0 < eisensteinCoordinateNorm a b := by
  simp only [eisensteinCoordinateNorm]
  by_contra hnpos
  have hid : 4 * (a ^ 2 - a * b + b ^ 2) =
      (2 * a - b) ^ 2 + 3 * b ^ 2 := by ring
  have hb2 : b ^ 2 = 0 := by
    nlinarith [sq_nonneg (2 * a - b), sq_nonneg b]
  have hb : b = 0 := sq_eq_zero_iff.mp hb2
  have ha : a = 0 := by
    rw [hb] at hnpos
    norm_num at hnpos
    exact hnpos
  exact h ⟨ha, hb⟩

private lemma eisensteinCoordinateNorm_ne_two_or_five (a b : ℤ) :
    eisensteinCoordinateNorm a b ≠ 2 ∧ eisensteinCoordinateNorm a b ≠ 5 := by
  have hpow := ZMod.pow_card ((a + b : ℤ) : ZMod 3)
  constructor <;> intro hnorm
  · have hmod := congrArg (fun z : ℤ ↦ (z : ZMod 3)) hnorm
    simp only [eisensteinCoordinateNorm] at hmod
    push_cast at hmod
    have hsq : (((a + b : ℤ) : ZMod 3) ^ 2) = 2 := by
      calc
        _ = (a : ZMod 3) ^ 2 - (a : ZMod 3) * b + (b : ZMod 3) ^ 2 := by
          push_cast
          have hthree : (3 : ZMod 3) = 0 := by decide
          rw [← sub_eq_iff_eq_add]
          linear_combination hthree * ((a : ZMod 3) * b)
        _ = 2 := hmod
    have hx0 : ((a + b : ℤ) : ZMod 3) = 0 := by
      rw [show ((a + b : ℤ) : ZMod 3) ^ 3 =
          ((a + b : ℤ) : ZMod 3) ^ 2 * ((a + b : ℤ) : ZMod 3) by ring,
        hsq] at hpow
      linear_combination hpow
    rw [hx0] at hsq
    exact (by decide : (0 : ZMod 3) ≠ 2) hsq
  · have hmod := congrArg (fun z : ℤ ↦ (z : ZMod 3)) hnorm
    simp only [eisensteinCoordinateNorm] at hmod
    push_cast at hmod
    have hsq : (((a + b : ℤ) : ZMod 3) ^ 2) = 2 := by
      calc
        _ = (a : ZMod 3) ^ 2 - (a : ZMod 3) * b + (b : ZMod 3) ^ 2 := by
          push_cast
          have hthree : (3 : ZMod 3) = 0 := by decide
          rw [← sub_eq_iff_eq_add]
          linear_combination hthree * ((a : ZMod 3) * b)
        _ = (5 : ZMod 3) := hmod
        _ = 2 := by decide
    have hx0 : ((a + b : ℤ) : ZMod 3) = 0 := by
      rw [show ((a + b : ℤ) : ZMod 3) ^ 3 =
          ((a + b : ℤ) : ZMod 3) ^ 2 * ((a + b : ℤ) : ZMod 3) by ring,
        hsq] at hpow
      linear_combination hpow
    rw [hx0] at hsq
    exact (by decide : (0 : ZMod 3) ≠ 2) hsq

omit [NumberField K] [IsCyclotomicExtension {3} ℚ K] in
private lemma eisenstein_mul_coords (a b c d : ℤ) :
    ((a : 𝓞 K) + b * hζ.toInteger) *
        ((c : 𝓞 K) + d * hζ.toInteger) =
      ((a * c - b * d : ℤ) : 𝓞 K) +
        (a * d + b * c - b * d) * hζ.toInteger := by
  have hroot := hζ.toInteger_isPrimitiveRoot.isRoot_cyclotomic
    (by norm_num)
  rw [Polynomial.cyclotomic_three] at hroot
  norm_num [Polynomial.IsRoot] at hroot
  push_cast
  linear_combination b * d * hroot

omit [NumberField K] [IsCyclotomicExtension {3} ℚ K] in
private lemma isUnit_of_eisensteinCoordinateNorm_eq_one {a b : ℤ}
    (h : eisensteinCoordinateNorm a b = 1) :
    IsUnit ((a : 𝓞 K) + b * hζ.toInteger) := by
  rw [isUnit_iff_exists_inv]
  refine ⟨((a - b : ℤ) : 𝓞 K) - b * hζ.toInteger, ?_⟩
  rw [show ((a - b : ℤ) : 𝓞 K) - b * hζ.toInteger =
      ((a - b : ℤ) : 𝓞 K) + (-b : ℤ) * hζ.toInteger by push_cast; ring]
  rw [eisenstein_mul_coords hζ]
  simp only [eisensteinCoordinateNorm] at h
  push_cast
  have hreal : a * (a - b) - b * -b = 1 := by
    linear_combination h
  have heta : a * -b + b * (a - b) - b * -b = 0 := by ring
  have hrealO := congrArg (fun z : ℤ ↦ (z : 𝓞 K)) hreal
  have hetaO := congrArg (fun z : ℤ ↦ (z : 𝓞 K)) heta
  push_cast at hrealO hetaO
  rw [hrealO, hetaO]
  ring

private lemma eisenstein_prime_two_or_five (hζ : IsPrimitiveRoot ζ 3)
    (r : ℤ) (hr : r = 2 ∨ r = 5) :
    Prime (r : 𝓞 K) := by
  letI : IsPrincipalIdealRing (𝓞 K) :=
    IsCyclotomicExtension.Rat.three_pid K
  apply Irreducible.prime
  rw [irreducible_iff]
  constructor
  · intro hunit
    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hunit
    obtain ⟨c, d, hycoords⟩ := exists_eisenstein_integer_coords hζ y
    have hprod : (r : 𝓞 K) *
        ((c : 𝓞 K) + d * hζ.toInteger) = 1 := by
      rw [← hycoords]
      exact hy
    have hprod' :
        ((r : 𝓞 K) + (0 : ℤ) * hζ.toInteger) *
            ((c : 𝓞 K) + d * hζ.toInteger) =
          ((1 : ℤ) : 𝓞 K) + (0 : ℤ) * hζ.toInteger := by
      simpa using hprod
    rw [eisenstein_mul_coords hζ] at hprod'
    have hcoords := eisensteinEtaCoords_injective
      (a := r * c - 0 * d) (b := r * d + 0 * c - 0 * d)
      (c := 1) (d := 0) hζ (by
        simpa only [Int.cast_add, Int.cast_sub, Int.cast_mul,
          Int.cast_zero, Int.cast_one] using hprod')
    rcases hr with rfl | rfl <;> omega
  · intro x y hxy
    obtain ⟨a, b, hx⟩ := exists_eisenstein_integer_coords hζ x
    obtain ⟨c, d, hy⟩ := exists_eisenstein_integer_coords hζ y
    have hxy' :
        ((a : 𝓞 K) + b * hζ.toInteger) *
            ((c : 𝓞 K) + d * hζ.toInteger) = (r : 𝓞 K) := by
      rw [← hx, ← hy, ← hxy]
    rw [eisenstein_mul_coords hζ] at hxy'
    have hxy'' :
        ((a * c - b * d : ℤ) : 𝓞 K) +
            (a * d + b * c - b * d) * hζ.toInteger =
          (r : 𝓞 K) + (0 : ℤ) * hζ.toInteger := by
      simpa using hxy'
    have hcoords := eisensteinEtaCoords_injective
      (a := a * c - b * d) (b := a * d + b * c - b * d)
      (c := r) (d := 0) hζ (by
        simpa only [Int.cast_add, Int.cast_sub, Int.cast_mul,
          Int.cast_zero] using hxy'')
    have hnormprod : eisensteinCoordinateNorm a b * eisensteinCoordinateNorm c d = r ^ 2 := by
      rw [← eisensteinCoordinateNorm_mul]
      simp only [hcoords.1, hcoords.2, eisensteinCoordinateNorm]
      ring
    by_contra hnonunits
    simp only [not_or] at hnonunits
    have hab0 : ¬(a = 0 ∧ b = 0) := by
      rintro ⟨rfl, rfl⟩
      have hx0 : x = 0 := by
        simpa only [Int.cast_zero, zero_mul, add_zero] using hx
      rw [hx0, zero_mul] at hxy
      rcases hr with rfl | rfl <;> norm_num at hxy
    have hcd0 : ¬(c = 0 ∧ d = 0) := by
      rintro ⟨rfl, rfl⟩
      have hy0 : y = 0 := by
        simpa only [Int.cast_zero, zero_mul, add_zero] using hy
      rw [hy0, mul_zero] at hxy
      rcases hr with rfl | rfl <;> norm_num at hxy
    have hNabpos := eisensteinCoordinateNorm_pos hab0
    have hNcdpos := eisensteinCoordinateNorm_pos hcd0
    have hNabne1 : eisensteinCoordinateNorm a b ≠ 1 := fun h ↦
      hnonunits.1 (hx.symm ▸ isUnit_of_eisensteinCoordinateNorm_eq_one hζ h)
    have hNcdne1 : eisensteinCoordinateNorm c d ≠ 1 := fun h ↦
      hnonunits.2 (hy.symm ▸ isUnit_of_eisensteinCoordinateNorm_eq_one hζ h)
    have hNab2 : 2 ≤ eisensteinCoordinateNorm a b := by omega
    have hNcd2 : 2 ≤ eisensteinCoordinateNorm c d := by omega
    have hNabBound : eisensteinCoordinateNorm a b ≤ 12 := by
      rcases hr with rfl | rfl
      · nlinarith
      · nlinarith
    rcases hr with rfl | rfl
    · have hNab : eisensteinCoordinateNorm a b = 2 := by nlinarith
      exact (eisensteinCoordinateNorm_ne_two_or_five a b).1 hNab
    · have hNab : eisensteinCoordinateNorm a b = 5 := by
        interval_cases hN : eisensteinCoordinateNorm a b <;> omega
      exact (eisensteinCoordinateNorm_ne_two_or_five a b).2 hNab

/-- The rational prime `2` remains prime in the Eisenstein integers. -/
theorem eisenstein_two_prime (hζ : IsPrimitiveRoot ζ 3) :
    Prime (2 : 𝓞 K) := by
  simpa only [Int.cast_ofNat] using
    eisenstein_prime_two_or_five hζ (2 : ℤ) (Or.inl rfl)

/-- The rational prime `5` remains prime in the Eisenstein integers. -/
theorem eisenstein_five_prime (hζ : IsPrimitiveRoot ζ 3) :
    Prime (5 : 𝓞 K) := by
  simpa only [Int.cast_ofNat] using
    eisenstein_prime_two_or_five hζ (5 : ℤ) (Or.inr rfl)

/-- The element `√-3` generates the ramified prime over `3`. -/
theorem eisensteinSqrtNegThree_prime : Prime (eisensteinSqrtNegThree hζ) := by
  have hroot := hζ.toInteger_isPrimitiveRoot.isRoot_cyclotomic
    (by norm_num)
  rw [Polynomial.cyclotomic_three] at hroot
  norm_num [Polynomial.IsRoot] at hroot
  have hfactor : eisensteinSqrtNegThree hζ =
      (-hζ.toInteger) * (hζ.toInteger - 1) := by
    simp only [eisensteinSqrtNegThree]
    linear_combination hroot
  rw [hfactor]
  exact (prime_isUnit_mul
    (hζ.toInteger_isPrimitiveRoot.isUnit (by decide)).neg).mpr
      hζ.zeta_sub_one_prime'

omit [NumberField K] [IsCyclotomicExtension {3} ℚ K] in
/-- A prime common to the conjugate norm factors divides `2`, `√-3`, or
the constant `1500`. -/
theorem common_prime_support
    {U V : ℚ} (D : TargetEisensteinNormalizedIntegralData U V)
    (p : 𝓞 K) (hp : Prime p)
    (hminus : p ∣ D.toTargetEisensteinIntegralData.minusFactor hζ)
    (hplus : p ∣ D.toTargetEisensteinIntegralData.plusFactor hζ) :
    p ∣ (2 : 𝓞 K) ∨ p ∣ eisensteinSqrtNegThree hζ ∨
      p ∣ (1500 : 𝓞 K) := by
  have hsum : p ∣ (2 : 𝓞 K) * D.n := by
    have h := dvd_add hminus hplus
    change p ∣ ((D.n : 𝓞 K) - D.b * eisensteinSqrtNegThree hζ) +
      ((D.n : 𝓞 K) + D.b * eisensteinSqrtNegThree hζ) at h
    convert h using 1
    ring
  rcases hp.dvd_mul.mp hsum with hp2 | hpn
  · exact Or.inl hp2
  have hdifference : p ∣ (2 : 𝓞 K) * D.b * eisensteinSqrtNegThree hζ := by
    have h := dvd_sub hplus hminus
    change p ∣ ((D.n : 𝓞 K) + D.b * eisensteinSqrtNegThree hζ) -
      ((D.n : 𝓞 K) - D.b * eisensteinSqrtNegThree hζ) at h
    convert h using 1
    ring
  rcases hp.dvd_mul.mp hdifference with hptwoB | hpsqrt
  · rcases hp.dvd_mul.mp hptwoB with hp2 | hpb
    · exact Or.inl hp2
    · have hcop0 := D.n_coprime_d.map (Int.castRingHom (𝓞 K))
      change IsCoprime (D.n : 𝓞 K) (D.d : 𝓞 K) at hcop0
      have hcop : IsCoprime (D.n : 𝓞 K) (D.d : 𝓞 K) := hcop0
      rw [D.b_eq] at hpb
      push_cast at hpb
      rcases hp.dvd_mul.mp hpb with hpd | hpc
      · exact False.elim (hp.not_unit (hcop.isUnit_of_dvd' hpn hpd))
      · have hpm3 : p ∣ (D.m : 𝓞 K) ^ 3 := by
          rw [← D.toTargetEisensteinIntegralData.factors_mul hζ]
          exact hminus.mul_right _
        have hpm : p ∣ (D.m : 𝓞 K) := hp.dvd_of_dvd_pow hpm3
        have h1500d : p ∣ (1500 : 𝓞 K) * (D.d : 𝓞 K) ^ 2 := by
          have h12m : p ∣ (12 : 𝓞 K) * D.m := hpm.mul_left 12
          have h := dvd_sub hpc h12m
          convert h using 1
          ring
        rcases hp.dvd_mul.mp h1500d with h1500 | hd2
        · exact Or.inr (Or.inr h1500)
        · have hpd : p ∣ (D.d : 𝓞 K) := hp.dvd_of_dvd_pow hd2
          exact False.elim (hp.not_unit (hcop.isUnit_of_dvd' hpn hpd))
  · exact Or.inr (Or.inl hpsqrt)

/-- Every prime common to the conjugate factors is associated to one of the
three exceptional prime elements `2`, `√-3`, and `5`. -/
theorem common_prime_associated
    {U V : ℚ} (D : TargetEisensteinNormalizedIntegralData U V)
    (p : 𝓞 K) (hp : Prime p)
    (hminus : p ∣ D.toTargetEisensteinIntegralData.minusFactor hζ)
    (hplus : p ∣ D.toTargetEisensteinIntegralData.plusFactor hζ) :
    Associated p (2 : 𝓞 K) ∨
      Associated p (eisensteinSqrtNegThree hζ) ∨
      Associated p (5 : 𝓞 K) := by
  have hp2 : Prime (2 : 𝓞 K) := eisenstein_two_prime hζ
  have hp5 : Prime (5 : 𝓞 K) := eisenstein_five_prime hζ
  have hps : Prime (eisensteinSqrtNegThree hζ) := eisensteinSqrtNegThree_prime hζ
  rcases common_prime_support hζ D p hp hminus hplus with
    h2 | hs | h1500
  · exact Or.inl (hp.irreducible.associated_of_dvd hp2.irreducible h2)
  · exact Or.inr (Or.inl
      (hp.irreducible.associated_of_dvd hps.irreducible hs))
  · have hfactor : (1500 : 𝓞 K) =
        (2 : 𝓞 K) ^ 2 * (3 : 𝓞 K) * (5 : 𝓞 K) ^ 3 := by norm_num
    rw [hfactor] at h1500
    rcases hp.dvd_mul.mp h1500 with htwoThree | hfive
    · rcases hp.dvd_mul.mp htwoThree with htwo | hthree
      · have h2 : p ∣ (2 : 𝓞 K) := hp.dvd_of_dvd_pow htwo
        exact Or.inl (hp.irreducible.associated_of_dvd hp2.irreducible h2)
      · have hthree' : p ∣ eisensteinSqrtNegThree hζ ^ 2 := by
          have hsquare : eisensteinSqrtNegThree hζ ^ 2 = (-3 : 𝓞 K) := by
            have hroot := hζ.toInteger_isPrimitiveRoot.isRoot_cyclotomic
              (by norm_num)
            rw [Polynomial.cyclotomic_three] at hroot
            norm_num [Polynomial.IsRoot] at hroot
            simp only [eisensteinSqrtNegThree]
            linear_combination 4 * hroot
          rw [hsquare]
          exact hthree.neg_right
        have hs : p ∣ eisensteinSqrtNegThree hζ :=
          hp.dvd_of_dvd_pow hthree'
        exact Or.inr (Or.inl
          (hp.irreducible.associated_of_dvd hps.irreducible hs))
    · have h5 : p ∣ (5 : 𝓞 K) := hp.dvd_of_dvd_pow hfive
      exact Or.inr (Or.inr
        (hp.irreducible.associated_of_dvd hp5.irreducible h5))

private def EisensteinConjugate (x y : 𝓞 K) : Prop :=
  ∃ a b : ℤ,
    x = (a : 𝓞 K) + b * hζ.toInteger ∧
    y = ((a - b : ℤ) : 𝓞 K) + (-b : ℤ) * hζ.toInteger

omit [IsCyclotomicExtension {3} ℚ K] in
private lemma EisensteinConjugate.right_unique {x y z : 𝓞 K}
    (hxy : EisensteinConjugate hζ x y) (hxz : EisensteinConjugate hζ x z) :
    y = z := by
  obtain ⟨a, b, hxab, hyab⟩ := hxy
  obtain ⟨c, d, hxcd, hzcd⟩ := hxz
  have hcoords := eisensteinEtaCoords_injective hζ (hxab.symm.trans hxcd)
  rcases hcoords with ⟨rfl, rfl⟩
  rw [hyab, hzcd]

omit [NumberField K] [IsCyclotomicExtension {3} ℚ K] in
private lemma EisensteinConjugate.symm {x y : 𝓞 K}
    (hxy : EisensteinConjugate hζ x y) :
    EisensteinConjugate hζ y x := by
  obtain ⟨a, b, rfl, rfl⟩ := hxy
  refine ⟨a - b, -b, ?_, ?_⟩
  · rfl
  · push_cast
    ring

omit [NumberField K] [IsCyclotomicExtension {3} ℚ K] in
private lemma EisensteinConjugate.mul {x₁ y₁ x₂ y₂ : 𝓞 K}
    (h₁ : EisensteinConjugate hζ x₁ y₁) (h₂ : EisensteinConjugate hζ x₂ y₂) :
    EisensteinConjugate hζ (x₁ * x₂) (y₁ * y₂) := by
  obtain ⟨a, b, rfl, rfl⟩ := h₁
  obtain ⟨c, d, rfl, rfl⟩ := h₂
  refine ⟨a * c - b * d, a * d + b * c - b * d, ?_, ?_⟩
  · simpa only [Int.cast_add, Int.cast_sub, Int.cast_mul] using
      eisenstein_mul_coords hζ a b c d
  · rw [eisenstein_mul_coords hζ]
    push_cast
    ring

omit [NumberField K] [IsCyclotomicExtension {3} ℚ K] in
private lemma EisensteinConjugate.one :
    EisensteinConjugate hζ (1 : 𝓞 K) 1 := by
  refine ⟨1, 0, ?_, ?_⟩ <;> push_cast <;> ring

omit [NumberField K] [IsCyclotomicExtension {3} ℚ K] in
private lemma EisensteinConjugate.pow {x y : 𝓞 K}
    (hxy : EisensteinConjugate hζ x y)
    (k : ℕ) : EisensteinConjugate hζ (x ^ k) (y ^ k) := by
  induction k with
  | zero => simpa using EisensteinConjugate.one hζ
  | succ k ih => simpa [pow_succ] using ih.mul hζ hxy

private lemma exists_eisensteinConjugate (x : 𝓞 K) :
    ∃ y, EisensteinConjugate hζ x y := by
  obtain ⟨a, b, rfl⟩ := exists_eisenstein_integer_coords hζ x
  exact ⟨_, a, b, rfl, rfl⟩

private lemma EisensteinConjugate.pow_dvd_iff {q q' x y : 𝓞 K}
    (hq : EisensteinConjugate hζ q q') (hxy : EisensteinConjugate hζ x y) (k : ℕ) :
    q ^ k ∣ x ↔ q' ^ k ∣ y := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨z', hzz'⟩ := exists_eisensteinConjugate hζ z
    have hprod := (hq.pow hζ k).mul hζ hzz'
    refine ⟨z', ?_⟩
    apply hxy.right_unique hζ
    rw [hz]
    exact hprod
  · rintro ⟨z, hz⟩
    obtain ⟨z', hzz'⟩ := exists_eisensteinConjugate hζ z
    have hprod := ((hq.symm hζ).pow hζ k).mul hζ hzz'
    refine ⟨z', ?_⟩
    apply (hxy.symm hζ).right_unique hζ
    rw [hz]
    exact hprod

omit [NumberField K] [IsCyclotomicExtension {3} ℚ K] in
private lemma eisensteinConjugate_intCast (r : ℤ) :
    EisensteinConjugate hζ (r : 𝓞 K) (r : 𝓞 K) := by
  refine ⟨r, 0, ?_, ?_⟩ <;> push_cast <;> ring

omit [NumberField K] [IsCyclotomicExtension {3} ℚ K] in
private lemma eisensteinSqrtNegThree_conjugate :
    EisensteinConjugate hζ (eisensteinSqrtNegThree hζ)
      (-eisensteinSqrtNegThree hζ) := by
  refine ⟨1, 2, ?_, ?_⟩ <;>
    simp only [eisensteinSqrtNegThree] <;> push_cast <;> ring

omit [NumberField K] [IsCyclotomicExtension {3} ℚ K] in
private lemma factors_conjugate {U V : ℚ}
    (D : TargetEisensteinIntegralData U V) :
    EisensteinConjugate hζ (D.minusFactor hζ) (D.plusFactor hζ) := by
  refine ⟨D.n - D.b, -2 * D.b, D.minusFactor_coords hζ, ?_⟩
  rw [D.plusFactor_coords hζ]
  push_cast
  ring

omit [NumberField K] [IsCyclotomicExtension {3} ℚ K] in
private lemma exists_associated_cube_of_factor_counts
    [NormalizationMonoid (𝓞 K)] [UniqueFactorizationMonoid (𝓞 K)]
    [DecidableEq (𝓞 K)]
    {x : 𝓞 K} (hx : x ≠ 0)
    (hcount : ∀ p : 𝓞 K, 3 ∣ (normalizedFactors x).count p) :
    ∃ z : 𝓞 K, Associated (z ^ 3) x := by
  classical
  let f : 𝓞 K → 𝓞 K := fun p ↦
    p ^ ((normalizedFactors x).count p / 3)
  have hf : f.HasFiniteMulSupport := by
    apply (normalizedFactors x).toFinset.finite_toSet.subset
    intro p hp
    have hcount0 : (normalizedFactors x).count p ≠ 0 := by
      intro hzero
      apply hp
      change p ^ ((normalizedFactors x).count p / 3) = 1
      rw [hzero]
      norm_num
    exact Multiset.mem_toFinset.mpr (Multiset.count_pos.mp (Nat.pos_of_ne_zero hcount0))
  refine ⟨∏ᶠ p, f p, ?_⟩
  have hcube : (∏ᶠ p, f p) ^ 3 =
      ∏ᶠ p : 𝓞 K, p ^ (normalizedFactors x).count p := by
    rw [finprod_pow hf]
    apply finprod_congr
    intro p
    simp only [f, ← pow_mul]
    rw [Nat.div_mul_cancel (hcount p)]
  rw [hcube]
  exact associated_finprod_pow_count hx

private lemma TargetEisensteinNormalizedIntegralData.m_ne_zero
    {U V : ℚ} (D : TargetEisensteinNormalizedIntegralData U V) :
    D.m ≠ 0 := by
  intro hm
  have hb : D.b ≠ 0 := by
    rw [D.b_eq, hm]
    norm_num
    exact D.d_ne_zero
  have hnorm := D.norm_eq
  rw [hm] at hnorm
  nlinarith [sq_nonneg D.n, sq_pos_of_ne_zero hb]

/-- Every normalized irreducible factor of the negative Eisenstein factor has
multiplicity divisible by three. -/
theorem minusFactor_count_dvd_three
    [NormalizationMonoid (𝓞 K)] [UniqueFactorizationMonoid (𝓞 K)]
    [DecidableEq (𝓞 K)]
    {U V : ℚ} (D : TargetEisensteinNormalizedIntegralData U V)
    (p : 𝓞 K) :
    3 ∣ (normalizedFactors
      (D.toTargetEisensteinIntegralData.minusFactor hζ)).count p := by
  classical
  let x := D.toTargetEisensteinIntegralData.minusFactor hζ
  let y := D.toTargetEisensteinIntegralData.plusFactor hζ
  let M : 𝓞 K := (D.m : 𝓞 K)
  have hmZ : D.m ≠ 0 := D.m_ne_zero
  have hm : M ≠ 0 := by
    dsimp only [M]
    exact_mod_cast hmZ
  have hmul : x * y = M ^ 3 := by
    simpa only [x, y, M] using
      D.toTargetEisensteinIntegralData.factors_mul hζ
  have hx : x ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hmul
    exact (pow_ne_zero 3 hm) hmul.symm
  have hy : y ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmul
    exact (pow_ne_zero 3 hm) hmul.symm
  have hfac : factorization x + factorization y =
      3 • factorization M := by
    rw [← factorization_mul hx hy, hmul, factorization_pow]
  have hcountEq := DFunLike.congr_fun hfac p
  simp only [Finsupp.add_apply, factorization_eq_count,
    Finsupp.smul_apply, smul_eq_mul] at hcountEq
  by_cases hpx : p ∈ normalizedFactors x
  · have hp : Prime p := prime_of_normalized_factor p hpx
    have hpdivx : p ∣ x := dvd_of_mem_normalizedFactors hpx
    by_cases hpdivy : p ∣ y
    · have hassoc := common_prime_associated hζ D p hp hpdivx hpdivy
      have hxyconj : EisensteinConjugate hζ x y := by
        simpa only [x, y] using
          factors_conjugate hζ D.toTargetEisensteinIntegralData
      have hcountSame : (normalizedFactors x).count p =
          (normalizedFactors y).count p := by
        have hnorm : normalize p = p := normalize_normalized_factor p hpx
        have hemp : emultiplicity p x = emultiplicity p y := by
          rcases hassoc with hp2 | hps | hp5
          · calc
              emultiplicity p x = emultiplicity (2 : 𝓞 K) x :=
                (emultiplicity_eq_of_associated_left hp2).symm
              _ = emultiplicity (2 : 𝓞 K) y :=
                emultiplicity_eq_emultiplicity_iff.mpr fun k ↦
                  (by simpa only [Int.cast_ofNat] using
                    (eisensteinConjugate_intCast hζ 2).pow_dvd_iff hζ hxyconj k)
              _ = emultiplicity p y :=
                emultiplicity_eq_of_associated_left hp2
          · calc
              emultiplicity p x =
                  emultiplicity (eisensteinSqrtNegThree hζ) x :=
                (emultiplicity_eq_of_associated_left hps).symm
              _ = emultiplicity (-eisensteinSqrtNegThree hζ) y :=
                emultiplicity_eq_emultiplicity_iff.mpr fun k ↦
                  (eisensteinSqrtNegThree_conjugate hζ).pow_dvd_iff hζ hxyconj k
              _ = emultiplicity (eisensteinSqrtNegThree hζ) y :=
                emultiplicity_eq_of_associated_left Associated.rfl.neg_right
              _ = emultiplicity p y :=
                emultiplicity_eq_of_associated_left hps
          · calc
              emultiplicity p x = emultiplicity (5 : 𝓞 K) x :=
                (emultiplicity_eq_of_associated_left hp5).symm
              _ = emultiplicity (5 : 𝓞 K) y :=
                emultiplicity_eq_emultiplicity_iff.mpr fun k ↦
                  (by simpa only [Int.cast_ofNat] using
                    (eisensteinConjugate_intCast hζ 5).pow_dvd_iff hζ hxyconj k)
              _ = emultiplicity p y :=
                emultiplicity_eq_of_associated_left hp5
        have hmult : multiplicity p x = multiplicity p y :=
          multiplicity_eq_of_emultiplicity_eq hemp
        have hmx' := multiplicity_eq_count_normalizedFactors hp.irreducible hx
        have hmy' := multiplicity_eq_count_normalizedFactors hp.irreducible hy
        calc
          (normalizedFactors x).count p = multiplicity p x := by
            rw [hmx', hnorm]
          _ = multiplicity p y := hmult
          _ = (normalizedFactors y).count p := by rw [hmy', hnorm]
      rw [hcountSame] at hcountEq
      have hthree : 3 ∣ 2 * (normalizedFactors x).count p := by
        refine ⟨(normalizedFactors M).count p, ?_⟩
        omega
      exact Nat.Coprime.dvd_of_dvd_mul_left (by decide) hthree
    · have hpynmem : p ∉ normalizedFactors y := fun hpy ↦
        hpdivy (dvd_of_mem_normalizedFactors hpy)
      have hcounty : (normalizedFactors y).count p = 0 :=
        Multiset.count_eq_zero.mpr hpynmem
      rw [hcounty, add_zero] at hcountEq
      exact ⟨(normalizedFactors M).count p, hcountEq⟩
  · rw [Multiset.count_eq_zero.mpr hpx]
    exact dvd_zero 3

/-- The negative Eisenstein norm factor of normalized target data is
associated to a cube. -/
theorem exists_associated_cube
    {U V : ℚ} (D : TargetEisensteinNormalizedIntegralData U V) :
    ∃ z : 𝓞 K, Associated (z ^ 3)
      (D.toTargetEisensteinIntegralData.minusFactor hζ) := by
  classical
  letI : IsPrincipalIdealRing (𝓞 K) :=
    IsCyclotomicExtension.Rat.three_pid K
  letI : StrongNormalizationMonoid (𝓞 K) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let x := D.toTargetEisensteinIntegralData.minusFactor hζ
  have hmZ : D.m ≠ 0 := D.m_ne_zero
  have hm : (D.m : 𝓞 K) ≠ 0 := by exact_mod_cast hmZ
  have hx : x ≠ 0 := by
    intro hzero
    have hmul := D.toTargetEisensteinIntegralData.factors_mul hζ
    change x * D.toTargetEisensteinIntegralData.plusFactor hζ =
      (D.m : 𝓞 K) ^ 3 at hmul
    rw [hzero, zero_mul] at hmul
    exact (pow_ne_zero 3 hm) hmul.symm
  apply exists_associated_cube_of_factor_counts hx
  intro p
  simpa only [x] using minusFactor_count_dvd_three hζ D p

/-- The ideal-support contract required by the order-35 Eisenstein descent. -/
theorem targetEisensteinAssociatedCube : TargetEisensteinAssociatedCube := by
  intro K _ _ _ ζ hζ X Y hP
  obtain ⟨D⟩ := targetEisensteinNormalizedIntegralData hP
  obtain ⟨z, hz⟩ := exists_associated_cube hζ D
  exact ⟨D, z, hz⟩

/-- The explicit optimal quotient used at level `35` has Mordell--Weil rank
zero, with no remaining arithmetic hypothesis. -/
theorem optimalQuotientModel_rank_zero :
    Module.finrank ℤ optimalQuotientModel.toAffine.Point = 0 :=
  optimalQuotientModel_rank_zero_of_associatedCube targetEisensteinAssociatedCube

/-- The rational point group of the fixed explicit level-`35` model is finite,
with no remaining arithmetic hypothesis.  Identifying this model with the
required modular quotient is a separate geometric step. -/
theorem optimalQuotientModel_finite :
    Finite optimalQuotientModel.toAffine.Point :=
  optimalQuotientModel_finite_of_associatedCube targetEisensteinAssociatedCube

end MazurTorsion.OrderThirtyFive

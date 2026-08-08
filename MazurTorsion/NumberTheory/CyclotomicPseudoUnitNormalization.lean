/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.CyclotomicPseudoUnitReciprocity

/-!
# Coprime integral representatives of cyclotomic pseudo-units

This file proves the denominator-dependent normalization step used in a
one-sided Kummer reciprocity argument.  Its ideal-theoretic input is the
standard Dedekind-domain fact that an ideal class has an integral
representative coprime to any prescribed nonzero proper ideal.

The proof is internal to Mathlib's Dedekind-domain API.  If `J` is an
integral representative of the inverse class and `F` is the prescribed
ideal, `IsDedekindDomain.exists_sup_span_eq` supplies `x` with
`J * F + (x) = J`.  Cancelling `J` shows that `(x) * J⁻¹` is both
integral and coprime to `F`.
-/

open scoped NumberField nonZeroDivisors

namespace FractionalIdeal

universe u v

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
variable {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]

/-- A nonzero fractional ideal can be rescaled by a field unit to an
integral ideal coprime to any prescribed nonzero proper ideal. -/
theorem exists_integral_coprime_principal_multiple
    (A : (FractionalIdeal R⁰ K)ˣ) (F : Ideal R)
    (hF_ne : F ≠ ⊥) (hF_proper : F ≠ ⊤) :
    ∃ (c : Kˣ) (B : Ideal R) (hB : B ≠ ⊥),
      toPrincipalIdeal R K c * A =
          FractionalIdeal.mk0 K
            ⟨B, mem_nonZeroDivisors_iff_ne_zero.mpr hB⟩ ∧
        IsCoprime B F := by
  obtain ⟨a, J, ha, hAinv⟩ :=
    FractionalIdeal.exists_eq_spanSingleton_mul
      ((A⁻¹ : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K)
  have hAinv_ne :
      ((A⁻¹ : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) ≠ 0 :=
    Units.ne_zero _
  have hJ : J ≠ ⊥ :=
    FractionalIdeal.ideal_factor_ne_zero hAinv_ne hAinv
  have hJF : J * F ≠ ⊥ := mul_ne_zero hJ hF_ne
  obtain ⟨x, hx⟩ := IsDedekindDomain.exists_sup_span_eq
    (I := J * F) (J := J) Ideal.mul_le_right hJF
  have hx_ne : x ≠ 0 := by
    intro hx_zero
    subst x
    have hx' : J * F = J := by
      simpa only [Ideal.span_singleton_zero, sup_bot_eq] using hx
    have hF_one : F = 1 := by
      apply mul_left_cancel₀ hJ
      simpa only [mul_one] using hx'
    exact hF_proper (by simpa only [Ideal.one_eq_top] using hF_one)
  let T : FractionalIdeal R⁰ K :=
    (Ideal.span {x} : Ideal R) * (J : FractionalIdeal R⁰ K)⁻¹
  have hJ_fractional : (J : FractionalIdeal R⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hJ
  have hx_le : Ideal.span {x} ≤ J := le_sup_right.trans_eq hx
  have hT_le : T ≤ 1 := by
    rw [show (1 : FractionalIdeal R⁰ K) =
        (J : FractionalIdeal R⁰ K) * (J : FractionalIdeal R⁰ K)⁻¹ by
      exact (mul_inv_cancel₀ hJ_fractional).symm]
    exact mul_le_mul_of_nonneg_right
      ((FractionalIdeal.coeIdeal_le_coeIdeal K).mpr hx_le) bot_le
  obtain ⟨B, hB⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hT_le
  have hT_ne : T ≠ 0 := by
    apply mul_ne_zero
    · exact FractionalIdeal.coeIdeal_ne_zero.mpr
        (Ideal.span_singleton_eq_bot.not.mpr hx_ne)
    · exact inv_ne_zero hJ_fractional
  have hB_ne : B ≠ ⊥ := by
    have hB_fractional : (B : FractionalIdeal R⁰ K) ≠ 0 := by
      rw [hB]
      exact hT_ne
    exact (FractionalIdeal.coeIdeal_ne_zero (K := K)).mp hB_fractional
  have hBJ : B * J = Ideal.span {x} := by
    apply FractionalIdeal.coeIdeal_injective (K := K)
    change ((B * J : Ideal R) : FractionalIdeal R⁰ K) =
      ((Ideal.span {x} : Ideal R) : FractionalIdeal R⁰ K)
    rw [FractionalIdeal.coeIdeal_mul, hB]
    change
      ((Ideal.span {x} : Ideal R) : FractionalIdeal R⁰ K) *
          (J : FractionalIdeal R⁰ K)⁻¹ *
          (J : FractionalIdeal R⁰ K) =
        ((Ideal.span {x} : Ideal R) : FractionalIdeal R⁰ K)
    rw [mul_assoc, inv_mul_cancel₀ hJ_fractional, mul_one]
  have hcoprime : IsCoprime B F := by
    rw [Ideal.isCoprime_iff_add]
    have hcancel : J * (B + F) = J * 1 := by
      rw [mul_add, mul_one, mul_comm J B, hBJ]
      simpa only [Ideal.add_eq_sup, sup_comm] using hx
    exact mul_left_cancel₀ hJ hcancel
  have ha_map : algebraMap R K a ≠ 0 :=
    by simpa only [map_zero] using (IsFractionRing.injective R K).ne ha
  have hx_map : algebraMap R K x ≠ 0 :=
    by simpa only [map_zero] using (IsFractionRing.injective R K).ne hx_ne
  let c : Kˣ := Units.mk0
    (algebraMap R K x / algebraMap R K a)
    (div_ne_zero hx_map ha_map)
  have hA : (A : FractionalIdeal R⁰ K) =
      FractionalIdeal.spanSingleton R⁰ (algebraMap R K a) *
        (J : FractionalIdeal R⁰ K)⁻¹ := by
    calc
      (A : FractionalIdeal R⁰ K) =
          (((A⁻¹ : (FractionalIdeal R⁰ K)ˣ) :
            FractionalIdeal R⁰ K))⁻¹ := by simp
      _ = (FractionalIdeal.spanSingleton R⁰
            (algebraMap R K a)⁻¹ *
          (J : FractionalIdeal R⁰ K))⁻¹ := by rw [hAinv]
      _ = FractionalIdeal.spanSingleton R⁰ (algebraMap R K a) *
          (J : FractionalIdeal R⁰ K)⁻¹ := by
        rw [mul_inv, FractionalIdeal.spanSingleton_inv, inv_inv,
          mul_comm]
  refine ⟨c, B, hB_ne, ?_, hcoprime⟩
  apply Units.ext
  rw [FractionalIdeal.coe_mk0, Units.val_mul, coe_toPrincipalIdeal,
    hA, hB]
  change FractionalIdeal.spanSingleton R⁰
        (algebraMap R K x / algebraMap R K a) *
      (FractionalIdeal.spanSingleton R⁰ (algebraMap R K a) *
        (J : FractionalIdeal R⁰ K)⁻¹) = T
  rw [← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton,
    div_mul_cancel₀ _ ha_map]
  unfold T
  rw [FractionalIdeal.coeIdeal_span_singleton]

end FractionalIdeal

namespace NumberTheory.CyclotomicCharacter.InverseExtension

universe u

variable {p : ℕ} [Fact p.Prime]
variable {L : Type u} [Field L] [NumberField L]
variable [Algebra (PrimeCyclotomicField p) L]
variable [IsScalarTower ℚ (PrimeCyclotomicField p) L]

/-- A pseudo-unit radicand can be changed by a `p`-th power so that it is
integral and its principal ideal is simultaneously coprime to a prescribed
nonzero denominator ideal and to the cyclotomic prime. -/
theorem exists_coprime_integral_pseudoUnit_normalization
    (E : InverseExtension p L)
    (hdiv : ∀ v : FinitePrime (PrimeCyclotomicField p),
      (p : ℤ) ∣ FractionalIdeal.count (PrimeCyclotomicField p) v
        (FractionalIdeal.spanSingleton
          (nonZeroDivisors
            (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
          E.kummerPresentation.radicand))
    (I : Ideal
      (NumberField.RingOfIntegers (PrimeCyclotomicField p)))
    (hI : I ≠ ⊥) :
    ∃ (c : (PrimeCyclotomicField p)ˣ)
        (η : NumberField.RingOfIntegers (PrimeCyclotomicField p))
        (B : Ideal
          (NumberField.RingOfIntegers (PrimeCyclotomicField p))),
      η ≠ 0 ∧
      algebraMap
          (NumberField.RingOfIntegers (PrimeCyclotomicField p))
          (PrimeCyclotomicField p) η =
        E.kummerPresentation.radicand *
          (c : PrimeCyclotomicField p) ^ p ∧
      Ideal.span {η} = B ^ p ∧
      IsCoprime (Ideal.span {η}) I ∧
      IsCoprime (Ideal.span {η}) (cyclotomicPrime p).asIdeal := by
  let R := NumberField.RingOfIntegers (PrimeCyclotomicField p)
  let K := PrimeCyclotomicField p
  let v := cyclotomicPrime p
  let F : Ideal R := I * v.asIdeal
  have hF_ne : F ≠ ⊥ := by
    exact mul_ne_zero hI v.ne_bot
  have hF_proper : F ≠ ⊤ := by
    intro hF
    apply v.isPrime.ne_top
    apply top_unique
    rw [← hF]
    exact Ideal.mul_le_left
  obtain ⟨c, B, hB, hcB, hcoprime⟩ :=
    FractionalIdeal.exists_integral_coprime_principal_multiple
      E.unramifiedRadicandRootIdeal F hF_ne hF_proper
  let a : Kˣ := Units.mk0 E.kummerPresentation.radicand
    (E.kummerPresentation.radicand_ne_zero E)
  let B₀ : (Ideal R)⁰ :=
    ⟨B, mem_nonZeroDivisors_iff_ne_zero.mpr hB⟩
  have hroot : E.unramifiedRadicandRootIdeal ^ p =
      toPrincipalIdeal R K a :=
    E.unramifiedRadicandRootIdeal_pow_eq_of_dvd_counts hdiv
  have hpowUnits :
      toPrincipalIdeal R K (c ^ p * a) =
        FractionalIdeal.mk0 K (B₀ ^ p) := by
    calc
      toPrincipalIdeal R K (c ^ p * a) =
          (toPrincipalIdeal R K c) ^ p *
            toPrincipalIdeal R K a := by
        rw [map_mul, map_pow]
      _ = (toPrincipalIdeal R K c) ^ p *
          E.unramifiedRadicandRootIdeal ^ p := by rw [hroot]
      _ = (toPrincipalIdeal R K c *
          E.unramifiedRadicandRootIdeal) ^ p := by rw [mul_pow]
      _ = (FractionalIdeal.mk0 K B₀) ^ p := by rw [hcB]
      _ = FractionalIdeal.mk0 K (B₀ ^ p) :=
        (map_pow (FractionalIdeal.mk0 K) B₀ p).symm
  have hspan :
      FractionalIdeal.spanSingleton R⁰
          ((c : K) ^ p * E.kummerPresentation.radicand) =
        ((B ^ p : Ideal R) : FractionalIdeal R⁰ K) := by
    have hpowValues := congrArg Units.val hpowUnits
    simp only [coe_toPrincipalIdeal, Units.val_mul,
      Units.val_pow_eq_pow_val, Units.val_mk0,
      FractionalIdeal.coe_mk0, a] at hpowValues
    change FractionalIdeal.spanSingleton R⁰
        ((c : K) ^ p * E.kummerPresentation.radicand) =
      ((B ^ p : Ideal R) : FractionalIdeal R⁰ K) at hpowValues
    exact hpowValues
  have hnormalized_mem :
      E.kummerPresentation.radicand * (c : K) ^ p ∈
        (1 : FractionalIdeal R⁰ K) := by
    rw [← FractionalIdeal.spanSingleton_le_iff_mem]
    rw [mul_comm, hspan]
    exact FractionalIdeal.coeIdeal_le_one
  obtain ⟨η, hη⟩ :=
    (FractionalIdeal.mem_one_iff R⁰).mp hnormalized_mem
  have hnormalized_ne :
      E.kummerPresentation.radicand * (c : K) ^ p ≠ 0 :=
    mul_ne_zero (E.kummerPresentation.radicand_ne_zero E)
      (pow_ne_zero p (Units.ne_zero c))
  have hη_ne : η ≠ 0 := by
    intro hη_zero
    subst η
    apply hnormalized_ne
    simpa only [map_zero] using hη.symm
  have hη_span : Ideal.span {η} = B ^ p := by
    apply FractionalIdeal.coeIdeal_injective (K := K)
    change
      ((Ideal.span {η} : Ideal R) : FractionalIdeal R⁰ K) =
        ((B ^ p : Ideal R) : FractionalIdeal R⁰ K)
    rw [FractionalIdeal.coeIdeal_span_singleton, hη]
    simpa only [mul_comm] using hspan
  have hpow_coprime : IsCoprime (B ^ p) (I * v.asIdeal) := by
    change IsCoprime (B ^ p) F
    exact hcoprime.pow_left
  refine ⟨c, η, B, hη_ne, hη, hη_span, ?_, ?_⟩
  · rw [hη_span]
    exact hpow_coprime.of_mul_right_left
  · rw [hη_span]
    exact hpow_coprime.of_mul_right_right

end NumberTheory.CyclotomicCharacter.InverseExtension

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import MazurTorsion.NumberTheory.CyclotomicUnramified

/-!
# Finite congruences from local cyclotomic primary data

This file converts a power in an adic completion into congruences of global
integers.  The approximation statement is stronger than the depth needed in
the cyclotomic application: if an integral element is a `q`-th power in the
completion at `v`, then it is congruent to a `q`-th power modulo every power
of `v`.

For the cyclotomic prime, depth `p + 1` gives the finite hyperprimary
condition used in one-sided Kummer reciprocity.
-/

open scoped NumberField nonZeroDivisors

namespace NumberTheory.CyclotomicCharacter.InverseExtension

universe u

variable {p : ℕ} [Fact p.Prime]

/-- A global integer can approximate an integral element of an adic
completion to any nonzero valuation threshold at most one. -/
private theorem exists_integer_valuation_sub_lt_adic
    {K : Type u} [Field K] [NumberField K]
    (v : FinitePrime K)
    (y : v.adicCompletion K)
    (hy : Valued.v y ≤ 1)
    (γ : (WithZero (Multiplicative ℤ))ˣ)
    (hγ : (γ : WithZero (Multiplicative ℤ)) ≤ 1) :
    ∃ b : NumberField.RingOfIntegers K,
      Valued.v
        (algebraMap (NumberField.RingOfIntegers K)
            (v.adicCompletion K) b - y) <
        (γ : WithZero (Multiplicative ℤ)) := by
  let e : NNReal := Ideal.absNorm v.asIdeal
  have he : 1 < e := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
  let ε : ℝ := WithZeroMulInt.toNNReal (ne_zero_of_lt he)
    (γ : WithZero (Multiplicative ℤ))
  have hγzero : (γ : WithZero (Multiplicative ℤ)) ≠ 0 :=
    Units.ne_zero γ
  have hε : 0 < ε := by
    exact_mod_cast WithZeroMulInt.toNNReal_pos (ne_zero_of_lt he) hγzero
  obtain ⟨x, hx⟩ :=
    (v.denseRange_algebraMap K).exists_dist_lt y hε
  have hxval :
      Valued.v (algebraMap K (v.adicCompletion K) x - y) <
        (γ : WithZero (Multiplicative ℤ)) := by
    have hxnorm :
        ‖algebraMap K (v.adicCompletion K) x - y‖ < ε := by
      have hx' : dist (algebraMap K (v.adicCompletion K) x) y < ε := by
        simpa only [dist_comm] using hx
      simpa only [dist_eq_norm] using hx'
    rw [NumberField.FinitePlace.norm_def v] at hxnorm
    exact_mod_cast
      (WithZeroMulInt.toNNReal_strictMono he).lt_iff_lt.mp hxnorm
  have hxleC : Valued.v (algebraMap K (v.adicCompletion K) x) ≤ 1 := by
    rw [show algebraMap K (v.adicCompletion K) x =
        (algebraMap K (v.adicCompletion K) x - y) + y by ring]
    exact Valued.v.map_add_le (hxval.le.trans hγ) hy
  have hxle : v.valuation K x ≤ 1 := by
    change Valued.v (x : v.adicCompletion K) ≤ 1 at hxleC
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      at hxleC
    exact hxleC
  obtain ⟨b, hb⟩ := v.exists_valuation_sub_lt_of_integer hxle γ
  refine ⟨b, ?_⟩
  have hbC :
      Valued.v
          (algebraMap K (v.adicCompletion K)
            (algebraMap (NumberField.RingOfIntegers K) K b - x)) <
        (γ : WithZero (Multiplicative ℤ)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
    simp only [Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'
      v (algebraMap (NumberField.RingOfIntegers K) K b - x)]
    exact hb
  rw [IsScalarTower.algebraMap_apply
    (NumberField.RingOfIntegers K) K (v.adicCompletion K)]
  rw [show
      algebraMap K (v.adicCompletion K)
          (algebraMap (NumberField.RingOfIntegers K) K b) - y =
        algebraMap K (v.adicCompletion K)
            (algebraMap (NumberField.RingOfIntegers K) K b - x) +
          (algebraMap K (v.adicCompletion K) x - y) by
      rw [map_sub]
      ring]
  exact Valued.v.map_add_lt hbC hxval

/-- If an integral element is a nontrivial power in the completion at `v`,
then it is congruent to the same power of a global integer modulo every
prescribed power of `v`. -/
theorem exists_integral_pow_congr_mod_prime_pow_of_adic_pow
    {K : Type u} [Field K] [NumberField K]
    (v : FinitePrime K)
    (q n : ℕ)
    (hq : q ≠ 0)
    (η : NumberField.RingOfIntegers K)
    (hroot : ∃ y : v.adicCompletion K,
      y ^ q = algebraMap (NumberField.RingOfIntegers K)
        (v.adicCompletion K) η) :
    ∃ b : NumberField.RingOfIntegers K,
      η - b ^ q ∈ v.asIdeal ^ n := by
  let γ : (WithZero (Multiplicative ℤ))ˣ :=
    Units.mk0 (WithZero.exp (-(n : ℤ))) (by simp)
  have hγ : (γ : WithZero (Multiplicative ℤ)) =
      WithZero.exp (-(n : ℤ)) := rfl
  have hγle : (γ : WithZero (Multiplicative ℤ)) ≤ 1 := by
    rw [hγ, ← WithZero.exp_zero, WithZero.exp_le_exp]
    simp
  obtain ⟨y, hy⟩ := hroot
  have hηle :
      Valued.v
          (algebraMap (NumberField.RingOfIntegers K)
            (v.adicCompletion K) η) ≤ 1 := by
    rw [IsScalarTower.algebraMap_apply
      (NumberField.RingOfIntegers K) K (v.adicCompletion K)]
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
    simp only [Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact v.intValuation_le_one η
  have hyle : Valued.v y ≤ 1 := by
    apply (pow_le_one_iff_of_nonneg bot_le hq).mp
    rw [← Valuation.map_pow, hy]
    exact hηle
  obtain ⟨b, hby⟩ :=
    exists_integer_valuation_sub_lt_adic v y hyle γ hγle
  let bC : v.adicCompletion K :=
    algebraMap (NumberField.RingOfIntegers K) (v.adicCompletion K) b
  have hbCle : Valued.v bC ≤ 1 := by
    dsimp only [bC]
    rw [IsScalarTower.algebraMap_apply
      (NumberField.RingOfIntegers K) K (v.adicCompletion K)]
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion]
    simp only [Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact v.intValuation_le_one b
  have hyb : Valued.v (y - bC) < (γ : WithZero (Multiplicative ℤ)) := by
    rw [Valuation.map_sub_swap]
    exact hby
  let s : v.adicCompletion K :=
    ∑ i ∈ Finset.range q, y ^ i * bC ^ (q - 1 - i)
  have hsle : Valued.v s ≤ 1 := by
    dsimp only [s]
    apply Valued.v.map_sum_le
    intro i _
    rw [Valuation.map_mul, Valuation.map_pow, Valuation.map_pow]
    exact mul_le_one₀ (pow_le_one₀ bot_le hyle) bot_le
      (pow_le_one₀ bot_le hbCle)
  have hpow : Valued.v (y ^ q - bC ^ q) <
      (γ : WithZero (Multiplicative ℤ)) := by
    rw [← (Commute.all y bC).mul_geom_sum₂ q]
    rw [Valuation.map_mul]
    calc
      Valued.v (y - bC) * Valued.v s ≤
          Valued.v (y - bC) * 1 := by
            simpa only [mul_comm] using
              (mul_le_mul_left hsle (Valued.v (y - bC)))
      _ = Valued.v (y - bC) := mul_one _
      _ < (γ : WithZero (Multiplicative ℤ)) := hyb
  have hglobal : v.intValuation (η - b ^ q) <
      WithZero.exp (-(n : ℤ)) := by
    have hC :
        Valued.v
            (algebraMap (NumberField.RingOfIntegers K)
              (v.adicCompletion K) (η - b ^ q)) <
          WithZero.exp (-(n : ℤ)) := by
      rw [map_sub, map_pow, ← hy]
      exact hγ ▸ hpow
    rw [IsScalarTower.algebraMap_apply
      (NumberField.RingOfIntegers K) K (v.adicCompletion K)] at hC
    rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion] at hC
    simp only [Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply] at hC
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap] at hC
    exact hC
  exact ⟨b, (v.intValuation_le_pow_iff_mem (η - b ^ q) n).mp hglobal.le⟩

/-- The finite hyperprimary condition at the cyclotomic prime: the numerator
is a cyclotomic-prime unit and is a `p`-th power modulo `λ^(p+1)`. -/
def IsFinitePrimaryAtCyclotomicPrime
    (η : NumberField.RingOfIntegers (PrimeCyclotomicField p)) : Prop :=
  η ∉ (cyclotomicPrime p).asIdeal ∧
    ∃ b : NumberField.RingOfIntegers (PrimeCyclotomicField p),
      η - b ^ p ∈ (cyclotomicPrime p).asIdeal ^ (p + 1)

/-- An integral cyclotomic-prime unit with a `p`-th root in the completion
is finite-primary. -/
theorem isFinitePrimaryAtCyclotomicPrime_of_adic_pthPower
    (η : NumberField.RingOfIntegers (PrimeCyclotomicField p))
    (hηPrime : η ∉ (cyclotomicPrime p).asIdeal)
    (hroot : ∃ y : (cyclotomicPrime p).adicCompletion
        (PrimeCyclotomicField p),
      y ^ p = algebraMap
        (NumberField.RingOfIntegers (PrimeCyclotomicField p))
        ((cyclotomicPrime p).adicCompletion (PrimeCyclotomicField p)) η) :
    IsFinitePrimaryAtCyclotomicPrime η := by
  refine ⟨hηPrime, ?_⟩
  exact exists_integral_pow_congr_mod_prime_pow_of_adic_pow
    (cyclotomicPrime p) p (p + 1) (Fact.out : p.Prime).ne_zero η hroot

end NumberTheory.CyclotomicCharacter.InverseExtension

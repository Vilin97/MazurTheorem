/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/

import MazurTorsion.NumberTheory.XOneEighteenDyadicProjection
import MazurTorsion.NumberTheory.XOneEighteenDyadicCubicCertificate
import MazurTorsion.NumberTheory.XOneEighteenQuotientTwoDescentModel
import EllipticCurves.X18SelmerLocal

/-!
# The cubic dyadic local image for the `X₁(18)` quotient

This file models the unramified cubic quotient modulo `2⁷` as

`(ZMod 128)[T] / (T³ - 3T - 1)`.

The normalized local curve has equation

`Y² = X (X² + 62X + 65)`.

Its quadratic factor is exactly `(X + 31)²` modulo `128`.  The proof
below uses that factorization together with a bounded dyadic valuation
argument; it does not enumerate pairs of cubic residues.
-/

open Polynomial

namespace MazurTorsion.XOneEighteenDyadicLocalImage

noncomputable section

/-- The coefficient cubic at dyadic precision `2⁷`. -/
def cubicPolynomial128 : Polynomial (ZMod 128) :=
  X ^ 3 - 3 * X - 1

/-- The unramified cubic residue ring modulo `2⁷`. -/
abbrev CubicResidue128 := AdjoinRoot cubicPolynomial128

/-- The coefficient cubic over the residue field. -/
def cubicPolynomial2 : Polynomial (ZMod 2) :=
  X ^ 3 - 3 * X - 1

/-- The residue field of the unramified cubic ring. -/
abbrev CubicResidue2 := AdjoinRoot cubicPolynomial2

private theorem cubicPolynomial128_monic : cubicPolynomial128.Monic := by
  simp only [cubicPolynomial128]
  monicity <;> norm_num

private theorem cubicPolynomial128_natDegree :
    cubicPolynomial128.natDegree = 3 := by
  simp only [cubicPolynomial128]
  compute_degree!

private theorem cubicPolynomial2_monic : cubicPolynomial2.Monic := by
  simp only [cubicPolynomial2]
  monicity <;> norm_num

private theorem cubicPolynomial2_irreducible :
    Irreducible cubicPolynomial2 := by
  have hdegree : cubicPolynomial2.natDegree = 3 := by
    simp only [cubicPolynomial2]
    compute_degree!
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    (p := cubicPolynomial2) ?_ ?_
  · rw [hdegree]
    norm_num
  · intro z
    unfold Polynomial.IsRoot
    simp only [cubicPolynomial2, eval_sub, eval_pow, eval_X,
      eval_mul, eval_ofNat, eval_one]
    fin_cases z <;> decide

private instance cubicPolynomial2_irreducibleFact :
    Fact (Irreducible cubicPolynomial2) :=
  ⟨cubicPolynomial2_irreducible⟩

private def reduceBase : ZMod 128 →+* ZMod 2 :=
  ZMod.castHom (by norm_num : 2 ∣ 128) (ZMod 2)

private theorem cubicPolynomial_map_reduceBase :
    cubicPolynomial128.map reduceBase = cubicPolynomial2 := by
  norm_num [cubicPolynomial128, cubicPolynomial2, reduceBase]

/-- Reduction of the cubic residue ring modulo `2`. -/
def reduce : CubicResidue128 →+* CubicResidue2 :=
  AdjoinRoot.map reduceBase cubicPolynomial128 cubicPolynomial2
    (by rw [cubicPolynomial_map_reduceBase])

@[simp]
private theorem reduce_mk (p : Polynomial (ZMod 128)) :
    reduce (AdjoinRoot.mk cubicPolynomial128 p) =
      AdjoinRoot.mk cubicPolynomial2 (p.map reduceBase) := by
  exact AdjoinRoot.map_mk _ _ _

private theorem reduce_surjective : Function.Surjective reduce := by
  intro z
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  obtain ⟨q, hq⟩ := Polynomial.map_surjective reduceBase
    (ZMod.castHom_surjective (by norm_num : 2 ∣ 128)) p
  refine ⟨AdjoinRoot.mk cubicPolynomial128 q, ?_⟩
  rw [reduce_mk, hq]

private theorem base_eq_two_mul_of_reduce_eq_zero :
    ∀ a : ZMod 128, reduceBase a = 0 → ∃ b : ZMod 128, a = 2 * b := by
  decide +kernel

private theorem eq_two_mul_of_reduce_eq_zero
    (z : CubicResidue128) (hz : reduce z = 0) :
    ∃ w : CubicResidue128, z = 2 * w := by
  classical
  induction z using AdjoinRoot.induction_on with
  | ih q =>
      let r := q %ₘ cubicPolynomial128
      have hredq :
          AdjoinRoot.mk cubicPolynomial2 (q.map reduceBase) = 0 := by
        simpa only [reduce_mk] using hz
      have hdvd : cubicPolynomial2 ∣ q.map reduceBase :=
        AdjoinRoot.mk_eq_zero.mp hredq
      have hrmap : r.map reduceBase = 0 := by
        dsimp only [r]
        rw [Polynomial.map_modByMonic reduceBase cubicPolynomial128_monic,
          cubicPolynomial_map_reduceBase]
        exact (Polynomial.modByMonic_eq_zero_iff_dvd
          cubicPolynomial2_monic).2 hdvd
      have hcoeff (n : ℕ) : reduceBase (r.coeff n) = 0 := by
        have h := congrArg (fun p : Polynomial (ZMod 2) ↦ p.coeff n) hrmap
        simpa only [coeff_map, coeff_zero] using h
      choose b hb using fun n ↦
        base_eq_two_mul_of_reduce_eq_zero (r.coeff n) (hcoeff n)
      let s : Polynomial (ZMod 128) :=
        ∑ n ∈ r.support, C (b n) * X ^ n
      have hrs : r = C 2 * s := by
        rw [Polynomial.as_sum_support_C_mul_X_pow r]
        simp only [s, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        rw [hb n, map_mul]
        ring
      refine ⟨AdjoinRoot.mk cubicPolynomial128 s, ?_⟩
      calc
        AdjoinRoot.mk cubicPolynomial128 q =
            AdjoinRoot.mk cubicPolynomial128 r := by
              symm
              simpa only [r, AdjoinRoot.modByMonicHom_mk] using
                AdjoinRoot.mk_leftInverse cubicPolynomial128_monic
                  (AdjoinRoot.mk cubicPolynomial128 q)
        _ = AdjoinRoot.mk cubicPolynomial128 (C 2 * s) := by rw [← hrs]
        _ = 2 * AdjoinRoot.mk cubicPolynomial128 s := by
          simp only [map_mul, AdjoinRoot.mk_C]
          rw [map_ofNat]

private theorem algebraMap_ne_zero {a : ZMod 128} (ha : a ≠ 0) :
    algebraMap (ZMod 128) CubicResidue128 a ≠ 0 := by
  rw [AdjoinRoot.algebraMap_eq]
  apply AdjoinRoot.mk_ne_zero_of_natDegree_lt cubicPolynomial128_monic
  · simpa only [C_ne_zero]
  · simp only [natDegree_C, cubicPolynomial128_natDegree]
    norm_num

private theorem isUnit_of_reduce_ne_zero {z : CubicResidue128}
    (hz : reduce z ≠ 0) : IsUnit z := by
  obtain ⟨w, hw⟩ := reduce_surjective ((reduce z)⁻¹ : CubicResidue2)
  have hker : reduce (1 - z * w) = 0 := by
    rw [map_sub, map_one, map_mul, hw]
    exact sub_eq_zero.mpr (mul_inv_cancel₀ hz).symm
  obtain ⟨q, hq⟩ := eq_two_mul_of_reduce_eq_zero (1 - z * w) hker
  have hnil : IsNilpotent (1 - z * w) := by
    refine ⟨7, ?_⟩
    rw [hq]
    calc
      (2 * q) ^ 7 = 128 * q ^ 7 := by ring
      _ = 0 := by
        rw [← map_ofNat (algebraMap (ZMod 128) CubicResidue128) 128]
        have h128 : (128 : ZMod 128) = 0 := by decide
        rw [h128, map_zero, zero_mul]
  have hzw : IsUnit (z * w) := by
    simpa only [sub_sub_cancel] using hnil.isUnit_one_sub
  exact (IsUnit.mul_iff.mp hzw).1

private theorem isUnit_or_eq_two_mul (z : CubicResidue128) :
    IsUnit z ∨ ∃ w : CubicResidue128, z = 2 * w := by
  by_cases hz : reduce z = 0
  · exact Or.inr (eq_two_mul_of_reduce_eq_zero z hz)
  · exact Or.inl (isUnit_of_reduce_ne_zero hz)

private theorem scalar_four_ne_zero : (4 : CubicResidue128) ≠ 0 := by
  rw [← map_ofNat (algebraMap (ZMod 128) CubicResidue128) 4]
  exact algebraMap_ne_zero (by decide)

private theorem scalar_eight_ne_zero : (8 : CubicResidue128) ≠ 0 := by
  rw [← map_ofNat (algebraMap (ZMod 128) CubicResidue128) 8]
  exact algebraMap_ne_zero (by decide)

private theorem scalar_sixteen_ne_zero : (16 : CubicResidue128) ≠ 0 := by
  rw [← map_ofNat (algebraMap (ZMod 128) CubicResidue128) 16]
  exact algebraMap_ne_zero (by decide)

private theorem scalar_thirtytwo_ne_zero : (32 : CubicResidue128) ≠ 0 := by
  rw [← map_ofNat (algebraMap (ZMod 128) CubicResidue128) 32]
  exact algebraMap_ne_zero (by decide)

private theorem scalar_sixtyfour_ne_zero : (64 : CubicResidue128) ≠ 0 := by
  rw [← map_ofNat (algebraMap (ZMod 128) CubicResidue128) 64]
  exact algebraMap_ne_zero (by decide)

private theorem eq_zero_of_mul_unit_eq_zero {a u : CubicResidue128}
    (hu : IsUnit u) (h : a * u = 0) : a = 0 := by
  obtain ⟨U, rfl⟩ := hu
  calc
    a = (a * (U : CubicResidue128)) *
        (↑(U⁻¹) : CubicResidue128) := by simp
    _ = 0 := by rw [h, zero_mul]

private theorem not_isUnit_of_mul_eq_zero {a u : CubicResidue128}
    (ha : a ≠ 0) (h : a * u = 0) : ¬ IsUnit u := by
  intro hu
  exact ha (eq_zero_of_mul_unit_eq_zero hu h)

private theorem eq_thirtytwo_mul_of_four_mul_eq_zero
    (z : CubicResidue128) (hz : 4 * z = 0) :
    ∃ w : CubicResidue128, z = 32 * w := by
  have hnz : ¬ IsUnit z :=
    not_isUnit_of_mul_eq_zero scalar_four_ne_zero hz
  obtain ⟨z₁, hz₁⟩ := (isUnit_or_eq_two_mul z).resolve_left hnz
  have h₁ : 8 * z₁ = 0 := by rw [hz₁] at hz; linear_combination hz
  have hnz₁ : ¬ IsUnit z₁ :=
    not_isUnit_of_mul_eq_zero scalar_eight_ne_zero h₁
  obtain ⟨z₂, hz₂⟩ := (isUnit_or_eq_two_mul z₁).resolve_left hnz₁
  have h₂ : 16 * z₂ = 0 := by rw [hz₂] at h₁; linear_combination h₁
  have hnz₂ : ¬ IsUnit z₂ :=
    not_isUnit_of_mul_eq_zero scalar_sixteen_ne_zero h₂
  obtain ⟨z₃, hz₃⟩ := (isUnit_or_eq_two_mul z₂).resolve_left hnz₂
  have h₃ : 32 * z₃ = 0 := by rw [hz₃] at h₂; linear_combination h₂
  have hnz₃ : ¬ IsUnit z₃ :=
    not_isUnit_of_mul_eq_zero scalar_thirtytwo_ne_zero h₃
  obtain ⟨z₄, hz₄⟩ := (isUnit_or_eq_two_mul z₃).resolve_left hnz₃
  have h₄ : 64 * z₄ = 0 := by rw [hz₄] at h₃; linear_combination h₃
  have hnz₄ : ¬ IsUnit z₄ :=
    not_isUnit_of_mul_eq_zero scalar_sixtyfour_ne_zero h₄
  obtain ⟨z₅, hz₅⟩ := (isUnit_or_eq_two_mul z₄).resolve_left hnz₄
  refine ⟨z₅, ?_⟩
  rw [hz₁, hz₂, hz₃, hz₄, hz₅]
  ring

private theorem eq_eight_mul_of_sixteen_mul_eq_zero
    (z : CubicResidue128) (hz : 16 * z = 0) :
    ∃ w : CubicResidue128, z = 8 * w := by
  have hnz : ¬ IsUnit z :=
    not_isUnit_of_mul_eq_zero scalar_sixteen_ne_zero hz
  obtain ⟨z₁, hz₁⟩ := (isUnit_or_eq_two_mul z).resolve_left hnz
  have h₁ : 32 * z₁ = 0 := by rw [hz₁] at hz; linear_combination hz
  have hnz₁ : ¬ IsUnit z₁ :=
    not_isUnit_of_mul_eq_zero scalar_thirtytwo_ne_zero h₁
  obtain ⟨z₂, hz₂⟩ := (isUnit_or_eq_two_mul z₁).resolve_left hnz₁
  have h₂ : 64 * z₂ = 0 := by rw [hz₂] at h₁; linear_combination h₁
  have hnz₂ : ¬ IsUnit z₂ :=
    not_isUnit_of_mul_eq_zero scalar_sixtyfour_ne_zero h₂
  obtain ⟨z₃, hz₃⟩ := (isUnit_or_eq_two_mul z₂).resolve_left hnz₂
  refine ⟨z₃, ?_⟩
  rw [hz₁, hz₂, hz₃]
  ring

private theorem scalar_one_twenty_eight_eq_zero :
    (128 : CubicResidue128) = 0 := by
  rw [← map_ofNat (algebraMap (ZMod 128) CubicResidue128) 128]
  have h128 : (128 : ZMod 128) = 0 := by decide
  rw [h128, map_zero]

private theorem reduce_ne_zero_of_isUnit {z : CubicResidue128}
    (hz : IsUnit z) : reduce z ≠ 0 :=
  (hz.map reduce).ne_zero

private theorem reduce_two_eq_zero :
    reduce (2 : CubicResidue128) = 0 := by
  rw [map_ofNat]
  rw [← map_ofNat (algebraMap (ZMod 2) CubicResidue2) 2]
  have htwo : (2 : ZMod 2) = 0 := by decide
  rw [htwo, map_zero]

private theorem reduce_four_eq_zero :
    reduce (4 : CubicResidue128) = 0 := by
  rw [show (4 : CubicResidue128) = 2 * 2 by ring, map_mul,
    reduce_two_eq_zero, zero_mul]

private theorem reduce_eight_eq_zero :
    reduce (8 : CubicResidue128) = 0 := by
  rw [show (8 : CubicResidue128) = 2 * 4 by ring, map_mul,
    reduce_two_eq_zero, zero_mul]

private theorem reduce_thirtytwo_eq_zero :
    reduce (32 : CubicResidue128) = 0 := by
  rw [show (32 : CubicResidue128) = 2 * 16 by ring, map_mul,
    reduce_two_eq_zero, zero_mul]

private theorem isSquare_of_eq_sq_add_eight_mul
    {x z a : CubicResidue128} (hz : IsUnit z)
    (hx : x = z ^ 2 + 8 * a) : IsSquare x := by
  let u₀ : CubicResidue128 := ↑(hz.unit⁻¹)
  have hzu₀ : z * u₀ = 1 := by
    dsimp only [u₀]
    calc
      z * (↑(hz.unit⁻¹) : CubicResidue128) =
          (↑hz.unit : CubicResidue128) *
            (↑(hz.unit⁻¹) : CubicResidue128) := by
              rw [hz.unit_spec]
      _ = 1 := by simp
  let z₁ : CubicResidue128 := z + 4 * a * u₀
  let a₁ : CubicResidue128 := -(a ^ 2 * u₀ ^ 2)
  have hx₁ : x = z₁ ^ 2 + 16 * a₁ := by
    rw [hx]
    dsimp only [z₁, a₁]
    linear_combination -8 * a * hzu₀
  have hz₁ : IsUnit z₁ := by
    apply isUnit_of_reduce_ne_zero
    have hzred := reduce_ne_zero_of_isUnit hz
    dsimp only [z₁]
    simpa only [map_add, map_mul, reduce_four_eq_zero, zero_mul,
      zero_add, add_zero] using hzred
  let u₁ : CubicResidue128 := ↑(hz₁.unit⁻¹)
  have hz₁u₁ : z₁ * u₁ = 1 := by
    dsimp only [u₁]
    calc
      z₁ * (↑(hz₁.unit⁻¹) : CubicResidue128) =
          (↑hz₁.unit : CubicResidue128) *
            (↑(hz₁.unit⁻¹) : CubicResidue128) := by
              rw [hz₁.unit_spec]
      _ = 1 := by simp
  let z₂ : CubicResidue128 := z₁ + 8 * a₁ * u₁
  let a₂ : CubicResidue128 := -(a₁ ^ 2 * u₁ ^ 2)
  have hx₂ : x = z₂ ^ 2 + 64 * a₂ := by
    rw [hx₁]
    dsimp only [z₂, a₂]
    linear_combination -16 * a₁ * hz₁u₁
  have hz₂ : IsUnit z₂ := by
    apply isUnit_of_reduce_ne_zero
    have hz₁red := reduce_ne_zero_of_isUnit hz₁
    dsimp only [z₂]
    simpa only [map_add, map_mul, reduce_eight_eq_zero, zero_mul,
      zero_add, add_zero] using hz₁red
  let u₂ : CubicResidue128 := ↑(hz₂.unit⁻¹)
  have hz₂u₂ : z₂ * u₂ = 1 := by
    dsimp only [u₂]
    calc
      z₂ * (↑(hz₂.unit⁻¹) : CubicResidue128) =
          (↑hz₂.unit : CubicResidue128) *
            (↑(hz₂.unit⁻¹) : CubicResidue128) := by
              rw [hz₂.unit_spec]
      _ = 1 := by simp
  let z₃ : CubicResidue128 := z₂ + 32 * a₂ * u₂
  have hx₃ : x = z₃ ^ 2 := by
    rw [hx₂]
    dsimp only [z₃]
    linear_combination -64 * a₂ * hz₂u₂ -
      8 * a₂ ^ 2 * u₂ ^ 2 * scalar_one_twenty_eight_eq_zero
  exact ⟨z₃, by simpa only [pow_two] using hx₃⟩

private theorem quadratic_factor_eq_square (x : CubicResidue128) :
    x ^ 2 + 62 * x + 65 = (x + 31) ^ 2 := by
  linear_combination -7 * scalar_one_twenty_eight_eq_zero

private theorem eq_two_mul_of_sq_eq_mul_sq_of_eq_two_mul
    {x y t u : CubicResidue128} (hcurve : y ^ 2 = x * t ^ 2)
    (ht : t = 2 * u) :
    ∃ v : CubicResidue128, y = 2 * v := by
  have htred : reduce t = 0 := by
    rw [ht, map_mul, reduce_two_eq_zero, zero_mul]
  have hyredsq : reduce y ^ 2 = 0 := by
    rw [← map_pow, hcurve, map_mul, map_pow, htred]
    ring
  have hyred : reduce y = 0 := sq_eq_zero_iff.mp hyredsq
  exact eq_two_mul_of_reduce_eq_zero y hyred

private theorem isUnit_of_add_thirtyone_eq_two_mul
    {x u : CubicResidue128} (hx : x + 31 = 2 * u) :
    IsUnit x := by
  apply isUnit_of_reduce_ne_zero
  intro hxred
  have hred := congrArg reduce hx
  rw [map_add, hxred, map_mul, reduce_two_eq_zero, zero_mul] at hred
  have hthirtyone : reduce (31 : CubicResidue128) = 1 := by
    rw [show (31 : CubicResidue128) = 1 + 2 * 15 by ring,
      map_add, map_one, map_mul, reduce_two_eq_zero, zero_mul, add_zero]
  rw [hthirtyone, zero_add] at hred
  exact one_ne_zero hred

private theorem isSquare_of_unit_scaled_congruence
    {x v u a : CubicResidue128} (hx : IsUnit x) (hu : IsUnit u)
    (hcong : v ^ 2 - x * u ^ 2 = 8 * a) :
    IsSquare x := by
  let uInv : CubicResidue128 := ↑(hu.unit⁻¹)
  have huuInv : u * uInv = 1 := by
    dsimp only [uInv]
    calc
      u * (↑(hu.unit⁻¹) : CubicResidue128) =
          (↑hu.unit : CubicResidue128) *
            (↑(hu.unit⁻¹) : CubicResidue128) := by
              rw [hu.unit_spec]
      _ = 1 := by simp
  let z : CubicResidue128 := v * uInv
  let b : CubicResidue128 := -(a * uInv ^ 2)
  have hxz : x = z ^ 2 + 8 * b := by
    dsimp only [z, b]
    linear_combination -uInv ^ 2 * hcong -
      x * (u * uInv + 1) * huuInv
  have hz : IsUnit z := by
    apply isUnit_of_reduce_ne_zero
    intro hzred
    have hxred := reduce_ne_zero_of_isUnit hx
    apply hxred
    have hred := congrArg reduce hxz
    rw [map_add, map_pow, hzred, zero_pow (by norm_num : 2 ≠ 0),
      map_mul, reduce_eight_eq_zero, zero_mul, add_zero] at hred
    exact hred
  exact isSquare_of_eq_sq_add_eight_mul hz hxz

private theorem isSquare_of_shift_valuation_one
    {x y u : CubicResidue128}
    (hcurve : y ^ 2 = x * (x + 31) ^ 2)
    (hshift : x + 31 = 2 * u) (hu : IsUnit u) :
    IsSquare x := by
  obtain ⟨v, hv⟩ :=
    eq_two_mul_of_sq_eq_mul_sq_of_eq_two_mul hcurve hshift
  have hfour : 4 * (v ^ 2 - x * u ^ 2) = 0 := by
    rw [hv, hshift] at hcurve
    linear_combination hcurve
  obtain ⟨a, ha⟩ :=
    eq_thirtytwo_mul_of_four_mul_eq_zero
      (v ^ 2 - x * u ^ 2) hfour
  have ha8 : v ^ 2 - x * u ^ 2 = 8 * (4 * a) := by
    rw [ha]
    ring
  exact isSquare_of_unit_scaled_congruence
    (isUnit_of_add_thirtyone_eq_two_mul hshift) hu ha8

private theorem isSquare_of_shift_valuation_two
    {x y u : CubicResidue128}
    (hcurve : y ^ 2 = x * (x + 31) ^ 2)
    (hshift : x + 31 = 4 * u) (hu : IsUnit u) :
    IsSquare x := by
  have hshift2 : x + 31 = 2 * (2 * u) := by rw [hshift]; ring
  obtain ⟨y₁, hy₁⟩ :=
    eq_two_mul_of_sq_eq_mul_sq_of_eq_two_mul hcurve hshift2
  have hfour : 4 * (y₁ ^ 2 - 4 * x * u ^ 2) = 0 := by
    rw [hy₁, hshift] at hcurve
    linear_combination hcurve
  obtain ⟨a₁, ha₁⟩ :=
    eq_thirtytwo_mul_of_four_mul_eq_zero
      (y₁ ^ 2 - 4 * x * u ^ 2) hfour
  have hy₁redsq : reduce y₁ ^ 2 = 0 := by
    have hred := congrArg reduce ha₁
    simpa only [map_sub, map_pow, map_mul, reduce_four_eq_zero,
      reduce_thirtytwo_eq_zero, zero_mul, sub_zero] using hred
  have hy₁red : reduce y₁ = 0 := sq_eq_zero_iff.mp hy₁redsq
  obtain ⟨v, hv⟩ := eq_two_mul_of_reduce_eq_zero y₁ hy₁red
  have hsixteen : 16 * (v ^ 2 - x * u ^ 2) = 0 := by
    rw [hy₁, hv, hshift] at hcurve
    linear_combination hcurve
  obtain ⟨a, ha⟩ :=
    eq_eight_mul_of_sixteen_mul_eq_zero
      (v ^ 2 - x * u ^ 2) hsixteen
  exact isSquare_of_unit_scaled_congruence
    (isUnit_of_add_thirtyone_eq_two_mul hshift2) hu ha

private theorem isSquare_of_shift_divisible_by_eight
    {x u : CubicResidue128} (hshift : x + 31 = 8 * u) :
    IsSquare x := by
  have hx : x = (1 : CubicResidue128) ^ 2 + 8 * (u - 4) := by
    linear_combination hshift
  exact isSquare_of_eq_sq_add_eight_mul isUnit_one hx

/--
Every point of the normalized curve over the unramified cubic quotient
modulo `2⁷` has square first coordinate.  The proof splits according to the
truncated valuation of `X + 31`; it performs no enumeration of residue-ring
pairs.
-/
theorem integral_cubic_mod128 :
    ∀ X Y : CubicResidue128,
      Y ^ 2 = X * (X ^ 2 + 62 * X + 65) → IsSquare X := by
  intro x y hcurve
  have hcurve' : y ^ 2 = x * (x + 31) ^ 2 := by
    rw [← quadratic_factor_eq_square]
    exact hcurve
  rcases isUnit_or_eq_two_mul (x + 31) with hunit | ⟨u, hshift⟩
  · let uInv : CubicResidue128 := ↑(hunit.unit⁻¹)
    have huuInv : (x + 31) * uInv = 1 := by
      dsimp only [uInv]
      calc
        (x + 31) * (↑(hunit.unit⁻¹) : CubicResidue128) =
            (↑hunit.unit : CubicResidue128) *
              (↑(hunit.unit⁻¹) : CubicResidue128) := by
                rw [hunit.unit_spec]
        _ = 1 := by simp
    refine ⟨y * uInv, ?_⟩
    have hroot : x = (y * uInv) ^ 2 := by
      linear_combination -uInv ^ 2 * hcurve' -
        x * ((x + 31) * uInv + 1) * huuInv
    simpa only [pow_two] using hroot
  · rcases isUnit_or_eq_two_mul u with hu | ⟨u₂, hu₂⟩
    · exact isSquare_of_shift_valuation_one hcurve' hshift hu
    · have hshift4 : x + 31 = 4 * u₂ := by rw [hshift, hu₂]; ring
      rcases isUnit_or_eq_two_mul u₂ with hu₂unit | ⟨u₃, hu₃⟩
      · exact isSquare_of_shift_valuation_two hcurve' hshift4 hu₂unit
      · exact isSquare_of_shift_divisible_by_eight (by
          rw [hshift4, hu₃]
          ring)

/-- Witness form of `integral_cubic_mod128`, matching the scalar certificate
API in `XOneEighteenDyadicProjection`. -/
theorem integral_cubic_mod128_exists
    (X Y : CubicResidue128)
    (hcurve : Y ^ 2 = X * (X ^ 2 + 62 * X + 65)) :
    ∃ Z : CubicResidue128, Z ^ 2 = X := by
  obtain ⟨Z, hZ⟩ := integral_cubic_mod128 X Y hcurve
  exact ⟨Z, by simpa only [pow_two] using hZ.symm⟩

/--
Formal transport boundary for an integral local model: once a reduction map
to the explicit unramified cubic quotient has been constructed, every
normalized integral curve point has square `X`-reduction.  This theorem does
not assert or postulate the missing arithmetic identification of a concrete
adic-completion quotient with `CubicResidue128`.
-/
theorem square_reduction_of_normalized_curve
    {R : Type*} [CommRing R] (reduction : R →+* CubicResidue128)
    {X Y : R} (hcurve : Y ^ 2 = X * (X ^ 2 + 62 * X + 65)) :
    IsSquare (reduction X) := by
  apply integral_cubic_mod128 (reduction X) (reduction Y)
  simpa only [map_pow, map_mul, map_add, map_ofNat] using
    congrArg reduction hcurve

end

end MazurTorsion.XOneEighteenDyadicLocalImage

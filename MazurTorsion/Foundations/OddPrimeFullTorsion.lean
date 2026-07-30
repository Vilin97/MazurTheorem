/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Discriminant obstructions to full odd-prime torsion

For an odd integer `n`, the nonzero `n`-torsion points modulo sign are the roots of the
univariate division polynomial `preΨ' n`. If all of those points are rational, that polynomial
splits over `ℚ`, so its discriminant is a rational square. For `n = 5` and `n = 7`, the classical
division-polynomial discriminant formula has respectively the shapes

* `5 ^ 11 * Δ ^ 22`, and
* `-(7 ^ 23 * Δ ^ 92)`.

Neither is a square when the curve discriminant `Δ` is nonzero. This file establishes the
polynomial and rational-arithmetic part of that argument. The two missing geometric identities
(the torsion/root equivalence and the division-polynomial discriminant formula) are intentionally
not postulated here.
-/

namespace MazurTorsion.OddPrimeFullTorsion

open Polynomial
open scoped WeierstrassCurve.Affine

private def derivativePairProduct (s : Multiset ℚ) : ℚ :=
  (s.map fun x ↦ ((s.erase x).map fun y ↦ x - y).prod).prod

private lemma derivativePairProduct_cons {a : ℚ} {s : Multiset ℚ} (ha : a ∉ s) :
    derivativePairProduct (a ::ₘ s) =
      (-1) ^ s.card * ((s.map fun x ↦ a - x).prod) ^ 2 *
        derivativePairProduct s := by
  have htail :
      (s.map fun x ↦ (((a ::ₘ s).erase x).map fun y ↦ x - y).prod).prod =
        (s.map fun x ↦ x - a).prod * derivativePairProduct s := by
    rw [derivativePairProduct, ← Multiset.prod_map_mul]
    congr 1
    apply Multiset.map_congr rfl
    intro x hx
    have hax : a ≠ x := by
      intro h
      apply ha
      simpa [h] using hx
    rw [Multiset.erase_cons_tail s hax]
    simp only [Multiset.map_cons, Multiset.prod_cons]
  have hreverse :
      (s.map fun x ↦ x - a).prod =
        (-1) ^ s.card * (s.map fun x ↦ a - x).prod := by
    calc
      (s.map fun x ↦ x - a).prod =
          ((s.map fun x ↦ a - x).map fun x ↦ -x).prod := by
            congr 1
            simp only [Multiset.map_map, Function.comp_apply]
            apply Multiset.map_congr rfl
            intro x _
            ring
      _ = (-1) ^ (s.map fun x ↦ a - x).card *
          (s.map fun x ↦ a - x).prod := Multiset.prod_map_neg _
      _ = (-1) ^ s.card * (s.map fun x ↦ a - x).prod := by simp
  rw [derivativePairProduct]
  simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.erase_cons_head]
  rw [htail, hreverse]
  ring

private lemma derivativePairProduct_isSquare (s : Multiset ℚ) :
    IsSquare
      ((-1) ^ (s.card * (s.card - 1) / 2) * derivativePairProduct s) := by
  induction s using Multiset.induction_on with
  | empty => simp [derivativePairProduct]
  | @cons a s ih =>
      by_cases ha : a ∈ s
      · have hzero : derivativePairProduct (a ::ₘ s) = 0 := by
          rw [derivativePairProduct]
          apply Multiset.prod_eq_zero
          apply Multiset.mem_map.mpr
          refine ⟨a, by simp, ?_⟩
          apply Multiset.prod_eq_zero
          apply Multiset.mem_map.mpr
          exact ⟨a, by simpa using ha, sub_self a⟩
        simp [hzero]
      · rw [derivativePairProduct_cons ha]
        rcases ih with ⟨z, hz⟩
        refine ⟨(s.map fun x ↦ a - x).prod * z, ?_⟩
        simp only [Multiset.card_cons]
        have hexponent : (s.card + 1) * (s.card + 1 - 1) / 2 =
            s.card + s.card * (s.card - 1) / 2 := by
          rw [← Nat.choose_two_right, ← Nat.choose_two_right]
          simp [Nat.choose_succ_succ]
        rw [hexponent, pow_add]
        have hsign : ((-1 : ℚ) ^ s.card) * (-1) ^ s.card = 1 := by
          rw [← pow_add]
          simp [← two_mul]
        calc
          (-1 : ℚ) ^ s.card * (-1) ^ (s.card * (s.card - 1) / 2) *
                ((-1) ^ s.card * (s.map fun x ↦ a - x).prod ^ 2 *
                  derivativePairProduct s) =
              ((-1 : ℚ) ^ s.card * (-1) ^ s.card) *
                ((s.map fun x ↦ a - x).prod ^ 2 *
                  ((-1) ^ (s.card * (s.card - 1) / 2) *
                    derivativePairProduct s)) := by ring
          _ = (s.map fun x ↦ a - x).prod ^ 2 *
                ((-1) ^ (s.card * (s.card - 1) / 2) *
                  derivativePairProduct s) := by
                    rw [hsign, one_mul]
          _ = (s.map fun x ↦ a - x).prod ^ 2 * (z * z) := by rw [hz]
          _ = (s.map fun x ↦ a - x).prod * z *
              ((s.map fun x ↦ a - x).prod * z) := by ring

private theorem isSquare_discr_of_splits_of_monic {f : ℚ[X]}
    (hf : f.Splits) (hm : f.Monic) :
    IsSquare f.discr := by
  by_cases hdegree : f.natDegree = 0
  · rw [Polynomial.eq_one_of_monic_natDegree_zero hm hdegree]
    change IsSquare (Polynomial.discr (Polynomial.C (1 : ℚ)))
    rw [Polynomial.discr_C]
    exact IsSquare.one
  have hdegree_pos : 0 < f.natDegree := Nat.pos_of_ne_zero hdegree
  have hresultant_discr :=
    Polynomial.resultant_deriv
      (Polynomial.natDegree_pos_iff_degree_pos.mp hdegree_pos)
  have hresultant_roots :=
    Polynomial.resultant_eq_prod_eval f f.derivative (f.natDegree - 1)
      f.natDegree_derivative_le hf
  simp only [hm.leadingCoeff, mul_one] at hresultant_discr
  simp only [hm.leadingCoeff, one_pow, one_mul] at hresultant_roots
  have hroot_product :
      (f.roots.map fun x ↦ Polynomial.eval x f.derivative).prod =
        derivativePairProduct f.roots := by
    rw [derivativePairProduct]
    congr 1
    apply Multiset.map_congr rfl
    intro x hx
    exact hf.eval_root_derivative hm hx
  rw [hroot_product] at hresultant_roots
  have hpair :
      derivativePairProduct f.roots =
        (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.discr :=
    hresultant_roots.symm.trans hresultant_discr
  have hsquare := derivativePairProduct_isSquare f.roots
  rw [← hf.natDegree_eq_card_roots, hpair] at hsquare
  let k := f.natDegree * (f.natDegree - 1) / 2
  have hsign : ((-1 : ℚ) ^ k) * (-1) ^ k = 1 := by
    rw [← pow_add]
    simp [← two_mul]
  have hcancel :
      (-1 : ℚ) ^ k * ((-1) ^ k * f.discr) = f.discr := by
    calc
      (-1 : ℚ) ^ k * ((-1) ^ k * f.discr) =
          ((-1) ^ k * (-1) ^ k) * f.discr := by ring
      _ = f.discr := by rw [hsign, one_mul]
  change IsSquare ((-1 : ℚ) ^ k * ((-1) ^ k * f.discr)) at hsquare
  rwa [hcancel] at hsquare

private lemma discr_C_mul {c : ℚ} (hc : c ≠ 0) {f : ℚ[X]}
    (hdegree : 0 < f.natDegree) :
    (Polynomial.C c * f).discr =
      c ^ (2 * f.natDegree - 2) * f.discr := by
  have hdegree' : 0 < f.degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp hdegree
  have hscaled_degree :
      (Polynomial.C c * f).natDegree = f.natDegree :=
    Polynomial.natDegree_C_mul hc
  have hscaled_degree' : 0 < (Polynomial.C c * f).degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos, hscaled_degree]
    exact hdegree
  have hresultant := Polynomial.resultant_deriv hdegree'
  have hscaled_resultant := Polynomial.resultant_deriv hscaled_degree'
  rw [hscaled_degree, Polynomial.derivative_C_mul,
    Polynomial.resultant_C_mul_left, Polynomial.resultant_C_mul_right] at hscaled_resultant
  have hleading :
      (Polynomial.C c * f).leadingCoeff = c * f.leadingCoeff := by
    rw [Polynomial.leadingCoeff, hscaled_degree, Polynomial.coeff_C_mul]
    rfl
  rw [hresultant, hleading] at hscaled_resultant
  have hpow :
      c ^ (f.natDegree - 1) * c ^ f.natDegree =
        c * c ^ (2 * f.natDegree - 2) := by
    rw [← pow_add, ← pow_succ']
    congr 1
    omega
  let sign : ℚ := (-1) ^ (f.natDegree * (f.natDegree - 1) / 2)
  have hcommon :
      sign * c * f.leadingCoeff *
          (c ^ (2 * f.natDegree - 2) * f.discr) =
        sign * c * f.leadingCoeff * (Polynomial.C c * f).discr := by
    dsimp [sign]
    calc
      (-1 : ℚ) ^ (f.natDegree * (f.natDegree - 1) / 2) * c *
            f.leadingCoeff * (c ^ (2 * f.natDegree - 2) * f.discr) =
          (c ^ (f.natDegree - 1) * c ^ f.natDegree) *
            ((-1) ^ (f.natDegree * (f.natDegree - 1) / 2) *
              f.leadingCoeff * f.discr) := by rw [hpow]; ring
      _ = (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) *
          (c * f.leadingCoeff) * (Polynomial.C c * f).discr := by
            simpa only [mul_assoc] using hscaled_resultant
      _ = (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * c *
          f.leadingCoeff * (Polynomial.C c * f).discr := by ring
  have hcommon_ne : sign * c * f.leadingCoeff ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hc)
      (Polynomial.leadingCoeff_ne_zero.mpr
      (Polynomial.ne_zero_of_natDegree_gt hdegree))
  exact (mul_left_cancel₀ hcommon_ne hcommon).symm

/-- A polynomial over `ℚ` which splits completely has square discriminant.

This includes the repeated-root case, when the discriminant is zero. The result is the elementary
polynomial bridge used by the fixed-prime torsion obstruction below. -/
theorem isSquare_discr_of_splits {f : ℚ[X]} (hf : f.Splits) :
    IsSquare f.discr := by
  by_cases hdegree : f.natDegree = 0
  · obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hdegree
    rw [← hc, Polynomial.discr_C]
    exact IsSquare.one
  have hdegree_pos : 0 < f.natDegree := Nat.pos_of_ne_zero hdegree
  have hf_ne : f ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hdegree_pos
  have hlc : f.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hf_ne
  let g : ℚ[X] := Polynomial.C f.leadingCoeff⁻¹ * f
  have hg_monic : g.Monic := by
    simpa only [g, mul_comm] using Polynomial.monic_mul_leadingCoeff_inv hf_ne
  have hg_splits : g.Splits := hf.C_mul _
  have hg_square : IsSquare g.discr :=
    isSquare_discr_of_splits_of_monic hg_splits hg_monic
  have hg_degree : 0 < g.natDegree := by
    dsimp [g]
    rw [Polynomial.natDegree_C_mul (inv_ne_zero hlc)]
    exact hdegree_pos
  have hrecover : Polynomial.C f.leadingCoeff * g = f := by
    dsimp [g]
    rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hlc,
      Polynomial.C_1, one_mul]
  have hscale := discr_C_mul hlc hg_degree
  rw [hrecover] at hscale
  have hscale_square :
      IsSquare (f.leadingCoeff ^ (2 * g.natDegree - 2)) := by
    refine ⟨f.leadingCoeff ^ (g.natDegree - 1), ?_⟩
    rw [← pow_add]
    congr 1
    omega
  rw [hscale]
  exact hscale_square.mul hg_square

private theorem divisionPolynomial_splits_of_full_torsion
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    {n d : ℕ} (hd : 0 < d)
    (representative : Fin d → ZMod n × ZMod n)
    (hrepresentative_ne : ∀ i, representative i ≠ 0)
    (hrepresentative_unique :
      ∀ i j, representative i = representative j ∨
        representative i = -representative j → i = j)
    (hrepresentative_torsion : ∀ i, n • representative i = 0)
    (hdegree : (W.preΨ' n).natDegree = d)
    (hroot :
      ∀ {x y : ℚ} (hP : W.toAffine.Nonsingular x y),
        n • WeierstrassCurve.Affine.Point.some x y hP = 0 →
          Polynomial.eval x (W.preΨ' n) = 0)
    (φ : (ZMod n × ZMod n) →+ W.toAffine.Point)
    (hφ : Function.Injective φ) :
    (W.preΨ' n).Splits := by
  have hpolynomial : W.preΨ' n ≠ 0 :=
    Polynomial.ne_zero_of_natDegree_gt (hdegree.symm ▸ hd)
  have himage_ne (i : Fin d) : φ (representative i) ≠ 0 := by
    intro hi
    apply hrepresentative_ne i
    apply hφ
    simpa using hi
  have haffine (i : Fin d) :
      ∃ x y : ℚ, ∃ hP : W.toAffine.Nonsingular x y,
        φ (representative i) =
          WeierstrassCurve.Affine.Point.some x y hP := by
    generalize hi : φ (representative i) = P
    cases P with
    | zero => exact (himage_ne i hi).elim
    | some x y hP => exact ⟨x, y, hP, rfl⟩
  choose x y hP hpoint using haffine
  have htorsion (i : Fin d) : n • φ (representative i) = 0 := by
    rw [← map_nsmul, hrepresentative_torsion i, map_zero]
  let rootMap : Fin d → {r // r ∈ (W.preΨ' n).rootSet ℚ} :=
    fun i ↦ ⟨x i, by
      rw [Polynomial.mem_rootSet_of_ne hpolynomial]
      simp only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id]
      apply hroot (hP i)
      rw [← hpoint i]
      exact htorsion i⟩
  have hrootMap_injective : Function.Injective rootMap := by
    intro i j hij
    apply hrepresentative_unique
    have hx : x i = x j :=
      congrArg (fun r : {r // r ∈ (W.preΨ' n).rootSet ℚ} ↦ r.1) hij
    have hxrep :
        (φ (representative i)).xRep = (φ (representative j)).xRep := by
      rw [hpoint i, hpoint j]
      simp [hx]
    rcases WeierstrassCurve.Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep hxrep
      with heq | heq
    · exact Or.inl (hφ heq)
    · apply Or.inr
      apply hφ
      calc
        φ (representative i) = -φ (representative j) := heq
        _ = φ (-representative j) := (map_neg φ _).symm
  have hrootSet_lower :
      d ≤ Set.ncard ((W.preΨ' n).rootSet ℚ) := by
    have hcard :
        Nat.card (Fin d) ≤
          Nat.card {r // r ∈ (W.preΨ' n).rootSet ℚ} :=
      Nat.card_le_card_of_injective rootMap hrootMap_injective
    simpa only [Nat.card_fin, Nat.card_coe_set_eq] using hcard
  have hrootSet_roots :
      Set.ncard ((W.preΨ' n).rootSet ℚ) ≤ (W.preΨ' n).roots.card := by
    classical
    rw [Polynomial.rootSet_def, Set.ncard_coe_finset]
    simpa only [Polynomial.aroots_def, Algebra.algebraMap_self,
      Polynomial.map_id] using
        Multiset.toFinset_card_le (W.preΨ' n).roots
  rw [Polynomial.splits_iff_card_roots]
  apply le_antisymm
  · exact (W.preΨ' n).card_roots'
  · rw [hdegree]
    exact hrootSet_lower.trans hrootSet_roots

/-- The forward division-polynomial root criterion needed by the discriminant argument.

Mathlib currently defines the division polynomials but does not yet connect their evaluation to
scalar multiplication of affine points. -/
def HasDivisionPolynomialRootCriterion
    (W : WeierstrassCurve ℚ) [W.IsElliptic] (n : ℕ) : Prop :=
  ∀ {x y : ℚ} (hP : W.toAffine.Nonsingular x y),
    n • WeierstrassCurve.Affine.Point.some x y hP = 0 →
      Polynomial.eval x (W.preΨ' n) = 0

private def fiveRepresentatives : Fin 12 → ZMod 5 × ZMod 5 :=
  ![(0, 1), (0, 2),
    (1, 0), (1, 1), (1, 2), (1, 3), (1, 4),
    (2, 0), (2, 1), (2, 2), (2, 3), (2, 4)]

private def sevenRepresentatives : Fin 24 → ZMod 7 × ZMod 7 :=
  ![(0, 1), (0, 2), (0, 3),
    (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6),
    (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5), (2, 6),
    (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (3, 6)]

/-- Full rational `5`-torsion makes the fifth division polynomial split, assuming only the
forward torsion/root criterion. -/
theorem fifth_division_polynomial_splits_of_full_torsion
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (hroot : HasDivisionPolynomialRootCriterion W 5)
    (φ : (ZMod 5 × ZMod 5) →+ W.toAffine.Point)
    (hφ : Function.Injective φ) :
    (W.preΨ' 5).Splits := by
  have hdegree : (W.preΨ' 5).natDegree = 12 := by
    rw [W.natDegree_preΨ' (n := 5) (by norm_num)]
    norm_num [show ¬Even 5 by decide]
  exact divisionPolynomial_splits_of_full_torsion W
    (d := 12) (by norm_num) fiveRepresentatives
    (by decide) (by decide) (by decide) hdegree hroot φ hφ

/-- Full rational `7`-torsion makes the seventh division polynomial split, assuming only the
forward torsion/root criterion. -/
theorem seventh_division_polynomial_splits_of_full_torsion
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (hroot : HasDivisionPolynomialRootCriterion W 7)
    (φ : (ZMod 7 × ZMod 7) →+ W.toAffine.Point)
    (hφ : Function.Injective φ) :
    (W.preΨ' 7).Splits := by
  have hdegree : (W.preΨ' 7).natDegree = 24 := by
    rw [W.natDegree_preΨ' (n := 7) (by norm_num)]
    norm_num [show ¬Even 7 by decide]
  exact divisionPolynomial_splits_of_full_torsion W
    (d := 24) (by norm_num) sevenRepresentatives
    (by decide) (by decide) (by decide) hdegree hroot φ hφ

private lemma nonsquare_mul_sq {a t : ℚ} (ha : ¬ IsSquare a) (ht : t ≠ 0) :
    ¬ IsSquare (a * t ^ 2) := by
  rintro ⟨q, hq⟩
  apply ha
  refine ⟨q / t, ?_⟩
  field_simp [ht]
  nlinarith [hq]

/-- The square class occurring in the discriminant of the fifth division polynomial is
nontrivial over `ℚ`. -/
theorem not_isSquare_five_discriminant_shape {Δ : ℚ} (hΔ : Δ ≠ 0) :
    ¬ IsSquare ((5 : ℚ) ^ 11 * Δ ^ 22) := by
  have hfive : ¬ IsSquare (5 : ℚ) := by
    intro h
    exact (by decide : Nat.Prime 5).not_isSquare
      (Rat.isSquare_natCast_iff.mp h)
  have ht : (5 : ℚ) ^ 5 * Δ ^ 11 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 5 (by norm_num)) (pow_ne_zero 11 hΔ)
  rw [show (5 : ℚ) ^ 11 * Δ ^ 22 = 5 * ((5 : ℚ) ^ 5 * Δ ^ 11) ^ 2 by ring]
  exact nonsquare_mul_sq hfive ht

/-- The square class occurring in the discriminant of the seventh division polynomial is
nontrivial over `ℚ`. -/
theorem not_isSquare_seven_discriminant_shape {Δ : ℚ} (hΔ : Δ ≠ 0) :
    ¬ IsSquare (-((7 : ℚ) ^ 23 * Δ ^ 92)) := by
  have hnegseven : ¬ IsSquare (-7 : ℚ) := by norm_num
  have ht : (7 : ℚ) ^ 11 * Δ ^ 46 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 11 (by norm_num)) (pow_ne_zero 46 hΔ)
  rw [show -((7 : ℚ) ^ 23 * Δ ^ 92) =
    -7 * ((7 : ℚ) ^ 11 * Δ ^ 46) ^ 2 by ring]
  exact nonsquare_mul_sq hnegseven ht

/-- A rational polynomial with the fifth-division discriminant shape cannot split over `ℚ`. -/
theorem not_splits_of_discr_eq_five_shape {f : ℚ[X]} {Δ : ℚ}
    (hΔ : Δ ≠ 0)
    (hdiscr : f.discr = (5 : ℚ) ^ 11 * Δ ^ 22) :
    ¬ f.Splits := by
  intro hsplits
  apply not_isSquare_five_discriminant_shape hΔ
  rw [← hdiscr]
  exact isSquare_discr_of_splits hsplits

/-- A rational polynomial with the seventh-division discriminant shape cannot split over `ℚ`. -/
theorem not_splits_of_discr_eq_seven_shape {f : ℚ[X]} {Δ : ℚ}
    (hΔ : Δ ≠ 0)
    (hdiscr : f.discr = -((7 : ℚ) ^ 23 * Δ ^ 92)) :
    ¬ f.Splits := by
  intro hsplits
  apply not_isSquare_seven_discriminant_shape hΔ
  rw [← hdiscr]
  exact isSquare_discr_of_splits hsplits

/-- The fifth division polynomial cannot split once its classical discriminant identity is
available. This isolates that identity as the only missing polynomial calculation. -/
theorem fifth_division_polynomial_not_splits_of_discr
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (hdiscr :
      (W.preΨ' 5).discr = (5 : ℚ) ^ 11 * W.Δ ^ 22) :
    ¬ (W.preΨ' 5).Splits :=
  not_splits_of_discr_eq_five_shape W.isUnit_Δ.ne_zero hdiscr

/-- The seventh division polynomial cannot split once its classical discriminant identity is
available. This isolates that identity as the only missing polynomial calculation. -/
theorem seventh_division_polynomial_not_splits_of_discr
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (hdiscr :
      (W.preΨ' 7).discr = -((7 : ℚ) ^ 23 * W.Δ ^ 92)) :
    ¬ (W.preΨ' 7).Splits :=
  not_splits_of_discr_eq_seven_shape W.isUnit_Δ.ne_zero hdiscr

/-- The exact full-rational-`5`-torsion obstruction obtained from the two missing
division-polynomial inputs. -/
theorem not_injective_zmod_five_square_of_division_inputs
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (hroot : HasDivisionPolynomialRootCriterion W 5)
    (hdiscr :
      (W.preΨ' 5).discr = (5 : ℚ) ^ 11 * W.Δ ^ 22)
    (φ : (ZMod 5 × ZMod 5) →+ W.toAffine.Point) :
    ¬ Function.Injective φ := by
  intro hφ
  exact fifth_division_polynomial_not_splits_of_discr W hdiscr
    (fifth_division_polynomial_splits_of_full_torsion W hroot φ hφ)

/-- The exact full-rational-`7`-torsion obstruction obtained from the two missing
division-polynomial inputs. -/
theorem not_injective_zmod_seven_square_of_division_inputs
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (hroot : HasDivisionPolynomialRootCriterion W 7)
    (hdiscr :
      (W.preΨ' 7).discr = -((7 : ℚ) ^ 23 * W.Δ ^ 92))
    (φ : (ZMod 7 × ZMod 7) →+ W.toAffine.Point) :
    ¬ Function.Injective φ := by
  intro hφ
  exact seventh_division_polynomial_not_splits_of_discr W hdiscr
    (seventh_division_polynomial_splits_of_full_torsion W hroot φ hφ)

end MazurTorsion.OddPrimeFullTorsion

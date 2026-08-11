/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenHaoShift

/-!
# The quadratically shifted Hao function on `X₁(13)`

For `g = w-(X²+2X)`, this file proves the exact affine factorization

`(g) = I(0,1) I(-1,-1)⁴`.

The fourth-order multiplicity is proved through explicit powers of the point
ideal at `(-1,-1)`, using only the affine curve equation in the local
coordinates `z=X+1` and `t=Y+1`.  No divisor order is assumed.
-/

namespace MazurTorsion.XOneThirteenHaoQuadraticShift

open Ideal IsFractionRing Polynomial
open scoped nonZeroDivisors

open XOneThirteenMumford
open XOneThirteenPicard
open XOneThirteenPicard.CoordinateRing
open XOneThirteenHaoFunctions
open XOneThirteenHaoShift

noncomputable section

/-- The ordinate polynomial for `w-(X²+2X)`. -/
def quadraticShiftHaoPolynomial : ℚ[X] :=
  haoPolynomial + 2 * X ^ 2 + 4 * X

/-- The support polynomial predicted by its norm. -/
def quadraticShiftHaoSupport : ℚ[X] :=
  X * (X + 1) ^ 4

/-- The function `g = w-(X²+2X)`. -/
def haoWMinusQuadratic : CoordinateRing :=
  haoW - supportClass (X ^ 2 + 2 * X)

/-- The opposite factor `(Y+q(X))/2`. -/
def haoWMinusQuadraticOpposite : CoordinateRing :=
  halfClass * ordinateClass (-quadraticShiftHaoPolynomial)

/-- Local support coordinate `z=X+1` at `(-1,-1)`. -/
def negOneSupportPolynomial : ℚ[X] :=
  X + 1

/-- The contact ordinate `X`, equivalently `-1+(X+1)`. -/
def negOneContactPolynomial : ℚ[X] :=
  X

/-- The doubled cusp ideal at `(-1,-1)`. -/
def negOneDoubleIdeal : Ideal CoordinateRing :=
  mumfordIdeal (negOneSupportPolynomial ^ 2) negOneContactPolynomial

/-- The tripled cusp ideal at `(-1,-1)`. -/
def negOneTripleIdeal : Ideal CoordinateRing :=
  mumfordIdeal (negOneSupportPolynomial ^ 3) negOneContactPolynomial

/-- The quadrupled cusp ideal at `(-1,-1)`. -/
def negOneFourthIdeal : Ideal CoordinateRing :=
  mumfordIdeal (negOneSupportPolynomial ^ 4) quadraticShiftHaoPolynomial

/-- Exact norm certificate
`f-q² = -4 X(X+1)⁴`. -/
theorem quadraticShiftHaoPolynomial_norm_identity :
    sexticPolynomial - quadraticShiftHaoPolynomial ^ 2 =
      -(C 4 * quadraticShiftHaoSupport) := by
  apply Polynomial.funext
  intro x
  simp only [sexticPolynomial, quadraticShiftHaoPolynomial, haoPolynomial,
    quadraticShiftHaoSupport, eval_sub, eval_neg, eval_add, eval_mul,
    eval_pow, eval_X, eval_C, eval_one, eval_ofNat]
  ring

/-- `g` is one half of `Y-q(X)`. -/
theorem haoWMinusQuadratic_eq_half_ordinate :
    haoWMinusQuadratic =
      halfClass * ordinateClass quadraticShiftHaoPolynomial := by
  rw [haoWMinusQuadratic, haoW]
  calc
    halfClass * ordinateClass haoPolynomial -
        supportClass (X ^ 2 + 2 * X) =
      halfClass * ordinateClass haoPolynomial -
        (halfClass * 2) * supportClass (X ^ 2 + 2 * X) := by
      rw [halfClass_mul_two, one_mul]
    _ = halfClass *
        (ordinateClass haoPolynomial -
          2 * supportClass (X ^ 2 + 2 * X)) := by ring
    _ = halfClass * ordinateClass quadraticShiftHaoPolynomial := by
      simp only [quadraticShiftHaoPolynomial, ordinateClass, supportClass,
        map_add, map_mul, map_pow, map_ofNat]
      ring

/-- The product with the opposite factor is `-X(X+1)⁴`. -/
theorem haoWMinusQuadratic_mul_opposite :
    haoWMinusQuadratic * haoWMinusQuadraticOpposite =
      -supportClass quadraticShiftHaoSupport := by
  rw [haoWMinusQuadratic_eq_half_ordinate, haoWMinusQuadraticOpposite]
  calc
    halfClass * ordinateClass quadraticShiftHaoPolynomial *
        (halfClass * ordinateClass (-quadraticShiftHaoPolynomial)) =
      halfClass ^ 2 *
        (ordinateClass (-quadraticShiftHaoPolynomial) *
          ordinateClass quadraticShiftHaoPolynomial) := by
      ring
    _ = halfClass ^ 2 *
        algebraMap ℚ[X] CoordinateRing
          (sexticPolynomial - quadraticShiftHaoPolynomial ^ 2) := by
      rw [ordinateClass_neg_mul_ordinateClass]
    _ = halfClass ^ 2 *
        (-4 * supportClass quadraticShiftHaoSupport) := by
      rw [quadraticShiftHaoPolynomial_norm_identity, map_neg, map_mul]
      simp only [map_ofNat, supportClass]
      ring
    _ = -supportClass quadraticShiftHaoSupport := by
      calc
        halfClass ^ 2 * (-4 * supportClass quadraticShiftHaoSupport) =
            -(halfClass * 2) ^ 2 *
              supportClass quadraticShiftHaoSupport := by
          ring
        _ = -supportClass quadraticShiftHaoSupport := by
          rw [halfClass_mul_two]
          ring

/-! ## Exact local algebra at `(-1,-1)` -/

/-- The affine curve equation in `z=X+1`, `t=Y+1`. -/
theorem negOneLocalEquation :
    ordinateClass (C (-1)) ^ 2 - 2 * ordinateClass (C (-1)) =
      -2 * supportClass negOneSupportPolynomial +
        supportClass negOneSupportPolynomial ^ 2 -
        2 * supportClass negOneSupportPolynomial ^ 3 +
        6 * supportClass negOneSupportPolynomial ^ 4 -
        4 * supportClass negOneSupportPolynomial ^ 5 +
        supportClass negOneSupportPolynomial ^ 6 := by
  calc
    ordinateClass (C (-1)) ^ 2 - 2 * ordinateClass (C (-1)) =
        yCoordinate ^ 2 - 1 := by
      simp only [ordinateClass, map_neg, map_one]
      ring
    _ = algebraMap ℚ[X] CoordinateRing sexticPolynomial - 1 := by
      rw [yCoordinate_sq]
    _ = -2 * supportClass negOneSupportPolynomial +
        supportClass negOneSupportPolynomial ^ 2 -
        2 * supportClass negOneSupportPolynomial ^ 3 +
        6 * supportClass negOneSupportPolynomial ^ 4 -
        4 * supportClass negOneSupportPolynomial ^ 5 +
        supportClass negOneSupportPolynomial ^ 6 := by
      simp only [sexticPolynomial, negOneSupportPolynomial, supportClass,
        map_add, map_mul, map_pow, map_ofNat, map_one]
      ring

/-- In local coordinates, `Y-X = t-z`. -/
theorem negOneContactOrdinate_eq :
    ordinateClass negOneContactPolynomial =
      ordinateClass (C (-1)) -
        supportClass negOneSupportPolynomial := by
  simp only [negOneContactPolynomial, negOneSupportPolynomial,
    ordinateClass, supportClass, map_add, map_one]
  norm_num

/-- The degree-four contact polynomial is `X+(X+1)³`. -/
theorem quadraticShiftHaoPolynomial_eq_contact :
    quadraticShiftHaoPolynomial =
      negOneContactPolynomial + negOneSupportPolynomial ^ 3 := by
  simp only [quadraticShiftHaoPolynomial, haoPolynomial,
    negOneContactPolynomial, negOneSupportPolynomial]
  ring

theorem quadraticShiftOrdinate_eq_contact :
    ordinateClass quadraticShiftHaoPolynomial =
      ordinateClass negOneContactPolynomial -
        supportClass negOneSupportPolynomial ^ 3 := by
  rw [quadraticShiftHaoPolynomial_eq_contact]
  simp only [ordinateClass, supportClass, map_add, map_pow]
  ring

/-- Second-order cancellation at `(-1,-1)`. -/
theorem two_mul_negOneContactOrdinate_second :
    2 * ordinateClass negOneContactPolynomial =
      ordinateClass (C (-1)) ^ 2 -
        (supportClass negOneSupportPolynomial ^ 2 -
          2 * supportClass negOneSupportPolynomial ^ 3 +
          6 * supportClass negOneSupportPolynomial ^ 4 -
          4 * supportClass negOneSupportPolynomial ^ 5 +
          supportClass negOneSupportPolynomial ^ 6) := by
  have hcurve := negOneLocalEquation
  rw [negOneContactOrdinate_eq]
  linear_combination -hcurve

/-- Third-order cancellation at `(-1,-1)`. -/
theorem two_mul_negOneContactOrdinate_third :
    2 * ordinateClass negOneContactPolynomial =
      ordinateClass negOneContactPolynomial * ordinateClass (C (-1)) +
        supportClass negOneSupportPolynomial *
          ordinateClass negOneContactPolynomial +
        (2 * supportClass negOneSupportPolynomial ^ 3 -
          6 * supportClass negOneSupportPolynomial ^ 4 +
          4 * supportClass negOneSupportPolynomial ^ 5 -
          supportClass negOneSupportPolynomial ^ 6) := by
  have hcurve := negOneLocalEquation
  rw [negOneContactOrdinate_eq]
  linear_combination -hcurve

/-- Fourth-order cancellation at `(-1,-1)`. -/
theorem two_mul_quadraticShiftOrdinate :
    2 * ordinateClass quadraticShiftHaoPolynomial =
      ordinateClass negOneContactPolynomial * ordinateClass (C (-1)) +
        supportClass negOneSupportPolynomial *
          ordinateClass negOneContactPolynomial -
        (6 * supportClass negOneSupportPolynomial ^ 4 -
          4 * supportClass negOneSupportPolynomial ^ 5 +
          supportClass negOneSupportPolynomial ^ 6) := by
  rw [quadraticShiftOrdinate_eq_contact]
  have hthird := two_mul_negOneContactOrdinate_third
  linear_combination hthird

/-! ## Exact powers of `I(-1,-1)` -/

/-- First local thickening:
`I(-1,-1)² = ⟨(X+1)²,Y-X⟩`. -/
theorem cuspNegOneConjugatePointIdeal_sq :
    pointIdeal (-1) (-1) ^ 2 = negOneDoubleIdeal := by
  rw [pow_two, cuspNegOneConjugatePointIdeal_eq_mumfordIdeal,
    negOneDoubleIdeal, mumfordIdeal, mumfordIdeal,
    Ideal.span_pair_mul_span_pair]
  change Ideal.span
      {supportClass negOneSupportPolynomial *
          supportClass negOneSupportPolynomial,
        supportClass negOneSupportPolynomial * ordinateClass (C (-1)),
        ordinateClass (C (-1)) * supportClass negOneSupportPolynomial,
        ordinateClass (C (-1)) * ordinateClass (C (-1))} =
    Ideal.span
      {supportClass (negOneSupportPolynomial ^ 2),
        ordinateClass negOneContactPolynomial}
  rw [show supportClass (negOneSupportPolynomial ^ 2) =
      supportClass negOneSupportPolynomial ^ 2 by
    simp only [supportClass, map_pow]]
  let I₂ : Ideal CoordinateRing :=
    .span {supportClass negOneSupportPolynomial *
        supportClass negOneSupportPolynomial,
      supportClass negOneSupportPolynomial * ordinateClass (C (-1)),
      ordinateClass (C (-1)) * supportClass negOneSupportPolynomial,
      ordinateClass (C (-1)) * ordinateClass (C (-1))}
  let J₂ : Ideal CoordinateRing :=
    .span {supportClass negOneSupportPolynomial ^ 2,
      ordinateClass negOneContactPolynomial}
  change I₂ = J₂
  have hz2J : supportClass negOneSupportPolynomial ^ 2 ∈ J₂ := by
    exact Ideal.subset_span (by simp)
  have hdJ : ordinateClass negOneContactPolynomial ∈ J₂ := by
    exact Ideal.subset_span (by simp)
  have hztJ : supportClass negOneSupportPolynomial *
      ordinateClass (C (-1)) ∈ J₂ := by
    have hsum := J₂.add_mem
      (J₂.mul_mem_left (supportClass negOneSupportPolynomial) hdJ)
      hz2J
    convert hsum using 1
    rw [negOneContactOrdinate_eq]
    ring
  apply le_antisymm
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · change supportClass negOneSupportPolynomial *
          supportClass negOneSupportPolynomial ∈ J₂
      simpa only [pow_two] using hz2J
    · change supportClass negOneSupportPolynomial *
          ordinateClass (C (-1)) ∈ J₂
      exact hztJ
    · change ordinateClass (C (-1)) *
          supportClass negOneSupportPolynomial ∈ J₂
      simpa only [mul_comm] using hztJ
    · change ordinateClass (C (-1)) * ordinateClass (C (-1)) ∈ J₂
      have hsum := J₂.add_mem
        (J₂.mul_mem_left (ordinateClass (C (-1))) hdJ)
        hztJ
      convert hsum using 1
      rw [negOneContactOrdinate_eq]
      ring
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    have hz2I : supportClass negOneSupportPolynomial ^ 2 ∈ I₂ := by
      have hgen : supportClass negOneSupportPolynomial *
          supportClass negOneSupportPolynomial ∈ I₂ := by
        exact Ideal.subset_span (by simp)
      simpa only [pow_two] using hgen
    rcases hz with rfl | rfl
    · change supportClass negOneSupportPolynomial ^ 2 ∈ I₂
      exact hz2I
    · change ordinateClass negOneContactPolynomial ∈ I₂
      have ht2I : ordinateClass (C (-1)) ^ 2 ∈ I₂ := by
        have hgen : ordinateClass (C (-1)) * ordinateClass (C (-1)) ∈ I₂ := by
          exact Ideal.subset_span (by simp)
        simpa only [pow_two] using hgen
      have hrest :
          supportClass negOneSupportPolynomial ^ 2 -
              2 * supportClass negOneSupportPolynomial ^ 3 +
              6 * supportClass negOneSupportPolynomial ^ 4 -
              4 * supportClass negOneSupportPolynomial ^ 5 +
              supportClass negOneSupportPolynomial ^ 6 ∈ I₂ := by
        have hmultiple := I₂.mul_mem_right
          (1 - 2 * supportClass negOneSupportPolynomial +
            6 * supportClass negOneSupportPolynomial ^ 2 -
            4 * supportClass negOneSupportPolynomial ^ 3 +
            supportClass negOneSupportPolynomial ^ 4) hz2I
        convert hmultiple using 1
        ring
      have htwo : 2 * ordinateClass negOneContactPolynomial ∈ I₂ := by
        rw [two_mul_negOneContactOrdinate_second]
        exact I₂.sub_mem ht2I hrest
      have hscaled := I₂.mul_mem_left halfClass htwo
      have hscaleeq :
          halfClass * (2 * ordinateClass negOneContactPolynomial) =
            ordinateClass negOneContactPolynomial := by
        calc
          halfClass * (2 * ordinateClass negOneContactPolynomial) =
              (halfClass * 2) * ordinateClass negOneContactPolynomial := by
            ring
          _ = ordinateClass negOneContactPolynomial := by
            rw [halfClass_mul_two, one_mul]
      rw [← hscaleeq]
      exact hscaled

/-- Second local thickening:
`⟨(X+1)²,Y-X⟩ I(-1,-1) = ⟨(X+1)³,Y-X⟩`. -/
theorem negOneDoubleIdeal_mul_pointIdeal :
    negOneDoubleIdeal * pointIdeal (-1) (-1) = negOneTripleIdeal := by
  rw [negOneDoubleIdeal, negOneTripleIdeal,
    cuspNegOneConjugatePointIdeal_eq_mumfordIdeal,
    mumfordIdeal, mumfordIdeal, mumfordIdeal,
    Ideal.span_pair_mul_span_pair]
  change Ideal.span
      {supportClass (negOneSupportPolynomial ^ 2) *
          supportClass negOneSupportPolynomial,
        supportClass (negOneSupportPolynomial ^ 2) *
          ordinateClass (C (-1)),
        ordinateClass negOneContactPolynomial *
          supportClass negOneSupportPolynomial,
        ordinateClass negOneContactPolynomial * ordinateClass (C (-1))} =
    Ideal.span
      {supportClass (negOneSupportPolynomial ^ 3),
        ordinateClass negOneContactPolynomial}
  simp only [supportClass, map_pow]
  let I₃ : Ideal CoordinateRing :=
    .span {supportClass negOneSupportPolynomial ^ 2 *
        supportClass negOneSupportPolynomial,
      supportClass negOneSupportPolynomial ^ 2 * ordinateClass (C (-1)),
      ordinateClass negOneContactPolynomial *
        supportClass negOneSupportPolynomial,
      ordinateClass negOneContactPolynomial * ordinateClass (C (-1))}
  let J₃ : Ideal CoordinateRing :=
    .span {supportClass negOneSupportPolynomial ^ 3,
      ordinateClass negOneContactPolynomial}
  change I₃ = J₃
  have hz3J : supportClass negOneSupportPolynomial ^ 3 ∈ J₃ := by
    exact Ideal.subset_span (by simp)
  have hdJ : ordinateClass negOneContactPolynomial ∈ J₃ := by
    exact Ideal.subset_span (by simp)
  apply le_antisymm
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · change supportClass negOneSupportPolynomial ^ 2 *
          supportClass negOneSupportPolynomial ∈ J₃
      simpa only [pow_succ] using hz3J
    · change supportClass negOneSupportPolynomial ^ 2 *
          ordinateClass (C (-1)) ∈ J₃
      have hsum := J₃.add_mem
        (J₃.mul_mem_left (supportClass negOneSupportPolynomial ^ 2) hdJ)
        hz3J
      convert hsum using 1
      rw [negOneContactOrdinate_eq]
      ring
    · change ordinateClass negOneContactPolynomial *
          supportClass negOneSupportPolynomial ∈ J₃
      exact J₃.mul_mem_right (supportClass negOneSupportPolynomial) hdJ
    · change ordinateClass negOneContactPolynomial *
          ordinateClass (C (-1)) ∈ J₃
      exact J₃.mul_mem_right (ordinateClass (C (-1))) hdJ
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    have hz3I : supportClass negOneSupportPolynomial ^ 3 ∈ I₃ := by
      have hgen : supportClass negOneSupportPolynomial ^ 2 *
          supportClass negOneSupportPolynomial ∈ I₃ := by
        exact Ideal.subset_span (by simp)
      simpa only [pow_succ] using hgen
    rcases hz with rfl | rfl
    · change supportClass negOneSupportPolynomial ^ 3 ∈ I₃
      exact hz3I
    · change ordinateClass negOneContactPolynomial ∈ I₃
      have hdtI : ordinateClass negOneContactPolynomial *
          ordinateClass (C (-1)) ∈ I₃ := by
        exact Ideal.subset_span (by simp)
      have hdzI : ordinateClass negOneContactPolynomial *
          supportClass negOneSupportPolynomial ∈ I₃ := by
        exact Ideal.subset_span (by simp)
      have hhigh :
          2 * supportClass negOneSupportPolynomial ^ 3 -
              6 * supportClass negOneSupportPolynomial ^ 4 +
              4 * supportClass negOneSupportPolynomial ^ 5 -
              supportClass negOneSupportPolynomial ^ 6 ∈ I₃ := by
        have hmultiple := I₃.mul_mem_right
          (2 - 6 * supportClass negOneSupportPolynomial +
            4 * supportClass negOneSupportPolynomial ^ 2 -
            supportClass negOneSupportPolynomial ^ 3) hz3I
        convert hmultiple using 1
        ring
      have htwo : 2 * ordinateClass negOneContactPolynomial ∈ I₃ := by
        rw [two_mul_negOneContactOrdinate_third]
        have hzdI : supportClass negOneSupportPolynomial *
            ordinateClass negOneContactPolynomial ∈ I₃ := by
          simpa only [mul_comm] using hdzI
        exact I₃.add_mem (I₃.add_mem hdtI hzdI) hhigh
      have hscaled := I₃.mul_mem_left halfClass htwo
      have hscaleeq :
          halfClass * (2 * ordinateClass negOneContactPolynomial) =
            ordinateClass negOneContactPolynomial := by
        calc
          halfClass * (2 * ordinateClass negOneContactPolynomial) =
              (halfClass * 2) * ordinateClass negOneContactPolynomial := by
            ring
          _ = ordinateClass negOneContactPolynomial := by
            rw [halfClass_mul_two, one_mul]
      rw [← hscaleeq]
      exact hscaled

theorem cuspNegOneConjugatePointIdeal_cube :
    pointIdeal (-1) (-1) ^ 3 = negOneTripleIdeal := by
  rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ,
    cuspNegOneConjugatePointIdeal_sq, negOneDoubleIdeal_mul_pointIdeal]

/-- Third local thickening:
`⟨(X+1)³,Y-X⟩ I(-1,-1) = ⟨(X+1)⁴,Y-q⟩`. -/
theorem negOneTripleIdeal_mul_pointIdeal :
    negOneTripleIdeal * pointIdeal (-1) (-1) = negOneFourthIdeal := by
  rw [negOneTripleIdeal, negOneFourthIdeal,
    cuspNegOneConjugatePointIdeal_eq_mumfordIdeal,
    mumfordIdeal, mumfordIdeal, mumfordIdeal,
    Ideal.span_pair_mul_span_pair]
  change Ideal.span
      {supportClass (negOneSupportPolynomial ^ 3) *
          supportClass negOneSupportPolynomial,
        supportClass (negOneSupportPolynomial ^ 3) *
          ordinateClass (C (-1)),
        ordinateClass negOneContactPolynomial *
          supportClass negOneSupportPolynomial,
        ordinateClass negOneContactPolynomial * ordinateClass (C (-1))} =
    Ideal.span
      {supportClass (negOneSupportPolynomial ^ 4),
        ordinateClass quadraticShiftHaoPolynomial}
  simp only [supportClass, map_pow]
  let I₄ : Ideal CoordinateRing :=
    .span {supportClass negOneSupportPolynomial ^ 3 *
        supportClass negOneSupportPolynomial,
      supportClass negOneSupportPolynomial ^ 3 * ordinateClass (C (-1)),
      ordinateClass negOneContactPolynomial *
        supportClass negOneSupportPolynomial,
      ordinateClass negOneContactPolynomial * ordinateClass (C (-1))}
  let J₄ : Ideal CoordinateRing :=
    .span {supportClass negOneSupportPolynomial ^ 4,
      ordinateClass quadraticShiftHaoPolynomial}
  change I₄ = J₄
  have hz4J : supportClass negOneSupportPolynomial ^ 4 ∈ J₄ := by
    exact Ideal.subset_span (by simp)
  have heJ : ordinateClass quadraticShiftHaoPolynomial ∈ J₄ := by
    exact Ideal.subset_span (by simp)
  have hz3tJ : supportClass negOneSupportPolynomial ^ 3 *
      ordinateClass (C (-1)) ∈ J₄ := by
    have hfirst := J₄.mul_mem_left
      (supportClass negOneSupportPolynomial ^ 3) heJ
    have hsecond := hz4J
    have hthird := J₄.mul_mem_right
      (supportClass negOneSupportPolynomial ^ 2) hz4J
    have hsum := J₄.add_mem (J₄.add_mem hfirst hsecond) hthird
    convert hsum using 1
    rw [quadraticShiftOrdinate_eq_contact, negOneContactOrdinate_eq]
    ring
  have hdzJ : ordinateClass negOneContactPolynomial *
      supportClass negOneSupportPolynomial ∈ J₄ := by
    have hfirst := J₄.mul_mem_right
      (supportClass negOneSupportPolynomial) heJ
    have hsum := J₄.add_mem hfirst hz4J
    convert hsum using 1
    rw [quadraticShiftOrdinate_eq_contact]
    ring
  apply le_antisymm
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · change supportClass negOneSupportPolynomial ^ 3 *
          supportClass negOneSupportPolynomial ∈ J₄
      simpa only [pow_succ] using hz4J
    · change supportClass negOneSupportPolynomial ^ 3 *
          ordinateClass (C (-1)) ∈ J₄
      exact hz3tJ
    · change ordinateClass negOneContactPolynomial *
          supportClass negOneSupportPolynomial ∈ J₄
      exact hdzJ
    · change ordinateClass negOneContactPolynomial *
          ordinateClass (C (-1)) ∈ J₄
      have hfirst := J₄.mul_mem_left (ordinateClass (C (-1))) heJ
      have hsum := J₄.add_mem hfirst hz3tJ
      convert hsum using 1
      rw [quadraticShiftOrdinate_eq_contact]
      ring
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    have hz4I : supportClass negOneSupportPolynomial ^ 4 ∈ I₄ := by
      have hgen : supportClass negOneSupportPolynomial ^ 3 *
          supportClass negOneSupportPolynomial ∈ I₄ := by
        exact Ideal.subset_span (by simp)
      simpa only [pow_succ] using hgen
    rcases hz with rfl | rfl
    · change supportClass negOneSupportPolynomial ^ 4 ∈ I₄
      exact hz4I
    · change ordinateClass quadraticShiftHaoPolynomial ∈ I₄
      have hdtI : ordinateClass negOneContactPolynomial *
          ordinateClass (C (-1)) ∈ I₄ := by
        exact Ideal.subset_span (by simp)
      have hdzI : ordinateClass negOneContactPolynomial *
          supportClass negOneSupportPolynomial ∈ I₄ := by
        exact Ideal.subset_span (by simp)
      have hrest :
          6 * supportClass negOneSupportPolynomial ^ 4 -
              4 * supportClass negOneSupportPolynomial ^ 5 +
              supportClass negOneSupportPolynomial ^ 6 ∈ I₄ := by
        have hmultiple := I₄.mul_mem_right
          (6 - 4 * supportClass negOneSupportPolynomial +
            supportClass negOneSupportPolynomial ^ 2) hz4I
        convert hmultiple using 1
        ring
      have htwo :
          2 * ordinateClass quadraticShiftHaoPolynomial ∈ I₄ := by
        rw [two_mul_quadraticShiftOrdinate]
        have hzdI : supportClass negOneSupportPolynomial *
            ordinateClass negOneContactPolynomial ∈ I₄ := by
          simpa only [mul_comm] using hdzI
        exact I₄.sub_mem (I₄.add_mem hdtI hzdI) hrest
      have hscaled := I₄.mul_mem_left halfClass htwo
      have hscaleeq :
          halfClass * (2 * ordinateClass quadraticShiftHaoPolynomial) =
            ordinateClass quadraticShiftHaoPolynomial := by
        calc
          halfClass * (2 * ordinateClass quadraticShiftHaoPolynomial) =
              (halfClass * 2) *
                ordinateClass quadraticShiftHaoPolynomial := by ring
          _ = ordinateClass quadraticShiftHaoPolynomial := by
            rw [halfClass_mul_two, one_mul]
      rw [← hscaleeq]
      exact hscaled

/-- Exact fourth power of the cusp ideal at `(-1,-1)`. -/
theorem cuspNegOneConjugatePointIdeal_fourth :
    pointIdeal (-1) (-1) ^ 4 = negOneFourthIdeal := by
  rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ,
    cuspNegOneConjugatePointIdeal_cube, negOneTripleIdeal_mul_pointIdeal]

/-! ## Global affine factorization -/

theorem cuspZeroPointIdeal_eq_mumfordIdeal :
    pointIdeal 0 1 = mumfordIdeal X (C 1) := by
  rw [cuspZeroPointIdeal_eq_span]
  rfl

theorem zeroSupport_isCoprime_negOneSupportFourth :
    IsCoprime (X : ℚ[X]) (negOneSupportPolynomial ^ 4) := by
  have hlinear :
      IsCoprime (X - C (0 : ℚ)) (X - C (-1 : ℚ)) := by
    apply isCoprime_X_sub_C_of_isUnit_sub
    norm_num
  have hpow := hlinear.pow_right (n := 4)
  norm_num [negOneSupportPolynomial] at hpow ⊢
  exact hpow

theorem quadraticShiftHao_sub_one :
    quadraticShiftHaoPolynomial - C 1 =
      X * (X ^ 2 + 3 * X + 4) := by
  simp [quadraticShiftHaoPolynomial, haoPolynomial]
  ring

/-- Composition of `I(0,1)` with the fourth thickening at `(-1,-1)`. -/
theorem cuspZeroPointIdeal_mul_negOneFourthIdeal :
    pointIdeal 0 1 * negOneFourthIdeal =
      mumfordIdeal quadraticShiftHaoSupport quadraticShiftHaoPolynomial := by
  rw [cuspZeroPointIdeal_eq_mumfordIdeal, negOneFourthIdeal]
  change mumfordIdeal X (C 1) *
      mumfordIdeal (negOneSupportPolynomial ^ 4)
        quadraticShiftHaoPolynomial =
    mumfordIdeal (X * negOneSupportPolynomial ^ 4)
      quadraticShiftHaoPolynomial
  apply mumfordIdeal_mul_of_coprime_support
      zeroSupport_isCoprime_negOneSupportFourth
  · rw [quadraticShiftHao_sub_one]
    exact ⟨X ^ 2 + 3 * X + 4, rfl⟩
  · simp

/-- Clearing the denominator in `g`. -/
theorem two_mul_haoWMinusQuadratic :
    (2 : CoordinateRing) * haoWMinusQuadratic =
      ordinateClass quadraticShiftHaoPolynomial := by
  rw [haoWMinusQuadratic_eq_half_ordinate]
  calc
    (2 : CoordinateRing) *
        (halfClass * ordinateClass quadraticShiftHaoPolynomial) =
      (halfClass * 2) * ordinateClass quadraticShiftHaoPolynomial := by ring
    _ = ordinateClass quadraticShiftHaoPolynomial := by
      rw [halfClass_mul_two, one_mul]

/-- The thick-support ideal is the principal ideal of `g`. -/
theorem span_haoWMinusQuadratic_eq_mumfordIdeal :
    Ideal.span {haoWMinusQuadratic} =
      mumfordIdeal quadraticShiftHaoSupport quadraticShiftHaoPolynomial := by
  rw [mumfordIdeal]
  apply le_antisymm
  · rw [Ideal.span_singleton_le_iff_mem,
      haoWMinusQuadratic_eq_half_ordinate]
    exact (Ideal.span
      {supportClass quadraticShiftHaoSupport,
        ordinateClass quadraticShiftHaoPolynomial}).mul_mem_left halfClass
          (Ideal.subset_span (by simp))
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · have hproduct := (Ideal.span {haoWMinusQuadratic}).mul_mem_right
          haoWMinusQuadraticOpposite
          (Ideal.mem_span_singleton_self haoWMinusQuadratic)
      rw [haoWMinusQuadratic_mul_opposite] at hproduct
      change supportClass quadraticShiftHaoSupport ∈
        Ideal.span {haoWMinusQuadratic}
      simpa only [neg_neg] using
        (Ideal.span {haoWMinusQuadratic}).neg_mem hproduct
    · rw [← two_mul_haoWMinusQuadratic]
      exact (Ideal.span {haoWMinusQuadratic}).mul_mem_left 2
        (Ideal.mem_span_singleton_self haoWMinusQuadratic)

/-- Exact integral factorization
`(g) = I(0,1) I(-1,-1)⁴`. -/
theorem span_haoWMinusQuadratic_eq_pointIdealProduct :
    Ideal.span {haoWMinusQuadratic} =
      pointIdeal 0 1 * pointIdeal (-1) (-1) ^ 4 := by
  rw [cuspNegOneConjugatePointIdeal_fourth,
    cuspZeroPointIdeal_mul_negOneFourthIdeal]
  exact span_haoWMinusQuadratic_eq_mumfordIdeal

/-- Fractional-ideal form of
`(g) = I(0,1) I(-1,-1)⁴`. -/
theorem fractionalIdeal_haoWMinusQuadratic_eq_pointProduct :
    FractionalIdeal.spanSingleton CoordinateRing⁰
        (algebraMap CoordinateRing FractionField haoWMinusQuadratic) =
      pointFractionalIdeal 0 1 *
        pointFractionalIdeal (-1) (-1) ^ 4 := by
  simp only [pointFractionalIdeal]
  rw [← FractionalIdeal.coeIdeal_pow,
    ← FractionalIdeal.coeIdeal_mul,
    ← span_haoWMinusQuadratic_eq_pointIdealProduct,
    FractionalIdeal.coeIdeal_span_singleton]

/-- Class-group consumer:
`[I(0,1)] + 4[I(-1,-1)] = 0`. -/
theorem cuspZeroClass_mul_cuspNegOneConjugateClass_fourth :
    cuspZeroClass * cuspNegOneConjugateClass ^ 4 = 1 := by
  simp only [cuspZeroClass, cuspNegOneConjugateClass, pointClass]
  rw [← map_pow, ← map_mul]
  apply (ClassGroup.mk_eq_one_iff).2
  change ((pointFractionalIdeal 0 1 *
      pointFractionalIdeal (-1) (-1) ^ 4 :
        FractionalIdeal CoordinateRing⁰ FractionField) :
      Submodule CoordinateRing FractionField).IsPrincipal
  rw [← fractionalIdeal_haoWMinusQuadratic_eq_pointProduct,
    FractionalIdeal.coe_spanSingleton]
  exact ⟨⟨_, rfl⟩⟩

end

end MazurTorsion.XOneThirteenHaoQuadraticShift

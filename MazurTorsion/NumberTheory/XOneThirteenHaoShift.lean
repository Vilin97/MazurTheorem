/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenHaoFunctions

/-!
# The higher-multiplicity Hao function on `X₁(13)`

This file proves, entirely inside the explicit affine coordinate ring, the
higher-multiplicity factorization

`(w - X) = I(0,1)³ I(-1,-1)`.

The multiplicity three at `(0,1)` is not assumed.  It is established by two
checked ideal identities obtained from the affine curve equation:

* `I(0,1)² = ⟨X², Y-(1+2X)⟩`;
* `I(0,1)³ = ⟨X³, Y-(1+2X+X²)⟩`.

The resulting thickened cusp ideal is then composed with `I(-1,-1)` using
the coprime-support ideal lemma.  No divisor-order or projective Jacobian
claim is used.
-/

namespace MazurTorsion.XOneThirteenHaoShift

open Ideal IsFractionRing Polynomial
open scoped nonZeroDivisors

open XOneThirteenMumford
open XOneThirteenPicard
open XOneThirteenPicard.CoordinateRing
open XOneThirteenHaoFunctions

noncomputable section

/-- The ordinate polynomial for `w-X`. -/
def shiftedHaoPolynomial : ℚ[X] :=
  haoPolynomial + 2 * X

/-- The support polynomial predicted by the norm of `w-X`. -/
def shiftedHaoSupport : ℚ[X] :=
  X ^ 3 * (X + 1)

/-- The function `w-X` in the affine coordinate ring. -/
def haoWMinusX : CoordinateRing :=
  haoW - supportClass X

/-- The opposite factor `(Y + (X³+X²+2X+1))/2`. -/
def haoWMinusXOpposite : CoordinateRing :=
  halfClass * ordinateClass (-shiftedHaoPolynomial)

/-- The degree-two contact ordinate at `(0,1)`. -/
def doubleCuspOrdinatePolynomial : ℚ[X] :=
  C 1 + 2 * X

/-- The degree-three contact ordinate at `(0,1)`. -/
def tripleCuspOrdinatePolynomial : ℚ[X] :=
  C 1 + 2 * X + X ^ 2

/-- The explicit doubled affine cusp ideal. -/
def cuspDoubleIdeal : Ideal CoordinateRing :=
  mumfordIdeal (X ^ 2) doubleCuspOrdinatePolynomial

/-- The explicit tripled affine cusp ideal. -/
def cuspTripleIdeal : Ideal CoordinateRing :=
  mumfordIdeal (X ^ 3) tripleCuspOrdinatePolynomial

/-- Exact polynomial norm certificate
`f-(p+2X)² = -4 X³(X+1)`. -/
theorem shiftedHaoPolynomial_norm_identity :
    sexticPolynomial - shiftedHaoPolynomial ^ 2 =
      -(C 4 * shiftedHaoSupport) := by
  apply Polynomial.funext
  intro x
  simp only [sexticPolynomial, shiftedHaoPolynomial, haoPolynomial,
    shiftedHaoSupport, eval_sub, eval_neg, eval_add, eval_mul, eval_pow,
    eval_X, eval_C, eval_one, eval_ofNat]
  ring

/-- `w-X` is one half of `Y-(p+2X)`. -/
theorem haoWMinusX_eq_half_ordinate :
    haoWMinusX = halfClass * ordinateClass shiftedHaoPolynomial := by
  rw [haoWMinusX, haoW]
  calc
    halfClass * ordinateClass haoPolynomial - supportClass X =
        halfClass * ordinateClass haoPolynomial -
          (halfClass * 2) * supportClass X := by
      rw [halfClass_mul_two, one_mul]
    _ = halfClass *
        (ordinateClass haoPolynomial - 2 * supportClass X) := by ring
    _ = halfClass * ordinateClass shiftedHaoPolynomial := by
      simp only [shiftedHaoPolynomial, ordinateClass, supportClass,
        map_add, map_mul, map_ofNat]
      ring

/-- The product with the opposite factor is `-X³(X+1)`. -/
theorem haoWMinusX_mul_opposite :
    haoWMinusX * haoWMinusXOpposite =
      -supportClass shiftedHaoSupport := by
  rw [haoWMinusX_eq_half_ordinate, haoWMinusXOpposite]
  calc
    halfClass * ordinateClass shiftedHaoPolynomial *
        (halfClass * ordinateClass (-shiftedHaoPolynomial)) =
      halfClass ^ 2 *
        (ordinateClass (-shiftedHaoPolynomial) *
          ordinateClass shiftedHaoPolynomial) := by
      ring
    _ = halfClass ^ 2 *
        algebraMap ℚ[X] CoordinateRing
          (sexticPolynomial - shiftedHaoPolynomial ^ 2) := by
      rw [ordinateClass_neg_mul_ordinateClass]
    _ = halfClass ^ 2 * (-4 * supportClass shiftedHaoSupport) := by
      rw [shiftedHaoPolynomial_norm_identity, map_neg, map_mul]
      simp only [map_ofNat, supportClass]
      ring
    _ = -supportClass shiftedHaoSupport := by
      calc
        halfClass ^ 2 * (-4 * supportClass shiftedHaoSupport) =
            -(halfClass * 2) ^ 2 * supportClass shiftedHaoSupport := by
          ring
        _ = -supportClass shiftedHaoSupport := by
          rw [halfClass_mul_two]
          ring

/-! ## Checked local multiplicity at `(0,1)` -/

/-- The affine curve equation expanded at `(0,1)`, with
`t = Y-1` and `x = X`. -/
theorem cuspLocalEquation :
    ordinateClass (C 1) ^ 2 + 2 * ordinateClass (C 1) =
      4 * supportClass X + 6 * supportClass X ^ 2 +
        2 * supportClass X ^ 3 + supportClass X ^ 4 +
        2 * supportClass X ^ 5 + supportClass X ^ 6 := by
  calc
    ordinateClass (C 1) ^ 2 + 2 * ordinateClass (C 1) =
        yCoordinate ^ 2 - 1 := by
      simp only [ordinateClass, map_one]
      ring
    _ = algebraMap ℚ[X] CoordinateRing sexticPolynomial - 1 := by
      rw [yCoordinate_sq]
    _ = 4 * supportClass X + 6 * supportClass X ^ 2 +
        2 * supportClass X ^ 3 + supportClass X ^ 4 +
        2 * supportClass X ^ 5 + supportClass X ^ 6 := by
      simp only [sexticPolynomial, supportClass, map_add, map_mul, map_pow,
        map_ofNat, map_one]
      ring

/-- The exact second-order cancellation identity at `(0,1)`. -/
theorem two_mul_doubleCuspOrdinate :
    2 * ordinateClass doubleCuspOrdinatePolynomial =
      6 * supportClass X ^ 2 + 2 * supportClass X ^ 3 +
        supportClass X ^ 4 + 2 * supportClass X ^ 5 +
        supportClass X ^ 6 - ordinateClass (C 1) ^ 2 := by
  have hcurve := cuspLocalEquation
  simp only [doubleCuspOrdinatePolynomial, ordinateClass, map_add, map_mul,
    map_ofNat, map_one, supportClass] at hcurve ⊢
  linear_combination hcurve

/-- The exact third-order cancellation identity at `(0,1)`. -/
theorem two_mul_tripleCuspOrdinate :
    2 * ordinateClass tripleCuspOrdinatePolynomial =
      (2 * supportClass X ^ 3 + supportClass X ^ 4 +
          2 * supportClass X ^ 5 + supportClass X ^ 6) -
        ordinateClass doubleCuspOrdinatePolynomial * ordinateClass (C 1) -
        2 * supportClass X * ordinateClass doubleCuspOrdinatePolynomial := by
  have hcurve := cuspLocalEquation
  simp only [doubleCuspOrdinatePolynomial, tripleCuspOrdinatePolynomial,
    ordinateClass, map_add, map_mul, map_pow, map_ofNat, map_one,
    supportClass] at hcurve ⊢
  linear_combination hcurve

theorem doubleCuspOrdinate_eq :
    ordinateClass doubleCuspOrdinatePolynomial =
      ordinateClass (C 1) - 2 * supportClass X := by
  simp only [doubleCuspOrdinatePolynomial, ordinateClass, supportClass,
    map_add, map_mul, map_ofNat]
  ring

theorem tripleCuspOrdinate_eq :
    ordinateClass tripleCuspOrdinatePolynomial =
      ordinateClass doubleCuspOrdinatePolynomial - supportClass X ^ 2 := by
  simp only [doubleCuspOrdinatePolynomial, tripleCuspOrdinatePolynomial,
    ordinateClass, supportClass, map_add, map_mul, map_pow, map_ofNat]
  ring

theorem cuspZeroPointIdeal_eq_span :
    pointIdeal 0 1 =
      Ideal.span {supportClass X, ordinateClass (C 1)} := by
  simp only [pointIdeal, xClass, yClass, supportClass, ordinateClass]
  norm_num

/-- First local multiplicity identity:
`I(0,1)² = ⟨X²,Y-(1+2X)⟩`. -/
theorem cuspZeroPointIdeal_sq :
    pointIdeal 0 1 ^ 2 = cuspDoubleIdeal := by
  rw [pow_two, cuspZeroPointIdeal_eq_span, cuspDoubleIdeal, mumfordIdeal,
    Ideal.span_pair_mul_span_pair]
  rw [show supportClass (X ^ 2) = supportClass X ^ 2 by
    simp only [supportClass, map_pow]]
  let I₂ : Ideal CoordinateRing :=
    .span {supportClass X * supportClass X,
      supportClass X * ordinateClass (C 1),
      ordinateClass (C 1) * supportClass X,
      ordinateClass (C 1) * ordinateClass (C 1)}
  let J₂ : Ideal CoordinateRing :=
    .span {supportClass X ^ 2,
      ordinateClass doubleCuspOrdinatePolynomial}
  change I₂ = J₂
  have hx2J : supportClass X ^ 2 ∈ J₂ := by
    exact Ideal.subset_span (by simp)
  have hdJ : ordinateClass doubleCuspOrdinatePolynomial ∈ J₂ := by
    exact Ideal.subset_span (by simp)
  have hxtJ : supportClass X * ordinateClass (C 1) ∈ J₂ := by
    have hsum := J₂.add_mem
      (J₂.mul_mem_left (supportClass X) hdJ)
      (J₂.mul_mem_left 2 hx2J)
    convert hsum using 1
    rw [doubleCuspOrdinate_eq]
    ring
  apply le_antisymm
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · change supportClass X * supportClass X ∈ J₂
      simpa only [pow_two] using hx2J
    · change supportClass X * ordinateClass (C 1) ∈ J₂
      exact hxtJ
    · change ordinateClass (C 1) * supportClass X ∈ J₂
      simpa only [mul_comm] using hxtJ
    · change ordinateClass (C 1) * ordinateClass (C 1) ∈ J₂
      have hsum := J₂.add_mem
        (J₂.mul_mem_left (ordinateClass (C 1)) hdJ)
        (J₂.mul_mem_left 2 hxtJ)
      convert hsum using 1
      rw [doubleCuspOrdinate_eq]
      ring
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    have hx2I : supportClass X ^ 2 ∈ I₂ := by
      have hgen : supportClass X * supportClass X ∈ I₂ := by
        exact Ideal.subset_span (by simp)
      simpa only [pow_two] using hgen
    rcases hz with rfl | rfl
    · change supportClass X ^ 2 ∈ I₂
      exact hx2I
    · change ordinateClass doubleCuspOrdinatePolynomial ∈ I₂
      have ht2I : ordinateClass (C 1) ^ 2 ∈ I₂ := by
        have hgen : ordinateClass (C 1) * ordinateClass (C 1) ∈ I₂ := by
          exact Ideal.subset_span (by simp)
        simpa only [pow_two] using hgen
      have hhigh :
          6 * supportClass X ^ 2 + 2 * supportClass X ^ 3 +
              supportClass X ^ 4 + 2 * supportClass X ^ 5 +
              supportClass X ^ 6 ∈ I₂ := by
        have hmultiple := I₂.mul_mem_right
          (6 + 2 * supportClass X + supportClass X ^ 2 +
            2 * supportClass X ^ 3 + supportClass X ^ 4) hx2I
        convert hmultiple using 1
        ring
      have htwo :
          2 * ordinateClass doubleCuspOrdinatePolynomial ∈ I₂ := by
        rw [two_mul_doubleCuspOrdinate]
        exact I₂.sub_mem hhigh ht2I
      have hscaled := I₂.mul_mem_left halfClass htwo
      have hscaleeq :
        halfClass * (2 * ordinateClass doubleCuspOrdinatePolynomial) =
          ordinateClass doubleCuspOrdinatePolynomial := by
        calc
          halfClass * (2 * ordinateClass doubleCuspOrdinatePolynomial) =
            (halfClass * 2) *
              ordinateClass doubleCuspOrdinatePolynomial := by ring
          _ = ordinateClass doubleCuspOrdinatePolynomial := by
            rw [halfClass_mul_two, one_mul]
      rw [← hscaleeq]
      exact hscaled

theorem tripleCuspOrdinate_eq_expanded :
    ordinateClass tripleCuspOrdinatePolynomial =
      ordinateClass (C 1) - 2 * supportClass X - supportClass X ^ 2 := by
  rw [tripleCuspOrdinate_eq, doubleCuspOrdinate_eq]

/-- Second local multiplicity identity:
`⟨X²,Y-(1+2X)⟩ I(0,1) = ⟨X³,Y-(1+2X+X²)⟩`. -/
theorem cuspDoubleIdeal_mul_cuspZeroPointIdeal :
    cuspDoubleIdeal * pointIdeal 0 1 = cuspTripleIdeal := by
  rw [cuspDoubleIdeal, cuspTripleIdeal, cuspZeroPointIdeal_eq_span,
    mumfordIdeal, mumfordIdeal, Ideal.span_pair_mul_span_pair]
  rw [show supportClass (X ^ 2) = supportClass X ^ 2 by
      simp only [supportClass, map_pow],
    show supportClass (X ^ 3) = supportClass X ^ 3 by
      simp only [supportClass, map_pow]]
  let I₃ : Ideal CoordinateRing :=
    .span {supportClass X ^ 2 * supportClass X,
      supportClass X ^ 2 * ordinateClass (C 1),
      ordinateClass doubleCuspOrdinatePolynomial * supportClass X,
      ordinateClass doubleCuspOrdinatePolynomial * ordinateClass (C 1)}
  let J₃ : Ideal CoordinateRing :=
    .span {supportClass X ^ 3,
      ordinateClass tripleCuspOrdinatePolynomial}
  change I₃ = J₃
  have hx3J : supportClass X ^ 3 ∈ J₃ := by
    exact Ideal.subset_span (by simp)
  have hd3J : ordinateClass tripleCuspOrdinatePolynomial ∈ J₃ := by
    exact Ideal.subset_span (by simp)
  have hx2tJ : supportClass X ^ 2 * ordinateClass (C 1) ∈ J₃ := by
    have hfirst := J₃.mul_mem_left (supportClass X ^ 2) hd3J
    have hsecond := J₃.mul_mem_left 2 hx3J
    have hthird := J₃.mul_mem_right (supportClass X) hx3J
    have hsum := J₃.add_mem (J₃.add_mem hfirst hsecond) hthird
    convert hsum using 1
    rw [tripleCuspOrdinate_eq_expanded]
    ring
  have hd2xJ :
      ordinateClass doubleCuspOrdinatePolynomial * supportClass X ∈ J₃ := by
    have hfirst := J₃.mul_mem_right (supportClass X) hd3J
    have hsum := J₃.add_mem hfirst hx3J
    convert hsum using 1
    rw [tripleCuspOrdinate_eq]
    ring
  apply le_antisymm
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · change supportClass X ^ 2 * supportClass X ∈ J₃
      simpa only [pow_succ] using hx3J
    · change supportClass X ^ 2 * ordinateClass (C 1) ∈ J₃
      exact hx2tJ
    · change ordinateClass doubleCuspOrdinatePolynomial * supportClass X ∈ J₃
      exact hd2xJ
    · change ordinateClass doubleCuspOrdinatePolynomial *
          ordinateClass (C 1) ∈ J₃
      have hfirst := J₃.mul_mem_left (ordinateClass (C 1)) hd3J
      have hsum := J₃.add_mem hfirst hx2tJ
      convert hsum using 1
      rw [tripleCuspOrdinate_eq]
      ring
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    have hx3I : supportClass X ^ 3 ∈ I₃ := by
      have hgen : supportClass X ^ 2 * supportClass X ∈ I₃ := by
        exact Ideal.subset_span (by simp)
      simpa only [pow_succ] using hgen
    rcases hz with rfl | rfl
    · change supportClass X ^ 3 ∈ I₃
      exact hx3I
    · change ordinateClass tripleCuspOrdinatePolynomial ∈ I₃
      have hd2tI : ordinateClass doubleCuspOrdinatePolynomial *
          ordinateClass (C 1) ∈ I₃ := by
        exact Ideal.subset_span (by simp)
      have hd2xI : ordinateClass doubleCuspOrdinatePolynomial *
          supportClass X ∈ I₃ := by
        exact Ideal.subset_span (by simp)
      have hhigh :
          2 * supportClass X ^ 3 + supportClass X ^ 4 +
              2 * supportClass X ^ 5 + supportClass X ^ 6 ∈ I₃ := by
        have hmultiple := I₃.mul_mem_right
          (2 + supportClass X + 2 * supportClass X ^ 2 +
            supportClass X ^ 3) hx3I
        convert hmultiple using 1
        ring
      have htwo : 2 * ordinateClass tripleCuspOrdinatePolynomial ∈ I₃ := by
        rw [two_mul_tripleCuspOrdinate]
        have h2xd : 2 * supportClass X *
            ordinateClass doubleCuspOrdinatePolynomial ∈ I₃ := by
          convert I₃.mul_mem_left 2 hd2xI using 1
          ring
        exact I₃.sub_mem (I₃.sub_mem hhigh hd2tI)
          h2xd
      have hscaled := I₃.mul_mem_left halfClass htwo
      have hscaleeq :
          halfClass * (2 * ordinateClass tripleCuspOrdinatePolynomial) =
            ordinateClass tripleCuspOrdinatePolynomial := by
        calc
          halfClass * (2 * ordinateClass tripleCuspOrdinatePolynomial) =
              (halfClass * 2) *
                ordinateClass tripleCuspOrdinatePolynomial := by ring
          _ = ordinateClass tripleCuspOrdinatePolynomial := by
            rw [halfClass_mul_two, one_mul]
      rw [← hscaleeq]
      exact hscaled

/-- The exact thickened-cusp identity `I(0,1)³ = cuspTripleIdeal`. -/
theorem cuspZeroPointIdeal_cube :
    pointIdeal 0 1 ^ 3 = cuspTripleIdeal := by
  rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ,
    cuspZeroPointIdeal_sq, cuspDoubleIdeal_mul_cuspZeroPointIdeal]

/-! ## Composition with the conjugate cusp at `X=-1` -/

theorem cuspNegOneConjugatePointIdeal_eq_mumfordIdeal :
    pointIdeal (-1) (-1) = mumfordIdeal (X + 1) (C (-1)) := by
  simp only [pointIdeal, mumfordIdeal, xClass, yClass, supportClass,
    ordinateClass]
  norm_num

theorem shiftedHao_sub_tripleCuspOrdinate :
    shiftedHaoPolynomial - tripleCuspOrdinatePolynomial = X ^ 3 := by
  simp [shiftedHaoPolynomial, haoPolynomial,
    tripleCuspOrdinatePolynomial]
  ring

theorem shiftedHao_sub_neg_one :
    shiftedHaoPolynomial - C (-1) = (X + 1) * (X ^ 2 + 2) := by
  simp only [shiftedHaoPolynomial, haoPolynomial]
  norm_num
  ring

theorem cubeSupport_isCoprime_negOneSupport :
    IsCoprime (X ^ 3 : ℚ[X]) (X + 1) := by
  have hlinear :
      IsCoprime (X - C (0 : ℚ)) (X - C (-1 : ℚ)) := by
    apply isCoprime_X_sub_C_of_isUnit_sub
    norm_num
  have hpow := hlinear.pow_left (m := 3)
  norm_num at hpow ⊢
  exact hpow

/-- The tripled cusp ideal composes with `I(-1,-1)` to the thick support of
`w-X`. -/
theorem cuspTripleIdeal_mul_cuspNegOneConjugatePointIdeal :
    cuspTripleIdeal * pointIdeal (-1) (-1) =
      mumfordIdeal shiftedHaoSupport shiftedHaoPolynomial := by
  rw [cuspTripleIdeal, cuspNegOneConjugatePointIdeal_eq_mumfordIdeal]
  change mumfordIdeal (X ^ 3) tripleCuspOrdinatePolynomial *
      mumfordIdeal (X + 1) (C (-1)) =
    mumfordIdeal (X ^ 3 * (X + 1)) shiftedHaoPolynomial
  apply mumfordIdeal_mul_of_coprime_support
      cubeSupport_isCoprime_negOneSupport
  · rw [shiftedHao_sub_tripleCuspOrdinate]
  · rw [shiftedHao_sub_neg_one]
    exact ⟨X ^ 2 + 2, rfl⟩

/-- Clearing the denominator in `w-X`. -/
theorem two_mul_haoWMinusX :
    (2 : CoordinateRing) * haoWMinusX =
      ordinateClass shiftedHaoPolynomial := by
  rw [haoWMinusX_eq_half_ordinate]
  calc
    (2 : CoordinateRing) *
        (halfClass * ordinateClass shiftedHaoPolynomial) =
      (halfClass * 2) * ordinateClass shiftedHaoPolynomial := by ring
    _ = ordinateClass shiftedHaoPolynomial := by
      rw [halfClass_mul_two, one_mul]

/-- The generalized thick-support ideal is exactly the principal ideal of
`w-X`. -/
theorem span_haoWMinusX_eq_shiftedMumfordIdeal :
    Ideal.span {haoWMinusX} =
      mumfordIdeal shiftedHaoSupport shiftedHaoPolynomial := by
  rw [mumfordIdeal]
  apply le_antisymm
  · rw [Ideal.span_singleton_le_iff_mem, haoWMinusX_eq_half_ordinate]
    exact (Ideal.span
      {supportClass shiftedHaoSupport,
        ordinateClass shiftedHaoPolynomial}).mul_mem_left halfClass
          (Ideal.subset_span (by simp))
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · have hproduct := (Ideal.span {haoWMinusX}).mul_mem_right
          haoWMinusXOpposite (Ideal.mem_span_singleton_self haoWMinusX)
      rw [haoWMinusX_mul_opposite] at hproduct
      change supportClass shiftedHaoSupport ∈ Ideal.span {haoWMinusX}
      simpa only [neg_neg] using
        (Ideal.span {haoWMinusX}).neg_mem hproduct
    · rw [← two_mul_haoWMinusX]
      exact (Ideal.span {haoWMinusX}).mul_mem_left 2
        (Ideal.mem_span_singleton_self haoWMinusX)

/-- Exact integral ideal factorization
`(w-X) = I(0,1)³ I(-1,-1)`. -/
theorem span_haoWMinusX_eq_pointIdealProduct :
    Ideal.span {haoWMinusX} =
      pointIdeal 0 1 ^ 3 * pointIdeal (-1) (-1) := by
  rw [cuspZeroPointIdeal_cube,
    cuspTripleIdeal_mul_cuspNegOneConjugatePointIdeal]
  exact span_haoWMinusX_eq_shiftedMumfordIdeal

/-- Fractional-ideal form of
`(w-X) = I(0,1)³ I(-1,-1)`. -/
theorem fractionalIdeal_haoWMinusX_eq_pointProduct :
    FractionalIdeal.spanSingleton CoordinateRing⁰
        (algebraMap CoordinateRing FractionField haoWMinusX) =
      pointFractionalIdeal 0 1 ^ 3 *
        pointFractionalIdeal (-1) (-1) := by
  simp only [pointFractionalIdeal]
  rw [← FractionalIdeal.coeIdeal_pow,
    ← FractionalIdeal.coeIdeal_mul,
    ← span_haoWMinusX_eq_pointIdealProduct,
    FractionalIdeal.coeIdeal_span_singleton]

private theorem cuspNegOneConjugate_isAffinePoint :
    IsAffinePoint (-1) (-1) := by
  norm_num [IsAffinePoint, sexticPolynomial]

/-- The affine Picard class of the cusp `(-1,-1)`. -/
noncomputable def cuspNegOneConjugateClass : ClassGroup CoordinateRing :=
  pointClass (-1) (-1) cuspNegOneConjugate_isAffinePoint (by norm_num)

/-- Named class-group consumer of the higher-multiplicity factorization:
`3[I(0,1)] + [I(-1,-1)] = 0`. -/
theorem cuspZeroClass_cube_mul_cuspNegOneConjugateClass :
    cuspZeroClass ^ 3 * cuspNegOneConjugateClass = 1 := by
  simp only [cuspZeroClass, cuspNegOneConjugateClass, pointClass]
  rw [← map_pow, ← map_mul]
  apply (ClassGroup.mk_eq_one_iff).2
  change ((pointFractionalIdeal 0 1 ^ 3 *
      pointFractionalIdeal (-1) (-1) :
        FractionalIdeal CoordinateRing⁰ FractionField) :
      Submodule CoordinateRing FractionField).IsPrincipal
  rw [← fractionalIdeal_haoWMinusX_eq_pointProduct,
    FractionalIdeal.coe_spanSingleton]
  exact ⟨⟨_, rfl⟩⟩

end

end MazurTorsion.XOneThirteenHaoShift

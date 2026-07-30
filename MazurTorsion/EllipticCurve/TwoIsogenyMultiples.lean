/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.EllipticCurve.TwoIsogeny
import MazurTorsion.GroupTheory.IndependentCyclicGenerators

/-!
# Fixed-multiple compatibility for the explicit two-isogeny

This file derives the compatibility of `pointMapFun` with small fixed
multiples.  The key observation for doubling is that the composite in the
opposite order is another instance of the already proved composite formula,
after replacing `(a,b)` by `(-2a,a²-4b)`.
-/

open WeierstrassCurve

namespace MazurTorsion.TwoIsogeny

open WeierstrassCurve.Affine

noncomputable local instance transformedSource_isElliptic
    (a b : ℚ) [(sourceCurve a b).IsElliptic] :
    (sourceCurve (-2 * a) (a ^ 2 - 4 * b)).IsElliptic := by
  change (targetCurve a b).IsElliptic
  infer_instance

private def targetAsTransformedSource (a b : ℚ) :
    (targetCurve a b).toAffine.Point →
      (sourceCurve (-2 * a) (a ^ 2 - 4 * b)).toAffine.Point
  | .zero => .zero
  | .some X Y h =>
      .some X Y (by simpa [sourceCurve, targetCurve] using h)

private lemma targetAsTransformedSource_eq (a b : ℚ)
    (Q : (targetCurve a b).toAffine.Point) :
    targetAsTransformedSource a b Q = Q := by
  cases Q <;> rfl

private lemma pointMapFun_dualPointMapFun_eq_transformed_comp
    {a b : ℚ} [(sourceCurve a b).IsElliptic]
    (Q : (targetCurve a b).toAffine.Point) :
    targetAsTransformedSource a b
        (pointMapFun a b (dualPointMapFun a b Q)) =
      dualPointMapFun (-2 * a) (a ^ 2 - 4 * b)
        (pointMapFun (-2 * a) (a ^ 2 - 4 * b)
          (targetAsTransformedSource a b Q)) := by
  cases Q with
  | zero => rfl
  | some X Y h =>
      by_cases hX : X = 0
      · subst X
        have hY : Y = 0 :=
          target_y_eq_zero_of_x_eq_zero h rfl
        subst Y
        rfl
      · have h' :
            (sourceCurve (-2 * a) (a ^ 2 - 4 * b)).toAffine.Nonsingular
              X Y := by
          simpa [sourceCurve, targetCurve] using h
        by_cases hY : Y = 0
        · subst Y
          rw [dualPointMapFun_some_of_ne h hX]
          simp [targetAsTransformedSource, dualMapX, pointMapFun,
            dualPointMapFun, mapX, hX]
        · have hmapX : mapX X Y ≠ 0 :=
            div_ne_zero (pow_ne_zero 2 hY) (pow_ne_zero 2 hX)
          have hdualX : dualMapX X Y ≠ 0 :=
            div_ne_zero (pow_ne_zero 2 hY)
              (mul_ne_zero (by norm_num) (pow_ne_zero 2 hX))
          rw [dualPointMapFun_some_of_ne h hX,
            pointMapFun_some_of_ne _ hdualX,
            show pointMapFun (-2 * a) (a ^ 2 - 4 * b)
                (targetAsTransformedSource a b
                  (.some X Y h)) =
                .some (mapX X Y) (mapY (a ^ 2 - 4 * b) X Y) _ by
              simpa only [targetAsTransformedSource] using
                pointMapFun_some_of_ne h' hX,
            dualPointMapFun_some_of_ne _ hmapX]
          simp only [targetAsTransformedSource, Point.some.injEq]
          constructor <;>
            simp only [mapX, mapY, dualMapX, dualMapY] <;>
            field_simp [hX, hY] <;>
            ring

theorem pointMapFun_comp_dualPointMapFun {a b : ℚ}
    [(sourceCurve a b).IsElliptic]
    (Q : (targetCurve a b).toAffine.Point) :
    pointMapFun a b (dualPointMapFun a b Q) =
      (2 : ℕ) • Q := by
  have hcomp :=
    pointMapFun_dualPointMapFun_eq_transformed_comp Q
  rw [dualPointMapFun_comp_pointMapFun] at hcomp
  rw [targetAsTransformedSource_eq a b _,
    targetAsTransformedSource_eq a b Q] at hcomp
  exact hcomp

theorem pointMapFun_two_nsmul {a b : ℚ}
    [(sourceCurve a b).IsElliptic]
    (P : (sourceCurve a b).toAffine.Point) :
    pointMapFun a b ((2 : ℕ) • P) =
      (2 : ℕ) • pointMapFun a b P := by
  rw [← dualPointMapFun_comp_pointMapFun P,
    pointMapFun_comp_dualPointMapFun]

theorem dualPointMapFun_two_nsmul {a b : ℚ}
    [(sourceCurve a b).IsElliptic]
    (Q : (targetCurve a b).toAffine.Point) :
    dualPointMapFun a b ((2 : ℕ) • Q) =
      (2 : ℕ) • dualPointMapFun a b Q := by
  rw [← pointMapFun_comp_dualPointMapFun Q,
    dualPointMapFun_comp_pointMapFun]

theorem pointMapFun_pow_two_nsmul {a b : ℚ}
    [(sourceCurve a b).IsElliptic]
    (n : ℕ) (P : (sourceCurve a b).toAffine.Point) :
    pointMapFun a b ((2 ^ n : ℕ) • P) =
      (2 ^ n : ℕ) • pointMapFun a b P := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpow : (2 ^ (n + 1) : ℕ) = 2 * 2 ^ n := by
        rw [pow_succ, Nat.mul_comm]
      calc
        pointMapFun a b ((2 ^ (n + 1) : ℕ) • P) =
            pointMapFun a b
              ((2 : ℕ) • ((2 ^ n : ℕ) • P)) := by
          rw [hpow, mul_nsmul]
          rw [← mul_nsmul, ← mul_nsmul, Nat.mul_comm]
        _ = (2 : ℕ) •
            pointMapFun a b ((2 ^ n : ℕ) • P) :=
          pointMapFun_two_nsmul _
        _ = (2 : ℕ) •
            ((2 ^ n : ℕ) • pointMapFun a b P) :=
          congrArg ((2 : ℕ) • ·) ih
        _ = (2 ^ (n + 1) : ℕ) • pointMapFun a b P := by
          rw [hpow, mul_nsmul]
          rw [← mul_nsmul, ← mul_nsmul, Nat.mul_comm]

theorem dualPointMapFun_pow_two_nsmul {a b : ℚ}
    [(sourceCurve a b).IsElliptic]
    (n : ℕ) (Q : (targetCurve a b).toAffine.Point) :
    dualPointMapFun a b ((2 ^ n : ℕ) • Q) =
      (2 ^ n : ℕ) • dualPointMapFun a b Q := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hpow : (2 ^ (n + 1) : ℕ) = 2 * 2 ^ n := by
        rw [pow_succ, Nat.mul_comm]
      calc
        dualPointMapFun a b ((2 ^ (n + 1) : ℕ) • Q) =
            dualPointMapFun a b
              ((2 : ℕ) • ((2 ^ n : ℕ) • Q)) := by
          rw [hpow, mul_nsmul]
          rw [← mul_nsmul, ← mul_nsmul, Nat.mul_comm]
        _ = (2 : ℕ) •
            dualPointMapFun a b ((2 ^ n : ℕ) • Q) :=
          dualPointMapFun_two_nsmul _
        _ = (2 : ℕ) •
            ((2 ^ n : ℕ) • dualPointMapFun a b Q) :=
          congrArg ((2 : ℕ) • ·) ih
        _ = (2 ^ (n + 1) : ℕ) • dualPointMapFun a b Q := by
          rw [hpow, mul_nsmul]
          rw [← mul_nsmul, ← mul_nsmul, Nat.mul_comm]

lemma sourceOrigin_ne_zero (a b : ℚ)
    [(sourceCurve a b).IsElliptic] :
    sourceOrigin a b ≠ 0 :=
  Point.some_ne_zero _

lemma targetOrigin_ne_zero (a b : ℚ)
    [(sourceCurve a b).IsElliptic] :
    targetOrigin a b ≠ 0 :=
  Point.some_ne_zero _

private lemma nsmul_ne_zero_of_addOrderOf_eq
    {G : Type*} [AddGroup G] {P : G} {n m : ℕ}
    (horder : addOrderOf P = n) (hndvd : ¬n ∣ m) :
    m • P ≠ 0 := by
  intro hm
  apply hndvd
  rw [← horder]
  exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hm

/-- Doubling compatibility already extracts the order-five and full
two-torsion data needed in the order-twenty branch.  No compatibility with
odd multiples is required. -/
theorem order_twenty_image_data {a b : ℚ}
    [(sourceCurve a b).IsElliptic]
    (Q : (sourceCurve a b).toAffine.Point)
    (hQ : addOrderOf Q = 20)
    (hmid : (10 : ℕ) • Q = sourceOrigin a b) :
    (2 : ℕ) • pointMapFun a b ((5 : ℕ) • Q) = 0 ∧
      pointMapFun a b ((5 : ℕ) • Q) ≠ 0 ∧
      pointMapFun a b ((5 : ℕ) • Q) ≠ targetOrigin a b ∧
      addOrderOf
          ((3 : ℕ) • pointMapFun a b ((4 : ℕ) • Q)) = 5 := by
  have h10Q :
      (10 : ℕ) • Q ≠ 0 :=
    nsmul_ne_zero_of_addOrderOf_eq hQ (by norm_num)
  have h20Q : (20 : ℕ) • Q = 0 := by
    rw [← hQ]
    exact addOrderOf_nsmul_eq_zero Q
  let S := pointMapFun a b ((5 : ℕ) • Q)
  let A := pointMapFun a b ((4 : ℕ) • Q)
  have hS_two : (2 : ℕ) • S = 0 := by
    calc
      (2 : ℕ) • S =
          pointMapFun a b ((2 : ℕ) • ((5 : ℕ) • Q)) :=
        (pointMapFun_two_nsmul _).symm
      _ = pointMapFun a b ((10 : ℕ) • Q) := by
        congr 1
        rw [← mul_nsmul]
      _ = pointMapFun a b (sourceOrigin a b) := by rw [hmid]
      _ = 0 := pointMapFun_sourceOrigin a b
  have hS_ne : S ≠ 0 := by
    intro hS
    have hkilled :
        (2 : ℕ) • ((5 : ℕ) • Q) = 0 :=
      pointMapFun_kernel_killed_by_two hS
    apply h10Q
    rw [← mul_nsmul] at hkilled
    norm_num at hkilled
    exact hkilled
  have hS_origin : S ≠ targetOrigin a b := by
    intro hS
    dsimp [S] at hS
    apply h10Q
    calc
      (10 : ℕ) • Q =
          (2 : ℕ) • ((5 : ℕ) • Q) := by
        rw [← mul_nsmul]
      _ = dualPointMapFun a b
          (pointMapFun a b ((5 : ℕ) • Q)) :=
        (dualPointMapFun_comp_pointMapFun _).symm
      _ = dualPointMapFun a b (targetOrigin a b) := by rw [hS]
      _ = 0 := dualPointMapFun_targetOrigin a b
  have h16A : (16 : ℕ) • A = A := by
    calc
      (16 : ℕ) • A =
          pointMapFun a b ((16 : ℕ) • ((4 : ℕ) • Q)) := by
        simpa only [show (16 : ℕ) = 2 ^ 4 by norm_num] using
          (pointMapFun_pow_two_nsmul 4 ((4 : ℕ) • Q)).symm
      _ = pointMapFun a b ((64 : ℕ) • Q) := by
        congr 1
      _ = pointMapFun a b ((4 : ℕ) • Q) := by
        rw [nsmul_eq_mod_nsmul 64 h20Q]
      _ = A := rfl
  have h15A : (15 : ℕ) • A = 0 := by
    rw [show (15 : ℕ) • A = (16 : ℕ) • A - A by abel,
      h16A, sub_self]
  have hthreeA : (3 : ℕ) • A ≠ 0 := by
    intro hthree
    have hfour : (4 : ℕ) • A = A := by
      rw [show (4 : ℕ) • A = (3 : ℕ) • A + A by abel,
        hthree, zero_add]
    have hdual_four :
        (4 : ℕ) • dualPointMapFun a b A =
          dualPointMapFun a b A := by
      calc
        (4 : ℕ) • dualPointMapFun a b A =
            dualPointMapFun a b ((4 : ℕ) • A) := by
          simpa only [show (4 : ℕ) = 2 ^ 2 by norm_num] using
            (dualPointMapFun_pow_two_nsmul 2 A).symm
        _ = dualPointMapFun a b A := by rw [hfour]
    have hdualA :
        dualPointMapFun a b A = (8 : ℕ) • Q := by
      calc
        dualPointMapFun a b A =
            (2 : ℕ) • ((4 : ℕ) • Q) :=
          dualPointMapFun_comp_pointMapFun _
        _ = (8 : ℕ) • Q := by
          rw [← mul_nsmul]
    have h32eq8 : (32 : ℕ) • Q = (8 : ℕ) • Q := by
      calc
        (32 : ℕ) • Q =
            (4 : ℕ) • ((8 : ℕ) • Q) := by
          rw [← mul_nsmul]
        _ = (4 : ℕ) • dualPointMapFun a b A := by rw [hdualA]
        _ = dualPointMapFun a b A := hdual_four
        _ = (8 : ℕ) • Q := hdualA
    have h24Q : (24 : ℕ) • Q = 0 := by
      rw [show (24 : ℕ) • Q =
          (32 : ℕ) • Q - (8 : ℕ) • Q by abel,
        h32eq8, sub_self]
    have hdvd : addOrderOf Q ∣ 24 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mpr h24Q
    rw [hQ] at hdvd
    norm_num at hdvd
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have horder_five : addOrderOf ((3 : ℕ) • A) = 5 := by
    apply addOrderOf_eq_prime
    · rw [← mul_nsmul]
      norm_num
      exact h15A
    · exact hthreeA
  exact ⟨hS_two, hS_ne, hS_origin, horder_five⟩

/-- In the order-twenty-four branch, doubling alone produces two distinct
nonzero target two-torsion points, a half of one of them, and a point of
exact order three.  These are precisely the point data used by the
completed `C₂ × C₁₂` obstruction. -/
theorem order_twenty_four_image_data {a b : ℚ}
    [(sourceCurve a b).IsElliptic]
    (Q : (sourceCurve a b).toAffine.Point)
    (hQ : addOrderOf Q = 24)
    (hmid : (12 : ℕ) • Q = sourceOrigin a b) :
    (2 : ℕ) • pointMapFun a b ((6 : ℕ) • Q) = 0 ∧
      pointMapFun a b ((6 : ℕ) • Q) ≠ 0 ∧
      pointMapFun a b ((6 : ℕ) • Q) ≠ targetOrigin a b ∧
      (2 : ℕ) • pointMapFun a b ((3 : ℕ) • Q) =
        pointMapFun a b ((6 : ℕ) • Q) ∧
      addOrderOf (pointMapFun a b ((3 : ℕ) • Q)) = 4 ∧
      addOrderOf (pointMapFun a b ((8 : ℕ) • Q)) = 3 := by
  have h12Q :
      (12 : ℕ) • Q ≠ 0 :=
    nsmul_ne_zero_of_addOrderOf_eq hQ (by norm_num)
  have h16Q :
      (16 : ℕ) • Q ≠ 0 :=
    nsmul_ne_zero_of_addOrderOf_eq hQ (by norm_num)
  have h24Q : (24 : ℕ) • Q = 0 := by
    rw [← hQ]
    exact addOrderOf_nsmul_eq_zero Q
  let S := pointMapFun a b ((6 : ℕ) • Q)
  let B := pointMapFun a b ((3 : ℕ) • Q)
  let A := pointMapFun a b ((8 : ℕ) • Q)
  have hS_two : (2 : ℕ) • S = 0 := by
    calc
      (2 : ℕ) • S =
          pointMapFun a b ((2 : ℕ) • ((6 : ℕ) • Q)) :=
        (pointMapFun_two_nsmul _).symm
      _ = pointMapFun a b ((12 : ℕ) • Q) := by
        congr 1
        rw [← mul_nsmul]
      _ = pointMapFun a b (sourceOrigin a b) := by rw [hmid]
      _ = 0 := pointMapFun_sourceOrigin a b
  have hS_ne : S ≠ 0 := by
    intro hS
    have hkilled :
        (2 : ℕ) • ((6 : ℕ) • Q) = 0 :=
      pointMapFun_kernel_killed_by_two hS
    apply h12Q
    rw [← mul_nsmul] at hkilled
    norm_num at hkilled
    exact hkilled
  have hS_origin : S ≠ targetOrigin a b := by
    intro hS
    dsimp [S] at hS
    apply h12Q
    calc
      (12 : ℕ) • Q =
          (2 : ℕ) • ((6 : ℕ) • Q) := by
        rw [← mul_nsmul]
      _ = dualPointMapFun a b
          (pointMapFun a b ((6 : ℕ) • Q)) :=
        (dualPointMapFun_comp_pointMapFun _).symm
      _ = dualPointMapFun a b (targetOrigin a b) := by rw [hS]
      _ = 0 := dualPointMapFun_targetOrigin a b
  have hB_double : (2 : ℕ) • B = S := by
    calc
      (2 : ℕ) • B =
          pointMapFun a b ((2 : ℕ) • ((3 : ℕ) • Q)) :=
        (pointMapFun_two_nsmul _).symm
      _ = pointMapFun a b ((6 : ℕ) • Q) := by
        congr 1
        rw [← mul_nsmul]
      _ = S := rfl
  have hB_four : (4 : ℕ) • B = 0 := by
    calc
      (4 : ℕ) • B = (2 : ℕ) • ((2 : ℕ) • B) := by
        rw [← mul_nsmul]
      _ = (2 : ℕ) • S := by rw [hB_double]
      _ = 0 := hS_two
  have hB_two_ne : (2 : ℕ) • B ≠ 0 := by
    rw [hB_double]
    exact hS_ne
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have horder_B : addOrderOf B = 4 := by
    simpa using
      (addOrderOf_eq_prime_pow (p := 2) (n := 1)
        hB_two_ne hB_four)
  have hA_ne : A ≠ 0 := by
    intro hA
    have hkilled :
        (2 : ℕ) • ((8 : ℕ) • Q) = 0 :=
      pointMapFun_kernel_killed_by_two hA
    apply h16Q
    rw [← mul_nsmul] at hkilled
    norm_num at hkilled
    exact hkilled
  have h4A : (4 : ℕ) • A = A := by
    calc
      (4 : ℕ) • A =
          pointMapFun a b ((4 : ℕ) • ((8 : ℕ) • Q)) := by
        simpa only [show (4 : ℕ) = 2 ^ 2 by norm_num] using
          (pointMapFun_pow_two_nsmul 2 ((8 : ℕ) • Q)).symm
      _ = pointMapFun a b ((32 : ℕ) • Q) := by
        congr 1
      _ = pointMapFun a b ((8 : ℕ) • Q) := by
        rw [nsmul_eq_mod_nsmul 32 h24Q]
      _ = A := rfl
  have h3A : (3 : ℕ) • A = 0 := by
    rw [show (3 : ℕ) • A = (4 : ℕ) • A - A by abel,
      h4A, sub_self]
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have horder_A : addOrderOf A = 3 :=
    addOrderOf_eq_prime h3A hA_ne
  exact
    ⟨hS_two, hS_ne, hS_origin, hB_double, horder_B,
      horder_A⟩

/-- A source point of order twenty whose midpoint is the isogeny kernel
produces a target point of exact order ten.  The visible target
two-torsion point is independent of its cyclic subgroup. -/
theorem exists_order_ten_image_independent {a b : ℚ}
    [(sourceCurve a b).IsElliptic]
    (Q : (sourceCurve a b).toAffine.Point)
    (hQ : addOrderOf Q = 20)
    (hmid : (10 : ℕ) • Q = sourceOrigin a b) :
    ∃ C : (targetCurve a b).toAffine.Point,
      addOrderOf C = 10 ∧
        targetOrigin a b ∉ AddSubgroup.zmultiples C := by
  let S := pointMapFun a b ((5 : ℕ) • Q)
  let R := (3 : ℕ) • pointMapFun a b ((4 : ℕ) • Q)
  have hdata := order_twenty_image_data Q hQ hmid
  change (2 : ℕ) • S = 0 ∧ S ≠ 0 ∧
    S ≠ targetOrigin a b ∧ addOrderOf R = 5 at hdata
  rcases hdata with ⟨hS_two, hS_ne, hS_origin, hR_order⟩
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hS_order : addOrderOf S = 2 :=
    addOrderOf_eq_prime hS_two hS_ne
  have hT_two : (2 : ℕ) • targetOrigin a b = 0 := by
    simpa only [two_nsmul] using targetOrigin_add_self a b
  have hT_order : addOrderOf (targetOrigin a b) = 2 :=
    addOrderOf_eq_prime hT_two (targetOrigin_ne_zero a b)
  let C := S + R
  have hcoprime :
      Nat.Coprime (addOrderOf S) (addOrderOf R) := by
    rw [hS_order, hR_order]
    norm_num
  have hC_order : addOrderOf C = 10 := by
    calc
      addOrderOf C = addOrderOf S * addOrderOf R :=
        AddCommute.addOrderOf_add_eq_mul_addOrderOf_of_coprime
          (AddCommute.all S R) hcoprime
      _ = 10 := by rw [hS_order, hR_order]
  have hfiveS : (5 : ℕ) • S = S := by
    simpa using nsmul_eq_mod_nsmul 5 hS_two
  have hfiveR : (5 : ℕ) • R = 0 := by
    rw [← hR_order]
    exact addOrderOf_nsmul_eq_zero R
  have hhalf : (5 : ℕ) • C = S := by
    dsimp only [C]
    rw [nsmul_add, hfiveS, hfiveR, add_zero]
  refine ⟨C, hC_order, ?_⟩
  apply
    IndependentCyclicGenerators.orderTwo_not_mem_zmultiples
      (targetOrigin a b) C 5 hT_order
  · simpa using hC_order
  · rw [hhalf]
    exact hS_origin.symm

/-- A source point of order twenty-four whose midpoint is the isogeny
kernel produces a target point of exact order twelve.  Again the visible
target two-torsion point lies outside the generated cyclic subgroup. -/
theorem exists_order_twelve_image_independent {a b : ℚ}
    [(sourceCurve a b).IsElliptic]
    (Q : (sourceCurve a b).toAffine.Point)
    (hQ : addOrderOf Q = 24)
    (hmid : (12 : ℕ) • Q = sourceOrigin a b) :
    ∃ C : (targetCurve a b).toAffine.Point,
      addOrderOf C = 12 ∧
        targetOrigin a b ∉ AddSubgroup.zmultiples C := by
  let S := pointMapFun a b ((6 : ℕ) • Q)
  let B := pointMapFun a b ((3 : ℕ) • Q)
  let A := pointMapFun a b ((8 : ℕ) • Q)
  have hdata := order_twenty_four_image_data Q hQ hmid
  change (2 : ℕ) • S = 0 ∧ S ≠ 0 ∧
    S ≠ targetOrigin a b ∧ (2 : ℕ) • B = S ∧
      addOrderOf B = 4 ∧ addOrderOf A = 3 at hdata
  rcases hdata with
    ⟨hS_two, hS_ne, hS_origin, hB_double, hB_order, hA_order⟩
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hT_two : (2 : ℕ) • targetOrigin a b = 0 := by
    simpa only [two_nsmul] using targetOrigin_add_self a b
  have hT_order : addOrderOf (targetOrigin a b) = 2 :=
    addOrderOf_eq_prime hT_two (targetOrigin_ne_zero a b)
  let C := B + A
  have hcoprime :
      Nat.Coprime (addOrderOf B) (addOrderOf A) := by
    rw [hB_order, hA_order]
    norm_num
  have hC_order : addOrderOf C = 12 := by
    calc
      addOrderOf C = addOrderOf B * addOrderOf A :=
        AddCommute.addOrderOf_add_eq_mul_addOrderOf_of_coprime
          (AddCommute.all B A) hcoprime
      _ = 12 := by rw [hB_order, hA_order]
  have hB_four : (4 : ℕ) • B = 0 := by
    rw [← hB_order]
    exact addOrderOf_nsmul_eq_zero B
  have hA_three : (3 : ℕ) • A = 0 := by
    rw [← hA_order]
    exact addOrderOf_nsmul_eq_zero A
  have hsixB : (6 : ℕ) • B = (2 : ℕ) • B := by
    simpa using nsmul_eq_mod_nsmul 6 hB_four
  have hsixA : (6 : ℕ) • A = 0 := by
    simpa using nsmul_eq_mod_nsmul 6 hA_three
  have hhalf : (6 : ℕ) • C = S := by
    dsimp only [C]
    rw [nsmul_add, hsixB, hsixA, hB_double, add_zero]
  refine ⟨C, hC_order, ?_⟩
  apply
    IndependentCyclicGenerators.orderTwo_not_mem_zmultiples
      (targetOrigin a b) C 6 hT_order
  · simpa using hC_order
  · rw [hhalf]
    exact hS_origin.symm

end MazurTorsion.TwoIsogeny

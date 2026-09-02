/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.EllipticCurve.DoublingCoordinates
import MazurTorsion.Kubert.OrderFiveIsogeny
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Doubling compatibility for the order-five Vélu map

The full binary addition law is more than the order-twenty-five descent
needs.  This file instead checks the homogeneous polynomial identities that
make the explicit Vélu map commute with tangent doubling.  Together with
kernel-translation invariance, this is enough to prove that the image of an
order-twenty-five division point has exact order five.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.Kubert

/-- Product of the two affine kernel-pole factors. -/
def orderFiveKernelPolynomial (c x : ℚ) : ℚ :=
  x * (x - c)

/-- Cleared numerator of the Vélu abscissa. -/
def orderFiveVeluXNumerator (c x : ℚ) : ℚ :=
  x ^ 5 - 2 * c * x ^ 4 + (c ^ 3 + 3 * c ^ 2 - c) * x ^ 3 +
    (-3 * c ^ 3 + 3 * c ^ 2) * x ^ 2 +
    (c ^ 4 - 3 * c ^ 3) * x + c ^ 4

/-- Cleared numerator of the Vélu completed-ordinate multiplier. -/
def orderFiveVeluDifferentialNumerator (c x : ℚ) : ℚ :=
  x ^ 6 - 3 * c * x ^ 5 + (-c ^ 3 + c ^ 2 + c) * x ^ 4 +
    (-c ^ 4 + 3 * c ^ 3 - 5 * c ^ 2) * x ^ 3 +
    (-3 * c ^ 4 + 9 * c ^ 3) * x ^ 2 +
    (c ^ 5 - 7 * c ^ 4) * x + 2 * c ^ 5

/-- Cleared abscissa formula. -/
theorem orderFiveVeluX_eq_div
    {c x : ℚ} (hx0 : x ≠ 0) (hxc : x ≠ c) :
    orderFiveVeluX c x =
      orderFiveVeluXNumerator c x /
        orderFiveKernelPolynomial c x ^ 2 := by
  simp only [orderFiveVeluX, orderFiveVeluXNumerator,
    orderFiveKernelPolynomial]
  field_simp [hx0, sub_ne_zero.mpr hxc]
  ring

/-- Cleared differential formula. -/
theorem orderFiveVeluDifferential_eq_div
    {c x : ℚ} (hx0 : x ≠ 0) (hxc : x ≠ c) :
    orderFiveVeluDifferential c x =
      orderFiveVeluDifferentialNumerator c x /
        orderFiveKernelPolynomial c x ^ 3 := by
  simp only [orderFiveVeluDifferential,
    orderFiveVeluDifferentialNumerator, orderFiveKernelPolynomial]
  field_simp [hx0, sub_ne_zero.mpr hxc]
  ring

/-- Degree-five homogenization of the cleared Vélu abscissa. -/
def orderFiveVeluXNumeratorHomogeneous
    {R : Type*} [CommRing R] (c u v : R) : R :=
  u ^ 5 - 2 * c * u ^ 4 * v +
    (c ^ 3 + 3 * c ^ 2 - c) * u ^ 3 * v ^ 2 +
    (-3 * c ^ 3 + 3 * c ^ 2) * u ^ 2 * v ^ 3 +
    (c ^ 4 - 3 * c ^ 3) * u * v ^ 4 + c ^ 4 * v ^ 5

/-- Degree-six homogenization of the cleared differential numerator. -/
def orderFiveVeluDifferentialNumeratorHomogeneous
    {R : Type*} [CommRing R] (c u v : R) : R :=
  u ^ 6 - 3 * c * u ^ 5 * v +
    (-c ^ 3 + c ^ 2 + c) * u ^ 4 * v ^ 2 +
    (-c ^ 4 + 3 * c ^ 3 - 5 * c ^ 2) * u ^ 3 * v ^ 3 +
    (-3 * c ^ 4 + 9 * c ^ 3) * u ^ 2 * v ^ 4 +
    (c ^ 5 - 7 * c ^ 4) * u * v ^ 5 + 2 * c ^ 5 * v ^ 6

@[simp] theorem orderFiveVeluXNumeratorHomogeneous_at_one
    (c x : ℚ) :
    orderFiveVeluXNumeratorHomogeneous c x 1 =
      orderFiveVeluXNumerator c x := by
  simp only [orderFiveVeluXNumeratorHomogeneous,
    orderFiveVeluXNumerator]
  ring

@[simp] theorem orderFiveVeluDifferentialNumeratorHomogeneous_at_one
    (c x : ℚ) :
    orderFiveVeluDifferentialNumeratorHomogeneous c x 1 =
      orderFiveVeluDifferentialNumerator c x := by
  simp only [orderFiveVeluDifferentialNumeratorHomogeneous,
    orderFiveVeluDifferentialNumerator]
  ring

/-- The doubled source kernel denominator factors as the original kernel
denominator times the Vélu differential numerator. -/
private theorem orderFive_kernel_double_certificate (c x : ℚ) :
    let H := Doubling.completedCubic (orderFiveCurve c) x
    let p := Doubling.xNumerator (orderFiveCurve c) x
    p * (p - c * H) =
      orderFiveKernelPolynomial c x *
        orderFiveVeluDifferentialNumerator c x := by
  simp only [Doubling.completedCubic, Doubling.xNumerator,
    orderFiveVeluDifferentialNumerator, orderFiveCurve,
    tateNormalCurve, orderFiveKernelPolynomial,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- Homogeneous abscissa identity for doubling through the explicit
degree-five quotient. -/
private theorem orderFiveVeluX_double_homogeneous (c x : ℚ) :
    orderFiveVeluXNumeratorHomogeneous c
        (Doubling.xNumerator (orderFiveCurve c) x)
        (Doubling.completedCubic (orderFiveCurve c) x) =
      Doubling.xNumeratorHomogeneous (orderFiveVeluTarget c)
        (orderFiveVeluXNumerator c x)
        (orderFiveKernelPolynomial c x ^ 2) := by
  simp only [orderFiveVeluXNumeratorHomogeneous,
    orderFiveVeluXNumerator, orderFiveKernelPolynomial, Doubling.xNumerator,
    Doubling.completedCubic, Doubling.xNumeratorHomogeneous,
    orderFiveCurve, orderFiveVeluTarget, tateNormalCurve,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- Homogeneous completed-ordinate identity for doubling through the
explicit degree-five quotient. -/
private theorem orderFiveVeluDifferential_double_homogeneous
    (c x : ℚ) :
    orderFiveVeluDifferentialNumeratorHomogeneous c
        (Doubling.xNumerator (orderFiveCurve c) x)
        (Doubling.completedCubic (orderFiveCurve c) x) *
          Doubling.completedYNumerator (orderFiveCurve c) x =
      Doubling.completedYNumeratorHomogeneous (orderFiveVeluTarget c)
        (orderFiveVeluXNumerator c x)
        (orderFiveKernelPolynomial c x ^ 2) := by
  simp only [orderFiveVeluDifferentialNumeratorHomogeneous,
    orderFiveVeluXNumerator, orderFiveKernelPolynomial, Doubling.xNumerator,
    Doubling.completedCubic, Doubling.completedYNumerator,
    Doubling.completedYNumeratorHomogeneous, orderFiveCurve,
    orderFiveVeluTarget, tateNormalCurve, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

/-- Completed-square identity for the explicit Vélu map. -/
private theorem orderFiveVelu_completedSquare
    {c x : ℚ} (hx0 : x ≠ 0) (hxc : x ≠ c) :
    orderFiveVeluDifferential c x ^ 2 *
        Doubling.completedCubic (orderFiveCurve c) x =
      Doubling.completedCubic (orderFiveVeluTarget c)
        (orderFiveVeluX c x) := by
  simp only [orderFiveVeluDifferential, orderFiveVeluX,
    Doubling.completedCubic, orderFiveCurve, orderFiveVeluTarget,
    tateNormalCurve, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  field_simp [hx0, sub_ne_zero.mpr hxc]
  ring

private theorem orderFiveKernelPolynomial_at_double
    {c H p x₂ K N : ℚ}
    (hp : p = x₂ * H)
    (hcert : p * (p - c * H) = K * N) :
    x₂ * (x₂ - c) * H ^ 2 = K * N := by
  rw [hp] at hcert
  linear_combination hcert

private theorem orderFiveVeluX_double_homogeneous_of_abscissa
    (c x x₂ : ℚ)
    (hp : Doubling.xNumerator (orderFiveCurve c) x =
      x₂ * Doubling.completedCubic (orderFiveCurve c) x) :
    orderFiveVeluXNumerator c x₂ *
        Doubling.completedCubic (orderFiveCurve c) x ^ 5 =
      Doubling.xNumeratorHomogeneous (orderFiveVeluTarget c)
        (orderFiveVeluXNumerator c x)
        (orderFiveKernelPolynomial c x ^ 2) := by
  rw [← orderFiveVeluXNumeratorHomogeneous_at_one]
  calc
    orderFiveVeluXNumeratorHomogeneous c x₂ 1 *
          Doubling.completedCubic (orderFiveCurve c) x ^ 5 =
        orderFiveVeluXNumeratorHomogeneous c
          (x₂ * Doubling.completedCubic (orderFiveCurve c) x)
          (Doubling.completedCubic (orderFiveCurve c) x) := by
      simp only [orderFiveVeluXNumeratorHomogeneous]
      ring
    _ = orderFiveVeluXNumeratorHomogeneous c
          (Doubling.xNumerator (orderFiveCurve c) x)
          (Doubling.completedCubic (orderFiveCurve c) x) := by
      rw [hp]
    _ = Doubling.xNumeratorHomogeneous (orderFiveVeluTarget c)
          (orderFiveVeluXNumerator c x)
          (orderFiveKernelPolynomial c x ^ 2) :=
      orderFiveVeluX_double_homogeneous c x

private theorem orderFiveVeluDifferential_double_homogeneous_of_abscissa
    (c x x₂ : ℚ)
    (hp : Doubling.xNumerator (orderFiveCurve c) x =
      x₂ * Doubling.completedCubic (orderFiveCurve c) x) :
    orderFiveVeluDifferentialNumerator c x₂ *
        Doubling.completedCubic (orderFiveCurve c) x ^ 6 *
          Doubling.completedYNumerator (orderFiveCurve c) x =
      Doubling.completedYNumeratorHomogeneous (orderFiveVeluTarget c)
        (orderFiveVeluXNumerator c x)
        (orderFiveKernelPolynomial c x ^ 2) := by
  rw [← orderFiveVeluDifferentialNumeratorHomogeneous_at_one]
  calc
    orderFiveVeluDifferentialNumeratorHomogeneous c x₂ 1 *
          Doubling.completedCubic (orderFiveCurve c) x ^ 6 *
            Doubling.completedYNumerator (orderFiveCurve c) x =
        orderFiveVeluDifferentialNumeratorHomogeneous c
            (x₂ * Doubling.completedCubic (orderFiveCurve c) x)
            (Doubling.completedCubic (orderFiveCurve c) x) *
          Doubling.completedYNumerator (orderFiveCurve c) x := by
      simp only [orderFiveVeluDifferentialNumeratorHomogeneous]
      ring
    _ = orderFiveVeluDifferentialNumeratorHomogeneous c
            (Doubling.xNumerator (orderFiveCurve c) x)
            (Doubling.completedCubic (orderFiveCurve c) x) *
          Doubling.completedYNumerator (orderFiveCurve c) x := by
      rw [hp]
    _ = Doubling.completedYNumeratorHomogeneous (orderFiveVeluTarget c)
          (orderFiveVeluXNumerator c x)
          (orderFiveKernelPolynomial c x ^ 2) :=
      orderFiveVeluDifferential_double_homogeneous c x

private theorem orderFiveQuotient_doubleX_of_homogeneous
    {H F₂ K₂ K N PhiT : ℚ}
    (hH : H ≠ 0) (hK : K ≠ 0) (hN : N ≠ 0) (hK₂ : K₂ ≠ 0)
    (hkernel : K₂ * H ^ 2 = K * N)
    (hhom : F₂ * H ^ 5 = PhiT) :
    F₂ / K₂ ^ 2 =
      (PhiT / K ^ 8) / ((N / K ^ 3) ^ 2 * H) := by
  field_simp [hH, hK, hN, hK₂]
  have hkernel₂ : K₂ ^ 2 * H ^ 4 = K ^ 2 * N ^ 2 := by
    calc
      K₂ ^ 2 * H ^ 4 = (K₂ * H ^ 2) ^ 2 := by ring
      _ = (K * N) ^ 2 := by rw [hkernel]
      _ = K ^ 2 * N ^ 2 := by ring
  calc
    F₂ * K ^ 2 * N ^ 2 * H = F₂ * (K ^ 2 * N ^ 2) * H := by ring
    _ = F₂ * (K₂ ^ 2 * H ^ 4) * H := by rw [← hkernel₂]
    _ = K₂ ^ 2 * (F₂ * H ^ 5) := by ring
    _ = K₂ ^ 2 * PhiT := by rw [hhom]

private theorem orderFiveQuotient_doubleCompletedY_of_homogeneous
    {V H R V₂ N₂ K₂ K N RT : ℚ}
    (hV : V ≠ 0) (hK : K ≠ 0) (hN : N ≠ 0) (hK₂ : K₂ ≠ 0)
    (hH : H = V ^ 2)
    (hsource : V ^ 3 * V₂ = R)
    (hkernel : K₂ * H ^ 2 = K * N)
    (hhom : N₂ * H ^ 6 * R = RT) :
    (N₂ / K₂ ^ 3) * V₂ =
      (RT / K ^ 12) / ((N / K ^ 3 * V) ^ 3) := by
  field_simp [hV, hK, hN, hK₂]
  rw [hH] at hkernel hhom
  have hkernel₃ : K₂ ^ 3 * V ^ 12 = K ^ 3 * N ^ 3 := by
    calc
      K₂ ^ 3 * V ^ 12 = (K₂ * (V ^ 2) ^ 2) ^ 3 := by ring
      _ = (K * N) ^ 3 := by rw [hkernel]
      _ = K ^ 3 * N ^ 3 := by ring
  calc
    N₂ * V₂ * K ^ 3 * N ^ 3 * V ^ 3 =
        N₂ * V₂ * (K ^ 3 * N ^ 3) * V ^ 3 := by ring
    _ = N₂ * V₂ * (K₂ ^ 3 * V ^ 12) * V ^ 3 := by
      rw [← hkernel₃]
    _ = K₂ ^ 3 * (N₂ * V ^ 12 * (V ^ 3 * V₂)) := by ring
    _ = K₂ ^ 3 * (N₂ * V ^ 12 * R) := by rw [hsource]
    _ = K₂ ^ 3 * RT := by
      rw [← hhom]
      ring

private theorem orderFive_xNumerator_div_square
    (W : WeierstrassCurve ℚ) {u k : ℚ} (hk : k ≠ 0) :
    Doubling.xNumerator W (u / k ^ 2) =
      Doubling.xNumeratorHomogeneous W u (k ^ 2) / k ^ 8 := by
  simp only [Doubling.xNumerator, Doubling.xNumeratorHomogeneous]
  field_simp [hk]

private theorem orderFive_completedYNumerator_div_square
    (W : WeierstrassCurve ℚ) {u k : ℚ} (hk : k ≠ 0) :
    Doubling.completedYNumerator W (u / k ^ 2) =
      Doubling.completedYNumeratorHomogeneous W u (k ^ 2) /
        k ^ 12 := by
  simp only [Doubling.completedYNumerator,
    Doubling.completedYNumeratorHomogeneous]
  field_simp [hk]

private theorem two_nsmul_ne_zero_of_orderTwentyFive
    {G : Type*} [AddCommGroup G] {P : G}
    (hP : addOrderOf P = 25) :
    (2 : ℕ) • P ≠ 0 := by
  intro hzero
  have hdvd : (25 : ℕ) ∣ 2 := by
    rw [← hP]
    exact addOrderOf_dvd_of_nsmul_eq_zero hzero
  norm_num at hdvd

private def OrderFiveDoublingCoordinates (c x y : ℚ) : Prop :=
  let W := (orderFiveCurve c).toAffine
  let Wq := (orderFiveVeluTarget c).toAffine
  let m := W.slope x x y y
  let x₂ := W.addX x x m
  let y₂ := W.addY x x y m
  let X := orderFiveVeluX c x
  let Y := orderFiveVeluY c x y
  let M := Wq.slope X X Y Y
  let X₂ := Wq.addX X X M
  let Y₂ := Wq.addY X X Y M
  orderFiveVeluX c x₂ = X₂ ∧
    2 * orderFiveVeluY c x₂ y₂ +
        Wq.a₁ * orderFiveVeluX c x₂ + Wq.a₃ =
      2 * Y₂ + Wq.a₁ * X₂ + Wq.a₃

private theorem orderFiveVeluPoint_two_nsmul_of_coordinates
    {c x y x₂ y₂ : ℚ} [(orderFiveCurve c).IsElliptic]
    (hP : (orderFiveCurve c).toAffine.Nonsingular x y)
    (hP₂ : (orderFiveCurve c).toAffine.Nonsingular x₂ y₂)
    (hx0 : x ≠ 0) (hxc : x ≠ c)
    (hx0₂ : x₂ ≠ 0) (hxc₂ : x₂ ≠ c)
    (hcompletedY :
      2 * orderFiveVeluY c x y +
          (orderFiveVeluTarget c).toAffine.a₁ * orderFiveVeluX c x +
          (orderFiveVeluTarget c).toAffine.a₃ ≠ 0)
    (hX : orderFiveVeluX c x₂ =
      (orderFiveVeluTarget c).toAffine.addX
        (orderFiveVeluX c x) (orderFiveVeluX c x)
        ((orderFiveVeluTarget c).toAffine.slope
          (orderFiveVeluX c x) (orderFiveVeluX c x)
          (orderFiveVeluY c x y) (orderFiveVeluY c x y)))
    (hcompleted :
      2 * orderFiveVeluY c x₂ y₂ +
          (orderFiveVeluTarget c).toAffine.a₁ *
            orderFiveVeluX c x₂ +
          (orderFiveVeluTarget c).toAffine.a₃ =
        2 * (orderFiveVeluTarget c).toAffine.addY
            (orderFiveVeluX c x) (orderFiveVeluX c x)
            (orderFiveVeluY c x y)
            ((orderFiveVeluTarget c).toAffine.slope
              (orderFiveVeluX c x) (orderFiveVeluX c x)
              (orderFiveVeluY c x y) (orderFiveVeluY c x y)) +
          (orderFiveVeluTarget c).toAffine.a₁ *
            (orderFiveVeluTarget c).toAffine.addX
              (orderFiveVeluX c x) (orderFiveVeluX c x)
              ((orderFiveVeluTarget c).toAffine.slope
                (orderFiveVeluX c x) (orderFiveVeluX c x)
                (orderFiveVeluY c x y) (orderFiveVeluY c x y)) +
          (orderFiveVeluTarget c).toAffine.a₃) :
    orderFiveVeluPoint hP₂ hx0₂ hxc₂ =
      (2 : ℕ) • orderFiveVeluPoint hP hx0 hxc := by
  have hYne : orderFiveVeluY c x y ≠
      (orderFiveVeluTarget c).toAffine.negY
        (orderFiveVeluX c x) (orderFiveVeluY c x y) := by
    intro hY
    apply hcompletedY
    simp only [WeierstrassCurve.Affine.negY] at hY
    linear_combination hY
  rw [two_nsmul]
  simp only [orderFiveVeluPoint]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hYne]
  apply WeierstrassCurve.Affine.Point.some_eq_some
    (orderFiveVeluTarget c)
  · exact hX
  · linear_combination
      (1 / 2 : ℚ) * hcompleted -
        ((orderFiveVeluTarget c).toAffine.a₁ / 2) * hX

private theorem orderFivePointMap_two_nsmul_of_orderTwentyFive_affine
    {c x y : ℚ} [(orderFiveCurve c).IsElliptic]
    (hP : (orderFiveCurve c).toAffine.Nonsingular x y)
    (horder : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (orderFiveCurve c).toAffine.Point) = 25)
    (hcoordinates : OrderFiveDoublingCoordinates c x y) :
    orderFivePointMap c
        ((2 : ℕ) • (WeierstrassCurve.Affine.Point.some x y hP :
          (orderFiveCurve c).toAffine.Point)) =
      (2 : ℕ) • orderFivePointMap c
        (WeierstrassCurve.Affine.Point.some x y hP) := by
  let W := (orderFiveCurve c).toAffine
  let m := W.slope x x y y
  let x₂ := W.addX x x m
  let y₂ := W.addY x x y m
  have htwo_ne :
      (2 : ℕ) • (WeierstrassCurve.Affine.Point.some x y hP :
        (orderFiveCurve c).toAffine.Point) ≠ 0 :=
    two_nsmul_ne_zero_of_orderTwentyFive horder
  have hy : y ≠ W.negY x y := by
    intro hy
    apply htwo_ne
    rw [two_nsmul]
    exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy
  let hP₂ : (orderFiveCurve c).toAffine.Nonsingular x₂ y₂ :=
    W.nonsingular_add hP hP (fun hxy ↦ hy hxy.2)
  have hadd :
      (2 : ℕ) • (WeierstrassCurve.Affine.Point.some x y hP :
          (orderFiveCurve c).toAffine.Point) =
        WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ := by
    rw [two_nsmul,
      WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy]
  have horder₂ : addOrderOf
      (WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ :
        (orderFiveCurve c).toAffine.Point) = 25 := by
    rw [← hadd, addOrderOf_nsmul'
      (WeierstrassCurve.Affine.Point.some x y hP) (by norm_num), horder]
    norm_num
  have hx := not_orderFiveKernelX_of_orderTwentyFive hP horder
  have hx₂ := not_orderFiveKernelX_of_orderTwentyFive hP₂ horder₂
  have hx0 : x ≠ 0 := fun h ↦ hx (Or.inl h)
  have hxc : x ≠ c := fun h ↦ hx (Or.inr h)
  have hx0₂ : x₂ ≠ 0 := fun h ↦ hx₂ (Or.inl h)
  have hxc₂ : x₂ ≠ c := fun h ↦ hx₂ (Or.inr h)
  have hK : orderFiveKernelPolynomial c x ≠ 0 :=
    mul_ne_zero hx0 (sub_ne_zero.mpr hxc)
  have hK₂ : orderFiveKernelPolynomial c x₂ ≠ 0 :=
    mul_ne_zero hx0₂ (sub_ne_zero.mpr hxc₂)
  have hv : 2 * y + (orderFiveCurve c).a₁ * x +
      (orderFiveCurve c).a₃ ≠ 0 := by
    intro hv
    apply hy
    simp only [W, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.toAffine]
    linarith
  have hH : Doubling.completedCubic (orderFiveCurve c) x ≠ 0 := by
    rw [Doubling.completedCubic_eq_completedY_sq
      (orderFiveCurve c) hP.1]
    exact pow_ne_zero 2 hv
  have hp : Doubling.xNumerator (orderFiveCurve c) x =
      x₂ * Doubling.completedCubic (orderFiveCurve c) x :=
    (Doubling.addX_self_mul_completedCubic
      (orderFiveCurve c) hP.1 hv).symm
  have hkernel :
      orderFiveKernelPolynomial c x₂ *
          Doubling.completedCubic (orderFiveCurve c) x ^ 2 =
        orderFiveKernelPolynomial c x *
          orderFiveVeluDifferentialNumerator c x := by
    exact orderFiveKernelPolynomial_at_double hp
      (orderFive_kernel_double_certificate c x)
  have hN : orderFiveVeluDifferentialNumerator c x ≠ 0 := by
    intro hN
    have hleft : orderFiveKernelPolynomial c x₂ *
        Doubling.completedCubic (orderFiveCurve c) x ^ 2 ≠ 0 :=
      mul_ne_zero hK₂ (pow_ne_zero 2 hH)
    apply hleft
    rw [hkernel, hN, mul_zero]
  have hdiff : orderFiveVeluDifferential c x ≠ 0 := by
    rw [orderFiveVeluDifferential_eq_div hx0 hxc]
    exact div_ne_zero hN (pow_ne_zero 3 hK)
  have hcompletedY :
      2 * orderFiveVeluY c x y +
          (orderFiveVeluTarget c).toAffine.a₁ * orderFiveVeluX c x +
          (orderFiveVeluTarget c).toAffine.a₃ ≠ 0 := by
    rw [orderFiveVelu_completedY]
    exact mul_ne_zero hdiff hv
  obtain ⟨hX, hcompleted⟩ := hcoordinates
  rw [hadd, orderFivePointMap_some_of_not_kernelX hP₂ hx₂,
    orderFivePointMap_some_of_not_kernelX hP hx]
  exact orderFiveVeluPoint_two_nsmul_of_coordinates hP hP₂
    hx0 hxc hx0₂ hxc₂ hcompletedY hX hcompleted

private theorem orderFiveVelu_double_coordinates
    {c x y : ℚ} [(orderFiveCurve c).IsElliptic]
    (hP : (orderFiveCurve c).toAffine.Nonsingular x y)
    (horder : addOrderOf
      (WeierstrassCurve.Affine.Point.some x y hP :
        (orderFiveCurve c).toAffine.Point) = 25) :
    OrderFiveDoublingCoordinates c x y := by
  let W := orderFiveCurve c
  let Wq := orderFiveVeluTarget c
  let m := W.toAffine.slope x x y y
  let x₂ := W.toAffine.addX x x m
  let y₂ := W.toAffine.addY x x y m
  let X := orderFiveVeluX c x
  let Y := orderFiveVeluY c x y
  let M := Wq.toAffine.slope X X Y Y
  let X₂ := Wq.toAffine.addX X X M
  let Y₂ := Wq.toAffine.addY X X Y M
  change orderFiveVeluX c x₂ = X₂ ∧
    2 * orderFiveVeluY c x₂ y₂ +
        Wq.a₁ * orderFiveVeluX c x₂ + Wq.a₃ =
      2 * Y₂ + Wq.a₁ * X₂ + Wq.a₃
  have htwo_ne :
      (2 : ℕ) • (WeierstrassCurve.Affine.Point.some x y hP :
        W.toAffine.Point) ≠ 0 :=
    two_nsmul_ne_zero_of_orderTwentyFive horder
  have hy : y ≠ W.toAffine.negY x y := by
    intro hy
    apply htwo_ne
    rw [two_nsmul]
    exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy
  let hP₂ : W.toAffine.Nonsingular x₂ y₂ :=
    W.toAffine.nonsingular_add hP hP (fun hxy ↦ hy hxy.2)
  have hadd :
      (2 : ℕ) • (WeierstrassCurve.Affine.Point.some x y hP :
          W.toAffine.Point) =
        WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ := by
    rw [two_nsmul,
      WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy]
  have horder₂ : addOrderOf
      (WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ :
        W.toAffine.Point) = 25 := by
    rw [← hadd, addOrderOf_nsmul'
      (WeierstrassCurve.Affine.Point.some x y hP) (by norm_num), horder]
    norm_num
  have hx := not_orderFiveKernelX_of_orderTwentyFive hP horder
  have hx₂ := not_orderFiveKernelX_of_orderTwentyFive hP₂ horder₂
  have hx0 : x ≠ 0 := fun h ↦ hx (Or.inl h)
  have hxc : x ≠ c := fun h ↦ hx (Or.inr h)
  have hx0₂ : x₂ ≠ 0 := fun h ↦ hx₂ (Or.inl h)
  have hxc₂ : x₂ ≠ c := fun h ↦ hx₂ (Or.inr h)
  let V := 2 * y + W.a₁ * x + W.a₃
  let V₂ := 2 * y₂ + W.a₁ * x₂ + W.a₃
  let H := Doubling.completedCubic W x
  let p := Doubling.xNumerator W x
  let K := orderFiveKernelPolynomial c x
  let K₂ := orderFiveKernelPolynomial c x₂
  let N := orderFiveVeluDifferentialNumerator c x
  let N₂ := orderFiveVeluDifferentialNumerator c x₂
  let F := orderFiveVeluXNumerator c x
  let F₂ := orderFiveVeluXNumerator c x₂
  let PhiT := Doubling.xNumeratorHomogeneous Wq F (K ^ 2)
  let R := Doubling.completedYNumerator W x
  let RT := Doubling.completedYNumeratorHomogeneous Wq F (K ^ 2)
  have hK : K ≠ 0 := mul_ne_zero hx0 (sub_ne_zero.mpr hxc)
  have hK₂ : K₂ ≠ 0 := mul_ne_zero hx0₂ (sub_ne_zero.mpr hxc₂)
  have hV : V ≠ 0 := by
    intro hV
    apply hy
    simp only [W, WeierstrassCurve.Affine.negY,
      WeierstrassCurve.toAffine]
    linarith
  have hH_eq : H = V ^ 2 :=
    Doubling.completedCubic_eq_completedY_sq W hP.1
  have hH : H ≠ 0 := by
    rw [hH_eq]
    exact pow_ne_zero 2 hV
  have hp : p = x₂ * H :=
    (Doubling.addX_self_mul_completedCubic W hP.1 hV).symm
  have hkernel : K₂ * H ^ 2 = K * N := by
    exact orderFiveKernelPolynomial_at_double hp
      (orderFive_kernel_double_certificate c x)
  have hN : N ≠ 0 := by
    intro hN
    have hleft : K₂ * H ^ 2 ≠ 0 :=
      mul_ne_zero hK₂ (pow_ne_zero 2 hH)
    apply hleft
    rw [hkernel, hN, mul_zero]
  have hsourceY : V ^ 3 * V₂ = R :=
    Doubling.completedY_add_self W hP.1 hV
  have hhomX : F₂ * H ^ 5 = PhiT :=
    orderFiveVeluX_double_homogeneous_of_abscissa c x x₂ hp
  have hhomY : N₂ * H ^ 6 * R = RT :=
    orderFiveVeluDifferential_double_homogeneous_of_abscissa c x x₂ hp
  have hquotX :
      F₂ / K₂ ^ 2 =
        (PhiT / K ^ 8) / ((N / K ^ 3) ^ 2 * H) :=
    orderFiveQuotient_doubleX_of_homogeneous
      hH hK hN hK₂ hkernel hhomX
  have hquotY :
      (N₂ / K₂ ^ 3) * V₂ =
        (RT / K ^ 12) / ((N / K ^ 3 * V) ^ 3) :=
    orderFiveQuotient_doubleCompletedY_of_homogeneous
      hV hK hN hK₂ hH_eq hsourceY hkernel hhomY
  have hxMap : X = F / K ^ 2 :=
    orderFiveVeluX_eq_div hx0 hxc
  have hxMap₂ : orderFiveVeluX c x₂ = F₂ / K₂ ^ 2 :=
    orderFiveVeluX_eq_div hx0₂ hxc₂
  have hdiff : orderFiveVeluDifferential c x = N / K ^ 3 :=
    orderFiveVeluDifferential_eq_div hx0 hxc
  have hdiff₂ : orderFiveVeluDifferential c x₂ = N₂ / K₂ ^ 3 :=
    orderFiveVeluDifferential_eq_div hx0₂ hxc₂
  have hcurveImage : Wq.toAffine.Equation X Y :=
    orderFiveVelu_equation hP hx0 hxc
  have himageV : 2 * Y + Wq.a₁ * X + Wq.a₃ = N / K ^ 3 * V := by
    calc
      2 * Y + Wq.a₁ * X + Wq.a₃ =
          orderFiveVeluDifferential c x * V :=
        orderFiveVelu_completedY c x y
      _ = N / K ^ 3 * V := by rw [hdiff]
  have himageV_ne : 2 * Y + Wq.a₁ * X + Wq.a₃ ≠ 0 := by
    rw [himageV]
    exact mul_ne_zero (div_ne_zero hN (pow_ne_zero 3 hK)) hV
  have htargetH :
      Doubling.completedCubic Wq X = (N / K ^ 3) ^ 2 * H := by
    have hsquare := orderFiveVelu_completedSquare hx0 hxc
    change orderFiveVeluDifferential c x ^ 2 * H =
      Doubling.completedCubic Wq X at hsquare
    rw [hdiff] at hsquare
    exact hsquare.symm
  have htargetH_ne : (N / K ^ 3) ^ 2 * H ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2
      (div_ne_zero hN (pow_ne_zero 3 hK))) hH
  have htargetNumerator :
      Doubling.xNumerator Wq X = PhiT / K ^ 8 := by
    rw [hxMap]
    exact orderFive_xNumerator_div_square Wq hK
  have htargetCompletedYNumerator :
      Doubling.completedYNumerator Wq X = RT / K ^ 12 := by
    rw [hxMap]
    exact orderFive_completedYNumerator_div_square Wq hK
  have htargetXmul :
      X₂ * Doubling.completedCubic Wq X =
        Doubling.xNumerator Wq X :=
    Doubling.addX_self_mul_completedCubic Wq hcurveImage himageV_ne
  have htargetX :
      X₂ = (PhiT / K ^ 8) / ((N / K ^ 3) ^ 2 * H) := by
    apply (eq_div_iff htargetH_ne).2
    calc
      X₂ * ((N / K ^ 3) ^ 2 * H) =
          X₂ * Doubling.completedCubic Wq X := by rw [htargetH]
      _ = Doubling.xNumerator Wq X := htargetXmul
      _ = PhiT / K ^ 8 := htargetNumerator
  have htargetYmul :
      (2 * Y + Wq.a₁ * X + Wq.a₃) ^ 3 *
          (2 * Y₂ + Wq.a₁ * X₂ + Wq.a₃) =
        Doubling.completedYNumerator Wq X :=
    Doubling.completedY_add_self Wq hcurveImage himageV_ne
  have htargetY :
      2 * Y₂ + Wq.a₁ * X₂ + Wq.a₃ =
        (RT / K ^ 12) / ((N / K ^ 3 * V) ^ 3) := by
    apply (eq_div_iff (pow_ne_zero 3
      (mul_ne_zero (div_ne_zero hN (pow_ne_zero 3 hK)) hV))).2
    calc
      (2 * Y₂ + Wq.a₁ * X₂ + Wq.a₃) *
          (N / K ^ 3 * V) ^ 3 =
        (2 * Y + Wq.a₁ * X + Wq.a₃) ^ 3 *
          (2 * Y₂ + Wq.a₁ * X₂ + Wq.a₃) := by
            rw [himageV]
            ring
      _ = Doubling.completedYNumerator Wq X := htargetYmul
      _ = RT / K ^ 12 := htargetCompletedYNumerator
  constructor
  · calc
      orderFiveVeluX c x₂ = F₂ / K₂ ^ 2 := hxMap₂
      _ = (PhiT / K ^ 8) / ((N / K ^ 3) ^ 2 * H) := hquotX
      _ = X₂ := htargetX.symm
  · calc
      2 * orderFiveVeluY c x₂ y₂ +
          Wq.a₁ * orderFiveVeluX c x₂ + Wq.a₃ =
        orderFiveVeluDifferential c x₂ * V₂ :=
          orderFiveVelu_completedY c x₂ y₂
      _ = (N₂ / K₂ ^ 3) * V₂ := by rw [hdiff₂]
      _ = (RT / K ^ 12) / ((N / K ^ 3 * V) ^ 3) := hquotY
      _ = 2 * Y₂ + Wq.a₁ * X₂ + Wq.a₃ := htargetY.symm

/-- On an exact-order-twenty-five point, the explicit total order-five
Vélu map commutes with tangent doubling. -/
theorem orderFivePointMap_two_nsmul_of_orderTwentyFive
    {c : ℚ} [(orderFiveCurve c).IsElliptic]
    {Q : (orderFiveCurve c).toAffine.Point}
    (hQ : addOrderOf Q = 25) :
    orderFivePointMap c ((2 : ℕ) • Q) =
      (2 : ℕ) • orderFivePointMap c Q := by
  cases Q with
  | zero =>
      have hfalse : (1 : ℕ) = 25 := by
        rw [← hQ]
        exact (addOrderOf_zero
          (G := (orderFiveCurve c).toAffine.Point)).symm
      norm_num at hfalse
  | some x y hP =>
      exact orderFivePointMap_two_nsmul_of_orderTwentyFive_affine
        hP hQ (orderFiveVelu_double_coordinates hP hQ)

/-- Every point in the zero fiber of the explicit Vélu function is killed
by five on the source curve. -/
theorem orderFivePointMap_kernel_killed_by_five
    {c : ℚ} [(orderFiveCurve c).IsElliptic]
    {Q : (orderFiveCurve c).toAffine.Point}
    (hQ : orderFivePointMap c Q = 0) :
    (5 : ℕ) • Q = 0 := by
  cases Q with
  | zero => rfl
  | some x y hP =>
      obtain ⟨hc, -⟩ := orderFiveCurve_parameters_ne c
      exact five_nsmul_eq_zero_of_orderFive_kernel_abscissa hc hP
        ((orderFivePointMap_some_eq_zero_iff hP).mp hQ)

/-- If `5Q` is the marked kernel generator, doubling compatibility,
negation, and kernel-translation invariance force the Vélu image to be
killed by five. -/
theorem five_nsmul_orderFivePointMap_of_orderTwentyFive
    {c : ℚ} [(orderFiveCurve c).IsElliptic]
    {Q : (orderFiveCurve c).toAffine.Point}
    (hQ : addOrderOf Q = 25)
    (hfive : (5 : ℕ) • Q = orderFiveOrigin c) :
    (5 : ℕ) • orderFivePointMap c Q = 0 := by
  have h2Q : addOrderOf ((2 : ℕ) • Q) = 25 := by
    rw [addOrderOf_nsmul' Q (by norm_num), hQ]
    norm_num
  have hdoubleQ := orderFivePointMap_two_nsmul_of_orderTwentyFive hQ
  have hdouble2Q :=
    orderFivePointMap_two_nsmul_of_orderTwentyFive h2Q
  have hmap4 : orderFivePointMap c ((4 : ℕ) • Q) =
      (4 : ℕ) • orderFivePointMap c Q := by
    calc
      orderFivePointMap c ((4 : ℕ) • Q) =
          orderFivePointMap c ((2 : ℕ) • ((2 : ℕ) • Q)) := by
            rw [← mul_nsmul]
      _ = (2 : ℕ) • orderFivePointMap c ((2 : ℕ) • Q) :=
        hdouble2Q
      _ = (2 : ℕ) • ((2 : ℕ) • orderFivePointMap c Q) := by
        rw [hdoubleQ]
      _ = (4 : ℕ) • orderFivePointMap c Q := by
        rw [← mul_nsmul]
  have hnegOrder : addOrderOf (-Q) = 25 := by
    rw [addOrderOf_neg, hQ]
  have hinvariant :=
    orderFivePointMap_add_origin_of_orderTwentyFive hnegOrder
  have hfour :
      (4 : ℕ) • Q = -Q + orderFiveOrigin c := by
    calc
      (4 : ℕ) • Q = (5 : ℕ) • Q - Q := by abel
      _ = orderFiveOrigin c - Q := by rw [hfive]
      _ = -Q + orderFiveOrigin c := by abel
  have hfourImage :
      (4 : ℕ) • orderFivePointMap c Q =
        -orderFivePointMap c Q := by
    calc
      (4 : ℕ) • orderFivePointMap c Q =
          orderFivePointMap c ((4 : ℕ) • Q) := hmap4.symm
      _ = orderFivePointMap c (-Q + orderFiveOrigin c) := by rw [hfour]
      _ = orderFivePointMap c (-Q) := hinvariant
      _ = -orderFivePointMap c Q := orderFivePointMap_neg c Q
  calc
    (5 : ℕ) • orderFivePointMap c Q =
        (4 : ℕ) • orderFivePointMap c Q +
          orderFivePointMap c Q := by abel
    _ = 0 := by rw [hfourImage, neg_add_cancel]

/-- The explicit quotient image of a genuine five-division point has exact
order five. -/
theorem addOrderOf_orderFivePointMap_of_orderTwentyFive
    {c : ℚ} [(orderFiveCurve c).IsElliptic]
    {Q : (orderFiveCurve c).toAffine.Point}
    (hQ : addOrderOf Q = 25)
    (hfive : (5 : ℕ) • Q = orderFiveOrigin c) :
    addOrderOf (orderFivePointMap c Q) = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply addOrderOf_eq_prime
  · exact five_nsmul_orderFivePointMap_of_orderTwentyFive hQ hfive
  · intro hzero
    have hkilled := orderFivePointMap_kernel_killed_by_five hzero
    have hdvd : (25 : ℕ) ∣ 5 := by
      rw [← hQ]
      exact addOrderOf_dvd_of_nsmul_eq_zero hkilled
    norm_num at hdvd

end MazurTorsion.Kubert

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import EllipticCurves.ReductionAtPrime
import Mathlib.RingTheory.Polynomial.RationalRoot
import MazurTorsion.NumberTheory.XOneFifteenDescent

/-!
# Rational points on the chosen `X₁(15)` model

The two-isogeny descent proves that the rational point group of

`V² = U(U² - 7U + 16)`

is finite.  Reduction at seven bounds its cardinality by eight.  The
visible point `(4,4)` has order four, while a denominator-free duplication
identity and a monic quartic obstruction modulo seventeen rule out points
of order eight.  The exact two-torsion cardinality then forces the whole
group to have cardinality four.
-/

open WeierstrassCurve

namespace MazurTorsion.XOneFifteen

open WeierstrassCurve.Affine
  IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The integral model used for reduction at seven. -/
def integralCurve : WeierstrassCurve ℤ :=
  ⟨0, -7, 0, 16, 0⟩

lemma map_integralCurve :
    (integralCurve.map (algebraMap ℤ ℚ)).toAffine =
      curve.toAffine := by
  ext <;> simp [integralCurve, curve]

lemma discriminant_integralCurve :
    integralCurve.Δ = -61440 := by
  norm_num [integralCurve, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance : curve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [curve, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The height-one prime `(p)` of `ℤ`. -/
def intPrime (p : ℕ) [Fact p.Prime] :
    HeightOneSpectrum ℤ :=
  .ofPrime (p := Ideal.span {(p : ℤ)})
    (Ideal.prime_span_singleton_iff.mpr
      (Nat.prime_iff_prime_int.mp Fact.out))

@[simp] lemma intPrime_asIdeal (p : ℕ) [Fact p.Prime] :
    (intPrime p).asIdeal = Ideal.span {(p : ℤ)} :=
  rfl

instance (p : ℕ) [Fact p.Prime] :
    DecidableEq (ℤ ⧸ (intPrime p).asIdeal) :=
  (Int.quotientSpanNatEquivZMod p).toEquiv.decidableEq

lemma isElliptic_redCurve {p : ℕ} [Fact p.Prime]
    (h : ¬ (p : ℤ) ∣ integralCurve.Δ) :
    (redCurve (intPrime p) integralCurve).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  change
    (integralCurve.map
      (algebraMap ℤ (ℤ ⧸ (intPrime p).asIdeal))).Δ ≠ 0
  rwa [Ne, WeierstrassCurve.map_Δ,
    Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem,
    intPrime_asIdeal, Ideal.mem_span_singleton]

instance :
    (redCurve (intPrime 7) integralCurve).IsElliptic :=
  isElliptic_redCurve
    (by norm_num [discriminant_integralCurve])

/-- The concrete reduction over `ZMod 7`. -/
def curveModSeven : WeierstrassCurve (ZMod 7) :=
  ⟨0, -7, 0, 16, 0⟩

instance : curveModSeven.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  decide

noncomputable def residueSevenAlgEquiv :
    (ℤ ⧸ (intPrime 7).asIdeal) ≃ₐ[ℤ] ZMod 7 :=
  AlgEquiv.ofRingEquiv
    (f := Int.quotientSpanNatEquivZMod 7) fun x ↦ by
      simp only [algebraMap_int_eq, eq_intCast, map_intCast]

lemma baseChange_modSeven :
    ((integralCurve.toAffine ⁄ (ZMod 7)) :
      WeierstrassCurve _).toAffine =
        curveModSeven.toAffine := by
  ext <;> decide +kernel

/-- Identification of the abstract residue-field point group with the
computable `ZMod 7` point group. -/
noncomputable def reducedPointEquiv :
    (redCurve (intPrime 7) integralCurve).Point ≃+
      curveModSeven.toAffine.Point :=
  (Point.mapEquiv (W' := integralCurve.toAffine)
      residueSevenAlgEquiv).trans
    (Point.congr baseChange_modSeven)

noncomputable instance :
    Finite (redCurve (intPrime 7) integralCurve).Point :=
  .of_equiv curveModSeven.toAffine.Point
    reducedPointEquiv.symm.toEquiv

/-- The reduction modulo seven has exactly eight points. -/
theorem card_reducedCurve :
    Nat.card
      (redCurve (intPrime 7) integralCurve).Point = 8 := by
  calc
    Nat.card
        (redCurve (intPrime 7) integralCurve).Point =
        Fintype.card curveModSeven.toAffine.Point :=
      (Nat.card_congr reducedPointEquiv.toEquiv).trans
        Nat.card_eq_fintype_card
    _ = 8 := by decide

lemma seven_mem_prime :
    (7 : ℤ) ∈ (intPrime 7).asIdeal :=
  Ideal.mem_span_singleton_self 7

lemma seven_not_mem_prime_pow_six :
    (7 : ℤ) ∉ (intPrime 7).asIdeal ^ (7 - 1) := by
  rw [intPrime_asIdeal, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  norm_num

/-- Reduction at seven is injective on the finite rational point group. -/
theorem reduction_injective [Finite curve.toAffine.Point] :
    Function.Injective
      (redHom (intPrime 7) map_integralCurve) := by
  intro P Q hPQ
  apply sub_eq_zero.mp
  apply eq_zero_of_isOfFinAddOrder_of_red_eq_zero
    (intPrime 7) map_integralCurve
    (by norm_num) seven_mem_prime
    seven_not_mem_prime_pow_six
    (isOfFinAddOrder_of_finite (P - Q))
  change
    redHom (intPrime 7) map_integralCurve (P - Q) = 0
  rw [map_sub, hPQ, sub_self]

/-- There are at most eight rational points on the chosen `X₁(15)` model. -/
theorem point_card_le_eight :
    Nat.card curve.toAffine.Point ≤ 8 := by
  letI : Finite curve.toAffine.Point := point_finite
  calc
    Nat.card curve.toAffine.Point ≤
        Nat.card
          (redCurve (intPrime 7) integralCurve).Point :=
      Nat.card_le_card_of_injective
        (redHom (intPrime 7) map_integralCurve)
        reduction_injective
    _ = 8 := card_reducedCurve

private lemma double_G_reduction : (2 : ℕ) • G = T := by
  simp only [two_nsmul, G]
  rw [Point.add_self_of_Y_ne
    (by norm_num [negY, curve])]
  rw [T]
  simp only [Point.some.injEq]
  constructor
  · norm_num [addX, WeierstrassCurve.Affine.slope, negY, curve]
  · norm_num [addY, addX,
      WeierstrassCurve.Affine.slope, negY, curve]

private lemma double_T_reduction : (2 : ℕ) • T = 0 := by
  simp only [two_nsmul]
  rw [T]
  apply Point.add_self_of_Y_eq
  norm_num [negY, curve]

private lemma four_G_reduction : (4 : ℕ) • G = 0 := by
  calc
    (4 : ℕ) • G = (2 : ℕ) • ((2 : ℕ) • G) := by
      norm_num [← mul_nsmul]
    _ = (2 : ℕ) • T := by rw [double_G_reduction]
    _ = 0 := double_T_reduction

/-- The visible point `(4,4)` has exact additive order four. -/
theorem addOrderOf_G : addOrderOf G = 4 := by
  apply addOrderOf_eq_of_nsmul_and_div_prime_nsmul
    (by norm_num) four_G_reduction
  intro p hp hpdiv
  have hp22 : p ∣ 2 * 2 := by
    simpa using hpdiv
  have hp2 : p = 2 := by
    rcases hp.dvd_mul.mp hp22 with hp2 | hp2
    · rcases (Nat.dvd_prime
        (by decide : Nat.Prime 2)).mp hp2 with hp1 | hp2
      · exact (hp.ne_one hp1).elim
      · exact hp2
    · rcases (Nat.dvd_prime
        (by decide : Nat.Prime 2)).mp hp2 with hp1 | hp2
      · exact (hp.ne_one hp1).elim
      · exact hp2
  subst p
  rw [show 4 / 2 = 2 by norm_num, double_G_reduction]
  simp [T]

private lemma curve_equation
    {x y : ℚ} (h : curve.toAffine.Nonsingular x y) :
    y ^ 2 = x ^ 3 - 7 * x ^ 2 + 16 * x := by
  have heq := h.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  simp only [curve] at heq
  convert heq using 1 <;> ring

private lemma duplication_identity_algebra
    {x y x₂ : ℚ} (hy : y ≠ 0)
    (hcurve : y ^ 2 = x ^ 3 - 7 * x ^ 2 + 16 * x)
    (hx₂ :
      x₂ =
        ((3 * x ^ 2 - 14 * x + 16) / (2 * y)) ^ 2 +
          7 - 2 * x) :
    x₂ * (2 * y) ^ 2 = (x ^ 2 - 16) ^ 2 := by
  rw [hx₂]
  field_simp [hy]
  linear_combination -4 * (-7 + 2 * x) * hcurve

/-- The denominator-free duplication identity on the chosen model. -/
private lemma duplication_identity_of_double
    {x y x₂ y₂ : ℚ}
    (hP : curve.toAffine.Nonsingular x y)
    (hP₂ : curve.toAffine.Nonsingular x₂ y₂)
    (hdouble :
      (2 : ℕ) • Point.some x y hP =
        Point.some x₂ y₂ hP₂) :
    x₂ * (2 * y) ^ 2 = (x ^ 2 - 16) ^ 2 := by
  have hy : y ≠ curve.toAffine.negY x y := by
    intro hy
    have hzero :
        (2 : ℕ) • Point.some x y hP = 0 := by
      rw [two_nsmul, Point.add_self_of_Y_eq hy]
    rw [hzero] at hdouble
    exact Point.some_ne_zero hP₂ hdouble.symm
  have hy0 : y ≠ 0 := by
    intro hy0
    apply hy
    simp [curve, negY, hy0]
  let ℓ := curve.toAffine.slope x x y y
  have hadd :=
    Point.add_self_of_Y_ne
      (W := curve.toAffine) (h₁ := hP) hy
  have hx₂ : curve.toAffine.addX x x ℓ = x₂ := by
    have hsum :
        Point.some x y hP + Point.some x y hP =
          Point.some x₂ y₂ hP₂ := by
      simpa [two_nsmul] using hdouble
    exact (Point.some.inj (hadd.symm.trans hsum)).1
  have hℓ :
      ℓ = (3 * x ^ 2 - 14 * x + 16) / (2 * y) := by
    dsimp [ℓ]
    rw [slope_of_Y_ne rfl hy]
    simp only [negY]
    simp [curve]
    ring
  apply duplication_identity_algebra hy0
    (curve_equation hP)
  rw [← hx₂]
  simp only [addX]
  rw [hℓ]
  simp [curve]
  ring

private noncomputable def orderEightPolynomial : Polynomial ℤ :=
  Polynomial.X ^ 4 -
    Polynomial.C 16 * Polynomial.X ^ 3 +
    Polynomial.C 80 * Polynomial.X ^ 2 -
    Polynomial.C 256 * Polynomial.X +
    Polynomial.C 256

private lemma orderEightPolynomial_monic :
    Polynomial.Monic orderEightPolynomial := by
  unfold orderEightPolynomial
  monicity!

private lemma orderEightPolynomial_no_root_mod_seventeen :
    ∀ x : ZMod 17,
      x ^ 4 - 16 * x ^ 3 + 80 * x ^ 2 -
        256 * x + 256 ≠ 0 := by
  decide

private lemma orderEightPolynomial_no_rational_root (x : ℚ) :
    x ^ 4 - 16 * x ^ 3 + 80 * x ^ 2 -
      256 * x + 256 ≠ 0 := by
  intro hx
  have hroot :
      Polynomial.aeval x orderEightPolynomial = 0 := by
    rw [Polynomial.aeval_def]
    norm_num [orderEightPolynomial]
    exact hx
  obtain ⟨z, hxz, -⟩ :=
    exists_integer_of_is_root_of_monic
      orderEightPolynomial_monic hroot
  have hzrat :
      (z : ℚ) ^ 4 - 16 * (z : ℚ) ^ 3 +
          80 * (z : ℚ) ^ 2 - 256 * (z : ℚ) + 256 = 0 := by
    have hzcast : (z : ℚ) = x := by
      simpa using hxz.symm
    rw [hzcast]
    exact hx
  have hzint :
      z ^ 4 - 16 * z ^ 3 + 80 * z ^ 2 -
          256 * z + 256 = 0 := by
    exact_mod_cast hzrat
  apply orderEightPolynomial_no_root_mod_seventeen (z : ZMod 17)
  simpa using congrArg (fun n : ℤ ↦ (n : ZMod 17)) hzint

private def twoVisible :
    Fin 2 → {P : curve.toAffine.Point // (2 : ℕ) • P = 0}
  | 0 => ⟨0, by simp⟩
  | 1 => ⟨T, double_T_reduction⟩

private lemma twoVisible_injective :
    Function.Injective twoVisible := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [twoVisible, T] at hij ⊢

private lemma twoVisible_bijective :
    Function.Bijective twoVisible := by
  letI : Finite
      {P : curve.toAffine.Point // (2 : ℕ) • P = 0} :=
    MazurTorsion.finite_two_torsion curve
  exact twoVisible_injective.bijective_of_nat_card_le
    (by simpa using two_torsion_card_eq_two.le)

private lemma eq_zero_or_eq_T
    {P : curve.toAffine.Point} (hP : (2 : ℕ) • P = 0) :
    P = 0 ∨ P = T := by
  obtain ⟨i, hi⟩ := twoVisible_bijective.2 ⟨P, hP⟩
  fin_cases i
  · left
    simpa [twoVisible] using congrArg Subtype.val hi.symm
  · right
    simpa [twoVisible] using congrArg Subtype.val hi.symm

/-- No rational point on the chosen model has additive order eight. -/
theorem addOrderOf_ne_eight (Q : curve.toAffine.Point) :
    addOrderOf Q ≠ 8 := by
  intro hQorder
  let P : curve.toAffine.Point := (2 : ℕ) • Q
  have hPorder : addOrderOf P = 4 := by
    dsimp [P]
    rw [addOrderOf_nsmul' Q (by norm_num), hQorder]
    norm_num
  have hdoublePorder :
      addOrderOf ((2 : ℕ) • P) = 2 := by
    rw [addOrderOf_nsmul' P (by norm_num), hPorder]
    norm_num
  have hdoublePtwo :
      (2 : ℕ) • ((2 : ℕ) • P) = 0 := by
    apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
    rw [hdoublePorder]
  have hdoublePne :
      (2 : ℕ) • P ≠ 0 := by
    intro hzero
    have hdiv : addOrderOf P ∣ 2 :=
      addOrderOf_dvd_of_nsmul_eq_zero hzero
    rw [hPorder] at hdiv
    norm_num at hdiv
  have hdoubleP :
      (2 : ℕ) • P = T :=
    (eq_zero_or_eq_T hdoublePtwo).resolve_left hdoublePne
  have hPne : P ≠ 0 := by
    intro hzero
    rw [hzero] at hPorder
    norm_num at hPorder
  obtain ⟨xP, yP, hPns, hPcoords⟩ :
      ∃ (x y : ℚ) (h : curve.toAffine.Nonsingular x y),
        P = Point.some x y h := by
    cases hcase : P with
    | zero => exact (hPne hcase).elim
    | some x y h => exact ⟨x, y, h, rfl⟩
  have hPTcoords :
      (2 : ℕ) • Point.some xP yP hPns =
        Point.some 0 0
          (by
            apply curve.toAffine.equation_iff_nonsingular.mp
            norm_num [WeierstrassCurve.Affine.equation_iff, curve]) := by
    simpa only [hPcoords, T] using hdoubleP
  have hdupP :=
    duplication_identity_of_double hPns _ hPTcoords
  have hxPsq : xP ^ 2 = 16 := by
    have hsquare : (xP ^ 2 - 16) ^ 2 = 0 := by
      simpa using hdupP.symm
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
  have hxP : xP = 4 := by
    have hcases : xP = 4 ∨ xP = -4 := by
      apply (sq_eq_sq_iff_eq_or_eq_neg).mp
      norm_num
      exact hxPsq
    rcases hcases with hxP | hxP
    · exact hxP
    · have hcurveP := curve_equation hPns
      rw [hxP] at hcurveP
      norm_num at hcurveP
      nlinarith [sq_nonneg yP]
  have hQne : Q ≠ 0 := by
    intro hzero
    rw [hzero] at hQorder
    norm_num at hQorder
  obtain ⟨xQ, yQ, hQns, hQcoords⟩ :
      ∃ (x y : ℚ) (h : curve.toAffine.Nonsingular x y),
        Q = Point.some x y h := by
    cases hcase : Q with
    | zero => exact (hQne hcase).elim
    | some x y h => exact ⟨x, y, h, rfl⟩
  have hQPcoords :
      (2 : ℕ) • Point.some xQ yQ hQns =
        Point.some xP yP hPns := by
    rw [← hQcoords, ← hPcoords]
  have hdupQ :=
    duplication_identity_of_double hQns hPns hQPcoords
  have hcurveQ := curve_equation hQns
  apply orderEightPolynomial_no_rational_root xQ
  rw [hxP] at hdupQ
  nlinarith [hdupQ, hcurveQ]

private lemma point_card_ne_eight :
    Nat.card curve.toAffine.Point ≠ 8 := by
  letI : Finite curve.toAffine.Point := point_finite
  intro hcard
  let f : curve.toAffine.Point →+ curve.toAffine.Point :=
    nsmulAddMonoidHom 2
  have hker : Nat.card f.ker = 2 := by
    change Nat.card
      {P : curve.toAffine.Point // (2 : ℕ) • P = 0} = 2
    exact two_torsion_card_eq_two
  have hrangeCard : Nat.card f.range = 4 := by
    have hproduct := f.ker.index_mul_card
    rw [AddSubgroup.index_ker, hker, hcard] at hproduct
    omega
  have hfour (P : curve.toAffine.Point) :
      (4 : ℕ) • P = 0 := by
    have hdvd : addOrderOf P ∣ 8 := by
      simpa [hcard] using addOrderOf_dvd_natCard P
    have hdvdpow : addOrderOf P ∣ 2 ^ 3 := by
      norm_num
      exact hdvd
    obtain ⟨k, hk, horder⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two).mp hdvdpow
    have hk2 : k ≤ 2 := by
      by_contra hknot
      have hk3 : k = 3 := by omega
      apply addOrderOf_ne_eight P
      rw [horder, hk3]
      norm_num
    apply addOrderOf_dvd_iff_nsmul_eq_zero.mp
    rw [horder]
    interval_cases k <;> norm_num
  have hrange_le_ker : f.range ≤ f.ker := by
    rintro R ⟨P, rfl⟩
    change (2 : ℕ) • ((2 : ℕ) • P) = 0
    calc
      (2 : ℕ) • ((2 : ℕ) • P) =
          (4 : ℕ) • P := by
        rw [← mul_nsmul]
      _ = 0 := hfour P
  have hle : Nat.card f.range ≤ Nat.card f.ker :=
    AddSubgroup.card_le_of_le hrange_le_ker
  rw [hrangeCard, hker] at hle
  omega

/-- The chosen `X₁(15)` model has exactly four rational points. -/
theorem point_card_eq_four :
    Nat.card curve.toAffine.Point = 4 := by
  letI : Finite curve.toAffine.Point := point_finite
  have hle := point_card_le_eight
  have hdiv : 4 ∣ Nat.card curve.toAffine.Point := by
    rw [← addOrderOf_G]
    exact addOrderOf_dvd_natCard G
  obtain ⟨k, hk⟩ := hdiv
  have hpos : 0 < Nat.card curve.toAffine.Point :=
    Nat.card_pos
  have hcases :
      Nat.card curve.toAffine.Point = 4 ∨
        Nat.card curve.toAffine.Point = 8 := by
    omega
  exact hcases.resolve_right point_card_ne_eight

/-- The four visible rational points. -/
private lemma nonsingular_four_neg_four_reduction :
    curve.toAffine.Nonsingular 4 (-4) := by
  apply curve.toAffine.equation_iff_nonsingular.mp
  norm_num [WeierstrassCurve.Affine.equation_iff, curve]

def fourVisiblePoints : Fin 4 → curve.toAffine.Point
  | 0 => 0
  | 1 => T
  | 2 => G
  | 3 => .some 4 (-4) nonsingular_four_neg_four_reduction

theorem fourVisiblePoints_injective :
    Function.Injective fourVisiblePoints := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [fourVisiblePoints, T, G] at hij ⊢
  all_goals norm_num at hij

/-- The four visible points exhaust the rational point group. -/
theorem fourVisiblePoints_bijective :
    Function.Bijective fourVisiblePoints := by
  letI : Finite curve.toAffine.Point := point_finite
  exact fourVisiblePoints_injective.bijective_of_nat_card_le
    (by simp [point_card_eq_four])

/-- Every affine rational point on the chosen model has abscissa zero or
four. -/
theorem point_abscissa_eq_zero_or_four
    {U V : ℚ}
    (hP : curve.toAffine.Nonsingular U V) :
    U = 0 ∨ U = 4 := by
  let P : curve.toAffine.Point := .some U V hP
  obtain ⟨i, hi⟩ := fourVisiblePoints_bijective.2 P
  fin_cases i
  · have hzero : P ≠ 0 := Point.some_ne_zero hP
    exact (hzero (by
      simpa only [fourVisiblePoints] using hi.symm)).elim
  · left
    have hcoords : (0 : ℚ) = U ∧ (0 : ℚ) = V := by
      simpa only [fourVisiblePoints, T, P,
        Point.some.injEq] using hi
    exact hcoords.1.symm
  · right
    have hcoords : (4 : ℚ) = U ∧ (4 : ℚ) = V := by
      simpa only [fourVisiblePoints, G, P,
        Point.some.injEq] using hi
    exact hcoords.1.symm
  · right
    have hcoords : (4 : ℚ) = U ∧ (-4 : ℚ) = V := by
      simpa only [fourVisiblePoints, G, P,
        Point.some.injEq] using hi
    exact hcoords.1.symm

end MazurTorsion.XOneFifteen

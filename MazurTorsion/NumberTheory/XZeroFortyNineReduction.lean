/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import EllipticCurves.ReductionAtPrime
import MazurTorsion.NumberTheory.XZeroFortyNineDescent

/-!
# Rational points on the `X₀(49)` model

The two-isogeny descent proves that the rational point group of

`y² = x(x² + 21x + 112)`

is finite with no point of order four.  Good reduction at three bounds
the cardinality by four, and an element of order three would force the
cardinality to be at least six.  Hence every rational point is killed by
two, and the group is exactly `{0, (0,0)}`: the two rational cusps of
`X₀(49)`.
-/

open WeierstrassCurve

namespace MazurTorsion.XZeroFortyNine

open WeierstrassCurve.Affine
  IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- The integral model used for reduction at three. -/
def integralCurve : WeierstrassCurve ℤ :=
  ⟨0, 21, 0, 112, 0⟩

lemma map_integralCurve :
    (integralCurve.map (algebraMap ℤ ℚ)).toAffine =
      curve.toAffine := by
  ext <;> simp [integralCurve, curve]

lemma discriminant_integralCurve :
    integralCurve.Δ = -1404928 := by
  norm_num [integralCurve, WeierstrassCurve.Δ,
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

instance :
    (redCurve (intPrime 3) integralCurve).IsElliptic := by
  rw [isElliptic_iff, isUnit_iff_ne_zero]
  change (integralCurve.map
    (algebraMap ℤ (ℤ ⧸ (intPrime 3).asIdeal))).Δ ≠ 0
  rw [Ne, map_Δ, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem,
    intPrime_asIdeal, Ideal.mem_span_singleton,
    discriminant_integralCurve]
  norm_num

/-- The concrete reduction over `ZMod 3`. -/
def curveModThree : WeierstrassCurve (ZMod 3) :=
  ⟨0, 21, 0, 112, 0⟩

instance : curveModThree.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  decide

noncomputable def residueThreeAlgEquiv :
    (ℤ ⧸ (intPrime 3).asIdeal) ≃ₐ[ℤ] ZMod 3 :=
  AlgEquiv.ofRingEquiv
    (f := Int.quotientSpanNatEquivZMod 3) fun x ↦ by
      simp only [algebraMap_int_eq, eq_intCast, map_intCast]

lemma baseChange_modThree :
    ((integralCurve.toAffine ⁄ (ZMod 3)) :
      WeierstrassCurve _).toAffine =
        curveModThree.toAffine := by
  ext <;> decide +kernel

/-- Identification of the abstract residue-field point group with the
computable `ZMod 3` point group. -/
noncomputable def reducedPointEquiv :
    (redCurve (intPrime 3) integralCurve).Point ≃+
      curveModThree.toAffine.Point :=
  (Point.mapEquiv (W' := integralCurve.toAffine)
      residueThreeAlgEquiv).trans
    (Point.congr baseChange_modThree)

noncomputable instance :
    Finite (redCurve (intPrime 3) integralCurve).Point :=
  .of_equiv curveModThree.toAffine.Point
    reducedPointEquiv.symm.toEquiv

/-- The reduction modulo three has exactly four points. -/
theorem card_reducedCurve :
    Nat.card
      (redCurve (intPrime 3) integralCurve).Point = 4 := by
  calc
    Nat.card
        (redCurve (intPrime 3) integralCurve).Point =
        Fintype.card curveModThree.toAffine.Point :=
      (Nat.card_congr reducedPointEquiv.toEquiv).trans
        Nat.card_eq_fintype_card
    _ = 4 := by decide

lemma three_mem_prime :
    (3 : ℤ) ∈ (intPrime 3).asIdeal :=
  Ideal.mem_span_singleton_self 3

lemma three_not_mem_prime_pow_two :
    (3 : ℤ) ∉ (intPrime 3).asIdeal ^ (3 - 1) := by
  rw [intPrime_asIdeal, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  norm_num

/-- Reduction at three is injective on the finite rational point group. -/
theorem reduction_injective [Finite curve.toAffine.Point] :
    Function.Injective
      (redHom (intPrime 3) map_integralCurve) := by
  intro P Q hPQ
  apply sub_eq_zero.mp
  apply eq_zero_of_isOfFinAddOrder_of_red_eq_zero
    (intPrime 3) map_integralCurve
    (by norm_num) three_mem_prime
    three_not_mem_prime_pow_two
    (isOfFinAddOrder_of_finite (P - Q))
  change
    redHom (intPrime 3) map_integralCurve (P - Q) = 0
  rw [map_sub, hPQ, sub_self]

/-- There are at most four rational points on the `X₀(49)` model. -/
theorem point_card_le_four :
    Nat.card curve.toAffine.Point ≤ 4 := by
  letI : Finite curve.toAffine.Point := point_finite
  calc
    Nat.card curve.toAffine.Point ≤
        Nat.card
          (redCurve (intPrime 3) integralCurve).Point :=
      Nat.card_le_card_of_injective
        (redHom (intPrime 3) map_integralCurve)
        reduction_injective
    _ = 4 := card_reducedCurve

/-- Every rational point of the `X₀(49)` model is `0` or `(0,0)`: the two
rational cusps. -/
theorem point_eq_zero_or_T (P : curve.toAffine.Point) :
    P = 0 ∨ P = T := by
  letI : Finite curve.toAffine.Point := point_finite
  have hcard := point_card_le_four
  have hcard_pos : 0 < Nat.card curve.toAffine.Point :=
    Nat.card_pos
  have hT0 : T ≠ 0 :=
    WeierstrassCurve.Affine.Point.some_ne_zero
      nonsingular_zero_zero
  have hT2smul : (2 : ℕ) • T = 0 := by
    simp only [two_nsmul]
    rw [T]
    apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
    norm_num [WeierstrassCurve.Affine.negY, curve]
  have hT2 : (2 : ℕ) ∣ Nat.card curve.toAffine.Point := by
    have hTorder : addOrderOf T = 2 := by
      have hdvd := addOrderOf_dvd_of_nsmul_eq_zero hT2smul
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exfalso
        apply hT0
        simpa [h1] using addOrderOf_nsmul_eq_zero T
      · exact h2
    rw [← hTorder]
    exact addOrderOf_dvd_natCard T
  have hP2 : (2 : ℕ) • P = 0 := by
    have horder := addOrderOf_dvd_natCard P
    have hpos : 0 < addOrderOf P :=
      (isOfFinAddOrder_of_finite P).addOrderOf_pos
    have hle : addOrderOf P ≤ 4 :=
      (Nat.le_of_dvd hcard_pos horder).trans hcard
    interval_cases h : addOrderOf P
    · -- order one
      have h1 := addOrderOf_nsmul_eq_zero P
      rw [h, one_nsmul] at h1
      rw [h1, smul_zero]
    · -- order two
      rw [← h]
      exact addOrderOf_nsmul_eq_zero P
    · -- order three forces cardinality at least six
      exfalso
      have h3 : (3 : ℕ) ∣ Nat.card curve.toAffine.Point := by
        rw [← h]
        exact addOrderOf_dvd_natCard P
      have h6 : (6 : ℕ) ∣ Nat.card curve.toAffine.Point :=
        Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) hT2 h3
      have := Nat.le_of_dvd hcard_pos h6
      omega
    · -- order four is impossible
      exfalso
      have h4 : (4 : ℕ) • P = 0 := by
        rw [← h]
        exact addOrderOf_nsmul_eq_zero P
      have h22 : (2 : ℕ) • ((2 : ℕ) • P) = 0 := by
        rw [← mul_nsmul]
        exact h4
      have h20 : (2 : ℕ) • P ≠ 0 := by
        intro hzero
        have hdvd := addOrderOf_dvd_of_nsmul_eq_zero hzero
        rw [h] at hdvd
        omega
      have h2T : (2 : ℕ) • P = T := by
        rcases eq_zero_or_T_of_two_nsmul_eq_zero _ h22 with h0 | hT
        · exact absurd h0 h20
        · exact hT
      exact no_order_four P h2T
  exact eq_zero_or_T_of_two_nsmul_eq_zero P hP2

end MazurTorsion.XZeroFortyNine

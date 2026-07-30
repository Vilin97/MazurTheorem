/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import EllipticCurves.ReductionAtPrime
import MazurTorsion.NumberTheory.XZeroTwentyOneRankZero

/-!
# Rational points on the split `X₀(21)` model

The two-isogeny descent proves that the rational point group of

`W² = V(V - 9)(V + 7)`

is finite and exhibits eight distinct points.  This file applies good
reduction at five.  The reduced curve has exactly eight points, and the
reduction map is injective on the finite rational point group.
Consequently the eight visible points exhaust the rational points, and
every finite point has abscissa `0`, `9`, `-7`, `-3`, or `21`.

This closes both quartic leaves isolated by `XZeroTwentyOneDescent`:
`PrincipalQuarticClassified` and `NegativeThreeQuarticClassified` become
theorems, and the conditional classifications of that file hold
unconditionally.
-/

open WeierstrassCurve

namespace MazurTorsion.XZeroTwentyOne

open WeierstrassCurve.Affine
  IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The integral model used for reduction at five. -/
def integralCurve : WeierstrassCurve ℤ :=
  ⟨0, -2, 0, -63, 0⟩

lemma map_integralCurve :
    (integralCurve.map (algebraMap ℤ ℚ)).toAffine =
      fullTwoCurve.toAffine := by
  ext <;> simp [integralCurve, fullTwoCurve]

lemma discriminant_integralCurve :
    integralCurve.Δ = 16257024 := by
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
    (redCurve (intPrime 5) integralCurve).IsElliptic := by
  rw [isElliptic_iff, isUnit_iff_ne_zero]
  change (integralCurve.map
    (algebraMap ℤ (ℤ ⧸ (intPrime 5).asIdeal))).Δ ≠ 0
  rw [Ne, map_Δ, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem,
    intPrime_asIdeal, Ideal.mem_span_singleton,
    discriminant_integralCurve]
  norm_num

/-- The concrete reduction over `ZMod 5`. -/
def curveModFive : WeierstrassCurve (ZMod 5) :=
  ⟨0, -2, 0, -63, 0⟩

instance : curveModFive.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  decide

noncomputable def residueFiveAlgEquiv :
    (ℤ ⧸ (intPrime 5).asIdeal) ≃ₐ[ℤ] ZMod 5 :=
  AlgEquiv.ofRingEquiv
    (f := Int.quotientSpanNatEquivZMod 5) fun x ↦ by
      simp only [algebraMap_int_eq, eq_intCast, map_intCast]

lemma baseChange_modFive :
    ((integralCurve.toAffine ⁄ (ZMod 5)) :
      WeierstrassCurve _).toAffine =
        curveModFive.toAffine := by
  ext <;> decide +kernel

/-- Identification of the abstract residue-field point group with the
computable `ZMod 5` point group. -/
noncomputable def reducedPointEquiv :
    (redCurve (intPrime 5) integralCurve).Point ≃+
      curveModFive.toAffine.Point :=
  (Point.mapEquiv (W' := integralCurve.toAffine)
      residueFiveAlgEquiv).trans
    (Point.congr baseChange_modFive)

noncomputable instance :
    Finite (redCurve (intPrime 5) integralCurve).Point :=
  .of_equiv curveModFive.toAffine.Point
    reducedPointEquiv.symm.toEquiv

/-- The reduction modulo five has exactly eight points. -/
theorem card_reducedCurve :
    Nat.card
      (redCurve (intPrime 5) integralCurve).Point = 8 := by
  calc
    Nat.card
        (redCurve (intPrime 5) integralCurve).Point =
        Fintype.card curveModFive.toAffine.Point :=
      (Nat.card_congr reducedPointEquiv.toEquiv).trans
        Nat.card_eq_fintype_card
    _ = 8 := by decide

lemma five_mem_prime :
    (5 : ℤ) ∈ (intPrime 5).asIdeal :=
  Ideal.mem_span_singleton_self 5

lemma five_not_mem_prime_pow_four :
    (5 : ℤ) ∉ (intPrime 5).asIdeal ^ (5 - 1) := by
  rw [intPrime_asIdeal, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  norm_num

/-- Reduction at five is injective on the finite rational point group. -/
theorem reduction_injective
    [Finite fullTwoCurve.toAffine.Point] :
    Function.Injective
      (redHom (intPrime 5) map_integralCurve) := by
  intro P Q hPQ
  apply sub_eq_zero.mp
  apply eq_zero_of_isOfFinAddOrder_of_red_eq_zero
    (intPrime 5) map_integralCurve
    (by norm_num) five_mem_prime
    five_not_mem_prime_pow_four
    (isOfFinAddOrder_of_finite (P - Q))
  change
    redHom (intPrime 5) map_integralCurve (P - Q) = 0
  rw [map_sub, hPQ, sub_self]

/-- There are at most eight rational points on the split model. -/
theorem point_card_le_eight :
    Nat.card fullTwoCurve.toAffine.Point ≤ 8 := by
  letI : Finite fullTwoCurve.toAffine.Point := point_finite
  calc
    Nat.card fullTwoCurve.toAffine.Point ≤
        Nat.card
          (redCurve (intPrime 5) integralCurve).Point :=
      Nat.card_le_card_of_injective
        (redHom (intPrime 5) map_integralCurve)
        reduction_injective
    _ = 8 := card_reducedCurve

/-- The eight points constructed by the descent file exhaust the rational
point group. -/
theorem eightVisiblePoints_bijective :
    Function.Bijective eightVisiblePoints := by
  letI : Finite fullTwoCurve.toAffine.Point := point_finite
  exact
    eightVisiblePoints_injective.bijective_of_nat_card_le
      (by simpa using point_card_le_eight)

/-- Every affine rational point of the split model is one of the seven
visible affine points. -/
theorem fullTwo_point_classification
    {U V : ℚ}
    (hP : fullTwoCurve.toAffine.Nonsingular U V) :
    (U = 0 ∧ V = 0) ∨
    (U = 9 ∧ V = 0) ∨
    (U = -7 ∧ V = 0) ∨
    (U = -3 ∧ V = 12) ∨
    (U = -3 ∧ V = -12) ∨
    (U = 21 ∧ V = 84) ∨
    (U = 21 ∧ V = -84) := by
  let P : fullTwoCurve.toAffine.Point := .some U V hP
  obtain ⟨i, hi⟩ :=
    eightVisiblePoints_bijective.2 P
  fin_cases i
  · exfalso
    have hzero : P ≠ 0 :=
      WeierstrassCurve.Affine.Point.some_ne_zero hP
    exact hzero
      (by simpa only [eightVisiblePoints] using hi.symm)
  · left
    have hcoords : (0 : ℚ) = U ∧ (0 : ℚ) = V := by
      simpa only [eightVisiblePoints, T, P,
        WeierstrassCurve.Affine.Point.some.injEq] using hi
    exact ⟨hcoords.1.symm, hcoords.2.symm⟩
  · right; left
    have hcoords : (9 : ℚ) = U ∧ (0 : ℚ) = V := by
      simpa only [eightVisiblePoints, T₉, P,
        WeierstrassCurve.Affine.Point.some.injEq] using hi
    exact ⟨hcoords.1.symm, hcoords.2.symm⟩
  · right; right; left
    have hcoords : (-7 : ℚ) = U ∧ (0 : ℚ) = V := by
      simpa only [eightVisiblePoints, T₇, P,
        WeierstrassCurve.Affine.Point.some.injEq] using hi
    exact ⟨hcoords.1.symm, hcoords.2.symm⟩
  · right; right; right; left
    have hcoords : (-3 : ℚ) = U ∧ (12 : ℚ) = V := by
      simpa only [eightVisiblePoints, P₃, P,
        WeierstrassCurve.Affine.Point.some.injEq] using hi
    exact ⟨hcoords.1.symm, hcoords.2.symm⟩
  · right; right; right; right; left
    have hcoords : (-3 : ℚ) = U ∧ (-12 : ℚ) = V := by
      simpa only [eightVisiblePoints, P₃neg, P,
        WeierstrassCurve.Affine.Point.some.injEq] using hi
    exact ⟨hcoords.1.symm, hcoords.2.symm⟩
  · right; right; right; right; right; left
    have hcoords : (21 : ℚ) = U ∧ (84 : ℚ) = V := by
      simpa only [eightVisiblePoints, P₂₁, P,
        WeierstrassCurve.Affine.Point.some.injEq] using hi
    exact ⟨hcoords.1.symm, hcoords.2.symm⟩
  · right; right; right; right; right; right
    have hcoords : (21 : ℚ) = U ∧ (-84 : ℚ) = V := by
      simpa only [eightVisiblePoints, P₂₁neg, P,
        WeierstrassCurve.Affine.Point.some.injEq] using hi
    exact ⟨hcoords.1.symm, hcoords.2.symm⟩

/-- Unconditional abscissa classification on the split model. -/
theorem abscissa_eq_of_onFullTwoCurve
    {V W : ℚ} (h : OnFullTwoCurve V W) :
    V = 0 ∨ V = 9 ∨ V = -7 ∨ V = -3 ∨ V = 21 := by
  rcases fullTwo_point_classification
      (nonsingular_of_onFullTwoCurve h) with
      ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ |
        ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h1)))

/-! ## The two quartic leaves become theorems -/

private lemma not_sq_eq_twentyOne_mul_sq
    {m n : ℤ} (hmn : IsCoprime m n)
    (h : m ^ 2 = 21 * n ^ 2) : False := by
  have h3 : (3 : ℤ) ∣ m := by
    have h3sq : (3 : ℤ) ∣ m ^ 2 := ⟨7 * n ^ 2, by linear_combination h⟩
    exact (Int.Prime.dvd_pow' (by norm_num) h3sq)
  obtain ⟨k, hk⟩ := h3
  have h9 : 9 * k ^ 2 = 21 * n ^ 2 := by
    rw [hk] at h
    linear_combination h
  have h3n : (3 : ℤ) ∣ n := by
    have h3sq : (3 : ℤ) ∣ n ^ 2 := by
      have h7 : 3 * k ^ 2 = 7 * n ^ 2 := by linarith
      have hdvd : (3 : ℤ) ∣ 7 * n ^ 2 := ⟨k ^ 2, by linarith⟩
      rcases (Int.Prime.dvd_mul' (by norm_num) hdvd) with h' | h'
      · norm_num at h'
      · exact h'
    exact (Int.Prime.dvd_pow' (by norm_num) h3sq)
  have : IsUnit (3 : ℤ) := hmn.isUnit_of_dvd' ⟨k, hk⟩ h3n
  norm_num [Int.isUnit_iff] at this

private lemma not_three_mul_sq_eq_seven_mul_sq
    {m n : ℤ} (hmn : IsCoprime m n)
    (h : 3 * m ^ 2 = 7 * n ^ 2) : False := by
  have h7 : (7 : ℤ) ∣ m := by
    have h7sq : (7 : ℤ) ∣ m ^ 2 := by
      have hdvd : (7 : ℤ) ∣ 3 * m ^ 2 := ⟨n ^ 2, by linear_combination h⟩
      rcases (Int.Prime.dvd_mul' (by norm_num) hdvd) with h' | h'
      · norm_num at h'
      · exact h'
    exact (Int.Prime.dvd_pow' (by norm_num) h7sq)
  obtain ⟨k, hk⟩ := h7
  have h49 : 3 * (49 * k ^ 2) = 7 * n ^ 2 := by
    rw [hk] at h
    linear_combination h
  have h7n : (7 : ℤ) ∣ n := by
    have h7sq : (7 : ℤ) ∣ n ^ 2 := by
      have h21 : 21 * k ^ 2 = n ^ 2 := by linarith
      exact ⟨3 * k ^ 2, by linarith⟩
    exact (Int.Prime.dvd_pow' (by norm_num) h7sq)
  have : IsUnit (7 : ℤ) := hmn.isUnit_of_dvd' ⟨k, hk⟩ h7n
  norm_num [Int.isUnit_iff] at this

/-- The principal quartic leaf, now a theorem. -/
theorem principalQuarticClassified : PrincipalQuarticClassified := by
  intro m n c hmn hc
  by_cases hm : m = 0
  · exact Or.inl hm
  by_cases hn : n = 0
  · exact Or.inr (Or.inl hn)
  right; right
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  set V : ℚ := ((m : ℚ) / n) ^ 2 with hVdef
  set W : ℚ := (m : ℚ) * c / n ^ 3 with hWdef
  have hOn : OnFullTwoCurve V W := by
    unfold OnFullTwoCurve
    rw [hVdef, hWdef]
    have hcQ : (c : ℚ) ^ 2 =
        (m : ℚ) ^ 4 - 2 * m ^ 2 * n ^ 2 - 63 * n ^ 4 := by
      exact_mod_cast congrArg (fun z : ℤ ↦ (z : ℚ)) hc
    field_simp
    linear_combination hcQ
  have hVpos : 0 < V := by
    rw [hVdef]
    positivity
  rcases abscissa_eq_of_onFullTwoCurve hOn with
      h | h | h | h | h
  · exact absurd h (by positivity)
  · -- `V = 9` forces `m² = 9n²`
    rw [hVdef] at h
    have : (m : ℚ) ^ 2 = 9 * n ^ 2 := by
      field_simp at h
      linear_combination h
    exact_mod_cast this
  · exact absurd h (by intro h'; rw [h'] at hVpos; norm_num at hVpos)
  · exact absurd h (by intro h'; rw [h'] at hVpos; norm_num at hVpos)
  · -- `V = 21` contradicts primitivity
    exfalso
    rw [hVdef] at h
    have h21 : (m : ℚ) ^ 2 = 21 * n ^ 2 := by
      field_simp at h
      linear_combination h
    exact not_sq_eq_twentyOne_mul_sq hmn (by exact_mod_cast h21)

/-- The second quartic leaf, now a theorem. -/
theorem negativeThreeQuarticClassified :
    NegativeThreeQuarticClassified := by
  intro m n c hmn hc
  by_cases hm : m = 0
  · exact Or.inl hm
  by_cases hn : n = 0
  · exact Or.inr (Or.inl hn)
  right; right
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  set V : ℚ := -(3 * ((m : ℚ) / n) ^ 2) with hVdef
  set W : ℚ := 3 * (m : ℚ) * c / n ^ 3 with hWdef
  have hOn : OnFullTwoCurve V W := by
    unfold OnFullTwoCurve
    rw [hVdef, hWdef]
    have hcQ : (c : ℚ) ^ 2 =
        -3 * (m : ℚ) ^ 4 - 2 * m ^ 2 * n ^ 2 + 21 * n ^ 4 := by
      exact_mod_cast congrArg (fun z : ℤ ↦ (z : ℚ)) hc
    field_simp
    linear_combination 3 * hcQ
  have hVneg : V < 0 := by
    rw [hVdef]
    have : 0 < 3 * ((m : ℚ) / n) ^ 2 := by positivity
    linarith
  rcases abscissa_eq_of_onFullTwoCurve hOn with
      h | h | h | h | h
  · exact absurd h (by intro h'; rw [h'] at hVneg; norm_num at hVneg)
  · exact absurd h (by intro h'; rw [h'] at hVneg; norm_num at hVneg)
  · -- `V = -7` contradicts primitivity
    exfalso
    rw [hVdef] at h
    have h37 : 3 * (m : ℚ) ^ 2 = 7 * n ^ 2 := by
      field_simp at h
      linear_combination -h
    exact not_three_mul_sq_eq_seven_mul_sq hmn (by exact_mod_cast h37)
  · -- `V = -3` forces `m² = n²`
    rw [hVdef] at h
    have : (m : ℚ) ^ 2 = n ^ 2 := by
      field_simp at h
      linear_combination -h
    exact_mod_cast this
  · exact absurd h (by intro h'; rw [h'] at hVneg; norm_num at hVneg)

/-! ## The unconditional classifications -/

/-- Every affine rational point of the minimal conductor-`21` model is one
of the seven listed points, unconditionally. -/
theorem curve_affine_classification_unconditional
    {x y : ℚ} (hcurve : OnCurve x y) :
    (x = -1 / 4 ∧ y = 1 / 8) ∨
    (x = 2 ∧ y = -1) ∨
    (x = -2 ∧ y = 1) ∨
    (x = -1 ∧ y = 2) ∨
    (x = -1 ∧ y = -1) ∨
    (x = 5 ∧ y = 8) ∨
    (x = 5 ∧ y = -13) :=
  curve_affine_classification
    principalQuarticClassified negativeThreeQuarticClassified hcurve

/-- Every affine rational solution of the split model is one of the seven
listed points, unconditionally. -/
theorem fullTwo_affine_classification_unconditional
    {V W : ℚ} (hcurve : OnFullTwoCurve V W) :
    (V = 0 ∧ W = 0) ∨
    (V = 9 ∧ W = 0) ∨
    (V = -7 ∧ W = 0) ∨
    (V = -3 ∧ W = 12) ∨
    (V = -3 ∧ W = -12) ∨
    (V = 21 ∧ W = 84) ∨
    (V = 21 ∧ W = -84) :=
  fullTwo_affine_classification
    principalQuarticClassified negativeThreeQuarticClassified hcurve

end MazurTorsion.XZeroTwentyOne

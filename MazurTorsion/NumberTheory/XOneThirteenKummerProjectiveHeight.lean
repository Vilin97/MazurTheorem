/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Int.Interval
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import MazurTorsion.NumberTheory.XOneThirteenAbstractHalvingDescent

/-!
# Finite-height integral coordinates for the `X₁(13)` Kummer target

Once rational projective coordinates have been cleared and made primitive,
their remaining sign ambiguity can be fixed deterministically.  This file
packages that integral target for the abstract halving descent:

* four integral coordinates which are not all zero;
* gcd of their absolute values equal to one;
* the first nonzero coordinate positive;
* height equal to the maximum absolute value of the four coordinates.

The sign-normalization operation is defined and checked for every already
primitive integral representative.  Each normalized record also maps to an
actual Mathlib `Projectivization ℚ (Fin 4 → ℚ)` point, and normalization is
proved not to change that point.

Most importantly, every natural-height sublevel of these normalized records
is finite.  The proof injects it into four copies of the finite integer
interval `[-N, N]`.  No Kummer equation, duplication map, Jacobian, or
collision theorem is asserted here.  Clearing denominators and dividing the
content of an arbitrary rational vector are intentionally left to the future
curve-specific Kummer map.
-/

namespace MazurTorsion.XOneThirteenKummerProjectiveHeight

open scoped LinearAlgebra.Projectivization

/-- Four integral homogeneous coordinates. -/
abbrev IntegralFour := Fin 4 → ℤ

/-- The first nonzero coordinate, in the standard order `0,1,2,3`, is
positive.  Writing the four cases explicitly keeps sign normalization fully
computable and independent of any choice of a minimal support index. -/
def IsSignNormalized (v : IntegralFour) : Prop :=
  0 < v 0 ∨
    (v 0 = 0 ∧ 0 < v 1) ∨
    (v 0 = 0 ∧ v 1 = 0 ∧ 0 < v 2) ∨
    (v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0 ∧ 0 < v 3)

instance (v : IntegralFour) : Decidable (IsSignNormalized v) := by
  unfold IsSignNormalized
  infer_instance

/-- A nonzero vector or its negative has the prescribed sign. -/
theorem isSignNormalized_or_neg (v : IntegralFour) (hv : v ≠ 0) :
    IsSignNormalized v ∨ IsSignNormalized (-v) := by
  by_cases h0 : v 0 = 0
  · by_cases h1 : v 1 = 0
    · by_cases h2 : v 2 = 0
      · by_cases h3 : v 3 = 0
        · exact (hv (by funext i; fin_cases i <;> simp_all)).elim
        · rcases lt_or_gt_of_ne h3 with h3neg | h3pos
          · right
            simp only [IsSignNormalized, Pi.neg_apply]
            omega
          · left
            simp only [IsSignNormalized]
            omega
      · rcases lt_or_gt_of_ne h2 with h2neg | h2pos
        · right
          simp only [IsSignNormalized, Pi.neg_apply]
          omega
        · left
          simp only [IsSignNormalized]
          omega
    · rcases lt_or_gt_of_ne h1 with h1neg | h1pos
      · right
        simp only [IsSignNormalized, Pi.neg_apply]
        omega
      · left
        simp only [IsSignNormalized]
        omega
  · rcases lt_or_gt_of_ne h0 with h0neg | h0pos
    · right
      simp only [IsSignNormalized, Pi.neg_apply]
      omega
    · left
      simp only [IsSignNormalized]
      omega

/-- A sign-normalized nonzero vector cannot have its negative normalized as
well. -/
theorem not_isSignNormalized_neg (v : IntegralFour)
    (hv : IsSignNormalized v) : ¬IsSignNormalized (-v) := by
  intro hneg
  simp only [IsSignNormalized, Pi.neg_apply] at hv hneg
  rcases hv with hv | hv | hv | hv <;>
    rcases hneg with hneg | hneg | hneg | hneg <;> omega

/-- For a nonzero vector, negation reverses the normalization predicate. -/
theorem isSignNormalized_neg_iff_not (v : IntegralFour) (hv : v ≠ 0) :
    IsSignNormalized (-v) ↔ ¬IsSignNormalized v := by
  constructor
  · intro hneg h
    exact not_isSignNormalized_neg v h hneg
  · intro h
    rcases isSignNormalized_or_neg v hv with hpos | hneg
    · exact (h hpos).elim
    · exact hneg

/-- Choose the unique sign for which the first nonzero coordinate is
positive. -/
def signNormalize (v : IntegralFour) : IntegralFour :=
  if IsSignNormalized v then v else -v

/-- Sign normalization changes a vector by at most a factor `-1`. -/
theorem signNormalize_eq_or_eq_neg (v : IntegralFour) :
    signNormalize v = v ∨ signNormalize v = -v := by
  by_cases h : IsSignNormalized v
  · left
    simp [signNormalize, h]
  · right
    simp [signNormalize, h]

/-- A nonzero vector becomes sign-normalized. -/
theorem signNormalize_isSignNormalized (v : IntegralFour) (hv : v ≠ 0) :
    IsSignNormalized (signNormalize v) := by
  by_cases h : IsSignNormalized v
  · simp [signNormalize, h]
  · have hneg := (isSignNormalized_neg_iff_not v hv).2 h
    simpa [signNormalize, h] using hneg

/-- Sign normalization never turns a nonzero vector into zero. -/
theorem signNormalize_ne_zero (v : IntegralFour) (hv : v ≠ 0) :
    signNormalize v ≠ 0 := by
  intro hzero
  rcases signNormalize_eq_or_eq_neg v with h | h
  · rw [h] at hzero
    exact hv hzero
  · rw [h] at hzero
    exact hv (neg_eq_zero.mp hzero)

/-- Normalizing either sign gives the same vector. -/
theorem signNormalize_neg (v : IntegralFour) (hv : v ≠ 0) :
    signNormalize (-v) = signNormalize v := by
  by_cases h : IsSignNormalized v
  · have hneg := not_isSignNormalized_neg v h
    rw [signNormalize, if_neg hneg, signNormalize, if_pos h]
    exact neg_neg v
  · have hneg := (isSignNormalized_neg_iff_not v hv).2 h
    rw [signNormalize, if_pos hneg, signNormalize, if_neg h]

/-- Gcd of the absolute values of the four coordinates. -/
def content (v : IntegralFour) : ℕ :=
  Finset.univ.gcd fun i => (v i).natAbs

/-- The normalized integer gcd of a finite family is the natural gcd of its
absolute values, cast back to `ℤ`. -/
private theorem int_finset_gcd_eq_natAbs_finset_gcd
    {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    s.gcd f = ((s.gcd (fun i => (f i).natAbs) : ℕ) : ℤ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.gcd_insert, Finset.gcd_insert, ih, ← Int.coe_gcd,
        Int.gcd_eq_natAbs]
      simp
      rfl

@[simp]
theorem content_neg (v : IntegralFour) : content (-v) = content v := by
  simp [content]

@[simp]
theorem content_signNormalize (v : IntegralFour) :
    content (signNormalize v) = content v := by
  rcases signNormalize_eq_or_eq_neg v with h | h
  · rw [h]
  · rw [h, content_neg]

/-- A canonical primitive integral representative of a rational point of
projective three-space. -/
structure NormalizedPrimitiveFour where
  coords : IntegralFour
  nonzero : coords ≠ 0
  content_eq_one : content coords = 1
  sign_normalized : IsSignNormalized coords

namespace NormalizedPrimitiveFour

@[ext]
theorem ext {P Q : NormalizedPrimitiveFour} (h : P.coords = Q.coords) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

/-- Normalize the sign of an already primitive nonzero integral vector. -/
def ofPrimitive (v : IntegralFour) (hv : v ≠ 0) (hprimitive : content v = 1) :
    NormalizedPrimitiveFour where
  coords := signNormalize v
  nonzero := signNormalize_ne_zero v hv
  content_eq_one := by simpa using hprimitive
  sign_normalized := signNormalize_isSignNormalized v hv

@[simp]
theorem ofPrimitive_coords (v : IntegralFour) (hv : v ≠ 0)
    (hprimitive : content v = 1) :
    (ofPrimitive v hv hprimitive).coords = signNormalize v :=
  rfl

/-- The normalized coordinates are the supplied primitive coordinates or
their simultaneous negative. -/
theorem ofPrimitive_coords_eq_or_eq_neg (v : IntegralFour) (hv : v ≠ 0)
    (hprimitive : content v = 1) :
    (ofPrimitive v hv hprimitive).coords = v ∨
      (ofPrimitive v hv hprimitive).coords = -v :=
  signNormalize_eq_or_eq_neg v

/-- Primitive representatives which differ only by simultaneous negation
normalize to the same record. -/
theorem ofPrimitive_eq_of_eq_or_eq_neg
    (v w : IntegralFour) (hv : v ≠ 0) (hw : w ≠ 0)
    (hvPrimitive : content v = 1) (hwPrimitive : content w = 1)
    (h : w = v ∨ w = -v) :
    ofPrimitive w hw hwPrimitive = ofPrimitive v hv hvPrimitive := by
  apply ext
  rcases h with rfl | rfl
  · rfl
  · exact signNormalize_neg v hv

/-- Cast an integral coordinate vector to rational coordinates. -/
def rationalCoordinatesOf (v : IntegralFour) : Fin 4 → ℚ :=
  fun i => v i

/-- A nonzero integral vector remains nonzero after casting to `ℚ`. -/
theorem rationalCoordinatesOf_ne_zero (v : IntegralFour) (hv : v ≠ 0) :
    rationalCoordinatesOf v ≠ 0 := by
  intro hzero
  apply hv
  funext i
  have hi : (v i : ℚ) = 0 := by
    simpa [rationalCoordinatesOf] using congrFun hzero i
  exact_mod_cast hi

/-- Rational coordinates represented by a normalized record. -/
def rationalCoordinates (P : NormalizedPrimitiveFour) : Fin 4 → ℚ :=
  rationalCoordinatesOf P.coords

theorem rationalCoordinates_ne_zero (P : NormalizedPrimitiveFour) :
    P.rationalCoordinates ≠ 0 :=
  rationalCoordinatesOf_ne_zero P.coords P.nonzero

/-- Equality of the canonical rational coordinate vectors recovers equality
of normalized records. -/
theorem rationalCoordinates_injective :
    Function.Injective rationalCoordinates := by
  intro P Q h
  apply ext
  funext i
  have hi := congrFun h i
  change (P.coords i : ℚ) = (Q.coords i : ℚ) at hi
  exact_mod_cast hi

/-- The actual rational projective point represented by a normalized
integral record. -/
def toProjectivePoint (P : NormalizedPrimitiveFour) :
    Projectivization ℚ (Fin 4 → ℚ) :=
  Projectivization.mk ℚ P.rationalCoordinates P.rationalCoordinates_ne_zero

/-- The four primitive coordinates generate the unit ideal over `ℤ`. -/
private theorem exists_bezout_coefficients (P : NormalizedPrimitiveFour) :
    ∃ c : Fin 4 → ℤ, 1 = ∑ i, P.coords i * c i := by
  have hgcd : Finset.univ.gcd P.coords = (1 : ℤ) := by
    rw [int_finset_gcd_eq_natAbs_finset_gcd]
    change (content P.coords : ℤ) = 1
    simp [P.content_eq_one]
  obtain ⟨c, hc⟩ := Finset.gcd_eq_sum_mul Finset.univ P.coords
  refine ⟨c, ?_⟩
  simpa [hgcd] using hc

/-- If a rational scalar sends a primitive integral vector to another
integral vector, then that scalar is an integer. -/
private theorem scalar_eq_intCast_of_smul_rationalCoordinates
    (P Q : NormalizedPrimitiveFour) (a : ℚ)
    (h : a • Q.rationalCoordinates = P.rationalCoordinates) :
    ∃ k : ℤ, a = (k : ℚ) := by
  obtain ⟨c, hc⟩ := exists_bezout_coefficients Q
  let k : ℤ := ∑ i, P.coords i * c i
  refine ⟨k, ?_⟩
  have hcoord (i : Fin 4) :
      a * (Q.coords i : ℚ) = (P.coords i : ℚ) := by
    have hi := congrFun h i
    simpa [rationalCoordinates, rationalCoordinatesOf, smul_eq_mul] using hi
  have hcQ : ∑ i, (Q.coords i : ℚ) * (c i : ℚ) = 1 := by
    exact_mod_cast hc.symm
  calc
    a = a * 1 := by simp
    _ = a * ∑ i, (Q.coords i : ℚ) * (c i : ℚ) := by rw [hcQ]
    _ = ∑ i, (a * (Q.coords i : ℚ)) * (c i : ℚ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ∑ i, (P.coords i : ℚ) * (c i : ℚ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hcoord]
    _ = (k : ℚ) := by
      simp only [k]
      norm_cast

/-- A normalized primitive integral representative is the unique such
representative of its rational projective point. -/
theorem toProjectivePoint_injective :
    Function.Injective toProjectivePoint := by
  intro P Q hPQ
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff' ℚ _ _ _ _).1 hPQ
  have ha0 : a ≠ 0 := by
    intro hzero
    apply P.rationalCoordinates_ne_zero
    rw [← ha, hzero, zero_smul]
  obtain ⟨k, hak⟩ :=
    scalar_eq_intCast_of_smul_rationalCoordinates P Q a ha
  have hreverse : a⁻¹ • P.rationalCoordinates = Q.rationalCoordinates := by
    rw [← ha, ← mul_smul, inv_mul_cancel₀ ha0, one_smul]
  obtain ⟨l, hal⟩ :=
    scalar_eq_intCast_of_smul_rationalCoordinates Q P a⁻¹ hreverse
  have hkl_rat : (k : ℚ) * (l : ℚ) = 1 := by
    rw [← hak, ← hal, mul_inv_cancel₀ ha0]
  have hkl : k * l = 1 := by
    exact_mod_cast hkl_rat
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hkl with hk | hk
  · apply rationalCoordinates_injective
    calc
      P.rationalCoordinates = a • Q.rationalCoordinates := ha.symm
      _ = Q.rationalCoordinates := by simp [hak, hk]
  · have hcoords : P.coords = -Q.coords := by
      funext i
      have hi := congrFun ha i
      change a * (Q.coords i : ℚ) = (P.coords i : ℚ) at hi
      rw [hak, hk] at hi
      norm_num at hi
      have hiZ : P.coords i = -Q.coords i := by
        exact_mod_cast hi.symm
      simpa using hiZ
    have hnegNormalized : IsSignNormalized (-Q.coords) := by
      rw [← hcoords]
      exact P.sign_normalized
    exact (not_isSignNormalized_neg Q.coords Q.sign_normalized hnegNormalized).elim

/-- Sign-normalizing a primitive integral vector preserves its rational
projective point. -/
theorem toProjectivePoint_ofPrimitive
    (v : IntegralFour) (hv : v ≠ 0) (hprimitive : content v = 1) :
    (ofPrimitive v hv hprimitive).toProjectivePoint =
      Projectivization.mk ℚ (rationalCoordinatesOf v)
        (rationalCoordinatesOf_ne_zero v hv) := by
  apply (Projectivization.mk_eq_mk_iff' ℚ _ _ _ _).2
  rcases signNormalize_eq_or_eq_neg v with h | h
  · refine ⟨1, ?_⟩
    change (1 : ℚ) • rationalCoordinatesOf v =
      rationalCoordinatesOf (signNormalize v)
    rw [h]
    simp
  · refine ⟨-1, ?_⟩
    change (-1 : ℚ) • rationalCoordinatesOf v =
      rationalCoordinatesOf (signNormalize v)
    rw [h]
    funext i
    simp [rationalCoordinatesOf]

/-! ## Natural height and finite sublevels -/

/-- Maximum absolute value of the four primitive integral coordinates. -/
def height (P : NormalizedPrimitiveFour) : ℕ :=
  max (P.coords 0).natAbs
    (max (P.coords 1).natAbs
      (max (P.coords 2).natAbs (P.coords 3).natAbs))

/-- Every coordinate is bounded by the maximum-coordinate height. -/
theorem coordinate_natAbs_le_height (P : NormalizedPrimitiveFour) (i : Fin 4) :
    (P.coords i).natAbs ≤ P.height := by
  fin_cases i <;> simp [height]

/-- Encode a height-bounded record by four entries in the finite interval
`[-N,N]`. -/
def boundedCoordinates (N : ℕ)
    (P : {P : NormalizedPrimitiveFour // P.height ≤ N}) :
    Fin 4 → Set.Icc (-(N : ℤ)) (N : ℤ) :=
  fun i =>
    ⟨P.1.coords i, by
      have hnat : (P.1.coords i).natAbs ≤ N :=
        (coordinate_natAbs_le_height P.1 i).trans P.2
      have hcast : ((P.1.coords i).natAbs : ℤ) ≤ (N : ℤ) := by
        exact_mod_cast hnat
      rw [Int.natCast_natAbs] at hcast
      exact abs_le.mp hcast⟩

/-- The bounded-coordinate encoding loses no normalized record. -/
theorem boundedCoordinates_injective (N : ℕ) :
    Function.Injective (boundedCoordinates N) := by
  intro P Q h
  apply Subtype.ext
  apply ext
  funext i
  exact congrArg Subtype.val (congrFun h i)

/-- Every maximum-height sublevel of normalized primitive integral
projective four-tuples is finite.  This has exactly the shape required by
`XOneThirteenAbstractHalvingDescent.Certificate.finite_sublevel`. -/
theorem finite_height_sublevel (N : ℕ) :
    Finite {P : NormalizedPrimitiveFour // P.height ≤ N} :=
  Finite.of_injective (boundedCoordinates N) (boundedCoordinates_injective N)

end NormalizedPrimitiveFour

end MazurTorsion.XOneThirteenKummerProjectiveHeight

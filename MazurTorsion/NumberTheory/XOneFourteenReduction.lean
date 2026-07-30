/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import EllipticCurves.ReductionAtPrime
import MazurTorsion.NumberTheory.XOneFourteenDescent

/-!
# Rational points on the chosen `X₁(14)` model

The two-isogeny descent proves that the rational point group of

`V² = U(U² - 11U + 32)`

is finite and exhibits six distinct points.  This file applies good
reduction at three.  The reduced curve has exactly six points, and the
reduction map is injective on the finite rational point group.  Consequently
the six visible points exhaust the rational points, and every finite point
has abscissa `0`, `4`, or `8`.
-/

open WeierstrassCurve

namespace MazurTorsion.XOneFourteen

open WeierstrassCurve.Affine
  IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- The integral model used for reduction at three. -/
def integralCurve : WeierstrassCurve ℤ :=
  ⟨0, -11, 0, 32, 0⟩

lemma map_integralCurve :
    (integralCurve.map (algebraMap ℤ ℚ)).toAffine =
      curve.toAffine := by
  ext <;> simp [integralCurve, curve]

lemma discriminant_integralCurve :
    integralCurve.Δ = -114688 := by
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
    (redCurve (intPrime 3) integralCurve).IsElliptic :=
  isElliptic_redCurve
    (by norm_num [discriminant_integralCurve])

/-- The concrete reduction over `ZMod 3`. -/
def curveModThree : WeierstrassCurve (ZMod 3) :=
  ⟨0, -11, 0, 32, 0⟩

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

/-- The reduction modulo three has exactly six points. -/
theorem card_reducedCurve :
    Nat.card
      (redCurve (intPrime 3) integralCurve).Point = 6 := by
  calc
    Nat.card
        (redCurve (intPrime 3) integralCurve).Point =
        Fintype.card curveModThree.toAffine.Point :=
      (Nat.card_congr reducedPointEquiv.toEquiv).trans
        Nat.card_eq_fintype_card
    _ = 6 := by decide

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

/-- There are at most six rational points on the chosen `X₁(14)` model. -/
theorem point_card_le_six :
    Nat.card curve.toAffine.Point ≤ 6 := by
  letI : Finite curve.toAffine.Point := point_finite
  calc
    Nat.card curve.toAffine.Point ≤
        Nat.card
          (redCurve (intPrime 3) integralCurve).Point :=
      Nat.card_le_card_of_injective
        (redHom (intPrime 3) map_integralCurve)
        reduction_injective
    _ = 6 := card_reducedCurve

/-- The six points constructed by the descent file exhaust the rational
point group. -/
theorem sixVisiblePoints_bijective :
    Function.Bijective sixVisiblePoints := by
  letI : Finite curve.toAffine.Point := point_finite
  exact
    sixVisiblePoints_injective.bijective_of_nat_card_le
      (by simpa using point_card_le_six)

/-- Every affine rational point on the chosen model has abscissa `0`, `4`,
or `8`. -/
theorem point_abscissa_eq_zero_four_or_eight
    {U V : ℚ}
    (hP : curve.toAffine.Nonsingular U V) :
    U = 0 ∨ U = 4 ∨ U = 8 := by
  let P : curve.toAffine.Point := .some U V hP
  obtain ⟨i, hi⟩ :=
    sixVisiblePoints_bijective.2 P
  fin_cases i
  · have hzero : P ≠ 0 :=
      WeierstrassCurve.Affine.Point.some_ne_zero hP
    exact (hzero (by simpa only [sixVisiblePoints] using hi.symm)).elim
  · left
    have hcoords : (0 : ℚ) = U ∧ (0 : ℚ) = V := by
      simpa only [sixVisiblePoints, T, P,
        WeierstrassCurve.Affine.Point.some.injEq] using hi
    exact hcoords.1.symm
  · right; right
    have hcoords : (8 : ℚ) = U ∧ (8 : ℚ) = V := by
      simpa only [sixVisiblePoints, G, P,
        WeierstrassCurve.Affine.Point.some.injEq] using hi
    exact hcoords.1.symm
  · right; right
    have hcoords : (8 : ℚ) = U ∧ (-8 : ℚ) = V := by
      simpa only [sixVisiblePoints, Gneg, P,
        WeierstrassCurve.Affine.Point.some.injEq] using hi
    exact hcoords.1.symm
  · right; left
    have hcoords : (4 : ℚ) = U ∧ (4 : ℚ) = V := by
      simpa only [sixVisiblePoints, H, P,
        WeierstrassCurve.Affine.Point.some.injEq] using hi
    exact hcoords.1.symm
  · right; left
    have hcoords : (4 : ℚ) = U ∧ (-4 : ℚ) = V := by
      simpa only [sixVisiblePoints, Hneg, P,
        WeierstrassCurve.Affine.Point.some.injEq] using hi
    exact hcoords.1.symm

end MazurTorsion.XOneFourteen

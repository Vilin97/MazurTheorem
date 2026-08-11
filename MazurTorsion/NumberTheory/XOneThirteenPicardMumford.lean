/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenPicardClass
import MazurTorsion.NumberTheory.XOneThirteenMumfordComposition

/-!
# Mumford ideals in the affine coordinate ring of `X₁(13)`

This file attaches the two-generator ideal `⟨u(X), Y - v(X)⟩` to the
existing affine Mumford coordinates for the fixed sextic model.  When `u`
and `v` are coprime, the ideal has the displayed conjugate inverse
`⟨u(X), Y + v(X)⟩ / u(X)`.  Thus the polynomial divisibility certificate
already carried by `AffineMumford` gives an actual invertible affine Picard
class.

This is deliberately a curve-specific bridge, not a general Jacobian API.
The first concrete consumer is the degree-two cusp composition from
`XOneThirteenMumfordComposition`.
-/

namespace MazurTorsion.XOneThirteenPicard

open Ideal IsFractionRing Polynomial
open scoped nonZeroDivisors

open XOneThirteenMumford

noncomputable section

namespace CoordinateRing

/-- The image of a support polynomial in the affine coordinate ring. -/
noncomputable def supportClass (u : ℚ[X]) : CoordinateRing :=
  algebraMap ℚ[X] CoordinateRing u

/-- The element `Y - v(X)` in the affine coordinate ring. -/
noncomputable def ordinateClass (v : ℚ[X]) : CoordinateRing :=
  yCoordinate - algebraMap ℚ[X] CoordinateRing v

/-- The affine Mumford ideal `⟨u(X), Y - v(X)⟩`. -/
noncomputable def mumfordIdeal (u v : ℚ[X]) : Ideal CoordinateRing :=
  .span {supportClass u, ordinateClass v}

@[simp]
theorem conjugation_supportClass (u : ℚ[X]) :
    conjugation (supportClass u) = supportClass u := by
  exact conjugation.commutes u

@[simp]
theorem conjugation_ordinateClass (v : ℚ[X]) :
    conjugation (ordinateClass v) = -ordinateClass (-v) := by
  simp only [ordinateClass, map_sub, conjugation_yCoordinate,
    conjugation.commutes, map_neg]
  ring

/-- The two conjugate ordinate generators multiply to `f - v²`. -/
theorem ordinateClass_neg_mul_ordinateClass (v : ℚ[X]) :
    ordinateClass (-v) * ordinateClass v =
      algebraMap ℚ[X] CoordinateRing (sexticPolynomial - v ^ 2) := by
  calc
    ordinateClass (-v) * ordinateClass v =
        yCoordinate ^ 2 -
          (algebraMap ℚ[X] CoordinateRing v) ^ 2 := by
      simp only [ordinateClass, map_neg]
      ring
    _ = algebraMap ℚ[X] CoordinateRing sexticPolynomial -
        algebraMap ℚ[X] CoordinateRing (v ^ 2) := by
      rw [yCoordinate_sq, map_pow]
    _ = algebraMap ℚ[X] CoordinateRing
        (sexticPolynomial - v ^ 2) := by
      rw [map_sub]

/-- Coprime Mumford data give an invertible ideal: the product with the
hyperelliptic conjugate is the principal support ideal.

The `IsCoprime u v` hypothesis excludes a common Weierstrass component.  It
is exactly what is needed in the reverse containment: Bézout combines `u²`
and `uv`, both visible among the four product generators, to recover `u`. -/
theorem mumfordIdeal_neg_mul_mumfordIdeal
    {u v : ℚ[X]} (hequation : u ∣ sexticPolynomial - v ^ 2)
    (hcoprime : IsCoprime u v) :
    mumfordIdeal u (-v) * mumfordIdeal u v =
      Ideal.span {supportClass u} := by
  obtain ⟨q, hq⟩ := hequation
  rw [mumfordIdeal, mumfordIdeal, Ideal.span_pair_mul_span_pair]
  apply le_antisymm
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact (Ideal.span {supportClass u}).mul_mem_left (supportClass u)
        (Ideal.mem_span_singleton_self (supportClass u))
    · exact (Ideal.span {supportClass u}).mul_mem_right (ordinateClass v)
        (Ideal.mem_span_singleton_self (supportClass u))
    · exact (Ideal.span {supportClass u}).mul_mem_left (ordinateClass (-v))
        (Ideal.mem_span_singleton_self (supportClass u))
    · rw [ordinateClass_neg_mul_ordinateClass, hq, map_mul]
      exact (Ideal.span {supportClass u}).mul_mem_right
        (algebraMap ℚ[X] CoordinateRing q)
        (Ideal.mem_span_singleton_self (supportClass u))
  · rw [Ideal.span_singleton_le_iff_mem]
    let J : Ideal CoordinateRing :=
      .span {supportClass u * supportClass u,
        supportClass u * ordinateClass v,
        ordinateClass (-v) * supportClass u,
        ordinateClass (-v) * ordinateClass v}
    change supportClass u ∈ J
    have huu : supportClass u * supportClass u ∈ J := by
      exact Ideal.subset_span (by simp)
    have hminus : supportClass u * ordinateClass v ∈ J := by
      exact Ideal.subset_span (by simp)
    have hplus : ordinateClass (-v) * supportClass u ∈ J := by
      exact Ideal.subset_span (by simp)
    have htwouv :
        (2 : CoordinateRing) * supportClass u *
            algebraMap ℚ[X] CoordinateRing v ∈ J := by
      convert J.sub_mem hplus hminus using 1
      simp only [ordinateClass, map_neg]
      ring
    have hhalf :
        algebraMap ℚ[X] CoordinateRing (C (1 / 2 : ℚ)) * 2 = 1 := by
      rw [show (2 : CoordinateRing) =
          algebraMap ℚ[X] CoordinateRing (C 2) by
        rw [C_ofNat, map_ofNat]]
      rw [← map_mul, ← C_mul]
      norm_num
    have huv : supportClass u *
        algebraMap ℚ[X] CoordinateRing v ∈ J := by
      have hscaled := J.mul_mem_left
        (algebraMap ℚ[X] CoordinateRing (C (1 / 2 : ℚ))) htwouv
      have hscaleeq :
        algebraMap ℚ[X] CoordinateRing (C (1 / 2 : ℚ)) *
            (2 * supportClass u * algebraMap ℚ[X] CoordinateRing v) =
          supportClass u * algebraMap ℚ[X] CoordinateRing v := by
        calc
          algebraMap ℚ[X] CoordinateRing (C (1 / 2 : ℚ)) *
              (2 * supportClass u * algebraMap ℚ[X] CoordinateRing v) =
            (algebraMap ℚ[X] CoordinateRing (C (1 / 2 : ℚ)) * 2) *
              (supportClass u * algebraMap ℚ[X] CoordinateRing v) := by
            ring
          _ = supportClass u * algebraMap ℚ[X] CoordinateRing v := by
            rw [hhalf, one_mul]
      rw [← hscaleeq]
      exact hscaled
    obtain ⟨a, b, hab⟩ := hcoprime
    have hcomb := J.add_mem
      (J.mul_mem_left (algebraMap ℚ[X] CoordinateRing a) huu)
      (J.mul_mem_left (algebraMap ℚ[X] CoordinateRing b) huv)
    convert hcomb using 1
    rw [supportClass]
    have hmapped := congrArg (algebraMap ℚ[X] CoordinateRing) hab
    simp only [map_add, map_mul, map_one] at hmapped
    calc
      algebraMap ℚ[X] CoordinateRing u =
          1 * algebraMap ℚ[X] CoordinateRing u := by ring
      _ = (algebraMap ℚ[X] CoordinateRing a *
            algebraMap ℚ[X] CoordinateRing u +
          algebraMap ℚ[X] CoordinateRing b *
            algebraMap ℚ[X] CoordinateRing v) *
            algebraMap ℚ[X] CoordinateRing u := by rw [hmapped]
      _ = algebraMap ℚ[X] CoordinateRing a *
            (algebraMap ℚ[X] CoordinateRing u *
              algebraMap ℚ[X] CoordinateRing u) +
          algebraMap ℚ[X] CoordinateRing b *
            (algebraMap ℚ[X] CoordinateRing u *
              algebraMap ℚ[X] CoordinateRing v) := by ring

/-! ## Coprime-support composition at the ideal level -/

/-- Polynomial interpolation over coprime supports agrees with multiplication
of the corresponding two-generator ideals.

This is the affine ideal-class form of the coprime-support composition lemma
already proved for `AffineMumford`.  It supplies the group-law bridge without
introducing a general Jacobian implementation. -/
theorem mumfordIdeal_mul_of_coprime_support
    {u₁ v₁ u₂ v₂ w : ℚ[X]}
    (hcoprime : IsCoprime u₁ u₂)
    (h₁ : u₁ ∣ w - v₁) (h₂ : u₂ ∣ w - v₂) :
    mumfordIdeal u₁ v₁ * mumfordIdeal u₂ v₂ =
      mumfordIdeal (u₁ * u₂) w := by
  obtain ⟨q₁, hq₁⟩ := h₁
  obtain ⟨q₂, hq₂⟩ := h₂
  have hv₁ : ordinateClass v₁ =
      ordinateClass w + supportClass u₁ *
        algebraMap ℚ[X] CoordinateRing q₁ := by
    calc
      ordinateClass v₁ = ordinateClass w +
          algebraMap ℚ[X] CoordinateRing (w - v₁) := by
        simp only [ordinateClass, map_sub]
        ring
      _ = ordinateClass w + supportClass u₁ *
          algebraMap ℚ[X] CoordinateRing q₁ := by
        rw [hq₁, map_mul]
        rfl
  have hv₂ : ordinateClass v₂ =
      ordinateClass w + supportClass u₂ *
        algebraMap ℚ[X] CoordinateRing q₂ := by
    calc
      ordinateClass v₂ = ordinateClass w +
          algebraMap ℚ[X] CoordinateRing (w - v₂) := by
        simp only [ordinateClass, map_sub]
        ring
      _ = ordinateClass w + supportClass u₂ *
          algebraMap ℚ[X] CoordinateRing q₂ := by
        rw [hq₂, map_mul]
        rfl
  rw [mumfordIdeal, mumfordIdeal, mumfordIdeal,
    Ideal.span_pair_mul_span_pair]
  let I : Ideal CoordinateRing :=
    .span {supportClass u₁ * supportClass u₂,
      supportClass u₁ * ordinateClass v₂,
      ordinateClass v₁ * supportClass u₂,
      ordinateClass v₁ * ordinateClass v₂}
  let M : Ideal CoordinateRing :=
    .span {supportClass (u₁ * u₂), ordinateClass w}
  change I = M
  have hsM : supportClass u₁ * supportClass u₂ ∈ M := by
    have hgen : supportClass (u₁ * u₂) ∈ M := by
      exact Ideal.subset_span (by simp)
    simpa only [supportClass, map_mul] using hgen
  have hwM : ordinateClass w ∈ M := by
    exact Ideal.subset_span (by simp)
  apply le_antisymm
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact hsM
    · rw [hv₂, mul_add]
      apply M.add_mem
      · exact M.mul_mem_left (supportClass u₁) hwM
      · convert M.mul_mem_right (algebraMap ℚ[X] CoordinateRing q₂) hsM using 1
        ring
    · rw [hv₁, add_mul]
      apply M.add_mem
      · exact M.mul_mem_right (supportClass u₂) hwM
      · convert M.mul_mem_right (algebraMap ℚ[X] CoordinateRing q₁) hsM using 1
        ring
    · rw [hv₂, mul_add]
      apply M.add_mem
      · exact M.mul_mem_left (ordinateClass v₁) hwM
      · rw [hv₁, add_mul]
        apply M.add_mem
        · exact M.mul_mem_right
            (supportClass u₂ * algebraMap ℚ[X] CoordinateRing q₂) hwM
        · convert M.mul_mem_right
            (algebraMap ℚ[X] CoordinateRing q₁ *
              algebraMap ℚ[X] CoordinateRing q₂) hsM using 1
          ring
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    have hsI : supportClass u₁ * supportClass u₂ ∈ I := by
      exact Ideal.subset_span (by simp)
    rcases hz with rfl | rfl
    · change supportClass (u₁ * u₂) ∈ I
      simpa only [supportClass, map_mul] using hsI
    · have hleftGen : supportClass u₁ * ordinateClass v₂ ∈ I := by
        exact Ideal.subset_span (by simp)
      have hrightGen : ordinateClass v₁ * supportClass u₂ ∈ I := by
        exact Ideal.subset_span (by simp)
      have hleft : supportClass u₁ * ordinateClass w ∈ I := by
        rw [hv₂, mul_add] at hleftGen
        have hmultiple := I.mul_mem_right
          (algebraMap ℚ[X] CoordinateRing q₂) hsI
        convert I.sub_mem hleftGen hmultiple using 1
        ring
      have hright : supportClass u₂ * ordinateClass w ∈ I := by
        rw [hv₁, add_mul] at hrightGen
        have hmultiple := I.mul_mem_right
          (algebraMap ℚ[X] CoordinateRing q₁) hsI
        convert I.sub_mem hrightGen hmultiple using 1
        ring
      obtain ⟨a, b, hab⟩ := hcoprime
      have hcomb := I.add_mem
        (I.mul_mem_left (algebraMap ℚ[X] CoordinateRing a) hleft)
        (I.mul_mem_left (algebraMap ℚ[X] CoordinateRing b) hright)
      have hmapped := congrArg (algebraMap ℚ[X] CoordinateRing) hab
      simp only [map_add, map_mul, map_one] at hmapped
      have heq : ordinateClass w =
          algebraMap ℚ[X] CoordinateRing a *
              (supportClass u₁ * ordinateClass w) +
            algebraMap ℚ[X] CoordinateRing b *
              (supportClass u₂ * ordinateClass w) := by
        calc
          ordinateClass w = 1 * ordinateClass w := by ring
          _ = (algebraMap ℚ[X] CoordinateRing a *
              algebraMap ℚ[X] CoordinateRing u₁ +
            algebraMap ℚ[X] CoordinateRing b *
              algebraMap ℚ[X] CoordinateRing u₂) *
              ordinateClass w := by rw [hmapped]
          _ = algebraMap ℚ[X] CoordinateRing a *
              (supportClass u₁ * ordinateClass w) +
            algebraMap ℚ[X] CoordinateRing b *
              (supportClass u₂ * ordinateClass w) := by
            simp only [supportClass]
            ring
      rw [heq]
      exact hcomb

/-! ## Invertible Mumford ideals and their affine Picard classes -/

private theorem algebraMap_polynomial_injective :
    Function.Injective (algebraMap ℚ[X] CoordinateRing) := by
  exact AdjoinRoot.of.injective_of_degree_ne_zero (by
    rw [degree_eq_natDegree relationPolynomial_monic.ne_zero,
      relationPolynomial_natDegree]
    norm_num)

theorem supportClass_ne_zero {u : ℚ[X]} (hu : u ≠ 0) :
    supportClass u ≠ 0 := by
  simpa only [supportClass, map_zero] using
    algebraMap_polynomial_injective.ne hu

theorem supportClass_fraction_ne_zero
    (D : XOneThirteenMumford.AffineMumford) :
    algebraMap CoordinateRing FractionField (supportClass D.u) ≠ 0 := by
  simpa only [map_zero] using
    (IsFractionRing.injective CoordinateRing FractionField).ne
      (supportClass_ne_zero D.u_monic.ne_zero)

/-- The integral Mumford ideal embedded in the fractional-ideal monoid. -/
noncomputable def mumfordFractionalIdeal
    (D : XOneThirteenMumford.AffineMumford) :
    FractionalIdeal CoordinateRing⁰ FractionField :=
  (mumfordIdeal D.u D.v : Ideal CoordinateRing)

/-- The conjugate-product certificate for an affine Mumford record. -/
theorem mumfordFractionalIdeal_neg_mul_mumfordFractionalIdeal
    (D : XOneThirteenMumford.AffineMumford)
    (hcoprime : IsCoprime D.u D.v) :
    mumfordFractionalIdeal (XOneThirteenMumford.AffineMumford.neg D) *
        mumfordFractionalIdeal D =
      FractionalIdeal.spanSingleton CoordinateRing⁰
        (algebraMap CoordinateRing FractionField (supportClass D.u)) := by
  simp only [mumfordFractionalIdeal,
    XOneThirteenMumford.AffineMumford.neg_u,
    XOneThirteenMumford.AffineMumford.neg_v]
  rw [← FractionalIdeal.coeIdeal_mul,
    mumfordIdeal_neg_mul_mumfordIdeal D.equation_mod_u hcoprime,
    FractionalIdeal.coeIdeal_span_singleton]

/-- A displayed inverse for a coprime affine Mumford ideal. -/
noncomputable def mumfordFractionalIdealInverse
    (D : XOneThirteenMumford.AffineMumford) :
    FractionalIdeal CoordinateRing⁰ FractionField :=
  FractionalIdeal.spanSingleton CoordinateRing⁰
      (algebraMap CoordinateRing FractionField (supportClass D.u))⁻¹ *
    mumfordFractionalIdeal (XOneThirteenMumford.AffineMumford.neg D)

private theorem mumfordFractionalIdeal_mul_inverse
    (D : XOneThirteenMumford.AffineMumford)
    (hcoprime : IsCoprime D.u D.v) :
    mumfordFractionalIdeal D * mumfordFractionalIdealInverse D = 1 := by
  rw [mumfordFractionalIdealInverse]
  calc
    mumfordFractionalIdeal D *
        (FractionalIdeal.spanSingleton CoordinateRing⁰
            (algebraMap CoordinateRing FractionField (supportClass D.u))⁻¹ *
          mumfordFractionalIdeal
            (XOneThirteenMumford.AffineMumford.neg D)) =
      FractionalIdeal.spanSingleton CoordinateRing⁰
          (algebraMap CoordinateRing FractionField (supportClass D.u))⁻¹ *
        (mumfordFractionalIdeal
            (XOneThirteenMumford.AffineMumford.neg D) *
          mumfordFractionalIdeal D) := by
      ac_rfl
    _ = FractionalIdeal.spanSingleton CoordinateRing⁰
          (algebraMap CoordinateRing FractionField (supportClass D.u))⁻¹ *
        FractionalIdeal.spanSingleton CoordinateRing⁰
          (algebraMap CoordinateRing FractionField (supportClass D.u)) := by
      rw [mumfordFractionalIdeal_neg_mul_mumfordFractionalIdeal D hcoprime]
    _ = 1 := by
      rw [FractionalIdeal.spanSingleton_mul_spanSingleton,
        inv_mul_cancel₀ (supportClass_fraction_ne_zero D),
        FractionalIdeal.spanSingleton_one]

/-- The invertible fractional ideal represented by coprime affine Mumford
coordinates. -/
noncomputable def mumfordFractionalIdealUnit
    (D : XOneThirteenMumford.AffineMumford)
    (hcoprime : IsCoprime D.u D.v) :
    (FractionalIdeal CoordinateRing⁰ FractionField)ˣ :=
  Units.mkOfMulEqOne (mumfordFractionalIdeal D)
    (mumfordFractionalIdealInverse D)
    (mumfordFractionalIdeal_mul_inverse D hcoprime)

/-- The affine Picard class represented by coprime affine Mumford
coordinates. -/
noncomputable def mumfordClass
    (D : XOneThirteenMumford.AffineMumford)
    (hcoprime : IsCoprime D.u D.v) : ClassGroup CoordinateRing :=
  ClassGroup.mk FractionField (mumfordFractionalIdealUnit D hcoprime)

private theorem mumfordFractionalIdealUnit_neg_mul
    (D : XOneThirteenMumford.AffineMumford)
    (hcoprime : IsCoprime D.u D.v) :
    mumfordFractionalIdealUnit
        (XOneThirteenMumford.AffineMumford.neg D) hcoprime.neg_right *
      mumfordFractionalIdealUnit D hcoprime =
        toPrincipalIdeal CoordinateRing FractionField
          (Units.mk0
            (algebraMap CoordinateRing FractionField (supportClass D.u))
            (supportClass_fraction_ne_zero D)) := by
  apply Units.ext
  rw [Units.val_mul, coe_toPrincipalIdeal, Units.val_mk0]
  exact mumfordFractionalIdeal_neg_mul_mumfordFractionalIdeal D hcoprime

/-- Hyperelliptic conjugation gives inverse affine Picard classes for every
coprime affine Mumford record. -/
theorem mumfordClass_neg_mul
    (D : XOneThirteenMumford.AffineMumford)
    (hcoprime : IsCoprime D.u D.v) :
    mumfordClass (XOneThirteenMumford.AffineMumford.neg D)
        hcoprime.neg_right *
      mumfordClass D hcoprime = 1 := by
  simp only [mumfordClass]
  rw [← map_mul,
    mumfordFractionalIdealUnit_neg_mul D hcoprime]
  apply (ClassGroup.mk_eq_one_iff).2
  rw [coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton]
  exact ⟨⟨_, rfl⟩⟩

/-! ## Compatibility with the existing affine point classes -/

/-- The Mumford record obtained from an affine point stated in the coordinate
ring convention used by `pointClass`. -/
def mumfordOfAffinePoint (x y : ℚ) (hcurve : IsAffinePoint x y) :
    XOneThirteenMumford.AffineMumford :=
  XOneThirteenMumford.AffineMumford.ofPoint x y (by
    rw [← XOneThirteenMumford.eval_sexticPolynomial]
    exact hcurve)

@[simp]
theorem mumfordOfAffinePoint_u (x y : ℚ) (hcurve : IsAffinePoint x y) :
    (mumfordOfAffinePoint x y hcurve).u = X - C x := rfl

@[simp]
theorem mumfordOfAffinePoint_v (x y : ℚ) (hcurve : IsAffinePoint x y) :
    (mumfordOfAffinePoint x y hcurve).v = C y := rfl

/-- A non-Weierstrass affine point has coprime degree-one Mumford
coordinates. -/
theorem mumfordOfAffinePoint_isCoprime
    (x y : ℚ) (hcurve : IsAffinePoint x y) (hy : y ≠ 0) :
    IsCoprime (mumfordOfAffinePoint x y hcurve).u
      (mumfordOfAffinePoint x y hcurve).v := by
  simp only [mumfordOfAffinePoint_u, mumfordOfAffinePoint_v]
  refine ⟨0, C y⁻¹, ?_⟩
  simp only [zero_mul, zero_add]
  rw [← C_mul, inv_mul_cancel₀ hy, C_1]

/-- The degree-one Mumford ideal is definitionally the previously constructed
point ideal. -/
theorem mumfordIdeal_mumfordOfAffinePoint
    (x y : ℚ) (hcurve : IsAffinePoint x y) :
    mumfordIdeal (mumfordOfAffinePoint x y hcurve).u
        (mumfordOfAffinePoint x y hcurve).v =
      pointIdeal x y := by
  simp only [mumfordOfAffinePoint_u, mumfordOfAffinePoint_v,
    mumfordIdeal, pointIdeal, supportClass, ordinateClass, xClass, yClass]

/-- Compatibility consumer: passing a non-Weierstrass point through degree-one
Mumford coordinates recovers its existing affine Picard class. -/
theorem mumfordClass_mumfordOfAffinePoint
    (x y : ℚ) (hcurve : IsAffinePoint x y) (hy : y ≠ 0) :
    mumfordClass (mumfordOfAffinePoint x y hcurve)
        (mumfordOfAffinePoint_isCoprime x y hcurve hy) =
      pointClass x y hcurve hy := by
  apply congrArg (ClassGroup.mk FractionField)
  apply Units.ext
  change mumfordFractionalIdeal (mumfordOfAffinePoint x y hcurve) =
    pointFractionalIdeal x y
  simp only [mumfordFractionalIdeal, pointFractionalIdeal,
    mumfordIdeal_mumfordOfAffinePoint]

/-! ## Concrete degree-two cusp consumer -/

theorem cuspComposition_isCoprime :
    IsCoprime XOneThirteenMumford.AffineMumford.cuspComposition.u
      XOneThirteenMumford.AffineMumford.cuspComposition.v := by
  rw [XOneThirteenMumford.AffineMumford.cuspComposition_u,
    XOneThirteenMumford.AffineMumford.cuspComposition_v]
  simpa [linearPolynomial] using
    (isCoprime_one_right :
      IsCoprime (monicQuadratic 0 1) (1 : ℚ[X]))

/-- The affine Picard class of the degree-two cusp Mumford record. -/
noncomputable def cuspCompositionClass : ClassGroup CoordinateRing :=
  mumfordClass XOneThirteenMumford.AffineMumford.cuspComposition
    cuspComposition_isCoprime

/-- Concrete consumer: the conjugate degree-two cusp class is the inverse of
the degree-two cusp class. -/
theorem cuspCompositionClass_neg_mul :
    mumfordClass
        (XOneThirteenMumford.AffineMumford.neg
          XOneThirteenMumford.AffineMumford.cuspComposition)
        cuspComposition_isCoprime.neg_right *
      cuspCompositionClass = 1 := by
  exact mumfordClass_neg_mul
    XOneThirteenMumford.AffineMumford.cuspComposition
    cuspComposition_isCoprime

private theorem cuspNegOne_isAffinePoint : IsAffinePoint (-1) 1 := by
  norm_num [IsAffinePoint, sexticPolynomial]

/-- The affine Picard class of the second affine cusp `(-1,1)`. -/
noncomputable def cuspNegOneClass : ClassGroup CoordinateRing :=
  pointClass (-1) 1 cuspNegOne_isAffinePoint one_ne_zero

/-- The polynomial interpolation construction of `cuspComposition` agrees
with multiplication of the two affine cusp ideals. -/
theorem cuspZeroIdeal_mul_cuspNegOneIdeal :
    pointIdeal 0 1 * pointIdeal (-1) 1 =
      mumfordIdeal
        XOneThirteenMumford.AffineMumford.cuspComposition.u
        XOneThirteenMumford.AffineMumford.cuspComposition.v := by
  have hcoprime :
      IsCoprime (X - C (0 : ℚ)) (X - C (-1 : ℚ)) := by
    apply isCoprime_X_sub_C_of_isUnit_sub
    norm_num
  have hleft : X - C (0 : ℚ) ∣
      linearPolynomial 1 0 - C 1 := by
    simp [linearPolynomial]
  have hright : X - C (-1 : ℚ) ∣
      linearPolynomial 1 0 - C 1 := by
    simp [linearPolynomial]
  have hmul := mumfordIdeal_mul_of_coprime_support hcoprime hleft hright
  calc
    pointIdeal 0 1 * pointIdeal (-1) 1 =
        mumfordIdeal (X - C (0 : ℚ)) (C 1) *
          mumfordIdeal (X - C (-1 : ℚ)) (C 1) := by
      rfl
    _ = mumfordIdeal
        ((X - C (0 : ℚ)) * (X - C (-1 : ℚ)))
          (linearPolynomial 1 0) := hmul
    _ = mumfordIdeal
        XOneThirteenMumford.AffineMumford.cuspComposition.u
        XOneThirteenMumford.AffineMumford.cuspComposition.v := by
      rw [XOneThirteenMumford.AffineMumford.two_point_support_coefficients,
        XOneThirteenMumford.AffineMumford.cuspComposition_u,
        XOneThirteenMumford.AffineMumford.cuspComposition_v]
      norm_num

/-- Concrete group-law consumer: the degree-two cusp composition class is
the product of the two degree-one cusp classes. -/
theorem cuspZeroClass_mul_cuspNegOneClass :
    cuspZeroClass * cuspNegOneClass = cuspCompositionClass := by
  simp only [cuspZeroClass, cuspNegOneClass, cuspCompositionClass,
    pointClass, mumfordClass]
  rw [← map_mul]
  apply congrArg (ClassGroup.mk FractionField)
  apply Units.ext
  rw [Units.val_mul]
  change pointFractionalIdeal 0 1 * pointFractionalIdeal (-1) 1 =
    mumfordFractionalIdeal
      XOneThirteenMumford.AffineMumford.cuspComposition
  simp only [pointFractionalIdeal, mumfordFractionalIdeal]
  rw [← FractionalIdeal.coeIdeal_mul,
    cuspZeroIdeal_mul_cuspNegOneIdeal]

end CoordinateRing

end

end MazurTorsion.XOneThirteenPicard

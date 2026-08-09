/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Chris Birkbeck, Kenny Lau, Claude Fable 5,
  Claude Opus 4.8, OpenAI Codex
-/

import MazurTorsion.Upstream.AINTLIB.ForMathlib.TateNormalForm
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.NumberTheory.Divisors
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The affine Tate base for the split Gamma-one route

This file isolates the ring-level Tate-normal-form base needed to construct
the fine `Y₁(N)` scheme.  It contains no moduli representability assertion.
The formulas and proofs are adapted from AINTLIB's
`Moduli/Representability.lean` and `ModularCurve/YOneAssembly.lean`; their
licensed-default exact blobs are
`efd838f8a7702725bcbe974b9e7141e683eee644` and
`7732e39a206a348ca7c6d59ecdb9b8359abccc33`, respectively, at commit
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`. Full provenance and license
evidence are recorded in `PORTING.md`.

The first part proves the canonical ring-level Tate normalization.  The
second constructs

`Spec R[A, B][Delta(A, B)⁻¹]`

and its universal Tate-normal Weierstrass equation over an arbitrary affine
base ring `R`.  The missing next layer is the projective elliptic family with
its marked section and its fine-moduli universal property.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial

namespace MazurTorsion.ModularCurve.XZeroModuli.GammaOneTate

universe u

section TateNormalForm

variable {R : Type u} [CommRing R]

/-- Tate normal form is the equation
`Y² + AXY + BY = X³ + BX²`. -/
def _root_.WeierstrassCurve.IsTateNormal (W : WeierstrassCurve R) : Prop :=
  W.a₂ = W.a₃ ∧ W.a₄ = 0 ∧ W.a₆ = 0

/-- The division-polynomial unit condition. When `W` is elliptic and `(x, y)`
is an on-curve nonsingular point, this says fibrewise that the point is nowhere
of order one, two, or three. -/
def NowhereOrderLEThree (W : WeierstrassCurve R) (x y : R) : Prop :=
  IsUnit ((W.Ψ 2).evalEval x y * (W.Ψ 3).evalEval x y)

open WeierstrassCurve.Affine in
/-- A point satisfying the division-polynomial unit condition has a unique
Tate-normalizing change of variables carrying it to `(0, 0)`. -/
theorem exists_unique_variableChange_isTateNormal
    (W : WeierstrassCurve R) [W.IsElliptic]
    (x y : R) (h : W.toAffine.Equation x y)
    (hord : NowhereOrderLEThree W x y) :
    ∃! C : WeierstrassCurve.VariableChange R,
      (C • W).IsTateNormal ∧ C.r = x ∧ C.t = y := by
  obtain hR | hR := subsingleton_or_nontrivial R
  · exact
      ⟨⟨1, x, 0, y⟩,
        ⟨⟨Subsingleton.elim _ _, Subsingleton.elim _ _,
            Subsingleton.elim _ _⟩, rfl, rfl⟩,
        fun C _ ↦ by ext <;> subsingleton⟩
  · obtain ⟨h2, h3⟩ := IsUnit.mul_iff.mp hord
    simp only [W.Ψ_two, W.Ψ_three, evalEval_C] at h2 h3
    have hns : W.toAffine.Nonsingular x y := ⟨h, Or.inr h2.ne_zero⟩
    let P : W.toAffine.Point := Point.some x y hns
    letI : P.NeZero := ⟨Point.some_ne_zero hns⟩
    letI : P.TwiceNeZero := Point.twiceNeZero_of_isUnit P h2
    letI : P.ThriceNeZero := Point.thriceNeZero_of_isUnit P h3
    exact
      ⟨W.toAffine.toTateNF P,
        ⟨⟨toTateNF_a₂₃ W P, toTateNF_a₄ W P,
            toTateNF_a₆ W P⟩, rfl, rfl⟩,
        fun C hC ↦
          toTateNF_unique W P C hC.2.1 hC.2.2 hC.1.2.1 hC.1.1⟩

/-- The universal Tate-normal Weierstrass curve over `ℤ[A, B]`. -/
noncomputable def tateCurve : WeierstrassCurve (MvPolynomial (Fin 2) ℤ) :=
  { a₁ := MvPolynomial.X 0
    a₂ := MvPolynomial.X 1
    a₃ := MvPolynomial.X 1
    a₄ := 0
    a₆ := 0 }

theorem tateCurve_isTateNormal : tateCurve.IsTateNormal :=
  ⟨rfl, rfl, rfl⟩

/-- The coordinate ring `ℤ[A, B][Delta(A,B)⁻¹]`. -/
noncomputable abbrev tateRing : Type :=
  Localization.Away tateCurve.Δ

private theorem tateRing_eval₂Hom_comp
    (A : Type u) [CommRing A] (φ : tateRing →+* A) :
    MvPolynomial.eval₂Hom (Int.castRingHom A)
        (fun i : Fin 2 ↦ if i = 0 then
          φ (algebraMap (MvPolynomial (Fin 2) ℤ) tateRing
            (MvPolynomial.X 0))
        else
          φ (algebraMap (MvPolynomial (Fin 2) ℤ) tateRing
            (MvPolynomial.X 1))) =
      φ.comp (algebraMap (MvPolynomial (Fin 2) ℤ) tateRing) :=
  MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun i ↦ by
    fin_cases i <;> simp

/-- Ring maps from the universal Tate ring are canonically equivalent to
Tate parameters with invertible discriminant. -/
theorem tateRing_homEquiv (A : Type u) [CommRing A] :
    ∃ e : (tateRing →+* A) ≃
        { c : A × A //
          IsUnit ((tateCurve.map
            (MvPolynomial.eval₂Hom (Int.castRingHom A)
              (fun i ↦ if i = 0 then c.1 else c.2))).Δ) },
      ∀ φ : tateRing →+* A,
        ((e φ).1 : A × A) =
          (φ (algebraMap (MvPolynomial (Fin 2) ℤ) tateRing
            (MvPolynomial.X 0)),
           φ (algebraMap (MvPolynomial (Fin 2) ℤ) tateRing
            (MvPolynomial.X 1))) := by
  refine
    ⟨⟨fun φ ↦
        ⟨(φ (algebraMap (MvPolynomial (Fin 2) ℤ) tateRing
              (MvPolynomial.X 0)),
            φ (algebraMap (MvPolynomial (Fin 2) ℤ) tateRing
              (MvPolynomial.X 1))), ?_⟩,
      fun c ↦ IsLocalization.Away.lift tateCurve.Δ
        (WeierstrassCurve.map_Δ (A := A) tateCurve _ ▸ c.2),
      fun φ ↦ ?_, fun c ↦ ?_⟩,
      fun φ ↦ rfl⟩
  · rw [WeierstrassCurve.map_Δ, tateRing_eval₂Hom_comp A φ]
    exact (IsLocalization.Away.algebraMap_isUnit tateCurve.Δ).map φ
  · exact IsLocalization.ringHom_ext (Submonoid.powers tateCurve.Δ)
      ((IsLocalization.Away.lift_comp _ _).trans
        (tateRing_eval₂Hom_comp A φ))
  · simp

end TateNormalForm

section RelativeTateBase

variable (R : CommRingCat.{u})

/-- The universal Tate-normal equation over `R[A, B]`. -/
noncomputable def tateCurveOver : WeierstrassCurve (MvPolynomial (Fin 2) R) :=
  tateCurve.map (MvPolynomial.map (Int.castRingHom R))

/-- The relative marked-Tate atlas ring `R[A, B][Delta⁻¹]`. -/
noncomputable abbrev tateRingOver : Type u :=
  Localization.Away (tateCurveOver R).Δ

/-- The universal Tate equation over its discriminant localization. -/
noncomputable def tateCurveLocOver : WeierstrassCurve (tateRingOver R) :=
  (tateCurveOver R).map (algebraMap _ _)

noncomputable instance tateCurveLocOver_isElliptic :
    (tateCurveLocOver R).IsElliptic :=
  WeierstrassCurve.IsElliptic.mk <| by
    rw [tateCurveLocOver, WeierstrassCurve.map_Δ]
    exact IsLocalization.map_units (Localization.Away (tateCurveOver R).Δ)
      ⟨(tateCurveOver R).Δ, Submonoid.mem_powers _⟩

/-- The Tate discriminant is divisible by the cube of the marked parameter
`B`. -/
theorem tateB_cube_dvd_Δ :
    (MvPolynomial.X 1 : MvPolynomial (Fin 2) R) ^ 3 ∣
      (tateCurveOver R).Δ := by
  refine
    ⟨-(MvPolynomial.X 0 ^ 2 + 4 * MvPolynomial.X 1) ^ 2 -
        8 * MvPolynomial.X 0 ^ 3 +
        9 * MvPolynomial.X 0 *
          (MvPolynomial.X 0 ^ 2 + 4 * MvPolynomial.X 1) -
        27 * MvPolynomial.X 1, ?_⟩
  simp only [tateCurveOver, tateCurve, WeierstrassCurve.map,
    WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, MvPolynomial.map_X,
    map_zero]
  ring

/-- The parameter `B` becomes a unit after inverting the Tate
discriminant. -/
theorem isUnit_algebraMap_tateB :
    IsUnit (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R)
      (MvPolynomial.X 1)) := by
  have hΔ : IsUnit
      (algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R)
        (tateCurveOver R).Δ) :=
    IsLocalization.Away.algebraMap_isUnit (tateCurveOver R).Δ
  have h3 : IsUnit
      ((algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R)
        (MvPolynomial.X 1)) ^ 3) := by
    rw [← map_pow]
    exact isUnit_of_dvd_unit
      ((algebraMap _ (tateRingOver R)).map_dvd (tateB_cube_dvd_Δ R)) hΔ
  exact (isUnit_pow_iff (by norm_num)).mp h3

theorem isUnit_tateA₃ : IsUnit (tateCurveLocOver R).a₃ := by
  have h : (tateCurveLocOver R).a₃ =
      algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R)
        (MvPolynomial.X 1) := by
    simp [tateCurveLocOver, tateCurveOver, WeierstrassCurve.map,
      tateCurve]
  rw [h]
  exact isUnit_algebraMap_tateB R

theorem isUnit_tateA₂ : IsUnit (tateCurveLocOver R).a₂ := by
  have h : (tateCurveLocOver R).a₂ =
      algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R)
        (MvPolynomial.X 1) := by
    simp [tateCurveLocOver, tateCurveOver, WeierstrassCurve.map,
      tateCurve]
  rw [h]
  exact isUnit_algebraMap_tateB R

theorem tateA₄_eq_zero : (tateCurveLocOver R).a₄ = 0 := by
  simp [tateCurveLocOver, tateCurveOver, WeierstrassCurve.map,
    tateCurve]

theorem tateA₆_eq_zero : (tateCurveLocOver R).a₆ = 0 := by
  simp [tateCurveLocOver, tateCurveOver, WeierstrassCurve.map,
    tateCurve]

/-- The affine Tate-parameter base. The marked section is constructed in the
next projective-family layer, not in this ring-level leaf. -/
@[reducible]
noncomputable def tateBase : Scheme.{u} :=
  Spec (CommRingCat.of (tateRingOver R))

/-- The marked-Tate base structure morphism to `Spec R`. -/
noncomputable def tateStructMap : tateBase R ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom
    ((algebraMap (MvPolynomial (Fin 2) R) (tateRingOver R)).comp
      MvPolynomial.C))

end RelativeTateBase

/-- If both `N` and a proper positive multiple `a` kill an element, a
proper divisor of `N` already kills it. -/
theorem exists_properDivisor_smul_eq_zero
    {G : Type u} [AddCommGroup G] {x : G} {N a : ℕ}
    (hNx : (N : ℤ) • x = 0) (ha0 : 0 < a) (haN : a < N)
    (hax : (a : ℤ) • x = 0) :
    ∃ d ∈ N.properDivisors, 0 < d ∧ (d : ℤ) • x = 0 := by
  refine ⟨Nat.gcd a N, ?_, Nat.gcd_pos_iff.mpr (Or.inl ha0), ?_⟩
  · exact Nat.mem_properDivisors.mpr
      ⟨Nat.gcd_dvd_right a N,
        lt_of_le_of_lt (Nat.gcd_le_left N ha0) haN⟩
  · have hax' : a • x = 0 := by exact_mod_cast hax
    have hNx' : N • x = 0 := by exact_mod_cast hNx
    have hg : Nat.gcd a N • x = 0 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mp
        (Nat.dvd_gcd
          (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hax')
          (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hNx'))
    exact_mod_cast hg

end MazurTorsion.ModularCurve.XZeroModuli.GammaOneTate

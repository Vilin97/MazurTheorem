/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Chris Birkbeck, AINTLIB ModularCurves contributors,
  OpenAI Codex
-/

import MazurTorsion.ModularCurve.XZeroGammaOneTateProjectiveFamily
import MazurTorsion.Upstream.AINTLIB.ForMathlib.ProjectiveSpaceChart
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Ideal.Maximal

/-!
# Jacobian comaximality for projective Weierstrass charts

For an elliptic Weierstrass curve over an arbitrary commutative ring, this file proves
that the dehomogenized cubic and its two partial derivatives generate the unit ideal on
each of the three standard projective charts.  The proof passes a hypothetical maximal
ideal containing the Jacobian ideal to its residue field, where it would define a
singular affine point of an elliptic curve.

The formulas and proof are selectively adapted from AINTLIB's
`projects/ModularCurves/ModularCurves/EllipticCurve/WeierstrassModel.lean` at commit
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`, exact source blob
`0cea4fbbcd8f0976b8cb0949755ecacec6e58b26` (Apache-2.0).  Only the generic
dehomogenized Jacobian-comaximality slice is retained here; no smoothness, chart-ring,
point-dictionary, or moduli assertion is made.
-/

noncomputable section

open MvPolynomial

namespace MazurTorsion.ModularCurve.XZeroModuli.GammaOneTate
namespace ProjectiveFamily

universe u

variable {R : Type u} [CommRing R]

private lemma ringHom_eq_aeval {σ : Type} {K : Type u} [CommRing K] [Algebra R K]
    (χ : MvPolynomial σ R →+* K)
    (hχ : ∀ r, χ (MvPolynomial.C r) = algebraMap R K r)
    (p : MvPolynomial σ R) :
    χ p = MvPolynomial.aeval (fun j => χ (MvPolynomial.X j)) p := by
  have hχ' : ∀ r, χ (algebraMap R (MvPolynomial σ R) r) = algebraMap R K r := by
    intro r
    rw [MvPolynomial.algebraMap_eq]
    exact hχ r
  have h := MvPolynomial.aeval_unique (⟨χ, hχ'⟩ : MvPolynomial σ R →ₐ[R] K)
  calc χ p = (⟨χ, hχ'⟩ : MvPolynomial σ R →ₐ[R] K) p := rfl
    _ = _ := by rw [h]; rfl

private lemma aeval_dehomog_two (W : WeierstrassCurve R) {K : Type u} [CommRing K]
    [Algebra R K] (v : {j : Fin 3 // j ≠ 2} → K) :
    MvPolynomial.aeval v
        (MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial) =
      v ⟨1, by decide⟩ ^ 2 + algebraMap R K W.a₁ * v ⟨0, by decide⟩ * v ⟨1, by decide⟩
        + algebraMap R K W.a₃ * v ⟨1, by decide⟩
        - (v ⟨0, by decide⟩ ^ 3 + algebraMap R K W.a₂ * v ⟨0, by decide⟩ ^ 2
          + algebraMap R K W.a₄ * v ⟨0, by decide⟩ + algebraMap R K W.a₆) := by
  rw [WeierstrassCurve.Projective.polynomial]
  simp only [map_sub, map_add, map_mul, map_pow,
    MvPolynomial.dehomogenizeAux_C, MvPolynomial.dehomogenizeAux_X_self,
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (0 : Fin 3) ≠ 2 by decide),
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (1 : Fin 3) ≠ 2 by decide),
    MvPolynomial.aeval_C, MvPolynomial.aeval_X, mul_one, one_pow]

private lemma aeval_dehomog_one (W : WeierstrassCurve R) {K : Type u} [CommRing K]
    [Algebra R K] (v : {j : Fin 3 // j ≠ 1} → K) :
    MvPolynomial.aeval v
        (MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial) =
      v ⟨2, by decide⟩ + algebraMap R K W.a₁ * v ⟨0, by decide⟩ * v ⟨2, by decide⟩
        + algebraMap R K W.a₃ * v ⟨2, by decide⟩ ^ 2
        - (v ⟨0, by decide⟩ ^ 3
          + algebraMap R K W.a₂ * v ⟨0, by decide⟩ ^ 2 * v ⟨2, by decide⟩
          + algebraMap R K W.a₄ * v ⟨0, by decide⟩ * v ⟨2, by decide⟩ ^ 2
          + algebraMap R K W.a₆ * v ⟨2, by decide⟩ ^ 3) := by
  rw [WeierstrassCurve.Projective.polynomial]
  simp only [map_sub, map_add, map_mul, map_pow,
    MvPolynomial.dehomogenizeAux_C, MvPolynomial.dehomogenizeAux_X_self,
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (0 : Fin 3) ≠ 1 by decide),
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (2 : Fin 3) ≠ 1 by decide),
    MvPolynomial.aeval_C, MvPolynomial.aeval_X, mul_one, one_pow, one_mul]

private lemma aeval_dehomog_zero (W : WeierstrassCurve R) {K : Type u} [CommRing K]
    [Algebra R K] (v : {j : Fin 3 // j ≠ 0} → K) :
    MvPolynomial.aeval v
        (MvPolynomial.dehomogenizeAux R 0 W.toProjective.polynomial) =
      v ⟨1, by decide⟩ ^ 2 * v ⟨2, by decide⟩
        + algebraMap R K W.a₁ * v ⟨1, by decide⟩ * v ⟨2, by decide⟩
        + algebraMap R K W.a₃ * v ⟨1, by decide⟩ * v ⟨2, by decide⟩ ^ 2
        - (1 + algebraMap R K W.a₂ * v ⟨2, by decide⟩
          + algebraMap R K W.a₄ * v ⟨2, by decide⟩ ^ 2
          + algebraMap R K W.a₆ * v ⟨2, by decide⟩ ^ 3) := by
  rw [WeierstrassCurve.Projective.polynomial]
  simp only [map_sub, map_add, map_mul, map_pow,
    MvPolynomial.dehomogenizeAux_C, MvPolynomial.dehomogenizeAux_X_self,
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (1 : Fin 3) ≠ 0 by decide),
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (2 : Fin 3) ≠ 0 by decide),
    MvPolynomial.aeval_C, MvPolynomial.aeval_X, map_one, mul_one, one_pow]

private lemma aeval_pderiv_dehomog_two_u (W : WeierstrassCurve R) {K : Type u}
    [CommRing K] [Algebra R K] (v : {j : Fin 3 // j ≠ 2} → K) :
    MvPolynomial.aeval v (MvPolynomial.pderiv ⟨0, by decide⟩
        (MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial)) =
      algebraMap R K W.a₁ * v ⟨1, by decide⟩ - (3 * v ⟨0, by decide⟩ ^ 2
        + 2 * algebraMap R K W.a₂ * v ⟨0, by decide⟩ + algebraMap R K W.a₄) := by
  rw [WeierstrassCurve.Projective.polynomial]
  simp only [map_sub, map_add, map_mul, map_pow,
    MvPolynomial.dehomogenizeAux_C, MvPolynomial.dehomogenizeAux_X_self,
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (0 : Fin 3) ≠ 2 by decide),
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (1 : Fin 3) ≠ 2 by decide),
    mul_one, one_pow]
  simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_C,
    MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_X_of_ne (show (⟨1, by decide⟩ : {j : Fin 3 // j ≠ 2}) ≠
      ⟨0, by decide⟩ by simp), map_add]
  simp only [map_add, map_mul, map_pow, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, map_zero, map_one, map_natCast]
  ring

private lemma aeval_pderiv_dehomog_two_v (W : WeierstrassCurve R) {K : Type u}
    [CommRing K] [Algebra R K] (v : {j : Fin 3 // j ≠ 2} → K) :
    MvPolynomial.aeval v (MvPolynomial.pderiv ⟨1, by decide⟩
        (MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial)) =
      2 * v ⟨1, by decide⟩ + algebraMap R K W.a₁ * v ⟨0, by decide⟩
        + algebraMap R K W.a₃ := by
  rw [WeierstrassCurve.Projective.polynomial]
  simp only [map_sub, map_add, map_mul, map_pow,
    MvPolynomial.dehomogenizeAux_C, MvPolynomial.dehomogenizeAux_X_self,
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (0 : Fin 3) ≠ 2 by decide),
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (1 : Fin 3) ≠ 2 by decide),
    mul_one, one_pow]
  simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_C,
    MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_X_of_ne (show (⟨0, by decide⟩ : {j : Fin 3 // j ≠ 2}) ≠
      ⟨1, by decide⟩ by simp), map_add]
  simp only [map_add, map_mul, map_pow, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, map_zero, map_one, map_natCast]
  ring

/-- For an elliptic Weierstrass curve, the dehomogenized cubic and its two partials
generate the unit ideal on the `Z`-chart. -/
theorem span_dehomog_jacobian_eq_top (W : WeierstrassCurve R) [W.IsElliptic] :
    Ideal.span {MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial,
      MvPolynomial.pderiv ⟨0, by decide⟩
        (MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial),
      MvPolynomial.pderiv ⟨1, by decide⟩
        (MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial)} = ⊤ := by
  by_contra hne
  obtain ⟨m, hmax, hle⟩ := Ideal.exists_le_maximal _ hne
  letI : Field (MvPolynomial {j : Fin 3 // j ≠ 2} R ⧸ m) := Ideal.Quotient.field m
  set q : MvPolynomial {j : Fin 3 // j ≠ 2} R →+*
      MvPolynomial {j : Fin 3 // j ≠ 2} R ⧸ m := Ideal.Quotient.mk m with hq
  letI : Algebra R (MvPolynomial {j : Fin 3 // j ≠ 2} R ⧸ m) :=
    (q.comp (algebraMap R (MvPolynomial {j : Fin 3 // j ≠ 2} R))).toAlgebra
  have haev : ∀ p : MvPolynomial {j : Fin 3 // j ≠ 2} R,
      q p = MvPolynomial.aeval (fun j => q (MvPolynomial.X j)) p :=
    ringHom_eq_aeval q (fun r => rfl)
  set f : R →+* MvPolynomial {j : Fin 3 // j ≠ 2} R ⧸ m :=
    q.comp (algebraMap R (MvPolynomial {j : Fin 3 // j ≠ 2} R)) with hf
  have halg : algebraMap R (MvPolynomial {j : Fin 3 // j ≠ 2} R ⧸ m) = f := rfl
  have hmem : ∀ p ∈ ({MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial,
      MvPolynomial.pderiv ⟨0, by decide⟩
        (MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial),
      MvPolynomial.pderiv ⟨1, by decide⟩
        (MvPolynomial.dehomogenizeAux R 2 W.toProjective.polynomial)} :
      Set (MvPolynomial {j : Fin 3 // j ≠ 2} R)), q p = 0 := by
    intro p hp
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span hp))
  have h1 : (W.map f).toAffine.Equation (q (MvPolynomial.X ⟨0, by decide⟩))
      (q (MvPolynomial.X ⟨1, by decide⟩)) := by
    rw [WeierstrassCurve.Affine.equation_iff]
    have hF := hmem _ (Set.mem_insert _ _)
    rw [haev, aeval_dehomog_two] at hF
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
    linear_combination hF
  have h2 : ¬ (W.map f).toAffine.Nonsingular (q (MvPolynomial.X ⟨0, by decide⟩))
      (q (MvPolynomial.X ⟨1, by decide⟩)) := by
    rw [WeierstrassCurve.Affine.nonsingular_iff']
    rintro ⟨-, hu | hv⟩
    · apply hu
      have hFu := hmem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      rw [haev, aeval_pderiv_dehomog_two_u] at hFu
      simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
        WeierstrassCurve.map_a₄]
      linear_combination hFu
    · apply hv
      have hFv := hmem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
      rw [haev, aeval_pderiv_dehomog_two_v] at hFv
      simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
      linear_combination hFv
  haveI : ((W.map f).toAffine).IsElliptic := inferInstanceAs ((W.map f).IsElliptic)
  exact h2 (WeierstrassCurve.Affine.equation_iff_nonsingular.mp h1)

private lemma aeval_pderiv_dehomog_one_u (W : WeierstrassCurve R) {K : Type u}
    [CommRing K] [Algebra R K] (v : {j : Fin 3 // j ≠ 1} → K) :
    MvPolynomial.aeval v (MvPolynomial.pderiv ⟨0, by decide⟩
        (MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial)) =
      algebraMap R K W.a₁ * v ⟨2, by decide⟩ - (3 * v ⟨0, by decide⟩ ^ 2
        + 2 * algebraMap R K W.a₂ * v ⟨0, by decide⟩ * v ⟨2, by decide⟩
        + algebraMap R K W.a₄ * v ⟨2, by decide⟩ ^ 2) := by
  rw [WeierstrassCurve.Projective.polynomial]
  simp only [map_sub, map_add, map_mul, map_pow,
    MvPolynomial.dehomogenizeAux_C, MvPolynomial.dehomogenizeAux_X_self,
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (0 : Fin 3) ≠ 1 by decide),
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (2 : Fin 3) ≠ 1 by decide),
    mul_one, one_pow, one_mul]
  simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_C,
    MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_X_of_ne (show (⟨2, by decide⟩ : {j : Fin 3 // j ≠ 1}) ≠
      ⟨0, by decide⟩ by simp), map_add]
  simp only [map_add, map_mul, map_pow, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, map_zero, map_one, map_natCast]
  ring

private lemma aeval_pderiv_dehomog_one_w (W : WeierstrassCurve R) {K : Type u}
    [CommRing K] [Algebra R K] (v : {j : Fin 3 // j ≠ 1} → K) :
    MvPolynomial.aeval v (MvPolynomial.pderiv ⟨2, by decide⟩
        (MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial)) =
      1 + algebraMap R K W.a₁ * v ⟨0, by decide⟩
        + 2 * algebraMap R K W.a₃ * v ⟨2, by decide⟩
        - (algebraMap R K W.a₂ * v ⟨0, by decide⟩ ^ 2
          + 2 * algebraMap R K W.a₄ * v ⟨0, by decide⟩ * v ⟨2, by decide⟩
          + 3 * algebraMap R K W.a₆ * v ⟨2, by decide⟩ ^ 2) := by
  rw [WeierstrassCurve.Projective.polynomial]
  simp only [map_sub, map_add, map_mul, map_pow,
    MvPolynomial.dehomogenizeAux_C, MvPolynomial.dehomogenizeAux_X_self,
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (0 : Fin 3) ≠ 1 by decide),
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (2 : Fin 3) ≠ 1 by decide),
    mul_one, one_pow, one_mul]
  simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_C,
    MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_X_of_ne (show (⟨0, by decide⟩ : {j : Fin 3 // j ≠ 1}) ≠
      ⟨2, by decide⟩ by simp), map_add]
  simp only [map_add, map_mul, map_pow, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, map_zero, map_one, map_natCast]
  ring

private lemma aeval_pderiv_dehomog_zero_s (W : WeierstrassCurve R) {K : Type u}
    [CommRing K] [Algebra R K] (v : {j : Fin 3 // j ≠ 0} → K) :
    MvPolynomial.aeval v (MvPolynomial.pderiv ⟨1, by decide⟩
        (MvPolynomial.dehomogenizeAux R 0 W.toProjective.polynomial)) =
      2 * v ⟨1, by decide⟩ * v ⟨2, by decide⟩
        + algebraMap R K W.a₁ * v ⟨2, by decide⟩
        + algebraMap R K W.a₃ * v ⟨2, by decide⟩ ^ 2 := by
  rw [WeierstrassCurve.Projective.polynomial]
  simp only [map_sub, map_add, map_mul, map_pow,
    MvPolynomial.dehomogenizeAux_C, MvPolynomial.dehomogenizeAux_X_self,
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (1 : Fin 3) ≠ 0 by decide),
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (2 : Fin 3) ≠ 0 by decide),
    mul_one, one_pow]
  simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_C,
    MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_X_of_ne (show (⟨2, by decide⟩ : {j : Fin 3 // j ≠ 0}) ≠
      ⟨1, by decide⟩ by simp), map_add, Derivation.map_one_eq_zero]
  simp only [map_add, map_mul, map_pow, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, map_zero, map_one, map_natCast]
  ring

private lemma aeval_pderiv_dehomog_zero_t (W : WeierstrassCurve R) {K : Type u}
    [CommRing K] [Algebra R K] (v : {j : Fin 3 // j ≠ 0} → K) :
    MvPolynomial.aeval v (MvPolynomial.pderiv ⟨2, by decide⟩
        (MvPolynomial.dehomogenizeAux R 0 W.toProjective.polynomial)) =
      v ⟨1, by decide⟩ ^ 2 + algebraMap R K W.a₁ * v ⟨1, by decide⟩
        + 2 * algebraMap R K W.a₃ * v ⟨1, by decide⟩ * v ⟨2, by decide⟩
        - (algebraMap R K W.a₂ + 2 * algebraMap R K W.a₄ * v ⟨2, by decide⟩
          + 3 * algebraMap R K W.a₆ * v ⟨2, by decide⟩ ^ 2) := by
  rw [WeierstrassCurve.Projective.polynomial]
  simp only [map_sub, map_add, map_mul, map_pow,
    MvPolynomial.dehomogenizeAux_C, MvPolynomial.dehomogenizeAux_X_self,
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (1 : Fin 3) ≠ 0 by decide),
    MvPolynomial.dehomogenizeAux_X_ne _ _ (show (2 : Fin 3) ≠ 0 by decide),
    mul_one, one_pow]
  simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_C,
    MvPolynomial.pderiv_X_self,
    MvPolynomial.pderiv_X_of_ne (show (⟨1, by decide⟩ : {j : Fin 3 // j ≠ 0}) ≠
      ⟨2, by decide⟩ by simp), map_add, Derivation.map_one_eq_zero]
  simp only [map_add, map_mul, map_pow, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, map_zero, map_one, map_natCast]
  ring

private lemma not_affine_singular (W : WeierstrassCurve R) [W.IsElliptic]
    {K : Type u} [Field K] [Algebra R K] (x y : K)
    (hE : y ^ 2 + algebraMap R K W.a₁ * x * y + algebraMap R K W.a₃ * y =
      x ^ 3 + algebraMap R K W.a₂ * x ^ 2 + algebraMap R K W.a₄ * x
        + algebraMap R K W.a₆)
    (hx : algebraMap R K W.a₁ * y = 3 * x ^ 2 + 2 * algebraMap R K W.a₂ * x
      + algebraMap R K W.a₄)
    (hy : 2 * y + algebraMap R K W.a₁ * x + algebraMap R K W.a₃ = 0) : False := by
  haveI : ((W.map (algebraMap R K)).toAffine).IsElliptic :=
    inferInstanceAs ((W.map (algebraMap R K)).IsElliptic)
  have h1 : (W.map (algebraMap R K)).toAffine.Equation x y := by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
    linear_combination hE
  have h2 := WeierstrassCurve.Affine.equation_iff_nonsingular.mp h1
  rw [WeierstrassCurve.Affine.nonsingular_iff'] at h2
  rcases h2.2 with h | h
  · exact h (by
      simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
        WeierstrassCurve.map_a₄]
      linear_combination hx)
  · exact h (by
      simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
      linear_combination hy)

/-- For an elliptic Weierstrass curve, the dehomogenized cubic and its two partials
generate the unit ideal on the `Y`-chart. -/
theorem span_dehomog_jacobian_eq_top_one (W : WeierstrassCurve R) [W.IsElliptic] :
    Ideal.span {MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial,
      MvPolynomial.pderiv ⟨0, by decide⟩
        (MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial),
      MvPolynomial.pderiv ⟨2, by decide⟩
        (MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial)} = ⊤ := by
  by_contra hne
  obtain ⟨m, hmax, hle⟩ := Ideal.exists_le_maximal _ hne
  letI : Field (MvPolynomial {j : Fin 3 // j ≠ 1} R ⧸ m) := Ideal.Quotient.field m
  set q : MvPolynomial {j : Fin 3 // j ≠ 1} R →+*
      MvPolynomial {j : Fin 3 // j ≠ 1} R ⧸ m := Ideal.Quotient.mk m with hq
  letI : Algebra R (MvPolynomial {j : Fin 3 // j ≠ 1} R ⧸ m) :=
    (q.comp (algebraMap R (MvPolynomial {j : Fin 3 // j ≠ 1} R))).toAlgebra
  have haev : ∀ p : MvPolynomial {j : Fin 3 // j ≠ 1} R,
      q p = MvPolynomial.aeval (fun j => q (MvPolynomial.X j)) p :=
    ringHom_eq_aeval q (fun r => rfl)
  have hmem : ∀ p ∈ ({MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial,
      MvPolynomial.pderiv ⟨0, by decide⟩
        (MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial),
      MvPolynomial.pderiv ⟨2, by decide⟩
        (MvPolynomial.dehomogenizeAux R 1 W.toProjective.polynomial)} :
      Set (MvPolynomial {j : Fin 3 // j ≠ 1} R)), q p = 0 := fun p hp =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span hp))
  set u := q (MvPolynomial.X ⟨0, by decide⟩) with hu
  set w := q (MvPolynomial.X ⟨2, by decide⟩) with hwdef
  have hF := hmem _ (Set.mem_insert _ _)
  have hU := hmem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hW := hmem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  rw [haev, aeval_dehomog_one] at hF
  rw [haev, aeval_pderiv_dehomog_one_u] at hU
  rw [haev, aeval_pderiv_dehomog_one_w] at hW
  by_cases hw : w = 0
  · rw [← hu, ← hwdef, hw] at hF hW
    have hu3 : u ^ 3 = 0 := by linear_combination -hF
    have hu0 : u = 0 := pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0) |>.mp hu3
    rw [hu0] at hW
    exact one_ne_zero (by linear_combination hW)
  · rw [← hu, ← hwdef] at hF hU hW
    have hinv : w * w⁻¹ = 1 := mul_inv_cancel₀ hw
    have hcomb : w * (2 + algebraMap R _ W.a₁ * u + algebraMap R _ W.a₃ * w) = 0 := by
      linear_combination 3 * hF - u * hU - w * hW
    have h2aw : 2 + algebraMap R _ W.a₁ * u + algebraMap R _ W.a₃ * w = 0 :=
      (mul_eq_zero.mp hcomb).resolve_left hw
    refine not_affine_singular W (u * w⁻¹) w⁻¹ ?_ ?_ ?_
    · field_simp
      linear_combination hF
    · field_simp
      linear_combination hU
    · field_simp
      linear_combination h2aw

/-- For an elliptic Weierstrass curve, the dehomogenized cubic and its two partials
generate the unit ideal on the `X`-chart. -/
theorem span_dehomog_jacobian_eq_top_zero (W : WeierstrassCurve R) [W.IsElliptic] :
    Ideal.span {MvPolynomial.dehomogenizeAux R 0 W.toProjective.polynomial,
      MvPolynomial.pderiv ⟨1, by decide⟩
        (MvPolynomial.dehomogenizeAux R 0 W.toProjective.polynomial),
      MvPolynomial.pderiv ⟨2, by decide⟩
        (MvPolynomial.dehomogenizeAux R 0 W.toProjective.polynomial)} = ⊤ := by
  by_contra hne
  obtain ⟨m, hmax, hle⟩ := Ideal.exists_le_maximal _ hne
  letI : Field (MvPolynomial {j : Fin 3 // j ≠ 0} R ⧸ m) := Ideal.Quotient.field m
  set q : MvPolynomial {j : Fin 3 // j ≠ 0} R →+*
      MvPolynomial {j : Fin 3 // j ≠ 0} R ⧸ m := Ideal.Quotient.mk m with hq
  letI : Algebra R (MvPolynomial {j : Fin 3 // j ≠ 0} R ⧸ m) :=
    (q.comp (algebraMap R (MvPolynomial {j : Fin 3 // j ≠ 0} R))).toAlgebra
  have haev : ∀ p : MvPolynomial {j : Fin 3 // j ≠ 0} R,
      q p = MvPolynomial.aeval (fun j => q (MvPolynomial.X j)) p :=
    ringHom_eq_aeval q (fun r => rfl)
  have hmem : ∀ p ∈ ({MvPolynomial.dehomogenizeAux R 0 W.toProjective.polynomial,
      MvPolynomial.pderiv ⟨1, by decide⟩
        (MvPolynomial.dehomogenizeAux R 0 W.toProjective.polynomial),
      MvPolynomial.pderiv ⟨2, by decide⟩
        (MvPolynomial.dehomogenizeAux R 0 W.toProjective.polynomial)} :
      Set (MvPolynomial {j : Fin 3 // j ≠ 0} R)), q p = 0 := fun p hp =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span hp))
  set sc := q (MvPolynomial.X ⟨1, by decide⟩) with hsc
  set t := q (MvPolynomial.X ⟨2, by decide⟩) with htdef
  have hF := hmem _ (Set.mem_insert _ _)
  have hS := hmem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hT := hmem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  rw [haev, aeval_dehomog_zero] at hF
  rw [haev, aeval_pderiv_dehomog_zero_s] at hS
  rw [haev, aeval_pderiv_dehomog_zero_t] at hT
  by_cases ht : t = 0
  · rw [← hsc, ← htdef, ht] at hF
    exact one_ne_zero (by linear_combination -hF)
  · rw [← hsc, ← htdef] at hF hS hT
    have hinv : t * t⁻¹ = 1 := mul_inv_cancel₀ ht
    have hcomb : algebraMap R _ W.a₁ * sc * t - 3
        - 2 * algebraMap R _ W.a₂ * t - algebraMap R _ W.a₄ * t ^ 2 = 0 := by
      linear_combination 3 * hF - sc * hS - t * hT
    have hsplit : t * (2 * sc + algebraMap R _ W.a₁ + algebraMap R _ W.a₃ * t) = 0 := by
      linear_combination hS
    have hy0 := (mul_eq_zero.mp hsplit).resolve_left ht
    refine not_affine_singular W t⁻¹ (sc * t⁻¹) ?_ ?_ ?_
    · field_simp
      linear_combination hF
    · field_simp
      linear_combination hcomb
    · field_simp
      linear_combination hy0

end ProjectiveFamily
end MazurTorsion.ModularCurve.XZeroModuli.GammaOneTate

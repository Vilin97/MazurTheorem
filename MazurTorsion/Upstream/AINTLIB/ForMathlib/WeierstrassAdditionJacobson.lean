/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors, Chris Birkbeck

This file selectively adapts the reduced-Jacobson addition-law declarations
from AINTLIB's `EllipticCurve/AdditionLawOnCurve.lean`, exact source blob
`6cdd1aa98921c9fbf607b855e3243de316fdca6d`. Its private vanishing helper is
adapted from `EllipticCurve/AdditionLaw.lean`, exact source blob
`c6ea88db42629fd166902494bb5617d4511e309b`. Both source blobs are present at
AINTLIB's Apache-2.0 licensed default commit
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`.
-/

import MazurTorsion.Upstream.AINTLIB.ForMathlib.WeierstrassSecondAdditionCoverage
import Mathlib.RingTheory.Jacobson.Ring

/-!
# Weierstrass addition laws over reduced Jacobson rings

Evaluation in residue fields promotes the field-valued curve equations for
the two Bosma–Lenstra addition triples to reduced Jacobson rings. The two
public theorems are the ring-level inputs needed to construct addition-chart
morphisms; no chart or scheme definitions occur here.
-/

local notation3 "x" => (0 : Fin 3)
local notation3 "y" => (1 : Fin 3)
local notation3 "z" => (2 : Fin 3)

namespace WeierstrassCurve.Projective

local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow,
    WeierstrassCurve.map, Function.comp_apply])

section Map

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {W' : Projective R}

private lemma map_dblAddX (P Q : Fin 3 → R) :
    (W'.map f).dblAddX (f ∘ P) (f ∘ Q) = f (W'.dblAddX P Q) := by
  simp only [dblAddX]
  map_simp

private lemma map_dblAddY (P Q : Fin 3 → R) :
    (W'.map f).dblAddY (f ∘ P) (f ∘ Q) = f (W'.dblAddY P Q) := by
  simp only [dblAddY]
  map_simp

private lemma map_dblAddZ (P Q : Fin 3 → R) :
    (W'.map f).dblAddZ (f ∘ P) (f ∘ Q) = f (W'.dblAddZ P Q) := by
  simp only [dblAddZ]
  map_simp

private lemma map_dblAddXYZ (P Q : Fin 3 → R) :
    (W'.map f).dblAddXYZ (f ∘ P) (f ∘ Q) = f ∘ W'.dblAddXYZ P Q := by
  funext i
  fin_cases i
  · change (W'.map f).dblAddX (f ∘ P) (f ∘ Q) = f (W'.dblAddX P Q)
    exact map_dblAddX f P Q
  · change (W'.map f).dblAddY (f ∘ P) (f ∘ Q) = f (W'.dblAddY P Q)
    exact map_dblAddY f P Q
  · change (W'.map f).dblAddZ (f ∘ P) (f ∘ Q) = f (W'.dblAddZ P Q)
    exact map_dblAddZ f P Q

end Map

section ZeroArgs

variable {R : Type*} [CommRing R] {W' : Projective R}

private lemma dblAddXYZ_zero_fst (Q : Fin 3 → R) : W'.dblAddXYZ 0 Q = 0 := by
  have h := W'.dblAddXYZ_smul_left Q Q 0
  rwa [zero_smul, zero_pow two_ne_zero, zero_smul] at h

private lemma dblAddXYZ_smul_right (P Q : Fin 3 → R) (v : R) :
    W'.dblAddXYZ P (v • Q) = v ^ 2 • W'.dblAddXYZ P Q := by
  simpa using W'.dblAddXYZ_smul P Q 1 v

private lemma dblAddXYZ_zero_snd (P : Fin 3 → R) : W'.dblAddXYZ P 0 = 0 := by
  have h := dblAddXYZ_smul_right (W' := W') P P 0
  rwa [zero_smul, zero_pow two_ne_zero, zero_smul] at h

private lemma addXYZ_zero_fst (Q : Fin 3 → R) : W'.addXYZ 0 Q = 0 := by
  have h := W'.addXYZ_smul_left Q Q 0
  rwa [zero_smul, zero_pow two_ne_zero, zero_smul] at h

private lemma addXYZ_smul_right (P Q : Fin 3 → R) (v : R) :
    W'.addXYZ P (v • Q) = v ^ 2 • W'.addXYZ P Q := by
  simpa using W'.addXYZ_smul P Q 1 v

private lemma addXYZ_zero_snd (P : Fin 3 → R) : W'.addXYZ P 0 = 0 := by
  have h := addXYZ_smul_right (W' := W') P P 0
  rwa [zero_smul, zero_pow two_ne_zero, zero_smul] at h

end ZeroArgs

section Field

variable {F : Type*} [Field F] {W : Projective F}

private lemma nonsingular_of_equation_of_ne_zero [W.IsElliptic] {P : Fin 3 → F}
    (hP : W.Equation P) (h0 : P ≠ 0) : W.Nonsingular P := by
  by_cases hz : P z = 0
  · have hx : P x = 0 := X_eq_zero_of_Z_eq_zero hP hz
    have hy : P y ≠ 0 := by
      intro hy
      refine h0 (funext fun j => ?_)
      fin_cases j
      exacts [hx, hy, hz]
    have hPy : P = P y • ![0, 1, 0] := by
      funext j
      fin_cases j
      · change P x = P y * 0
        rw [hx, mul_zero]
      · change P y = P y * 1
        rw [mul_one]
      · change P z = P y * 0
        rw [hz, mul_zero]
    rw [hPy, nonsingular_smul _ (Ne.isUnit hy)]
    exact nonsingular_zero
  · rw [nonsingular_of_Z_ne_zero hz, ← Affine.equation_iff_nonsingular]
    exact (equation_of_Z_ne_zero hz).mp hP

private theorem equation_dblAddXYZ_of_equation [W.IsElliptic] {P Q : Fin 3 → F}
    (hP : W.Equation P) (hQ : W.Equation Q) : W.Equation (W.dblAddXYZ P Q) := by
  by_cases h0P : P = 0
  · rw [h0P, dblAddXYZ_zero_fst]
    exact equation_zero_triple
  by_cases h0Q : Q = 0
  · rw [h0Q, dblAddXYZ_zero_snd]
    exact equation_zero_triple
  exact equation_dblAddXYZ (nonsingular_of_equation_of_ne_zero hP h0P)
    (nonsingular_of_equation_of_ne_zero hQ h0Q)

private theorem equation_addXYZ_of_equation [W.IsElliptic] {P Q : Fin 3 → F}
    (hP : W.Equation P) (hQ : W.Equation Q) : W.Equation (W.addXYZ P Q) := by
  by_cases h0P : P = 0
  · rw [h0P, addXYZ_zero_fst]
    exact equation_zero_triple
  by_cases h0Q : Q = 0
  · rw [h0Q, addXYZ_zero_snd]
    exact equation_zero_triple
  exact equation_addXYZ (nonsingular_of_equation_of_ne_zero hP h0P)
    (nonsingular_of_equation_of_ne_zero hQ h0Q)

end Field

private theorem eq_zero_of_forall_isMaximal_mem {A : Type*} [CommRing A]
    [IsJacobsonRing A] [IsReduced A] {a : A}
    (h : ∀ I : Ideal A, I.IsMaximal → a ∈ I) : a = 0 := by
  have hj : a ∈ (⊥ : Ideal A).jacobson := Ideal.mem_sInf.mpr fun _ hJ => h _ hJ.2
  rw [← Ideal.radical_eq_jacobson] at hj
  have hn : a ∈ nilradical A := hj
  rwa [nilradical_eq_zero, Ideal.zero_eq_bot, Ideal.mem_bot] at hn

section RingHom

variable {A : Type*} [CommRing A]

open MvPolynomial in
private lemma map_polynomial_eval_dblAddXYZ_eq_zero {K : Type*} [CommRing K]
    (hK : IsField K) (φ : A →+* K) {W' : Projective A} (hΔ : IsUnit W'.Δ)
    {P Q : Fin 3 → A} (hP : W'.Equation P) (hQ : W'.Equation Q) :
    φ (eval (W'.dblAddXYZ P Q) W'.polynomial) = 0 := by
  letI := hK.toField
  haveI : (W'.map φ).IsElliptic := ⟨by rw [map_Δ]; exact hΔ.map φ⟩
  have key : (W'.map φ).Equation ((W'.map φ).dblAddXYZ (φ ∘ P) (φ ∘ Q)) :=
    equation_dblAddXYZ_of_equation (hP.map φ) (hQ.map φ)
  rw [map_dblAddXYZ] at key
  rwa [Equation, map_polynomial, eval_map, ← eval₂_comp] at key

open MvPolynomial in
private lemma map_polynomial_eval_addXYZ_eq_zero {K : Type*} [CommRing K]
    (hK : IsField K) (φ : A →+* K) {W' : Projective A} (hΔ : IsUnit W'.Δ)
    {P Q : Fin 3 → A} (hP : W'.Equation P) (hQ : W'.Equation Q) :
    φ (eval (W'.addXYZ P Q) W'.polynomial) = 0 := by
  letI := hK.toField
  haveI : (W'.map φ).IsElliptic := ⟨by rw [map_Δ]; exact hΔ.map φ⟩
  have key : (W'.map φ).Equation ((W'.map φ).addXYZ (φ ∘ P) (φ ∘ Q)) :=
    equation_addXYZ_of_equation (hP.map φ) (hQ.map φ)
  rw [map_addXYZ] at key
  rwa [Equation, map_polynomial, eval_map, ← eval₂_comp] at key

end RingHom

section Jacobson

variable {A : Type*} [CommRing A] [IsReduced A] [IsJacobsonRing A]
  {W' : Projective A}

open MvPolynomial in
/-- Over a reduced Jacobson ring with invertible discriminant, the second
Bosma–Lenstra addition triple satisfies the Weierstrass equation. -/
theorem equation_dblAddXYZ_of_isJacobsonRing (hΔ : IsUnit W'.Δ) {P Q : Fin 3 → A}
    (hP : W'.Equation P) (hQ : W'.Equation Q) : W'.Equation (W'.dblAddXYZ P Q) := by
  rw [Equation]
  refine eq_zero_of_forall_isMaximal_mem fun m hm => ?_
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact map_polynomial_eval_dblAddXYZ_eq_zero
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient m).mp hm)
    (Ideal.Quotient.mk m) hΔ hP hQ

open MvPolynomial in
/-- Over a reduced Jacobson ring with invertible discriminant, Mathlib's first
Bosma–Lenstra addition triple satisfies the Weierstrass equation. -/
theorem equation_addXYZ_of_isJacobsonRing (hΔ : IsUnit W'.Δ) {P Q : Fin 3 → A}
    (hP : W'.Equation P) (hQ : W'.Equation Q) : W'.Equation (W'.addXYZ P Q) := by
  rw [Equation]
  refine eq_zero_of_forall_isMaximal_mem fun m hm => ?_
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact map_polynomial_eval_addXYZ_eq_zero
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient m).mp hm)
    (Ideal.Quotient.mk m) hΔ hP hQ

end Jacobson

end WeierstrassCurve.Projective

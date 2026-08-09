/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck

This file adapts AINTLIB's `EllipticCurve/AdditionChartTensor.lean`, exact
source blob `8934898a972e7abe51cadbd34942849d1d0dc629`. The source blob is present at
AINTLIB's Apache-2.0 licensed default commit
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`.
-/

import MazurTorsion.Upstream.AINTLIB.ForMathlib.WeierstrassAdditionChartRing

/-!
# The chart-product ring is the tensor product of the chart rings (T-W7.0c-c5β, β1 core)

`biChartRing W i j ≃ₐ[R] affineChartRing W i ⊗[R] affineChartRing W j`.

This is the algebra half of β1: `pullbackSpecIso` identifies `Γ` of the `(i,j)` chart-product
of `E ×_R E` with `chartRing i ⊗[R] chartRing j`, and this equivalence transports the
addition-law triples (`lawOneTriple`, `lawTwoTriple`) and their on-curve theorems onto that
`Γ`, where the `addOnZ`/`addOnY` chart morphisms are defined.

Built directly (`AlgEquiv.ofAlgHom`) rather than by chasing extended ideals: forward is
`aeval` of the two families of generators; backward is `Algebra.TensorProduct.lift` of the two
rename-and-quotient maps. The two key computation lemmas say that the forward map turns
`rename Sum.inl`/`rename Sum.inr` into `· ⊗ₜ 1` / `1 ⊗ₜ ·`, which is exactly why the two curve
relations die.
-/

open MvPolynomial TensorProduct

namespace WeierstrassCurve.Projective

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (i j : Fin 3)

local notation "A" => affineChartRing W i
local notation "B" => affineChartRing W j

/-- The generators of the chart-product, sent into the tensor product. -/
private noncomputable def toTensorAux :
    MvPolynomial ({k : Fin 3 // k ≠ i} ⊕ {k : Fin 3 // k ≠ j}) R →ₐ[R] A ⊗[R] B :=
  aeval (Sum.elim
    (fun k => (Ideal.Quotient.mk _ (X k) : A) ⊗ₜ[R] (1 : B))
    (fun k => (1 : A) ⊗ₜ[R] (Ideal.Quotient.mk _ (X k) : B)))

/-- The forward map turns the left factor's variables into `· ⊗ₜ 1`. -/
private lemma toTensorAux_rename_inl (p : MvPolynomial {k : Fin 3 // k ≠ i} R) :
    toTensorAux W i j (rename Sum.inl p) =
      (Ideal.Quotient.mk _ p : A) ⊗ₜ[R] (1 : B) := by
  have h : (toTensorAux W i j).comp (rename (R := R) (Sum.inl : {k : Fin 3 // k ≠ i} → _)) =
      (Algebra.TensorProduct.includeLeft (S := R)).comp
        (Ideal.Quotient.mkₐ R (Ideal.span
          {dehomogenizeAux R i W.toProjective.polynomial})) := by
    refine MvPolynomial.algHom_ext fun k => ?_
    simp [toTensorAux, Algebra.TensorProduct.includeLeft_apply]
  exact AlgHom.congr_fun h p

/-- The forward map turns the right factor's variables into `1 ⊗ₜ ·`. -/
private lemma toTensorAux_rename_inr (p : MvPolynomial {k : Fin 3 // k ≠ j} R) :
    toTensorAux W i j (rename Sum.inr p) =
      (1 : A) ⊗ₜ[R] (Ideal.Quotient.mk _ p : B) := by
  have h : (toTensorAux W i j).comp (rename (R := R) (Sum.inr : {k : Fin 3 // k ≠ j} → _)) =
      (Algebra.TensorProduct.includeRight).comp
        (Ideal.Quotient.mkₐ R (Ideal.span
          {dehomogenizeAux R j W.toProjective.polynomial})) := by
    refine MvPolynomial.algHom_ext fun k => ?_
    simp [toTensorAux, Algebra.TensorProduct.includeRight_apply]
  exact AlgHom.congr_fun h p

/-- The forward algebra map on the chart-product ring. -/
private noncomputable def toTensor : biChartRing W i j →ₐ[R] A ⊗[R] B :=
  Ideal.Quotient.liftₐ _ (toTensorAux W i j) <| by
    intro a ha
    refine Submodule.span_induction ?_ (by simp) (fun x y _ _ hx hy => by simp [hx, hy])
      (fun c x _ hx => by simp [hx]) ha
    rintro x (rfl | rfl)
    · rw [toTensorAux_rename_inl,
        show (Ideal.Quotient.mk _ (dehomogenizeAux R i W.toProjective.polynomial) : A) = 0 from
          (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mem_span_singleton_self _), zero_tmul]
    · rw [toTensorAux_rename_inr,
        show (Ideal.Quotient.mk _ (dehomogenizeAux R j W.toProjective.polynomial) : B) = 0 from
          (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mem_span_singleton_self _), tmul_zero]

/-- The left chart ring, into the chart-product ring. -/
private noncomputable def fromLeft : A →ₐ[R] biChartRing W i j :=
  Ideal.Quotient.liftₐ _
    ((Ideal.Quotient.mkₐ R _).comp (rename (R := R) Sum.inl)) <| by
      intro a ha
      rw [Ideal.mem_span_singleton] at ha
      obtain ⟨c, rfl⟩ := ha
      simp only [AlgHom.coe_comp, Function.comp_apply, map_mul, Ideal.Quotient.mkₐ_eq_mk]
      exact mul_eq_zero_of_left (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))) _

/-- The right chart ring, into the chart-product ring. -/
private noncomputable def fromRight : B →ₐ[R] biChartRing W i j :=
  Ideal.Quotient.liftₐ _
    ((Ideal.Quotient.mkₐ R _).comp (rename (R := R) Sum.inr)) <| by
      intro a ha
      rw [Ideal.mem_span_singleton] at ha
      obtain ⟨c, rfl⟩ := ha
      simp only [AlgHom.coe_comp, Function.comp_apply, map_mul, Ideal.Quotient.mkₐ_eq_mk]
      exact mul_eq_zero_of_left (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))) _

private lemma toTensor_mk (x : MvPolynomial ({k : Fin 3 // k ≠ i} ⊕ {k : Fin 3 // k ≠ j}) R) :
    toTensor W i j (Ideal.Quotient.mk _ x) = toTensorAux W i j x := rfl

private lemma fromLeft_mk (p : MvPolynomial {k : Fin 3 // k ≠ i} R) :
    fromLeft W i j (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (rename Sum.inl p) := rfl

private lemma fromRight_mk (q : MvPolynomial {k : Fin 3 // k ≠ j} R) :
    fromRight W i j (Ideal.Quotient.mk _ q) = Ideal.Quotient.mk _ (rename Sum.inr q) := rfl

/-- The backward algebra map. -/
private noncomputable def fromTensor : A ⊗[R] B →ₐ[R] biChartRing W i j :=
  Algebra.TensorProduct.lift (fromLeft W i j) (fromRight W i j) fun _ _ => Commute.all _ _

/-- **(β1 core)** The `(i,j)` chart-product ring of `E ×_R E` is the tensor product over `R` of
the two chart rings. `pullbackSpecIso` turns this into the identification of `Spec (biChartRing)`
with the `(i,j)` chart-product open of `E ×_R E`. -/
noncomputable def biChartRingTensorEquiv :
    biChartRing W i j ≃ₐ[R] A ⊗[R] B :=
  AlgEquiv.ofAlgHom (toTensor W i j) (fromTensor W i j)
    (by
      refine Algebra.TensorProduct.ext' fun a b => ?_
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
      simp only [AlgHom.comp_apply, AlgHom.id_apply]
      rw [fromTensor, Algebra.TensorProduct.lift_tmul, fromLeft_mk, fromRight_mk, ← map_mul,
        toTensor_mk, map_mul, toTensorAux_rename_inl, toTensorAux_rename_inr,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one])
    (by
      refine Ideal.Quotient.algHom_ext R (MvPolynomial.algHom_ext fun k => ?_)
      simp only [AlgHom.comp_apply, AlgHom.id_apply, Ideal.Quotient.mkₐ_eq_mk, toTensor_mk,
        toTensorAux, aeval_X]
      rcases k with k | k
      · rw [Sum.elim_inl, fromTensor, Algebra.TensorProduct.lift_tmul, map_one, mul_one,
          fromLeft_mk, rename_X]
      · rw [Sum.elim_inr, fromTensor, Algebra.TensorProduct.lift_tmul, map_one, one_mul,
          fromRight_mk, rename_X])

@[simp]
lemma biChartRingTensorEquiv_mk_rename_inl (p : MvPolynomial {k : Fin 3 // k ≠ i} R) :
    biChartRingTensorEquiv W i j (Ideal.Quotient.mk _ (rename Sum.inl p)) =
      (Ideal.Quotient.mk _ p : A) ⊗ₜ[R] (1 : B) :=
  toTensorAux_rename_inl W i j p

@[simp]
lemma biChartRingTensorEquiv_mk_rename_inr (p : MvPolynomial {k : Fin 3 // k ≠ j} R) :
    biChartRingTensorEquiv W i j (Ideal.Quotient.mk _ (rename Sum.inr p)) =
      (1 : A) ⊗ₜ[R] (Ideal.Quotient.mk _ p : B) :=
  toTensorAux_rename_inr W i j p

end WeierstrassCurve.Projective

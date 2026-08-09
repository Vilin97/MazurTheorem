/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck

This file adapts AINTLIB's `EllipticCurve/AdditionChartRing.lean`, exact source
blob `3d20f1bf04ca4e17618f896a044b77bb836e5ae2`. The source blob is present at
AINTLIB's Apache-2.0 licensed default commit
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`.
-/

import MazurTorsion.Upstream.AINTLIB.ForMathlib.WeierstrassAdditionJacobson
import MazurTorsion.Upstream.AINTLIB.ForMathlib.ProjectiveSpaceChart

/-!
# Chart-level curve points and the addition-law triples (T-W7.0c-c5β, β2)

The ring-level substrate for the `addOnZ`/`addOnY` morphisms. Everything here is presented
polynomial algebra — no schemes:

* `affineChartRing W i` — the chart ring of the projective model at `X i`, in its
  `chartCoordEquiv` presentation `R[u_j : j ≠ i] ⧸ (dehomogenised cubic)`;
* `affineChartPoint W i` — the tautological homogeneous coordinates (`1` at `i`), which
  satisfy the curve equation *by construction* (`equation_affineChartPoint`);
* `biChartRing W i j` — the presented coordinate ring of the `(i,j)` chart-product of
  `E ×_R E` (a 4-variable polynomial ring modulo the two dehomogenised cubics), with its
  two tautological points;
* the two Bosma–Lenstra triples evaluated at those points, and their **on-curve**
  statements `equation_dblAddXYZ_biChart` / `equation_addXYZ_biChart`, discharged from the
  c5α theorems whenever the chart-product ring is reduced and Jacobson (which the universal
  instantiation supplies — β2b; the scheme layer identifies `Spec (biChartRing …)` with the
  chart-products of the pullback — β1/β3).
-/

open MvPolynomial

namespace WeierstrassCurve.Projective

variable {R : Type*} [CommRing R]

/-! ## Single charts -/

/-- The chart ring of the projective model at `X i`, in the `chartCoordEquiv` presentation:
the plane coordinate ring modulo the dehomogenised cubic. -/
abbrev affineChartRing (W : WeierstrassCurve R) (i : Fin 3) : Type _ :=
  MvPolynomial {j : Fin 3 // j ≠ i} R ⧸
    Ideal.span {dehomogenizeAux R i W.toProjective.polynomial}

/-- The tautological homogeneous coordinates on chart `i`: `1` in slot `i`, the chart
generators elsewhere. -/
noncomputable def affineChartPoint (W : WeierstrassCurve R) (i : Fin 3) :
    Fin 3 → affineChartRing W i := fun j =>
  if h : j = i then 1 else Ideal.Quotient.mk _ (X ⟨j, h⟩)

/-- Tautology: evaluation of a homogeneous polynomial at the chart coordinates is the class
of its dehomogenisation. -/
lemma eval₂_affineChartPoint (W : WeierstrassCurve R) (i : Fin 3)
    (p : MvPolynomial (Fin 3) R) :
    eval₂ (algebraMap R (affineChartRing W i)) (affineChartPoint W i) p =
      Ideal.Quotient.mk _ (dehomogenizeAux R i p) := by
  have h : (eval₂Hom (algebraMap R (affineChartRing W i)) (affineChartPoint W i)) =
      (Ideal.Quotient.mk _).comp (dehomogenizeAux R i) := by
    refine ringHom_ext (fun r => ?_) (fun j => ?_)
    · simp [IsScalarTower.algebraMap_apply R (MvPolynomial {j : Fin 3 // j ≠ i} R)
        (affineChartRing W i), MvPolynomial.algebraMap_eq, Ideal.Quotient.algebraMap_eq]
    · by_cases hj : j = i
      · subst hj
        simp [affineChartPoint]
      · simp [affineChartPoint, hj]
  exact RingHom.congr_fun h p

/-- The tautological chart point lies on the curve. -/
lemma equation_affineChartPoint (W : WeierstrassCurve R) (i : Fin 3) :
    (W.map (algebraMap R (affineChartRing W i))).toProjective.Equation
      (affineChartPoint W i) := by
  rw [Equation, map_polynomial, eval_map, eval₂_affineChartPoint,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

/-! ## Chart products -/

/-- The presented coordinate ring of the `(i,j)` chart-product of `E ×_R E`: four variables
(the left chart's two and the right chart's two) modulo the two dehomogenised cubics. -/
abbrev biChartRing (W : WeierstrassCurve R) (i j : Fin 3) : Type _ :=
  MvPolynomial ({k : Fin 3 // k ≠ i} ⊕ {k : Fin 3 // k ≠ j}) R ⧸
    (Ideal.span {rename Sum.inl (dehomogenizeAux R i W.toProjective.polynomial),
      rename Sum.inr (dehomogenizeAux R j W.toProjective.polynomial)})

/-- The first tautological point of the chart-product (the left factor's coordinates). -/
noncomputable def biChartPointFst (W : WeierstrassCurve R) (i j : Fin 3) :
    Fin 3 → biChartRing W i j := fun k =>
  if h : k = i then 1 else Ideal.Quotient.mk _ (X (Sum.inl ⟨k, h⟩))

/-- The second tautological point of the chart-product (the right factor's coordinates). -/
noncomputable def biChartPointSnd (W : WeierstrassCurve R) (i j : Fin 3) :
    Fin 3 → biChartRing W i j := fun k =>
  if h : k = j then 1 else Ideal.Quotient.mk _ (X (Sum.inr ⟨k, h⟩))

lemma eval₂_biChartPointFst (W : WeierstrassCurve R) (i j : Fin 3)
    (p : MvPolynomial (Fin 3) R) :
    eval₂ (algebraMap R (biChartRing W i j)) (biChartPointFst W i j) p =
      Ideal.Quotient.mk _ (rename Sum.inl (dehomogenizeAux R i p)) := by
  have h : (eval₂Hom (algebraMap R (biChartRing W i j)) (biChartPointFst W i j)) =
      ((Ideal.Quotient.mk _).comp (rename Sum.inl).toRingHom).comp (dehomogenizeAux R i) := by
    refine ringHom_ext (fun r => ?_) (fun k => ?_)
    · simp [IsScalarTower.algebraMap_apply R
        (MvPolynomial ({k : Fin 3 // k ≠ i} ⊕ {k : Fin 3 // k ≠ j}) R) (biChartRing W i j),
        MvPolynomial.algebraMap_eq, Ideal.Quotient.algebraMap_eq]
    · by_cases hk : k = i
      · subst hk
        simp [biChartPointFst]
      · simp [biChartPointFst, hk]
  exact RingHom.congr_fun h p

lemma eval₂_biChartPointSnd (W : WeierstrassCurve R) (i j : Fin 3)
    (p : MvPolynomial (Fin 3) R) :
    eval₂ (algebraMap R (biChartRing W i j)) (biChartPointSnd W i j) p =
      Ideal.Quotient.mk _ (rename Sum.inr (dehomogenizeAux R j p)) := by
  have h : (eval₂Hom (algebraMap R (biChartRing W i j)) (biChartPointSnd W i j)) =
      ((Ideal.Quotient.mk _).comp (rename Sum.inr).toRingHom).comp (dehomogenizeAux R j) := by
    refine ringHom_ext (fun r => ?_) (fun k => ?_)
    · simp [IsScalarTower.algebraMap_apply R
        (MvPolynomial ({k : Fin 3 // k ≠ i} ⊕ {k : Fin 3 // k ≠ j}) R) (biChartRing W i j),
        MvPolynomial.algebraMap_eq, Ideal.Quotient.algebraMap_eq]
    · by_cases hk : k = j
      · subst hk
        simp [biChartPointSnd]
      · simp [biChartPointSnd, hk]
  exact RingHom.congr_fun h p

/-- The first tautological point lies on the curve. -/
lemma equation_biChartPointFst (W : WeierstrassCurve R) (i j : Fin 3) :
    (W.map (algebraMap R (biChartRing W i j))).toProjective.Equation (biChartPointFst W i j) := by
  rw [Equation, map_polynomial, eval_map, eval₂_biChartPointFst,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_insert _ _)

/-- The second tautological point lies on the curve. -/
lemma equation_biChartPointSnd (W : WeierstrassCurve R) (i j : Fin 3) :
    (W.map (algebraMap R (biChartRing W i j))).toProjective.Equation (biChartPointSnd W i j) := by
  rw [Equation, map_polynomial, eval_map, eval₂_biChartPointSnd,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

/-! ## The addition-law triples on a chart-product -/

variable (W : WeierstrassCurve R) (i j : Fin 3)

/-- The second Bosma–Lenstra law (the diagonal-covering one), evaluated at the tautological
points of the `(i,j)` chart-product. These three ring elements are the coordinates of the
would-be `addOnY` morphism on this chart-product. -/
noncomputable def lawTwoTriple : Fin 3 → biChartRing W i j :=
  (W.map (algebraMap R (biChartRing W i j))).toProjective.dblAddXYZ
    (biChartPointFst W i j) (biChartPointSnd W i j)

/-- The first Bosma–Lenstra law (mathlib's `addXYZ`), evaluated at the tautological points. -/
noncomputable def lawOneTriple : Fin 3 → biChartRing W i j :=
  (W.map (algebraMap R (biChartRing W i j))).toProjective.addXYZ
    (biChartPointFst W i j) (biChartPointSnd W i j)

/-- **(β2, law 2)** On a reduced Jacobson chart-product (e.g. over the universal atlas),
the second addition law lands on the curve: the input to the `addOnY` chart morphisms. -/
theorem equation_lawTwoTriple [IsReduced (biChartRing W i j)]
    [IsJacobsonRing (biChartRing W i j)] (hΔ : IsUnit W.Δ) :
    (W.map (algebraMap R (biChartRing W i j))).toProjective.Equation (lawTwoTriple W i j) :=
  equation_dblAddXYZ_of_isJacobsonRing (by rw [map_Δ]; exact hΔ.map _)
    (equation_biChartPointFst W i j) (equation_biChartPointSnd W i j)

/-- **(β2, law 1)** On a reduced Jacobson chart-product, the first addition law lands on the
curve: the input to the `addOnZ` chart morphisms. -/
theorem equation_lawOneTriple [IsReduced (biChartRing W i j)]
    [IsJacobsonRing (biChartRing W i j)] (hΔ : IsUnit W.Δ) :
    (W.map (algebraMap R (biChartRing W i j))).toProjective.Equation (lawOneTriple W i j) :=
  equation_addXYZ_of_isJacobsonRing (by rw [map_Δ]; exact hΔ.map _)
    (equation_biChartPointFst W i j) (equation_biChartPointSnd W i j)

end WeierstrassCurve.Projective

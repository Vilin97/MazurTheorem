/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Chris Birkbeck, AINTLIB ModularCurves contributors,
  OpenAI Codex
-/

import MazurTorsion.ModularCurve.XZeroGammaOneTateProjectiveChartAlgebra

/-!
# Points on projective Weierstrass charts

This file identifies points of a projective Weierstrass model that factor through a
standard coordinate chart with compatible ring homomorphisms from that chart.  It also
identifies those homomorphisms with solutions of the dehomogenized cubic and proves
that every field-valued point lies in one of the three charts.

The declarations are selectively adapted from AINTLIB's
`projects/ModularCurves/ModularCurves/EllipticCurve/WeierstrassModel.lean` at commit
`1c1c74664e40071c2c2165bc55ca2616a67ccd6b`, exact source blob
`0cea4fbbcd8f0976b8cb0949755ecacec6e58b26` (Chris Birkbeck, Apache-2.0).
They reuse the separately ported chart-coordinate equivalence and stop before chart
transitions or a global point dictionary.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial
open HomogeneousIdeal HomogeneousLocalization

namespace MazurTorsion.ModularCurve.XZeroModuli.GammaOneTate
namespace ProjectiveFamily

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R]

/-- The `K`-points of an `R`-scheme, as morphisms over `Spec R`. -/
def SpecPoints (X : Scheme.{u}) (f : X ⟶ Spec (.of R)) (K : Type u)
    [CommRing K] [Algebra R K] : Type u :=
  {g : Spec (.of K) ⟶ X // g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R K))}

/-- Every field-valued point of the projective model factors through one of its three
standard coordinate charts. -/
theorem specPoint_factors_through_chart (W : WeierstrassCurve R)
    {K : Type u} [Field K] [Algebra R K] (g : Spec (.of K) ⟶ model W) :
    ∃ (i : Fin 3) (h : Spec (.of K) ⟶
        Spec (.of (Away (quotientGrading (ideal W))
          ((quotientGradingHom (ideal W)) (MvPolynomial.X i))))),
      h ≫ Proj.awayι (quotientGrading (ideal W)) _
        (coordinateClass_mem_degreeOne W i) one_pos = g := by
  have htop := iSup_coordinateBasicOpen_eq_top W
  have hcover : (⋃ i : Fin 3, ((Proj.basicOpen (quotientGrading (ideal W))
      (Ideal.Quotient.mk (ideal W).toIdeal (MvPolynomial.X i))) :
        Set (Proj (quotientGrading (ideal W))))) = Set.univ := by
    have h := congrArg
      (fun U : (Proj (quotientGrading (ideal W))).Opens =>
        (U : Set (Proj (quotientGrading (ideal W))))) htop
    simpa only [TopologicalSpace.Opens.coe_iSup,
      TopologicalSpace.Opens.coe_top] using h
  have hmem : g.base default ∈ ⋃ i : Fin 3,
      ((Proj.basicOpen (quotientGrading (ideal W))
        (Ideal.Quotient.mk (ideal W).toIdeal (MvPolynomial.X i))) :
        Set (Proj (quotientGrading (ideal W)))) := by
    rw [hcover]
    exact Set.mem_univ _
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hmem
  refine ⟨i, IsOpenImmersion.lift
    (Proj.awayι (quotientGrading (ideal W)) _
      (coordinateClass_mem_degreeOne W i) one_pos) g ?_,
    IsOpenImmersion.lift_fac _ _ _⟩
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  have hy : y = default := Subsingleton.elim _ _
  subst hy
  have hrange : ((Proj.awayι (quotientGrading (ideal W)) _
      (coordinateClass_mem_degreeOne W i) one_pos).opensRange :
      TopologicalSpace.Opens (model W)) =
      Proj.basicOpen (quotientGrading (ideal W))
        (Ideal.Quotient.mk (ideal W).toIdeal (MvPolynomial.X i)) :=
    Proj.opensRange_awayι _ _ _ _
  have : g.base default ∈ (Proj.awayι (quotientGrading (ideal W)) _
      (coordinateClass_mem_degreeOne W i) one_pos).opensRange := by
    rw [hrange]
    exact hi
  exact this

private theorem ringHom_eq_aeval {σ : Type} {K : Type u} [CommRing K] [Algebra R K]
    (χ : MvPolynomial σ R →+* K)
    (hχ : ∀ r, χ (MvPolynomial.C r) = algebraMap R K r)
    (p : MvPolynomial σ R) :
    χ p = MvPolynomial.aeval (fun j => χ (MvPolynomial.X j)) p := by
  have hχ' : ∀ r, χ (algebraMap R (MvPolynomial σ R) r) = algebraMap R K r := by
    intro r
    rw [MvPolynomial.algebraMap_eq]
    exact hχ r
  have h := MvPolynomial.aeval_unique (⟨χ, hχ'⟩ : MvPolynomial σ R →ₐ[R] K)
  calc
    χ p = (⟨χ, hχ'⟩ : MvPolynomial σ R →ₐ[R] K) p := rfl
    _ = _ := by rw [h]; rfl

/-- Evaluation of a chart homomorphism is polynomial evaluation at the images of the
two dehomogenized coordinates. -/
theorem chart_hom_aeval (W : WeierstrassCurve R) (i : Fin 3) {K : Type u}
    [CommRing K] [Algebra R K]
    (φ : Away (quotientGrading (ideal W))
      ((quotientGradingHom (ideal W)) (MvPolynomial.X i)) →+* K)
    (hφ : φ.comp ((algebraMap (↥(quotientGrading (ideal W) 0))
        (Away (quotientGrading (ideal W))
          ((quotientGradingHom (ideal W)) (MvPolynomial.X i)))).comp
      ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (ideal W) 0))) =
      algebraMap R K)
    (p : MvPolynomial {j : Fin 3 // j ≠ i} R) :
    φ (chartCoordEquiv W i (Ideal.Quotient.mk
        (Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial}) p)) =
      MvPolynomial.aeval (fun j => φ (chartCoordEquiv W i (Ideal.Quotient.mk
        (Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial})
        (MvPolynomial.X j)))) p := by
  refine ringHom_eq_aeval (φ.comp (((chartCoordEquiv W i) :
    MvPolynomial {j : Fin 3 // j ≠ i} R ⧸
      Ideal.span {MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial} →+*
      Away (quotientGrading (ideal W))
        ((quotientGradingHom (ideal W)) (MvPolynomial.X i))).comp
    (Ideal.Quotient.mk _))) (fun r => ?_) p
  change φ (chartCoordEquiv W i (Ideal.Quotient.mk _ (MvPolynomial.C r))) = _
  rw [chartCoordEquiv_mk_C]
  exact RingHom.congr_fun hφ r

private def ringHomPrecompEquiv {A B C : Type*} [Semiring A] [Semiring B]
    [Semiring C] (e : A ≃+* B) : (B →+* C) ≃ (A →+* C) where
  toFun φ := φ.comp (e : A →+* B)
  invFun ψ := ψ.comp (e.symm : B →+* A)
  left_inv φ := RingHom.ext fun x => by simp
  right_inv ψ := RingHom.ext fun x => by simp

private noncomputable def quotSolutionsEquiv {i : Fin 3}
    (F : MvPolynomial {j : Fin 3 // j ≠ i} R)
    (K : Type u) [CommRing K] [Algebra R K] :
    {ψ : (MvPolynomial {j : Fin 3 // j ≠ i} R ⧸ Ideal.span {F}) →+* K //
      ∀ r, ψ (Ideal.Quotient.mk (Ideal.span {F}) (MvPolynomial.C r)) =
        algebraMap R K r} ≃
    {v : {j : Fin 3 // j ≠ i} → K // MvPolynomial.aeval v F = 0} where
  toFun ψ := ⟨fun j => ψ.1 (Ideal.Quotient.mk _ (MvPolynomial.X j)), by
    have hzero := ringHom_eq_aeval
      (ψ.1.comp (Ideal.Quotient.mk (Ideal.span {F}))) (fun r => ψ.2 r) F
    rw [show (ψ.1.comp (Ideal.Quotient.mk (Ideal.span {F}))) F =
      ψ.1 0 from congrArg ψ.1 (Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton_self _)), map_zero] at hzero
    exact hzero.symm⟩
  invFun v := ⟨Ideal.Quotient.lift (Ideal.span {F})
      ((MvPolynomial.aeval v.1 : MvPolynomial {j : Fin 3 // j ≠ i} R →ₐ[R] K) :
        MvPolynomial {j : Fin 3 // j ≠ i} R →+* K)
      (fun a ha => by
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
        simp only [RingHom.coe_coe, map_mul, v.2, zero_mul]), fun r => by
    rw [Ideal.Quotient.lift_mk]
    simp⟩
  left_inv ψ := by
    refine Subtype.ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun p => ?_))
    simp only [RingHom.comp_apply, Ideal.Quotient.lift_mk]
    exact (ringHom_eq_aeval (ψ.1.comp (Ideal.Quotient.mk (Ideal.span {F})))
      (fun r => ψ.2 r) p).symm
  right_inv v := by
    refine Subtype.ext (funext fun j => ?_)
    simp only [Ideal.Quotient.lift_mk, RingHom.coe_coe, MvPolynomial.aeval_X]

/-- Compatible ring homomorphisms from a projective chart are precisely the solutions
of its dehomogenized Weierstrass equation. -/
noncomputable def chartSolutionsEquiv (W : WeierstrassCurve R) (i : Fin 3)
    (K : Type u) [CommRing K] [Algebra R K] :
    {φ : Away (quotientGrading (ideal W))
        ((quotientGradingHom (ideal W)) (MvPolynomial.X i)) →+* K //
      φ.comp ((algebraMap (↥(quotientGrading (ideal W) 0))
          (Away (quotientGrading (ideal W))
            ((quotientGradingHom (ideal W)) (MvPolynomial.X i)))).comp
        ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (ideal W) 0))) =
        algebraMap R K} ≃
    {v : {j : Fin 3 // j ≠ i} → K //
      MvPolynomial.aeval v
        (MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial) = 0} :=
  (Equiv.subtypeEquiv (ringHomPrecompEquiv (chartCoordEquiv W i)) (fun φ => by
    constructor
    · intro h r
      change φ (chartCoordEquiv W i _) = _
      rw [chartCoordEquiv_mk_C]
      exact RingHom.congr_fun h r
    · intro h
      refine RingHom.ext fun r => ?_
      have hr := h r
      rw [show (ringHomPrecompEquiv (chartCoordEquiv W i) φ)
          (Ideal.Quotient.mk _ (MvPolynomial.C r)) =
          φ (chartCoordEquiv W i (Ideal.Quotient.mk _ (MvPolynomial.C r))) from rfl,
        chartCoordEquiv_mk_C] at hr
      exact hr)).trans
    (quotSolutionsEquiv (MvPolynomial.dehomogenizeAux R i W.toProjective.polynomial) K)

/-- Restricted to one coordinate chart, the model projection is `Spec` of the chart's
coefficient-ring map. -/
theorem awayι_projection (W : WeierstrassCurve R) (i : Fin 3) :
    Proj.awayι (quotientGrading (ideal W))
      ((quotientGradingHom (ideal W)) (MvPolynomial.X i))
      (coordinateClass_mem_degreeOne W i) one_pos ≫ projection W =
      Spec.map (CommRingCat.ofHom
        ((algebraMap (↥(quotientGrading (ideal W) 0))
          (Away (quotientGrading (ideal W))
            ((quotientGradingHom (ideal W)) (MvPolynomial.X i)))).comp
        ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (ideal W) 0)))) := by
  change Proj.awayι _ _ _ _ ≫ Proj.toSpecZero (quotientGrading (ideal W)) ≫
    Spec.map (CommRingCat.ofHom (algebraMapGradeZero (ideal W))) = _
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

private noncomputable def chartPointOfHom (W : WeierstrassCurve R) (i : Fin 3)
    {K : Type u} [CommRing K] [Algebra R K]
    (φ : {φ : Away (quotientGrading (ideal W))
        ((quotientGradingHom (ideal W)) (MvPolynomial.X i)) →+* K //
      φ.comp ((algebraMap (↥(quotientGrading (ideal W) 0))
          (Away (quotientGrading (ideal W))
            ((quotientGradingHom (ideal W)) (MvPolynomial.X i)))).comp
        ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (ideal W) 0))) =
        algebraMap R K}) :
    {g : SpecPoints (model W) (projection W) K //
      ∃ h : Spec (.of K) ⟶ Spec (.of (Away (quotientGrading (ideal W))
          ((quotientGradingHom (ideal W)) (MvPolynomial.X i)))),
        h ≫ Proj.awayι (quotientGrading (ideal W)) _
          (coordinateClass_mem_degreeOne W i) one_pos = g.1} :=
  ⟨⟨Spec.map (CommRingCat.ofHom φ.1) ≫ Proj.awayι _ _
      (coordinateClass_mem_degreeOne W i) one_pos, by
    rw [Category.assoc, awayι_projection W i, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, φ.2]⟩, ⟨Spec.map (CommRingCat.ofHom φ.1), rfl⟩⟩

private theorem chartPointOfHom_bijective (W : WeierstrassCurve R) (i : Fin 3)
    {K : Type u} [CommRing K] [Algebra R K] :
    Function.Bijective (chartPointOfHom W i (K := K)) := by
  constructor
  · intro φ₁ φ₂ h
    have hmaps : Spec.map (CommRingCat.ofHom φ₁.1) ≫ Proj.awayι _ _
        (coordinateClass_mem_degreeOne W i) one_pos =
        Spec.map (CommRingCat.ofHom φ₂.1) ≫ Proj.awayι _ _
          (coordinateClass_mem_degreeOne W i) one_pos :=
      congrArg (fun g => g.1.1) h
    have hspec := Spec.map_injective ((cancel_mono _).mp hmaps)
    exact Subtype.ext (congrArg CommRingCat.Hom.hom hspec)
  · rintro ⟨⟨g, hg⟩, h, hfac⟩
    have hπ : (h ≫ Proj.awayι (quotientGrading (ideal W)) _
        (coordinateClass_mem_degreeOne W i) one_pos) ≫ projection W =
        Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
      rw [hfac]
      exact hg
    rw [Category.assoc, awayι_projection W i, ← Spec.map_preimage h,
      ← Spec.map_comp] at hπ
    have hcond := congrArg CommRingCat.Hom.hom (Spec.map_injective hπ)
    refine ⟨⟨(Spec.preimage h).hom, hcond⟩, ?_⟩
    refine Subtype.ext (Subtype.ext ?_)
    change Spec.map (CommRingCat.ofHom (Spec.preimage h).hom) ≫ _ = g
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    exact hfac

/-- Points over `Spec R` that factor through a chosen coordinate chart are equivalent
to compatible ring homomorphisms from that chart. -/
noncomputable def chartHomEquiv (W : WeierstrassCurve R) (i : Fin 3)
    (K : Type u) [CommRing K] [Algebra R K] :
    {g : SpecPoints (model W) (projection W) K //
      ∃ h : Spec (.of K) ⟶ Spec (.of (Away (quotientGrading (ideal W))
          ((quotientGradingHom (ideal W)) (MvPolynomial.X i)))),
        h ≫ Proj.awayι (quotientGrading (ideal W)) _
          (coordinateClass_mem_degreeOne W i) one_pos = g.1} ≃
    {φ : Away (quotientGrading (ideal W))
        ((quotientGradingHom (ideal W)) (MvPolynomial.X i)) →+* K //
      φ.comp ((algebraMap (↥(quotientGrading (ideal W) 0))
          (Away (quotientGrading (ideal W))
            ((quotientGradingHom (ideal W)) (MvPolynomial.X i)))).comp
        ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (ideal W) 0))) =
        algebraMap R K} :=
  (Equiv.ofBijective _ (chartPointOfHom_bijective W i (K := K))).symm

/-- A chart point represented by `Spec.map φ` is read back as `φ`. -/
theorem chartHomEquiv_eq_of_specMap (W : WeierstrassCurve R) (i : Fin 3)
    {K : Type u} [CommRing K] [Algebra R K]
    (g : {g : SpecPoints (model W) (projection W) K //
      ∃ h : Spec (.of K) ⟶ Spec (.of (Away (quotientGrading (ideal W))
          ((quotientGradingHom (ideal W)) (MvPolynomial.X i)))),
        h ≫ Proj.awayι (quotientGrading (ideal W)) _
          (coordinateClass_mem_degreeOne W i) one_pos = g.1})
    (φ : {φ : Away (quotientGrading (ideal W))
        ((quotientGradingHom (ideal W)) (MvPolynomial.X i)) →+* K //
      φ.comp ((algebraMap (↥(quotientGrading (ideal W) 0))
          (Away (quotientGrading (ideal W))
            ((quotientGradingHom (ideal W)) (MvPolynomial.X i)))).comp
        ((gradeZeroRingEquiv W) : R →+* ↥(quotientGrading (ideal W) 0))) =
        algebraMap R K})
    (hfac : Spec.map (CommRingCat.ofHom φ.1) ≫ Proj.awayι
        (quotientGrading (ideal W)) _
        (coordinateClass_mem_degreeOne W i) one_pos = g.1.1) :
    chartHomEquiv W i K g = φ := by
  have hpt : chartPointOfHom W i φ = g := Subtype.ext (Subtype.ext hfac)
  rw [chartHomEquiv, ← hpt]
  exact (Equiv.ofBijective _
    (chartPointOfHom_bijective W i (K := K))).symm_apply_apply φ

/-- The homomorphism read from a chart-factoring point represents that point through
the chart immersion. -/
theorem chartHomEquiv_specMap_factors (W : WeierstrassCurve R) (i : Fin 3)
    {K : Type u} [CommRing K] [Algebra R K]
    (g : {g : SpecPoints (model W) (projection W) K //
      ∃ h : Spec (.of K) ⟶ Spec (.of (Away (quotientGrading (ideal W))
          ((quotientGradingHom (ideal W)) (MvPolynomial.X i)))),
        h ≫ Proj.awayι (quotientGrading (ideal W)) _
          (coordinateClass_mem_degreeOne W i) one_pos = g.1}) :
    Spec.map (CommRingCat.ofHom (chartHomEquiv W i K g).1) ≫
        Proj.awayι (quotientGrading (ideal W)) _
          (coordinateClass_mem_degreeOne W i) one_pos = g.1.1 :=
  congrArg (fun z => (z : {g : SpecPoints (model W) (projection W) K //
      ∃ h : Spec (.of K) ⟶ Spec (.of (Away (quotientGrading (ideal W))
          ((quotientGradingHom (ideal W)) (MvPolynomial.X i)))),
        h ≫ Proj.awayι (quotientGrading (ideal W)) _
          (coordinateClass_mem_degreeOne W i) one_pos = g.1}).1.1)
    ((Equiv.ofBijective _
      (chartPointOfHom_bijective W i (K := K))).apply_symm_apply g)

end ProjectiveFamily
end MazurTorsion.ModularCurve.XZeroModuli.GammaOneTate

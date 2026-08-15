/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.SmoothCurveReduced
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Graph components in base changes of étale coordinates

An étale affine coordinate has open-and-closed diagonal.  After replacing
one factor by an arbitrary algebra over the coordinate chart, the same
splitting selects the graph of that algebra map as the first coproduct
summand.  This is the scheme-level form needed to retain the genuine curve
incidence sheet and discard the complementary equal-coordinate sheets.

The named downstream consumer is the local fpqc incidence comparison in
`PointedIncidenceDescent`.
-/

noncomputable section

universe u

open scoped TensorProduct
open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.EtaleGraphCoproduct

/-- Any open-and-closed immersion exhibits its target as the coproduct of
its source and the complementary open subscheme. -/
theorem exists_coproduct_of_isOpenImmersion_isClosedImmersion
    {X Y : Scheme.{u}} (h : X ⟶ Y) [IsOpenImmersion h]
    [IsClosedImmersion h] :
    ∃ (W : Scheme.{u}) (E : Y ≅ X ⨿ W), h ≫ E.hom = coprod.inl := by
  let W : Y.Opens :=
    ⟨h.opensRangeᶜ, h.isClosedMap.isClosed_range.isOpen_compl⟩
  have hCompl : IsCompl h.opensRange W.ι.opensRange := by
    simp [isCompl_iff, disjoint_iff, codisjoint_iff, W, SetLike.ext'_iff]
  obtain ⟨H⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl
    h W.ι hCompl
  let E : Y ≅ X ⨿ W.toScheme :=
    H.coconePointUniqueUpToIso (colimit.isColimit (pair X W.toScheme))
  refine ⟨W.toScheme, E, ?_⟩
  change h ≫ E.hom = colimit.ι (pair X W.toScheme) ⟨WalkingPair.left⟩
  exact H.comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit (pair X W.toScheme)) ⟨WalkingPair.left⟩

/-- Base-change an arbitrary subspace of `pullback f g` along `π`, then
identify the resulting iterated pullback with `pullback f (π ≫ g)`. -/
noncomputable def baseChangedComponentInclusion
    {U N S B P : Scheme.{u}} (f : U ⟶ S) (g : N ⟶ S)
    (π : B ⟶ N) (j : P ⟶ pullback f g) :
    pullback (j ≫ pullback.snd f g) π ⟶ pullback f (π ≫ g) :=
  ((pullbackRightPullbackFstIso (pullback.snd f g) π j).inv ≫
    pullback.snd j (pullback.fst (pullback.snd f g) π)) ≫
      (pullbackLeftPullbackSndIso f g π).hom

@[reassoc]
theorem baseChangedComponentInclusion_fst
    {U N S B P : Scheme.{u}} (f : U ⟶ S) (g : N ⟶ S)
    (π : B ⟶ N) (j : P ⟶ pullback f g) :
    baseChangedComponentInclusion f g π j ≫ pullback.fst f (π ≫ g) =
      pullback.fst (j ≫ pullback.snd f g) π ≫
        j ≫ pullback.fst f g := by
  simp only [baseChangedComponentInclusion, Category.assoc,
    pullbackLeftPullbackSndIso_hom_fst, ← pullback.condition_assoc,
    pullbackRightPullbackFstIso_inv_fst_assoc]

@[reassoc]
theorem baseChangedComponentInclusion_snd
    {U N S B P : Scheme.{u}} (f : U ⟶ S) (g : N ⟶ S)
    (π : B ⟶ N) (j : P ⟶ pullback f g) :
    baseChangedComponentInclusion f g π j ≫ pullback.snd f (π ≫ g) =
      pullback.snd (j ≫ pullback.snd f g) π := by
  simp only [baseChangedComponentInclusion, Category.assoc,
    pullbackLeftPullbackSndIso_hom_snd,
    pullbackRightPullbackFstIso_inv_snd_snd]

instance baseChangedComponentInclusion_isOpenImmersion
    {U N S B P : Scheme.{u}} (f : U ⟶ S) (g : N ⟶ S)
    (π : B ⟶ N) (j : P ⟶ pullback f g) [IsOpenImmersion j] :
    IsOpenImmersion (baseChangedComponentInclusion f g π j) := by
  let p := pullback.snd j (pullback.fst (pullback.snd f g) π)
  haveI : IsOpenImmersion p :=
    MorphismProperty.pullback_snd (P := @IsOpenImmersion) _ _
      (show IsOpenImmersion j from inferInstance)
  change IsOpenImmersion
    ((pullbackRightPullbackFstIso (pullback.snd f g) π j).inv ≫ p ≫
      (pullbackLeftPullbackSndIso f g π).hom)
  infer_instance

instance baseChangedComponentInclusion_isClosedImmersion
    {U N S B P : Scheme.{u}} (f : U ⟶ S) (g : N ⟶ S)
    (π : B ⟶ N) (j : P ⟶ pullback f g) [IsClosedImmersion j] :
    IsClosedImmersion (baseChangedComponentInclusion f g π j) := by
  let p := pullback.snd j (pullback.fst (pullback.snd f g) π)
  haveI : IsClosedImmersion p :=
    IsClosedImmersion.isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback j (pullback.fst (pullback.snd f g) π))
      (show IsClosedImmersion j from inferInstance)
  change IsClosedImmersion
    ((pullbackRightPullbackFstIso (pullback.snd f g) π j).inv ≫ p ≫
      (pullbackLeftPullbackSndIso f g π).hom)
  infer_instance

/-- The graph of a morphism into a separated étale scheme is an
open-and-closed summand after arbitrary base change.  This scheme-level
version avoids choosing affine presentations of the source of the graph. -/
theorem exists_graphCoproduct_of_etale
    {X S B : Scheme.{u}} (f : X ⟶ S) [Etale f] [IsSeparated f]
    (q : B ⟶ S) (h : B ⟶ X) (w : h ≫ f = q) :
    let graph : B ⟶ pullback f q :=
      pullback.lift h (𝟙 B) (by simpa using w)
    ∃ (W : Scheme.{u}) (E : pullback f q ≅ B ⨿ W),
      graph ≫ E.hom = coprod.inl := by
  subst q
  let graph' : B ⟶ pullback (h ≫ f) f :=
    pullback.lift (𝟙 B) h (by simp)
  have hGraphPullback := pullback_lift_diagonal_isPullback h f
  let graph : B ⟶ pullback f (h ≫ f) :=
    pullback.lift h (𝟙 B) (by simp)
  have hGraph : graph = graph' ≫ (pullbackSymmetry f (h ≫ f)).inv := by
    apply pullback.hom_ext
    · simp only [graph, graph', pullback.lift_fst, Category.assoc,
        pullbackSymmetry_inv_comp_fst, pullback.lift_snd]
    · simp only [graph, graph', pullback.lift_snd, Category.assoc,
        pullbackSymmetry_inv_comp_snd, pullback.lift_fst]
  haveI : IsOpenImmersion graph' :=
    MorphismProperty.of_isPullback hGraphPullback inferInstance
  haveI : IsClosedImmersion graph' := inferInstance
  haveI : IsOpenImmersion graph := by
    rw [hGraph]
    infer_instance
  haveI : IsClosedImmersion graph := by
    rw [hGraph]
    infer_instance
  exact exists_coproduct_of_isOpenImmersion_isClosedImmersion graph

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]

/-- Evaluation on the graph of `Spec B → Spec A` inside the base change
`Spec A ×_{Spec R} Spec B`. -/
noncomputable def graphEvaluation : A ⊗[R] B →ₐ[R] B :=
  Algebra.TensorProduct.lift
    (IsScalarTower.toAlgHom R A B) (AlgHom.id R B) fun _ _ ↦ .all _ _

@[simp]
theorem graphEvaluation_tmul (a : A) (b : B) :
    graphEvaluation R A B (a ⊗ₜ[R] b) = algebraMap A B a * b := by
  simp [graphEvaluation]

/-- The categorical graph map agrees with affine-spectrum evaluation on the
tensor-product coordinate ring. -/
theorem graph_eq_SpecMap :
    let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let q := Spec.map (CommRingCat.ofHom (algebraMap R B))
    let h := Spec.map (CommRingCat.ofHom (algebraMap A B))
    let graph : Spec (.of B) ⟶ pullback f q :=
      pullback.lift h (𝟙 _) (by
        rw [Category.id_comp, ← Spec.map_comp, Spec.map_inj]
        exact CommRingCat.hom_ext (IsScalarTower.algebraMap_eq R A B).symm)
    graph =
      Spec.map (CommRingCat.ofHom (graphEvaluation R A B).toRingHom) ≫
        (pullbackSpecIso R A B).inv := by
  dsimp only
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.assoc, pullbackSpecIso_inv_fst,
      ← Spec.map_comp, Spec.map_inj]
    apply CommRingCat.hom_ext
    apply RingHom.ext fun a ↦ ?_
    simp [graphEvaluation]
  · rw [pullback.lift_snd, Category.assoc, pullbackSpecIso_inv_snd,
      ← Spec.map_comp, ← Spec.map_id, Spec.map_inj]
    apply CommRingCat.hom_ext
    apply RingHom.ext fun b ↦ ?_
    simp [graphEvaluation]

/-- After arbitrary base change on one factor, the graph of an étale
coordinate map is exactly the first summand of a coproduct decomposition of
the fiber product. -/
theorem exists_graphCoproduct [Algebra.Etale R A] :
    let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
    let q := Spec.map (CommRingCat.ofHom (algebraMap R B))
    let h := Spec.map (CommRingCat.ofHom (algebraMap A B))
    let graph : Spec (.of B) ⟶ pullback f q :=
      pullback.lift h (𝟙 _) (by
        rw [Category.id_comp, ← Spec.map_comp, Spec.map_inj]
        exact CommRingCat.hom_ext (IsScalarTower.algebraMap_eq R A B).symm)
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra A T)
      (E : pullback f q ≅
        Spec (.of B) ⨿ Spec (.of (B ⊗[A] T))),
      graph ≫ E.hom = coprod.inl := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let q := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let h := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let graph : Spec (.of B) ⟶ pullback f q :=
    pullback.lift h (𝟙 _) (by
      rw [Category.id_comp, ← Spec.map_comp, Spec.map_inj]
      exact CommRingCat.hom_ext (IsScalarTower.algebraMap_eq R A B).symm)
  obtain ⟨T, _, _, e, he⟩ :=
    SmoothCurveReduced.etale_coordinateBaseChange_exists_graphProduct R A B
  let e' : A ⊗[R] B ≃+* B × (B ⊗[A] T) :=
    (Algebra.TensorProduct.comm R A B).toRingEquiv.trans e.toRingEquiv
  let eSpec : Spec (.of (A ⊗[R] B)) ≅
      Spec (.of (B × (B ⊗[A] T))) :=
    (Scheme.Spec.mapIso e'.toCommRingCatIso.op).symm
  let E : pullback f q ≅ Spec (.of B) ⨿ Spec (.of (B ⊗[A] T)) :=
    pullbackSpecIso R A B ≪≫ eSpec ≪≫ (asIso (coprodSpec B (B ⊗[A] T))).symm
  refine ⟨T, inferInstance, inferInstance, E, ?_⟩
  apply (cancel_mono (coprodSpec B (B ⊗[A] T))).mp
  change graph ≫ E.hom ≫ coprodSpec B (B ⊗[A] T) =
    coprod.inl ≫ coprodSpec B (B ⊗[A] T)
  rw [coprodSpec_inl]
  rw [show graph =
      Spec.map (CommRingCat.ofHom (graphEvaluation R A B).toRingHom) ≫
        (pullbackSpecIso R A B).inv from graph_eq_SpecMap R A B]
  dsimp only [E]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc,
    Iso.inv_hom_id_assoc, IsIso.inv_hom_id, Category.comp_id]
  dsimp only [eSpec]
  change Spec.map (CommRingCat.ofHom (graphEvaluation R A B).toRingHom) ≫
      Spec.map e'.symm.toCommRingCatIso.hom =
    Spec.map (CommRingCat.ofHom (RingHom.fst B (B ⊗[A] T)))
  rw [← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  apply RingHom.ext fun z ↦ ?_
  change graphEvaluation R A B (e'.symm z) = z.1
  have hcompat (x : B ⊗[R] A) :
      graphEvaluation R A B
          ((Algebra.TensorProduct.comm R A B).symm x) = (e x).1 := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, Prod.fst_add]
    | tmul b a =>
      rw [he]
      simp [graphEvaluation, mul_comm]
  exact (hcompat (e.symm z)).trans
    (congrArg Prod.fst (e.apply_symm_apply z))

end MazurTorsion.AlgebraicGeometry.Jacobian.EtaleGraphCoproduct

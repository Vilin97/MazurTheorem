/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FiniteTranslationQuotientGroup
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Adjoin.Tower

/-!
# Geometry of a finite translation quotient group scheme

This file proves geometric properties of the actual finite-action quotient constructed by
AINTLIB after it has been equipped with the descended commutative group law. The base is an
affine locally noetherian scheme Spec R; no quotient scheme or geometric property is supplied
as data.

The finite-type argument is the Artin--Tate lemma on the affine quotient atlas. Geometric
reducedness descends through the finite étale surjection by injectivity on stalks, and geometric
irreducibility descends through its surjective underlying map. For separatedness, the pullback
of the quotient diagonal along the product fpqc cover is the relation E ×_(E/G) E ⟶ E ×_S E.
This relation is proper because its source is proper over S and its target is separated over S;
universal closedness then descends along the product cover.

The Artin--Tate step uses Mathlib's fg_of_fg_of_fg (Atiyah--Macdonald, Proposition 7.8;
Stacks Project, Tag 00IS). The finite quotient, torsor, and quotient-chart results are the
Apache-2.0 AINTLIB port recorded in the imported quotient modules.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace AlgebraicGeometry

/-- A reduced source descends reducedness through a flat surjective morphism.

At a point of the target, choose a point above it.  Flatness of the local homomorphism together
with its being local makes the stalk extension faithfully flat, hence injective. -/
theorem isReduced_of_flat_of_surjective_source {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [Surjective f] [IsReduced X] : IsReduced Y := by
  refine @isReduced_of_isReduced_stalk Y ?_
  intro y
  obtain ⟨x, rfl⟩ := f.surjective y
  apply isReduced_of_injective (f.stalkMap x).hom
  algebraize [(f.stalkMap x).hom]
  have : Module.FaithfullyFlat
      (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  exact ‹RingHom.FaithfullyFlat _›.injective

/-- Affine Artin--Tate cancellation for a finite flat surjective cover of the source. -/
theorem locallyOfFiniteType_of_finite_flat_surjective_comp_affine
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [IsAffine X] [IsAffine Y] [IsAffine S] [IsLocallyNoetherian S]
    [IsFinite f] [Flat f] [Surjective f] [LocallyOfFiniteType (f ≫ g)] :
    LocallyOfFiniteType g := by
  letI : IsNoetherianRing Γ(S, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)]
  have hAC : (f.appTop.hom.comp g.appTop.hom).FiniteType := by
    simpa only [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop] using
      (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp
        (inferInstance : LocallyOfFiniteType (f ≫ g))
  have hBC : f.appTop.hom.Finite := f.finite_appTop
  have hBCfaithful : f.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp
      ⟨inferInstance, inferInstance⟩
  algebraize [g.appTop.hom, f.appTop.hom, f.appTop.hom.comp g.appTop.hom]
  exact ⟨fg_of_fg_of_fg
    (A := Γ(S, ⊤)) (B := Γ(Y, ⊤)) (C := Γ(X, ⊤))
    Algebra.FiniteType.out Module.Finite.fg_top
    (FaithfulSMul.algebraMap_injective Γ(Y, ⊤) Γ(X, ⊤))⟩

/-- Flatness cancels a faithfully flat map on the target. -/
private theorem ringHom_flat_of_comp_faithfullyFlat
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (hf : (g.comp f).Flat)
    (hg : g.FaithfullyFlat) : f.Flat := by
  algebraize [f, g, g.comp f]
  change Module.Flat R S
  rw [Module.Flat.iff_lTensor_injectiveₛ]
  intro N _ _ P
  let h := P.subtype
  have hh : Function.Injective h := Subtype.val_injective
  change Function.Injective
    (TensorProduct.AlgebraTensorModule.lTensor S S h)
  apply (Module.FaithfullyFlat.lTensor_injective_iff_injective S T
    (TensorProduct.AlgebraTensorModule.lTensor S S h)).mp
  change Function.Injective (TensorProduct.AlgebraTensorModule.lTensor T T
    (TensorProduct.AlgebraTensorModule.lTensor S S h))
  let eN := TensorProduct.AlgebraTensorModule.cancelBaseChange R S S T P
  let eN' := TensorProduct.AlgebraTensorModule.cancelBaseChange R S S T N
  have hdirect : Function.Injective
      (TensorProduct.AlgebraTensorModule.lTensor S T h) :=
    Module.Flat.lTensor_preserves_injective_linearMap h hh
  have hleft : Function.Injective
      ((TensorProduct.AlgebraTensorModule.lTensor S T h).comp eN.toLinearMap) :=
    hdirect.comp eN.injective
  have heq := TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange
    R S S (M := T) h
  have hright : Function.Injective
      (eN'.toLinearMap.comp (TensorProduct.AlgebraTensorModule.lTensor S T
        (TensorProduct.AlgebraTensorModule.lTensor S S h))) := by
    rw [← heq]
    exact hleft
  have hgoal : Function.Injective
      (TensorProduct.AlgebraTensorModule.lTensor S T
        (TensorProduct.AlgebraTensorModule.lTensor S S h)) :=
    fun _ _ hab ↦ hright (congrArg eN' hab)
  simpa only [TensorProduct.AlgebraTensorModule.coe_lTensor] using hgoal

/-- Flatness descends through a flat surjective cover of the source. -/
private theorem flat_of_flat_surjective_comp {X Y Z : Scheme.{u}}
    (q : X ⟶ Y) (p : Y ⟶ Z) [Flat q] [Surjective q] [Flat (q ≫ p)] :
    Flat p := by
  apply Flat.of_stalkMap p
  intro y
  obtain ⟨x, rfl⟩ := q.surjective y
  apply ringHom_flat_of_comp_faithfullyFlat
    (p.stalkMap (q x)).hom (q.stalkMap x).hom
  · rw [← CommRingCat.hom_comp, ← Scheme.Hom.stalkMap_comp]
    exact Flat.stalkMap (q ≫ p) x
  · algebraize [(q.stalkMap x).hom]
    exact @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap q x) (q.toLRSHom.prop x)

namespace FiniteTranslationQuotient

variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G] [hGfinite : Finite G]
variable
  (E : CommGroupScheme (Spec (.of R)))
  (sections : G →* (𝟙_ (Over (Spec (.of R))) ⟶ E.X))
  [hDiagonalAffine : IsAffineHom (pullback.diagonal (terminal.from E.X.left))]
  (V : E.X.left → E.X.left.Opens)
  (hVs : ∀ x, (translationAction E sections).IsStableOpen (V x))
  (hVa : ∀ x, IsAffineOpen (V x))
  (hVmem : ∀ x, x ∈ V x)
  (hfree : ∀ g : G, g ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ E.X.left),
    t ≫ (translationAction E sections).hom g = t → IsEmpty T)

include hGfinite hDiagonalAffine

include hfree in
/-- The structure morphism of the actual quotient is geometrically reduced. -/
theorem structureMap_geometricallyReduced [GeometricallyReduced E.X.hom] :
    GeometricallyReduced (structureMap E sections V hVs hVa hVmem) := by
  let q := projection E sections V hVs hVa hVmem
  let p := structureMap E sections V hVs hVa hVmem
  letI : Etale q := projection_etale E sections V hVs hVa hVmem hfree
  letI : Surjective q := projection_surjective E sections V hVs hVa hVmem
  have hqp : q ≫ p = E.X.hom :=
    projection_comp_structureMap E sections V hVs hVa hVmem
  letI : GeometricallyReduced (q ≫ p) := by
    rw [hqp]
    infer_instance
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun L _ y ↦ ?_⟩
  let qL : pullback q (pullback.fst p y) ⟶ pullback p y :=
    pullback.snd q (pullback.fst p y)
  letI : Flat qL := MorphismProperty.pullback_snd _ _ (inferInstanceAs (Flat q))
  letI : Surjective qL :=
    MorphismProperty.pullback_snd _ _ (inferInstanceAs (Surjective q))
  have hsourceComposite : IsReduced (pullback (q ≫ p) y) :=
    GeometricallyReduced.geometrically_isReduced _ _ _ (.of_hasPullback _ _)
  have hsource : IsReduced (pullback q (pullback.fst p y)) :=
    ObjectProperty.prop_of_iso (IsReduced ·)
      (pullbackRightPullbackFstIso p y q).symm hsourceComposite
  letI : IsReduced (pullback q (pullback.fst p y)) := hsource
  exact isReduced_of_flat_of_surjective_source qL

/-- The structure morphism of the actual quotient is geometrically irreducible. -/
theorem structureMap_geometricallyIrreducible [GeometricallyIrreducible E.X.hom] :
    GeometricallyIrreducible (structureMap E sections V hVs hVa hVmem) := by
  let q := projection E sections V hVs hVa hVmem
  let p := structureMap E sections V hVs hVa hVmem
  letI : Surjective q := projection_surjective E sections V hVs hVa hVmem
  have hqp : q ≫ p = E.X.hom :=
    projection_comp_structureMap E sections V hVs hVa hVmem
  letI : GeometricallyIrreducible (q ≫ p) := by
    rw [hqp]
    infer_instance
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun L _ y ↦ ?_⟩
  let qL : pullback q (pullback.fst p y) ⟶ pullback p y :=
    pullback.snd q (pullback.fst p y)
  letI : Surjective qL :=
    MorphismProperty.pullback_snd _ _ (inferInstanceAs (Surjective q))
  have hsourceComposite : IrreducibleSpace ↥(pullback (q ≫ p) y) :=
    GeometricallyIrreducible.geometrically_irreducibleSpace _ _ _ (.of_hasPullback _ _)
  have hsource : IrreducibleSpace ↥(pullback q (pullback.fst p y)) :=
    ObjectProperty.prop_of_iso (fun X : Scheme.{u} ↦ IrreducibleSpace ↥X)
      (pullbackRightPullbackFstIso p y q).symm hsourceComposite
  letI : IrreducibleSpace ↥(pullback q (pullback.fst p y)) := hsource
  exact Function.Surjective.irreducibleSpace qL.continuous qL.surjective

include hfree in
/-- The structure morphism of the actual quotient is geometrically integral. -/
theorem structureMap_geometricallyIntegral [GeometricallyIntegral E.X.hom] :
    GeometricallyIntegral (structureMap E sections V hVs hVa hVmem) := by
  letI : GeometricallyReduced (structureMap E sections V hVs hVa hVmem) :=
    structureMap_geometricallyReduced E sections V hVs hVa hVmem hfree
  letI : GeometricallyIrreducible (structureMap E sections V hVs hVa hVmem) :=
    structureMap_geometricallyIrreducible E sections V hVs hVa hVmem
  exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _

include hfree in
/-- The structure morphism of the actual quotient is locally of finite type.

This is checked on AINTLIB's affine quotient charts.  Their inverse images are the chosen affine
opens of `E`, and the chart projection is finite, flat, and surjective. -/
theorem structureMap_locallyOfFiniteType [IsNoetherianRing R]
    [LocallyOfFiniteType E.X.hom] :
    LocallyOfFiniteType (structureMap E sections V hVs hVa hVmem) := by
  letI : IsZariskiLocalAtSource
      (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := @RingHom.FiniteType)
  let σ := translationAction E sections
  let q := projection E sections V hVs hVa hVmem
  let p := structureMap E sections V hVs hVa hVmem
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @LocallyOfFiniteType)
    (fun x ↦ σ.quotientChart V hVs hVa x) (σ.iSup_quotientChart_eq_top V hVs hVa)]
  intro x
  let U := σ.quotientChart V hVs hVa x
  let f : (V x : Scheme.{u}) ⟶ U :=
    σ.localQuotientπ (hVs x) (hVa x) ≫ (σ.quotientChartIso V hVs hVa x).hom
  let g : (U : Scheme.{u}) ⟶ Spec (.of R) := U.ι ≫ p
  letI : IsAffine (V x : Scheme.{u}) := hVa x
  letI : IsAffine U := σ.isAffineOpen_quotientChart V hVs hVa x
  letI : IsFinite q := projection_isFinite E sections V hVs hVa hVmem hfree
  letI : Etale q := projection_etale E sections V hVs hVa hVmem hfree
  letI : Surjective q := projection_surjective E sections V hVs hVa hVmem
  have hpb : IsPullback (V x).ι f q U.ι := by
    simpa only [σ, q, U, f] using
      σ.isPullback_quotientπ_quotientChart V hVs hVa hVmem x
  letI : IsFinite f := MorphismProperty.of_isPullback hpb (inferInstanceAs (IsFinite q))
  letI : Flat f := MorphismProperty.of_isPullback hpb (inferInstanceAs (Flat q))
  letI : Surjective f :=
    MorphismProperty.of_isPullback hpb (inferInstanceAs (Surjective q))
  have hfg : f ≫ g = (V x).ι ≫ E.X.hom := by
    calc
      f ≫ g = (V x).ι ≫ q ≫ p := by
        simpa only [f, g, U, q, Category.assoc] using
          congrArg (fun k ↦ k ≫ p)
            (σ.localQuotientπ_quotientChartIso V hVs hVa hVmem x)
      _ = (V x).ι ≫ E.X.hom := by
        simpa only [q, p] using
          congrArg (fun k ↦ (V x).ι ≫ k)
            (projection_comp_structureMap E sections V hVs hVa hVmem)
  letI : LocallyOfFiniteType (f ≫ g) := by
    rw [hfg]
    infer_instance
  exact locallyOfFiniteType_of_finite_flat_surjective_comp_affine f g

include hfree in
/-- Flatness of the source structure morphism descends to the actual quotient. -/
theorem structureMap_flat [Flat E.X.hom] :
    Flat (structureMap E sections V hVs hVa hVmem) := by
  let q := projection E sections V hVs hVa hVmem
  let p := structureMap E sections V hVs hVa hVmem
  letI : Etale q := projection_etale E sections V hVs hVa hVmem hfree
  letI : Surjective q := projection_surjective E sections V hVs hVa hVmem
  have hqp : q ≫ p = E.X.hom :=
    projection_comp_structureMap E sections V hVs hVa hVmem
  letI : Flat (q ≫ p) := by
    rw [hqp]
    infer_instance
  exact flat_of_flat_surjective_comp q p

include hfree in
/-- The structure morphism of the actual quotient is separated. -/
theorem structureMap_isSeparated [IsProper E.X.hom] :
    IsSeparated (structureMap E sections V hVs hVa hVmem) := by
  let q := projection E sections V hVs hVa hVmem
  let p := structureMap E sections V hVs hVa hVmem
  let r := pullback.mapDesc q q p
  let c := pullback.map (q ≫ p) (q ≫ p) p p q q (𝟙 _)
    (Category.comp_id _) (Category.comp_id _)
  let d := pullback.diagonal p
  let sR := pullback.fst q q ≫ (q ≫ p)
  let sT := pullback.fst (q ≫ p) (q ≫ p) ≫ (q ≫ p)
  letI : IsFinite q := projection_isFinite E sections V hVs hVa hVmem hfree
  letI : Etale q := projection_etale E sections V hVs hVa hVmem hfree
  letI : Surjective q := projection_surjective E sections V hVs hVa hVmem
  have hqp : q ≫ p = E.X.hom :=
    projection_comp_structureMap E sections V hVs hVa hVmem
  letI : IsProper (q ≫ p) := by
    rw [hqp]
    infer_instance
  letI : IsProper sR := by
    dsimp only [sR]
    infer_instance
  letI : IsProper sT := by
    dsimp only [sT]
    infer_instance
  have hrs : r ≫ sT = sR := by
    dsimp only [r, sT, sR, pullback.mapDesc, pullback.map]
    simp only [Category.assoc, pullback.lift_fst_assoc, Category.id_comp]
  letI : IsProper (r ≫ sT) := by
    rw [hrs]
    infer_instance
  letI : IsSeparated sT := IsProper.toIsSeparated
  letI : IsProper r := IsProper.of_comp r sT
  have hr : UniversallyClosed r := inferInstance
  letI : MorphismProperty.IsStableUnderComposition
      (@Surjective : MorphismProperty Scheme.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative
      (@Surjective : MorphismProperty Scheme.{u})).toIsStableUnderComposition
  letI : MorphismProperty.RespectsIso
      (@UniversallyClosed : MorphismProperty Scheme.{u}) :=
    universallyClosed_respectsIso
  have hcSurjective : Surjective c := by
    dsimp only [c]
    exact MorphismProperty.pullbackMap (P := @Surjective)
      (inferInstanceAs (Surjective q)) (inferInstanceAs (Surjective q)) rfl rfl
  have hcFlat : Flat c := by
    dsimp only [c]
    exact MorphismProperty.pullbackMap (P := @Flat)
      (inferInstanceAs (Flat q)) (inferInstanceAs (Flat q)) rfl rfl
  have hcQuasiCompact : QuasiCompact c := by
    dsimp only [c]
    exact MorphismProperty.pullbackMap (P := @QuasiCompact)
      (inferInstanceAs (QuasiCompact q)) (inferInstanceAs (QuasiCompact q)) rfl rfl
  have hc : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) c :=
    ⟨⟨hcSurjective, hcFlat⟩, hcQuasiCompact⟩
  have hpb : IsPullback (pullback.fst q q ≫ q) r d c := by
    simpa only [r, c, d] using pullback_map_diagonal_isPullback q q p
  have hcanonical : UniversallyClosed (pullback.fst c d) := by
    exact (MorphismProperty.cancel_left_of_respectsIso @UniversallyClosed
      hpb.flip.isoPullback.hom (pullback.fst c d)).mp
        (by simpa only [hpb.flip.isoPullback_hom_fst] using hr)
  have hd : UniversallyClosed d :=
    MorphismProperty.of_pullback_fst_of_descendsAlong
      (P := @UniversallyClosed)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hc hcanonical
  letI : UniversallyClosed d := hd
  haveI : IsClosedImmersion d :=
    IsClosedImmersion.of_isPreimmersion d d.isClosedMap.isClosed_range
  exact ⟨inferInstance⟩

include hfree in
/-- The structure morphism of the actual quotient is proper. -/
theorem structureMap_isProper [IsNoetherianRing R] [IsProper E.X.hom] :
    IsProper (structureMap E sections V hVs hVa hVmem) := by
  let q := projection E sections V hVs hVa hVmem
  let p := structureMap E sections V hVs hVa hVmem
  letI : Surjective q := projection_surjective E sections V hVs hVa hVmem
  have hqp : q ≫ p = E.X.hom :=
    projection_comp_structureMap E sections V hVs hVa hVmem
  letI : UniversallyClosed (q ≫ p) := by
    rw [hqp]
    infer_instance
  letI : UniversallyClosed p := UniversallyClosed.of_comp_surjective q p
  letI : IsSeparated p :=
    structureMap_isSeparated E sections V hVs hVa hVmem hfree
  letI : LocallyOfFiniteType p :=
    structureMap_locallyOfFiniteType E sections V hVs hVa hVmem hfree
  exact ⟨⟩

include hfree in
/-- A flat, geometrically reduced source gives a smooth actual quotient over a noetherian
affine base.  The descended group law makes every geometric fiber smooth. -/
theorem structureMap_smooth_of_flat [IsNoetherianRing R] [Flat E.X.hom]
    [LocallyOfFiniteType E.X.hom] [GeometricallyReduced E.X.hom] :
    Smooth (structureMap E sections V hVs hVa hVmem) := by
  let p := structureMap E sections V hVs hVa hVmem
  letI : GrpObj (Over.mk p) := by
    change GrpObj (asOver E sections V hVs hVa hVmem)
    exact quotientGrpObj E sections V hVs hVa hVmem hfree
  letI : Flat p := structureMap_flat E sections V hVs hVa hVmem hfree
  letI : LocallyOfFiniteType p :=
    structureMap_locallyOfFiniteType E sections V hVs hVa hVmem hfree
  letI : LocallyOfFinitePresentation p := inferInstance
  letI : GeometricallyReduced p :=
    structureMap_geometricallyReduced E sections V hVs hVa hVmem hfree
  apply Smooth.of_smooth_fiberToSpecResidueField p
  intro y
  letI : LocallyOfFiniteType (p.fiberToSpecResidueField y) := by
    change LocallyOfFiniteType (pullback.snd p _)
    infer_instance
  letI : GeometricallyReduced (p.fiberToSpecResidueField y) := by
    change GeometricallyReduced (pullback.snd p _)
    infer_instance
  letI : GrpObj (Over.mk (p.fiberToSpecResidueField y)) :=
    Over.grpObjMkPullbackSnd
  exact @smooth_of_grpObj _ inferInstance _ (p.fiberToSpecResidueField y)
    (inferInstanceAs (LocallyOfFiniteType (p.fiberToSpecResidueField y)))
    (inferInstanceAs (GrpObj (Over.mk (p.fiberToSpecResidueField y))))
    (inferInstanceAs (GeometricallyReduced (p.fiberToSpecResidueField y)))

end FiniteTranslationQuotient
end AlgebraicGeometry

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FiniteTranslationQuotientGroup
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Adjoin.Tower
import TauCeti.AlgebraicGeometry.AbelianVariety.Basic

/-!
# Geometry of a finite translation quotient of an abelian variety

This file proves that the actual finite-action quotient constructed by AINTLIB, after it has
been equipped with the descended commutative group law, is again an abelian variety.  No quotient
scheme or geometric property is supplied as data.

The finite-type argument is the Artin--Tate lemma on the affine quotient atlas.  Geometric
reducedness descends through the finite étale surjection by injectivity on stalks, and geometric
irreducibility descends through its surjective underlying map.  For separatedness, the pullback
of the quotient diagonal along the product fpqc cover is the relation
`E ×_(E/G) E ⟶ E ×_S E`.  This relation is proper because its source is proper over `S`
and its target is separated over `S`; universal closedness then descends along the product cover.

The Artin--Tate step uses Mathlib's `fg_of_fg_of_fg` (Atiyah--Macdonald, Proposition 7.8;
Stacks Project, Tag 00IS).  The finite quotient, torsor, and quotient-chart results are the
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

namespace FiniteTranslationQuotient

variable {K : Type u} [Field K]
variable {G : Type u} [Group G] [hGfinite : Finite G]
variable
  (E : CommGroupScheme (Spec (.of K)))
  (sections : G →* (𝟙_ (Over (Spec (.of K))) ⟶ E.X))
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
theorem structureMap_locallyOfFiniteType [LocallyOfFiniteType E.X.hom] :
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
  let g : (U : Scheme.{u}) ⟶ Spec (.of K) := U.ι ≫ p
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
theorem structureMap_isProper [IsProper E.X.hom] :
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
/-- The group-scheme structure makes the geometrically reduced quotient smooth. -/
theorem structureMap_smooth [IsProper E.X.hom] [GeometricallyIntegral E.X.hom] :
    Smooth (structureMap E sections V hVs hVa hVmem) := by
  letI : GrpObj (asOver E sections V hVs hVa hVmem) :=
    quotientGrpObj E sections V hVs hVa hVmem hfree
  letI : GrpObj (Over.mk (asOver E sections V hVs hVa hVmem).hom) := by
    change GrpObj (asOver E sections V hVs hVa hVmem)
    exact quotientGrpObj E sections V hVs hVa hVmem hfree
  letI : LocallyOfFiniteType (asOver E sections V hVs hVa hVmem).hom := by
    change LocallyOfFiniteType (structureMap E sections V hVs hVa hVmem)
    exact structureMap_locallyOfFiniteType E sections V hVs hVa hVmem hfree
  letI : GeometricallyReduced (asOver E sections V hVs hVa hVmem).hom := by
    change GeometricallyReduced (structureMap E sections V hVs hVa hVmem)
    exact structureMap_geometricallyReduced E sections V hVs hVa hVmem hfree
  change Smooth (asOver E sections V hVs hVa hVmem).hom
  exact smooth_of_grpObj (asOver E sections V hVs hVa hVmem).hom

include hfree in
/-- The actual finite translation quotient, bundled as an abelian variety. -/
noncomputable def abelianVariety [IsProper E.X.hom] [GeometricallyIntegral E.X.hom] :
    TauCeti.AlgebraicGeometry.AbelianVariety K := by
  let Q := commGroupScheme E sections V hVs hVa hVmem hfree
  letI : GrpObj Q.X := Q.grp
  letI : IsProper Q.X.hom := by
    change IsProper (structureMap E sections V hVs hVa hVmem)
    exact structureMap_isProper E sections V hVs hVa hVmem hfree
  letI : GeometricallyIntegral Q.X.hom := by
    change GeometricallyIntegral (structureMap E sections V hVs hVa hVmem)
    exact structureMap_geometricallyIntegral E sections V hVs hVa hVmem hfree
  exact TauCeti.AlgebraicGeometry.AbelianVariety.ofGeometricallyIntegral
    Q.X

@[simp]
theorem abelianVariety_toOver [IsProper E.X.hom] [GeometricallyIntegral E.X.hom] :
    (abelianVariety E sections V hVs hVa hVmem hfree).toOver =
      (commGroupScheme E sections V hVs hVa hVmem hfree).X :=
  rfl

/-- The genuine quotient projection, now regarded as a homomorphism to the abelian quotient. -/
noncomputable def projectionToAbelianVariety
    [IsProper E.X.hom] [GeometricallyIntegral E.X.hom] :
    E ⟶ CommGrp.mk (abelianVariety E sections V hVs hVa hVmem hfree).toOver :=
  projectionHom E sections V hVs hVa hVmem hfree

/-! ## Consumer for an existing abelian variety -/

variable
  (A : TauCeti.AlgebraicGeometry.AbelianVariety K)
  (abelianSections :
    G →* (𝟙_ (Over (Spec (.of K))) ⟶ (CommGrp.mk A.toOver).X))
  [IsAffineHom
    (pullback.diagonal (terminal.from (CommGrp.mk A.toOver).X.left))]
  (abelianV : (CommGrp.mk A.toOver).X.left →
    (CommGrp.mk A.toOver).X.left.Opens)
  (abelianVs : ∀ x,
    (translationAction (CommGrp.mk A.toOver) abelianSections).IsStableOpen (abelianV x))
  (abelianVa : ∀ x, IsAffineOpen (abelianV x))
  (abelianVmem : ∀ x, x ∈ abelianV x)
  (abelianFree : ∀ g : G, g ≠ 1 →
    ∀ (T : Scheme.{u}) (t : T ⟶ (CommGrp.mk A.toOver).X.left),
      t ≫ (translationAction (CommGrp.mk A.toOver) abelianSections).hom g = t →
        IsEmpty T)

/-- A finite free translation quotient of an actual abelian variety is an actual abelian
variety, constructed from the quotient rather than supplied as quotient data. -/
noncomputable def abelianVarietyOfAbelianVariety :
    TauCeti.AlgebraicGeometry.AbelianVariety K :=
  abelianVariety (CommGrp.mk A.toOver) abelianSections abelianV
    abelianVs abelianVa abelianVmem abelianFree

/-- The quotient projection for `abelianVarietyOfAbelianVariety`. -/
noncomputable def projectionOfAbelianVariety :
    CommGrp.mk A.toOver ⟶
      CommGrp.mk (abelianVarietyOfAbelianVariety A abelianSections abelianV
        abelianVs abelianVa abelianVmem abelianFree).toOver :=
  projectionToAbelianVariety (CommGrp.mk A.toOver) abelianSections abelianV
    abelianVs abelianVa abelianVmem abelianFree

end FiniteTranslationQuotient
end AlgebraicGeometry

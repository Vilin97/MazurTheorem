/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Vasily Ilin, Codex
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SheafCechInjectiveAugmentation

/-!
# Degree-one Cech comparison through an injective bicomplex

Construct the horizontal edge from global sections of the chosen injective
resolution. For an actual cover, left exactness of global sections transfers
the sheaf-level Cech resolution to exact low rows, so the horizontal and
vertical edge quasi-isomorphisms identify degree-one Cech homology with
genuine sheaf cohomology.  The augmented native short complex, its exactness,
and monicity of its augmentation are public because the project-level
degree-zero Cech comparison consumes precisely this left-exact boundary.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

noncomputable section

variable {X : TopCat.{u}}
variable {ι : Type u} (U : ι → Opens X)

noncomputable local instance : (globalSectionsFunctor X).Additive :=
  (CategoryTheory.constantSheafΓAdj
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).right_adjoint_additive

noncomputable local instance :
    (globalSectionsFunctor X).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive (F := globalSectionsFunctor X)

/-- Global sections applied degreewise to the chosen injective resolution. -/
private noncomputable def cechInjectiveResolutionGlobalSectionsComplex
    (F : Sheaf AddCommGrpCat.{u} X) :
    CochainComplex AddCommGrpCat.{u} ℕ :=
  ((globalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).obj
    (injectiveResolution (toSiteSheaf F)).cocomplex

private noncomputable def cechInjectiveResolutionGlobalSectionsMap
    {F G : Sheaf AddCommGrpCat.{u} X}
    (phi : (injectiveResolution (toSiteSheaf F)).cocomplex ⟶
      (injectiveResolution (toSiteSheaf G)).cocomplex) :
    cechInjectiveResolutionGlobalSectionsComplex F ⟶
      cechInjectiveResolutionGlobalSectionsComplex G :=
  ((globalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).map phi

@[simp]
private theorem cechInjectiveResolutionGlobalSectionsMap_f
    {F G : Sheaf AddCommGrpCat.{u} X}
    (phi : (injectiveResolution (toSiteSheaf F)).cocomplex ⟶
      (injectiveResolution (toSiteSheaf G)).cocomplex) (q : ℕ) :
    (cechInjectiveResolutionGlobalSectionsMap phi).f q =
      (globalSectionsFunctor X).map (phi.f q) :=
  rfl

/-- The row augmentation from global sections of the resolution to native
Cech degree zero. -/
private noncomputable def cechInjectiveResolutionHorizontalAugmentation
    (F : Sheaf AddCommGrpCat.{u} X) (q : ℕ) :
    (cechInjectiveResolutionGlobalSectionsComplex F).X q ⟶
      ((cechInjectiveResolutionBicomplex U F).X q).X 0 :=
  cechGlobalSectionsAugmentation
    ((injectiveResolution (toSiteSheaf F)).cocomplex.X q) U

@[simp]
private theorem cechInjectiveResolutionHorizontalAugmentation_eq
    (F : Sheaf AddCommGrpCat.{u} X) (q : ℕ) :
    cechInjectiveResolutionHorizontalAugmentation U F q =
      cechGlobalSectionsAugmentation
        ((injectiveResolution (toSiteSheaf F)).cocomplex.X q) U :=
  rfl

private theorem cechInjectiveResolutionHorizontalAugmentation_comm
    (F : Sheaf AddCommGrpCat.{u} X) (q q' : ℕ)
    (_ : (ComplexShape.up ℕ).Rel q q') :
    cechInjectiveResolutionHorizontalAugmentation U F q ≫
        ((cechInjectiveResolutionBicomplex U F).d q q').f 0 =
      (cechInjectiveResolutionGlobalSectionsComplex F).d q q' ≫
        cechInjectiveResolutionHorizontalAugmentation U F q' := by
  let I := injectiveResolution (toSiteSheaf F)
  change cechGlobalSectionsAugmentation (I.cocomplex.X q) U ≫
      ((cechComplexFunctor U).map (I.cocomplex.d q q').hom).f 0 =
    (globalSectionsFunctor X).map (I.cocomplex.d q q') ≫
      cechGlobalSectionsAugmentation (I.cocomplex.X q') U
  exact cechGlobalSectionsAugmentation_naturality
    (U := U) (F := I.cocomplex.X q) (I.cocomplex.d q q')

private theorem cechInjectiveResolutionHorizontalAugmentation_comp_d
    (F : Sheaf AddCommGrpCat.{u} X) (q : ℕ) :
    cechInjectiveResolutionHorizontalAugmentation U F q ≫
      ((cechInjectiveResolutionBicomplex U F).X q).d 0 1 = 0 := by
  let I := injectiveResolution (toSiteSheaf F)
  change cechGlobalSectionsAugmentation (I.cocomplex.X q) U ≫
    ((cechComplexFunctor U).obj (I.cocomplex.X q).obj).d 0 1 = 0
  exact cechGlobalSectionsAugmentation_comp_d (I.cocomplex.X q) U

/-- The native Cech short complex augmented by global sections. -/
noncomputable def cechGlobalSectionsNativeShortComplex
    (F : Sheaf AddCommGrpCat.{u} X) :
    ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk (cechGlobalSectionsAugmentation F U)
    (((cechComplexFunctor U).obj F.obj).d 0 1)
    (cechGlobalSectionsAugmentation_comp_d F U)

private noncomputable def cechGlobalSectionsMappedAugmentedShortComplex
    (F : Sheaf AddCommGrpCat.{u} X) :
    ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk
    ((globalSectionsFunctor X).map (cechAugmentation F U))
    ((globalSectionsFunctor X).map (cechDifferential F U 0))
    (by
      have hzero : cechAugmentation F U ≫ cechDifferential F U 0 = 0 :=
        cechAugmentation_comp F U
      calc
        _ = (globalSectionsFunctor X).map
            (cechAugmentation F U ≫ cechDifferential F U 0) :=
          ((globalSectionsFunctor X).map_comp _ _).symm
        _ = (globalSectionsFunctor X).map 0 :=
          congrArg (globalSectionsFunctor X).map hzero
        _ = 0 := (globalSectionsFunctor X).map_zero _ _)

private theorem cechGlobalSections_map_augmented_exact_and_mono
    (F : Sheaf AddCommGrpCat.{u} X) (hU : ⨆ i, U i = ⊤) :
    (cechGlobalSectionsMappedAugmentedShortComplex U F).Exact ∧
      Mono ((globalSectionsFunctor X).map (cechAugmentation F U)) := by
  let S := cechAugmentedShortComplex F U
  have hS : S.Exact := cechAugmentedShortComplex_exact F U hU
  have hmono : Mono S.f := by
    change Mono (cechAugmentation F U)
    exact cechAugmentation_mono F U hU
  have hmap := (((Functor.preservesFiniteLimits_tfae
    (globalSectionsFunctor X)).out 3 1 rfl rfl).mp
      (inferInstance : PreservesFiniteLimits (globalSectionsFunctor X)))
        S ⟨hS, hmono⟩
  refine ⟨?_, by simpa [S, cechAugmentedShortComplex] using hmap.2⟩
  have hex := (ShortComplex.ab_exact_iff _).mp hmap.1
  rw [ShortComplex.ab_exact_iff]
  intro x hx
  exact hex x hx

/-- The native Cech short complex augmented by global sections is exact for an
open cover. -/
theorem cechGlobalSectionsNativeShortComplex_exact
    (F : Sheaf AddCommGrpCat.{u} X) (hU : ⨆ i, U i = ⊤) :
    (cechGlobalSectionsNativeShortComplex U F).Exact := by
  let S := cechAugmentedShortComplex F U
  have hmap := cechGlobalSections_map_augmented_exact_and_mono U F hU
  have hcomm := (cechGlobalSectionsComplexIso F U).hom.comm 0 1
  change (cechGlobalSectionsXIso F U 0).hom ≫
      ((cechComplexFunctor U).obj F.obj).d 0 1 =
    (globalSectionsFunctor X).map (cechDifferential F U 0) ≫
      (cechGlobalSectionsXIso F U 1).hom at hcomm
  let e : cechGlobalSectionsMappedAugmentedShortComplex U F ≅
      cechGlobalSectionsNativeShortComplex U F :=
    ShortComplex.isoMk (Iso.refl _)
      (cechGlobalSectionsXIso F U 0)
      (cechGlobalSectionsXIso F U 1)
      (by
        change 𝟙 _ ≫ ((globalSectionsFunctor X).map
            (cechAugmentation F U) ≫
              (cechGlobalSectionsXIso F U 0).hom) =
          (globalSectionsFunctor X).map (cechAugmentation F U) ≫
            (cechGlobalSectionsXIso F U 0).hom
        rw [Category.id_comp]) hcomm
  exact ShortComplex.exact_of_iso e hmap.1

/-- The native Cech augmentation on global sections is monic for an open cover. -/
theorem cechGlobalSectionsAugmentation_mono
    (F : Sheaf AddCommGrpCat.{u} X) (hU : ⨆ i, U i = ⊤) :
    Mono (cechGlobalSectionsAugmentation F U) := by
  have hmap := cechGlobalSections_map_augmented_exact_and_mono U F hU
  letI : Mono ((globalSectionsFunctor X).map
      (cechAugmentation F U)) := hmap.2
  change Mono ((globalSectionsFunctor X).map (cechAugmentation F U) ≫
    (cechGlobalSectionsXIso F U 0).hom)
  infer_instance

/-- The horizontal edge from global sections of the injective resolution to
the total injective Cech bicomplex. -/
private noncomputable def cechInjectiveResolutionHorizontalEdge
    (F : Sheaf AddCommGrpCat.{u} X) :
    cechInjectiveResolutionGlobalSectionsComplex F ⟶
      (cechInjectiveResolutionBicomplex U F).total (.up ℕ) :=
  (cechInjectiveResolutionBicomplex U F).totalUpNatHorizontalEdge
    (cechInjectiveResolutionGlobalSectionsComplex F)
    (cechInjectiveResolutionHorizontalAugmentation U F)
    (cechInjectiveResolutionHorizontalAugmentation_comm U F)
    (cechInjectiveResolutionHorizontalAugmentation_comp_d U F)

@[simp]
private theorem cechInjectiveResolutionHorizontalEdge_f
    (F : Sheaf AddCommGrpCat.{u} X) (q : ℕ) :
    (cechInjectiveResolutionHorizontalEdge U F).f q =
      cechInjectiveResolutionHorizontalAugmentation U F q ≫
        (cechInjectiveResolutionBicomplex U F).ιTotal
          (.up ℕ) q 0 q rfl := by
  apply HomologicalComplex₂.totalUpNatHorizontalEdge_f

private theorem cechInjectiveResolutionHorizontalEdge_naturality
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (phi : InjectiveResolution.Hom
      (injectiveResolution (toSiteSheaf F))
      (injectiveResolution (toSiteSheaf G)) f) :
    cechInjectiveResolutionGlobalSectionsMap phi.hom ≫
        cechInjectiveResolutionHorizontalEdge U G =
      cechInjectiveResolutionHorizontalEdge U F ≫
        cechInjectiveResolutionTotalMap U phi.hom := by
  apply HomologicalComplex.Hom.ext
  funext q
  have hAug :
      cechInjectiveResolutionHorizontalAugmentation U F q ≫
          ((cechInjectiveResolutionBicomplexMap U phi.hom).f q).f 0 =
          (cechInjectiveResolutionGlobalSectionsMap phi.hom).f q ≫
          cechInjectiveResolutionHorizontalAugmentation U G q := by
    rw [cechInjectiveResolutionBicomplexMap_f_f,
      cechInjectiveResolutionGlobalSectionsMap_f,
      cechInjectiveResolutionHorizontalAugmentation_eq,
      cechInjectiveResolutionHorizontalAugmentation_eq]
    exact cechGlobalSectionsAugmentation_naturality
      (U := U) (f := phi.hom.f q)
  simp only [HomologicalComplex.comp_f,
    cechInjectiveResolutionHorizontalEdge_f]
  rw [Category.assoc, cechInjectiveResolutionTotalMap,
    HomologicalComplex₂.ιTotal_map]
  simp only [← Category.assoc]
  rw [hAug]

private theorem cechInjectiveResolution_row_exactAt_one
    (F : Sheaf AddCommGrpCat.{u} X) (hU : ⨆ i, U i = ⊤) :
    (ShortComplex.mk
      (((cechInjectiveResolutionBicomplex U F).X 0).d 0 1)
      (((cechInjectiveResolutionBicomplex U F).X 0).d 1 2)).Exact := by
  apply (HomologicalComplex.exactAt_iff'
    ((cechInjectiveResolutionBicomplex U F).X 0)
      0 1 2 (by simp) (by simp)).1
  exact cechInjectiveResolutionBicomplex_row_exactAt_one U F hU 0

/-- For a genuine cover, the horizontal edge is a quasi-isomorphism in degree
one. -/
private theorem cechInjectiveResolutionHorizontalEdge_quasiIsoAt_one
    (F : Sheaf AddCommGrpCat.{u} X) (hU : ⨆ i, U i = ⊤) :
    QuasiIsoAt (cechInjectiveResolutionHorizontalEdge U F) 1 := by
  let I := injectiveResolution (toSiteSheaf F)
  letI : Mono (cechInjectiveResolutionHorizontalAugmentation U F 1) := by
    change Mono (cechGlobalSectionsAugmentation (I.cocomplex.X 1) U)
    exact cechGlobalSectionsAugmentation_mono U (I.cocomplex.X 1) hU
  letI : Mono (cechInjectiveResolutionHorizontalAugmentation U F 2) := by
    change Mono (cechGlobalSectionsAugmentation (I.cocomplex.X 2) U)
    exact cechGlobalSectionsAugmentation_mono U (I.cocomplex.X 2) hU
  apply HomologicalComplex₂.totalUpNatHorizontalEdge_quasiIsoAt_one
  · change (cechGlobalSectionsNativeShortComplex U
      (I.cocomplex.X 0)).Exact
    exact cechGlobalSectionsNativeShortComplex_exact U (I.cocomplex.X 0) hU
  · change (cechGlobalSectionsNativeShortComplex U
      (I.cocomplex.X 1)).Exact
    exact cechGlobalSectionsNativeShortComplex_exact U (I.cocomplex.X 1) hU
  · exact cechInjectiveResolution_row_exactAt_one U F hU

private noncomputable def cechInjectiveResolutionVerticalHomologyIso
    (F : Sheaf AddCommGrpCat.{u} X)
    (hH : ∀ i : ι, Subsingleton (CategoryTheory.Sheaf.H
      ((restrict AddCommGrpCat (U i).isOpenEmbedding).obj F) 1)) :
    ((cechComplexFunctor U).obj F.obj).homology 1 ≅
      ((cechInjectiveResolutionBicomplex U F).total (.up ℕ)).homology 1 := by
  letI : QuasiIsoAt (cechInjectiveResolutionVerticalEdge U F) 1 :=
    cechInjectiveResolutionVerticalEdge_quasiIsoAt_one U F hH
  exact asIso (HomologicalComplex.homologyMap
    (cechInjectiveResolutionVerticalEdge U F) 1)

@[simp]
private theorem cechInjectiveResolutionVerticalHomologyIso_hom
    (F : Sheaf AddCommGrpCat.{u} X)
    (hH : ∀ i : ι, Subsingleton (CategoryTheory.Sheaf.H
      ((restrict AddCommGrpCat (U i).isOpenEmbedding).obj F) 1)) :
    (cechInjectiveResolutionVerticalHomologyIso U F hH).hom =
      HomologicalComplex.homologyMap
        (cechInjectiveResolutionVerticalEdge U F) 1 :=
  rfl

private noncomputable def cechInjectiveResolutionHorizontalHomologyIso
    (F : Sheaf AddCommGrpCat.{u} X) (hU : ⨆ i, U i = ⊤) :
    (cechInjectiveResolutionGlobalSectionsComplex F).homology 1 ≅
      ((cechInjectiveResolutionBicomplex U F).total (.up ℕ)).homology 1 := by
  letI : QuasiIsoAt (cechInjectiveResolutionHorizontalEdge U F) 1 :=
    cechInjectiveResolutionHorizontalEdge_quasiIsoAt_one U F hU
  exact asIso (HomologicalComplex.homologyMap
    (cechInjectiveResolutionHorizontalEdge U F) 1)

@[simp]
private theorem cechInjectiveResolutionHorizontalHomologyIso_hom
    (F : Sheaf AddCommGrpCat.{u} X) (hU : ⨆ i, U i = ⊤) :
    (cechInjectiveResolutionHorizontalHomologyIso U F hU).hom =
      HomologicalComplex.homologyMap
        (cechInjectiveResolutionHorizontalEdge U F) 1 :=
  rfl

private noncomputable def cechHomologyOneRightDerivedIso_of_subsingleton_H
    (F : Sheaf AddCommGrpCat.{u} X) (hU : ⨆ i, U i = ⊤)
    (hH : ∀ i : ι, Subsingleton (CategoryTheory.Sheaf.H
      ((restrict AddCommGrpCat (U i).isOpenEmbedding).obj F) 1)) :
    ((cechComplexFunctor U).obj F.obj).homology 1 ≅
      ((globalSectionsFunctor X).rightDerived 1).obj (toSiteSheaf F) :=
  cechInjectiveResolutionVerticalHomologyIso U F hH ≪≫
    (cechInjectiveResolutionHorizontalHomologyIso U F hU).symm ≪≫
    ((injectiveResolution (toSiteSheaf F)).isoRightDerivedObj
      (globalSectionsFunctor X) 1).symm

@[simp]
private theorem cechHomologyOneRightDerivedIso_of_subsingleton_H_hom
    (F : Sheaf AddCommGrpCat.{u} X) (hU : ⨆ i, U i = ⊤)
    (hH : ∀ i : ι, Subsingleton (CategoryTheory.Sheaf.H
      ((restrict AddCommGrpCat (U i).isOpenEmbedding).obj F) 1)) :
    (cechHomologyOneRightDerivedIso_of_subsingleton_H U F hU hH).hom =
      (cechInjectiveResolutionVerticalHomologyIso U F hH).hom ≫
        ((cechInjectiveResolutionHorizontalHomologyIso U F hU).inv ≫
          ((injectiveResolution (toSiteSheaf F)).isoRightDerivedObj
            (globalSectionsFunctor X) 1).inv) :=
  rfl

/-- Degree-one homology of an acyclic-cover Cech complex computes genuine
sheaf cohomology. In total degree one only `H¹` of the individual cover
members is required. -/
noncomputable def cechHomologyOneIsoOfSubsingletonH
    (F : Sheaf AddCommGrpCat.{u} X) (hU : ⨆ i, U i = ⊤)
    (hH : ∀ i : ι, Subsingleton (CategoryTheory.Sheaf.H
      ((restrict AddCommGrpCat (U i).isOpenEmbedding).obj F) 1)) :
    ((cechComplexFunctor U).obj F.obj).homology 1 ≅
      (CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology X) 1).obj F :=
  cechHomologyOneRightDerivedIso_of_subsingleton_H U F hU hH ≪≫
    (H.addEquivRightDerivedGlobalSections F 1).symm.toAddCommGrpIso

@[simp]
private theorem cechHomologyOneIsoOfSubsingletonH_hom
    (F : Sheaf AddCommGrpCat.{u} X) (hU : ⨆ i, U i = ⊤)
    (hH : ∀ i : ι, Subsingleton (CategoryTheory.Sheaf.H
      ((restrict AddCommGrpCat (U i).isOpenEmbedding).obj F) 1)) :
    (cechHomologyOneIsoOfSubsingletonH U F hU hH).hom =
      (cechHomologyOneRightDerivedIso_of_subsingleton_H U F hU hH).hom ≫
        (H.addEquivRightDerivedGlobalSections F 1).symm.toAddCommGrpIso.hom :=
  rfl

private theorem isoSquare_inv_naturality
    {A B C D : AddCommGrpCat.{u}} (e : A ≅ B) (e' : C ≅ D)
    (f : A ⟶ C) (g : B ⟶ D) (h : f ≫ e'.hom = e.hom ≫ g) :
    g ≫ e'.inv = e.inv ≫ f := by
  rw [e'.comp_inv_eq, Category.assoc, h]
  simp

private theorem cechInjectiveResolutionDerived_naturality
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (phi : InjectiveResolution.Hom
      (injectiveResolution (toSiteSheaf F))
      (injectiveResolution (toSiteSheaf G)) f) :
    HomologicalComplex.homologyMap
        (cechInjectiveResolutionGlobalSectionsMap phi.hom) 1 ≫
      ((injectiveResolution (toSiteSheaf G)).isoRightDerivedObj
        (globalSectionsFunctor X) 1).inv =
    ((injectiveResolution (toSiteSheaf F)).isoRightDerivedObj
        (globalSectionsFunctor X) 1).inv ≫
      ((globalSectionsFunctor X).rightDerived 1).map f := by
  letI hGlobalSectionsAdditive : (globalSectionsFunctor X).Additive :=
    (CategoryTheory.constantSheafΓAdj
      (Opens.grothendieckTopology X) AddCommGrpCat.{u}).right_adjoint_additive
  have h := @InjectiveResolution.isoRightDerivedObj_inv_naturality
    _ _ _ _ _ _ _ _ _ f
    (injectiveResolution (toSiteSheaf F))
    (injectiveResolution (toSiteSheaf G)) phi.hom
    phi.ι_f_zero_comp_hom_f_zero (globalSectionsFunctor X)
    hGlobalSectionsAdditive 1
  exact h.symm

private theorem cechHomologyOneRightDerivedIso_of_subsingleton_H_naturality
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (hU : ⨆ i, U i = ⊤)
    (hF : ∀ i : ι, Subsingleton (CategoryTheory.Sheaf.H
      ((restrict AddCommGrpCat (U i).isOpenEmbedding).obj F) 1))
    (hG : ∀ i : ι, Subsingleton (CategoryTheory.Sheaf.H
      ((restrict AddCommGrpCat (U i).isOpenEmbedding).obj G) 1)) :
    HomologicalComplex.homologyMap
        ((cechComplexFunctor U).map f.hom) 1 ≫
      (cechHomologyOneRightDerivedIso_of_subsingleton_H U G hU hG).hom =
    (cechHomologyOneRightDerivedIso_of_subsingleton_H U F hU hF).hom ≫
      ((globalSectionsFunctor X).rightDerived 1).map f := by
  let IF := injectiveResolution (toSiteSheaf F)
  let IG := injectiveResolution (toSiteSheaf G)
  let phi : InjectiveResolution.Hom IF IG f :=
    { hom := InjectiveResolution.desc f IG IF
      ι_f_zero_comp_hom_f_zero := by
        change IF.ι.f 0 ≫ (InjectiveResolution.desc f IG IF).f 0 =
          f ≫ IG.ι.f 0
        exact InjectiveResolution.desc_commutes_zero f IG IF }
  let verticalF := cechInjectiveResolutionVerticalEdge U F
  let verticalG := cechInjectiveResolutionVerticalEdge U G
  let horizontalF := cechInjectiveResolutionHorizontalEdge U F
  let horizontalG := cechInjectiveResolutionHorizontalEdge U G
  let totalMap := cechInjectiveResolutionTotalMap U phi.hom
  let sectionsMap := cechInjectiveResolutionGlobalSectionsMap phi.hom
  have hvertical :
      HomologicalComplex.homologyMap ((cechComplexFunctor U).map f.hom) 1 ≫
          (cechInjectiveResolutionVerticalHomologyIso U G hG).hom =
        (cechInjectiveResolutionVerticalHomologyIso U F hF).hom ≫
          HomologicalComplex.homologyMap totalMap 1 := by
    rw [cechInjectiveResolutionVerticalHomologyIso_hom,
      cechInjectiveResolutionVerticalHomologyIso_hom]
    rw [← HomologicalComplex.homologyMap_comp,
      ← HomologicalComplex.homologyMap_comp]
    exact congrArg (fun g ↦ HomologicalComplex.homologyMap g 1)
      (cechInjectiveResolutionVerticalEdge_naturality U f phi).symm
  have hhorizontal :
      HomologicalComplex.homologyMap sectionsMap 1 ≫
          (cechInjectiveResolutionHorizontalHomologyIso U G hU).hom =
        (cechInjectiveResolutionHorizontalHomologyIso U F hU).hom ≫
          HomologicalComplex.homologyMap totalMap 1 := by
    rw [cechInjectiveResolutionHorizontalHomologyIso_hom,
      cechInjectiveResolutionHorizontalHomologyIso_hom]
    rw [← HomologicalComplex.homologyMap_comp,
      ← HomologicalComplex.homologyMap_comp]
    exact congrArg (fun g ↦ HomologicalComplex.homologyMap g 1)
      (cechInjectiveResolutionHorizontalEdge_naturality U f phi)
  have htotal := isoSquare_inv_naturality
    (cechInjectiveResolutionHorizontalHomologyIso U F hU)
    (cechInjectiveResolutionHorizontalHomologyIso U G hU)
    (HomologicalComplex.homologyMap sectionsMap 1)
    (HomologicalComplex.homologyMap totalMap 1) hhorizontal
  have hderived :
      HomologicalComplex.homologyMap sectionsMap 1 ≫
          (IG.isoRightDerivedObj (globalSectionsFunctor X) 1).inv =
        (IF.isoRightDerivedObj (globalSectionsFunctor X) 1).inv ≫
          ((globalSectionsFunctor X).rightDerived 1).map f := by
    exact cechInjectiveResolutionDerived_naturality f phi
  have hmiddle :
      HomologicalComplex.homologyMap totalMap 1 ≫
          ((cechInjectiveResolutionHorizontalHomologyIso U G hU).inv ≫
            (IG.isoRightDerivedObj (globalSectionsFunctor X) 1).inv) =
        (cechInjectiveResolutionHorizontalHomologyIso U F hU).inv ≫
          ((IF.isoRightDerivedObj (globalSectionsFunctor X) 1).inv ≫
            ((globalSectionsFunctor X).rightDerived 1).map f) := by
    calc
      _ = (HomologicalComplex.homologyMap totalMap 1 ≫
            (cechInjectiveResolutionHorizontalHomologyIso U G hU).inv) ≫
            (IG.isoRightDerivedObj (globalSectionsFunctor X) 1).inv :=
        (Category.assoc _ _ _).symm
      _ = ((cechInjectiveResolutionHorizontalHomologyIso U F hU).inv ≫
            HomologicalComplex.homologyMap sectionsMap 1) ≫
            (IG.isoRightDerivedObj (globalSectionsFunctor X) 1).inv := by
        rw [htotal]
      _ = (cechInjectiveResolutionHorizontalHomologyIso U F hU).inv ≫
            (HomologicalComplex.homologyMap sectionsMap 1 ≫
              (IG.isoRightDerivedObj (globalSectionsFunctor X) 1).inv) :=
        Category.assoc _ _ _
      _ = _ := congrArg
        (fun g ↦ (cechInjectiveResolutionHorizontalHomologyIso U F hU).inv ≫ g)
        hderived
  rw [cechHomologyOneRightDerivedIso_of_subsingleton_H_hom,
    cechHomologyOneRightDerivedIso_of_subsingleton_H_hom]
  simp only [← Category.assoc]
  rw [hvertical]
  simp only [Category.assoc]
  rw [hmiddle]
  rfl

/-- The degree-one Cech comparison is natural in the coefficient sheaf. -/
theorem cechHomologyOneIsoOfSubsingletonH_naturality
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (hU : ⨆ i, U i = ⊤)
    (hF : ∀ i : ι, Subsingleton (CategoryTheory.Sheaf.H
      ((restrict AddCommGrpCat (U i).isOpenEmbedding).obj F) 1))
    (hG : ∀ i : ι, Subsingleton (CategoryTheory.Sheaf.H
      ((restrict AddCommGrpCat (U i).isOpenEmbedding).obj G) 1)) :
    HomologicalComplex.homologyMap
        ((cechComplexFunctor U).map f.hom) 1 ≫
      (cechHomologyOneIsoOfSubsingletonH U G hU hG).hom =
    (cechHomologyOneIsoOfSubsingletonH U F hU hF).hom ≫
      (CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology X) 1).map f := by
  rw [cechHomologyOneIsoOfSubsingletonH_hom,
    cechHomologyOneIsoOfSubsingletonH_hom]
  simp only [← Category.assoc]
  rw [cechHomologyOneRightDerivedIso_of_subsingleton_H_naturality
    U f hU hF hG]
  simp only [Category.assoc]
  congr 1
  ext x
  exact H.addEquivRightDerivedGlobalSections_symm_naturality f 1 x

end

end TopCat.Sheaf

/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SheafCechInjectiveAugmentation

/-!
# Degree-one Cech comparison through an injective bicomplex

Construct the horizontal edge from global sections of the chosen injective
resolution. For an actual cover, left exactness of global sections transfers
the sheaf-level Cech resolution to exact low rows, so the horizontal and
vertical edge quasi-isomorphisms identify degree-one Cech homology with
genuine sheaf cohomology.
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

/-- The row augmentation from global sections of the resolution to native
Cech degree zero. -/
private noncomputable def cechInjectiveResolutionHorizontalAugmentation
    (F : Sheaf AddCommGrpCat.{u} X) (q : ℕ) :
    (cechInjectiveResolutionGlobalSectionsComplex F).X q ⟶
      ((cechInjectiveResolutionBicomplex U F).X q).X 0 :=
  cechGlobalSectionsAugmentation
    ((injectiveResolution (toSiteSheaf F)).cocomplex.X q) U

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
private noncomputable def cechGlobalSectionsNativeShortComplex
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
private theorem cechGlobalSectionsNativeShortComplex_exact
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
private theorem cechGlobalSectionsAugmentation_mono
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

/-- Degree-one homology of an acyclic-cover Cech complex computes genuine
sheaf cohomology. In total degree one only `H¹` of the individual cover
members is required. -/
noncomputable def cechHomologyOneIso_of_subsingleton_H
    (F : Sheaf AddCommGrpCat.{u} X) (hU : ⨆ i, U i = ⊤)
    (hH : ∀ i : ι, Subsingleton (CategoryTheory.Sheaf.H
      ((restrict AddCommGrpCat (U i).isOpenEmbedding).obj F) 1)) :
    ((cechComplexFunctor U).obj F.obj).homology 1 ≅
      (CategoryTheory.Sheaf.functorH
        (Opens.grothendieckTopology X) 1).obj F := by
  letI : AddCommGroup (CategoryTheory.Sheaf.H F 1) :=
    CategoryTheory.Abelian.Ext.instAddCommGroup
  let vertical := cechInjectiveResolutionVerticalEdge U F
  let horizontal := cechInjectiveResolutionHorizontalEdge U F
  letI : QuasiIsoAt vertical 1 :=
    cechInjectiveResolutionVerticalEdge_quasiIsoAt_one U F hH
  letI : QuasiIsoAt horizontal 1 :=
    cechInjectiveResolutionHorizontalEdge_quasiIsoAt_one U F hU
  exact asIso (HomologicalComplex.homologyMap vertical 1) ≪≫
    (asIso (HomologicalComplex.homologyMap horizontal 1)).symm ≪≫
    ((injectiveResolution (toSiteSheaf F)).isoRightDerivedObj
      (globalSectionsFunctor X) 1).symm ≪≫
    (H.addEquivRightDerivedGlobalSections F 1).symm.toAddCommGrpIso

end

end TopCat.Sheaf

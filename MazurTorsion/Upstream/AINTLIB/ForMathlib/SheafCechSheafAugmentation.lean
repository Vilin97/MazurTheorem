/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SheafCechSheafComplex

/-!
# The augmentation of the sheaf-level Cech complex

This file defines the canonical map from a sheaf to the degree-zero term of its
sheaf-level Cech complex. Its composite with the first differential is zero because the
two degree-zero cofaces agree after restriction.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}
variable (F : Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} (U : ι → Opens X)

private noncomputable def cechAugmentationFactorSectionsIso (A V : Opens X) :
    ((restrict AddCommGrpCat A.isOpenEmbedding ⋙
        pushforward AddCommGrpCat A.inclusion').obj F).obj.obj (op V) ≅
      F.obj.obj (op (V ⊓ A)) :=
  F.obj.mapIso (eqToIso (congrArg op (Opens.functor_map_eq_inf A V)))

private theorem cechAugmentationFactorSectionsIso_hom (A V : Opens X) :
    (cechAugmentationFactorSectionsIso F A V).hom =
      ((eqToIso (by rw [toRestrict_obj_obj_obj,
          Opens.functor_map_eq_inf])) :
        ((restrict AddCommGrpCat A.isOpenEmbedding ⋙
          pushforward AddCommGrpCat A.inclusion').obj F).obj.obj (op V) ≅
            F.obj.obj (op (V ⊓ A))).hom := by
  rw [cechAugmentationFactorSectionsIso, Functor.mapIso_hom, eqToIso.hom,
    eqToIso.hom, eqToHom_map]
  cat_disch

/-- The canonical augmentation from `F` to the degree-zero term of its sheaf-level Cech
complex. -/
noncomputable def cechAugmentation : F ⟶ cechTerm F U 0 :=
  Pi.lift fun i : Fin 1 → ι =>
    (toRestrict AddCommGrpCat (∏ᶜ fun k : Fin 1 => U (i k))).app F

/-- Under the concrete section equivalence, the Cech augmentation restricts a section to
each member of the open family. -/
theorem cechAugmentation_apply (V : Opens X) (x : F.obj.obj (op V))
    (i : Fin 1 → ι) :
    cechTermSectionsAddEquiv F U 0 V
        ((cechAugmentation F U).hom.app (op V) x) i =
      F.obj.map (homOfLE (inf_le_left :
        (V ⊓ (∏ᶜ fun k : Fin 1 => U (i k))) ≤ V)).op x := by
  rw [cechTermSectionsAddEquiv_apply]
  rw [← cechAugmentationFactorSectionsIso_hom F
    (∏ᶜ fun k : Fin 1 => U (i k)) V]
  have hcomponent :
      (Pi.π (cechTermFactor F U 0) i).hom.app (op V)
          ((cechAugmentation F U).hom.app (op V) x) =
        ((toRestrict AddCommGrpCat
          (∏ᶜ fun k : Fin 1 => U (i k))).app F).hom.app (op V) x := by
    exact ConcreteCategory.congr_hom
      (congrArg (fun f => f.hom.app (op V))
        (Pi.lift_π (fun i : Fin 1 → ι =>
          (toRestrict AddCommGrpCat
            (∏ᶜ fun k : Fin 1 => U (i k))).app F) i)) x
  rw [hcomponent, toRestrict_app_hom_app]
  change (F.obj.map _ ≫ F.obj.map _) x = F.obj.map _ x
  exact ConcreteCategory.congr_hom
    ((F.obj.map_comp _ _).symm.trans
      (congrArg F.obj.map (Subsingleton.elim _ _))) x

private theorem cechAugmentation_comp_coface_eq :
    cechAugmentation F U ≫ cechCoface F U 0 0 =
      cechAugmentation F U ≫ cechCoface F U 0 1 := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  intro x
  apply (cechTermSectionsAddEquiv F U 1 V.unop).injective
  funext i
  have hcompZero :
      (cechAugmentation F U ≫ cechCoface F U 0 0).hom.app V =
        (cechAugmentation F U).hom.app V ≫
          (cechCoface F U 0 0).hom.app V := rfl
  have hcompOne :
      (cechAugmentation F U ≫ cechCoface F U 0 1).hom.app V =
        (cechAugmentation F U).hom.app V ≫
          (cechCoface F U 0 1).hom.app V := rfl
  rw [hcompZero, hcompOne, CategoryTheory.comp_apply,
    CategoryTheory.comp_apply, cechCoface_apply, cechCoface_apply,
    cechAugmentation_apply, cechAugmentation_apply]
  change (F.obj.map _ ≫ F.obj.map _) x =
    (F.obj.map _ ≫ F.obj.map _) x
  exact ConcreteCategory.congr_hom
    ((F.obj.map_comp _ _).symm.trans
      ((congrArg F.obj.map (Subsingleton.elim _ _)).trans
        (F.obj.map_comp _ _))) x

/-- The Cech augmentation followed by the first differential is zero. -/
theorem cechAugmentation_comp :
    cechAugmentation F U ≫ cechDifferential F U 0 = 0 := by
  rw [cechDifferential, Fin.sum_univ_two]
  simp [cechAugmentation_comp_coface_eq F U]

/-- The augmentation and first differential of the sheaf-level Cech complex. -/
noncomputable def cechAugmentedShortComplex :
    ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk (cechAugmentation F U) (cechDifferential F U 0)
    (cechAugmentation_comp F U)

end TopCat.Sheaf

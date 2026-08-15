/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleIsoTopSectionFormula

/-!
# Sections and successive open restrictions

The canonical comparison between restriction along a composite open
immersion and two successive restrictions agrees with the direct
identification of sections.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}}
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [IsOpenImmersion f] [IsOpenImmersion g]
  (M : Z.Modules)

/-- On sections, the restriction-composition comparison is the direct
identification obtained from the equality of image opens. -/
theorem restrictFunctorComp_hom_section
    (U : X.Opens)
    (x : Γ(M.restrict (f ≫ g), U)) :
    (M.restrictAppIso g (f ''ᵁ U)).hom
        (((M.restrict g).restrictAppIso f U).hom
          (((restrictFunctorComp f g).hom.app M).app U x)) =
      (eqToIso
        (congrArg (fun W => Γ(M, W))
          (Scheme.Hom.comp_image f g U))).hom
        ((M.restrictAppIso (f ≫ g) U).hom x) := by
  rw [restrictFunctorComp_hom_app_app]
  rw [eqToIso_sections_hom_eq_map
    M (Scheme.Hom.comp_image f g U)]
  exact
    ConcreteCategory.congr_hom
      (congrArg
        (fun q => M.presheaf.map q)
        (Subsingleton.elim _ _))
      x

/-- Equal open immersions have the expected image comparison with a
chosen factorization. -/
lemma image_eq_comp_of_eq
    (q : X ⟶ Z) [IsOpenImmersion q]
    (h : q = f ≫ g) (U : X.Opens) :
    q ''ᵁ U = g ''ᵁ (f ''ᵁ U) := by
  subst q
  exact Scheme.Hom.comp_image f g U

/-- The preceding comparison is compatible with replacing the composite
open immersion by an equal morphism. -/
theorem restrictFunctorCongr_comp_hom_section
    (q : X ⟶ Z) [IsOpenImmersion q]
    (h : q = f ≫ g)
    (U : X.Opens)
    (x : Γ(M.restrict q, U)) :
    (M.restrictAppIso g (f ''ᵁ U)).hom
        (((M.restrict g).restrictAppIso f U).hom
          (((restrictFunctorComp f g).hom.app M).app U
            (((restrictFunctorCongr h).hom.app M).app U x))) =
      (eqToIso
        (congrArg (fun W => Γ(M, W))
          (image_eq_comp_of_eq f g q h U))).hom
        ((M.restrictAppIso q U).hom x) := by
  rw [restrictFunctorComp_hom_section]
  rw [restrictFunctorCongr_hom_app_app]
  rw [eqToIso_sections_hom_eq_map
    M (Scheme.Hom.comp_image f g U)]
  rw [eqToIso_sections_hom_eq_map M
    (image_eq_comp_of_eq f g q h U)]
  simp only [restrictAppIso, Iso.refl_hom]
  change
    M.presheaf.map _ (M.presheaf.map _ x) =
      M.presheaf.map _ x
  erw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  exact
    ConcreteCategory.congr_hom
      (congrArg
        (fun r => M.presheaf.map r)
        (Subsingleton.elim _ _))
      x

/-- The image of the terminal open under a factorization through an
isomorphism is the image of the terminal open of the intermediate
scheme. -/
lemma image_top_eq_of_iso_comp
    (e : X ≅ Y) (g : Y ⟶ Z) [IsOpenImmersion g]
    (q : X ⟶ Z) [IsOpenImmersion q]
    (h : q = e.hom ≫ g) :
    q ''ᵁ (⊤ : X.Opens) =
      g ''ᵁ (⊤ : Y.Opens) :=
  (image_eq_comp_of_eq e.hom g q h ⊤).trans
    (congrArg (fun W => g ''ᵁ W)
      (iso_hom_image_top e))

/-- The section comparison for a factorization through an isomorphism,
specialized to terminal opens. -/
theorem restrictIso_comp_hom_top_section
    (e : X ≅ Y) (g : Y ⟶ Z) [IsOpenImmersion g]
    (q : X ⟶ Z) [IsOpenImmersion q]
    (h : q = e.hom ≫ g)
    (M : Z.Modules)
    (x : Γ(M.restrict q, ⊤)) :
    (M.restrictAppIso g ⊤).hom
        ((eqToIso
          (congrArg
            (fun W => Γ(M.restrict g, W))
            (iso_hom_image_top e))).hom
          (((M.restrict g).restrictAppIso e.hom ⊤).hom
            (((restrictFunctorComp e.hom g).hom.app M).app ⊤
              (((restrictFunctorCongr h).hom.app M).app ⊤ x)))) =
      (eqToIso
        (congrArg (fun W => Γ(M, W))
          (image_top_eq_of_iso_comp e g q h))).hom
        ((M.restrictAppIso q ⊤).hom x) := by
  rw [eqToIso_sections_hom_eq_map
    (M.restrict g) (iso_hom_image_top e)]
  rw [← CategoryTheory.comp_apply]
  rw [map_restrictAppIso_hom]
  rw [CategoryTheory.comp_apply]
  rw [restrictFunctorCongr_comp_hom_section]
  rw [eqToIso_sections_hom_eq_map M
    (image_eq_comp_of_eq e.hom g q h ⊤)]
  rw [eqToIso_sections_hom_eq_map M
    (image_top_eq_of_iso_comp e g q h)]
  simp only [restrictAppIso, Iso.refl_hom]
  change
    M.presheaf.map _
      (M.presheaf.map _ x) =
      M.presheaf.map _ x
  erw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  exact
    ConcreteCategory.congr_hom
      (congrArg
        (fun r => M.presheaf.map r)
        (Subsingleton.elim _ _))
      x

end AlgebraicGeometry.Scheme.Modules

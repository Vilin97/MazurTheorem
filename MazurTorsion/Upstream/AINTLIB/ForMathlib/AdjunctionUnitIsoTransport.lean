/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

Adapted from the Apache-licensed `AdjunctionUnitIsoTransport.lean`
in Vilin97/Clawristotle.
-/
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Transporting invertibility of adjunction units

Invertibility of an adjunction-unit component depends only on the left
adjoint up to natural isomorphism.
-/

open CategoryTheory

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₂} D]
variable {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}

/-- A natural isomorphism of left adjoints transports invertibility of unit components. -/
theorem isIso_unit_app_of_natIso_left
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (e : L₂ ≅ L₁) (X : C)
    [IsIso (adj₂.unit.app X)] :
    IsIso (adj₁.unit.app X) := by
  let β : R₁ ⟶ R₂ := conjugateEquiv adj₁ adj₂ e.hom
  haveI hβ : IsIso β := by
    dsimp only [β]
    infer_instance
  haveI heX : IsIso (e.hom.app X) := (e.app X).isIso_hom
  haveI hMapEX : IsIso (R₂.map (e.hom.app X)) :=
    Functor.map_isIso R₂ (e.hom.app X)
  haveI hright :
      IsIso (adj₂.unit.app X ≫ R₂.map (e.hom.app X)) :=
    IsIso.comp_isIso'
      (inferInstanceAs (IsIso (adj₂.unit.app X))) hMapEX
  haveI hleft :
      IsIso (adj₁.unit.app X ≫ β.app (L₁.obj X)) := by
    rw [unit_conjugateEquiv adj₁ adj₂ e.hom X]
    exact hright
  exact
    @IsIso.of_isIso_comp_right _ _ _ _ _
      (adj₁.unit.app X) (β.app (L₁.obj X))
      (inferInstanceAs (IsIso (β.app (L₁.obj X)))) hleft

/-- Unit-component invertibility is invariant under a natural isomorphism of left adjoints. -/
theorem isIso_unit_app_iff_of_natIso_left
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (e : L₂ ≅ L₁) (X : C) :
    IsIso (adj₁.unit.app X) ↔ IsIso (adj₂.unit.app X) := by
  constructor
  · intro h
    letI : IsIso (adj₁.unit.app X) := h
    exact isIso_unit_app_of_natIso_left adj₂ adj₁ e.symm X
  · intro h
    letI : IsIso (adj₂.unit.app X) := h
    exact isIso_unit_app_of_natIso_left adj₁ adj₂ e X

end CategoryTheory.Adjunction

namespace CategoryTheory.NatTrans

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₂} D]
variable {F G : C ⥤ D}

/-- Component invertibility of a natural transformation transports across an object isomorphism. -/
theorem isIso_app_of_iso
    (η : F ⟶ G) {X Y : C} (e : X ≅ Y)
    [IsIso (η.app Y)] :
    IsIso (η.app X) := by
  haveI hF : IsIso (F.map e.hom) := inferInstance
  haveI hG : IsIso (G.map e.hom) := inferInstance
  haveI hleft : IsIso (F.map e.hom ≫ η.app Y) := inferInstance
  exact IsIso.of_isIso_fac_right (η.naturality e.hom).symm

end CategoryTheory.NatTrans

/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Compatibility of open restriction and pullback with composition

For an open immersion, restriction and geometric pullback are the two
left adjoints of the same pushforward functor.  Their canonical
`leftAdjointUniq` comparison commutes with composition.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [IsOpenImmersion f] [IsOpenImmersion g]

/-- Restriction maps are computed objectwise on sections. -/
lemma restrictFunctor_map_app {P Q : Y.Modules}
    (φ : P ⟶ Q) (V : X.Opens) :
    ((restrictFunctor f).map φ).app V =
      φ.app (f ''ᵁ V) := rfl

/-- The mate of the canonical restriction-pullback comparison is the
identity of pushforward. -/
lemma restrictFunctorIsoPullback_conjugate :
    conjugateEquiv
        (pullbackPushforwardAdjunction f)
        (restrictAdjunction f)
        (restrictFunctorIsoPullback f).hom =
      𝟙 (pushforward f) := by
  simp [restrictFunctorIsoPullback,
    Adjunction.leftAdjointUniq]

/-- The composite of the two restriction-pullback comparisons also has
identity mate. -/
lemma restrictFunctorIsoPullback_comp_conjugate :
    conjugateEquiv
        ((pullbackPushforwardAdjunction g).comp
          (pullbackPushforwardAdjunction f))
        ((restrictAdjunction g).comp
          (restrictAdjunction f))
        (Functor.whiskerRight
              (restrictFunctorIsoPullback g).hom
              (restrictFunctor f) ≫
          Functor.whiskerLeft
              (pullback g)
              (restrictFunctorIsoPullback f).hom) =
      𝟙 (pushforward f ⋙ pushforward g) := by
  rw [← conjugateEquiv_comp
    ((pullbackPushforwardAdjunction g).comp
      (pullbackPushforwardAdjunction f))
    ((pullbackPushforwardAdjunction g).comp
      (restrictAdjunction f))
    ((restrictAdjunction g).comp
      (restrictAdjunction f))]
  rw [conjugateEquiv_whiskerLeft,
    conjugateEquiv_whiskerRight]
  simp [restrictFunctorIsoPullback,
    Adjunction.leftAdjointUniq]

omit [IsOpenImmersion f] [IsOpenImmersion g] in
/-- The mate of the pullback composition comparison is the inverse
pushforward composition comparison. -/
lemma pullbackComp_hom_conjugate :
    conjugateEquiv
        (pullbackPushforwardAdjunction (f ≫ g))
        ((pullbackPushforwardAdjunction g).comp
          (pullbackPushforwardAdjunction f))
        (pullbackComp f g).hom =
      (pushforwardComp f g).inv := by
  have hcomm := conjugateEquiv_comm
    (adj₁ :=
      (pullbackPushforwardAdjunction g).comp
        (pullbackPushforwardAdjunction f))
    (adj₂ := pullbackPushforwardAdjunction (f ≫ g))
    (show
      (pullbackComp f g).hom ≫
          (pullbackComp f g).inv =
        𝟙 _ from (pullbackComp f g).hom_inv_id)
  rw [conjugateEquiv_pullbackComp_inv] at hcomm
  exact (Iso.hom_comp_eq_id
    (pushforwardComp f g)).mp hcomm

/-- The mate of the restriction composition comparison is the
pushforward composition comparison. -/
lemma restrictFunctorComp_hom_conjugate :
    conjugateEquiv
        ((restrictAdjunction g).comp
          (restrictAdjunction f))
        (restrictAdjunction (f ≫ g))
        (restrictFunctorComp f g).hom =
      (pushforwardComp f g).hom := by
  ext M U x
  simp only [pushforward_obj_obj, Scheme.Hom.comp_base,
    TopologicalSpace.Opens.map_comp_obj, Functor.comp_obj,
    conjugateEquiv_apply_app, Adjunction.comp_counit_app,
    Functor.map_comp, Hom.comp_app,
    restrictAdjunction_unit_app_app, homOfLE_leOfHom,
    pushforward_obj_presheaf_map, pushforward_map_app,
    restrictFunctorComp_hom_app_app, Functor.op_obj, eqToHom_op,
    restrictFunctor_map_app, restrictAdjunction_counit_app_app,
    pushforwardComp_hom_app_app, AddCommGrpCat.hom_id]
  let A := M.presheaf.obj (Opposite.op (f ⁻¹ᵁ (g ⁻¹ᵁ U)))
  change (M.presheaf.map _ ≫ M.presheaf.map _ ≫ M.presheaf.map _ ≫
    M.presheaf.map _) x = (𝟙 A) x
  congr 1
  simp only [← Functor.map_comp]
  rw [← M.presheaf.map_id]
  congr 1

/-- The canonical identification of restriction with pullback commutes
with composition of open immersions. -/
lemma restrictFunctorIsoPullback_comp :
    (restrictFunctorIsoPullback (f ≫ g)).hom =
      (restrictFunctorComp f g).hom ≫
        Functor.whiskerRight
          (restrictFunctorIsoPullback g).hom
          (restrictFunctor f) ≫
        Functor.whiskerLeft
          (pullback g)
          (restrictFunctorIsoPullback f).hom ≫
        (pullbackComp f g).hom := by
  let adjP :=
    pullbackPushforwardAdjunction (f ≫ g)
  let adjPP :=
    (pullbackPushforwardAdjunction g).comp
      (pullbackPushforwardAdjunction f)
  let adjRR :=
    (restrictAdjunction g).comp
      (restrictAdjunction f)
  let adjR :=
    restrictAdjunction (f ≫ g)
  apply (conjugateEquiv adjP adjR).injective
  rw [restrictFunctorIsoPullback_conjugate]
  simp only [← Category.assoc]
  rw [← conjugateEquiv_comp adjP adjPP adjR]
  rw [Category.assoc]
  rw [← conjugateEquiv_comp adjPP adjRR adjR]
  rw [pullbackComp_hom_conjugate,
    restrictFunctorIsoPullback_comp_conjugate,
    restrictFunctorComp_hom_conjugate]
  rw [Category.id_comp, Iso.inv_hom_id]

/-- Objectwise form of
`restrictFunctorIsoPullback_comp`. -/
lemma restrictFunctorIsoPullback_comp_app
    (M : Z.Modules) :
    (restrictFunctorIsoPullback (f ≫ g)).hom.app M =
      (restrictFunctorComp f g).hom.app M ≫
        (restrictFunctor f).map
          ((restrictFunctorIsoPullback g).hom.app M) ≫
        (restrictFunctorIsoPullback f).hom.app
          ((pullback g).obj M) ≫
        (pullbackComp f g).hom.app M := by
  exact congr_app
    (restrictFunctorIsoPullback_comp f g) M

end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.BaseRingModuleSheafFunctor
import MazurTorsion.Upstream.CoherentCohomologyFinite.TopologicalSheafBaseLinearCategory

/-!
# Base-linear module sheaves and scheme pushforward

For a morphism of schemes over a fixed affine base, taking the
underlying sheaf of modules over the base ring commutes with direct
image.  The only non-definitional point is compatibility of the two
base-ring actions.
-/


open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing

variable {k : Type u} [CommRing k]
variable {X Y : Scheme.{u}}
variable [X.Over (Spec (CommRingCat.of k))]
variable [Y.Over (Spec (CommRingCat.of k))]

/-- The structural base-ring map on an open commutes with a morphism
over the base. -/
lemma algebraMapOnOpen_comp_app
    (f : X ⟶ Y)
    (h :
      f ≫ Y ↘ Spec (CommRingCat.of k) =
        X ↘ Spec (CommRingCat.of k))
    (U : Y.Opens) :
    (f.app U).hom.comp
        (algebraMapOnOpen (k := k) U) =
      algebraMapOnOpen (k := k) (f ⁻¹ᵁ U) := by
  rw [algebraMapOnOpen, algebraMapOnOpen]
  change
    (((Scheme.ΓSpecIso
          (CommRingCat.of k)).inv ≫
        (Y ↘ Spec (CommRingCat.of k)).appTop ≫
        Y.presheaf.map
          (homOfLE le_top).op) ≫
      f.app U).hom =
    ((Scheme.ΓSpecIso
        (CommRingCat.of k)).inv ≫
      (X ↘ Spec (CommRingCat.of k)).appTop ≫
      X.presheaf.map
        (homOfLE le_top).op).hom
  apply congrArg CommRingCat.Hom.hom
  simp only [Category.assoc]
  rw [cancel_epi]
  let eY : U ≤
      (Y ↘ Spec (CommRingCat.of k)) ⁻¹ᵁ
        (⊤ : (Spec (CommRingCat.of k)).Opens) := by
    simp
  let eX : f ⁻¹ᵁ U ≤
      (X ↘ Spec (CommRingCat.of k)) ⁻¹ᵁ
        (⊤ : (Spec (CommRingCat.of k)).Opens) := by
    simp
  have hY :
      (Y ↘ Spec (CommRingCat.of k)).appTop ≫
          Y.presheaf.map
            (homOfLE le_top).op =
        (Y ↘ Spec (CommRingCat.of k)).appLE
          (⊤ :
            (Spec (CommRingCat.of k)).Opens)
          U eY := by
    rfl
  have hX :
      (X ↘ Spec (CommRingCat.of k)).appTop ≫
          X.presheaf.map
            (homOfLE le_top).op =
        (X ↘ Spec (CommRingCat.of k)).appLE
          (⊤ :
            (Spec (CommRingCat.of k)).Opens)
          (f ⁻¹ᵁ U) eX := by
    rfl
  rw [← Category.assoc, hY, hX,
    f.app_eq_appLE]
  have hcomp :=
    Scheme.Hom.appLE_comp_appLE f
      (Y ↘ Spec (CommRingCat.of k))
      (⊤ : (Spec (CommRingCat.of k)).Opens)
      U (f ⁻¹ᵁ U) eY le_rfl
  simpa only [h] using hcomp

/-- Sectionwise comparison between the base-linear sheaf of a
scheme-module pushforward and the topological direct image. -/
noncomputable def moduleSheafPushforwardAppIso
    (f : X ⟶ Y)
    (h :
      f ≫ Y ↘ Spec (CommRingCat.of k) =
        X ↘ Spec (CommRingCat.of k))
    (M : X.Modules) (U : Y.Opensᵒᵖ) :
    (moduleSheaf
      (k := k)
      ((Scheme.Modules.pushforward f).obj M)).obj.obj U ≅
    (((TopCat.Sheaf.pushforward
        (ModuleCat.{u} k) f.base).obj
      (moduleSheaf (k := k) M :
        (X.toPresheafedSpace : TopCat).Sheaf
          (ModuleCat.{u} k))).presheaf.obj U) where
  hom :=
    ConcreteCategory.ofHom
      (C := ModuleCat.{u} k)
      { toFun := id
        map_add' := fun _ _ => rfl
        map_smul' := fun r x => by
          change
            ((f.app U.unop).hom
                (algebraMapOnOpen
                  (k := k) U.unop r) •
              (show
                Γ(M, f ⁻¹ᵁ U.unop)
                from x) :
                Γ(M, f ⁻¹ᵁ U.unop)) =
              algebraMapOnOpen
                  (k := k)
                  (f ⁻¹ᵁ U.unop) r •
                (show
                  Γ(M, f ⁻¹ᵁ U.unop)
                  from x)
          have hr :=
            DFunLike.congr_fun
              (algebraMapOnOpen_comp_app
                (k := k) f h U.unop) r
          change
            (f.app U.unop).hom
                (algebraMapOnOpen
                  (k := k) U.unop r) =
              algebraMapOnOpen
                (k := k)
                (f ⁻¹ᵁ U.unop) r at hr
          rw [hr] }
  inv :=
    ConcreteCategory.ofHom
      (C := ModuleCat.{u} k)
      { toFun := id
        map_add' := fun _ _ => rfl
        map_smul' := fun r x => by
          change
            (algebraMapOnOpen
                (k := k)
                (f ⁻¹ᵁ U.unop) r •
              (show
                Γ(M, f ⁻¹ᵁ U.unop)
                from x) :
                Γ(M, f ⁻¹ᵁ U.unop)) =
              (f.app U.unop).hom
                  (algebraMapOnOpen
                    (k := k) U.unop r) •
                (show
                  Γ(M, f ⁻¹ᵁ U.unop)
                  from x)
          have hr :=
            DFunLike.congr_fun
              (algebraMapOnOpen_comp_app
                (k := k) f h U.unop) r
          change
            (f.app U.unop).hom
                (algebraMapOnOpen
                  (k := k) U.unop r) =
              algebraMapOnOpen
                (k := k)
                (f ⁻¹ᵁ U.unop) r at hr
          rw [hr] }
  hom_inv_id := by
    ext x
    rfl
  inv_hom_id := by
    ext x
    rfl

/-- Taking the fixed-base module sheaf commutes with pushforward along
a morphism over that base. -/
noncomputable def moduleSheafPushforwardIso
    (f : X ⟶ Y)
    (h :
      f ≫ Y ↘ Spec (CommRingCat.of k) =
        X ↘ Spec (CommRingCat.of k))
    (M : X.Modules) :
    moduleSheaf
        (k := k)
        ((Scheme.Modules.pushforward f).obj M) ≅
      (TopCat.Sheaf.pushforward
        (ModuleCat.{u} k) f.base).obj
        (moduleSheaf (k := k) M :
          (X.toPresheafedSpace : TopCat).Sheaf
            (ModuleCat.{u} k)) :=
  ObjectProperty.isoMk _
    (NatIso.ofComponents
      (fun U =>
        moduleSheafPushforwardAppIso
          (k := k) f h M U)
      (fun {U V} i => by
        ext x
        rfl))

/-- Functorial form of `moduleSheafPushforwardIso`. -/
noncomputable def moduleSheafPushforwardNatIso
    (f : X ⟶ Y)
    (h :
      f ≫ Y ↘ Spec (CommRingCat.of k) =
        X ↘ Spec (CommRingCat.of k)) :
    Scheme.Modules.pushforward f ⋙
        moduleSheafFunctor
          (k := k) (X := Y) ≅
      moduleSheafFunctor
          (k := k) (X := X) ⋙
        TopCat.Sheaf.pushforward
          (ModuleCat.{u} k) f.base :=
  NatIso.ofComponents
    (fun M =>
      moduleSheafPushforwardIso
        (k := k) f h M)
    (fun {M N} φ => by
      ext U x
      rfl)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing

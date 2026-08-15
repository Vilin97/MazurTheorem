/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAffineQuasicoherent
import Mathlib.AlgebraicGeometry.Restrict

/-!
# Restricting a scheme-module pushforward

For a morphism `f : X ⟶ Y` and an open `U ⊆ Y`, restriction of `f_* M`
to `U` agrees with pushforward of `M` restricted to `f ⁻¹ U` along the
restricted morphism.  The proof is at the opens-site level: both sides are
pushforwards along naturally isomorphic composites.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- Compatibility of the structure-sheaf maps in the cartesian square
formed by restricting a morphism to an open of its target. -/
lemma morphismRestrict_appIso_compat
    (f : X ⟶ Y) (U : Y.Opens)
    (V : (↑U : Scheme.{u}).Opens) :
    (U.ι.appIso V).inv ≫
        f.app (U.ι ''ᵁ V) ≫
          X.presheaf.map
            (eqToHom
              (image_morphismRestrict_preimage
                f U V)).op =
      (f ∣_ U).app V ≫
        ((f ⁻¹ᵁ U).ι.appIso
          ((f ∣_ U) ⁻¹ᵁ V)).inv := by
  rw [Scheme.Opens.ι_appIso, Scheme.Opens.ι_appIso]
  change
    f.app (U.ι ''ᵁ V) ≫
        X.presheaf.map
          (eqToHom
            (image_morphismRestrict_preimage f U V)).op =
      (f ∣_ U).app V
  exact (morphismRestrict_app f U V).symm

/-- The two composites of opens functors in the restriction square agree. -/
lemma morphismRestrict_opensFunctor_eq
    (f : X ⟶ Y) (U : Y.Opens) :
    U.ι.opensFunctor ⋙ TopologicalSpace.Opens.map f.base =
      TopologicalSpace.Opens.map (f ∣_ U).base ⋙
        (f ⁻¹ᵁ U).ι.opensFunctor :=
  CategoryTheory.Functor.ext
    (fun V =>
      (image_morphismRestrict_preimage
        f U V).symm)
    (fun _ _ _ => Subsingleton.elim _ _)

/-- Restriction commutes with scheme-module pushforward. -/
noncomputable def pushforwardRestrictIso
    (f : X ⟶ Y) (U : Y.Opens) :
    Scheme.Modules.pushforward f ⋙
        Scheme.Modules.restrictFunctor U.ι ≅
      Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι ⋙
        Scheme.Modules.pushforward (f ∣_ U) :=
  haveI h₁ : Functor.IsContinuous
      (U.ι.opensFunctor ⋙
        TopologicalSpace.Opens.map f.base)
      (Opens.grothendieckTopology ↥(↑U : Scheme.{u}))
      (Opens.grothendieckTopology ↥X) :=
    Functor.isContinuous_comp _ _ _
      (Opens.grothendieckTopology ↥Y) _
  haveI h₂ : Functor.IsContinuous
      (TopologicalSpace.Opens.map (f ∣_ U).base ⋙
        (f ⁻¹ᵁ U).ι.opensFunctor)
      (Opens.grothendieckTopology ↥(↑U : Scheme.{u}))
      (Opens.grothendieckTopology ↥X) :=
    Functor.isContinuous_comp _ _ _
      (Opens.grothendieckTopology
        ↥(↑(f ⁻¹ᵁ U) : Scheme.{u})) _
  SheafOfModules.pushforwardComp _ _ ≪≫
    SheafOfModules.pushforwardNatIso _
      (NatIso.ofComponents
        (fun V =>
          eqToIso
            (image_morphismRestrict_preimage
              f U V))
        (fun _ => Subsingleton.elim _ _)) ≪≫
    SheafOfModules.pushforwardCongr (by
      ext V x
      exact
        congr($(morphismRestrict_appIso_compat
          f U (Opposite.unop V)) x)) ≪≫
    (SheafOfModules.pushforwardComp _ _).symm

/-- Pointwise form of the canonical comparison between restriction and
pushforward along a restricted morphism. -/
@[simp]
lemma pushforwardRestrictIso_hom_app_app
    (f : X ⟶ Y) (U : Y.Opens) (M : X.Modules)
    (V : (↑U : Scheme.{u}).Opens) :
    ((pushforwardRestrictIso f U).hom.app M).app V =
      M.presheaf.map
        (eqToHom
          (image_morphismRestrict_preimage f U V)).op := by
  rfl

/-- A pushforward presheaf acts on an arbitrary morphism in the
opposite opens category by applying the opposite opens functor. -/
@[simp]
lemma pushforward_obj_presheaf_map_op
    {A B : Scheme.{u}} (f : A ⟶ B) (M : A.Modules)
    {V W : B.Opensᵒᵖ} (i : V ⟶ W) :
    ((pushforward f).obj M).presheaf.map i =
      M.presheaf.map
        ((TopologicalSpace.Opens.map f.base).op.map i) := by
  rfl

end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.BaseRingModuleSheaf
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAffineCover
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Functoriality and exactness of base-linear module sheaves

For a scheme `X` over `Spec k`, `BaseRing.moduleSheaf M` remembers the
sectionwise `k`-module structure on an `𝒪_X`-module `M`.  This file makes
that construction functorial.

The resulting functor is faithful and exact.  Its exactness is proved by
forgetting the `k`-action: the composite is definitionally the usual
forgetful functor from sheaves of `𝒪_X`-modules to sheaves of abelian
groups.  In particular, epimorphic coherent presentations and their
kernels may be transported to the base-linear sheaf category.
-/


open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing

open Limits

variable {k : Type u} [CommRing k]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]

attribute [local instance] sectionsModule

/-- A morphism of scheme modules, regarded as a morphism of
base-linear sheaves. -/
noncomputable def moduleSheafMap {M N : X.Modules} (f : M ⟶ N) :
    moduleSheaf (k := k) M ⟶ moduleSheaf (k := k) N :=
  ⟨
    { app := fun U =>
        ModuleCat.ofHom
          { toFun := f.app U.unop
            map_add' := map_add _
            map_smul' := fun r x => by
              change
                f.app U.unop
                    ((algebraMapOnOpen (k := k) U.unop r) • x) =
                  (algebraMapOnOpen (k := k) U.unop r) •
                    f.app U.unop x
              exact Scheme.Modules.Hom.app_smul f _ _ }
      naturality := fun U V i => by
        ext x
        exact PresheafOfModules.naturality_apply f.val i x }⟩

@[simp]
lemma moduleSheafMap_app_apply {M N : X.Modules} (f : M ⟶ N)
    (U : X.Opensᵒᵖ) (x : Γ(M, U.unop)) :
    (moduleSheafMap (k := k) f).hom.app U x = f.app U.unop x :=
  rfl

/-- Regard an `𝒪_X`-module on a scheme over `Spec k` as a sheaf of
`k`-modules. -/
noncomputable def moduleSheafFunctor :
    X.Modules ⥤
      Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k) where
  obj M := moduleSheaf (k := k) M
  map f := moduleSheafMap (k := k) f
  map_id M := by
    ext U x
    change x = x
    rfl
  map_comp f g := by
    ext U x
    change g.app U.unop (f.app U.unop x) =
      g.app U.unop (f.app U.unop x)
    rfl

@[simp]
lemma moduleSheafFunctor_obj (M : X.Modules) :
    (moduleSheafFunctor (k := k) (X := X)).obj M =
      moduleSheaf (k := k) M :=
  rfl

/-- Forget the base-ring action on a sheaf of base modules. -/
noncomputable abbrev forgetBaseActionFunctor :
    Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k) ⥤
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  sheafCompose (Opens.grothendieckTopology X)
    (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u})

/-- Forgetting the base action after applying `moduleSheafFunctor`
recovers the ordinary underlying abelian sheaf functor. -/
noncomputable def moduleSheafFunctorForgetIso :
    moduleSheafFunctor (k := k) (X := X) ⋙
        forgetBaseActionFunctor (k := k) (X := X) ≅
      Scheme.Modules.toUnderlyingSheaf X :=
  Iso.refl _

noncomputable instance forgetBaseActionFunctor_preservesFiniteLimits :
    PreservesFiniteLimits
      (forgetBaseActionFunctor (k := k) (X := X)) := by
  letI :
      PreservesFiniteLimits
        (forgetBaseActionFunctor (k := k) (X := X) ⋙
          sheafToPresheaf
            (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := by
    change
      PreservesFiniteLimits
        (sheafToPresheaf
            (Opens.grothendieckTopology X) (ModuleCat.{u} k) ⋙
          (Functor.whiskeringRight X.Opensᵒᵖ
            (ModuleCat.{u} k) AddCommGrpCat.{u}).obj
              (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}))
    exact comp_preservesFiniteLimits _ _
  apply preservesFiniteLimits_of_reflects_of_preserves
    (forgetBaseActionFunctor (k := k) (X := X))
    (sheafToPresheaf
      (Opens.grothendieckTopology X) AddCommGrpCat.{u})

noncomputable instance forgetBaseActionFunctor_reflectsFiniteLimits :
    ReflectsFiniteLimits
      (forgetBaseActionFunctor (k := k) (X := X)) := by
  infer_instance

/-- Taking the base-linear sheaf preserves finite limits, in particular
kernels. -/
noncomputable instance moduleSheafFunctor_preservesFiniteLimits :
    PreservesFiniteLimits
      (moduleSheafFunctor (k := k) (X := X)) := by
  letI :
      PreservesFiniteLimits (Scheme.Modules.toUnderlyingSheaf X) :=
    Scheme.Modules.toUnderlyingSheaf_preservesFiniteLimits
  letI :
      PreservesFiniteLimits
        (moduleSheafFunctor (k := k) (X := X) ⋙
          forgetBaseActionFunctor (k := k) (X := X)) := by
    change PreservesFiniteLimits
      (Scheme.Modules.toUnderlyingSheaf X)
    exact Scheme.Modules.toUnderlyingSheaf_preservesFiniteLimits
  exact preservesFiniteLimits_of_reflects_of_preserves
    (moduleSheafFunctor (k := k) (X := X))
    (forgetBaseActionFunctor (k := k) (X := X))

instance moduleSheafFunctor_faithful :
    (moduleSheafFunctor (k := k) (X := X)).Faithful := by
  letI : (Scheme.Modules.toUnderlyingSheaf X).Faithful :=
    Scheme.Modules.toUnderlyingSheaf_faithful
  letI :
      (moduleSheafFunctor (k := k) (X := X) ⋙
        forgetBaseActionFunctor (k := k) (X := X)).Faithful := by
    change (Scheme.Modules.toUnderlyingSheaf X).Faithful
    exact Scheme.Modules.toUnderlyingSheaf_faithful
  exact Functor.Faithful.of_comp
    (moduleSheafFunctor (k := k) (X := X))
    (forgetBaseActionFunctor (k := k) (X := X))

/-- Taking the base-linear sheaf preserves epimorphisms. -/
noncomputable instance moduleSheafFunctor_preservesEpimorphisms :
    (moduleSheafFunctor (k := k) (X := X)).PreservesEpimorphisms := by
  letI : PreservesColimits
      (Scheme.Modules.toUnderlyingSheaf X) :=
    Scheme.Modules.toUnderlyingSheaf_preservesColimits
  letI :
      (Scheme.Modules.toUnderlyingSheaf X).PreservesEpimorphisms :=
    inferInstance
  letI :
      (moduleSheafFunctor (k := k) (X := X) ⋙
        forgetBaseActionFunctor
          (k := k) (X := X)).PreservesEpimorphisms := by
    change
      (Scheme.Modules.toUnderlyingSheaf X).PreservesEpimorphisms
    infer_instance
  letI :
      (forgetBaseActionFunctor (k := k) (X := X)).Faithful :=
    inferInstance
  letI :
      (forgetBaseActionFunctor
        (k := k) (X := X)).ReflectsEpimorphisms :=
    CategoryTheory.Functor.reflectsEpimorphisms_of_faithful _
  exact Functor.preservesEpimorphisms_of_preserves_of_reflects
    (moduleSheafFunctor (k := k) (X := X))
    (forgetBaseActionFunctor (k := k) (X := X))

noncomputable instance moduleSheafFunctor_additive :
    (moduleSheafFunctor (k := k) (X := X)).Additive where
  map_add := by
    intro M N f g
    ext U x
    rfl

noncomputable instance moduleSheafFunctor_preservesHomology :
    (moduleSheafFunctor (k := k) (X := X)).PreservesHomology := by
  letI :
      HasSheafify (Opens.grothendieckTopology X)
        (ModuleCat.{u} k) := by
    infer_instance
  letI :
      Abelian
        (Sheaf (Opens.grothendieckTopology X)
          (ModuleCat.{u} k)) :=
    sheafIsAbelian
  letI :
      (moduleSheafFunctor
        (k := k) (X := X)).PreservesZeroMorphisms :=
    CategoryTheory.Functor.preservesZeroMorphisms_of_additive _
  exact Functor.preservesHomology_of_preservesEpis_and_kernels
    (moduleSheafFunctor (k := k) (X := X))

/-- Taking the base-linear sheaf is exact. -/
noncomputable instance moduleSheafFunctor_preservesFiniteColimits :
    PreservesFiniteColimits
      (moduleSheafFunctor (k := k) (X := X)) := by
  apply Functor.preservesFiniteColimits_of_preservesHomology

/-- An epimorphism of scheme modules remains an epimorphism after
remembering only its base-linear structure. -/
theorem moduleSheafMap_epi {M N : X.Modules} (f : M ⟶ N) [Epi f] :
    Epi (moduleSheafMap (k := k) f) := by
  exact (moduleSheafFunctor (k := k) (X := X)).map_epi f

/-- The base-linear sheaf attached to a kernel is the kernel of the
attached base-linear sheaf morphism. -/
noncomputable def moduleSheafKernelIso {M N : X.Modules} (f : M ⟶ N) :
    moduleSheaf (k := k) (kernel f) ≅
      kernel (moduleSheafMap (k := k) f) :=
  PreservesKernel.iso
    (moduleSheafFunctor (k := k) (X := X)) f

@[reassoc (attr := simp)]
lemma moduleSheafKernelIso_inv_comp_map_ι
    {M N : X.Modules} (f : M ⟶ N) :
    (moduleSheafKernelIso (k := k) f).inv ≫
        moduleSheafMap (k := k) (kernel.ι f) =
      kernel.ι (moduleSheafMap (k := k) f) :=
  PreservesKernel.iso_inv_ι
    (moduleSheafFunctor (k := k) (X := X)) f

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing

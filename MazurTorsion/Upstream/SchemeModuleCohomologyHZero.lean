/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Topology.Sheaves.Abelian

/-!
# Global scalar actions and degree-zero cohomology of scheme modules

This file connects Mathlib's actual category of modules on a scheme to its
Ext-based sheaf cohomology.  The underlying abelian sheaf is supplied by the
existing functor `SheafOfModules.toSheaf`; no parallel sheaf or cohomology
notion is introduced.

For a module `M` on a scheme `X`, `zariskiFunctor X n` evaluates
`CategoryTheory.Sheaf.functorH` on the Zariski opens site.  In degree zero,
Mathlib's `CategoryTheory.Sheaf.H.equiv₀` identifies this group with the
genuine sections `Γ(M, ⊤)`.  We record its naturality for an actual module
morphism.  The separate `SchemeModuleCohomologyAffine` module consumes this
interface for affine tilde modules.

Mathlib's cohomology functor uses the underlying abelian sheaf, so it does not
directly retain the action of `Γ(X, ⊤)`.  Multiplication by a global function
is nevertheless an actual endomorphism of every scheme module.  Applying the
cohomology functor to these endomorphisms gives a canonical global-functions
action in every degree, independent of a cover or resolution.  The actions are
named definitions rather than global instances, so clients opt into them
without changing scalar inference for arbitrary `Ext` groups.

Nothing here asserts coherence, finite-dimensionality, affine acyclicity, or
vanishing in positive degree.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace
open _root_.AlgebraicGeometry
open scoped AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

/-- Ext-based cohomology of the underlying abelian sheaf of a scheme module,
on the Zariski site of opens. -/
noncomputable def zariskiFunctor (X : Scheme.{u}) (n : ℕ) :
    CategoryTheory.Functor X.Modules AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf X.ringCatSheaf ⋙
    CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n

noncomputable instance (X : Scheme.{u}) (n : ℕ) :
    (zariskiFunctor X n).Additive := by
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  let G := CategoryTheory.Sheaf.functorH
    (Opens.grothendieckTopology X) n
  change (F ⋙ G).Additive
  constructor
  intro M N f g
  change G.map (F.map (f + g)) = G.map (F.map f) + G.map (F.map g)
  rw [F.map_add, G.map_add]

/-- The degree-`n` Zariski sheaf cohomology group of a module on a scheme. -/
abbrev H {X : Scheme.{u}} (M : X.Modules) (n : ℕ) : Type u :=
  (zariskiFunctor X n).obj M

private def restrictGlobal {X : Scheme.{u}} (r : Γ(X, ⊤))
    (U : (Opens X)ᵒᵖ) : X.ringCatSheaf.obj.obj U :=
  X.presheaf.map
    (homOfLE (show U.unop ≤ ⊤ from le_top)).op r

private def globalSmulLinearMap {X : Scheme.{u}} (M : X.Modules)
    (U : (Opens X)ᵒᵖ) (r : Γ(X, ⊤)) : M.val.obj U ⟶ M.val.obj U :=
  ModuleCat.ofHom
    { toFun := fun x ↦ restrictGlobal r U • x
      map_add' := fun x y ↦ smul_add _ x y
      map_smul' := fun a x ↦ by
        letI : CommRing (X.ringCatSheaf.obj.obj U) :=
          inferInstanceAs (CommRing (X.presheaf.obj U))
        simpa only [RingHom.id_apply, smul_smul] using
          congrArg (fun b : X.ringCatSheaf.obj.obj U ↦ b • x)
            (mul_comm (restrictGlobal r U) a) }

/-- Multiplication by a global function, as an actual endomorphism of a
scheme module.  On every open it is multiplication by the restriction of the
global function. -/
def globalSmulHom {X : Scheme.{u}} (M : X.Modules) (r : Γ(X, ⊤)) : M ⟶ M where
  val :=
    { app := fun U ↦ globalSmulLinearMap M U r
      naturality := by
        intro U V i
        ext x
        change restrictGlobal r V • M.val.map i x =
          M.val.map i (restrictGlobal r U • x)
        rw [M.val.map_smul]
        congr 1
        unfold restrictGlobal
        change X.presheaf.map _ r =
          X.presheaf.map i (X.presheaf.map _ r)
        rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
        apply ConcreteCategory.congr_hom
        exact X.presheaf.congr_map (Subsingleton.elim _ _) }

private theorem globalSmulHom_zero {X : Scheme.{u}} (M : X.Modules) :
    globalSmulHom M 0 = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  change restrictGlobal 0 U • x = 0
  rw [restrictGlobal, map_zero]
  exact (M.val.obj U).isModule.zero_smul x

private theorem globalSmulHom_one {X : Scheme.{u}} (M : X.Modules) :
    globalSmulHom M 1 = 𝟙 M := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  change restrictGlobal 1 U • x = x
  rw [restrictGlobal, map_one]
  exact (M.val.obj U).isModule.one_smul x

private theorem globalSmulHom_add {X : Scheme.{u}} (M : X.Modules)
    (r s : Γ(X, ⊤)) :
    globalSmulHom M (r + s) = globalSmulHom M r + globalSmulHom M s := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  change restrictGlobal (r + s) U • x =
    restrictGlobal r U • x + restrictGlobal s U • x
  rw [restrictGlobal, map_add]
  exact (M.val.obj U).isModule.add_smul _ _ x

private theorem globalSmulHom_mul {X : Scheme.{u}} (M : X.Modules)
    (r s : Γ(X, ⊤)) :
    globalSmulHom M (r * s) = globalSmulHom M s ≫ globalSmulHom M r := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  change restrictGlobal (r * s) U • x =
    restrictGlobal r U • (restrictGlobal s U • x)
  rw [restrictGlobal, map_mul]
  exact (M.val.obj U).isModule.mul_smul _ _ x

/-- The canonical action of global functions on genuine Ext-based sheaf
cohomology.  A scalar acts by applying cohomology to the corresponding
endomorphism of the coefficient module. -/
noncomputable def globalSectionsCohomologyAction {X : Scheme.{u}}
    (M : X.Modules) (n : ℕ) : Γ(X, ⊤) →+* End ((zariskiFunctor X n).obj M) where
  toFun r := (zariskiFunctor X n).map (globalSmulHom M r)
  map_zero' := by rw [globalSmulHom_zero, Functor.map_zero]
  map_one' := by
    rw [globalSmulHom_one]
    simpa only [CategoryTheory.End.one_def] using
      (zariskiFunctor X n).map_id M
  map_add' r s := by rw [globalSmulHom_add, Functor.map_add]
  map_mul' r s := by
    rw [globalSmulHom_mul]
    simpa only [CategoryTheory.End.mul_def] using
      (zariskiFunctor X n).map_comp
        (globalSmulHom M s) (globalSmulHom M r)

/-- The canonical `Γ(X, ⊤)`-module structure on genuine sheaf cohomology
in every degree.  Unlike the older Cech-transported action, this definition
does not depend on an affine cover. -/
@[reducible]
noncomputable def globalSectionsCohomologyModule {X : Scheme.{u}}
    (M : X.Modules) (n : ℕ) : Module Γ(X, ⊤) (H M n) := by
  change Module Γ(X, ⊤)
    (ModuleCat.mkOfSMul' (globalSectionsCohomologyAction M n))
  infer_instance

/-- The canonical cohomology action evaluates to the cohomology map induced
by multiplication on the coefficient module. -/
theorem globalSectionsCohomologyModule_smul {X : Scheme.{u}}
    (M : X.Modules) (n : ℕ) (r : Γ(X, ⊤)) (x : H M n) :
    letI := globalSectionsCohomologyModule M n
    r • x = (zariskiFunctor X n).map (globalSmulHom M r) x := by
  rfl

/-- Multiplication by a global function commutes with every morphism of
scheme modules. -/
theorem globalSmulHom_naturality {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (r : Γ(X, ⊤)) :
    globalSmulHom M r ≫ f = f ≫ globalSmulHom N r := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  change f.val.app U (restrictGlobal r U • x) =
    restrictGlobal r U • f.val.app U x
  exact (f.val.app U).hom.map_smul (restrictGlobal r U) x

/-- Cohomology maps induced by actual morphisms of scheme modules are linear
for the canonical global-functions actions. -/
noncomputable def cohomologyLinearMap {X : Scheme.{u}} {M N : X.Modules}
    (n : ℕ) (f : M ⟶ N) :
    letI := globalSectionsCohomologyModule M n
    letI := globalSectionsCohomologyModule N n
    H M n →ₗ[Γ(X, ⊤)] H N n := by
  letI := globalSectionsCohomologyModule M n
  letI := globalSectionsCohomologyModule N n
  refine
    { toFun := (zariskiFunctor X n).map f
      map_add' := ((zariskiFunctor X n).map f).hom.map_add
      map_smul' := ?_ }
  intro r x
  change (zariskiFunctor X n).map f
      ((zariskiFunctor X n).map (globalSmulHom M r) x) =
    (zariskiFunctor X n).map (globalSmulHom N r)
      ((zariskiFunctor X n).map f x)
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    globalSmulHom_naturality, Functor.map_comp,
    ConcreteCategory.comp_apply]

/-- Degree-zero cohomology is the actual group of global sections at the top
open of the scheme. -/
noncomputable def hZeroEquivGlobalSections {X : Scheme.{u}}
    (M : X.Modules) : H M 0 ≃+ Γ(M, ⊤) :=
  CategoryTheory.Sheaf.H.equiv₀
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)
    (Limits.isTerminalTop : Limits.IsTerminal (⊤ : Opens X))

/-- The degree-zero/global-sections equivalence commutes with an actual
morphism of scheme modules. -/
theorem hZeroEquivGlobalSections_naturality {X : Scheme.{u}}
    {M N : X.Modules} (f : M ⟶ N) (x : H M 0) :
    f.app ⊤ (hZeroEquivGlobalSections M x) =
      hZeroEquivGlobalSections N ((zariskiFunctor X 0).map f x) :=
  CategoryTheory.Sheaf.H.equiv₀_naturality
    (Limits.isTerminalTop : Limits.IsTerminal (⊤ : Opens X))
    ((SheafOfModules.toSheaf X.ringCatSheaf).map f) x

/-- The `Γ(X, ⊤)`-module structure on degree-zero cohomology transported
from genuine global sections.  It is named, not registered globally, because
the underlying Ext group also carries native scalar structures coming from
linearity of its ambient abelian-sheaf category. -/
@[reducible]
noncomputable def hZeroModule {X : Scheme.{u}} (M : X.Modules) :
    Module Γ(X, ⊤) (H M 0) :=
  (hZeroEquivGlobalSections M).module Γ(X, ⊤)

/-- With the explicit transported action, the degree-zero/global-sections
comparison is linear over the ring of global functions. -/
noncomputable def hZeroLinearEquivGlobalSections {X : Scheme.{u}}
    (M : X.Modules) :
    letI := hZeroModule M
    H M 0 ≃ₗ[Γ(X, ⊤)] Γ(M, ⊤) :=
  letI := hZeroModule M
  (hZeroEquivGlobalSections M).linearEquiv Γ(X, ⊤)

/-- A morphism of scheme modules acts linearly on global sections.  This is
the target-side map in the linear naturality square for degree-zero
cohomology. -/
def globalSectionsLinearMap {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) : Γ(M, ⊤) →ₗ[Γ(X, ⊤)] Γ(N, ⊤) :=
  (f.val.app (.op (⊤ : Opens X))).hom

/-- The actual degree-zero cohomology map, bundled linearly using the
transported global-functions actions. -/
noncomputable def hZeroLinearMap {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) :
    letI := hZeroModule M
    letI := hZeroModule N
    H M 0 →ₗ[Γ(X, ⊤)] H N 0 := by
  letI := hZeroModule M
  letI := hZeroModule N
  exact (hZeroLinearEquivGlobalSections N).symm.toLinearMap.comp
    ((globalSectionsLinearMap f).comp
      (hZeroLinearEquivGlobalSections M).toLinearMap)

/-- The bundled linear map has the same underlying function as Mathlib's
Ext-based degree-zero cohomology functor. -/
theorem hZeroLinearMap_apply {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (x : H M 0) :
    letI := hZeroModule M
    letI := hZeroModule N
    hZeroLinearMap f x = (zariskiFunctor X 0).map f x := by
  letI := hZeroModule M
  letI := hZeroModule N
  simp only [hZeroLinearMap, LinearMap.comp_apply]
  apply (hZeroLinearEquivGlobalSections N).toEquiv.symm_apply_eq.mpr
  change f.app ⊤ (hZeroEquivGlobalSections M x) =
    hZeroEquivGlobalSections N ((zariskiFunctor X 0).map f x)
  exact hZeroEquivGlobalSections_naturality f x

/-- The degree-zero/global-sections linear equivalence is natural for actual
morphisms of scheme modules. -/
theorem hZeroLinearEquivGlobalSections_naturality {X : Scheme.{u}}
    {M N : X.Modules} (f : M ⟶ N) (x : H M 0) :
    letI := hZeroModule M
    letI := hZeroModule N
    globalSectionsLinearMap f (hZeroLinearEquivGlobalSections M x) =
      hZeroLinearEquivGlobalSections N (hZeroLinearMap f x) := by
  rw [hZeroLinearMap_apply]
  exact hZeroEquivGlobalSections_naturality f x

end MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

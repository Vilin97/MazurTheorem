/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Topology.Sheaves.Abelian

/-!
# Degree-zero cohomology of scheme modules

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

Mathlib also has a native scalar action on `Ext` when the entire ambient
abelian category is linear over the scalar ring.  Here the cohomology functor
uses the underlying abelian sheaf, so that construction supplies the canonical
integer action but does not retain the action of `Γ(X, ⊤)`.  In degree zero
we transport the existing module structure on global sections back across
`hZeroEquivGlobalSections`.  This transported structure is deliberately a
named definition rather than a global instance: clients opt into exactly this
degree-zero action, without changing scalar inference for arbitrary `Ext`
groups.

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

/-- The degree-`n` Zariski sheaf cohomology group of a module on a scheme. -/
abbrev H {X : Scheme.{u}} (M : X.Modules) (n : ℕ) : Type u :=
  (zariskiFunctor X n).obj M

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
@[instance_reducible]
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

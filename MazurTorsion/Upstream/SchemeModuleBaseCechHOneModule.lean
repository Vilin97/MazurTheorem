/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import Mathlib.Algebra.Module.TransferInstance
import MazurTorsion.Upstream.SchemeModuleBaseCechHOneComparison

/-!
# A base-module structure on genuine sheaf H¹

An affine-cover Cech comparison identifies native base-Cech degree-one
homology with genuine Ext-based sheaf `H¹` after forgetting scalars. This file
transports the global-functions action across that additive equivalence and
records the resulting linear comparison.

The action is explicit and depends on the chosen affine cover; it is not
registered as a global instance. Properness and finite generation are
separate inputs consumed downstream.
-/

noncomputable section

universe u

open _root_.AlgebraicGeometry CategoryTheory TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules

namespace MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

/-- The underlying type of genuine Ext-based degree-one sheaf cohomology. -/
abbrev GenuineSheafHOne
    {X : Scheme.{u}} (M : X.Modules) :=
  (CategoryTheory.Sheaf.functorH
    (Opens.grothendieckTopology X) 1).obj M.sheaf

/-- The underlying module type of native base-Cech degree-one homology. -/
abbrev NativeBaseCechHOne
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) :=
  (baseCechComplex π M U).homology 1

/-- Internal dependent package sharing the transported module instance with
the linear comparison definitionally. -/
private structure GenuineSheafHOneBaseModuleData
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) where
  module : Module Γ(S, (⊤ : S.Opens)) (GenuineSheafHOne M)
  linearEquiv :
    letI := module
    GenuineSheafHOne M ≃ₗ[Γ(S, (⊤ : S.Opens))] NativeBaseCechHOne π M U

private noncomputable def genuineSheafHOneBaseModuleData_of_affineOpenCover
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    [M.IsQuasicoherent] {ι : Type u} (U : ι → X.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i)) :
    GenuineSheafHOneBaseModuleData π M U := by
  let e : GenuineSheafHOne M ≃+ NativeBaseCechHOne π M U :=
    (nativeBaseCechHOneForgetIsoOfAffineOpenCover
      π M U hU hUaff).addCommGroupIsoToAddEquiv.symm
  let hmodule : Module Γ(S, (⊤ : S.Opens)) (GenuineSheafHOne M) :=
    e.module Γ(S, (⊤ : S.Opens))
  exact
    { module := hmodule
      linearEquiv := e.linearEquiv Γ(S, (⊤ : S.Opens)) }

/-- The global-functions module on genuine sheaf `H¹` transported from
native base-Cech homology through a chosen affine-cover comparison. -/
@[instance_reducible]
noncomputable def genuineSheafHOneBaseModuleOfAffineOpenCover
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    [M.IsQuasicoherent] {ι : Type u} (U : ι → X.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i)) :
    Module Γ(S, (⊤ : S.Opens)) (GenuineSheafHOne M) :=
  (genuineSheafHOneBaseModuleData_of_affineOpenCover
    π M U hU hUaff).module

/-- The affine-cover Cech/sheaf comparison is linear for the explicitly
transported global-functions action on genuine sheaf `H¹`. -/
noncomputable def genuineSheafHOneLinearEquivNativeBaseCechOfAffineOpenCover
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    [M.IsQuasicoherent] {ι : Type u} (U : ι → X.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i)) :
    letI := genuineSheafHOneBaseModuleOfAffineOpenCover
      π M U hU hUaff
    GenuineSheafHOne M ≃ₗ[Γ(S, (⊤ : S.Opens))] NativeBaseCechHOne π M U :=
  (genuineSheafHOneBaseModuleData_of_affineOpenCover
    π M U hU hUaff).linearEquiv

end MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

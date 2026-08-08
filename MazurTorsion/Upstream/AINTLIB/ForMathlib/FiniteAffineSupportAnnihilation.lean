/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

Adapted from the Apache-licensed `FiniteAffineSupportAnnihilation.lean`
in Vilin97/Clawristotle.
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.FiniteFamilySupportAnnihilation
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleSupport
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
# Uniform support annihilation on a finite affine cover

Global containment of a finite-type quasicoherent module's closed stalk
support in an ideal-sheaf support yields one ideal power annihilating the
module on every member of a finite affine cover.
-/

open CategoryTheory TopologicalSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme

/-- The affine open represented by a member of the canonical finite affine subcover. -/
def finiteAffineSubcoverAffineOpen (X : Scheme.{u}) [CompactSpace X]
    (i : X.affineCover.finiteSubcover.I₀) : X.affineOpens :=
  ⟨(X.affineCover.finiteSubcover.f i).opensRange,
    isAffineOpen_opensRange (X.affineCover.finiteSubcover.f i)⟩

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

private abbrev restrictFromSpec (F : X.Modules) (U : X.affineOpens) :
    (Spec Γ(X, U)).Modules :=
  @Scheme.Modules.restrict _ _ F U.2.fromSpec
    (IsAffineOpen.isOpenImmersion_fromSpec U.2)

/-- Global closed support containment implies affine module-support containment. -/
theorem moduleSupport_restrictFromSpec_subset_zeroLocus
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (J : X.IdealSheafData)
    (hSupport : closedStalkSupport F ≤ J.support)
    (U : X.affineOpens) :
    Module.support Γ(X, U)
        (moduleSpecΓFunctor.obj (restrictFromSpec F U)) ⊆
      PrimeSpectrum.zeroLocus (J.ideal U) := by
  letI : IsOpenImmersion U.2.fromSpec :=
    IsAffineOpen.isOpenImmersion_fromSpec U.2
  intro p hp
  have hpRestricted :
      p ∈ stalkSupport (restrictFromSpec F U) := by
    rw [stalkSupport_eq_moduleSupport_of_spectrum]
    exact hp
  have hpGlobal : U.2.fromSpec p ∈ stalkSupport F := by
    have hpPreimage : p ∈ U.2.fromSpec ⁻¹' stalkSupport F := by
      rw [preimage_stalkSupport_of_openImmersion]
      exact hpRestricted
    exact hpPreimage
  have hpClosed : U.2.fromSpec p ∈ closedStalkSupport F := by
    change U.2.fromSpec p ∈ (closedStalkSupport F : Set X)
    rw [coe_closedStalkSupport_eq_stalkSupport F]
    exact hpGlobal
  have hpIdeal : U.2.fromSpec p ∈ J.support :=
    hSupport hpClosed
  have hpU : U.2.fromSpec p ∈ U.1 := by
    change U.2.fromSpec p ∈ (U.1 : Set X)
    rw [← U.2.range_fromSpec]
    exact ⟨p, rfl⟩
  have hpZero :
      U.2.fromSpec p ∈ X.zeroLocus (U := U.1) (J.ideal U) :=
    (J.mem_support_iff_of_mem hpU).mp hpIdeal
  rw [← U.2.fromSpec_preimage_zeroLocus]
  exact hpZero

/-- A finite affine family has one ideal power annihilating every restricted module. -/
theorem exists_uniform_pow_isTorsionBySet_on_finiteAffineFamily
    [IsNoetherian X]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (J : X.IdealSheafData)
    (hSupport : closedStalkSupport F ≤ J.support)
    {ι : Type v} [Finite ι] (U : ι → X.affineOpens) :
    ∃ n : ℕ, ∀ i,
      Module.IsTorsionBySet Γ(X, (U i).1)
        (moduleSpecΓFunctor.obj (restrictFromSpec F (U i)))
        (((J.ideal (U i)) ^ n : Ideal Γ(X, (U i).1)) :
          Set Γ(X, (U i).1)) := by
  letI hfinite :
      ∀ i, Module.Finite Γ(X, (U i).1)
        (moduleSpecΓFunctor.obj (restrictFromSpec F (U i))) :=
    fun i ↦ by
      letI : IsOpenImmersion (U i).2.fromSpec :=
        IsAffineOpen.isOpenImmersion_fromSpec (U i).2
      letI : (restrictFromSpec F (U i)).IsFiniteType := by
        change (F.restrict (U i).2.fromSpec).IsFiniteType
        exact isFiniteType_restrict_fromSpec F (U i).1 (U i).2
      change Module.Finite Γ(X, (U i).1)
        Γ(restrictFromSpec F (U i), ⊤)
      exact
        globalSections_module_finite_of_isFiniteType
          (restrictFromSpec F (U i))
  letI hnoetherian : ∀ i, IsNoetherianRing Γ(X, (U i).1) :=
    fun i ↦ IsLocallyNoetherian.component_noetherian (U i)
  apply
    Module.exists_uniform_pow_isTorsionBySet_of_support_subset_zeroLocus
      (fun i ↦ Γ(X, (U i).1))
      (fun i ↦ moduleSpecΓFunctor.obj (restrictFromSpec F (U i)))
      (fun i ↦ J.ideal (U i))
  intro i
  exact moduleSupport_restrictFromSpec_subset_zeroLocus F J hSupport (U i)

/-- Positive-exponent form of uniform annihilation on a finite affine family. -/
theorem exists_uniform_succ_pow_isTorsionBySet_on_finiteAffineFamily
    [IsNoetherian X]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (J : X.IdealSheafData)
    (hSupport : closedStalkSupport F ≤ J.support)
    {ι : Type v} [Finite ι] (U : ι → X.affineOpens) :
    ∃ n : ℕ, ∀ i,
      Module.IsTorsionBySet Γ(X, (U i).1)
        (moduleSpecΓFunctor.obj (restrictFromSpec F (U i)))
        (((J.ideal (U i)) ^ (n + 1) : Ideal Γ(X, (U i).1)) :
          Set Γ(X, (U i).1)) := by
  letI hfinite :
      ∀ i, Module.Finite Γ(X, (U i).1)
        (moduleSpecΓFunctor.obj (restrictFromSpec F (U i))) :=
    fun i ↦ by
      letI : IsOpenImmersion (U i).2.fromSpec :=
        IsAffineOpen.isOpenImmersion_fromSpec (U i).2
      letI : (restrictFromSpec F (U i)).IsFiniteType := by
        change (F.restrict (U i).2.fromSpec).IsFiniteType
        exact isFiniteType_restrict_fromSpec F (U i).1 (U i).2
      change Module.Finite Γ(X, (U i).1)
        Γ(restrictFromSpec F (U i), ⊤)
      exact
        globalSections_module_finite_of_isFiniteType
          (restrictFromSpec F (U i))
  letI hnoetherian : ∀ i, IsNoetherianRing Γ(X, (U i).1) :=
    fun i ↦ IsLocallyNoetherian.component_noetherian (U i)
  apply
    Module.exists_uniform_succ_pow_isTorsionBySet_of_support_subset_zeroLocus
      (fun i ↦ Γ(X, (U i).1))
      (fun i ↦ moduleSpecΓFunctor.obj (restrictFromSpec F (U i)))
      (fun i ↦ J.ideal (U i))
  intro i
  exact moduleSupport_restrictFromSpec_subset_zeroLocus F J hSupport (U i)

/-- Uniform annihilation on the canonical finite affine subcover. -/
theorem exists_uniform_pow_isTorsionBySet_on_finiteAffineSubcover
    [IsNoetherian X]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (J : X.IdealSheafData)
    (hSupport : closedStalkSupport F ≤ J.support) :
    ∃ n : ℕ,
      ∀ i : X.affineCover.finiteSubcover.I₀,
        Module.IsTorsionBySet
          Γ(X, (Scheme.finiteAffineSubcoverAffineOpen X i).1)
          (moduleSpecΓFunctor.obj
            (restrictFromSpec F
              (Scheme.finiteAffineSubcoverAffineOpen X i)))
          (((J.ideal (Scheme.finiteAffineSubcoverAffineOpen X i)) ^ n :
              Ideal Γ(X, (Scheme.finiteAffineSubcoverAffineOpen X i).1)) :
            Set Γ(X, (Scheme.finiteAffineSubcoverAffineOpen X i).1)) :=
  exists_uniform_pow_isTorsionBySet_on_finiteAffineFamily
    F J hSupport (fun i ↦ Scheme.finiteAffineSubcoverAffineOpen X i)

/-- Positive uniform annihilation on the canonical finite affine subcover. -/
theorem exists_uniform_succ_pow_isTorsionBySet_on_finiteAffineSubcover
    [IsNoetherian X]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (J : X.IdealSheafData)
    (hSupport : closedStalkSupport F ≤ J.support) :
    ∃ n : ℕ,
      ∀ i : X.affineCover.finiteSubcover.I₀,
        Module.IsTorsionBySet
          Γ(X, (Scheme.finiteAffineSubcoverAffineOpen X i).1)
          (moduleSpecΓFunctor.obj
            (restrictFromSpec F
              (Scheme.finiteAffineSubcoverAffineOpen X i)))
          (((J.ideal
              (Scheme.finiteAffineSubcoverAffineOpen X i)) ^ (n + 1) :
              Ideal Γ(X, (Scheme.finiteAffineSubcoverAffineOpen X i).1)) :
            Set Γ(X, (Scheme.finiteAffineSubcoverAffineOpen X i).1)) :=
  exists_uniform_succ_pow_isTorsionBySet_on_finiteAffineFamily
    F J hSupport (fun i ↦ Scheme.finiteAffineSubcoverAffineOpen X i)

end AlgebraicGeometry.Scheme.Modules

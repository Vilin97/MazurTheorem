/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteFamilySupportAnnihilation
import MazurTorsion.Upstream.CoherentCohomologyFinite.ModuleSupport
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Uniform support annihilation on a finite affine family

If the closed stalk support of a finite-type quasicoherent module is
contained in the support of an ideal sheaf, then on any finite family of
affine opens one power of the local ideals annihilates all corresponding
affine modules of sections.
-/

open CategoryTheory TopologicalSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme

/-- The affine open of `X` represented by a member of its chosen finite
affine subcover. -/
def finiteAffineSubcoverAffineOpen (X : Scheme.{u}) [CompactSpace X]
    (i : X.affineCover.finiteSubcover.I₀) : X.affineOpens :=
  ⟨(X.affineCover.finiteSubcover.f i).opensRange,
    isAffineOpen_opensRange (X.affineCover.finiteSubcover.f i)⟩

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/--
Global containment of closed stalk support in the support of an ideal
sheaf implies the corresponding affine module-support containment.
-/
theorem moduleSupport_restrictFromSpec_subset_zeroLocus
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (J : X.IdealSheafData)
    (hSupport : closedStalkSupport F ≤ J.support)
    (U : X.affineOpens) :
    Module.support Γ(X, U)
        (moduleSpecΓFunctor.obj
          (F.restrict (isAffineOpen_coe U).fromSpec)) ⊆
      PrimeSpectrum.zeroLocus (J.ideal U) := by
  intro p hp
  have hpRestricted :
      p ∈ stalkSupport
        (F.restrict (isAffineOpen_coe U).fromSpec) := by
    rw [stalkSupport_eq_moduleSupport_of_spectrum]
    exact hp
  have hpGlobal :
      (isAffineOpen_coe U).fromSpec p ∈ stalkSupport F := by
    have hpPreimage :
        p ∈ (isAffineOpen_coe U).fromSpec ⁻¹' stalkSupport F := by
      rw [preimage_stalkSupport_of_openImmersion]
      exact hpRestricted
    exact hpPreimage
  have hpClosed :
      (isAffineOpen_coe U).fromSpec p ∈ closedStalkSupport F := by
    change
      (isAffineOpen_coe U).fromSpec p ∈
        (closedStalkSupport F : Set X)
    rw [coe_closedStalkSupport_eq_stalkSupport F]
    exact hpGlobal
  have hpIdeal : (isAffineOpen_coe U).fromSpec p ∈ J.support :=
    hSupport hpClosed
  have hpU : (isAffineOpen_coe U).fromSpec p ∈ U.1 := by
    change (isAffineOpen_coe U).fromSpec p ∈ (U.1 : Set X)
    rw [← (isAffineOpen_coe U).range_fromSpec]
    exact ⟨p, rfl⟩
  have hpZero :
      (isAffineOpen_coe U).fromSpec p ∈
        X.zeroLocus (U := U.1) (J.ideal U) :=
    (J.mem_support_iff_of_mem hpU).mp hpIdeal
  rw [← (isAffineOpen_coe U).fromSpec_preimage_zeroLocus]
  exact hpZero

/--
On a finite affine family, a single power of the local ideal sheaf
annihilates every restricted affine module.
-/
theorem exists_uniform_pow_isTorsionBySet_on_finiteAffineFamily
    [IsNoetherian X]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (J : X.IdealSheafData)
    (hSupport : closedStalkSupport F ≤ J.support)
    {ι : Type v} [Finite ι] (U : ι → X.affineOpens) :
    ∃ n : ℕ, ∀ i,
      Module.IsTorsionBySet Γ(X, (U i).1)
        (moduleSpecΓFunctor.obj
          (F.restrict (isAffineOpen_coe (U i)).fromSpec))
        ((((J.ideal (U i)) ^ n :
          Ideal Γ(X, (U i).1))) :
            Set Γ(X, (U i).1)) := by
  letI hfinite :
      ∀ i, Module.Finite Γ(X, (U i).1)
        (moduleSpecΓFunctor.obj
          (F.restrict (isAffineOpen_coe (U i)).fromSpec)) :=
    fun i =>
      finite_top_sections_of_isFiniteType_isQuasicoherent
        (F.restrict (isAffineOpen_coe (U i)).fromSpec)
  letI hnoetherian :
      ∀ i, IsNoetherianRing Γ(X, (U i).1) :=
    fun i => IsLocallyNoetherian.component_noetherian (U i)
  apply
    Module.exists_uniform_pow_isTorsionBySet_of_support_subset_zeroLocus
      (fun i => Γ(X, (U i).1))
      (fun i =>
        moduleSpecΓFunctor.obj
          (F.restrict (isAffineOpen_coe (U i)).fromSpec))
      (fun i => J.ideal (U i))
  intro i
  exact
    moduleSupport_restrictFromSpec_subset_zeroLocus
      F J hSupport (U i)

/--
Positive-exponent form of uniform annihilation on a finite affine
family.  This is the form used to pass to an ideal-sheaf power without
changing its support.
-/
theorem exists_uniform_succ_pow_isTorsionBySet_on_finiteAffineFamily
    [IsNoetherian X]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (J : X.IdealSheafData)
    (hSupport : closedStalkSupport F ≤ J.support)
    {ι : Type v} [Finite ι] (U : ι → X.affineOpens) :
    ∃ n : ℕ, ∀ i,
      Module.IsTorsionBySet Γ(X, (U i).1)
        (moduleSpecΓFunctor.obj
          (F.restrict (isAffineOpen_coe (U i)).fromSpec))
        ((((J.ideal (U i)) ^ (n + 1) :
          Ideal Γ(X, (U i).1))) :
            Set Γ(X, (U i).1)) := by
  letI hfinite :
      ∀ i, Module.Finite Γ(X, (U i).1)
        (moduleSpecΓFunctor.obj
          (F.restrict (isAffineOpen_coe (U i)).fromSpec)) :=
    fun i =>
      finite_top_sections_of_isFiniteType_isQuasicoherent
        (F.restrict (isAffineOpen_coe (U i)).fromSpec)
  letI hnoetherian :
      ∀ i, IsNoetherianRing Γ(X, (U i).1) :=
    fun i => IsLocallyNoetherian.component_noetherian (U i)
  apply
    Module.exists_uniform_succ_pow_isTorsionBySet_of_support_subset_zeroLocus
      (fun i => Γ(X, (U i).1))
      (fun i =>
        moduleSpecΓFunctor.obj
          (F.restrict (isAffineOpen_coe (U i)).fromSpec))
      (fun i => J.ideal (U i))
  intro i
  exact
    moduleSupport_restrictFromSpec_subset_zeroLocus
      F J hSupport (U i)

/--
Specialization to the canonical finite affine subcover of a Noetherian
scheme.
-/
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
            (F.restrict
              (isAffineOpen_coe
                (Scheme.finiteAffineSubcoverAffineOpen X i)).fromSpec))
          ((((J.ideal
              (Scheme.finiteAffineSubcoverAffineOpen X i)) ^ n :
                Ideal
                  Γ(X,
                    (Scheme.finiteAffineSubcoverAffineOpen X i).1))) :
              Set
                Γ(X,
                  (Scheme.finiteAffineSubcoverAffineOpen X i).1)) := by
  exact
    exists_uniform_pow_isTorsionBySet_on_finiteAffineFamily
      F J hSupport
      (fun i => Scheme.finiteAffineSubcoverAffineOpen X i)

/--
Positive-exponent specialization to the canonical finite affine
subcover of a Noetherian scheme.
-/
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
            (F.restrict
              (isAffineOpen_coe
                (Scheme.finiteAffineSubcoverAffineOpen X i)).fromSpec))
          ((((J.ideal
              (Scheme.finiteAffineSubcoverAffineOpen X i)) ^ (n + 1) :
                Ideal
                  Γ(X,
                    (Scheme.finiteAffineSubcoverAffineOpen X i).1))) :
              Set
                Γ(X,
                  (Scheme.finiteAffineSubcoverAffineOpen X i).1)) := by
  exact
    exists_uniform_succ_pow_isTorsionBySet_on_finiteAffineFamily
      F J hSupport
      (fun i => Scheme.finiteAffineSubcoverAffineOpen X i)

end AlgebraicGeometry.Scheme.Modules

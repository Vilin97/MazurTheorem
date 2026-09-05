/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleQuasicoherent
import MazurTorsion.Upstream.ProperCurveCohomologyFinite
import MazurTorsion.Upstream.SchemeModuleBaseCechHZeroComparison

/-!
# Finite degree-zero cohomology over a proper base

This file isolates the degree-zero finiteness input needed by the future
support-decreasing coherent-comodel construction.  The design boundary is
the finiteness of the module of global sections over the global-function
ring: properness makes that ring finite over the ground field, and no
coherence hypothesis is otherwise needed here.

The first named downstream consumer is a finite free sheaf.  The second is
any module admitting a monomorphism into a finite free sheaf.  Such coherent
free lattices are the `H⁰`-finite sources expected in the proper-curve
generic-generator construction.
-/

noncomputable section

open CategoryTheory
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

universe u

/-- The canonical degree-zero/global-sections comparison is linear after
restricting scalars along an arbitrary base morphism. -/
noncomputable def hZeroBaseSectionsLinearEquivGlobalSections
    {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules) :
    letI := baseSectionsHZeroModule f M
    letI : Module Γ(S, ⊤) Γ(M, ⊤) :=
      Module.compHom Γ(M, ⊤) f.appTop.hom
    H M 0 ≃ₗ[Γ(S, ⊤)] Γ(M, ⊤) := by
  letI : Module Γ(X, ⊤) (H M 0) :=
    globalSectionsCohomologyModule M 0
  letI := baseSectionsHZeroModule f M
  letI : Module Γ(S, ⊤) Γ(M, ⊤) :=
    Module.compHom Γ(M, ⊤) f.appTop.hom
  refine
    { hZeroCanonicalLinearEquivGlobalSections M with
      map_smul' := ?_ }
  intro r x
  exact (hZeroCanonicalLinearEquivGlobalSections M).map_smul
    (f.appTop.hom r) x

/-- Finite global sections over the source global-function ring descend to
finite canonical degree-zero cohomology over a base whose map on global
functions is finite. -/
theorem hZeroBaseSections_finite_of_globalSections_module_finite
    {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules)
    (hf : f.appTop.hom.Finite)
    (hM : Module.Finite Γ(X, ⊤) Γ(M, ⊤)) :
    letI := baseSectionsHZeroModule f M
    Module.Finite Γ(S, ⊤) (H M 0) := by
  let R := Γ(X, (⊤ : X.Opens))
  let B := Γ(S, (⊤ : S.Opens))
  letI : Algebra B R := f.appTop.hom.toAlgebra
  letI : Module.Finite B R := RingHom.finite_algebraMap.mp hf
  letI : Module R Γ(M, ⊤) := inferInstance
  letI : Module.Finite R Γ(M, ⊤) := hM
  letI : Module B Γ(M, ⊤) := Module.compHom Γ(M, ⊤) f.appTop.hom
  letI : IsScalarTower B R Γ(M, ⊤) :=
    IsScalarTower.of_compHom B R Γ(M, ⊤)
  letI : Module.Finite B Γ(M, ⊤) := Module.Finite.trans R Γ(M, ⊤)
  letI := baseSectionsHZeroModule f M
  exact Module.Finite.equiv
    (hZeroBaseSectionsLinearEquivGlobalSections f M).symm

/-- If the global sections of a sheaf are finite over the global-function
ring, then its canonical `H⁰` is finite-dimensional over the ground field
on an integral universally closed finite-type scheme. -/
theorem hZeroCanonical_finiteDimensional_of_globalSections_module_finite
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [UniversallyClosed f] [LocallyOfFiniteType f]
    (M : X.Modules)
    (hM : Module.Finite Γ(X, ⊤) Γ(M, ⊤)) :
    letI := hZeroCanonicalFieldModule K X f M
    FiniteDimensional K (H M 0) := by
  let S := Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens))
  letI : Algebra K S := (Scheme.ΓSpecIso (.of K)).inv.hom.toAlgebra
  letI : Module S (H M 0) := baseSectionsHZeroModule f M
  letI : Module.Finite S (H M 0) :=
    hZeroBaseSections_finite_of_globalSections_module_finite f M
      (finite_appTop_of_universallyClosed K f) hM
  letI := hZeroCanonicalFieldModule K X f M
  letI : IsScalarTower K S (H M 0) :=
    IsScalarTower.of_compHom K S (H M 0)
  have hS : RingHom.Finite (algebraMap K S) := by
    change RingHom.Finite (Scheme.ΓSpecIso (.of K)).inv.hom
    exact (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv.finite
  letI : Module.Finite K S := RingHom.finite_algebraMap.mp hS
  exact Module.Finite.trans S (H M 0)

/-- Canonical `H⁰` of a finite free sheaf on an integral proper scheme is
finite-dimensional.  This is the finite-free target consumed by the future
proper-curve coherent-comodel producer. -/
theorem freeHZeroCanonical_finiteDimensional_of_proper
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f]
    (I : Type u) [Finite I] :
    let M := SheafOfModules.free I (R := X.ringCatSheaf)
    letI := hZeroCanonicalFieldModule K X f M
    FiniteDimensional K (H M 0) := by
  exact hZeroCanonical_finiteDimensional_of_globalSections_module_finite
    K X f (SheafOfModules.free I (R := X.ringCatSheaf))
      (Scheme.Modules.free_globalSections_module_finite X I)

/-- A module which embeds into a finite free sheaf on an integral proper
scheme has finite-dimensional canonical `H⁰`.  Degree-zero cohomology is
identified with global sections, where a monomorphism of sheaves is
sectionwise injective.

The named downstream consumer is the full-support free-lattice reduction in
`ProperCurveFiniteSupportCech`: its geometric producer may construct a
coherent sublattice of a finite free sheaf instead of proving `H⁰`
finiteness separately. -/
theorem hZeroCanonical_finiteDimensional_of_mono_to_free
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f]
    (E : X.Modules) (I : Type u) [Finite I]
    (g : E ⟶ SheafOfModules.free I (R := X.ringCatSheaf)) [Mono g] :
    letI := hZeroCanonicalFieldModule K X f E
    FiniteDimensional K (H E 0) := by
  letI := hZeroCanonicalFieldModule K X f E
  letI := hZeroCanonicalFieldModule K X f
    (SheafOfModules.free I (R := X.ringCatSheaf))
  letI : FiniteDimensional K
      (H (SheafOfModules.free I (R := X.ringCatSheaf)) 0) :=
    freeHZeroCanonical_finiteDimensional_of_proper K X f I
  apply FiniteDimensional.of_injective
    (hZeroCanonicalFieldLinearMap K X f g)
  intro x y hxy
  apply (hZeroCanonicalFieldLinearEquivGlobalSections K X f E).injective
  have happ : Function.Injective (g.app (⊤ : X.Opens)) := by
    haveI : Mono ((Scheme.Modules.toPresheaf X).map g) := by
      exact (inferInstance :
        (Scheme.Modules.toPresheaf X).PreservesMonomorphisms).preserves g
    have hi : Function.Injective
        (((Scheme.Modules.toPresheaf X).map g).app
          (.op (⊤ : X.Opens))) := by
      haveI : Mono (((Scheme.Modules.toPresheaf X).map g).app
          (.op (⊤ : X.Opens))) := by infer_instance
      exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance
    exact hi
  apply happ
  change g.app ⊤ (hZeroEquivGlobalSections E x) =
    g.app ⊤ (hZeroEquivGlobalSections E y)
  have hxy' : (zariskiFunctor X 0).map g x =
      (zariskiFunctor X 0).map g y := hxy
  exact (hZeroEquivGlobalSections_naturality g x).trans <|
    (congrArg (hZeroEquivGlobalSections
      (SheafOfModules.free I (R := X.ringCatSheaf))) hxy').trans <|
      (hZeroEquivGlobalSections_naturality g y).symm

end MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

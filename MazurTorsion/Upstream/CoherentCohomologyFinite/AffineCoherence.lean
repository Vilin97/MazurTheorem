/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleSheaf
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Coherence on an affine scheme

This file isolates the commutative-algebra part of the passage from a
finite-type quasicoherent module to a coherent sheaf.

On an affine scheme, once the canonical counit
`tilde Γ(F) ⟶ F` is known to be an isomorphism, a finite module of global
sections over a Noetherian ring gives a finite presentation of `F`.
The missing geometric inputs are therefore clearly separated:

* identify a quasicoherent sheaf on an affine scheme with the tilde of its
  global sections;
* show that finite type of the sheaf makes the global-section module finite.
-/

open CategoryTheory Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

/--
Let `F` be a module sheaf on `Spec R`. If `R` is Noetherian, the global
sections of `F` are finite, and the affine tilde--global-sections counit is
an isomorphism, then `F` has a finite global presentation.

This is the local algebra engine in the standard proof that a finite-type
quasicoherent sheaf on a locally Noetherian scheme is coherent.
-/
theorem exists_finite_presentation_of_finite_sections
    {R : CommRingCat.{u}} (F : (Spec R).Modules)
    [IsIso (Scheme.Modules.fromTildeΓ F)]
    [IsNoetherianRing (R : Type u)]
    (hfin : Module.Finite (R : Type u) Γ(F, ⊤)) :
    ∃ P : F.Presentation, P.IsFinite := by
  set M₀ : ModuleCat.{u} (R : Type u) :=
    (modulesSpecToSheaf.obj F).presheaf.obj (op (⊤ : (Spec R).Opens))
  haveI : Module.Finite (R : Type u) M₀ := hfin
  obtain ⟨n, w, hw⟩ := Module.Finite.exists_fin (R := (R : Type u)) (M := M₀)
  let s : Set M₀ := Set.range w
  haveI : Finite (↥s) := (Set.finite_range w).to_subtype
  haveI : Module.Finite (R : Type u) (↥s →₀ (R : Type u)) := by
    infer_instance
  haveI : _root_.IsNoetherian (R : Type u) (↥s →₀ (R : Type u)) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  obtain ⟨T, hT⟩ := _root_.IsNoetherian.noetherian
    (Finsupp.linearCombination (R : Type u) (Subtype.val : ↥s → M₀)).ker
  haveI : Finite (↥(T : Set (↥s →₀ (R : Type u)))) :=
    T.finite_toSet.to_subtype
  let P₀ : (tilde M₀).Presentation :=
    presentationTilde M₀ s hw (T : Set (↥s →₀ (R : Type u))) hT
  haveI : P₀.generators.IsFiniteType :=
    { finite := inferInstanceAs (Finite ↥s) }
  haveI : P₀.relations.IsFiniteType :=
    { finite := inferInstanceAs
        (Finite (↥(T : Set (↥s →₀ (R : Type u))))) }
  haveI : P₀.IsFinite :=
    SheafOfModules.Presentation.IsFinite.mk
      (p := P₀) inferInstance inferInstance
  let e : tilde M₀ ≅ F :=
    @asIso _ _ _ _ (Scheme.Modules.fromTildeΓ F) inferInstance
  letI : IsIso e.hom := e.isIso_hom
  letI : Epi e.hom := inferInstance
  letI : Mono e.hom := inferInstance
  let P : F.Presentation :=
    @SheafOfModules.Presentation.ofIsIso.{u}
      _ _ _ _ _ _ _ _ e.hom e.isIso_hom P₀
  refine ⟨P, SheafOfModules.Presentation.IsFinite.mk ?_ ?_⟩
  · constructor
    change Finite ↥s
    infer_instance
  · constructor
    change Finite (↥(T : Set (↥s →₀ (R : Type u))))
    infer_instance

end AlgebraicGeometry.Scheme.Modules

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

universe v

section NoetherianModules

variable {R A B : Type v}
variable [CommRing R]
variable [AddCommGroup A] [Module R A]
variable [AddCommGroup B] [Module R B]

/--
Over a Noetherian ring, the kernel of a linear map out of a finite module is
finite. This is the local algebra closure fact used for kernels of coherent
sheaves.
-/
theorem module_finite_ker_of_noetherian
    [IsNoetherianRing R] [Module.Finite R A] (f : A →ₗ[R] B) :
    Module.Finite R (LinearMap.ker f) := by
  exact Module.Finite.of_fg
    (_root_.IsNoetherian.noetherian (LinearMap.ker f))

/--
The cokernel module of a linear map into a finite module is finite.
No Noetherian hypothesis is required for this quotient closure.
-/
theorem module_finite_coker (f : A →ₗ[R] B) [Module.Finite R B] :
    Module.Finite R (B ⧸ LinearMap.range f) :=
  Module.Finite.of_surjective (Submodule.mkQ (LinearMap.range f))
    (Submodule.mkQ_surjective (LinearMap.range f))

/--
Over a Noetherian ring, every finite module is finitely presented.
-/
theorem module_finitePresentation_of_finite_of_noetherian
    [IsNoetherianRing R] [Module.Finite R A] :
    Module.FinitePresentation R A :=
  Module.finitePresentation_of_finite R A

/--
Finitely presented modules over a Noetherian ring are closed under kernels.
-/
theorem module_finitePresentation_ker_of_noetherian
    [IsNoetherianRing R] [Module.FinitePresentation R A]
    (f : A →ₗ[R] B) :
    Module.FinitePresentation R (LinearMap.ker f) := by
  letI : Module.Finite R (LinearMap.ker f) :=
    module_finite_ker_of_noetherian f
  exact module_finitePresentation_of_finite_of_noetherian

/--
Finitely presented modules over a Noetherian ring are closed under
cokernels.  The statement is phrased using the concrete quotient model of
the cokernel.
-/
theorem module_finitePresentation_coker_of_noetherian
    [IsNoetherianRing R] [Module.FinitePresentation R B]
    (f : A →ₗ[R] B) :
    Module.FinitePresentation R (B ⧸ LinearMap.range f) := by
  letI : Module.Finite R (B ⧸ LinearMap.range f) :=
    module_finite_coker f
  exact module_finitePresentation_of_finite_of_noetherian

end NoetherianModules

end MazurTorsion.AlgebraicGeometry.CoherentCohomology

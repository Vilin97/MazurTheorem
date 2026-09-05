/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleCanonicalSupportThickening
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleOrderedBaseCechPushforward
import MazurTorsion.Upstream.CurveCohomologyGrothendieckVanishing
import MazurTorsion.Upstream.SchemeModuleFinitePushforward
import MazurTorsion.Upstream.SchemeModulePullbackCoherent

/-!
# Finite proper support on a smooth curve

This file isolates the zero-dimensional-support boundary in the proper-curve
cohomology argument. A strict closed subset of a smooth proper integral curve
is finite. Consequently, the canonical support thickening of a coherent
module with strict closed stalk support has finite underlying space.

The downstream chain upgrades that topological finiteness to finiteness of
the thickening's structure morphism, proves its pulled-back model coherent,
and uses finite pushforward over the affine field spectrum to recover finite
global sections of the original strict-support module. No full-support
comparison is asserted here.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry.SchemeWeilDivisor

namespace MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

/-- Every proper closed subset of a smooth proper integral curve has finite
underlying set. Properness supplies the Noetherian hypothesis required by the
relative-curve topology theorem. -/
theorem finite_closed_subset_of_proper_smoothRelativeDimension_one
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (Z : Set X) (hZ : IsClosed Z) (hZne : Z ≠ Set.univ) :
    Z.Finite := by
  letI : IsNoetherian X :=
    isNoetherian_of_proper_smoothRelativeDimension_one K X f
  exact finite_closed_subset_of_smoothRelativeDimension_one
    K X f Z hZ hZne

/-- Strict closed stalk support of a module on a smooth proper integral curve
is a finite set. -/
theorem finite_closedStalkSupport_of_lt_top
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (M : X.Modules) (hM : closedStalkSupport M < ⊤) :
    (closedStalkSupport M : Set X).Finite := by
  apply finite_closed_subset_of_proper_smoothRelativeDimension_one
    K X f _ (closedStalkSupport M).2
  intro htop
  apply hM.ne
  apply Closeds.ext
  simpa using htop

namespace CanonicalSupportThickening

/-- The canonical support thickening of a coherent module with strict support
has finite underlying type. -/
theorem finite_supportScheme_of_closedStalkSupport_lt_top
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent]
    (A : CanonicalSupportThickening M)
    (hM : closedStalkSupport M < ⊤) :
    Finite A.supportScheme := by
  have hsupport : (closedStalkSupport M : Set X).Finite :=
    finite_closedStalkSupport_of_lt_top K X f M hM
  have hrange : (Set.range A.inclusion).Finite := by
    rw [A.range_inclusion]
    exact hsupport
  letI : Finite (Set.range A.inclusion) :=
    Set.finite_coe_iff.mpr hrange
  exact Finite.of_injective
    (fun x : A.supportScheme ↦
      (⟨A.inclusion x, ⟨x, rfl⟩⟩ : Set.range A.inclusion))
    (fun x y hxy ↦ A.inclusion.isClosedEmbedding.injective
      (congrArg (fun z : Set.range A.inclusion ↦ z.1) hxy))

/-- The canonical support thickening of a coherent module with strict support
is finite over the ground field. This is the finite-morphism boundary consumed
by the subsequent global-sections argument. -/
theorem isFinite_comp_structureMap_of_closedStalkSupport_lt_top
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent]
    (A : CanonicalSupportThickening M)
    (hM : closedStalkSupport M < ⊤) :
    IsFinite (A.inclusion ≫ f) := by
  letI : Finite A.supportScheme :=
    finite_supportScheme_of_closedStalkSupport_lt_top K X f M A hM
  letI : LocallyOfFiniteType (A.inclusion ≫ f) := inferInstance
  letI : LocallyQuasiFinite (A.inclusion ≫ f) :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ fun _ ↦
      Set.toFinite _
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

/-- Base-linear global sections of a coherent module with strict support on
a smooth proper integral curve are finite over the global functions of the
ground-field spectrum. -/
theorem baseSections_finite_of_closedStalkSupport_lt_top
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent]
    (A : CanonicalSupportThickening M)
    (hM : closedStalkSupport M < ⊤) :
    Module.Finite Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens))
      (baseSections f M) := by
  let q := A.inclusion ≫ f
  let N := (pushforward q).obj A.modelModule
  letI : IsFinite q :=
    isFinite_comp_structureMap_of_closedStalkSupport_lt_top
      K X f M A hM
  have hModelQuasicoherent : A.modelModule.IsQuasicoherent :=
    A.modelModule_isQuasicoherent
  letI : A.modelModule.IsQuasicoherent := hModelQuasicoherent
  have hModelFinite : A.modelModule.IsFiniteType :=
    A.modelModule_isFiniteType
  letI : A.modelModule.IsFiniteType := hModelFinite
  have hNQuasicoherent : N.IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom q
  letI : N.IsQuasicoherent := hNQuasicoherent
  have hNFinite : N.IsFiniteType :=
    isFiniteType_pushforward_of_isFinite q
  letI : N.IsFiniteType := hNFinite
  have hSections :
      Module.Finite Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens))
        Γ(N, ⊤) :=
    globalSections_module_finite_of_isFiniteType_of_isAffine N
  letI :
      Module.Finite Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens))
        Γ(N, ⊤) := hSections
  let eComparison :
      baseSections f M ≅
        baseSections f ((pushforward A.inclusion).obj A.modelModule) :=
    ((baseModulePresheafFunctor f).mapIso A.comparisonIso).app
      (.op (⊤ : X.Opens))
  let eInclusion :
      baseSections q A.modelModule ≅
        baseSections f ((pushforward A.inclusion).obj A.modelModule) :=
    baseSectionsPushforwardIso A.inclusion f A.modelModule
  let ePushforward :
      baseSections q A.modelModule ≅
        (baseModulePresheaf (𝟙 (Spec (.of K))) N).obj
          (.op (⊤ : (Spec (.of K)).Opens)) :=
    baseSectionsPushforwardTopIso q A.modelModule
  let eIdentity :
      ModuleCat.of Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens))
          Γ(N, ⊤) ≅
        (baseModulePresheaf (𝟙 (Spec (.of K))) N).obj
          (.op (⊤ : (Spec (.of K)).Opens)) :=
    baseModulePresheafIdTopIso N
  let e :
      baseSections f M ≅
        ModuleCat.of Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens))
          Γ(N, ⊤) :=
    eComparison ≪≫ eInclusion.symm ≪≫ ePushforward ≪≫ eIdentity.symm
  exact Module.Finite.equiv e.symm.toLinearEquiv

/-- Global sections of a coherent module with strict support on a smooth
proper integral curve form a finite module over the curve's global-function
ring. -/
theorem globalSections_module_finite_of_closedStalkSupport_lt_top
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent]
    (A : CanonicalSupportThickening M)
    (hM : closedStalkSupport M < ⊤) :
    Module.Finite Γ(X, ⊤) Γ(M, ⊤) := by
  let B := Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens))
  let R := Γ(X, (⊤ : X.Opens))
  letI : Algebra B R := f.appTop.hom.toAlgebra
  let sourceModule : ModuleCat R :=
    ((PresheafOfModules.forgetToPresheafModuleCat
      (.op (⊤ : X.Opens)) (initialOpOfTerminal isTerminalTop)).obj M.1).obj
        (.op (⊤ : X.Opens))
  letI : Module B sourceModule :=
    Module.compHom sourceModule f.appTop.hom
  letI : IsScalarTower B R sourceModule :=
    IsScalarTower.of_compHom B R sourceModule
  have hBase : Module.Finite B sourceModule := by
    change Module.Finite B (baseSections f M)
    exact baseSections_finite_of_closedStalkSupport_lt_top
      K X f M A hM
  letI : Module.Finite B sourceModule := hBase
  letI : Module.Finite R sourceModule :=
    Module.Finite.of_restrictScalars_finite B R sourceModule
  let eSource : ModuleCat.of R Γ(M, ⊤) ≅ sourceModule := by
    refine ModuleCat.isoMk (Iso.refl _) ?_
    intro r
    ext (x : Γ(M, ⊤))
    change
      X.presheaf.map
          ((initialOpOfTerminal isTerminalTop).to
            (.op (⊤ : X.Opens))) r • x = r • x
    rw [show (initialOpOfTerminal isTerminalTop).to
      (.op (⊤ : X.Opens)) = 𝟙 _ from Subsingleton.elim _ _]
    simp
  exact Module.Finite.equiv eSource.symm.toLinearEquiv

end CanonicalSupportThickening

end MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

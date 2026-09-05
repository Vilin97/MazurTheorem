/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleCanonicalSupportThickening
import MazurTorsion.Upstream.CurveCohomologyGrothendieckVanishing

/-!
# Finite proper support on a smooth curve

This file isolates the zero-dimensional-support boundary in the proper-curve
cohomology argument. A strict closed subset of a smooth proper integral curve
is finite. Consequently, the canonical support thickening of a coherent
module with strict closed stalk support has finite underlying space.

The named downstream consumer is
`CanonicalSupportThickening.isFinite_comp_structureMap_of_closedStalkSupport_lt_top`:
it upgrades that topological finiteness to finiteness of the thickening's
structure morphism. No full-support comparison or cohomology conclusion is
asserted here.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace
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

end CanonicalSupportThickening

end MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

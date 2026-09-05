/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Upstream.ProperCurveCechLowDegreeFinite
import MazurTorsion.Upstream.ProperCurveFiniteSupport
import MazurTorsion.Upstream.SchemeModuleBaseCechHZeroFinite

/-!
# Cohomology of strict support on a proper curve

This file is the cohomological consumer of the finite canonical-support
model. It turns finite global sections for strict support into canonical
degree-zero finiteness and, on a pointed curve, ordered degree-zero and
degree-one Cech finiteness.

The design boundary remains strict support. The missing full-support
comparison producer must reduce support before the closed-support induction
can use these declarations for an arbitrary coherent module.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules

namespace MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology
namespace CanonicalSupportThickening

/-- Canonical `H⁰` of a coherent strict-support module on a smooth proper
integral curve is finite-dimensional over the ground field. -/
theorem hZeroCanonical_finiteDimensional_of_closedStalkSupport_lt_top
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent]
    (A : CanonicalSupportThickening M)
    (hM : closedStalkSupport M < ⊤) :
    letI := hZeroCanonicalFieldModule K X f M
    FiniteDimensional K (H M 0) := by
  exact hZeroCanonical_finiteDimensional_of_globalSections_module_finite
    K X f M
      (globalSections_module_finite_of_closedStalkSupport_lt_top
        K X f M A hM)

/-- A coherent strict-support module on a pointed smooth proper integral
curve has finite ordered base-Cech homology in degrees zero and one for every
linearly ordered affine cover. -/
theorem orderedBaseCechLowDegreeFinite_of_rationalSection_of_closedStalkSupport_lt_top
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (s : SmoothCurveRationalSection K X f)
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent]
    (A : CanonicalSupportThickening M)
    (hM : closedStalkSupport M < ⊤)
    {I : Type u} [LinearOrder I] (U : I → X.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i)) :
    OrderedBaseCechLowDegreeFinite f U M := by
  exact
    orderedBaseCechLowDegreeFinite_of_rationalSection_of_globalSections_module_finite
      K X f s M U hU hUaff
        (globalSections_module_finite_of_closedStalkSupport_lt_top
          K X f M A hM)

end CanonicalSupportThickening

open CanonicalSupportThickening

/-- On a pointed smooth proper integral curve, it is enough to construct
support comodels for coherent modules whose closed stalk support is the whole
curve.  Strict support is discharged by the canonical finite thickening and
the identity comodel.  This is the exact design boundary for the remaining
full-support geometric producer. -/
theorem orderedBaseCechLowDegreeFinite_of_fullSupportComodels
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (s : SmoothCurveRationalSection K X f)
    {I : Type u} [LinearOrder I] (U : I → X.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (hfull : ∀ (N : X.Modules),
      N.IsFiniteType → N.IsQuasicoherent →
        closedStalkSupport N = ⊤ →
          ∃ (E : X.Modules) (g : N ⟶ E),
            IsCoherentLowDegreeSupportComodel f U N E g)
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent] :
    OrderedBaseCechLowDegreeFinite f U M := by
  letI : IsNoetherian X :=
    isNoetherian_of_proper_smoothRelativeDimension_one K X f
  letI : X.IsSeparated :=
    ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  apply orderedBaseCechLowDegreeFinite_of_coherentSupportComodels
    f U hUaff _ M
  intro N hNfinite hNqc
  letI : N.IsFiniteType := hNfinite
  letI : N.IsQuasicoherent := hNqc
  by_cases hNtop : closedStalkSupport N = ⊤
  · exact hfull N hNfinite hNqc hNtop
  · have hNstrict : closedStalkSupport N < ⊤ :=
      lt_top_iff_ne_top.mpr hNtop
    let A : CanonicalSupportThickening N :=
      CanonicalSupportThickening.ofFiniteType N
    have hNlow : OrderedBaseCechLowDegreeFinite f U N :=
      orderedBaseCechLowDegreeFinite_of_rationalSection_of_closedStalkSupport_lt_top
        K X f s N A hNstrict U hU hUaff
    exact
      ⟨N, 𝟙 N,
        IsCoherentLowDegreeSupportComodel.identity f U N hNlow⟩

/-- The full-support-only comodel boundary implies finite-dimensional
canonical `H⁰` for every coherent module on the pointed proper curve.  The
named downstream consumer is the coherent-cohomology facade; no comparison
producer is hidden in this reduction theorem. -/
theorem hZeroCanonical_finiteDimensional_of_fullSupportComodels
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (s : SmoothCurveRationalSection K X f)
    {I : Type u} [LinearOrder I] (U : I → X.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (hfull : ∀ (N : X.Modules),
      N.IsFiniteType → N.IsQuasicoherent →
        closedStalkSupport N = ⊤ →
          ∃ (E : X.Modules) (g : N ⟶ E),
            IsCoherentLowDegreeSupportComodel f U N E g)
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent] :
    letI := hZeroCanonicalFieldModule K X f M
    FiniteDimensional K (H M 0) := by
  let S := Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens))
  letI : Algebra K S := (Scheme.ΓSpecIso (.of K)).inv.hom.toAlgebra
  letI : Module S (H M 0) := baseSectionsHZeroModule f M
  letI : Module.Finite S (H M 0) := by
    letI : Module.Finite S
        ((orderedBaseCechComplex f M U).homology 0) :=
      (orderedBaseCechLowDegreeFinite_of_fullSupportComodels
        K X f s U hU hUaff hfull M).1
    exact hZero_finite_of_orderedBaseCechComplex f M U hU
  letI := hZeroCanonicalFieldModule K X f M
  letI : IsScalarTower K S (H M 0) :=
    IsScalarTower.of_compHom K S (H M 0)
  have hS : RingHom.Finite (algebraMap K S) := by
    change RingHom.Finite (Scheme.ΓSpecIso (.of K)).inv.hom
    exact (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv.finite
  letI : Module.Finite K S := RingHom.finite_algebraMap.mp hS
  exact Module.Finite.trans S (H M 0)

end MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineFiniteGeneratorMap
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineFiniteSections
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveChartExtensionData
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafFiniteTypeRestriction

/-!
# Finite generators on the standard projective charts

A finite-type quasicoherent module restricts to a finite module on each
standard affine chart.  We record an explicitly finite spanning family of
top sections for later use in the Serre global-generation construction.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

variable (k : Type) [CommRing k] (d : ℕ)

/-- Finite type is preserved on each standard affine chart. -/
instance chartModule_isFiniteType
    (M : (scheme k d).Modules) [M.IsFiniteType]
    (j : Fin (d + 1)) :
    (chartModule k d M j).IsFiniteType := by
  letI : IsOpenImmersion ((standardAffineOpenCover k d).f j) :=
    (standardAffineOpenCover k d).map_prop j
  change
    (M.restrict
      ((standardAffineOpenCover k d).f j)).IsFiniteType
  exact
    AlgebraicGeometry.Scheme.Modules.isFiniteType_restrictFunctor
      ((standardAffineOpenCover k d).f j) M

/-- The top sections on a standard chart form a finite module over that
chart's coordinate ring. -/
theorem chartModule_topSections_finite
    (M : (scheme k d).Modules)
    [M.IsFiniteType] [M.IsQuasicoherent]
    (j : Fin (d + 1)) :
    Module.Finite (chartRing k d j)
      Γ(chartModule k d M j, ⊤) :=
  AlgebraicGeometry.Scheme.Modules.finite_top_sections_of_isFiniteType_isQuasicoherent
    (chartModule k d M j)

/-- A standard chart admits a finite spanning family of module sections. -/
theorem exists_finite_chart_generators
    (M : (scheme k d).Modules)
    [M.IsFiniteType] [M.IsQuasicoherent]
    (j : Fin (d + 1)) :
    ∃ (n : ℕ) (s : Fin n → Γ(chartModule k d M j, ⊤)),
      Submodule.span (chartRing k d j) (Set.range s) = ⊤ := by
  letI : Module.Finite (chartRing k d j)
      Γ(chartModule k d M j, ⊤) :=
    chartModule_topSections_finite k d M j
  exact Module.Finite.exists_fin

/-- A chosen finite spanning family on one standard affine chart. -/
structure ChartGenerators
    (M : (scheme k d).Modules) (j : Fin (d + 1)) where
  /-- Number of generators. -/
  count : ℕ
  /-- The generating top sections. -/
  generator : Fin count → Γ(chartModule k d M j, ⊤)
  /-- These sections span all top sections over the affine chart ring. -/
  span_eq_top :
    Submodule.span (chartRing k d j) (Set.range generator) = ⊤

/-- A finite-type quasicoherent module admits finite generators on every
standard chart. -/
theorem ChartGenerators.exists
    (M : (scheme k d).Modules)
    [M.IsFiniteType] [M.IsQuasicoherent]
    (j : Fin (d + 1)) :
    Nonempty (ChartGenerators k d M j) := by
  obtain ⟨n, s, hs⟩ :=
    exists_finite_chart_generators k d M j
  exact ⟨⟨n, s, hs⟩⟩

namespace ChartGenerators

/-- The finite free affine module map determined by the chosen chart
generators. -/
def toModuleMap
    {M : (scheme k d).Modules} {j : Fin (d + 1)}
    (G : ChartGenerators k d M j) :
    SheafOfModules.free
        (R := (Spec (chartRing k d j)).ringCatSheaf)
        (Fin G.count) ⟶
      chartModule k d M j :=
  AlgebraicGeometry.Scheme.Modules.freeToModuleOfTopSections
    (chartModule k d M j) G.generator

/-- The map associated to a spanning chart family is an epimorphism. -/
theorem toModuleMap_epi
    {M : (scheme k d).Modules} [M.IsQuasicoherent]
    {j : Fin (d + 1)}
    (G : ChartGenerators k d M j) :
    Epi (G.toModuleMap) :=
  AlgebraicGeometry.Scheme.Modules.freeToModuleOfTopSections_epi
    (chartModule k d M j) G.generator G.span_eq_top

end ChartGenerators

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

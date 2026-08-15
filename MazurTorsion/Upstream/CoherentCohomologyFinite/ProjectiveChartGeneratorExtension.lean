/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveChartSectionTransport

/-!
# Extending standard-chart generators

Fix a finite generating family on one standard chart.  On every other
standard chart its restriction to the pairwise overlap extends after
multiplication by a power of the coordinate ratio.  Finiteness of the
standard cover lets us choose one exponent for every chart and every
generator simultaneously.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open AlgebraicGeometry.QuasicoherentTilde

attribute [local instance]
  AlgebraicGeometry.QuasicoherentTilde.sectionModule

variable (k : Type) [CommRing k] (d : ℕ)

/-- Uniform chartwise extensions of the generators chosen on one anchor
chart. -/
structure ChartGeneratorExtensions
    {M : (scheme k d).Modules} {i : Fin (d + 1)}
    (G : ChartGenerators k d M i) where
  /-- The common denominator-clearing exponent. -/
  exponent : ℕ
  /-- The extended generators on every standard chart. -/
  extended :
    ∀ j : Fin (d + 1),
      Fin G.count → Γ(chartModule k d M j, ⊤)
  /-- On the overlap with the anchor chart, the extension is the prescribed
  section multiplied by the common power of `Xᵢ/Xⱼ`. -/
  restrict_extended :
    ∀ (j : Fin (d + 1)) (a : Fin G.count),
      (chartModule k d M j).presheaf.map
          (homOfLE
            (show PrimeSpectrum.basicOpen
                (chartRatioElement k d i j) ≤ ⊤ from le_top)).op
          (extended j a) =
        sectionSmul
          (M := chartModule k d M j)
          (chartRatioElement k d i j ^ exponent)
          (chartSectionOnOverlap k d M i j (G.generator a))

/-- Uniform chartwise extensions exist for every finite generating family
on an anchor chart. -/
theorem ChartGeneratorExtensions.exists
    {M : (scheme k d).Modules} [M.IsQuasicoherent]
    {i : Fin (d + 1)}
    (G : ChartGenerators k d M i) :
    Nonempty (ChartGeneratorExtensions k d G) := by
  have hlocal (j : Fin (d + 1)) :
      ∃ (n : ℕ)
        (t : Fin G.count → Γ(chartModule k d M j, ⊤)),
        ∀ a,
          (chartModule k d M j).presheaf.map
              (homOfLE
                (show PrimeSpectrum.basicOpen
                    (chartRatioElement k d i j) ≤ ⊤ from le_top)).op
              (t a) =
            sectionSmul
              (M := chartModule k d M j)
              (chartRatioElement k d i j ^ n)
              (chartSectionOnOverlap k d M i j (G.generator a)) :=
    exists_uniform_chart_extension k d M i j
      (fun a =>
        chartSectionOnOverlap k d M i j (G.generator a))
  choose n t ht using hlocal
  let N : ℕ := ⨆ j, n j
  have hn (j : Fin (d + 1)) : n j ≤ N :=
    le_ciSup (Finite.bddAbove_range n) j
  let t' (j : Fin (d + 1)) (a : Fin G.count) :
      Γ(chartModule k d M j, ⊤) :=
    chartRatioElement k d i j ^ (N - n j) • t j a
  refine ⟨⟨N, t', fun j a => ?_⟩⟩
  dsimp only [t']
  let scale
      (r : chartRing k d j)
      (x : Γ(chartModule k d M j,
        PrimeSpectrum.basicOpen
          (chartRatioElement k d i j))) :
      Γ(chartModule k d M j,
        PrimeSpectrum.basicOpen
          (chartRatioElement k d i j)) :=
    sectionSmul r x
  calc
    _ = scale (chartRatioElement k d i j ^ (N - n j))
          ((chartModule k d M j).presheaf.map
            (homOfLE
              (show PrimeSpectrum.basicOpen
                  (chartRatioElement k d i j) ≤ ⊤ from le_top)).op
            (t j a)) :=
      AlgebraicGeometry.Scheme.Modules.map_smul_Spec
        (M := chartModule k d M j)
        (homOfLE
          (show PrimeSpectrum.basicOpen
              (chartRatioElement k d i j) ≤ ⊤ from le_top)).op
        (chartRatioElement k d i j ^ (N - n j))
        (t j a)
    _ = scale (chartRatioElement k d i j ^ (N - n j))
          (sectionSmul
            (M := chartModule k d M j)
            (chartRatioElement k d i j ^ n j)
            (chartSectionOnOverlap k d M i j (G.generator a))) := by
      apply congrArg
        (scale (chartRatioElement k d i j ^ (N - n j)))
      exact ht j a
    _ = sectionSmul
          (M := chartModule k d M j)
          (chartRatioElement k d i j ^ N)
          (chartSectionOnOverlap k d M i j (G.generator a)) := by
      dsimp only [scale]
      calc
        _ = sectionSmul
              (M := chartModule k d M j)
              ((chartRatioElement k d i j ^ (N - n j)) *
                chartRatioElement k d i j ^ n j)
              (chartSectionOnOverlap k d M i j (G.generator a)) :=
          (sectionSmul_mul
            (M := chartModule k d M j)
            (U := show (Spec (chartRing k d j)).Opens from
              PrimeSpectrum.basicOpen
                (chartRatioElement k d i j))
            (chartRatioElement k d i j ^ (N - n j))
            (chartRatioElement k d i j ^ n j)
            (chartSectionOnOverlap k d M i j
              (G.generator a))).symm
        _ = _ := by
          congr 1
          rw [← pow_add, Nat.sub_add_cancel (hn j)]

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

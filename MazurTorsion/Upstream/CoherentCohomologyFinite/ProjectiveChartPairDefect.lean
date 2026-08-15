/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.DependentFinitePowerClearing
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveChartGeneratorExtension

/-!
# Pairwise defects of projective-chart generator extensions

An anchor-chart generator is extended independently to every standard
chart.  On the overlap of charts `j` and `l`, the difference between the
two extensions (after the degree transition factor) is their pairwise
defect.  If that defect vanishes on the further overlap with the anchor
chart, affine power-uniqueness kills it after a power of `Xᵢ/Xⱼ`.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open AlgebraicGeometry.QuasicoherentTilde

variable (k : Type) [CommRing k] (d : ℕ)

/-- The failure of two independently extended chart sections to satisfy
the degree-`E.exponent` transition equation on their pairwise overlap,
written in the coordinates of the first chart. -/
def chartPairDefect
    {M : (scheme k d).Modules} {i : Fin (d + 1)}
    {G : ChartGenerators k d M i}
    (E : ChartGeneratorExtensions k d G)
    (j l : Fin (d + 1)) (a : Fin G.count) :
    Γ(chartModule k d M j,
      PrimeSpectrum.basicOpen
        (chartRatioElement k d l j)) :=
  (show
      Γ(chartModule k d M j,
        PrimeSpectrum.basicOpen
          (chartRatioElement k d l j))
    from
      (chartModule k d M j).presheaf.map
        (homOfLE
          (show PrimeSpectrum.basicOpen
              (chartRatioElement k d l j) ≤ ⊤ from le_top)).op
        (E.extended j a)) -
    sectionSmul (chartRatioElement k d l j ^ E.exponent)
      (chartSectionOnOverlap k d M l j (E.extended l a))

/-- The defect restricted to the triple overlap with the anchor chart.
The product equation cuts out
`D(Xᵢ/Xⱼ) ∩ D(Xₗ/Xⱼ)` in the `j`-th affine chart. -/
def chartPairDefectOnAnchorOverlap
    {M : (scheme k d).Modules} {i : Fin (d + 1)}
    {G : ChartGenerators k d M i}
    (E : ChartGeneratorExtensions k d G)
    (j l : Fin (d + 1)) (a : Fin G.count) :
    Γ(chartModule k d M j,
      PrimeSpectrum.basicOpen
        (chartRatioElement k d i j *
          chartRatioElement k d l j)) :=
  (chartModule k d M j).presheaf.map
    (homOfLE
      (PrimeSpectrum.basicOpen_mul_le_right
        (chartRatioElement k d i j)
        (chartRatioElement k d l j))).op
    (chartPairDefect k d E j l a)

/-- Affine localization power-uniqueness: a pairwise defect which vanishes
after also entering the anchor chart is killed, on the pairwise overlap,
by a power of the anchor ratio. -/
theorem exists_pow_smul_chartPairDefect_eq_zero
    {M : (scheme k d).Modules} [M.IsQuasicoherent]
    {i : Fin (d + 1)}
    {G : ChartGenerators k d M i}
    (E : ChartGeneratorExtensions k d G)
    (j l : Fin (d + 1)) (a : Fin G.count)
    (hzero :
      chartPairDefectOnAnchorOverlap k d E j l a = 0) :
    ∃ n : ℕ,
      sectionSmul (chartRatioElement k d i j ^ n)
          (chartPairDefect k d E j l a) = 0 := by
  let f := chartRatioElement k d i j
  let g := chartRatioElement k d l j
  let V : (Spec (chartRing k d j)).Opens :=
    PrimeSpectrum.basicOpen g
  have hV :
      BasicOpenExtensionData (chartModule k d M j) V :=
    BasicOpenExtensionData.of_le g le_top
      (chartExtensionData k d M j)
  have hfg :
      PrimeSpectrum.basicOpen (f * g) ≤ V :=
    PrimeSpectrum.basicOpen_mul_le_right f g
  obtain ⟨n, hn⟩ :=
    hV.uniqueness (f * g) hfg
      (chartPairDefect k d E j l a) hzero
  refine ⟨n, ?_⟩
  have hreg :
      @IsSMulRegular (chartRing k d j)
        Γ(chartModule k d M j, PrimeSpectrum.basicOpen g)
        (sectionModule
          (M := chartModule k d M j)
          (PrimeSpectrum.basicOpen g)).toSMul
        (g ^ n) :=
    @IsSMulRegular.pow (chartRing k d j)
      Γ(chartModule k d M j, PrimeSpectrum.basicOpen g) g _
      (sectionMulAction
        (M := chartModule k d M j)
        (PrimeSpectrum.basicOpen g)) n
      ((chartModule k d M j).isSMulRegular_of_le_basicOpen
        (f := g) le_rfl)
  refine @IsSMulRegular.right_eq_zero_of_smul
    (chartRing k d j)
    Γ(chartModule k d M j, PrimeSpectrum.basicOpen g) _
    (sectionSMulZeroClass
      (M := chartModule k d M j)
      (PrimeSpectrum.basicOpen g))
    (g ^ n) (sectionSmul (f ^ n) (chartPairDefect k d E j l a))
    hreg ?_
  calc
    sectionSmul (g ^ n)
        (sectionSmul (f ^ n) (chartPairDefect k d E j l a)) =
      sectionSmul ((f * g) ^ n) (chartPairDefect k d E j l a) := by
        rw [mul_pow]
        exact
          (sectionSmul_comm (g ^ n) (f ^ n)
            (chartPairDefect k d E j l a)).trans
            (sectionSmul_mul (f ^ n) (g ^ n)
              (chartPairDefect k d E j l a)).symm
    _ = 0 := hn

/-- One exponent kills all pairwise defects of all extended generators,
provided every defect vanishes on its triple overlap with the anchor. -/
theorem exists_uniform_chartPairDefect_power
    {M : (scheme k d).Modules} [M.IsQuasicoherent]
    {i : Fin (d + 1)}
    {G : ChartGenerators k d M i}
    (E : ChartGeneratorExtensions k d G)
    (hzero :
      ∀ (j l : Fin (d + 1)) (a : Fin G.count),
        chartPairDefectOnAnchorOverlap k d E j l a = 0) :
    ∃ K : ℕ,
      ∀ (j l : Fin (d + 1)) (a : Fin G.count),
        sectionSmul (chartRatioElement k d i j ^ K)
            (chartPairDefect k d E j l a) = 0 := by
  let ι := Fin (d + 1) × Fin (d + 1) × Fin G.count
  let R : ι → Type :=
    fun q => chartRing k d q.1
  let N : ι → Type :=
    fun q =>
      Γ(chartModule k d M q.1,
        PrimeSpectrum.basicOpen
          (chartRatioElement k d q.2.1 q.1))
  letI : ∀ q, Module (R q) (N q) := fun q =>
    chartModule_sections_module k d M q.1
      (PrimeSpectrum.basicOpen
        (chartRatioElement k d q.2.1 q.1))
  let f : ∀ q, R q :=
    fun q => chartRatioElement k d i q.1
  let x : ∀ q, N q :=
    fun q => chartPairDefect k d E q.1 q.2.1 q.2.2
  have hx : ∀ q, ∃ n : ℕ, f q ^ n • x q = 0 := by
    intro q
    exact exists_pow_smul_chartPairDefect_eq_zero
      k d E q.1 q.2.1 q.2.2 (hzero q.1 q.2.1 q.2.2)
  obtain ⟨K, hK⟩ :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.exists_uniform_pow_smul_eq_zero_dependent
      R N f x hx
  exact ⟨K, fun j l a => hK (j, l, a)⟩

/-- Pairwise-defect data after choosing one common correcting exponent.
This is the algebraic compatibility package used before converting the
chart sections into local morphisms from a Serre twist. -/
structure CorrectedChartGeneratorExtensions
    {M : (scheme k d).Modules} {i : Fin (d + 1)}
    {G : ChartGenerators k d M i}
    (E : ChartGeneratorExtensions k d G) where
  /-- The extra power used to clear every pairwise defect. -/
  correctionExponent : ℕ
  /-- Every defect is killed by the corresponding anchor ratio power. -/
  defect_annihilated :
    ∀ (j l : Fin (d + 1)) (a : Fin G.count),
      sectionSmul (chartRatioElement k d i j ^ correctionExponent)
          (chartPairDefect k d E j l a) = 0

/-- Triple-overlap vanishing produces a corrected pairwise-compatible
extension package. -/
theorem CorrectedChartGeneratorExtensions.exists
    {M : (scheme k d).Modules} [M.IsQuasicoherent]
    {i : Fin (d + 1)}
    {G : ChartGenerators k d M i}
    (E : ChartGeneratorExtensions k d G)
    (hzero :
      ∀ (j l : Fin (d + 1)) (a : Fin G.count),
        chartPairDefectOnAnchorOverlap k d E j l a = 0) :
    Nonempty (CorrectedChartGeneratorExtensions k d E) := by
  obtain ⟨K, hK⟩ :=
    exists_uniform_chartPairDefect_power k d E hzero
  exact ⟨⟨K, hK⟩⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

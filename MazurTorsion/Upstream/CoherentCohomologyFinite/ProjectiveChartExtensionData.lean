/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineFinitePowerExtension
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineQuasicoherentTilde
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveStandardChartRatios
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafQuasicoherentRestriction

/-!
# Extension data on the standard projective charts

The restriction of a quasicoherent module to a standard projective chart is
a quasicoherent module on an affine spectrum.  Consequently its sections
satisfy the distinguished-open existence and power-uniqueness statements.
This file packages that fact at the exact chart rings used by the Serre
generation argument.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open HomogeneousLocalization
open AlgebraicGeometry.QuasicoherentTilde

variable (k : Type) [CommRing k] (d : ℕ)

/-- The affine coordinate ring of the `j`-th standard chart, kept as a
`CommRingCat` object so that its scalar action on module sections is
available without elaborator-side coercion guessing. -/
def chartRing (j : Fin (d + 1)) : CommRingCat :=
  CommRingCat.of
    (Away (homogeneousGrading k d) (coordinate k j))

/-- The coordinate ratio `Xᵢ/Xⱼ`, as an element of the `j`-th chart ring. -/
def chartRatioElement (i j : Fin (d + 1)) : chartRing k d j :=
  chartRatio k d i j

/-- The inclusion of a standard affine chart, with its source exposed in
the form used by the chart-module API. -/
def standardChartMap (j : Fin (d + 1)) :
    Spec (chartRing k d j) ⟶ scheme k d :=
  (standardAffineOpenCover k d).f j

instance standardChartMap_isOpenImmersion (j : Fin (d + 1)) :
    IsOpenImmersion (standardChartMap k d j) := by
  dsimp only [standardChartMap]
  exact (standardAffineOpenCover k d).map_prop j

/-- The concrete sheafification instance on an explicit chart over-site,
spelled out to keep elaboration below the default typeclass budget. -/
instance projectiveChart_sheafToPresheaf_isRightAdjoint
    (j : Fin (d + 1))
    (U : (Spec (chartRing k d j)).Opens) :
    (sheafToPresheaf
      ((Opens.grothendieckTopology
        (Spec (chartRing k d j))).over U)
      AddCommGrpCat.{0}).IsRightAdjoint :=
  CategoryTheory.sheafToPresheaf_isRightAdjoint
    ((Opens.grothendieckTopology
      (Spec (chartRing k d j))).over U)
    AddCommGrpCat.{0}

/-- The corresponding local-bijectivity characterization for sheafification. -/
instance projectiveChart_wEqualsLocallyBijective
    (j : Fin (d + 1))
    (U : (Spec (chartRing k d j)).Opens) :
    ((Opens.grothendieckTopology
      (Spec (chartRing k d j))).over U
      ).WEqualsLocallyBijective AddCommGrpCat.{0} := by
  apply GrothendieckTopology.WEqualsLocallyBijective.mk'

/-- Restriction of a projective module to the `j`-th standard affine
chart. -/
abbrev chartModule
    (M : (scheme k d).Modules) (j : Fin (d + 1)) :
    (Spec (chartRing k d j)).Modules := by
  let N := M.restrict (standardChartMap k d j)
  exact N

/-- The distinguished open cut out by one coordinate ratio, typed as an
open of the chart scheme rather than its underlying prime spectrum. -/
abbrev chartRatioOpen (i j : Fin (d + 1)) :
    (Spec (chartRing k d j)).Opens :=
  PrimeSpectrum.basicOpen (chartRatioElement k d i j)

/-- The distinguished open cut out by a product of two coordinate ratios. -/
abbrev chartRatioProductOpen (i l j : Fin (d + 1)) :
    (Spec (chartRing k d j)).Opens :=
  PrimeSpectrum.basicOpen
    (chartRatioElement k d i j * chartRatioElement k d l j)

/-- The affine chart ring acts on sections of the restricted module.
Naming this instance avoids unfolding the concrete cover construction
during scalar-action synthesis. -/
instance chartModule_sections_module
    (M : (scheme k d).Modules) (j : Fin (d + 1))
    (U : (Spec (chartRing k d j)).Opens) :
    Module (chartRing k d j) Γ(chartModule k d M j, U) :=
  inferInstanceAs
    (Module (chartRing k d j)
      (((modulesSpecToSheaf (R := chartRing k d j)).obj
        (chartModule k d M j)).obj.obj (.op U)))

instance chartModule_isQuasicoherent
    (M : (scheme k d).Modules) [M.IsQuasicoherent]
    (j : Fin (d + 1)) :
    (chartModule k d M j).IsQuasicoherent := by
  change
    (M.restrict
      (standardChartMap k d j)).IsQuasicoherent
  exact AlgebraicGeometry.Scheme.Modules.isQuasicoherent_restrictFunctor
    (standardChartMap k d j) M

/-- Quasicoherent modules have affine basic-open extension data on each
standard chart. -/
theorem chartExtensionData
    (M : (scheme k d).Modules) [M.IsQuasicoherent]
    (j : Fin (d + 1)) :
    BasicOpenExtensionData (chartModule k d M j) ⊤ := by
  exact
    AlgebraicGeometry.Scheme.Modules.basicOpenExtensionData_top_of_isQuasicoherent
      (chartModule k d M j)

/-- A finite family of sections on the overlap with the `i`-th chart
extends across the `j`-th chart after one common power of `Xᵢ/Xⱼ`. -/
theorem exists_uniform_chart_extension
    (M : (scheme k d).Modules) [M.IsQuasicoherent]
    (i j : Fin (d + 1))
    {ι : Type*} [Finite ι]
    (s : ι → Γ(chartModule k d M j,
      PrimeSpectrum.basicOpen (chartRatioElement k d i j))) :
    ∃ (N : ℕ) (t : ι → Γ(chartModule k d M j, ⊤)),
      ∀ a,
        (chartModule k d M j).presheaf.map
            (homOfLE le_top).op (t a) =
          sectionSmul (chartRatioElement k d i j ^ N) (s a) := by
  exact
    (chartExtensionData k d M j).exists_uniform_extension
      (chartRatioElement k d i j) le_top s

/-- A finite family of chart sections which vanishes on the overlap with
the `i`-th chart is killed by one common power of `Xᵢ/Xⱼ`. -/
theorem exists_uniform_chart_power_annihilates
    (M : (scheme k d).Modules) [M.IsQuasicoherent]
    (i j : Fin (d + 1))
    {ι : Type*} [Finite ι]
    (t : ι → Γ(chartModule k d M j, ⊤))
    (ht : ∀ a,
      (chartModule k d M j).presheaf.map
          (homOfLE
            (show PrimeSpectrum.basicOpen
                (chartRatioElement k d i j) ≤ ⊤ from le_top)).op
          (t a) =
        (0 : Γ(chartModule k d M j,
          PrimeSpectrum.basicOpen (chartRatioElement k d i j)))) :
    ∃ N : ℕ, ∀ a,
      sectionSmul (chartRatioElement k d i j ^ N) (t a) = 0 := by
  exact
    AlgebraicGeometry.QuasicoherentTilde.BasicOpenExtensionData.exists_uniform_pow_smul_eq_zero_of_restrict_eq_zero
        (chartExtensionData k d M j)
        (chartRatioElement k d i j) le_top t ht

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

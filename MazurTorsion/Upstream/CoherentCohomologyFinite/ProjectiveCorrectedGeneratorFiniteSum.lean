/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveCorrectedChartOverAnchor
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveCorrectedChartGlobalMap
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveTwistGeneratorAllCharts
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleOverEpiTransport

/-!
# A finite global sum of corrected projective generators

The corrected generators attached to each standard affine chart give an
epimorphic family after pullback to their anchor chart.  Taking the
dependent sum over all standard charts therefore gives one finite
epimorphism from integer Serre twists.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

namespace CorrectedChartGeneratorExtensions

variable {k : Type} [CommRing k] {d : ℕ}
variable {M : (scheme k d).Modules} {i : Fin (d + 1)}
variable {G : ChartGenerators k d M i}
variable {E : ChartGeneratorExtensions k d G}

/-- The glued corrected generators are epimorphic after pullback to
their anchor standard chart. -/
theorem correctedGlobalHom_anchor_pullback_epi
    [M.IsQuasicoherent]
    (C : CorrectedChartGeneratorExtensions k d E)
    (hcoordinate :
      SerreTwist.IntegerOverChartCoordinateTransition
        k d C.totalExponent) :
    Epi
      (Limits.Sigma.desc
        (fun a =>
          (Scheme.Modules.pullback
            ((SerreTwist.cover k d).f i)).map
              (C.correctedGlobalHom a hcoordinate))) := by
  have hover :
      Epi
        (Limits.Sigma.desc
          (fun a =>
            (C.correctedGlobalHom a hcoordinate).over
              (standardChart k i))) := by
    simpa only [C.correctedGlobalHom_over i] using
      C.correctedTwistOverHom_anchor_epi
  have hpullback :=
    Scheme.Modules.sigmaDesc_pullback_epi_of_over
      (standardChart k i)
      (fun _ : Fin G.count =>
        SerreTwist.OInt k d
          (-(C.totalExponent : ℤ)))
      M
      (fun a => C.correctedGlobalHom a hcoordinate)
      hover
  change
    Epi
      (Limits.Sigma.desc
        (fun a =>
          (Scheme.Modules.pullback
            (standardChart k i).ι).map
              (C.correctedGlobalHom a hcoordinate)))
  exact hpullback

/-- Corrected finite generator families from all standard charts
assemble into a global epimorphism from a finite sum of integer twists. -/
theorem correctedFiniteIntegerSumDesc_epi
    [M.IsQuasicoherent]
    (G : ∀ j : Fin (d + 1),
      ChartGenerators k d M j)
    (E : ∀ j : Fin (d + 1),
      ChartGeneratorExtensions k d (G j))
    (C : ∀ j : Fin (d + 1),
      CorrectedChartGeneratorExtensions k d (E j))
    (hcoordinate :
      ∀ j : Fin (d + 1),
        SerreTwist.IntegerOverChartCoordinateTransition
          k d (C j).totalExponent) :
    Epi
      (SerreTwist.finiteIntegerSumDesc k d
        (fun p : Σ j, Fin (G j).count =>
          -((C p.1).totalExponent : ℤ))
        (fun p =>
          (C p.1).correctedGlobalHom
            p.2 (hcoordinate p.1))) := by
  apply
    SerreTwist.finiteIntegerSumDesc_epi_of_anchorFamilies
      k d
      (fun j => (G j).count)
      (fun j _ => -((C j).totalExponent : ℤ))
      (fun j a =>
        (C j).correctedGlobalHom a (hcoordinate j))
  intro j
  exact
    (C j).correctedGlobalHom_anchor_pullback_epi
      (hcoordinate j)

end CorrectedChartGeneratorExtensions

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveCorrectedChartAnchor
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveChartTopSectionTransport
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleOpenSectionEpi
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteCoproductSubfamily

/-!
# Corrected generators on the anchor standard open

The epimorphic family of corrected affine-chart generators remains
epimorphic after transport to the slice site of the corresponding
standard projective open.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleOpenSectionHom
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleTopSectionHom

namespace CorrectedChartGeneratorExtensions

variable {k : Type} [CommRing k] {d : ℕ}
variable {M : (scheme k d).Modules} {i : Fin (d + 1)}
variable {G : ChartGenerators k d M i}
variable {E : ChartGeneratorExtensions k d G}

/-- The corrected ambient-open maps on the anchor chart form an
epimorphic coproduct. -/
theorem correctedOverHom_anchor_epi
    [M.IsQuasicoherent]
    (C : CorrectedChartGeneratorExtensions k d E) :
    Epi
      (Limits.Sigma.desc
        (fun a => C.correctedOverHom i a)) := by
  let U := standardChart k i
  let e := standardChartSchemeIso k d i
  let s₀ : Fin G.count →
      Γ(chartModule k d M i, ⊤) :=
    fun a => C.correctedSection i a
  let s₁ : Fin G.count →
      Γ((M.restrict U.ι).restrict e.hom, ⊤) :=
    fun a =>
      chartIteratedRestrictionTopSection
        k d M i (s₀ a)
  let s₂ : Fin G.count →
      Γ(M.restrict U.ι, ⊤) :=
    fun a =>
      chartOpenTopSection k d M i (s₀ a)
  have h₀ :
      Epi
        (Limits.Sigma.desc
          (fun a =>
            homOfTopSection
              (chartModule k d M i) (s₀ a))) := by
    simpa only [s₀, correctedLocalHom] using
      C.correctedLocalHom_anchor_epi
  have h₁ :
      Epi
        (Limits.Sigma.desc
          (fun a =>
            homOfTopSection
              ((M.restrict U.ι).restrict e.hom)
              (s₁ a))) := by
    simpa only [s₀, s₁,
      chartIteratedRestrictionTopSection] using
      Scheme.Modules.sigmaDesc_moduleIsoTopSection_epi
        (chartModuleRestrictionIso k d M i)
        s₀ h₀
  have h₂ :
      Epi
        (Limits.Sigma.desc
          (fun a =>
            homOfTopSection
              (M.restrict U.ι) (s₂ a))) := by
    simpa only [s₁, s₂, chartOpenTopSection] using
      Scheme.Modules.sigmaDesc_isoTransportedTopSection_epi
        e (M.restrict U.ι) s₁ h₁
  have h₂' :
      Epi
        (Scheme.Modules.restrictedTopSectionCoproduct
          M U s₂) := by
    unfold Scheme.Modules.restrictedTopSectionCoproduct
    change
      Epi
        (Limits.Sigma.desc
          (fun a =>
            homOfTopSection
              (M.restrict U.ι) (s₂ a)))
    exact h₂
  have h₃ :=
    Scheme.Modules.sigmaDesc_homOfOpenSection_epi_of_restrict
      M U s₂ h₂'
  have hsection (a : Fin G.count) :
      (eqToIso
        (congrArg (fun V => Γ(M, V))
          U.ι_image_top)).hom
        ((M.restrictAppIso U.ι ⊤).hom (s₂ a)) =
      C.correctedAmbientSection i a := by
    change
      chartTransportedAmbientSection
          k d M i (C.correctedSection i a) =
        C.correctedAmbientSection i a
    exact chartTransportedAmbientSection_eq
      k d M i (C.correctedSection i a)
  simpa only [correctedOverHom, hsection] using h₃

/-- Precomposing with the integer-twist trivialization preserves the
anchor-chart epimorphic family. -/
theorem correctedTwistOverHom_anchor_epi
    [M.IsQuasicoherent]
    (C : CorrectedChartGeneratorExtensions k d E) :
    Epi
      (Limits.Sigma.desc
        (fun a => C.correctedTwistOverHom i a)) := by
  apply
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.epi_sigmaDesc_of_epi_subfamily
      (fun _ : Fin G.count =>
        (SerreTwist.OInt k d
          (-(C.totalExponent : ℤ))).over
            (standardChart k i))
      (fun _ : Fin G.count =>
        SheafOfModules.unit
          ((scheme k d).ringCatSheaf.over
            (standardChart k i)))
      (fun a => a)
      (fun _ =>
        (SerreTwist.integerOverChartIso k d
          (-(C.totalExponent : ℤ)) i).inv)
      (fun a => C.correctedTwistOverHom i a)
  simpa only [correctedTwistOverHom, Category.assoc,
    Iso.inv_hom_id_assoc] using
    C.correctedOverHom_anchor_epi

end CorrectedChartGeneratorExtensions

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

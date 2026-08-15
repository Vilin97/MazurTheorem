/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineFiniteGeneratorSectionMap
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveCorrectedChartGlobalMap

/-!
# Corrected generators on their anchor chart

On the chart from which a finite generating family was chosen, every
coordinate-ratio correction is multiplication by one.  Consequently the
corrected section is the original generator.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open HomogeneousLocalization

variable (k : Type) [CommRing k] (d : ℕ)

/-- The diagonal coordinate ratio `Xᵢ/Xᵢ` is one. -/
lemma chartRatioElement_self (i : Fin (d + 1)) :
    chartRatioElement k d i i = 1 := by
  change
    chartRatio k d i i =
      (1 : Away (homogeneousGrading k d) (coordinate k i))
  apply HomogeneousLocalization.val_injective
  rw [chartRatio, Away.isLocalizationElem,
    Away.val_mk, HomogeneousLocalization.val_one]
  exact Localization.mk_self_mk _ _

/-- Restriction to the diagonal overlap agrees with the self-transported
section. -/
theorem restrict_eq_chartSectionOnOverlap_self
    (M : (scheme k d).Modules) (i : Fin (d + 1))
    (s : Γ(chartModule k d M i, ⊤)) :
    (chartModule k d M i).presheaf.map
        (homOfLE
          (show PrimeSpectrum.basicOpen
              (chartRatioElement k d i i) ≤ ⊤
            from le_top)).op s =
      chartSectionOnOverlap k d M i i s := by
  apply AddCommGrpCat.injective_of_mono
    (chartOverlapSectionsIso k d M i i).hom
  calc
    (chartOverlapSectionsIso k d M i i).hom
        ((chartModule k d M i).presheaf.map
          (homOfLE
            (show PrimeSpectrum.basicOpen
                (chartRatioElement k d i i) ≤ ⊤
              from le_top)).op s) =
      M.presheaf.map (homOfLE inf_le_left).op
        ((chartTopSectionsIso k d M i).hom s) :=
      chartOverlapSectionsIso_hom_restrict_top k d M i i s
    _ = M.presheaf.map (homOfLE inf_le_right).op
        ((chartTopSectionsIso k d M i).hom s) := by
      exact ConcreteCategory.congr_hom
        (congrArg (fun r => M.presheaf.map r)
          (Subsingleton.elim _ _))
        ((chartTopSectionsIso k d M i).hom s)
    _ = (chartOverlapSectionsIso k d M i i).hom
        (chartSectionOnOverlap k d M i i s) :=
      (chartOverlapSectionsIso_hom_chartSectionOnOverlap
        k d M i i s).symm

/-- Transport to the diagonal overlap is injective. -/
theorem chartSectionOnOverlap_self_injective
    (M : (scheme k d).Modules) (i : Fin (d + 1)) :
    Function.Injective
      (chartSectionOnOverlap k d M i i) := by
  intro s t h
  apply
    (chartTopSectionsIso k d M i).addCommGroupIsoToAddEquiv.injective
  have h' :=
    congrArg
      (chartOverlapSectionsIso k d M i i).hom h
  rw [chartOverlapSectionsIso_hom_chartSectionOnOverlap,
    chartOverlapSectionsIso_hom_chartSectionOnOverlap] at h'
  let q :=
    M.presheaf.map
      (homOfLE
        (show
          standardChart k i ⊓ standardChart k i ≤
            standardChart k i
          from inf_le_right)).op
  haveI :
      IsIso
        (homOfLE
          (show
            standardChart k i ⊓ standardChart k i ≤
              standardChart k i
            from inf_le_right)) := by
    rw [show
      (homOfLE
        (show
          standardChart k i ⊓ standardChart k i ≤
            standardChart k i
          from inf_le_right)) =
        eqToHom (inf_idem (standardChart k i))
      from Subsingleton.elim _ _]
    infer_instance
  haveI : IsIso q := inferInstance
  exact (AddCommGrpCat.mono_iff_injective q).mp inferInstance h'

namespace CorrectedChartGeneratorExtensions

variable {k d}
variable {M : (scheme k d).Modules} {i : Fin (d + 1)}
variable {G : ChartGenerators k d M i}
variable {E : ChartGeneratorExtensions k d G}

/-- The uncorrected extension on its anchor chart is the original
generator. -/
theorem extended_anchor
    (a : Fin G.count) :
    E.extended i a = G.generator a := by
  have h := E.restrict_extended i a
  simp only [chartRatioElement_self, one_pow] at h
  rw [sectionSmul_eq_smul_chart, one_smul] at h
  rw [restrict_eq_chartSectionOnOverlap_self
    k d M i (E.extended i a)] at h
  exact
    chartSectionOnOverlap_self_injective k d M i h

/-- Correcting an anchor-chart section leaves the chosen generator
unchanged. -/
theorem correctedSection_anchor
    (C : CorrectedChartGeneratorExtensions k d E)
    (a : Fin G.count) :
    C.correctedSection i a = G.generator a := by
  rw [correctedSection, chartRatioElement_self k d i,
    one_pow, one_smul, extended_anchor (E := E)]

/-- The corrected local section maps on the anchor chart form an
epimorphic coproduct. -/
theorem correctedLocalHom_anchor_epi
    [M.IsQuasicoherent]
    (C : CorrectedChartGeneratorExtensions k d E) :
    Epi
      (Limits.Sigma.desc
        (fun a => C.correctedLocalHom i a)) := by
  have h :=
    AlgebraicGeometry.Scheme.Modules.sigmaDesc_homOfTopSection_epi
      (chartModule k d M i) G.generator G.span_eq_top
  simpa only [correctedLocalHom,
    C.correctedSection_anchor] using h

end CorrectedChartGeneratorExtensions

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

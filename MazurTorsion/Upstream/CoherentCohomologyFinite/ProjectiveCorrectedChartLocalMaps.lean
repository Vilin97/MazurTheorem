/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveCorrectedChartSections
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistIntegerCoherence
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleOpenSectionHom
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleTopSectionHom

/-!
# Local maps attached to corrected projective-chart sections

A corrected chart section determines a morphism from the unit module on
that chart.  Evaluating this morphism on `1` over a pairwise overlap
recovers the exact Serre-twist transition equation proved for corrected
sections.
-/

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleTopSectionHom
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleOpenSectionHom
open SerreTwist

variable (k : Type) [CommRing k] (d : ℕ)

namespace CorrectedChartGeneratorExtensions

variable {k d}
variable {M : (scheme k d).Modules} {i : Fin (d + 1)}
variable {G : ChartGenerators k d M i}
variable {E : ChartGeneratorExtensions k d G}

/-- The local morphism from the unit module determined by a corrected
generator section. -/
def correctedLocalHom
    (C : CorrectedChartGeneratorExtensions k d E)
    (j : Fin (d + 1)) (a : Fin G.count) :
    SheafOfModules.unit (Spec (chartRing k d j)).ringCatSheaf ⟶
      chartModule k d M j :=
  homOfTopSection (chartModule k d M j) (C.correctedSection j a)

/-- The corrected local section, expressed directly as a section of the
ambient module on the corresponding standard projective open. -/
def correctedAmbientSection
    (C : CorrectedChartGeneratorExtensions k d E)
    (j : Fin (d + 1)) (a : Fin G.count) :
    Γ(M, standardChart k j) :=
  (chartTopSectionsIso k d M j).hom (C.correctedSection j a)

/-- Slice-site form of the map determined by a corrected ambient section. -/
def correctedOverHom
    (C : CorrectedChartGeneratorExtensions k d E)
    (j : Fin (d + 1)) (a : Fin G.count) :
    SheafOfModules.unit
        ((scheme k d).ringCatSheaf.over (standardChart k j)) ⟶
      M.over (standardChart k j) :=
  homOfOpenSection M (standardChart k j)
    (C.correctedAmbientSection j a)

/-- The corrected section defines the expected local map from the negative
integer twist. -/
def correctedTwistOverHom
    (C : CorrectedChartGeneratorExtensions k d E)
    (j : Fin (d + 1)) (a : Fin G.count) :
    (OInt k d (-(C.totalExponent : ℤ))).over
        (standardChart k j) ⟶
      M.over (standardChart k j) :=
  (integerOverChartIso k d (-(C.totalExponent : ℤ)) j).hom ≫
    C.correctedOverHom j a

private def correctedLocalHomAppRatioOneRaw
    (C : CorrectedChartGeneratorExtensions k d E)
    (j l : Fin (d + 1)) (a : Fin G.count) :=
  (homOfTopSection_app_one
      (chartModule k d M j) (C.correctedSection j a)
      (PrimeSpectrum.basicOpen
        (chartRatioElement k d l j))).trans
    (C.restrict_correctedSection j l a)

/-- On a pairwise overlap, the local map sends `1` to the transition
factor times the corrected section transported from the other chart. -/
theorem correctedLocalHom_app_ratio_one
    (C : CorrectedChartGeneratorExtensions k d E)
    (j l : Fin (d + 1)) (a : Fin G.count) :
    (C.correctedLocalHom j a).val.app
        (op (PrimeSpectrum.basicOpen
          (chartRatioElement k d l j)))
        (1 : (Spec (chartRing k d j)).ringCatSheaf.obj.obj
          (op (PrimeSpectrum.basicOpen
            (chartRatioElement k d l j)))) =
      (show
        Γ(chartModule k d M j,
          PrimeSpectrum.basicOpen
            (chartRatioElement k d l j))
        from
          chartRatioElement k d l j ^ C.totalExponent •
            chartSectionOnOverlap k d M l j
              (C.correctedSection l a)) := by
  exact correctedLocalHomAppRatioOneRaw C j l a

/-- Ambient-open form of the corrected transition equation.  Both sides
are now sections of `M` on `D₊(X_j) ∩ D₊(X_l)`, so this statement can be
used directly in open-cover gluing. -/
theorem restrict_correctedAmbientSection
    (C : CorrectedChartGeneratorExtensions k d E)
    (j l : Fin (d + 1)) (a : Fin G.count) :
    M.presheaf.map
        (homOfLE
          (show
            standardChart k j ⊓ standardChart k l ≤
              standardChart k j
            from inf_le_left)).op
        (C.correctedAmbientSection j a) =
      chartScalarOnPair k d l j
          (chartRatioElement k d l j) ^ C.totalExponent •
        M.presheaf.map
          (homOfLE
            (show
              standardChart k j ⊓ standardChart k l ≤
                standardChart k l
              from inf_le_right)).op
          (C.correctedAmbientSection l a) := by
  calc
    _ = (chartOverlapSectionsIso k d M l j).hom
          ((chartModule k d M j).presheaf.map
            (homOfLE
              (show PrimeSpectrum.basicOpen
                  (chartRatioElement k d l j) ≤ ⊤
                from le_top)).op
            (C.correctedSection j a)) :=
      (chartOverlapSectionsIso_hom_restrict_top
        k d M l j (C.correctedSection j a)).symm
    _ = (chartOverlapSectionsIso k d M l j).hom
          (chartRatioElement k d l j ^ C.totalExponent •
            chartSectionOnOverlap k d M l j
              (C.correctedSection l a)) :=
      congrArg (chartOverlapSectionsIso k d M l j).hom
        (C.restrict_correctedSection j l a)
    _ = chartScalarOnPair k d l j
            (chartRatioElement k d l j ^ C.totalExponent) •
          (chartOverlapSectionsIso k d M l j).hom
            (chartSectionOnOverlap k d M l j
              (C.correctedSection l a)) :=
      chartOverlapSectionsIso_hom_smul k d M l j
        (chartRatioElement k d l j ^ C.totalExponent) _
    _ = chartScalarOnPair k d l j
            (chartRatioElement k d l j) ^ C.totalExponent •
          (chartOverlapSectionsIso k d M l j).hom
            (chartSectionOnOverlap k d M l j
              (C.correctedSection l a)) := by
      rw [chartScalarOnPair_pow]
    _ = _ := congrArg
      (fun q => chartScalarOnPair k d l j
        (chartRatioElement k d l j) ^ C.totalExponent • q)
      (chartOverlapSectionsIso_hom_chartSectionOnOverlap
        k d M l j (C.correctedSection l a))

/-- The ambient transition equation restricted once more to an arbitrary
subopen of the pairwise intersection. -/
theorem restrict_correctedAmbientSection_over
    (C : CorrectedChartGeneratorExtensions k d E)
    (j l : Fin (d + 1)) (a : Fin G.count)
    (V : (Over
      (standardChart k j ⊓ standardChart k l))ᵒᵖ) :
    M.presheaf.map
        ((homOfLE
          (show standardChart k j ⊓ standardChart k l ≤
              standardChart k j from inf_le_left)).op ≫
            V.unop.hom.op)
        (C.correctedAmbientSection j a) =
      (scheme k d).presheaf.map V.unop.hom.op
          (chartScalarOnPair k d l j
            (chartRatioElement k d l j) ^ C.totalExponent) •
        M.presheaf.map
          ((homOfLE
            (show standardChart k j ⊓ standardChart k l ≤
                standardChart k l from inf_le_right)).op ≫
              V.unop.hom.op)
          (C.correctedAmbientSection l a) := by
  have h :=
    congrArg
      (fun q => M.presheaf.map V.unop.hom.op q)
      (C.restrict_correctedAmbientSection j l a)
  let q :=
    chartScalarOnPair k d l j
      (chartRatioElement k d l j) ^ C.totalExponent
  let t :=
    M.presheaf.map
      (homOfLE
        (show
          standardChart k j ⊓ standardChart k l ≤
            standardChart k l
          from inf_le_right)).op
      (C.correctedAmbientSection l a)
  have hsmul :
      M.presheaf.map V.unop.hom.op (q • t) =
        (scheme k d).presheaf.map V.unop.hom.op q •
          M.presheaf.map V.unop.hom.op t :=
    M.val.map_smul V.unop.hom.op q t
  change
    M.presheaf.map V.unop.hom.op
        (M.presheaf.map
          (homOfLE
            (show
              standardChart k j ⊓ standardChart k l ≤
                standardChart k j
              from inf_le_left)).op
          (C.correctedAmbientSection j a)) =
      M.presheaf.map V.unop.hom.op (q • t) at h
  rw [hsmul] at h
  rw [M.presheaf.map_comp, M.presheaf.map_comp]
  exact h

/-- The slice-site local map evaluated on the pairwise intersection has
the corrected Serre transition value. -/
theorem correctedOverHom_app_intersection_one
    (C : CorrectedChartGeneratorExtensions k d E)
    (j l : Fin (d + 1)) (a : Fin G.count) :
    (C.correctedOverHom j a).val.app
        (op (Over.mk
          (homOfLE
            (show
              standardChart k j ⊓ standardChart k l ≤
                standardChart k j
              from inf_le_left))))
        (1 : (scheme k d).ringCatSheaf.obj.obj
          (op (standardChart k j ⊓ standardChart k l))) =
      chartScalarOnPair k d l j
          (chartRatioElement k d l j) ^ C.totalExponent •
        M.presheaf.map
          (homOfLE
            (show
              standardChart k j ⊓ standardChart k l ≤
                standardChart k l
              from inf_le_right)).op
          (C.correctedAmbientSection l a) := by
  exact
    (homOfOpenSection_app_one M (standardChart k j)
      (C.correctedAmbientSection j a)
      (standardChart k j ⊓ standardChart k l)
      (show standardChart k j ⊓ standardChart k l ≤
          standardChart k j from inf_le_left)).trans
      (C.restrict_correctedAmbientSection j l a)

end CorrectedChartGeneratorExtensions

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

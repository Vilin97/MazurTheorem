/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveChartPairDefect
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveChartScalarCocycle

/-!
# Vanishing of projective-chart pair defects on the anchor overlap

The independently extended chart sections agree after restriction to
the anchor chart.  Transporting both sides to a common triple overlap
and using the coordinate-ratio cocycle shows that every pairwise defect
vanishes there.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

variable (k : Type) [CommRing k] (d : ℕ)

/-- Restricting a chart top section directly to a product ratio basic
open and then transporting it is ordinary restriction to the ambient
triple intersection. -/
theorem chartTripleSectionsIso_hom_restrict_top
    (M : (scheme k d).Modules)
    (i l j : Fin (d + 1))
    (s : Γ(chartModule k d M j, ⊤)) :
    (chartTripleSectionsIso k d M i l j).hom
        ((chartModule k d M j).presheaf.map
          (homOfLE
            (show chartRatioProductOpen k d i l j ≤ ⊤
              from le_top)).op s) =
      M.presheaf.map (homOfLE inf_le_left).op
        ((chartTopSectionsIso k d M j).hom s) := by
  dsimp only [chartTripleSectionsIso, chartTopSectionsIso]
  simp only [Iso.trans_hom, ConcreteCategory.comp_apply, id_eq]
  have hnat :
      (M.restrictAppIso ((standardAffineOpenCover k d).f j)
          (PrimeSpectrum.basicOpen
            (chartRatio k d i j * chartRatio k d l j))).hom
          ((chartModule k d M j).presheaf.map
            (homOfLE
              (show PrimeSpectrum.basicOpen
                  (chartRatio k d i j * chartRatio k d l j) ≤ ⊤
                from le_top)).op s) =
        M.presheaf.map
          (homOfLE
            (Scheme.Hom.image_mono
              ((standardAffineOpenCover k d).f j)
              (show PrimeSpectrum.basicOpen
                  (chartRatio k d i j * chartRatio k d l j) ≤ ⊤
                from le_top))).op
          ((M.restrictAppIso
            ((standardAffineOpenCover k d).f j) ⊤).hom s) := by
    exact congrArg
      (fun (φ : _ ⟶ _) => (ConcreteCategory.hom φ) s)
      (Scheme.Modules.map_restrictAppIso_hom
        ((standardAffineOpenCover k d).f j) M
        (homOfLE
          (show PrimeSpectrum.basicOpen
              (chartRatio k d i j * chartRatio k d l j) ≤ ⊤
            from le_top)).op)
  refine (congrArg
    (eqToIso (congrArg (fun U => Γ(M, U))
      (standardAffineCover_image_chartRatio_mul
        k d i l j))).hom hnat).trans ?_
  exact
    module_presheaf_map_eqToIso_apply M.presheaf
      (standardAffineCover_image_chartRatio_mul k d i l j)
      (standardAffineCover_image_top k d j)
      _ inf_le_left
      ((M.restrictAppIso
        ((standardAffineOpenCover k d).f j) ⊤).hom s)

/-- A section coming from chart `l`, restricted in chart `j` and then
transported to the common triple overlap, is its ordinary ambient
restriction from the `l`-th standard open. -/
theorem chartTripleSectionsIso_hom_chartSectionOnOverlap_right
    (M : (scheme k d).Modules)
    (i l j : Fin (d + 1))
    (s : Γ(chartModule k d M l, ⊤)) :
    (chartTripleSectionsIso k d M i l j).hom
        ((chartModule k d M j).presheaf.map
          (homOfLE
            (PrimeSpectrum.basicOpen_mul_le_right
              (chartRatioElement k d i j)
              (chartRatioElement k d l j))).op
          (chartSectionOnOverlap k d M l j s)) =
      M.presheaf.map
        (homOfLE (inf_le_right.trans inf_le_right)).op
        ((chartTopSectionsIso k d M l).hom s) := by
  rw [chartTripleSectionsIso_hom_restrict_pairJL,
    chartOverlapSectionsIso_hom_chartSectionOnOverlap]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The analogous identity for a section coming from the first
non-base chart in the product ratio basic open. -/
theorem chartTripleSectionsIso_hom_chartSectionOnOverlap_left
    (M : (scheme k d).Modules)
    (i l j : Fin (d + 1))
    (s : Γ(chartModule k d M i, ⊤)) :
    (chartTripleSectionsIso k d M i l j).hom
        ((chartModule k d M j).presheaf.map
          (homOfLE
            (PrimeSpectrum.basicOpen_mul_le_left
              (chartRatioElement k d i j)
              (chartRatioElement k d l j))).op
          (chartSectionOnOverlap k d M i j s)) =
      M.presheaf.map
        (homOfLE (inf_le_right.trans inf_le_left)).op
        ((chartTopSectionsIso k d M i).hom s) := by
  rw [chartTripleSectionsIso_hom_restrict_pairJI,
    chartOverlapSectionsIso_hom_chartSectionOnOverlap]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The anchor-chart section restricted to the common ambient triple
intersection. -/
def chartAnchorSectionOnTriple
    (M : (scheme k d).Modules)
    (i l j : Fin (d + 1))
    (s : Γ(chartModule k d M i, ⊤)) :
    Γ(M, standardChart k j ⊓
      (standardChart k i ⊓ standardChart k l)) :=
  M.presheaf.map
    (homOfLE (inf_le_right.trans inf_le_left)).op
    ((chartTopSectionsIso k d M i).hom s)

lemma sectionSmul_eq_smul_chart
    (M : (scheme k d).Modules) (j : Fin (d + 1))
    (U : (Spec (chartRing k d j)).Opens)
    (r : chartRing k d j) (x : Γ(chartModule k d M j, U)) :
    QuasicoherentTilde.sectionSmul r x = r • x :=
  rfl

theorem ChartGeneratorExtensions.restrict_extended_chartRatioOpen
    {M : (scheme k d).Modules} {i : Fin (d + 1)}
    {G : ChartGenerators k d M i}
    (E : ChartGeneratorExtensions k d G)
    (j : Fin (d + 1)) (a : Fin G.count) :
    (chartModule k d M j).presheaf.map
        (homOfLE
          (show chartRatioOpen k d i j ≤ ⊤ from le_top)).op
        (E.extended j a) =
      QuasicoherentTilde.sectionSmul
        (chartRatioElement k d i j ^ E.exponent)
        (chartSectionOnOverlap k d M i j (G.generator a)) := by
  exact E.restrict_extended j a

theorem chartTripleSectionsIso_hom_sectionSmul
    (M : (scheme k d).Modules)
    (i l j : Fin (d + 1))
    (r : chartRing k d j)
    (s : Γ(chartModule k d M j,
      chartRatioProductOpen k d i l j)) :
    (chartTripleSectionsIso k d M i l j).hom
        (QuasicoherentTilde.sectionSmul r s) =
      chartScalarOnTriple k d i l j r •
        (chartTripleSectionsIso k d M i l j).hom s := by
  rw [sectionSmul_eq_smul_chart]
  exact chartTripleSectionsIso_hom_smul k d M i l j r s

theorem chartOverlapSectionsIso_hom_sectionSmul
    (M : (scheme k d).Modules)
    (i j : Fin (d + 1))
    (r : chartRing k d j)
    (s : Γ(chartModule k d M j,
      chartRatioOpen k d i j)) :
    (chartOverlapSectionsIso k d M i j).hom
        (QuasicoherentTilde.sectionSmul r s) =
      chartScalarOnPair k d i j r •
        (chartOverlapSectionsIso k d M i j).hom s := by
  rw [sectionSmul_eq_smul_chart]
  exact chartOverlapSectionsIso_hom_smul k d M i j r s

/-- On the common triple overlap, the extension chosen on chart `j` is
the anchor generator multiplied by the transition scalar from chart
`i` to chart `j`. -/
theorem chartGeneratorExtensionOnTriple
    {M : (scheme k d).Modules} {i : Fin (d + 1)}
    {G : ChartGenerators k d M i}
    (E : ChartGeneratorExtensions k d G)
    (j l : Fin (d + 1)) (a : Fin G.count) :
    (chartTripleSectionsIso k d M i l j).hom
        ((chartModule k d M j).presheaf.map
          (homOfLE
            (show chartRatioProductOpen k d i l j ≤ ⊤
              from le_top)).op
          (E.extended j a)) =
      chartScalarOnTriple k d i l j
            (chartRatioElement k d i j) ^ E.exponent •
        chartAnchorSectionOnTriple k d M i l j
          (G.generator a) := by
  let hWU :
      chartRatioProductOpen k d i l j ≤
        chartRatioOpen k d i j :=
    PrimeSpectrum.basicOpen_mul_le_left
      (chartRatioElement k d i j)
      (chartRatioElement k d l j)
  let hUT :
      chartRatioOpen k d i j ≤
        (⊤ : (Spec (chartRing k d j)).Opens) :=
    le_top
  let scale
      (r : chartRing k d j)
      (x : Γ(chartModule k d M j,
        chartRatioProductOpen k d i l j)) :
      Γ(chartModule k d M j,
        chartRatioProductOpen k d i l j) :=
    QuasicoherentTilde.sectionSmul r x
  calc
    _ = (chartTripleSectionsIso k d M i l j).hom
          ((chartModule k d M j).presheaf.map
            (homOfLE hWU).op
            ((chartModule k d M j).presheaf.map
              (homOfLE hUT).op (E.extended j a))) := by
        congr 1
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        rfl
    _ = (chartTripleSectionsIso k d M i l j).hom
          ((chartModule k d M j).presheaf.map
            (homOfLE hWU).op
            (QuasicoherentTilde.sectionSmul
              (chartRatioElement k d i j ^ E.exponent)
                (chartSectionOnOverlap k d M i j
                  (G.generator a)))) := by
        have hr :
            (chartModule k d M j).presheaf.map
                (homOfLE hUT).op (E.extended j a) =
              QuasicoherentTilde.sectionSmul
                (chartRatioElement k d i j ^ E.exponent)
                (chartSectionOnOverlap k d M i j
                  (G.generator a)) := by
          exact E.restrict_extended_chartRatioOpen k d j a
        exact congrArg (fun x =>
          (chartTripleSectionsIso k d M i l j).hom
            ((chartModule k d M j).presheaf.map
              (homOfLE hWU).op x)) hr
    _ = (chartTripleSectionsIso k d M i l j).hom
          (scale (chartRatioElement k d i j ^ E.exponent)
            ((chartModule k d M j).presheaf.map
                (homOfLE hWU).op
                (chartSectionOnOverlap k d M i j
                  (G.generator a)))) := by
        have hm := QuasicoherentTilde.map_sectionSmul_Spec
          (M := chartModule k d M j) (homOfLE hWU).op
          (chartRatioElement k d i j ^ E.exponent)
          (chartSectionOnOverlap k d M i j (G.generator a))
        exact congrArg
          (fun x => (chartTripleSectionsIso k d M i l j).hom x) hm
    _ = chartScalarOnTriple k d i l j
            (chartRatioElement k d i j ^ E.exponent) •
          (chartTripleSectionsIso k d M i l j).hom
            ((chartModule k d M j).presheaf.map
              (homOfLE hWU).op
              (chartSectionOnOverlap k d M i j
                  (G.generator a))) := by
        exact chartTripleSectionsIso_hom_sectionSmul
          k d M i l j _ _
    _ = chartScalarOnTriple k d i l j
            (chartRatioElement k d i j) ^ E.exponent •
          chartAnchorSectionOnTriple k d M i l j
            (G.generator a) := by
        rw [chartScalarOnTriple_pow]
        have hx :
            (chartTripleSectionsIso k d M i l j).hom
                ((chartModule k d M j).presheaf.map
                  (homOfLE hWU).op
                  (chartSectionOnOverlap k d M i j
                    (G.generator a))) =
              chartAnchorSectionOnTriple k d M i l j
                (G.generator a) := by
          exact chartTripleSectionsIso_hom_chartSectionOnOverlap_left
            k d M i l j (G.generator a)
        rw [hx]

/-- The extension chosen on chart `l`, restricted to the common triple
overlap, is the anchor generator multiplied by the transition scalar
transported from chart `l`. -/
theorem chartGeneratorExtensionFromLOnTriple
    {M : (scheme k d).Modules} {i : Fin (d + 1)}
    {G : ChartGenerators k d M i}
    (E : ChartGeneratorExtensions k d G)
    (j l : Fin (d + 1)) (a : Fin G.count) :
    M.presheaf.map
        (homOfLE (inf_le_right.trans inf_le_right)).op
        ((chartTopSectionsIso k d M l).hom
          (E.extended l a)) =
      chartScalarFromLOnTriple k d i l j
            (chartRatioElement k d i l) ^ E.exponent •
        chartAnchorSectionOnTriple k d M i l j
          (G.generator a) := by
  let hTP := chartTriple_le_pairLI k d i l j
  let hPUl :
      standardChart k l ⊓ standardChart k i ≤
        standardChart k l :=
    inf_le_left
  let hPUi :
      standardChart k l ⊓ standardChart k i ≤
        standardChart k i :=
    inf_le_right
  calc
    _ = M.presheaf.map (homOfLE hTP).op
          (M.presheaf.map (homOfLE hPUl).op
            ((chartTopSectionsIso k d M l).hom
              (E.extended l a))) := by
        let x :=
          (chartTopSectionsIso k d M l).hom
            (E.extended l a)
        have hmaps :
            M.presheaf.map (homOfLE hPUl).op ≫
                M.presheaf.map (homOfLE hTP).op =
              M.presheaf.map
                (homOfLE
                  (inf_le_right.trans inf_le_right)).op := by
          rw [← Functor.map_comp]
          rfl
        exact (congrArg
          (fun (φ : _ ⟶ _) =>
            (ConcreteCategory.hom φ) x) hmaps).symm
    _ = M.presheaf.map (homOfLE hTP).op
          ((chartOverlapSectionsIso k d M i l).hom
            ((chartModule k d M l).presheaf.map
              (homOfLE
                (show chartRatioOpen k d i l ≤ ⊤
                  from le_top)).op
              (E.extended l a))) := by
        have ht :
            (chartOverlapSectionsIso k d M i l).hom
                ((chartModule k d M l).presheaf.map
                  (homOfLE
                    (show chartRatioOpen k d i l ≤ ⊤
                      from le_top)).op
                  (E.extended l a)) =
              M.presheaf.map (homOfLE hPUl).op
                ((chartTopSectionsIso k d M l).hom
                  (E.extended l a)) := by
          exact chartOverlapSectionsIso_hom_restrict_top
            k d M i l (E.extended l a)
        exact congrArg (fun x =>
          M.presheaf.map (homOfLE hTP).op x) ht.symm
    _ = M.presheaf.map (homOfLE hTP).op
          ((chartOverlapSectionsIso k d M i l).hom
            (QuasicoherentTilde.sectionSmul
              (chartRatioElement k d i l ^ E.exponent)
              (chartSectionOnOverlap k d M i l
                (G.generator a)))) := by
        have hr :
            (chartModule k d M l).presheaf.map
                (homOfLE
                  (show chartRatioOpen k d i l ≤ ⊤
                    from le_top)).op
                (E.extended l a) =
              QuasicoherentTilde.sectionSmul
                (chartRatioElement k d i l ^ E.exponent)
                (chartSectionOnOverlap k d M i l
                  (G.generator a)) := by
          exact E.restrict_extended_chartRatioOpen k d l a
        exact congrArg (fun x =>
          M.presheaf.map (homOfLE hTP).op
            ((chartOverlapSectionsIso k d M i l).hom x)) hr
    _ = M.presheaf.map (homOfLE hTP).op
          (chartScalarOnPair k d i l
                (chartRatioElement k d i l ^
                  E.exponent) •
            (chartOverlapSectionsIso k d M i l).hom
              (chartSectionOnOverlap k d M i l
                (G.generator a))) := by
        have hs := chartOverlapSectionsIso_hom_sectionSmul
          k d M i l (chartRatioElement k d i l ^ E.exponent)
          (chartSectionOnOverlap k d M i l (G.generator a))
        exact congrArg (fun x =>
          M.presheaf.map (homOfLE hTP).op x) hs
    _ = (scheme k d).presheaf.map
            (homOfLE hTP).op
            (chartScalarOnPair k d i l
              (chartRatioElement k d i l ^
                E.exponent)) •
          M.presheaf.map (homOfLE hTP).op
            ((chartOverlapSectionsIso k d M i l).hom
              (chartSectionOnOverlap k d M i l
                (G.generator a))) := by
        rw [Scheme.Modules.map_smul]
    _ = chartScalarFromLOnTriple k d i l j
            (chartRatioElement k d i l ^
              E.exponent) •
          chartAnchorSectionOnTriple k d M i l j
            (G.generator a) := by
        rw [chartScalarFromLOnTriple_eq_restrict_pairLI,
          chartOverlapSectionsIso_hom_chartSectionOnOverlap]
        congr 1
        dsimp only [chartAnchorSectionOnTriple]
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        rfl
    _ = chartScalarFromLOnTriple k d i l j
            (chartRatioElement k d i l) ^ E.exponent •
          chartAnchorSectionOnTriple k d M i l j
            (G.generator a) := by
        rw [chartScalarFromLOnTriple_pow]

/-- After transporting to ambient sections, the anchor-overlap defect is
the difference of the two scalar presentations of the same anchor
generator. -/
theorem chartPairDefectOnAnchorOverlap_transport
    {M : (scheme k d).Modules} {i : Fin (d + 1)}
    {G : ChartGenerators k d M i}
    (E : ChartGeneratorExtensions k d G)
    (j l : Fin (d + 1)) (a : Fin G.count) :
    (chartTripleSectionsIso k d M i l j).hom
        (chartPairDefectOnAnchorOverlap k d E j l a) =
      chartScalarOnTriple k d i l j
            (chartRatioElement k d i j) ^ E.exponent •
          chartAnchorSectionOnTriple k d M i l j
            (G.generator a) -
        chartScalarOnTriple k d i l j
              (chartRatioElement k d l j) ^ E.exponent •
          (chartScalarFromLOnTriple k d i l j
                (chartRatioElement k d i l) ^ E.exponent •
            chartAnchorSectionOnTriple k d M i l j
              (G.generator a)) := by
  let hWP :
      chartRatioProductOpen k d i l j ≤
        chartRatioOpen k d l j :=
    PrimeSpectrum.basicOpen_mul_le_right
      (chartRatioElement k d i j)
      (chartRatioElement k d l j)
  let hPT :
      chartRatioOpen k d l j ≤
        (⊤ : (Spec (chartRing k d j)).Opens) :=
    le_top
  let scale
      (r : chartRing k d j)
      (x : Γ(chartModule k d M j,
        chartRatioProductOpen k d i l j)) :
      Γ(chartModule k d M j,
        chartRatioProductOpen k d i l j) :=
    QuasicoherentTilde.sectionSmul r x
  have hfirst :
      (chartTripleSectionsIso k d M i l j).hom
          ((chartModule k d M j).presheaf.map
            (homOfLE hWP).op
            ((chartModule k d M j).presheaf.map
              (homOfLE hPT).op
              (E.extended j a))) =
        chartScalarOnTriple k d i l j
              (chartRatioElement k d i j) ^ E.exponent •
          chartAnchorSectionOnTriple k d M i l j
            (G.generator a) := by
    rw [← chartGeneratorExtensionOnTriple k d E j l a]
    congr 1
    let x := E.extended j a
    have hmaps :
        (chartModule k d M j).presheaf.map
              (homOfLE hPT).op ≫
            (chartModule k d M j).presheaf.map
              (homOfLE hWP).op =
          (chartModule k d M j).presheaf.map
            (homOfLE
            (show chartRatioProductOpen k d i l j ≤ ⊤
                from le_top)).op := by
      rw [← Functor.map_comp]
      rfl
    exact (congrArg
      (fun (φ : _ ⟶ _) =>
        (ConcreteCategory.hom φ) x) hmaps)
  have hsecond :
      (chartTripleSectionsIso k d M i l j).hom
          (scale
            (chartRatioElement k d l j ^ E.exponent)
            ((chartModule k d M j).presheaf.map
              (homOfLE hWP).op
              (chartSectionOnOverlap k d M l j
                (E.extended l a)))) =
        chartScalarOnTriple k d i l j
              (chartRatioElement k d l j) ^ E.exponent •
          (chartScalarFromLOnTriple k d i l j
                (chartRatioElement k d i l) ^ E.exponent •
            chartAnchorSectionOnTriple k d M i l j
              (G.generator a)) := by
    rw [chartTripleSectionsIso_hom_sectionSmul,
      chartScalarOnTriple_pow]
    have hx :
        (chartTripleSectionsIso k d M i l j).hom
            ((chartModule k d M j).presheaf.map
              (homOfLE hWP).op
              (chartSectionOnOverlap k d M l j
                (E.extended l a))) =
          M.presheaf.map
            (homOfLE (inf_le_right.trans inf_le_right)).op
            ((chartTopSectionsIso k d M l).hom
              (E.extended l a)) := by
      exact chartTripleSectionsIso_hom_chartSectionOnOverlap_right
        k d M i l j (E.extended l a)
    rw [hx, chartGeneratorExtensionFromLOnTriple]
  change
    (chartTripleSectionsIso k d M i l j).hom
        ((chartModule k d M j).presheaf.map
          (homOfLE hWP).op
          ((chartModule k d M j).presheaf.map
              (homOfLE hPT).op (E.extended j a) -
            QuasicoherentTilde.sectionSmul
              (chartRatioElement k d l j ^ E.exponent)
              (chartSectionOnOverlap k d M l j
                (E.extended l a)))) = _
  calc
    _ = (chartTripleSectionsIso k d M i l j).hom
          ((chartModule k d M j).presheaf.map
              (homOfLE hWP).op
              ((chartModule k d M j).presheaf.map
                (homOfLE hPT).op (E.extended j a)) -
            scale
              (chartRatioElement k d l j ^ E.exponent)
              ((chartModule k d M j).presheaf.map
                (homOfLE hWP).op
                (chartSectionOnOverlap k d M l j
                  (E.extended l a)))) := by
        rw [map_sub,
          QuasicoherentTilde.map_sectionSmul_Spec]
    _ = (chartTripleSectionsIso k d M i l j).hom
            ((chartModule k d M j).presheaf.map
              (homOfLE hWP).op
              ((chartModule k d M j).presheaf.map
                (homOfLE hPT).op (E.extended j a))) -
          (chartTripleSectionsIso k d M i l j).hom
            (scale
              (chartRatioElement k d l j ^ E.exponent)
              ((chartModule k d M j).presheaf.map
                (homOfLE hWP).op
                (chartSectionOnOverlap k d M l j
                  (E.extended l a)))) := by
        rw [map_sub]
    _ = _ := by
        rw [hfirst, hsecond]

/-- Every pairwise defect vanishes after restricting to the triple
overlap with the anchor chart. -/
theorem chartPairDefectOnAnchorOverlap_eq_zero
    {M : (scheme k d).Modules} {i : Fin (d + 1)}
    {G : ChartGenerators k d M i}
    (E : ChartGeneratorExtensions k d G)
    (j l : Fin (d + 1)) (a : Fin G.count) :
    chartPairDefectOnAnchorOverlap k d E j l a = 0 := by
  apply
    (chartTripleSectionsIso k d M i l j).addCommGroupIsoToAddEquiv.injective
  rw [Iso.addCommGroupIsoToAddEquiv_apply,
    Iso.addCommGroupIsoToAddEquiv_apply]
  rw [chartPairDefectOnAnchorOverlap_transport]
  simp only [map_zero, smul_smul]
  rw [chartScalarOnTriple_cocycle_pow]
  exact sub_self _

/-- A common correcting exponent exists without any additional
compatibility hypothesis: triple-overlap compatibility follows from the
anchor transition equations and the scalar cocycle. -/
theorem CorrectedChartGeneratorExtensions.exists_unconditionally
    {M : (scheme k d).Modules} [M.IsQuasicoherent]
    {i : Fin (d + 1)}
    {G : ChartGenerators k d M i}
    (E : ChartGeneratorExtensions k d G) :
    Nonempty (CorrectedChartGeneratorExtensions k d E) :=
  CorrectedChartGeneratorExtensions.exists k d E
    (chartPairDefectOnAnchorOverlap_eq_zero k d E)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveChartPairScalarCocycle

/-!
# Corrected compatible projective-chart sections

The common power annihilating all pairwise defects is absorbed into the
chart sections themselves.  The pair scalar cocycle then upgrades defect
annihilation to the exact transition equation for a single Serre twist.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

variable (k : Type) [CommRing k] (d : ℕ)

private def chartMapSectionSmulRaw
    (M : (scheme k d).Modules) (l j : Fin (d + 1))
    (r : chartRing k d l) (s : Γ(chartModule k d M l, ⊤)) :=
  congrArg (chartOverlapSectionsIso k d M j l).hom
    (QuasicoherentTilde.map_sectionSmul_Spec
      (M := chartModule k d M l)
      (homOfLE
        (show PrimeSpectrum.basicOpen
            (chartRatioElement k d j l) ≤ ⊤
          from le_top)).op r s)

private def chartMapSmulToSectionSmulRaw
    (M : (scheme k d).Modules) (l j : Fin (d + 1))
    (r : chartRing k d l) (s : Γ(chartModule k d M l, ⊤)) :=
  congrArg
    (fun x =>
      (chartOverlapSectionsIso k d M j l).hom
        ((chartModule k d M l).presheaf.map
          (homOfLE
            (show PrimeSpectrum.basicOpen
                (chartRatioElement k d j l) ≤ ⊤
              from le_top)).op x))
    (sectionSmul_eq_smul_chart k d M l ⊤ r s).symm

private def chartOverlapSectionsIso_hom_map_smul_top_raw
    (M : (scheme k d).Modules) (l j : Fin (d + 1))
    (r : chartRing k d l) (s : Γ(chartModule k d M l, ⊤)) :=
  (chartMapSmulToSectionSmulRaw k d M l j r s).trans
    ((chartMapSectionSmulRaw k d M l j r s).trans
      (chartOverlapSectionsIso_hom_sectionSmul k d M j l r _))

private theorem sectionSmul_eq_of_sectionSmul_sub_eq_zero
    {R : CommRingCat} {M : (Spec R).Modules}
    {U : (Spec R).Opens} (r : R) (x y : Γ(M, U))
    (h : QuasicoherentTilde.sectionSmul r (x - y) = 0) :
    QuasicoherentTilde.sectionSmul r x =
      QuasicoherentTilde.sectionSmul r y :=
  sub_eq_zero.mp
    ((QuasicoherentTilde.sectionSmul_sub r x y).symm.trans h)

private theorem chartOverlapSectionsIso_hom_sectionSmul_two
    (M : (scheme k d).Modules) (i j : Fin (d + 1))
    (r q : chartRing k d j)
    (s : Γ(chartModule k d M j, chartRatioOpen k d i j)) :
    (chartOverlapSectionsIso k d M i j).hom
        (QuasicoherentTilde.sectionSmul r
          (QuasicoherentTilde.sectionSmul q s)) =
      chartScalarOnPair k d i j r •
        (chartScalarOnPair k d i j q •
          (chartOverlapSectionsIso k d M i j).hom s) :=
  (chartOverlapSectionsIso_hom_sectionSmul k d M i j r _).trans
    (congrArg (fun y => chartScalarOnPair k d i j r • y)
      (chartOverlapSectionsIso_hom_sectionSmul k d M i j q s))

/-- Multiplying a top section on chart `l` by a chart-`l` scalar and then
transporting it to the `j,l` overlap is semilinear for the cross-chart
ambient scalar. -/
theorem chartOverlapSectionsIso_hom_chartSectionOnOverlap_smul
    (M : (scheme k d).Modules)
    (l j : Fin (d + 1))
    (r : chartRing k d l)
    (s : Γ(chartModule k d M l, ⊤)) :
    (chartOverlapSectionsIso k d M l j).hom
        (chartSectionOnOverlap k d M l j (r • s)) =
      chartScalarFromLOnPair k d l j r •
        (chartOverlapSectionsIso k d M l j).hom
          (chartSectionOnOverlap k d M l j s) := by
  rw [chartOverlapSectionsIso_hom_chartSectionOnOverlap,
    chartOverlapSectionsIso_hom_chartSectionOnOverlap]
  let hSwap :
      standardChart k l ⊓ standardChart k j =
        standardChart k j ⊓ standardChart k l :=
    inf_comm _ _
  let E :=
    eqToIso (congrArg (fun U => Γ(M, U)) hSwap)
  let hNativeUl :
      standardChart k l ⊓ standardChart k j ≤
        standardChart k l :=
    inf_le_left
  let hCommonUl :
      standardChart k j ⊓ standardChart k l ≤
        standardChart k l :=
    inf_le_right
  have hnative :
      M.presheaf.map (homOfLE hNativeUl).op
          ((chartTopSectionsIso k d M l).hom (r • s)) =
        chartScalarOnPair k d j l r •
          M.presheaf.map (homOfLE hNativeUl).op
            ((chartTopSectionsIso k d M l).hom s) := by
    calc
      _ = (chartOverlapSectionsIso k d M j l).hom
            ((chartModule k d M l).presheaf.map
              (homOfLE
                (show PrimeSpectrum.basicOpen
                    (chartRatioElement k d j l) ≤ ⊤
                  from le_top)).op
              (r • s)) :=
          (chartOverlapSectionsIso_hom_restrict_top
            k d M j l (r • s)).symm
      _ = (chartOverlapSectionsIso k d M j l).hom
            (QuasicoherentTilde.sectionSmul r
              ((chartModule k d M l).presheaf.map
                (homOfLE
                  (show PrimeSpectrum.basicOpen
                      (chartRatioElement k d j l) ≤ ⊤
                    from le_top)).op s)) := by
          exact chartMapSectionSmulRaw k d M l j r s
      _ = chartScalarOnPair k d j l r •
            (chartOverlapSectionsIso k d M j l).hom
              ((chartModule k d M l).presheaf.map
                (homOfLE
                  (show PrimeSpectrum.basicOpen
                      (chartRatioElement k d j l) ≤ ⊤
                    from le_top)).op s) := by
          exact chartOverlapSectionsIso_hom_sectionSmul
            k d M j l r _
      _ = chartScalarOnPair k d j l r •
            M.presheaf.map (homOfLE hNativeUl).op
              ((chartTopSectionsIso k d M l).hom s) := by
          exact congrArg
            (fun y => chartScalarOnPair k d j l r • y)
            (chartOverlapSectionsIso_hom_restrict_top
              k d M j l s)
  have hcast (x : Γ(chartModule k d M l, ⊤)) :
      E.hom
          (M.presheaf.map (homOfLE hNativeUl).op
            ((chartTopSectionsIso k d M l).hom x)) =
        M.presheaf.map (homOfLE hCommonUl).op
          ((chartTopSectionsIso k d M l).hom x) := by
    exact
      module_presheaf_map_eqToIso_apply M.presheaf
        hSwap
        (rfl : standardChart k l = standardChart k l)
        hNativeUl hCommonUl
        ((chartTopSectionsIso k d M l).hom x)
  calc
    _ = E.hom
          (M.presheaf.map (homOfLE hNativeUl).op
            ((chartTopSectionsIso k d M l).hom (r • s))) :=
        (hcast (r • s)).symm
    _ = E.hom
          (chartScalarOnPair k d j l r •
            M.presheaf.map (homOfLE hNativeUl).op
              ((chartTopSectionsIso k d M l).hom s)) :=
        congrArg E.hom hnative
    _ = chartScalarFromLOnPair k d l j r •
          E.hom
            (M.presheaf.map (homOfLE hNativeUl).op
              ((chartTopSectionsIso k d M l).hom s)) := by
        exact eqToIso_smul_apply M hSwap _ _
    _ = chartScalarFromLOnPair k d l j r •
          M.presheaf.map (homOfLE hCommonUl).op
            ((chartTopSectionsIso k d M l).hom s) := by
        rw [hcast]

namespace CorrectedChartGeneratorExtensions

variable {k d}
variable {M : (scheme k d).Modules} {i : Fin (d + 1)}
variable {G : ChartGenerators k d M i}
variable {E : ChartGeneratorExtensions k d G}

/-- The twist degree after absorbing the common defect-clearing power. -/
def totalExponent
    (C : CorrectedChartGeneratorExtensions k d E) : ℕ :=
  E.exponent + C.correctionExponent

/-- The corrected generator section on a standard affine chart. -/
def correctedSection
    (C : CorrectedChartGeneratorExtensions k d E)
    (j : Fin (d + 1)) (a : Fin G.count) :
    Γ(chartModule k d M j, ⊤) :=
  chartRatioElement k d i j ^ C.correctionExponent •
    E.extended j a

/-- Corrected chart sections satisfy the exact degree transition
equation on every pairwise overlap. -/
theorem restrict_correctedSection
    (C : CorrectedChartGeneratorExtensions k d E)
    (j l : Fin (d + 1)) (a : Fin G.count) :
    (chartModule k d M j).presheaf.map
        (homOfLE
          (show PrimeSpectrum.basicOpen
              (chartRatioElement k d l j) ≤ ⊤
            from le_top)).op
        (C.correctedSection j a) =
      (show
        Γ(chartModule k d M j,
          PrimeSpectrum.basicOpen
            (chartRatioElement k d l j))
        from
          chartRatioElement k d l j ^ C.totalExponent •
            chartSectionOnOverlap k d M l j
              (C.correctedSection l a)) := by
  have hdef :
      QuasicoherentTilde.sectionSmul
          (chartRatioElement k d i j ^
          C.correctionExponent)
          ((chartModule k d M j).presheaf.map
              (homOfLE
                (show PrimeSpectrum.basicOpen
                    (chartRatioElement k d l j) ≤ ⊤
                  from le_top)).op
              (E.extended j a)) =
        QuasicoherentTilde.sectionSmul
            (chartRatioElement k d i j ^
            C.correctionExponent)
          (QuasicoherentTilde.sectionSmul
            (chartRatioElement k d l j ^ E.exponent)
            (chartSectionOnOverlap k d M l j
              (E.extended l a))) := by
    have h := C.defect_annihilated j l a
    unfold chartPairDefect at h
    exact sectionSmul_eq_of_sectionSmul_sub_eq_zero
      (chartRatioElement k d i j ^ C.correctionExponent) _ _ h
  have hambientRaw := congrArg
    (chartOverlapSectionsIso k d M l j).hom hdef
  have hambient :=
    (chartOverlapSectionsIso_hom_sectionSmul
      k d M l j
      (chartRatioElement k d i j ^ C.correctionExponent) _).symm.trans
      (hambientRaw.trans
        (chartOverlapSectionsIso_hom_sectionSmul_two
          k d M l j
          (chartRatioElement k d i j ^ C.correctionExponent)
          (chartRatioElement k d l j ^ E.exponent) _))
  rw [chartScalarOnPair_pow, chartScalarOnPair_pow] at hambient
  have hscalar :
      chartScalarOnPair k d l j
              (chartRatioElement k d i j) ^
            C.correctionExponent *
          chartScalarOnPair k d l j
              (chartRatioElement k d l j) ^
            E.exponent =
        chartScalarOnPair k d l j
              (chartRatioElement k d l j) ^
            C.totalExponent *
          chartScalarFromLOnPair k d l j
              (chartRatioElement k d i l) ^
            C.correctionExponent := by
    rw [totalExponent, pow_add, mul_assoc,
      chartScalarOnPair_cocycle_pow, mul_comm]
  apply
    (chartOverlapSectionsIso k d M l j).addCommGroupIsoToAddEquiv.injective
  rw [Iso.addCommGroupIsoToAddEquiv_apply]
  calc
    _ = chartScalarOnPair k d l j
            (chartRatioElement k d i j) ^
          C.correctionExponent •
        (chartOverlapSectionsIso k d M l j).hom
          ((chartModule k d M j).presheaf.map
            (homOfLE
              (show PrimeSpectrum.basicOpen
                  (chartRatioElement k d l j) ≤ ⊤
                from le_top)).op
            (E.extended j a)) := by
        rw [correctedSection]
        exact
          (chartOverlapSectionsIso_hom_map_smul_top_raw
            k d M j l
            (chartRatioElement k d i j ^ C.correctionExponent)
            (E.extended j a)).trans
            (congrArg
              (fun q => q •
                (chartOverlapSectionsIso k d M l j).hom
                  ((chartModule k d M j).presheaf.map
                    (homOfLE
                      (show PrimeSpectrum.basicOpen
                          (chartRatioElement k d l j) ≤ ⊤
                        from le_top)).op
                    (E.extended j a)))
              (chartScalarOnPair_pow k d l j
                (chartRatioElement k d i j)
                C.correctionExponent))
    _ = chartScalarOnPair k d l j
            (chartRatioElement k d i j) ^
          C.correctionExponent •
        (chartScalarOnPair k d l j
              (chartRatioElement k d l j) ^
            E.exponent •
          (chartOverlapSectionsIso k d M l j).hom
            (chartSectionOnOverlap k d M l j
              (E.extended l a))) :=
        hambient
    _ = chartScalarOnPair k d l j
            (chartRatioElement k d l j) ^
          C.totalExponent •
        (chartScalarFromLOnPair k d l j
              (chartRatioElement k d i l) ^
            C.correctionExponent •
          (chartOverlapSectionsIso k d M l j).hom
            (chartSectionOnOverlap k d M l j
              (E.extended l a))) := by
        rw [smul_smul, smul_smul, hscalar]
    _ = chartScalarOnPair k d l j
            (chartRatioElement k d l j) ^
          C.totalExponent •
        (chartOverlapSectionsIso k d M l j).hom
          (chartSectionOnOverlap k d M l j
            (C.correctedSection l a)) := by
        rw [correctedSection,
          chartOverlapSectionsIso_hom_chartSectionOnOverlap_smul,
          chartScalarFromLOnPair_pow]
    _ = (chartOverlapSectionsIso k d M l j).hom
          (chartRatioElement k d l j ^ C.totalExponent •
            chartSectionOnOverlap k d M l j
              (C.correctedSection l a)) := by
        rw [chartOverlapSectionsIso_hom_smul,
          chartScalarOnPair_pow]

end CorrectedChartGeneratorExtensions

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

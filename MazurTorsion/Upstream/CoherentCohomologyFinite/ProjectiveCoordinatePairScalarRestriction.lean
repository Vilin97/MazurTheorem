/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveCoordinateTwistCompatibility

/-!
# Restricting projective coordinate scalars to pair overlaps

The homogeneous-localization section attached to an affine-chart
scalar restricts to the pair-overlap scalar used in the chart cocycle.
Keeping this calculation separate prevents the cover-descent proof from
unfolding the projective `awayToSection` comparison repeatedly.
-/


open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
open HomogeneousLocalization

variable (k : Type) [CommRing k] (d : ℕ)

noncomputable def chartAwayRestrictionSection
    (i j : Fin (d + 1)) (r : chartRing k d j) :
    Γ(scheme k d, standardChart k j ⊓ standardChart k i) :=
  (scheme k d).presheaf.map
    (homOfLE
      (show standardChart k j ⊓ standardChart k i ≤
        standardChart k j from inf_le_left)).op
    (Proj.awayToSection (homogeneousGrading k d)
      (coordinate k j) r)

noncomputable def chartAwayProductSection
    (i j : Fin (d + 1)) (r : chartRing k d j) :
    Γ(scheme k d,
      Proj.basicOpen (homogeneousGrading k d)
        (coordinate k i * coordinate k j)) :=
  Proj.awayToSection (homogeneousGrading k d)
    (coordinate k i * coordinate k j)
    (chartPairAwayOfElement k d i j r)

/-- Changing the chosen product equality in `awayMap` is the corresponding
equality transport on the target homogeneous localization. -/
theorem awayMap_eq_cast_of_eq
    {R A : Type} [CommRing R] [CommRing A] [Module R A]
    {𝒜 : ℕ → Submodule R A} [GradedRing 𝒜]
    {q : ℕ} {f g x : A} (hg : g ∈ 𝒜 q)
    (h : x = f * g) (r : Away 𝒜 f) :
    awayMap 𝒜 hg h r =
      RingEquiv.cast h.symm
        (awayMap 𝒜 hg (rfl : f * g = f * g) r) := by
  subst x
  rfl

lemma productBasicOpen_le_standardChart
    (i j : Fin (d + 1)) :
    Proj.basicOpen (homogeneousGrading k d)
        (coordinate k i * coordinate k j) ≤
      standardChart k j := by
  rw [← standardChart_inf_eq_productBasicOpen k d i j]
  exact inf_le_left

noncomputable def chartAwayDirectProductSection
    (i j : Fin (d + 1)) (r : chartRing k d j) :
    Γ(scheme k d,
      Proj.basicOpen (homogeneousGrading k d)
        (coordinate k i * coordinate k j)) :=
  Proj.awayToSection (homogeneousGrading k d)
    (coordinate k i * coordinate k j)
    (awayMap (homogeneousGrading k d)
      (coordinate_mem_degreeOne k i)
      (mul_comm (coordinate k i) (coordinate k j)) r)

lemma chartAwayRestrictionSection_productTransport
    (i j : Fin (d + 1)) (r : chartRing k d j) :
    (chartPairProductSectionsIso k d i j).hom
        (chartAwayRestrictionSection k d i j r) =
      (scheme k d).presheaf.map
        (homOfLE (productBasicOpen_le_standardChart k d i j)).op
        (Proj.awayToSection (homogeneousGrading k d)
          (coordinate k j) r) := by
  let hIJ := standardChart_inf_eq_productBasicOpen k d i j
  let hopen := productBasicOpen_le_standardChart k d i j
  unfold chartPairProductSectionsIso chartAwayRestrictionSection
  rw [← presheaf_mapIso_op_inv_eq_Γ_eqToIso_hom hIJ]
  calc
    _ = (scheme k d).presheaf.map (homOfLE hopen).op
        (((scheme k d).presheaf.mapIso
          (eqToIso (rfl : standardChart k j =
            standardChart k j)).op).inv.hom
          (Proj.awayToSection (homogeneousGrading k d)
            (coordinate k j) r)) :=
      presheafMapIsoSymm_restriction
        (X := scheme k d) (eI := rfl) (eJ := hIJ)
        (hA := (show standardChart k j ⊓ standardChart k i ≤
          standardChart k j from inf_le_left))
        (hU := hopen)
        (Proj.awayToSection (homogeneousGrading k d)
          (coordinate k j) r)
    _ = _ := by
      apply congrArg
        (fun z => (scheme k d).presheaf.map
          (homOfLE hopen).op z)
      rfl

lemma chartAwaySection_restrict_productOpen
    (i j : Fin (d + 1)) (r : chartRing k d j) :
    (scheme k d).presheaf.map
        (homOfLE (productBasicOpen_le_standardChart k d i j)).op
        (Proj.awayToSection (homogeneousGrading k d)
          (coordinate k j) r) =
      chartAwayDirectProductSection k d i j r := by
  unfold chartAwayDirectProductSection
  exact ambientAwaySection_restrict k d
    (coordinate k j) (coordinate k i)
    (coordinate_mem_degreeOne k i)
    (coordinate k i * coordinate k j)
    (mul_comm (coordinate k i) (coordinate k j))
    (productBasicOpen_le_standardChart k d i j) r

lemma chartAwayDirectProductSection_eq_productSection
    (i j : Fin (d + 1)) (r : chartRing k d j) :
    chartAwayDirectProductSection k d i j r =
      chartAwayProductSection k d i j r := by
  unfold chartAwayDirectProductSection chartAwayProductSection
  apply congrArg
    (Proj.awayToSection (homogeneousGrading k d)
      (coordinate k i * coordinate k j))
  unfold chartPairAwayOfElement chartProductSwap
  exact awayMap_eq_cast_of_eq
    (coordinate_mem_degreeOne k i)
    (mul_comm (coordinate k i) (coordinate k j)) r

lemma chartAwayRestrictionSection_eq_chartScalarOnPair
    (i j : Fin (d + 1)) (r : chartRing k d j) :
    chartAwayRestrictionSection k d i j r =
      chartScalarOnPair k d i j r := by
  let E := chartPairProductSectionsIso k d i j
  have htransport :=
    chartAwayRestrictionSection_productTransport k d i j r
  have hrestrict :=
    chartAwaySection_restrict_productOpen k d i j r
  have hproduct :=
    chartAwayDirectProductSection_eq_productSection k d i j r
  rw [chartScalarOnPair_eq_awaySectionOfElement]
  unfold chartPairAwaySectionOfElement
  change chartAwayRestrictionSection k d i j r =
    E.inv (chartAwayProductSection k d i j r)
  apply E.commRingCatIsoToRingEquiv.injective
  change E.hom (chartAwayRestrictionSection k d i j r) =
    E.hom (E.inv (chartAwayProductSection k d i j r))
  rw [E.inv_hom_id_apply]
  exact htransport.trans (hrestrict.trans hproduct)

/-- Restricting a homogeneous-localization section from the `j`-th
standard chart to its intersection with the `i`-th chart gives the
canonical pair-overlap scalar. -/
lemma chartAwaySection_restrict_pair
    (i j : Fin (d + 1))
    (r : chartRing k d j) :
    (scheme k d).presheaf.map
        (homOfLE
          (show
            standardChart k j ⊓ standardChart k i ≤
              standardChart k j
            from inf_le_left)).op
        (Proj.awayToSection
          (homogeneousGrading k d)
          (coordinate k j) r) =
      chartScalarOnPair k d i j r := by
  change chartAwayRestrictionSection k d i j r =
    chartScalarOnPair k d i j r
  exact chartAwayRestrictionSection_eq_chartScalarOnPair k d i j r

/-- The coordinate-ratio power specializes the preceding restriction
formula. -/
lemma coordinateChartSection_restrict_pair
    (N : ℕ) (r i j : Fin (d + 1)) :
    (scheme k d).presheaf.map
        (homOfLE
          (show
            standardChart k j ⊓ standardChart k i ≤
              standardChart k j
            from inf_le_left)).op
        (Proj.awayToSection
          (homogeneousGrading k d)
          (coordinate k j)
          (chartRatioElement k d r j ^ N)) =
      chartScalarOnPair k d i j
          (chartRatioElement k d r j) ^ N := by
  rw [← chartScalarOnPair_pow]
  exact
    chartAwaySection_restrict_pair
      k d i j (chartRatioElement k d r j ^ N)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveCoordinatePairScalarRestriction
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemePresheafSectionTransport

/-!
# Projective coordinate functions satisfy the Serre cover cocycle

The chart functions `(Xᵣ / Xⱼ)^N` transform on pair overlaps by the
positive degree-`N` Serre unit.  The proof is kept separate from the
homogeneous-localization restriction calculation.
-/


open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.CoverDescentData

variable (k : Type) [CommRing k] (d : ℕ)

/--
Restriction from the first chart to the pair overlap, written in the
orientation used by the glue datum, is the transported pair scalar.
-/
lemma coordinateChartSection_restrict_pair_fromFirst
    (N : ℕ) (r i j : Fin (d + 1)) :
    (scheme k d).presheaf.map
        (homOfLE
          (show
            standardChart k j ⊓ standardChart k i ≤
              standardChart k i
            from inf_le_right)).op
        (Proj.awayToSection
          (homogeneousGrading k d)
          (coordinate k i)
          (chartRatioElement k d r i ^ N)) =
      chartScalarFromLOnPair k d i j
          (chartRatioElement k d r i) ^ N := by
  rw [← chartScalarFromLOnPair_pow]
  unfold chartScalarFromLOnPair
  let s :=
    Proj.awayToSection
      (homogeneousGrading k d)
      (coordinate k i)
      (chartRatioElement k d r i ^ N)
  let E :=
    eqToIso
      (congrArg
        (fun U => Γ(scheme k d, U))
        (inf_comm
          (standardChart k i) (standardChart k j)))
  calc
    _ = E.hom
          ((scheme k d).presheaf.map
            (homOfLE
              (show
                standardChart k i ⊓ standardChart k j ≤
                  standardChart k i
                from inf_le_left)).op s) := by
      exact
        (schemePresheaf_map_eqToIso_apply
          (X := scheme k d)
          (inf_comm
            (standardChart k i) (standardChart k j))
          rfl
          (show
            standardChart k i ⊓ standardChart k j ≤
              standardChart k i
            from inf_le_left)
          (show
            standardChart k j ⊓ standardChart k i ≤
              standardChart k i
            from inf_le_right)
          s).symm
    _ = E.hom
          (chartScalarOnPair k d j i
            (chartRatioElement k d r i ^ N)) := by
      rw [chartScalarOnPair_pow]
      exact congrArg E.hom.hom
        (coordinateChartSection_restrict_pair
          k d N r j i)

lemma pairOverlapTopSectionsIso_coordinateChartFunction_first
    (N : ℕ) (r i j : Fin (d + 1)) :
    (pairOverlapTopSectionsIso k d i j).hom
        ((typedIntegerFirstOverlapMap k d i j).appTop
          (coordinateChartFunction k d N r i)) =
      chartScalarFromLOnPair k d i j
        (chartRatioElement k d r i) ^ N := by
  let s : Γ(scheme k d, standardChart k i) :=
    Proj.awayToSection
      (homogeneousGrading k d) (coordinate k i)
      (chartRatioElement k d r i ^ N)
  change
    (pairOverlapTopSectionsIso k d i j).hom
        ((typedIntegerFirstOverlapMap k d i j).appTop
          ((standardChart k i).topIso.inv s)) =
      _
  rw [pairOverlapTopSectionsIso_firstChart]
  unfold s
  exact coordinateChartSection_restrict_pair_fromFirst k d N r i j

lemma pairOverlapTopSectionsIso_coordinateChartFunction_second
    (N : ℕ) (r i j : Fin (d + 1)) :
    (pairOverlapTopSectionsIso k d i j).hom
        ((glueSecondOverlapMap k d i j).appTop
          (coordinateChartFunction k d N r j)) =
      chartScalarOnPair k d i j
        (chartRatioElement k d r j) ^ N := by
  let s : Γ(scheme k d, standardChart k j) :=
    Proj.awayToSection
      (homogeneousGrading k d) (coordinate k j)
      (chartRatioElement k d r j ^ N)
  change
    (pairOverlapTopSectionsIso k d i j).hom
        ((glueSecondOverlapMap k d i j).appTop
          ((standardChart k j).topIso.inv s)) =
      _
  rw [pairOverlapTopSectionsIso_secondChart]
  unfold s
  exact coordinateChartSection_restrict_pair k d N r i j

/--
The projective coordinate chart functions satisfy the degree-`N`
Serre scalar compatibility equation on every pair overlap.
-/
theorem coordinateChartFunction_coverCompatible
    (N : ℕ) (r : Fin (d + 1)) :
    CoverScalarSectionCompatibility
      (D := glueData k d)
      (integerCoverUnit k d (N : ℤ))
      (coordinateChartFunction k d N r) := by
  intro i j
  let i' : Fin (d + 1) := i
  let j' : Fin (d + 1) := j
  let a : Γ(typedIntegerPairOverlapScheme k d i' j', ⊤) :=
    (integerCoverUnit k d (N : ℤ) i' j').val
  change
    (typedIntegerFirstOverlapMap k d i' j').appTop
          (coordinateChartFunction k d N r i') *
        a =
      (glueSecondOverlapMap k d i' j').appTop
        (coordinateChartFunction k d N r j')
  apply
    (pairOverlapTopSectionsIso k d i' j').commRingCatIsoToRingEquiv.injective
  change
    (pairOverlapTopSectionsIso k d i' j').hom _ =
      (pairOverlapTopSectionsIso k d i' j').hom _
  rw [map_mul]
  rw [pairOverlapTopSectionsIso_coordinateChartFunction_first]
  dsimp only [a]
  rw [pairOverlapTopSectionsIso_integerCoverUnit]
  rw [pairOverlapTopSectionsIso_coordinateChartFunction_second]
  rw [mul_comm, chartScalarOnPair_cocycle_pow]

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

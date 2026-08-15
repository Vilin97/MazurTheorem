/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentBaseAmbientCoordinates
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistOpenOverlapTransition
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistPairLaurentFraction

/-!
# Chart-change fractions over an arbitrary coefficient ring

The inverse Serre transition on a pair of standard charts is the Laurent
monomial `X_j^m X_i⁻ᵐ`.  This file identifies its restriction to every
finite standard intersection with the corresponding degree-zero Laurent
basis vector, over an arbitrary commutative base ring.
-/

open CategoryTheory AlgebraicGeometry Opposite


noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
open MazurTorsion.AlgebraicGeometry.CoherentCohomology
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

/-- On ambient regular functions, reindexing the degree-zero Laurent
frame is multiplication by the inverse transition monomial. -/
lemma degreeZeroAmbientSectionsLinearEquivOver_chartChange
    (k : Type) [CommRing k] (d : ℕ)
    (I : Finset (Fin (d + 1))) [Nonempty ↥I]
    (i j : ↥I) (m : ℤ)
    (f : MonomialModule (ι := Fin (d + 1)) k 0 I) :
    letI : (scheme k d).Over (Spec (CommRingCat.of k)) :=
      ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec k d⟩
    letI : Module k Γ(scheme k d, laurentOpen k d I) :=
      sectionsModule
        (k := k) (SheafOfModules.unit (scheme k d).ringCatSheaf)
        (laurentOpen k d I)
    degreeZeroAmbientSectionOver k d I
        (monomialModuleChartChangeLinearEquiv
          (k := k) I i j m f) =
      degreeZeroAmbientSectionOver k d I
          (Finsupp.single
            (chartChangeAdmissibleExponent d I i j m) (1 : k)) *
        degreeZeroAmbientSectionOver k d I f := by
  letI : (scheme k d).Over (Spec (CommRingCat.of k)) :=
    ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec k d⟩
  letI : Module k Γ(scheme k d, laurentOpen k d I) :=
    sectionsModule
      (k := k) (SheafOfModules.unit (scheme k d).ringCatSheaf)
      (laurentOpen k d I)
  change
    Proj.awayToSection
        (homogeneousGrading k d)
        (variableProduct (k := k) I)
        (degreeZeroFractionLinearEquiv (k := k) I
          (monomialModuleChartChangeLinearEquiv
            (k := k) I i j m f)) =
      Proj.awayToSection
          (homogeneousGrading k d)
          (variableProduct (k := k) I)
          (degreeZeroFractionLinearEquiv (k := k) I
            (Finsupp.single
              (chartChangeAdmissibleExponent d I i j m) (1 : k))) *
        Proj.awayToSection
          (homogeneousGrading k d)
          (variableProduct (k := k) I)
          (degreeZeroFractionLinearEquiv (k := k) I f)
  rw [degreeZeroFractionLinearEquiv_chartChange,
    degreeZeroFractionLinearEquiv_single_chartChange,
    map_mul]

/-- A finite standard intersection containing `i` and `j` lies inside
the projective basic open away from `X_i X_j`. -/
lemma laurentOpen_le_pairProductOver
    (k : Type) [CommRing k] (d : ℕ)
    (I : Finset (Fin (d + 1))) (i j : ↥I) :
    laurentOpen k d I ≤
      Proj.basicOpen (homogeneousGrading k d)
        (coordinate k i.1 * coordinate k j.1) := by
  rw [Proj.basicOpen_mul]
  exact le_inf
    (laurentOpen_le_standardChart k d I i)
    (laurentOpen_le_standardChart k d I j)

/-- Casting the product-denominator inverse transition to the squarefree
coordinate-pair denominator gives the named chart-change fraction. -/
lemma cast_productInverseTransition_eq_pairChartChangeOver
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    (i j : Fin (d + 1)) (hij : i ≠ j) :
    RingEquiv.cast
        (variableProduct_coordinatePair (k := k) hij).symm
        ((((awayUnit k d i j) ^ m)⁻¹).val) =
      chartChangeFraction (k := k) d (coordinatePair i j)
        (coordinatePairLeft i j)
        (coordinatePairRight i j) m := by
  rw [← awayUnitOnCoordinatePair_zpow_inv_eq_chartChangeFraction
    (k := k) i j hij m]
  rw [awayUnitOnCoordinatePair_eq_map_awayUnit
    (k := k) i j hij]
  change
    RingEquiv.cast
        (variableProduct_coordinatePair (k := k) hij).symm
        ((((awayUnit k d i j) ^ m)⁻¹).val) =
      (((Units.map
          (RingEquiv.cast
            (variableProduct_coordinatePair
              (k := k) hij).symm).toMonoidHom
          (awayUnit k d i j) ^ m)⁻¹).val)
  rw [← map_zpow, ← map_inv]
  rfl

/-- The transition basis vector on a coordinate pair restricts to the
transition basis vector on every larger finite intersection. -/
lemma restriction_pairSingle_chartChangeOver
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I) :
    restriction (R := k) (coordinatePair_subset i j)
        (Finsupp.single
          (chartChangeAdmissibleExponent d
            (coordinatePair i.1 j.1)
            (coordinatePairLeft i.1 j.1)
            (coordinatePairRight i.1 j.1) m) (1 : k)) =
      Finsupp.single
        (chartChangeAdmissibleExponent d I i j m) (1 : k) := by
  apply (degreeZeroFractionLinearEquiv (k := k) I).injective
  rw [degreeZeroFractionLinearEquiv_restriction]
  rw [degreeZeroFractionLinearEquiv_single_chartChange,
    degreeZeroFractionLinearEquiv_single_chartChange]
  exact homogeneousAwayRestriction_pairChartChangeFraction
    (k := k) i j m

/-- Restricting the inverse transition section to a Laurent open gives
the regular function represented by its chart-change basis monomial. -/
lemma productAwayRestriction_eq_chartChangeAmbientOver
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) [Nonempty ↥I]
    (i j : ↥I) (hij : i.1 ≠ j.1) :
    (scheme k d).presheaf.map
        (homOfLE (laurentOpen_le_pairProductOver k d I i j)).op
        (Proj.awayToSection (homogeneousGrading k d)
          (coordinate k i.1 * coordinate k j.1)
          ((((awayUnit k d i.1 j.1) ^ m)⁻¹).val)) =
      degreeZeroAmbientSectionOver k d I
        (Finsupp.single
          (chartChangeAdmissibleExponent d I i j m) (1 : k)) := by
  let P := coordinatePair i.1 j.1
  let hPI : P ⊆ I := coordinatePair_subset i j
  let hvar :
      variableProduct (k := k) P =
        coordinate k i.1 * coordinate k j.1 :=
    variableProduct_coordinatePair (k := k) hij
  let B : (scheme k d).Opens :=
    Proj.basicOpen (homogeneousGrading k d)
      (coordinate k i.1 * coordinate k j.1)
  let eBP : B = laurentOpen k d P :=
    congrArg
      (Proj.basicOpen (homogeneousGrading k d))
      hvar.symm
  let a :
      HomogeneousLocalization.Away
        (homogeneousGrading k d)
        (coordinate k i.1 * coordinate k j.1) :=
    ((((awayUnit k d i.1 j.1) ^ m)⁻¹).val)
  let fP :
      MonomialModule (ι := Fin (d + 1)) k 0 P :=
    Finsupp.single
      (chartChangeAdmissibleExponent d P
        (coordinatePairLeft i.1 j.1)
        (coordinatePairRight i.1 j.1) m) (1 : k)
  letI : Nonempty ↥P := ⟨coordinatePairLeft i.1 j.1⟩
  letI : (scheme k d).Over (Spec (CommRingCat.of k)) :=
    ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec k d⟩
  letI : Module k Γ(scheme k d, laurentOpen k d P) :=
    sectionsModule
      (k := k) (SheafOfModules.unit (scheme k d).ringCatSheaf)
      (laurentOpen k d P)
  letI : Module k Γ(scheme k d, laurentOpen k d I) :=
    sectionsModule
      (k := k) (SheafOfModules.unit (scheme k d).ringCatSheaf)
      (laurentOpen k d I)
  have hpair :
      ((scheme k d).presheaf.mapIso
          (eqToIso eBP).op).inv.hom
        (Proj.awayToSection (homogeneousGrading k d)
          (coordinate k i.1 * coordinate k j.1) a) =
      degreeZeroAmbientSectionOver k d P fP := by
    rw [presheaf_mapIso_op_inv_eq_Γ_eqToIso_hom]
    change
      (eqToIso (congrArg
        (fun q => Γ(scheme k d,
          Proj.basicOpen (homogeneousGrading k d) q))
        hvar.symm)).hom
        (Proj.awayToSection (homogeneousGrading k d)
          (coordinate k i.1 * coordinate k j.1) a) =
        Proj.awayToSection (homogeneousGrading k d)
          (variableProduct (k := k) P)
          (degreeZeroFractionLinearEquiv (k := k) P fP)
    rw [awayToSection_cast k d
      (coordinate k i.1 * coordinate k j.1)
      (variableProduct (k := k) P)
      hvar.symm a,
      cast_productInverseTransition_eq_pairChartChangeOver
      k d m i.1 j.1 hij,
      degreeZeroFractionLinearEquiv_single_chartChange]
  have hnat :=
    presheafMapIsoSymm_restriction
      eBP rfl
      (laurentOpen_le_pairProductOver k d I i j)
      (laurentOpen_mono k d hPI)
      (Proj.awayToSection (homogeneousGrading k d)
        (coordinate k i.1 * coordinate k j.1) a)
  calc
    _ = (scheme k d).presheaf.map
        (homOfLE (laurentOpen_mono k d hPI)).op
        (((scheme k d).presheaf.mapIso
          (eqToIso eBP).op).inv.hom
          (Proj.awayToSection (homogeneousGrading k d)
            (coordinate k i.1 * coordinate k j.1) a)) := by
      simpa [a] using hnat
    _ = (scheme k d).presheaf.map
        (homOfLE (laurentOpen_mono k d hPI)).op
        (degreeZeroAmbientSectionOver k d P fP) := by
      exact congrArg
        ((scheme k d).presheaf.map
          (homOfLE (laurentOpen_mono k d hPI)).op).hom
        hpair
    _ = degreeZeroAmbientSectionOver k d I
        (restriction (R := k) hPI fP) :=
      (degreeZeroAmbientSectionsLinearEquivOver_restriction
        k d hPI fP).symm
    _ = _ := by
      rw [restriction_pairSingle_chartChangeOver k d m I i j]

/-- On a Laurent open, the geometric inverse transition is exactly the
ambient section represented by the chart-change monomial. -/
lemma inverseTransitionAmbientOpen_eq_chartChangeOver
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) [Nonempty ↥I]
    (i j : ↥I) (hij : i.1 ≠ j.1) :
    pairUnitSectionToAmbientViaSecondChartOpen
        k d i.1 j.1 (laurentOpen k d I)
        (laurentOpen_le_standardChart k d I i)
        (laurentOpen_le_standardChart k d I j)
        (integerInverseTransitionSectionOnPairOpen
          k d m i.1 j.1 (laurentOpen k d I)) =
      degreeZeroAmbientSectionOver k d I
        (Finsupp.single
          (chartChangeAdmissibleExponent d I i j m) (1 : k)) :=
  (inverseTransitionAmbientOpen_eq_productAwayRestriction
    k d m i.1 j.1 (laurentOpen k d I)
      (laurentOpen_le_standardChart k d I i)
      (laurentOpen_le_standardChart k d I j)).trans
    (productAwayRestriction_eq_chartChangeAmbientOver
      k d m I i j hij)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

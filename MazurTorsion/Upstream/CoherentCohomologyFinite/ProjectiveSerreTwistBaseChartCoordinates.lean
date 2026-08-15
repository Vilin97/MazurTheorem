/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentBaseChartChange
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistOpenCoordinateRestriction

/-!
# Laurent chart coordinates over an arbitrary base

For an integer Serre twist on a finite standard intersection, this file
defines Laurent coordinates using one chosen standard chart.  The
geometric transition law and the Laurent chart-change calculation show
that the resulting degree-`m` coordinate is independent of that choice.
The same coordinates commute with restriction when a chart is retained.
-/

open CategoryTheory AlgebraicGeometry Opposite


noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

/-- The degree-zero Laurent representative of an integer-twist section in
one selected standard chart. -/
noncomputable def integerChartDegreeZeroCoordinateOver
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (j : ↥I)
    (x : Γ(OInt k d m, laurentOpen k d I)) :
    MonomialModule (ι := Fin (d + 1)) k 0 I := by
  letI : Nonempty ↥I := ⟨j⟩
  letI : (scheme k d).Over (Spec (CommRingCat.of k)) :=
    ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec k d⟩
  letI : Module k Γ(scheme k d, laurentOpen k d I) :=
    sectionsModule
      (k := k) (SheafOfModules.unit (scheme k d).ringCatSheaf)
      (laurentOpen k d I)
  exact
    (degreeZeroAmbientSectionsLinearEquivOver k d I).symm.toFun
      (integerChartAmbientSectionsAddEquiv
        k d m j.1 (laurentOpen k d I)
        (laurentOpen_le_standardChart k d I j) x)

/-- The degree-`m` Laurent coordinate obtained from one standard-chart
trivialization. -/
noncomputable def integerChartLaurentCoordinateOver
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (j : ↥I)
    (x : Γ(OInt k d m, laurentOpen k d I)) :
    MonomialModule (ι := Fin (d + 1)) k m I :=
  monomialModuleShiftLinearEquiv (k := k) I j m
    (integerChartDegreeZeroCoordinateOver k d m I j x)

/-- The degree-zero representatives in two chart frames differ by the
inverse-transition chart change. -/
lemma integerChartDegreeZeroCoordinateOver_eq_chartChange
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt k d m, laurentOpen k d I)) :
    integerChartDegreeZeroCoordinateOver k d m I i x =
      monomialModuleChartChangeLinearEquiv (k := k) I i j m
        (integerChartDegreeZeroCoordinateOver k d m I j x) := by
  by_cases hij : i.1 = j.1
  · have hij' : i = j := Subtype.ext hij
    subst j
    apply (monomialModuleShiftLinearEquiv
      (k := k) I i m).injective
    exact
      (monomialModuleShift_chartChange
        (k := k) I i i m
          (integerChartDegreeZeroCoordinateOver
            k d m I i x)).symm
  · letI : Nonempty ↥I := ⟨i⟩
    letI : (scheme k d).Over (Spec (CommRingCat.of k)) :=
      ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec k d⟩
    letI : Module k Γ(scheme k d, laurentOpen k d I) :=
      sectionsModule
        (k := k) (SheafOfModules.unit (scheme k d).ringCatSheaf)
        (laurentOpen k d I)
    let E := degreeZeroAmbientSectionsLinearEquivOver k d I
    let ci :=
      integerChartAmbientSectionsAddEquiv
        k d m i.1 (laurentOpen k d I)
        (laurentOpen_le_standardChart k d I i) x
    let cj :=
      integerChartAmbientSectionsAddEquiv
        k d m j.1 (laurentOpen k d I)
        (laurentOpen_le_standardChart k d I j) x
    let t :=
      E.toFun (Finsupp.single
        (chartChangeAdmissibleExponent d I i j m) (1 : k))
    have hcoordinate :
        ci =
          cj *
            pairUnitSectionToAmbientViaSecondChartOpen
              k d i.1 j.1 (laurentOpen k d I)
              (laurentOpen_le_standardChart k d I i)
              (laurentOpen_le_standardChart k d I j)
              (integerInverseTransitionSectionOnPairOpen
                k d m i.1 j.1 (laurentOpen k d I)) :=
      integerChartAmbientCoordinateOpen_eq_mul_transition
        k d m i.1 j.1 (laurentOpen k d I)
        (laurentOpen_le_standardChart k d I i)
        (laurentOpen_le_standardChart k d I j) x
    have htransition :
        pairUnitSectionToAmbientViaSecondChartOpen
              k d i.1 j.1 (laurentOpen k d I)
              (laurentOpen_le_standardChart k d I i)
              (laurentOpen_le_standardChart k d I j)
              (integerInverseTransitionSectionOnPairOpen
                k d m i.1 j.1 (laurentOpen k d I)) =
          t :=
      inverseTransitionAmbientOpen_eq_chartChangeOver
        k d m I i j hij
    apply E.injective
    change
      E.toFun (E.symm.toFun ci) =
        E.toFun (monomialModuleChartChangeLinearEquiv (k := k) I i j m
          (E.symm.toFun cj))
    calc
      E.toFun (E.symm.toFun ci) = ci := E.apply_symm_apply ci
      _ = cj *
          pairUnitSectionToAmbientViaSecondChartOpen
            k d i.1 j.1 (laurentOpen k d I)
            (laurentOpen_le_standardChart k d I i)
            (laurentOpen_le_standardChart k d I j)
            (integerInverseTransitionSectionOnPairOpen
              k d m i.1 j.1 (laurentOpen k d I)) := hcoordinate
      _ = cj * t := congrArg (fun z => cj * z) htransition
      _ = t * cj := mul_comm cj t
      _ = t * E.toFun (E.symm.toFun cj) := by
        exact congrArg (fun z => t * z) (E.apply_symm_apply cj).symm
      _ = E.toFun
          (monomialModuleChartChangeLinearEquiv (k := k) I i j m
            (E.symm.toFun cj)) := by
        have hchange :=
          degreeZeroAmbientSectionsLinearEquivOver_chartChange
            k d I i j m (E.symm.toFun cj)
        change
          E.toFun
              (monomialModuleChartChangeLinearEquiv (k := k) I i j m
                (E.symm.toFun cj)) =
            t * E.toFun (E.symm.toFun cj) at hchange
        exact hchange.symm

/-- The final degree-`m` Laurent coordinate does not depend on the
chosen standard chart. -/
theorem integerChartLaurentCoordinateOver_eq
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (i j : ↥I)
    (x : Γ(OInt k d m, laurentOpen k d I)) :
    integerChartLaurentCoordinateOver k d m I i x =
      integerChartLaurentCoordinateOver k d m I j x := by
  unfold integerChartLaurentCoordinateOver
  rw [integerChartDegreeZeroCoordinateOver_eq_chartChange
    k d m I i j x]
  exact monomialModuleShift_chartChange
    (k := k) I i j m
      (integerChartDegreeZeroCoordinateOver k d m I j x)

/-- Keeping the same chart while restricting a twist section gives the
ordinary Laurent-monomial restriction. -/
lemma integerChartLaurentCoordinateOver_restriction
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    {I J : Finset (Fin (d + 1))}
    (hIJ : I ⊆ J) (j : ↥I)
    (x : Γ(OInt k d m, laurentOpen k d I)) :
    integerChartLaurentCoordinateOver k d m J
        ⟨j.1, hIJ j.2⟩
        ((OInt k d m).presheaf.map
          (homOfLE (laurentOpen_mono k d hIJ)).op x) =
      restriction (R := k) hIJ
        (integerChartLaurentCoordinateOver k d m I j x) := by
  letI : Nonempty ↥I := ⟨j⟩
  letI : Nonempty ↥J := ⟨⟨j.1, hIJ j.2⟩⟩
  letI : (scheme k d).Over (Spec (CommRingCat.of k)) :=
    ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec k d⟩
  letI : Module k Γ(scheme k d, laurentOpen k d I) :=
    sectionsModule
      (k := k) (SheafOfModules.unit (scheme k d).ringCatSheaf)
      (laurentOpen k d I)
  letI : Module k Γ(scheme k d, laurentOpen k d J) :=
    sectionsModule
      (k := k) (SheafOfModules.unit (scheme k d).ringCatSheaf)
      (laurentOpen k d J)
  unfold integerChartLaurentCoordinateOver
    integerChartDegreeZeroCoordinateOver
  rw [integerChartAmbientSectionsAddEquiv_restriction]
  rw [degreeZeroAmbientSectionsLinearEquivOver_symm_restriction]
  exact monomialModuleShiftLinearEquiv_restriction
    hIJ j m _

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

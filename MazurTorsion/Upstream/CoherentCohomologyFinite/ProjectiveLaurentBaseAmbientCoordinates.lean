/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentSectionsBaseLinear
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistLaurentChartIndependence

/-!
# Base-linear Laurent coordinates on ambient projective opens

This file gives the coefficient-linear degree-zero Laurent description
directly on a projective basic open and proves that it commutes with
restriction.  It is the ambient counterpart of the standard-intersection
description used for Serre twists.
-/

open CategoryTheory AlgebraicGeometry Opposite


noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
open MazurTorsion.AlgebraicGeometry.CoherentCohomology
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

/-- Degree-zero Laurent monomials as regular functions on the corresponding
projective basic open, linearly over the coefficient ring. -/
noncomputable def degreeZeroAmbientSectionsLinearEquivOver
    (k : Type) [CommRing k] (d : ℕ)
    (I : Finset (Fin (d + 1))) [Nonempty ↥I] :
    letI : (scheme k d).Over (Spec (CommRingCat.of k)) :=
      ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec k d⟩
    letI : Module k Γ(scheme k d, laurentOpen k d I) :=
      sectionsModule
        (k := k) (SheafOfModules.unit (scheme k d).ringCatSheaf)
        (laurentOpen k d I)
    MonomialModule (ι := Fin (d + 1)) k 0 I ≃ₗ[k]
      Γ(scheme k d, laurentOpen k d I) := by
  letI : (scheme k d).Over (Spec (CommRingCat.of k)) :=
    ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec k d⟩
  letI : Module k Γ(scheme k d, laurentOpen k d I) :=
    sectionsModule
      (k := k) (SheafOfModules.unit (scheme k d).ringCatSheaf)
      (laurentOpen k d I)
  let e :
      HomogeneousLocalization.Away
          (homogeneousGrading k d) (variableProduct (k := k) I) ≃+*
        Γ(scheme k d, laurentOpen k d I) :=
    (Proj.basicOpenIsoAway
      (homogeneousGrading k d)
      (variableProduct (k := k) I)
      (variableProduct_mem_degreeCard I)
      (by
        let j : ↥I := Classical.choice inferInstance
        exact Finset.card_pos.mpr ⟨j.1, j.2⟩)
      ).commRingCatIsoToRingEquiv
  let eLinear :
      HomogeneousLocalization.Away
          (homogeneousGrading k d) (variableProduct (k := k) I) ≃ₗ[k]
        Γ(scheme k d, laurentOpen k d I) :=
    { e.toAddEquiv with
      map_smul' := fun r x => by
        have hmul :
            e ((algebraMap k
              (HomogeneousLocalization.Away
                (homogeneousGrading k d)
                (variableProduct (k := k) I)) r) * x) =
              (algebraMapOnOpen (k := k)
                (laurentOpen k d I) r) * e x := by
          rw [map_mul]
          apply congrArg (fun z => z * e x)
          dsimp only [e]
          exact basicOpenIsoAway_hom_algebraMap k d I r
        convert hmul using 1
        · exact congrArg e (Algebra.smul_def r x)
        · change
            (algebraMapOnOpen (k := k)
              (laurentOpen k d I) ((RingHom.id k) r)) • e x =
              (algebraMapOnOpen (k := k)
                (laurentOpen k d I) r) * e x
          rw [RingHom.id_apply, Algebra.smul_def]
          rfl }
  exact
    (degreeZeroFractionLinearEquiv (k := k) I).trans eLinear

/-- A degree-zero Laurent vector evaluated as an ambient regular section,
with the section type exposed independently of the auxiliary module
instance used to construct the linear equivalence. -/
noncomputable def degreeZeroAmbientSectionOver
    (k : Type) [CommRing k] (d : ℕ)
    (I : Finset (Fin (d + 1))) [Nonempty ↥I]
    (f : MonomialModule (ι := Fin (d + 1)) k 0 I) :
    Γ(scheme k d, laurentOpen k d I) := by
  letI : (scheme k d).Over (Spec (CommRingCat.of k)) :=
    ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec k d⟩
  letI : Module k Γ(scheme k d, laurentOpen k d I) :=
    sectionsModule
      (k := k) (SheafOfModules.unit (scheme k d).ringCatSheaf)
      (laurentOpen k d I)
  exact (degreeZeroAmbientSectionsLinearEquivOver k d I).toFun f

/-- Ambient degree-zero Laurent coordinates commute with passage to a
smaller standard intersection. -/
lemma degreeZeroAmbientSectionsLinearEquivOver_restriction
    (k : Type) [CommRing k] (d : ℕ)
    {I J : Finset (Fin (d + 1))}
    [Nonempty ↥I] [Nonempty ↥J]
    (hIJ : I ⊆ J)
    (f : MonomialModule (ι := Fin (d + 1)) k 0 I) :
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
    (degreeZeroAmbientSectionsLinearEquivOver k d J).toFun
        (restriction (R := k) hIJ f) =
      (scheme k d).presheaf.map
        (homOfLE (laurentOpen_mono k d hIJ)).op
        ((degreeZeroAmbientSectionsLinearEquivOver k d I).toFun f) := by
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
  change
    Proj.awayToSection
        (homogeneousGrading k d)
        (variableProduct (k := k) J)
        (degreeZeroFractionLinearEquiv (k := k) J
          (restriction (R := k) hIJ f)) =
      (scheme k d).presheaf.map
        (homOfLE (laurentOpen_mono k d hIJ)).op
        (Proj.awayToSection
          (homogeneousGrading k d)
          (variableProduct (k := k) I)
          (degreeZeroFractionLinearEquiv (k := k) I f))
  rw [degreeZeroFractionLinearEquiv_restriction]
  have hnat :=
    Proj.awayMap_awayToSection
      (𝒜 := homogeneousGrading k d)
      (variableProduct_mem_degreeCard (J \ I))
      (variableProduct_mul_complement hIJ).symm
  exact congrArg
    (fun
      (φ :
        CommRingCat.of
            (HomogeneousLocalization.Away
              (homogeneousGrading k d)
              (variableProduct (k := k) I)) ⟶
          Γ(scheme k d, laurentOpen k d J)) =>
      (CommRingCat.Hom.hom φ)
        (degreeZeroFractionLinearEquiv (k := k) I f))
    hnat

/-- The inverse form of ambient degree-zero restriction. -/
lemma degreeZeroAmbientSectionsLinearEquivOver_symm_restriction
    (k : Type) [CommRing k] (d : ℕ)
    {I J : Finset (Fin (d + 1))}
    [Nonempty ↥I] [Nonempty ↥J]
    (hIJ : I ⊆ J)
    (x : Γ(scheme k d, laurentOpen k d I)) :
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
    (degreeZeroAmbientSectionsLinearEquivOver k d J).symm.toFun
        ((scheme k d).presheaf.map
          (homOfLE (laurentOpen_mono k d hIJ)).op x) =
      restriction (R := k) hIJ
        ((degreeZeroAmbientSectionsLinearEquivOver k d I).symm.toFun x) := by
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
  apply (degreeZeroAmbientSectionsLinearEquivOver k d J).injective
  calc
    (degreeZeroAmbientSectionsLinearEquivOver k d J).toFun
        ((degreeZeroAmbientSectionsLinearEquivOver k d J).symm.toFun
          ((scheme k d).presheaf.map
            (homOfLE (laurentOpen_mono k d hIJ)).op x)) =
      (scheme k d).presheaf.map
        (homOfLE (laurentOpen_mono k d hIJ)).op x :=
          (degreeZeroAmbientSectionsLinearEquivOver k d J).apply_symm_apply _
    _ = (scheme k d).presheaf.map
          (homOfLE (laurentOpen_mono k d hIJ)).op
          ((degreeZeroAmbientSectionsLinearEquivOver k d I).toFun
            ((degreeZeroAmbientSectionsLinearEquivOver k d I).symm.toFun x)) := by
      exact congrArg
        (fun y =>
          (scheme k d).presheaf.map
            (homOfLE (laurentOpen_mono k d hIJ)).op y)
        ((degreeZeroAmbientSectionsLinearEquivOver k d I).apply_symm_apply x).symm
    _ = (degreeZeroAmbientSectionsLinearEquivOver k d J).toFun
          (restriction (R := k) hIJ
            ((degreeZeroAmbientSectionsLinearEquivOver k d I).symm.toFun x)) :=
      (degreeZeroAmbientSectionsLinearEquivOver_restriction k d hIJ
        ((degreeZeroAmbientSectionsLinearEquivOver k d I).symm.toFun x)).symm

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

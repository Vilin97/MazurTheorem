/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentRestriction

open CategoryTheory AlgebraicGeometry
open scoped BigOperators


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.CoefficientRationalization
open MazurTorsion.AlgebraicGeometry.CoherentCohomology
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

noncomputable section

def laurentOpen
    (k : Type) [CommRing k] (d : ℕ)
    (I : Finset (Fin (d + 1))) :
    (scheme k d).Opens :=
  Proj.basicOpen (homogeneousGrading k d)
    (variableProduct (k := k) I)

lemma laurentOpen_mono
    (k : Type) [CommRing k] (d : ℕ)
    {I J : Finset (Fin (d + 1))} (hIJ : I ⊆ J) :
    laurentOpen k d J ≤ laurentOpen k d I :=
  Proj.basicOpen_mono _ _ _
    ⟨variableProduct (k := k) (J \ I),
      (variableProduct_mul_complement hIJ).symm⟩

def degreeZeroAmbientSectionsLinearEquiv
    (d : ℕ) (I : Finset (Fin (d + 1))) [Nonempty ↥I] :
    letI :
        (scheme ℚ d).Over (Spec (CommRingCat.of ℚ)) :=
      ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩
    letI : Module ℚ Γ(scheme ℚ d, laurentOpen ℚ d I) :=
      Geometric.sectionsModule
        (SheafOfModules.unit (scheme ℚ d).ringCatSheaf)
        (laurentOpen ℚ d I)
    MonomialModule (ι := Fin (d + 1)) ℚ 0 I ≃ₗ[ℚ]
      Γ(scheme ℚ d, laurentOpen ℚ d I) := by
  classical
  have hI : I.Nonempty := by
    let i : ↥I := Classical.choice inferInstance
    exact ⟨i.1, i.2⟩
  letI :
      (scheme ℚ d).Over (Spec (CommRingCat.of ℚ)) :=
    ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩
  letI : Module ℚ Γ(scheme ℚ d, laurentOpen ℚ d I) :=
    Geometric.sectionsModule
      (SheafOfModules.unit (scheme ℚ d).ringCatSheaf)
      (laurentOpen ℚ d I)
  exact addEquivToRatLinearEquiv <|
    (degreeZeroFractionLinearEquiv
      (k := ℚ) I).toAddEquiv.trans <|
      (Proj.basicOpenIsoAway
        (homogeneousGrading ℚ d)
        (variableProduct (k := ℚ) I)
        (variableProduct_mem_degreeCard I)
        (Finset.card_pos.mpr hI)).commRingCatIsoToRingEquiv.toAddEquiv

/-- A rational degree-zero Laurent vector evaluated as an ambient regular
section.  This wrapper exposes the section type without retaining the
auxiliary module instance used to construct the linear equivalence. -/
noncomputable def degreeZeroAmbientSection
    (d : ℕ) (I : Finset (Fin (d + 1))) [Nonempty ↥I]
    (f : MonomialModule (ι := Fin (d + 1)) ℚ 0 I) :
    Γ(scheme ℚ d, laurentOpen ℚ d I) := by
  letI :
      (scheme ℚ d).Over (Spec (CommRingCat.of ℚ)) :=
    ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩
  letI : Module ℚ Γ(scheme ℚ d, laurentOpen ℚ d I) :=
    Geometric.sectionsModule
      (SheafOfModules.unit (scheme ℚ d).ringCatSheaf)
      (laurentOpen ℚ d I)
  exact (degreeZeroAmbientSectionsLinearEquiv d I).toFun f

lemma degreeZeroAmbientSectionsLinearEquiv_restriction
    (d : ℕ) {I J : Finset (Fin (d + 1))}
    [Nonempty ↥I] [Nonempty ↥J]
    (hIJ : I ⊆ J)
    (f : MonomialModule (ι := Fin (d + 1)) ℚ 0 I) :
    letI :
        (scheme ℚ d).Over (Spec (CommRingCat.of ℚ)) :=
      ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩
    letI : Module ℚ Γ(scheme ℚ d, laurentOpen ℚ d I) :=
      Geometric.sectionsModule
        (SheafOfModules.unit (scheme ℚ d).ringCatSheaf)
        (laurentOpen ℚ d I)
    letI : Module ℚ Γ(scheme ℚ d, laurentOpen ℚ d J) :=
      Geometric.sectionsModule
        (SheafOfModules.unit (scheme ℚ d).ringCatSheaf)
        (laurentOpen ℚ d J)
    (degreeZeroAmbientSectionsLinearEquiv d J).toFun
        (restriction (R := ℚ) hIJ f) =
      (scheme ℚ d).presheaf.map
        (homOfLE (laurentOpen_mono ℚ d hIJ)).op
        ((degreeZeroAmbientSectionsLinearEquiv d I).toFun f) := by
  dsimp only
  letI :
      (scheme ℚ d).Over (Spec (CommRingCat.of ℚ)) :=
    ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩
  letI : Module ℚ Γ(scheme ℚ d, laurentOpen ℚ d I) :=
    Geometric.sectionsModule
      (SheafOfModules.unit (scheme ℚ d).ringCatSheaf)
      (laurentOpen ℚ d I)
  letI : Module ℚ Γ(scheme ℚ d, laurentOpen ℚ d J) :=
    Geometric.sectionsModule
      (SheafOfModules.unit (scheme ℚ d).ringCatSheaf)
      (laurentOpen ℚ d J)
  change
    Proj.awayToSection
        (homogeneousGrading ℚ d)
        (variableProduct (k := ℚ) J)
        (degreeZeroFractionLinearEquiv (k := ℚ) J
          (restriction (R := ℚ) hIJ f)) =
      (scheme ℚ d).presheaf.map
        (homOfLE (laurentOpen_mono ℚ d hIJ)).op
        (Proj.awayToSection
          (homogeneousGrading ℚ d)
          (variableProduct (k := ℚ) I)
          (degreeZeroFractionLinearEquiv (k := ℚ) I f))
  rw [degreeZeroFractionLinearEquiv_restriction]
  have hnat :=
    Proj.awayMap_awayToSection
      (𝒜 := homogeneousGrading ℚ d)
      (variableProduct_mem_degreeCard (J \ I))
      (variableProduct_mul_complement hIJ).symm
  have hx := congrArg
    (fun
      (φ :
        CommRingCat.of
            (HomogeneousLocalization.Away
              (homogeneousGrading ℚ d)
              (variableProduct (k := ℚ) I)) ⟶
          Γ(scheme ℚ d, laurentOpen ℚ d J)) =>
      (CommRingCat.Hom.hom φ)
        (degreeZeroFractionLinearEquiv (k := ℚ) I f))
    hnat
  exact hx

end
end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

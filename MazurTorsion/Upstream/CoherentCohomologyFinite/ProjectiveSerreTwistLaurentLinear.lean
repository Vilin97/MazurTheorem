/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistLaurentRestriction

open CategoryTheory AlgebraicGeometry
open scoped BigOperators


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.CoefficientRationalization
open MazurTorsion.AlgebraicGeometry.CoherentCohomology
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

noncomputable section

/-- On a nonempty intersection of projective standard opens, sections of the
integer Serre twist are the degree-`m` Laurent monomials. The chosen chart only
specifies the intermediate trivialization. -/
def integerChartLaurentSectionsLinearEquiv
    (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) (j : ↥I) :
    letI :
        (scheme ℚ d).Over (Spec (CommRingCat.of ℚ)) :=
      ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩
    (Geometric.moduleSheaf (OInt ℚ d m)).obj.obj
        (Opposite.op (laurentOpen ℚ d I)) ≃ₗ[ℚ]
      MonomialModule (ι := Fin (d + 1)) ℚ m I := by
  letI :
      (scheme ℚ d).Over (Spec (CommRingCat.of ℚ)) :=
    ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩
  letI : Nonempty ↥I := ⟨j⟩
  letI : Module ℚ Γ(OInt ℚ d m, laurentOpen ℚ d I) := by
    change Module ℚ
      ((Geometric.moduleSheaf (OInt ℚ d m)).obj.obj
        (Opposite.op (laurentOpen ℚ d I)))
    infer_instance
  letI : Module ℚ Γ(scheme ℚ d, laurentOpen ℚ d I) :=
    Geometric.sectionsModule
      (SheafOfModules.unit (scheme ℚ d).ringCatSheaf)
      (laurentOpen ℚ d I)
  exact
    (addEquivToRatLinearEquiv
      (integerChartLaurentSectionsAddEquiv d m I j)).trans <|
      (degreeZeroAmbientSectionsLinearEquiv d I).symm.trans <|
        monomialModuleShiftLinearEquiv I j m

lemma degreeZeroAmbientSectionsLinearEquiv_symm_restriction
    (d : ℕ) {I J : Finset (Fin (d + 1))}
    [Nonempty ↥I] [Nonempty ↥J]
    (hIJ : I ⊆ J)
    (x : Γ(scheme ℚ d, laurentOpen ℚ d I)) :
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
    (degreeZeroAmbientSectionsLinearEquiv d J).symm.toFun
        ((scheme ℚ d).presheaf.map
          (homOfLE (laurentOpen_mono ℚ d hIJ)).op x) =
      restriction (R := ℚ) hIJ
        ((degreeZeroAmbientSectionsLinearEquiv d I).symm.toFun x) := by
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
  apply (degreeZeroAmbientSectionsLinearEquiv d J).injective
  calc
    _ = (scheme ℚ d).presheaf.map
          (homOfLE (laurentOpen_mono ℚ d hIJ)).op x :=
      (degreeZeroAmbientSectionsLinearEquiv d J).apply_symm_apply _
    _ = (degreeZeroAmbientSectionsLinearEquiv d J).toFun
          (restriction (R := ℚ) hIJ
            ((degreeZeroAmbientSectionsLinearEquiv d I).symm.toFun x)) :=
      ((congrArg
          ((scheme ℚ d).presheaf.map
            (homOfLE (laurentOpen_mono ℚ d hIJ)).op).hom
          ((degreeZeroAmbientSectionsLinearEquiv d I).apply_symm_apply x)).symm).trans
        (degreeZeroAmbientSectionsLinearEquiv_restriction d hIJ _).symm

/-- The Laurent-section equivalence commutes with restriction as long as the
same standard chart is used to trivialize both source and target. -/
lemma integerChartLaurentSectionsLinearEquiv_restriction
    (d : ℕ) (m : ℤ)
    {I J : Finset (Fin (d + 1))}
    (hIJ : I ⊆ J) (j : ↥I)
    (x : letI :
        (scheme ℚ d).Over (Spec (CommRingCat.of ℚ)) :=
      ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩
      (Geometric.moduleSheaf (OInt ℚ d m)).obj.obj
        (Opposite.op (laurentOpen ℚ d I))) :
    letI :
        (scheme ℚ d).Over (Spec (CommRingCat.of ℚ)) :=
      ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩
    integerChartLaurentSectionsLinearEquiv
        d m J ⟨j.1, hIJ j.2⟩
        ((Geometric.moduleSheaf (OInt ℚ d m)).obj.map
          (homOfLE (laurentOpen_mono ℚ d hIJ)).op x) =
      restriction (R := ℚ) hIJ
        (integerChartLaurentSectionsLinearEquiv d m I j x) := by
  dsimp only
  letI :
      (scheme ℚ d).Over (Spec (CommRingCat.of ℚ)) :=
    ⟨MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.toSpec ℚ d⟩
  letI : Nonempty ↥I := ⟨j⟩
  letI : Nonempty ↥J := ⟨⟨j.1, hIJ j.2⟩⟩
  letI : Module ℚ Γ(scheme ℚ d, laurentOpen ℚ d I) :=
    Geometric.sectionsModule
      (SheafOfModules.unit (scheme ℚ d).ringCatSheaf)
      (laurentOpen ℚ d I)
  letI : Module ℚ Γ(scheme ℚ d, laurentOpen ℚ d J) :=
    Geometric.sectionsModule
      (SheafOfModules.unit (scheme ℚ d).ringCatSheaf)
      (laurentOpen ℚ d J)
  change
    monomialModuleShiftLinearEquiv J ⟨j.1, hIJ j.2⟩ m
      ((degreeZeroAmbientSectionsLinearEquiv d J).symm.toFun
        (integerChartLaurentSectionsAddEquiv d m J
          ⟨j.1, hIJ j.2⟩
          ((OInt ℚ d m).presheaf.map
            (homOfLE (laurentOpen_mono ℚ d hIJ)).op x))) =
      restriction (R := ℚ) hIJ
        (monomialModuleShiftLinearEquiv I j m
          ((degreeZeroAmbientSectionsLinearEquiv d I).symm.toFun
            (integerChartLaurentSectionsAddEquiv d m I j x)))
  calc
    _ = monomialModuleShiftLinearEquiv J ⟨j.1, hIJ j.2⟩ m
          ((degreeZeroAmbientSectionsLinearEquiv d J).symm.toFun
            ((scheme ℚ d).presheaf.map
              (homOfLE (laurentOpen_mono ℚ d hIJ)).op
              (integerChartLaurentSectionsAddEquiv d m I j x))) := by
      congr 2
      exact integerChartLaurentSectionsAddEquiv_restriction d m hIJ j x
    _ = monomialModuleShiftLinearEquiv J ⟨j.1, hIJ j.2⟩ m
          (restriction (R := ℚ) hIJ
            ((degreeZeroAmbientSectionsLinearEquiv d I).symm.toFun
              (integerChartLaurentSectionsAddEquiv d m I j x))) := by
      congr 1
      exact degreeZeroAmbientSectionsLinearEquiv_symm_restriction d hIJ _
    _ = _ := monomialModuleShiftLinearEquiv_restriction hIJ j m _

end
end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

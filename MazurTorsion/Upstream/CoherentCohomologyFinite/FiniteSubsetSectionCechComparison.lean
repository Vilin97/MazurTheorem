/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSubsetCechTranspose
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSubsetFreeSheafHomComparison

/-!
# Rational section Čech comparison

This file reconciles the integer signs coming from preadditive sheaf
boundaries with the rational signs used in the normalized Čech complex.
-/

open scoped BigOperators


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {ι M : Type*} [LinearOrder ι]
variable [AddCommGroup M] [Module ℚ M]

lemma insertionSign_int_smul_eq_rational
    (I : Finset ι) (j : ι) (x : M) :
    insertionSign (R := ℤ) I j • x =
      insertionSign (R := ℚ) I j • x := by
  rw [← Int.cast_smul_eq_zsmul ℚ]
  congr 1
  simp [insertionSign]

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

open CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable {T : TopCat}
variable {ι : Type} [Fintype ι] [LinearOrder ι]

/-- Over the rationals, the integer signs in the sheaf boundary are the
same scalar actions as the rational signs in the generic Čech complex. -/
lemma sectionPiDifferential_eq_finiteSubsetPiDifferential
    (U : ι → Opens T) (F : ModuleSheaf (R := ℚ) T)
    (q : ℕ) :
    sectionPiDifferential U F q =
      finiteSubsetPiDifferential
        (sectionModule U F)
        (sectionRestriction U F) q := by
  apply LinearMap.ext
  intro x
  funext J
  rw [sectionPiDifferential_apply,
    finiteSubsetPiDifferential_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact insertionSign_int_smul_eq_rational
    (J.1.erase j.1) j.1
    (sectionRestriction U F
      (Finset.erase_subset j.1 J.1)
      (x (J.erase j.1 j.2)))

/-- The target-oriented section complex is the generic target-oriented
finite-subset complex after identifying the two sign conventions. -/
noncomputable def sectionPiCechComplexIsoGeneric
    (U : ι → Opens T) (F : ModuleSheaf (R := ℚ) T) :
    sectionPiCechComplex U F ≅
      finiteSubsetPiCechComplex
        (sectionModule U F)
        (sectionRestriction U F)
        (sectionRestriction_comp U F) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => Iso.refl _)
    (by
      rintro i j (hij : i + 1 = j)
      subst hij
      simp only [sectionPiCechComplex,
        finiteSubsetPiCechComplex, CochainComplex.of_d,
        Iso.refl_hom, Category.comp_id, Category.id_comp]
      apply ModuleCat.hom_ext
      exact (sectionPiDifferential_eq_finiteSubsetPiDifferential
        U F i).symm)

/-- Over `ℚ`, the sheaf-theoretic target-oriented section Čech complex is
canonically isomorphic to the finite-support normalized Čech complex. -/
noncomputable def sectionPiCechComplexIsoFiniteSubset
    (U : ι → Opens T) (F : ModuleSheaf (R := ℚ) T) :
    sectionPiCechComplex U F ≅
      finiteSubsetCechComplex
        (sectionModule U F)
        (sectionRestriction U F)
        (sectionRestriction_comp U F) :=
  (sectionPiCechComplexIsoGeneric U F).trans
    (finiteSubsetCechComplexIsoPi
      (sectionModule U F)
      (sectionRestriction U F)
      (sectionRestriction_comp U F)).symm

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf

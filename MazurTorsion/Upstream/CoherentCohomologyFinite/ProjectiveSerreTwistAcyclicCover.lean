/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistLocalTrivialization
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAffineVanishing
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafCechComparison
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafUnitQuasicoherent

/-!
# Acyclicity of the standard cover for the Serre twist

Every nonempty finite standard intersection is affine, and the restriction
of `𝒪(m)` to it is the unit module.  Affine vanishing therefore makes the
standard cover Leray-acyclic for the underlying abelian sheaf of `𝒪(m)`.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafCechComparison

variable (k : Type) [CommRing k] (d m : ℕ)

/-- Restriction, rather than pullback, of the Serre twist to a finite
standard intersection is the unit module. -/
def intersectionRestrictIso
    {ι : Type} [Fintype ι]
    (a : ι → Fin (d + 1)) (j : ι) :
    (O k d m).restrict (standardIntersection k a).ι ≅
      SheafOfModules.unit
        (standardIntersection k a).toScheme.ringCatSheaf :=
  (Scheme.Modules.restrictFunctorIsoPullback
      (standardIntersection k a).ι).app (O k d m) ≪≫
    intersectionIso k d m a j

/-- Higher cohomology of the restricted twist vanishes on a nonempty
finite standard intersection. -/
theorem intersectionRestriction_higherCohomology_subsingleton
    {ι : Type} [Fintype ι] [Nonempty ι]
    (a : ι → Fin (d + 1)) (n : ℕ) :
    Subsingleton
      (CategoryTheory.Sheaf.H
        ((O k d m).restrict
          (standardIntersection k a).ι).underlyingSheaf
        (n + 1)) := by
  let j : ι := Classical.choice inferInstance
  letI :
      (SheafOfModules.unit
        (standardIntersection k a).toScheme.ringCatSheaf).IsQuasicoherent :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafUnit.unit_isQuasicoherent _
  letI :
      ((O k d m).restrict
        (standardIntersection k a).ι).IsQuasicoherent :=
    AlgebraicGeometry.Scheme.isQuasicoherent_of_iso
      (intersectionRestrictIso k d m a j).symm
  exact
    Scheme.Modules.subsingleton_H_of_isAffine
      ((O k d m).restrict
        (standardIntersection k a).ι) n

/-- Objectwise positive cohomology on a nonempty finite standard
intersection vanishes. -/
theorem subsingleton_H'_standardIntersection
    {ι : Type} [Fintype ι] [Nonempty ι]
    (a : ι → Fin (d + 1)) (n : ℕ) :
    Subsingleton
      (CategoryTheory.Sheaf.H'
        (O k d m).underlyingSheaf
        (n + 1) (standardIntersection k a)) := by
  apply
    TopCat.Sheaf.OpenCohomology.subsingleton_H'_of_subsingleton_restrict_H
      (O k d m).underlyingSheaf
      (standardIntersection k a) n
  change
    Subsingleton
      (CategoryTheory.Sheaf.H
        ((O k d m).restrict
          (standardIntersection k a).ι).underlyingSheaf
        (n + 1))
  exact
    intersectionRestriction_higherCohomology_subsingleton
      k d m a n

/-- The finite-intersection operation used by the Čech comparison agrees
with the product-basic-open model of the same standard intersection. -/
lemma finiteIntersection_standardChart
    (t : Finset (Fin (d + 1))) :
    finiteIntersection (standardChart k) t =
      standardIntersection k (fun i : ↥t => i.1) := by
  classical
  rw [standardIntersection_eq_iInf]
  unfold finiteIntersection
  apply le_antisymm
  · refine le_iInf (fun j => ?_)
    exact
      iInf_le_of_le j.1
        (iInf_le_of_le j.2 le_rfl)
  · refine le_iInf (fun i => le_iInf (fun hi => ?_))
    exact
      iInf_le
        (fun j : ↥t => standardChart k j.1)
        ⟨i, hi⟩

/-- The standard affine cover is acyclic for `𝒪(m)`. -/
theorem standardCover_isAcyclicOnIntersections :
    IsAcyclicOnIntersections
      (O k d m).underlyingSheaf
      (standardChart k)
      (Finset.univ : Finset (Fin (d + 1))) := by
  intro t ht _ q hq
  letI : Nonempty ↥t :=
    Finset.nonempty_coe_sort.mpr ht
  have h :=
    subsingleton_H'_standardIntersection
      k d m (fun i : ↥t => i.1) (q - 1)
  rw [Nat.sub_add_cancel hq] at h
  rw [finiteIntersection_standardChart k d t]
  exact h

/-- The standard charts form a finite cover in the form expected by the
finite-cover cohomology API. -/
lemma standardCover_finiteUnion :
    finiteUnion (standardChart k)
      (Finset.univ : Finset (Fin (d + 1))) = ⊤ := by
  simpa [finiteUnion] using iSup_standardChart k d

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

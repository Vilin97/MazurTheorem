/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistAcyclicCover
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistInteger

/-!
# Acyclicity of the standard cover for integer Serre twists

Every nonempty finite standard intersection is affine, and every integer
Serre twist restricts there to the unit module.  Thus the standard affine
cover is Leray-acyclic for the underlying abelian sheaf of `𝒪(m)`, for an
arbitrary integer `m`.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafCechComparison

variable (k : Type) [CommRing k] (d : ℕ)

/-- Restriction, rather than pullback, of an integer Serre twist to a
nonempty finite standard intersection is the unit module. -/
def integerIntersectionRestrictIso
    (m : ℤ) {ι : Type} [Fintype ι]
    (a : ι → Fin (d + 1)) (j : ι) :
    (OInt k d m).restrict (standardIntersection k a).ι ≅
      SheafOfModules.unit
        (standardIntersection k a).toScheme.ringCatSheaf :=
  (Scheme.Modules.restrictFunctorIsoPullback
      (standardIntersection k a).ι).app (OInt k d m) ≪≫
    integerIntersectionIso k d m a j

/-- Higher cohomology of an integer twist restricted to a nonempty finite
standard intersection vanishes. -/
theorem integerIntersectionRestriction_higherCohomology_subsingleton
    (m : ℤ) {ι : Type} [Fintype ι] [Nonempty ι]
    (a : ι → Fin (d + 1)) (n : ℕ) :
    Subsingleton
      (CategoryTheory.Sheaf.H
        ((OInt k d m).restrict
          (standardIntersection k a).ι).underlyingSheaf
        (n + 1)) := by
  let j : ι := Classical.choice inferInstance
  letI :
      (SheafOfModules.unit
        (standardIntersection k a).toScheme.ringCatSheaf).IsQuasicoherent :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafUnit.unit_isQuasicoherent _
  letI :
      ((OInt k d m).restrict
        (standardIntersection k a).ι).IsQuasicoherent :=
    AlgebraicGeometry.Scheme.isQuasicoherent_of_iso
      (integerIntersectionRestrictIso k d m a j).symm
  exact
    Scheme.Modules.subsingleton_H_of_isAffine
      ((OInt k d m).restrict
        (standardIntersection k a).ι) n

/-- Objectwise positive cohomology of an integer twist vanishes on each
nonempty finite standard intersection. -/
theorem subsingleton_integer_H'_standardIntersection
    (m : ℤ) {ι : Type} [Fintype ι] [Nonempty ι]
    (a : ι → Fin (d + 1)) (n : ℕ) :
    Subsingleton
      (CategoryTheory.Sheaf.H'
        (OInt k d m).underlyingSheaf
        (n + 1) (standardIntersection k a)) := by
  apply
    TopCat.Sheaf.OpenCohomology.subsingleton_H'_of_subsingleton_restrict_H
      (OInt k d m).underlyingSheaf
      (standardIntersection k a) n
  change
    Subsingleton
      (CategoryTheory.Sheaf.H
        ((OInt k d m).restrict
          (standardIntersection k a).ι).underlyingSheaf
        (n + 1))
  exact
    integerIntersectionRestriction_higherCohomology_subsingleton
      k d m a n

/-- The standard affine cover is acyclic for every integer Serre twist. -/
theorem integerStandardCover_isAcyclicOnIntersections (m : ℤ) :
    IsAcyclicOnIntersections
      (OInt k d m).underlyingSheaf
      (standardChart k)
      (Finset.univ : Finset (Fin (d + 1))) := by
  intro t ht _ q hq
  letI : Nonempty ↥t :=
    Finset.nonempty_coe_sort.mpr ht
  have h :=
    subsingleton_integer_H'_standardIntersection
      k d m (fun i : ↥t => i.1) (q - 1)
  rw [Nat.sub_add_cancel hq] at h
  rw [finiteIntersection_standardChart k d t]
  exact h

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverScalarTwistInverse
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveModuleSerreTwistEquivalence
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveSerreTwistEquivalence

/-!
# Opposite projective scalar-twist degrees

The inverse of the scalar-twist equivalence of degree `-m` is naturally
the scalar-twist functor of degree `m`, both on projective space and
after arbitrary base change.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.CoverDescentData

variable (k : Type) [CommRing k] (d : ℕ)

/-- The inverse of the degree `-m` projective cover-unit family is the
degree `m` family. -/
lemma inverseCoverUnit_integerCoverUnit_neg (m : ℤ) :
    inverseCoverUnit (D := glueData k d)
        (integerCoverUnit k d (-m)) =
      integerCoverUnit k d m := by
  funext i j
  unfold inverseCoverUnit integerCoverUnit
  rw [zpow_neg]
  apply Units.ext
  rfl

/-- The inverse of the degree `-m` ambient projective twist is naturally
the degree `m` ambient twist. -/
noncomputable def projectiveIntegerScalarTwistInverseNegIso
    (m : ℤ) :
    (projectiveIntegerScalarTwistEquivalence
        k d (-m)).inverse ≅
      (projectiveIntegerScalarTwistEquivalence
        k d m).functor := by
  change
    (openCoverScalarTwistEquivalence
        (cover k d)
        (integerCoverUnit k d (-m))
        (integerCoverUnit_self k d (-m))
        (integerCoverUnit_cocycle k d (-m))).inverse ≅
      (openCoverScalarTwistEquivalence
        (cover k d)
        (integerCoverUnit k d m)
        (integerCoverUnit_self k d m)
        (integerCoverUnit_cocycle k d m)).functor
  exact
    openCoverScalarTwistInverseFunctorIsoOfUnitsEq
      (cover k d)
      (integerCoverUnit k d (-m))
      (integerCoverUnit k d m)
      (integerCoverUnit_self k d (-m))
      (integerCoverUnit_cocycle k d (-m))
      (integerCoverUnit_self k d m)
      (integerCoverUnit_cocycle k d m)
      (inverseCoverUnit_integerCoverUnit_neg k d m)

variable {T : Scheme.{0}} (f : T ⟶ scheme k d)

/-- The inverse of the base-changed degree `-m` cover-unit family is the
base-changed degree `m` family. -/
lemma inverseCoverUnit_baseChangedIntegerCoverUnit_neg
    (m : ℤ) :
    inverseCoverUnit
        (D := Scheme.Cover.gluedCover
          ((cover k d).pullback₁ f))
        (baseChangedIntegerCoverUnit k d f (-m)) =
      baseChangedIntegerCoverUnit k d f m := by
  funext i j
  change
    (pullbackGlobalUnit
      (Scheme.Cover.baseChangeOverlapMap
        (cover k d) f i j)
      ((overlapUnit k d i j) ^ (-m)))⁻¹ =
    pullbackGlobalUnit
      (Scheme.Cover.baseChangeOverlapMap
        (cover k d) f i j)
      ((overlapUnit k d i j) ^ m)
  rw [zpow_neg]
  let p :=
    pullbackGlobalUnit
      (Scheme.Cover.baseChangeOverlapMap
        (cover k d) f i j)
  let u := (overlapUnit k d i j) ^ m
  change (p u⁻¹)⁻¹ = p u
  calc
    (p u⁻¹)⁻¹ = ((p u)⁻¹)⁻¹ :=
      congrArg Inv.inv (p.map_inv u)
    _ = p u := inv_inv _

/-- The inverse of the degree `-m` relative projective twist is naturally
the degree `m` relative projective twist. -/
noncomputable def relativeProjectiveSerreTwistInverseNegIso
    (m : ℤ) :
    (relativeProjectiveSerreTwistEquivalence
        k d f (-m)).inverse ≅
      (relativeProjectiveSerreTwistEquivalence
        k d f m).functor :=
  openCoverScalarTwistInverseFunctorIsoOfUnitsEq
    ((cover k d).pullback₁ f)
    (baseChangedIntegerCoverUnit k d f (-m))
    (baseChangedIntegerCoverUnit k d f m)
    (baseChangedIntegerCoverUnit_self k d f (-m))
    (baseChangedIntegerCoverUnit_cocycle k d f (-m))
    (baseChangedIntegerCoverUnit_self k d f m)
    (baseChangedIntegerCoverUnit_cocycle k d f m)
    (inverseCoverUnit_baseChangedIntegerCoverUnit_neg
      k d f m)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistCoefficientBaseChangeOverlap
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistBaseChangeCoverUnits

/-!
# Coefficient extension of relative Serre cover units

The canonical isomorphism between the two pulled-back standard covers
identifies their integer Serre unit cocycles.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
open AlgebraicGeometry.Scheme.Cover
open AlgebraicGeometry.Scheme.Modules

variable {k R : Type} [CommRing k] [CommRing R]
variable (φ : k →+* R) (d : ℕ)

private lemma pullbackGlobalUnit_three
    {W X Y Z : Scheme} (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (a : Γ(Z, ⊤)ˣ) :
    pullbackGlobalUnit f
        (pullbackGlobalUnit g (pullbackGlobalUnit h a)) =
      pullbackGlobalUnit ((f ≫ g) ≫ h) a := by
  rw [pullbackGlobalUnit_comp, pullbackGlobalUnit_comp,
    Category.assoc]

private lemma pullbackGlobalUnit_three_of_eq
    {W X Y Z : Scheme} (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (q : W ⟶ Z) (a : Γ(Z, ⊤)ˣ)
    (hq : (f ≫ g) ≫ h = q) :
    pullbackGlobalUnit f
        (pullbackGlobalUnit g (pullbackGlobalUnit h a)) =
      pullbackGlobalUnit q a :=
  (pullbackGlobalUnit_three f g h a).trans
    (congrArg (fun r => pullbackGlobalUnit r a) hq)

private lemma pullbackGlobalUnit_three_replace
    {W X Y Z : Scheme} (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (q : W ⟶ Z) (a : Γ(Z, ⊤)ˣ)
    (b : Γ(Y, ⊤)ˣ) (hab : pullbackGlobalUnit h a = b)
    (hq : (f ≫ g) ≫ h = q) :
    pullbackGlobalUnit f (pullbackGlobalUnit g b) =
      pullbackGlobalUnit q a := by
  rw [← hab]
  exact pullbackGlobalUnit_three_of_eq f g h q a hq

private lemma pullbackGlobalUnit_three_replace_of_eq
    {W X Y Z : Scheme} {f : W ⟶ X} {g : X ⟶ Y}
    {h : Y ⟶ Z} {q : W ⟶ Z} (hq : (f ≫ g) ≫ h = q)
    (a : Γ(Z, ⊤)ˣ) (b : Γ(Y, ⊤)ˣ)
    (hab : pullbackGlobalUnit h a = b) :
    pullbackGlobalUnit f (pullbackGlobalUnit g b) =
      pullbackGlobalUnit q a :=
  pullbackGlobalUnit_three_replace f g h q a b hab hq

private lemma equality_trans_of_first
    {α : Sort*} {a b : α} (hab : a = b) {c : α} (hbc : b = c) :
    a = c :=
  hab.trans hbc

/-- Coefficient extension preserves every integer power of the overlap unit. -/
theorem pullbackGlobalUnit_coefficientOverlapMap_integerCoverUnit
    (m : ℤ) (i j : Fin (d + 1)) :
    pullbackGlobalUnit
        (coefficientOverlapMap φ d i j)
        (integerCoverUnit k d m i j) =
      integerCoverUnit R d m i j := by
  unfold integerCoverUnit
  calc
    _ =
        (pullbackGlobalUnit
          (coefficientOverlapMap φ d i j)
          (overlapUnit k d i j)) ^ m :=
      map_zpow
        (pullbackGlobalUnit
          (coefficientOverlapMap φ d i j))
        (overlapUnit k d i j) m
    _ = _ :=
      congrArg (fun a => a ^ m)
        (pullbackGlobalUnit_coefficientOverlapMap
          φ d i j)

variable [Algebra k R] {Y : Scheme}
variable (g : Y ⟶ scheme R d)

private def coefficientCoverUnit_replacementProof
    (m : ℤ) (i j : Fin (d + 1)) :=
  congrArg
    (fun a =>
      pullbackGlobalUnit
        (coverIsoOverlapMap
          (coefficientBaseChangeStandardCoverIso
            (k := k) (R := R) d g) i j)
        (pullbackGlobalUnit
          (baseChangeOverlapMap (cover R d) g i j) a))
    (pullbackGlobalUnit_coefficientOverlapMap_integerCoverUnit
      (algebraMap k R) d m i j)

private def coefficientCoverUnit_associateProof
    (m : ℤ) (i j : Fin (d + 1)) :=
  pullbackGlobalUnit_three
    (coverIsoOverlapMap
      (coefficientBaseChangeStandardCoverIso
        (k := k) (R := R) d g) i j)
    (baseChangeOverlapMap (cover R d) g i j)
    (coefficientOverlapMap (algebraMap k R) d i j)
    (integerCoverUnit k d m i j)

private def coefficientCoverUnit_mapProof
    (m : ℤ) (i j : Fin (d + 1)) :=
  congrArg
    (fun q => pullbackGlobalUnit q (integerCoverUnit k d m i j))
    (coefficientBaseChangeOverlapMap_comp_coefficientOverlapMap
      d g i j)

private def coefficientCoverUnit_tailProof
    (m : ℤ) (i j : Fin (d + 1)) :=
  equality_trans_of_first
    (coefficientCoverUnit_associateProof
      (k := k) (R := R) d g m i j)
    (coefficientCoverUnit_mapProof
      (k := k) (R := R) d g m i j)

private def coefficientCoverUnit_pointwiseProof
    (m : ℤ) (i j : Fin (d + 1)) :=
  equality_trans_of_first
    (coefficientCoverUnit_replacementProof
      (k := k) (R := R) d g m i j).symm
    (coefficientCoverUnit_tailProof
      (k := k) (R := R) d g m i j)

private theorem coefficientCoverUnit_pointwise
    (m : ℤ) (i j : Fin (d + 1)) :
    pullbackGlobalUnit
        (coverIsoOverlapMap
          (coefficientBaseChangeStandardCoverIso
            (k := k) (R := R) d g) i j)
        (pullbackGlobalUnit
          (baseChangeOverlapMap (cover R d) g i j)
          (integerCoverUnit R d m i j)) =
      pullbackGlobalUnit
        (baseChangeOverlapMap (cover k d)
          (g ≫ coefficientMap (algebraMap k R) d) i j)
        (integerCoverUnit k d m i j) :=
  coefficientCoverUnit_pointwiseProof
    (k := k) (R := R) d g m i j

/--
Transporting the relative Serre units over `R` across the coefficient
base-change cover isomorphism gives the relative Serre units over `k`.
-/
theorem pullbackCoverUnitAlongIso_coefficientBaseChangeStandardCoverIso
    (m : ℤ) :
    pullbackCoverUnitAlongIso
        (coefficientBaseChangeStandardCoverIso d g)
        (baseChangedIntegerCoverUnit R d g m) =
      baseChangedIntegerCoverUnit k d
        (g ≫ coefficientMap (algebraMap k R) d) m := by
  funext i j
  change Fin (d + 1) at i j
  unfold pullbackCoverUnitAlongIso
  unfold baseChangedIntegerCoverUnit
  unfold baseChangeCoverUnit
  simp only [
    coefficientBaseChangeStandardCoverIso_hom_s₀]
  exact coefficientCoverUnit_pointwise
    (k := k) (R := R) d g m i j

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafCechComparison
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAffineVanishing
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# A finite affine-cover bound for quasicoherent cohomology

A compact separated scheme has a finite affine open cover whose
nonempty finite intersections are affine.  Affine quasicoherent
vanishing and Mayer--Vietoris therefore give a uniform natural-number
bound on cohomology.  This supplies the boundedness hypothesis needed
by descending Serre dévissage without first formalizing finiteness of
Krull dimension.
-/


open CategoryTheory Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/--
The finite affine subcover used for the cohomological bound.
-/
abbrev finiteAffineSubcover (X : Scheme.{u}) [CompactSpace X] :
    X.OpenCover :=
  X.affineCover.finiteSubcover

/--
The finite affine family, enlarged by one empty open so that its index
type is nonempty even when the scheme itself is empty.
-/
def finiteAffineOpenFamily (X : Scheme.{u}) [CompactSpace X] :
    Option (finiteAffineSubcover X).I₀ → X.Opens
  | none => ⊥
  | some i => ((finiteAffineSubcover X).f i).opensRange

lemma finiteAffineOpenFamily_isAffineOpen
    (X : Scheme.{u}) [CompactSpace X]
    (i : Option (finiteAffineSubcover X).I₀) :
    IsAffineOpen (finiteAffineOpenFamily X i) := by
  cases i with
  | none =>
      exact isAffineOpen_bot X
  | some i =>
      exact isAffineOpen_opensRange
        ((finiteAffineSubcover X).f i)

/--
The enlarged finite affine family still covers the scheme.
-/
lemma finiteAffineOpenFamily_covers
    (X : Scheme.{u}) [CompactSpace X] :
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafCechComparison.finiteUnion
        (finiteAffineOpenFamily X)
        Finset.univ =
      (⊤ : X.Opens) := by
  rw [MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafCechComparison.finiteUnion]
  simp only [Finset.mem_univ, iSup_true]
  rw [show
      (⨆ i : Option (finiteAffineSubcover X).I₀,
          finiteAffineOpenFamily X i) =
        (⨆ i : (finiteAffineSubcover X).I₀,
          ((finiteAffineSubcover X).f i).opensRange) by
    apply le_antisymm
    · refine iSup_le fun i => ?_
      cases i with
      | none => exact bot_le
      | some i => exact le_iSup (fun j =>
          ((finiteAffineSubcover X).f j).opensRange) i
    · refine iSup_le fun i => ?_
      exact le_iSup
        (finiteAffineOpenFamily X) (some i)]
  exact (finiteAffineSubcover X).iSup_opensRange

/--
Every nonempty finite intersection from the chosen family is affine on
a separated scheme.
-/
lemma finiteIntersection_finiteAffineOpenFamily_isAffineOpen
    (X : Scheme.{u}) [CompactSpace X] [X.IsSeparated]
    (s : Finset (Option (finiteAffineSubcover X).I₀))
    (hs : s.Nonempty) :
    IsAffineOpen
      (MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafCechComparison.finiteIntersection
        (finiteAffineOpenFamily X) s) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp at hs
  | @insert i s hi ih =>
      by_cases hs' : s.Nonempty
      · rw [
          MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafCechComparison.finiteIntersection_insert]
        exact
          (finiteAffineOpenFamily_isAffineOpen X i).inf
            (ih hs')
      · rw [Finset.not_nonempty_iff_eq_empty.mp hs']
        simpa using
          finiteAffineOpenFamily_isAffineOpen X i

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Modules

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafCechComparison

variable {X : Scheme.{u}}

/--
Quasicoherent cohomology on a compact separated scheme vanishes at and
above the cardinality of the chosen nonempty finite affine family.
-/
theorem subsingleton_H_of_finiteAffineCover_card_le
    [CompactSpace X] [X.IsSeparated]
    [HasExt.{u}
      (CategoryTheory.Sheaf
        (Opens.grothendieckTopology X)
        AddCommGrpCat.{u})]
    (F : X.Modules) [F.IsQuasicoherent]
    (q : ℕ)
    (hq :
      Fintype.card
          (Option (Scheme.finiteAffineSubcover X).I₀) ≤ q) :
    Subsingleton
      (CategoryTheory.Sheaf.H F.underlyingSheaf q) := by
  let U :=
    Scheme.finiteAffineOpenFamily X
  apply
    subsingleton_H_of_finite_acyclicCover
      F.underlyingSheaf U
      (Scheme.finiteAffineOpenFamily_covers X)
      (q := q)
  · intro s hs _ r hr
    letI :
        IsAffine
          (finiteIntersection U s) :=
      Scheme.finiteIntersection_finiteAffineOpenFamily_isAffineOpen
        X s hs
    have h :=
      subsingleton_H'_of_isAffineOpen
        F (finiteIntersection U s) (r - 1)
    have hr' : r - 1 + 1 = r := Nat.sub_add_cancel hr
    simpa [hr'] using h
  · exact hq

end AlgebraicGeometry.Scheme.Modules

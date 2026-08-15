/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.BaseRingModuleSheafFunctor
import MazurTorsion.Upstream.CoherentCohomologyFinite.ExtSubsingletonFiniteBiproduct
import MazurTorsion.Upstream.CoherentCohomologyFinite.FlatBaseProjectiveTwistVanishing
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistFiniteSumCoherence

/-!
# Acyclic finite sums of nonnegative projective twists

The Laurent contraction proves positive-degree Ext vanishing for one
nonnegative Serre twist.  Since the base-linear module-sheaf functor is
additive, the same is true for any finite sum of such twists.
-/


open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
open SerreTwist

/-- A module is isomorphic to a finite sum of nonnegative integer
Serre twists. -/
def IsBaseFiniteNonnegativeTwistSum
    (R : Type) [CommRing R] (d : ℕ)
    (E : (scheme R d).Modules) : Prop :=
  ∃ (ι : Type) (hι : Fintype ι) (degree : ι → ℤ),
    (∀ i, 0 ≤ degree i) ∧
      Nonempty
        (E ≅
          @finiteIntegerSum R inferInstance d ι hι degree)

/--
Every positive constant-source Ext group of a finite sum of
nonnegative twists vanishes.
-/
theorem moduleSheafExt_succ_subsingleton_of_nonnegativeTwistSum
    (R : Type) [CommRing R] [Module.Flat ℤ R]
    (d : ℕ)
    (hcoord :
      ∀ m : ℤ, BaseStandardCoverCoordinatesNatural R d m)
    (E : (scheme R d).Modules)
    (hE : IsBaseFiniteNonnegativeTwistSum R d E)
    (q : ℕ) :
    letI :
        (scheme R d).Over (Spec (CommRingCat.of R)) :=
      ⟨toSpec R d⟩
    Subsingleton
      (Abelian.Ext
        (constantRankOneSheaf (R := R) (scheme R d))
        (moduleSheaf (k := R) E) (q + 1)) := by
  letI :
      (scheme R d).Over (Spec (CommRingCat.of R)) :=
    ⟨toSpec R d⟩
  obtain ⟨ι, hι, degree, hdegree, ⟨e⟩⟩ := hE
  letI : Fintype ι := hι
  let F :=
    moduleSheafFunctor (k := R) (X := scheme R d)
  have hsummand :
      ∀ i : ι,
        Subsingleton
          (Abelian.Ext
            (constantRankOneSheaf (R := R) (scheme R d))
            (F.obj (OInt R d (degree i))) (q + 1)) := by
    intro i
    exact
      integerTwistConstantBaseExt_succ_subsingleton
        R d (degree i) (hcoord (degree i))
        (hdegree i) q
  have hsum :
      Subsingleton
        (Abelian.Ext
          (constantRankOneSheaf (R := R) (scheme R d))
          (F.obj (finiteIntegerSum R d degree)) (q + 1)) := by
    change
      Subsingleton
        (Abelian.Ext
          (constantRankOneSheaf (R := R) (scheme R d))
          (F.obj (∐ fun i => OInt R d (degree i))) (q + 1))
    exact
      ext_subsingleton_obj_finiteCoproduct
        F
        (constantRankOneSheaf (R := R) (scheme R d))
        (fun i => OInt R d (degree i)) (q + 1)
        hsummand
  let EExt :=
    ExtAdjunction.postcompIsoAddEquiv
      (X :=
        constantRankOneSheaf (R := R) (scheme R d))
      (F.mapIso e) (q + 1)
  exact
    ⟨fun x y =>
      EExt.injective
        (hsum.elim (EExt x) (EExt y))⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

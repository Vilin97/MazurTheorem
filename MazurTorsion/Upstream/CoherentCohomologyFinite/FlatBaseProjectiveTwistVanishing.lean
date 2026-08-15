/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FlatBaseAcyclicCoverCechLinearComparison
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentCechCategoricalVanishing

/-!
# Positive Ext vanishing for projective twists over a flat base

The coefficient-linear standard-cover comparison identifies
constant-source Ext of `𝒪(m)` with the Laurent Čech complex.  The
exponentwise Laurent contraction therefore gives positive-degree
vanishing for every nonnegative twist over an arbitrary coefficient
ring flat over `ℤ`.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FlatBaseAcyclicCoverCechComparison
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

/-- Constant-source Ext of a nonnegative integer twist vanishes in every
positive degree. -/
theorem integerTwistConstantBaseExt_succ_subsingleton
    (R : Type) [CommRing R] [Module.Flat ℤ R]
    (d : ℕ) (m : ℤ)
    (hcoord : BaseStandardCoverCoordinatesNatural R d m)
    (hm : 0 ≤ m) (q : ℕ) :
    letI :
        (scheme R d).Over (Spec (CommRingCat.of R)) :=
      ⟨toSpec R d⟩
    Subsingleton
      (Abelian.Ext
        (constantRankOneSheaf (R := R) (scheme R d))
        (MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing.moduleSheaf
          (k := R) (OInt R d m))
        (q + 1)) := by
  letI :
      (scheme R d).Over (Spec (CommRingCat.of R)) :=
    ⟨toSpec R d⟩
  let eExt :=
    (integerTwistConstantBaseExtLinearIsoStandardCechHomology
      R d m (q + 1)).toLinearEquiv
  let eCech :=
    ((HomologicalComplex.homologyFunctor
      (ModuleCat R) (ComplexShape.up ℕ) (q + 1)).mapIso
        (baseStandardSectionCechComplexIsoLaurent
          R d m hcoord)).toLinearEquiv
  have htarget :
      Subsingleton
        ((laurentCechComplex
          (ι := Fin (d + 1)) (R := R) m).homology
            (q + 1)) :=
    laurentCechPositiveCategoricalHomology_subsingleton
      (ι := Fin (d + 1)) (R := R) hm q
  exact
    ⟨fun x y =>
      eExt.injective <|
        eCech.injective <|
          htarget.elim
            (eCech (eExt x)) (eCech (eExt y))⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

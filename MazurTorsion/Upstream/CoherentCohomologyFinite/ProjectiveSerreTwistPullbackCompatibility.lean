/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverScalarTwistBaseChangeTransfer
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverScalarTwistGluedCanonicalBaseChange
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistPullbackPushforward

/-!
# Projective Serre twists and pullback

This file isolates the final specialization of open-cover scalar-twist
base change to the integer cocycle on the standard projective cover.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open AlgebraicGeometry.Scheme.Cover
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.CoverDescentData

/-- The central glued-cover base-change statement for every integer
projective Serre cocycle. -/
def ProjectiveGluedTwistPullbackCompatible
    (R : Type) [CommRing R] (d : ℕ)
    {Y : Scheme.{0}} (f : Y ⟶ scheme R d) : Prop :=
  ∀ m : ℤ,
    Nonempty
      ((scalarTwistGluedEquivalence
          (integerCoverUnit R d m)
          (integerCoverUnit_self R d m)
          (integerCoverUnit_cocycle R d m)).functor ⋙
          pullback
            (baseChangeGluedMap (cover R d) f) ≅
        pullback
            (baseChangeGluedMap (cover R d) f) ⋙
          (scalarTwistGluedEquivalence
            (baseChangedIntegerCoverUnit R d f m)
            (baseChangedIntegerCoverUnit_self R d f m)
            (baseChangedIntegerCoverUnit_cocycle
              R d f m)).functor)

/-- The standard integer cocycle on projective space commutes with
pullback on glued-cover module categories. -/
theorem projectiveGluedTwistPullbackCompatible
    (R : Type) [CommRing R] (d : ℕ)
    {Y : Scheme.{0}} (f : Y ⟶ scheme R d) :
    ProjectiveGluedTwistPullbackCompatible R d f := by
  intro m
  exact
    ⟨scalarTwistGluedBaseChangeNatIso
      (cover R d) f
      (integerCoverUnit R d m)
      (integerCoverUnit_self R d m)
      (integerCoverUnit_cocycle R d m)⟩

/-- Glued-cover base-change naturality for the standard integer cocycle
implies pullback naturality of projective Serre twists. -/
theorem projectiveTwistPullbackCompatible_of_glued
    (R : Type) [CommRing R] (d : ℕ)
    {Y : Scheme.{0}} (f : Y ⟶ scheme R d)
    (hglued :
      ProjectiveGluedTwistPullbackCompatible
        R d f) :
    ProjectiveTwistPullbackCompatible R d f := by
  intro m
  let e :=
    openCoverScalarTwistBaseChangeNatIsoOfGlued
      (cover R d) f
      (integerCoverUnit R d m)
      (integerCoverUnit_self R d m)
      (integerCoverUnit_cocycle R d m)
      (Classical.choice (hglued m))
  exact ⟨e⟩

/-- Projective Serre twists commute with pullback along every morphism
to projective space. -/
theorem projectiveTwistPullbackCompatible
    (R : Type) [CommRing R] (d : ℕ)
    {Y : Scheme.{0}} (f : Y ⟶ scheme R d) :
    ProjectiveTwistPullbackCompatible R d f :=
  projectiveTwistPullbackCompatible_of_glued
    R d f
    (projectiveGluedTwistPullbackCompatible R d f)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

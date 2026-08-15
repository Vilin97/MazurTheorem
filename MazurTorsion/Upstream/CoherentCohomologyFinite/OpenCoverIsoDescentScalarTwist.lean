/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverIsoDescentTransition
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleScalarTwistDescentFunctor

/-!
# Scalar twists and descent along an isomorphism of open covers

Pulling a scalar-twisted transition along an isomorphism of open covers
is the scalar twist of the pulled transition by the transported overlap
unit.
-/


open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.CoverDescentData

open Scheme.Cover

variable {X : Scheme.{0}} {𝒰 𝒱 : X.OpenCover}

private theorem scalarTwistObject_transition_coverIso
    (e : 𝒰 ≅ 𝒱)
    (A : CoverDescentData 𝒱.gluedCover)
    (b : ∀ i j, Γ(𝒱.gluedCover.V (i, j), ⊤)ˣ)
    (hself : ∀ i, b i i = 1)
    (hcocycle : CoverUnitCocycleCondition 𝒱.gluedCover b)
    (i j : 𝒰.I₀) :
    (scalarTwistObject b hself hcocycle A).transition
        (e.hom.s₀ i) (e.hom.s₀ j) =
      A.transition (e.hom.s₀ i) (e.hom.s₀ j) ≪≫
        scalarIso
          ((pullback
            (overlapTarget 𝒱 (e.hom.s₀ i) (e.hom.s₀ j))).obj
            (A.chart (e.hom.s₀ j)))
          (b (e.hom.s₀ i) (e.hom.s₀ j)) :=
  rfl

/-- Explicit pullback along a cover isomorphism commutes with scalar
twisting of a transition. -/
theorem coverIsoPullbackTransition_scalarTwist
    (e : 𝒰 ≅ 𝒱)
    (A : CoverDescentData 𝒱.gluedCover)
    (b : ∀ i j,
      Γ(𝒱.gluedCover.V (i, j), ⊤)ˣ)
    (hself : ∀ i, b i i = 1)
    (hcocycle :
      CoverUnitCocycleCondition
        𝒱.gluedCover b)
    (i j : 𝒰.I₀) :
    coverIsoPullbackTransition e
        (scalarTwistObject
          b hself hcocycle A) i j =
      coverIsoPullbackTransition e A i j ≪≫
        scalarIso
          ((pullback
            (overlapTarget 𝒰 i j)).obj
            ((pullback (e.hom.h₀ j)).obj
              (A.chart (e.hom.s₀ j))))
          (pullbackCoverUnitAlongIso e b i j) := by
  have hs :
      coverIsoSourceOverlapIso e
          (scalarTwistObject b hself hcocycle A) i j =
        coverIsoSourceOverlapIso e A i j :=
    rfl
  have ht :
      coverIsoTargetOverlapIso e
          (scalarTwistObject b hself hcocycle A) i j =
        coverIsoTargetOverlapIso e A i j :=
    rfl
  unfold coverIsoPullbackTransition
  rw [hs, ht]
  rw [scalarTwistObject_transition_coverIso]
  unfold pullbackCoverUnitAlongIso
  let p := coverIsoOverlapMap e i j
  let M := (pullback
    (overlapTarget 𝒱 (e.hom.s₀ i) (e.hom.s₀ j))).obj
      (A.chart (e.hom.s₀ j))
  let N := (pullback (overlapTarget 𝒰 i j)).obj
    ((pullback (e.hom.h₀ j)).obj
      (A.chart (e.hom.s₀ j)))
  let g := A.transition (e.hom.s₀ i) (e.hom.s₀ j)
  let s := coverIsoSourceOverlapIso e A i j
  let t := coverIsoTargetOverlapIso e A i j
  let z := b (e.hom.s₀ i) (e.hom.s₀ j)
  let u := pullbackGlobalUnit p z
  change
    s ≪≫ (pullback p).mapIso (g ≪≫ scalarIso M z) ≪≫ t.symm =
      (s ≪≫ (pullback p).mapIso g ≪≫ t.symm) ≪≫
        scalarIso N u
  have hmap :
      (pullback p).mapIso (g ≪≫ scalarIso M z) =
        (pullback p).mapIso g ≪≫
          (pullback p).mapIso (scalarIso M z) :=
    Functor.mapIso_trans (pullback p) g (scalarIso M z)
  have hpull :
      (pullback p).mapIso (scalarIso M z) =
        scalarIso ((pullback p).obj M) u :=
    pullback_scalarIso p M z
  have hn :
      scalarIso ((pullback p).obj M) u ≪≫ t.symm =
        t.symm ≪≫ scalarIso N u :=
    scalarIso_naturality t.symm u
  calc
    s ≪≫ (pullback p).mapIso (g ≪≫ scalarIso M z) ≪≫ t.symm =
        s ≪≫ ((pullback p).mapIso g ≪≫
          (pullback p).mapIso (scalarIso M z)) ≪≫ t.symm :=
      congrArg (fun q => s ≪≫ q ≪≫ t.symm) hmap
    _ = s ≪≫ ((pullback p).mapIso g ≪≫
          scalarIso ((pullback p).obj M) u) ≪≫ t.symm :=
      congrArg
        (fun q => s ≪≫ ((pullback p).mapIso g ≪≫ q) ≪≫ t.symm)
        hpull
    _ = (s ≪≫ (pullback p).mapIso g ≪≫ t.symm) ≪≫
          scalarIso N u := by
      let q := (pullback p).mapIso g
      let c := scalarIso ((pullback p).obj M) u
      let v := scalarIso N u
      have hleft :
          s ≪≫ (q ≪≫ c) ≪≫ t.symm =
            (s ≪≫ q) ≪≫ (c ≪≫ t.symm) :=
        (Iso.trans_assoc s (q ≪≫ c) t.symm).trans
          ((congrArg (fun r => s ≪≫ r)
            (Iso.trans_assoc q c t.symm)).trans
            (Iso.trans_assoc s q (c ≪≫ t.symm)).symm)
      have hright :
          (s ≪≫ q) ≪≫ (t.symm ≪≫ v) =
            (s ≪≫ q ≪≫ t.symm) ≪≫ v :=
        (Iso.trans_assoc s q (t.symm ≪≫ v)).trans
          ((congrArg (fun r => s ≪≫ r)
            (Iso.trans_assoc q t.symm v).symm).trans
            (Iso.trans_assoc s (q ≪≫ t.symm) v).symm)
      exact hleft.trans
        ((congrArg (fun r => (s ≪≫ q) ≪≫ r) hn).trans hright)

end AlgebraicGeometry.Scheme.Modules.CoverDescentData

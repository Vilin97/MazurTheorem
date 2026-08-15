/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverBaseChangeUnitCocycle
import Mathlib.AlgebraicGeometry.Cover.Open

/-!
# Pair overlaps under an isomorphism of open covers

An isomorphism of open covers identifies every pairwise overlap.  This
file packages the induced overlap isomorphism and its projection
compatibilities, which are the geometric input for transporting
unit-valued cover cocycles.
-/


open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Cover

variable {X : Scheme.{u}} {𝒰 𝒱 : X.OpenCover}

/-- The underlying isomorphism of pre-zero-hypercovers of an
isomorphism of open covers. -/
def openCoverIsoPreIso (e : 𝒰 ≅ 𝒱) :
    𝒰.toPreZeroHypercover ≅
      𝒱.toPreZeroHypercover where
  hom := e.hom
  inv := e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

/-- A component of an isomorphism of open covers is an isomorphism. -/
instance coverIsoChartMap_isIso
    (e : 𝒰 ≅ 𝒱) (i : 𝒰.I₀) :
    IsIso (e.hom.h₀ i) := by
  let ep := openCoverIsoPreIso e
  change IsIso (ep.hom.h₀ i)
  use
    ep.inv.h₀ (ep.hom.s₀ i) ≫
      eqToHom (congrArg 𝒰.X
        (PreZeroHypercover.hom_inv_s₀_apply ep i))
  rw [PreZeroHypercover.hom_inv_h₀_assoc,
    eqToHom_trans, eqToHom_refl, Category.assoc,
    ← eqToHom_naturality _ (by simp),
    PreZeroHypercover.inv_hom_h₀_assoc]
  simp

/-- The component isomorphism of an isomorphism of open covers. -/
def coverIsoChartIso
    (e : 𝒰 ≅ 𝒱) (i : 𝒰.I₀) :
    𝒰.X i ≅ 𝒱.X (e.hom.s₀ i) :=
  asIso (e.hom.h₀ i)

/-- The source overlap, mapped to the two target charts by a cover
isomorphism, is a pullback of the target chart maps. -/
theorem coverIsoOverlapIsPullback
    (e : 𝒰 ≅ 𝒱) (i j : 𝒰.I₀) :
    IsPullback
      (pullback.fst (𝒰.f i) (𝒰.f j) ≫
        e.hom.h₀ i)
      (pullback.snd (𝒰.f i) (𝒰.f j) ≫
        e.hom.h₀ j)
      (𝒱.f (e.hom.s₀ i))
      (𝒱.f (e.hom.s₀ j)) := by
  exact
    (IsPullback.of_hasPullback
      (𝒰.f i) (𝒰.f j)).of_iso
      (Iso.refl _)
      (coverIsoChartIso e i)
      (coverIsoChartIso e j)
      (Iso.refl _)
      (by rfl)
      (by rfl)
      (e.hom.w₀ i).symm
      (e.hom.w₀ j).symm

/-- The pair-overlap isomorphism induced by an isomorphism of open
covers. -/
def coverIsoOverlapIso
    (e : 𝒰 ≅ 𝒱) (i j : 𝒰.I₀) :
    𝒰.gluedCover.V (i, j) ≅
      𝒱.gluedCover.V
        (e.hom.s₀ i, e.hom.s₀ j) :=
  (coverIsoOverlapIsPullback e i j).isoPullback

/-- The map on pair overlaps induced by the forward components of an
isomorphism of open covers. -/
def coverIsoOverlapMap
    (e : 𝒰 ≅ 𝒱) (i j : 𝒰.I₀) :
    𝒰.gluedCover.V (i, j) ⟶
      𝒱.gluedCover.V
        (e.hom.s₀ i, e.hom.s₀ j) :=
  (coverIsoOverlapIso e i j).hom

@[simp, reassoc]
theorem coverIsoOverlapMap_fst
    (e : 𝒰 ≅ 𝒱) (i j : 𝒰.I₀) :
    coverIsoOverlapMap e i j ≫
        𝒱.gluedCover.f
          (e.hom.s₀ i) (e.hom.s₀ j) =
      𝒰.gluedCover.f i j ≫ e.hom.h₀ i := by
  exact
    (coverIsoOverlapIsPullback
      e i j).isoPullback_hom_fst

@[simp, reassoc]
theorem coverIsoOverlapMap_snd
    (e : 𝒰 ≅ 𝒱) (i j : 𝒰.I₀) :
    coverIsoOverlapMap e i j ≫
        pullback.snd
          (𝒱.f (e.hom.s₀ i))
          (𝒱.f (e.hom.s₀ j)) =
      pullback.snd (𝒰.f i) (𝒰.f j) ≫
        e.hom.h₀ j := by
  exact
    (coverIsoOverlapIsPullback
      e i j).isoPullback_hom_snd

@[simp, reassoc]
theorem coverIsoOverlapMap_overlapFst
    (e : 𝒰 ≅ 𝒱) (i j : 𝒰.I₀) :
    coverIsoOverlapMap e i j ≫
        overlapFst 𝒱 (e.hom.s₀ i) (e.hom.s₀ j) =
      overlapFst 𝒰 i j ≫ e.hom.h₀ i :=
  coverIsoOverlapMap_fst e i j

@[simp, reassoc]
theorem coverIsoOverlapMap_overlapSnd
    (e : 𝒰 ≅ 𝒱) (i j : 𝒰.I₀) :
    coverIsoOverlapMap e i j ≫
        overlapSnd 𝒱 (e.hom.s₀ i) (e.hom.s₀ j) =
      overlapSnd 𝒰 i j ≫ e.hom.h₀ j :=
  coverIsoOverlapMap_snd e i j

/-- A family of units on the target cover transports to the source
cover along the induced overlap isomorphisms. -/
def pullbackCoverUnitAlongIso
    (e : 𝒰 ≅ 𝒱)
    (b : ∀ i j : 𝒱.I₀,
      Γ(𝒱.gluedCover.V (i, j), ⊤)ˣ) :
    ∀ i j : 𝒰.I₀,
      Γ(𝒰.gluedCover.V (i, j), ⊤)ˣ :=
  fun i j =>
    Scheme.Modules.pullbackGlobalUnit
      (coverIsoOverlapMap e i j)
      (b (e.hom.s₀ i) (e.hom.s₀ j))

end AlgebraicGeometry.Scheme.Cover

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveLineBundleCocycleForcesNormalization
import MazurTorsion.Upstream.CurveLineBundleDescent
import Mathlib.Tactic.IrreducibleDef

/-!
# Chosen-overlap descent data from an isomorphism cocycle

An isomorphism-valued cocycle supplies its own diagonal normalization, so it directly constructs
chosen-overlap descent data.  Keeping this constructor fully pseudofunctor-generic gives concrete
scheme consumers a small opaque kernel boundary.
-/

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u v

/-- A scheme-module overlap family and its cocycle, with the local objects owned by the package. -/
structure SchemeIsoOverlapCocycle
    {X : Scheme.{u}} {cov : X.OpenCover}
    (sq : ∀ i j, ChosenPullback (cov.f i) (cov.f j))
    (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)) where
  /-- The local module on each cover member. -/
  obj : ∀ i : cov.I₀, (cov.X i).Modules
  /-- The chosen isomorphism on each pairwise overlap. -/
  overlapIso : ∀ i j,
    (Scheme.Modules.pullback (sq i j).p₁).obj (obj i) ≅
      (Scheme.Modules.pullback (sq i j).p₂).obj (obj j)
  /-- The two composites agree on every triple overlap. -/
  cocycle : ∀ i j k,
    Pseudofunctor.DescentData'.pullHom'
          (F := LineBundleDescent.modulesPseudofunctor) (sq := sq)
          (fun i j ↦ (overlapIso i j).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₂ ≫
        Pseudofunctor.DescentData'.pullHom'
          (F := LineBundleDescent.modulesPseudofunctor) (sq := sq)
          (fun i j ↦ (overlapIso i j).hom)
          (sq₃ i j k).p (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
      Pseudofunctor.DescentData'.pullHom'
        (F := LineBundleDescent.modulesPseudofunctor) (sq := sq)
        (fun i j ↦ (overlapIso i j).hom)
        (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₃

namespace SchemeIsoOverlapCocycle

/-- The exact diagonal normalization forced by a scheme-module cocycle. -/
theorem normalization
    {X : Scheme.{u}} {cov : X.OpenCover}
    {sq : ∀ i j, ChosenPullback (cov.f i) (cov.f j)}
    {sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)}
    (d : SchemeIsoOverlapCocycle sq sq₃) (i : cov.I₀) :
    Pseudofunctor.DescentData'.pullHom'
      (F := LineBundleDescent.modulesPseudofunctor) (sq := sq)
      (fun i j ↦ (d.overlapIso i j).hom)
      (cov.f i) (𝟙 (cov.X i)) (𝟙 (cov.X i)) = 𝟙 _ := by
  exact normalization_of_iso_cocycle
    (F := LineBundleDescent.modulesPseudofunctor)
    (Y := cov.X) (g := cov.f) (sq := sq) (sq₃ := sq₃)
    (obj := d.obj) d.overlapIso d.cocycle i

end SchemeIsoOverlapCocycle

/-- Scheme-module isomorphism cocycles supply normalized chosen-overlap descent data. -/
noncomputable irreducible_def schemeDescentDataPrimeOfIsoCocycle
    {X : Scheme.{u}} {cov : X.OpenCover}
    {sq : ∀ i j, ChosenPullback (cov.f i) (cov.f j)}
    {sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)}
    (d : SchemeIsoOverlapCocycle sq sq₃) :
    LineBundleDescent.modulesPseudofunctor.DescentData' sq sq₃ :=
  LineBundleDescent.DescentDataPrime.ofIso d.obj d.overlapIso
    d.normalization d.cocycle

/-- The chosen-overlap datum retains the objects owned by its scheme cocycle package. -/
theorem schemeDescentDataPrimeOfIsoCocycle_obj
    {X : Scheme.{u}} {cov : X.OpenCover}
    {sq : ∀ i j, ChosenPullback (cov.f i) (cov.f j)}
    {sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)}
    (d : SchemeIsoOverlapCocycle sq sq₃) (i : cov.I₀) :
    (schemeDescentDataPrimeOfIsoCocycle d).obj i = d.obj i := by
  rw [schemeDescentDataPrimeOfIsoCocycle_def]
  rfl

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

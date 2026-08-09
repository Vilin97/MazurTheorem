/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveLineBundleCocycleForcesNormalization
import MazurTorsion.Upstream.CurveLineBundleDescent
import Mathlib.Tactic.IrreducibleDef

/-!
# Chosen-overlap descent data from a scheme-module isomorphism cocycle

The transition family is stated in the native map API of the module pseudofunctor.  This avoids
converting concrete overlap morphisms through the definitionally equal
`Scheme.Modules.pullback` presentation.
-/

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u

/-- The full cocycle equation for a specified family of scheme modules and native
pseudofunctor overlap isomorphisms. -/
structure SchemeModulesOverlapCocycle
    {X : Scheme.{u}} {cov : X.OpenCover}
    (sq : ∀ i j, ChosenPullback (cov.f i) (cov.f j))
    (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
    (obj : ∀ i : cov.I₀,
      LineBundleDescent.modulesPseudofunctor.obj (.mk (.op (cov.X i))))
    (overlapIso : ∀ i j,
      (LineBundleDescent.modulesPseudofunctor.map
        (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ≅
      (LineBundleDescent.modulesPseudofunctor.map
        (sq i j).p₂.op.toLoc).toFunctor.obj (obj j)) : Prop where
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

/-- A native scheme-module isomorphism cocycle forces exact diagonal normalization. -/
theorem SchemeModulesOverlapCocycle.normalization
    {X : Scheme.{u}} {cov : X.OpenCover}
    {sq : ∀ i j, ChosenPullback (cov.f i) (cov.f j)}
    {sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)}
    (obj : ∀ i : cov.I₀,
      LineBundleDescent.modulesPseudofunctor.obj (.mk (.op (cov.X i))))
    (overlapIso : ∀ i j,
      (LineBundleDescent.modulesPseudofunctor.map
        (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ≅
      (LineBundleDescent.modulesPseudofunctor.map
        (sq i j).p₂.op.toLoc).toFunctor.obj (obj j))
    (c : SchemeModulesOverlapCocycle sq sq₃ obj overlapIso)
    (i : cov.I₀) :
    Pseudofunctor.DescentData'.pullHom'
      (F := LineBundleDescent.modulesPseudofunctor) (sq := sq)
      (fun i j ↦ (overlapIso i j).hom)
      (cov.f i) (𝟙 (cov.X i)) (𝟙 (cov.X i)) = 𝟙 _ := by
  exact normalization_of_iso_cocycle
    (F := LineBundleDescent.modulesPseudofunctor)
    (Y := cov.X) (g := cov.f) (sq := sq) (sq₃ := sq₃)
    (obj := obj) overlapIso c.cocycle i

/-- A packaged native scheme-module overlap cocycle constructs normalized chosen-overlap
descent data. -/
noncomputable irreducible_def schemeDescentDataPrimeOfOverlapCocycle
    {X : Scheme.{u}} {cov : X.OpenCover}
    {sq : ∀ i j, ChosenPullback (cov.f i) (cov.f j)}
    {sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)}
    (obj : ∀ i : cov.I₀,
      LineBundleDescent.modulesPseudofunctor.obj (.mk (.op (cov.X i))))
    (overlapIso : ∀ i j,
      (LineBundleDescent.modulesPseudofunctor.map
        (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ≅
      (LineBundleDescent.modulesPseudofunctor.map
        (sq i j).p₂.op.toLoc).toFunctor.obj (obj j))
    (c : SchemeModulesOverlapCocycle sq sq₃ obj overlapIso) :
  LineBundleDescent.modulesPseudofunctor.DescentData' sq sq₃ :=
  LineBundleDescent.DescentDataPrime.ofIso obj overlapIso
    (c.normalization obj overlapIso) c.cocycle

/-- The chosen-overlap datum constructed from a packaged cocycle retains its specified objects. -/
theorem schemeDescentDataPrimeOfOverlapCocycle_obj
    {X : Scheme.{u}} {cov : X.OpenCover}
    {sq : ∀ i j, ChosenPullback (cov.f i) (cov.f j)}
    {sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)}
    (obj : ∀ i : cov.I₀,
      LineBundleDescent.modulesPseudofunctor.obj (.mk (.op (cov.X i))))
    (overlapIso : ∀ i j,
      (LineBundleDescent.modulesPseudofunctor.map
        (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ≅
      (LineBundleDescent.modulesPseudofunctor.map
        (sq i j).p₂.op.toLoc).toFunctor.obj (obj j))
    (c : SchemeModulesOverlapCocycle sq sq₃ obj overlapIso)
    (i : cov.I₀) :
    (schemeDescentDataPrimeOfOverlapCocycle obj overlapIso c).obj i = obj i := by
  rw [schemeDescentDataPrimeOfOverlapCocycle_def]
  rfl

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

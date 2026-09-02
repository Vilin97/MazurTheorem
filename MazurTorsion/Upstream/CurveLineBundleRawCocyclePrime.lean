/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveLineBundleNamedTripleCocycle
import MazurTorsion.Upstream.CurveLineBundleIsoCocycleDescentDataPrime

/-!
# The raw divisor cocycle in the chosen-overlap descent API

This file transports the checked named raw triple cocycle from explicit face pullbacks to
Mathlib's `DescentData'.pullHom'` presentation.  Each face comparison is elaborated separately,
so the three large divisor transitions never unfold in a single command.
-/

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

open AffineDivisorLocalization
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open scoped AlgebraicGeometry

universe u v

private theorem raw_pullHom'₁₂_eq_transition
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i j k : (coordinateCover U hcover hU).I₀) :
    Pseudofunctor.DescentData'.pullHom'
        (F := LineBundleDescent.modulesPseudofunctor)
        (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
        (fun i j ↦ localLineBundleChosenOverlapHomOnProperSmoothCurve
          K X f U hnonempty hcover hU h D i j)
        (LineBundleDescent.tripleOverlap
          (coordinateCover U hcover hU) i j k).p
        (LineBundleDescent.tripleOverlap
          (coordinateCover U hcover hU) i j k).p₁
        (LineBundleDescent.tripleOverlap
          (coordinateCover U hcover hU) i j k).p₂ =
      localLineBundleRawTransition₁₂
        K X f U hnonempty hcover hU h D i j k := by
  exact Pseudofunctor.DescentData'.pullHom'_eq_pullHom
    (F := LineBundleDescent.modulesPseudofunctor)
    (obj := fun i ↦ (localLineBundles
      X U hnonempty hcover hU h D i).obj)
    (obj' := fun i ↦ (localLineBundles
      X U hnonempty hcover hU h D i).obj)
    (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
    (fun i j ↦ localLineBundleChosenOverlapHomOnProperSmoothCurve
      K X f U hnonempty hcover hU h D i j)
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).p
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).p₁
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).p₂
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).p₁₂
    (hf₁ := (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).w₁)
    (hf₂ := (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).w₂)
    (hp₁ := (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).p₁₂_p₁)
    (hp₂ := (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).p₁₂_p₂)

private theorem raw_pullHom'₂₃_eq_transition
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i j k : (coordinateCover U hcover hU).I₀) :
    Pseudofunctor.DescentData'.pullHom'
        (F := LineBundleDescent.modulesPseudofunctor)
        (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
        (fun i j ↦ localLineBundleChosenOverlapHomOnProperSmoothCurve
          K X f U hnonempty hcover hU h D i j)
        (LineBundleDescent.tripleOverlap
          (coordinateCover U hcover hU) i j k).p
        (LineBundleDescent.tripleOverlap
          (coordinateCover U hcover hU) i j k).p₂
        (LineBundleDescent.tripleOverlap
          (coordinateCover U hcover hU) i j k).p₃ =
      localLineBundleRawTransition₂₃
        K X f U hnonempty hcover hU h D i j k := by
  exact Pseudofunctor.DescentData'.pullHom'_eq_pullHom
    (F := LineBundleDescent.modulesPseudofunctor)
    (obj := fun i ↦ (localLineBundles
      X U hnonempty hcover hU h D i).obj)
    (obj' := fun i ↦ (localLineBundles
      X U hnonempty hcover hU h D i).obj)
    (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
    (fun i j ↦ localLineBundleChosenOverlapHomOnProperSmoothCurve
      K X f U hnonempty hcover hU h D i j)
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).p
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).p₂
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).p₃
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).p₂₃
    (hf₁ := (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).w₂)
    (hf₂ := (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).w₃)
    (hp₁ := (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).p₂₃_p₂)
    (hp₂ := (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).p₂₃_p₃)

private theorem raw_pullHom'₁₃_eq_transition
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i j k : (coordinateCover U hcover hU).I₀) :
    Pseudofunctor.DescentData'.pullHom'
        (F := LineBundleDescent.modulesPseudofunctor)
        (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
        (fun i j ↦ localLineBundleChosenOverlapHomOnProperSmoothCurve
          K X f U hnonempty hcover hU h D i j)
        (LineBundleDescent.tripleOverlap
          (coordinateCover U hcover hU) i j k).p
        (LineBundleDescent.tripleOverlap
          (coordinateCover U hcover hU) i j k).p₁
        (LineBundleDescent.tripleOverlap
          (coordinateCover U hcover hU) i j k).p₃ =
      localLineBundleRawTransition₁₃
        K X f U hnonempty hcover hU h D i j k := by
  exact Pseudofunctor.DescentData'.pullHom'_eq_pullHom
    (F := LineBundleDescent.modulesPseudofunctor)
    (obj := fun i ↦ (localLineBundles
      X U hnonempty hcover hU h D i).obj)
    (obj' := fun i ↦ (localLineBundles
      X U hnonempty hcover hU h D i).obj)
    (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
    (fun i j ↦ localLineBundleChosenOverlapHomOnProperSmoothCurve
      K X f U hnonempty hcover hU h D i j)
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).p
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).p₁
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).p₃
    (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).p₁₃
    (hf₁ := (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).w₁)
    (hf₂ := (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).w₃)
    (hp₁ := (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).p₁₃_p₁)
    (hp₂ := (LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k).p₁₃_p₃)

/-- The raw cocycle in the exact `DescentData'` API used by line-bundle gluing. -/
theorem localLineBundleChosenOverlapHom_raw_cocycle_prime
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i j k : (coordinateCover U hcover hU).I₀) :
    let raw := fun i j ↦ localLineBundleChosenOverlapHomOnProperSmoothCurve
      K X f U hnonempty hcover hU h D i j
    let T := LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k
    Pseudofunctor.DescentData'.pullHom'
          (F := LineBundleDescent.modulesPseudofunctor)
          (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
          raw T.p T.p₁ T.p₂ ≫
        Pseudofunctor.DescentData'.pullHom'
          (F := LineBundleDescent.modulesPseudofunctor)
          (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
          raw T.p T.p₂ T.p₃ =
      Pseudofunctor.DescentData'.pullHom'
        (F := LineBundleDescent.modulesPseudofunctor)
        (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
        raw T.p T.p₁ T.p₃ := by
  dsimp only
  rw [raw_pullHom'₁₂_eq_transition, raw_pullHom'₂₃_eq_transition,
    raw_pullHom'₁₃_eq_transition]
  exact localLineBundleRawTransition_cocycle
    K X f U hnonempty hcover hU h D i j k

/-- The same raw cocycle, with each transition displayed as the forward map of its chosen
overlap isomorphism. -/
theorem localLineBundleChosenOverlapIso_raw_cocycle_prime
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i j k : (coordinateCover U hcover hU).I₀) :
    let rawIso := fun i j ↦ localLineBundleChosenOverlapIsoOnProperSmoothCurve
      K X f U hnonempty hcover hU h D i j
    let T := LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k
    Pseudofunctor.DescentData'.pullHom'
          (F := LineBundleDescent.modulesPseudofunctor)
          (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
          (fun i j ↦ (rawIso i j).hom) T.p T.p₁ T.p₂ ≫
        Pseudofunctor.DescentData'.pullHom'
          (F := LineBundleDescent.modulesPseudofunctor)
          (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
          (fun i j ↦ (rawIso i j).hom) T.p T.p₂ T.p₃ =
      Pseudofunctor.DescentData'.pullHom'
        (F := LineBundleDescent.modulesPseudofunctor)
        (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
        (fun i j ↦ (rawIso i j).hom) T.p T.p₁ T.p₃ := by
  simpa only [localLineBundleChosenOverlapIsoOnProperSmoothCurve_hom] using
    localLineBundleChosenOverlapHom_raw_cocycle_prime
      K X f U hnonempty hcover hU h D i j k

/-- The chosen raw overlap isomorphisms as one opaque family. -/
noncomputable def localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i j : (coordinateCover U hcover hU).I₀) :
    (LineBundleDescent.modulesPseudofunctor.map
      (LineBundleDescent.overlap
        (coordinateCover U hcover hU) i j).p₁.op.toLoc).toFunctor.obj
        (localLineBundles X U hnonempty hcover hU h D i).obj ≅
      (LineBundleDescent.modulesPseudofunctor.map
        (LineBundleDescent.overlap
          (coordinateCover U hcover hU) i j).p₂.op.toLoc).toFunctor.obj
        (localLineBundles X U hnonempty hcover hU h D j).obj :=
  localLineBundleChosenOverlapIsoOnProperSmoothCurve
    K X f U hnonempty hcover hU h D i j

/-- The raw cocycle in terms of the opaque isomorphism family. -/
theorem localLineBundleRawOverlapIsoFamily_cocycle_prime
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i j k : (coordinateCover U hcover hU).I₀) :
    let T := LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k
    let rawIso := localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
      K X f U hnonempty hcover hU h D
    Pseudofunctor.DescentData'.pullHom'
          (F := LineBundleDescent.modulesPseudofunctor)
          (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
          (fun i j ↦ (rawIso i j).hom) T.p T.p₁ T.p₂ ≫
        Pseudofunctor.DescentData'.pullHom'
          (F := LineBundleDescent.modulesPseudofunctor)
          (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
          (fun i j ↦ (rawIso i j).hom) T.p T.p₂ T.p₃ =
      Pseudofunctor.DescentData'.pullHom'
        (F := LineBundleDescent.modulesPseudofunctor)
        (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
        (fun i j ↦ (rawIso i j).hom) T.p T.p₁ T.p₃ := by
  unfold localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
  exact localLineBundleChosenOverlapIso_raw_cocycle_prime
    K X f U hnonempty hcover hU h D i j k

/-- The raw all-index cocycle, bundled behind a short concrete source type. -/
structure LocalLineBundleRawCocycleProof
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) : Prop where
  /-- The exact cocycle equation on every chosen triple overlap. -/
  cocycle (i j k : (coordinateCover U hcover hU).I₀) :
    let rawIso := fun i j ↦ localLineBundleChosenOverlapIsoOnProperSmoothCurve
      K X f U hnonempty hcover hU h D i j
    let T := LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k
    Pseudofunctor.DescentData'.pullHom'
          (F := LineBundleDescent.modulesPseudofunctor)
          (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
          (fun i j ↦ (rawIso i j).hom) T.p T.p₁ T.p₂ ≫
        Pseudofunctor.DescentData'.pullHom'
          (F := LineBundleDescent.modulesPseudofunctor)
          (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
          (fun i j ↦ (rawIso i j).hom) T.p T.p₂ T.p₃ =
      Pseudofunctor.DescentData'.pullHom'
        (F := LineBundleDescent.modulesPseudofunctor)
        (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
        (fun i j ↦ (rawIso i j).hom) T.p T.p₁ T.p₃

/-- The checked raw divisor transition theorem as its short source bundle. -/
theorem localLineBundleRawCocycleProof
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) :
    LocalLineBundleRawCocycleProof
      K X f U hnonempty hcover hU h D where
  cocycle := localLineBundleChosenOverlapIso_raw_cocycle_prime
    K X f U hnonempty hcover hU h D

/-- A short raw source bundle exposes the exact scheme-module cocycle package. -/
theorem LocalLineBundleRawCocycleProof.toSchemeModulesOverlapCocycle
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (c : LocalLineBundleRawCocycleProof
      K X f U hnonempty hcover hU h D) :
    SchemeModulesOverlapCocycle
      (LineBundleDescent.overlap (coordinateCover U hcover hU))
      (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU))
      (fun i ↦ (localLineBundles X U hnonempty hcover hU h D i).obj)
      (localLineBundleChosenOverlapIsoOnProperSmoothCurve
        K X f U hnonempty hcover hU h D) where
  cocycle := c.cocycle

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

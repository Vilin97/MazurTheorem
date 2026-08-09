/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveLineBundleRawNativeFamily

/-!
# Native pseudofunctor form of the raw divisor cocycle

The local module family is named with its exact pseudofunctor-object type.  The transition family
and cocycle are then restated against that same constant, eliminating later dependent type
conversion through the scheme-module abbreviation.
-/

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor

universe u v

/-- The native transition family satisfies the exact all-index cocycle. -/
theorem localLineBundleRawNativeOverlapIsoFamily_cocycle
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
          (fun i j ↦ (localLineBundleRawNativeOverlapIsoFamily
            K X f U hnonempty hcover hU h D i j).hom)
          (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p
          (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₁
          (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₂ ≫
        Pseudofunctor.DescentData'.pullHom'
          (F := LineBundleDescent.modulesPseudofunctor)
          (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
          (fun i j ↦ (localLineBundleRawNativeOverlapIsoFamily
            K X f U hnonempty hcover hU h D i j).hom)
          (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p
          (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₂
          (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₃ =
      Pseudofunctor.DescentData'.pullHom'
        (F := LineBundleDescent.modulesPseudofunctor)
        (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
        (fun i j ↦ (localLineBundleRawNativeOverlapIsoFamily
          K X f U hnonempty hcover hU h D i j).hom)
        (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p
        (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₁
        (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₃ := by
  convert localLineBundleRawOverlapIsoFamily_cocycle_prime
    K X f U hnonempty hcover hU h D i j k using 1
  · simp only [localLineBundleRawNativeOverlapIsoFamily_def,
      localLineBundleRawModuleObjectFamily]
    congr!

/-- The exact cocycle for the named native morphism family. -/
theorem localLineBundleRawNativeOverlapHomFamily_cocycle
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
          (localLineBundleRawNativeOverlapHomFamily
            K X f U hnonempty hcover hU h D)
          (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p
          (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₁
          (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₂ ≫
        Pseudofunctor.DescentData'.pullHom'
          (F := LineBundleDescent.modulesPseudofunctor)
          (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
          (localLineBundleRawNativeOverlapHomFamily
            K X f U hnonempty hcover hU h D)
          (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p
          (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₂
          (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₃ =
      Pseudofunctor.DescentData'.pullHom'
        (F := LineBundleDescent.modulesPseudofunctor)
        (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
        (localLineBundleRawNativeOverlapHomFamily
          K X f U hnonempty hcover hU h D)
        (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p
        (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₁
        (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₃ := by
  have hhom :
      localLineBundleRawNativeOverlapHomFamily
          K X f U hnonempty hcover hU h D =
        (fun a b ↦ (localLineBundleRawNativeOverlapIsoFamily
          K X f U hnonempty hcover hU h D a b).hom) := by
    funext a b
    rw [localLineBundleRawNativeOverlapHomFamily_def]
  rw [hhom]
  exact localLineBundleRawNativeOverlapIsoFamily_cocycle
    K X f U hnonempty hcover hU h D i j k

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

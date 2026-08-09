/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveLineBundleRawCocyclePrime

/-!
# Exact-signature form of the raw divisor cocycle

The raw theorem packages its repeated transition family with `let` binders.  This small checked
corollary exposes the definitionally equal type consumed by the generic descent constructor.
-/

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor

universe u v

/-- The raw cocycle with the transition family and triple overlap exposed. -/
theorem localLineBundleRawOverlapIsoFamily_cocycle_exact
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
          (fun i j ↦ (localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
            K X f U hnonempty hcover hU h D i j).hom)
          (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p
          (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₁
          (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₂ ≫
        Pseudofunctor.DescentData'.pullHom'
          (F := LineBundleDescent.modulesPseudofunctor)
          (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
          (fun i j ↦ (localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
            K X f U hnonempty hcover hU h D i j).hom)
          (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p
          (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₂
          (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₃ =
      Pseudofunctor.DescentData'.pullHom'
        (F := LineBundleDescent.modulesPseudofunctor)
        (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
        (fun i j ↦ (localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
          K X f U hnonempty hcover hU h D i j).hom)
        (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p
        (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₁
        (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k).p₃ := by
  simpa only using localLineBundleRawOverlapIsoFamily_cocycle_prime
    K X f U hnonempty hcover hU h D i j k

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

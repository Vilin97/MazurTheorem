/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveLineBundleRawNativeCocycle
import MazurTorsion.Upstream.CurveLineBundleIsoCocycleDescentDataPrime

/-!
# Packaged raw divisor cocycle

The native raw transition family and exact cocycle theorem are placed in the Prop-valued package
consumed by the normalization constructor.
-/

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor

universe u v

/-- The exact raw cocycle as the opaque proof package consumed by normalization. -/
theorem localLineBundleRawOverlapCocycle
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) :
    SchemeModulesOverlapCocycle
      (LineBundleDescent.overlap (coordinateCover U hcover hU))
      (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU))
      (localLineBundleRawModuleObjectFamily X U hnonempty hcover hU h D)
      (localLineBundleRawNativeOverlapIsoFamily
        K X f U hnonempty hcover hU h D) := by
  exact @SchemeModulesOverlapCocycle.mk X (coordinateCover U hcover hU)
    (LineBundleDescent.overlap (coordinateCover U hcover hU))
    (LineBundleDescent.tripleOverlap (coordinateCover U hcover hU))
    (localLineBundleRawModuleObjectFamily X U hnonempty hcover hU h D)
    (localLineBundleRawNativeOverlapIsoFamily
      K X f U hnonempty hcover hU h D)
    (localLineBundleRawNativeOverlapIsoFamily_cocycle
      K X f U hnonempty hcover hU h D)

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

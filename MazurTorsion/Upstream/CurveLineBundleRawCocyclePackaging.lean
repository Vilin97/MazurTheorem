/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveLineBundleRawCocycleSystem

/-!
# Packaging the raw divisor cocycle

This module passes the already compiled opaque inverse-ideal overlap family and its all-index
cocycle directly to the pseudofunctor-level normalization constructor.  No second pullback API
is introduced at this boundary.
-/

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor

universe u v

/-- The exact raw family and its all-index cocycle as full coherent descent data. -/
noncomputable def localLineBundleRawDescentDataOnProperSmoothCurve
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) :
    LineBundleDescent.modulesPseudofunctor.DescentData
      (coordinateCover U hcover hU).f := by
  let d := localLineBundleRawIsoCocycleSystem
    K X f U hnonempty hcover hU h D
  let D' := d.toDescentDataPrime
  exact Pseudofunctor.DescentData'.descentData
    (F := LineBundleDescent.modulesPseudofunctor)
    (f := (coordinateCover U hcover hU).f)
    (sq := d.sq) (sq₃ := d.sq₃) D'

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

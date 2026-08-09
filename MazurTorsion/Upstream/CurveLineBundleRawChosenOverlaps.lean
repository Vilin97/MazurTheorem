/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveLineBundleRawCocyclePrime

/-!
# Named chosen overlaps for the raw divisor cocycle

The standard pair and triple overlap families are placed behind stable compiled constants.  All
later dependent descent declarations refer to these same constants literally.
-/

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

universe u v

/-- The standard chosen pairwise overlaps of the coordinate cover as one named family. -/
noncomputable def localLineBundleRawChosenOverlap
    (X : Scheme.{u}) {I : Type v} (U : I → X.Opens)
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (i j : (coordinateCover U hcover hU).I₀) :
    ChosenPullback ((coordinateCover U hcover hU).f i)
      ((coordinateCover U hcover hU).f j) :=
  LineBundleDescent.overlap (coordinateCover U hcover hU) i j

/-- The standard chosen triple overlaps, typed against the named pairwise family. -/
noncomputable def localLineBundleRawChosenTripleOverlap
    (X : Scheme.{u}) {I : Type v} (U : I → X.Opens)
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (i j k : (coordinateCover U hcover hU).I₀) :
    ChosenPullback₃
      (localLineBundleRawChosenOverlap X U hcover hU i j)
      (localLineBundleRawChosenOverlap X U hcover hU j k)
      (localLineBundleRawChosenOverlap X U hcover hU i k) := by
  simpa only [localLineBundleRawChosenOverlap] using
    LineBundleDescent.tripleOverlap (coordinateCover U hcover hU) i j k

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

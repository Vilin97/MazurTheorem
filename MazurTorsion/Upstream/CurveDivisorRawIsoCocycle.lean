/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveLineBundleRawCocyclePrime
import MazurTorsion.Upstream.CurveLineBundleIsoCocycleDescent

/-!
# The raw divisor transition family as coherent descent data

This file proves the remaining argument of the geometric named-face cocycle constructor and
converts the result to coherent Mathlib descent data. The argument type is inferred from that
constructor, so its projection witnesses are shared verbatim instead of reconstructed. It
changes no transition maps and makes no effectivity claim. Its named downstream consumer is
`CurveDivisorGlobalLineBundle`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace
open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

universe u

/-- The raw geometric overlap family satisfies the named-face cocycle condition. -/
theorem rawDivisorIsoCocycleConditionOnProperSmoothCurve
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) :
    LineBundleDescent.LineBundleIsoCocycleCondition
      (coordinateCover U hcover hU)
      (localLineBundles X U hnonempty hcover hU h D)
      (localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
        K X f U hnonempty hcover hU h D) :=
  LineBundleDescent.CocycleConstructor.complete
    (LineBundleDescent.lineBundleIsoCocycleConditionConstructor
      (coordinateCover U hcover hU)
      (localLineBundles X U hnonempty hcover hU h D)
      (localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
        K X f U hnonempty hcover hU h D))
    (localLineBundleRawOverlapIsoFamily_cocycle_prime
      K X f U hnonempty hcover hU h D)

/-- Coherent module descent data obtained from the raw divisor overlap isomorphisms. -/
noncomputable def rawDivisorDescentDataOnProperSmoothCurve
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) :
    LineBundleDescent.modulesPseudofunctor.DescentData
      (coordinateCover U hcover hU).f :=
  LineBundleDescent.descentDataOfLineBundleIsoCocycleCondition
    (localLineBundles X U hnonempty hcover hU h D)
    (localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
      K X f U hnonempty hcover hU h D)
    (rawDivisorIsoCocycleConditionOnProperSmoothCurve
      K X f U hnonempty hcover hU h D)

@[simp]
lemma rawDivisorDescentDataOnProperSmoothCurve_obj
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i : (coordinateCover U hcover hU).I₀) :
    (rawDivisorDescentDataOnProperSmoothCurve
      K X f U hnonempty hcover hU h D).obj i =
        (localLineBundles X U hnonempty hcover hU h D i).obj :=
  rfl

/-- The raw divisor descent datum, together with the checked invertibility of every specified
local object. -/
noncomputable def rawDivisorInvertibleDescentDataOnProperSmoothCurve
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) :
    LineBundleDescent.InvertibleDescentData (coordinateCover U hcover hU) :=
  LineBundleDescent.invertibleDescentDataOfLineBundleIsoCocycleCondition
    (localLineBundles X U hnonempty hcover hU h D)
    (localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
      K X f U hnonempty hcover hU h D)
    (rawDivisorIsoCocycleConditionOnProperSmoothCurve
      K X f U hnonempty hcover hU h D)

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

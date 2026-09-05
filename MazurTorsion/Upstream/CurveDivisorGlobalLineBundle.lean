/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveDivisorRawIsoCocycle
import MazurTorsion.Upstream.CurveLineBundleCompatibleFamilies
import MazurTorsion.Upstream.CurveLineBundleLocality

/-!
# The global line bundle of a divisor on a proper smooth curve

The raw inverse-ideal transition maps of a divisor form coherent locally invertible descent
data. On a universe-zero affine coordinate cover, the compatible-family equalizer proves module
effectivity, and locality of invertibility upgrades the resulting module to an invertible sheaf.
This constructs the global divisor line bundle without any caller-supplied effectivity witness.

The checked outputs include the full descent isomorphism and the restriction isomorphism to each
specified affine divisor line bundle. This is an object-level effectivity boundary for the fixed
coordinate cover. It does not claim fully faithful descent, independence of the chosen cover,
tensor additivity, or a Picard-group equivalence. The named downstream consumer is the
divisor-to-Picard comparison in `CurveDivisorPicardEquivalence`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace
open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

universe u

/-- The raw divisor descent datum is unconditionally effective on the universe-zero coordinate
cover. -/
theorem rawDivisorEffectiveInvertibleOnProperSmoothCurve
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) :
    LineBundleDescent.EffectiveInvertible (coordinateCover U hcover hU)
      (rawDivisorDescentDataOnProperSmoothCurve
        K X f U hnonempty hcover hU h D) :=
  (LineBundleDescent.invertibleEffectiveDescentFor_of_moduleEffectivity
    (LineBundleDescent.moduleEffectiveDescentForOpenCover
      (coordinateCover U hcover hU)))
    (rawDivisorInvertibleDescentDataOnProperSmoothCurve
      K X f U hnonempty hcover hU h D)

/-- The global invertible sheaf associated to a divisor on a proper smooth curve. No effectivity
witness is an argument: it is supplied internally by compatible-family descent. -/
noncomputable def globalDivisorLineBundleOnProperSmoothCurve
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) : InvertibleSheaf X :=
  (rawDivisorEffectiveInvertibleOnProperSmoothCurve
    K X f U hnonempty hcover hU h D).lineBundle

/-- The global divisor line bundle realizes exactly the coherent descent datum built from the
raw inverse-ideal transitions. -/
noncomputable def globalDivisorLineBundleDescentIsoOnProperSmoothCurve
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) :
    (LineBundleDescent.modulesPseudofunctor.toDescentData
      (coordinateCover U hcover hU).f).obj
        (globalDivisorLineBundleOnProperSmoothCurve
          K X f U hnonempty hcover hU h D).obj ≅
      rawDivisorDescentDataOnProperSmoothCurve
        K X f U hnonempty hcover hU h D :=
  (rawDivisorEffectiveInvertibleOnProperSmoothCurve
    K X f U hnonempty hcover hU h D).descentIso

/-- On every coordinate chart, the global divisor line bundle restricts to the specified local
inverse-ideal line bundle. -/
noncomputable def globalDivisorLineBundleRestrictionIsoOnProperSmoothCurve
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i : (coordinateCover U hcover hU).I₀) :
    (Scheme.Modules.pullback ((coordinateCover U hcover hU).f i)).obj
        (globalDivisorLineBundleOnProperSmoothCurve
          K X f U hnonempty hcover hU h D).obj ≅
      (localLineBundles X U hnonempty hcover hU h D i).obj :=
  (rawDivisorEffectiveInvertibleOnProperSmoothCurve
      K X f U hnonempty hcover hU h D).restrictionIso i ≪≫
    eqToIso (rawDivisorDescentDataOnProperSmoothCurve_obj
      K X f U hnonempty hcover hU h D i)

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

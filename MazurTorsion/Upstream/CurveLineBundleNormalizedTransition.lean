/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveLineBundleRawCocycleComparisons

/-!
# Normalized divisor transitions on curve-chart overlaps

The divisor transition isomorphism is definitionally aligned with the raw `pullHom` used by
triple-overlap naturality. Off the diagonal, normalization retains that raw transition; on the
diagonal, it selects the canonical coherent self-overlap isomorphism.
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

/-- Away from the diagonal, normalized overlap isomorphisms retain the explicit transported
inverse-ideal comparison. -/
theorem localLineBundleNormalizedOverlapIsoOnProperSmoothCurve_of_ne
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i j : (coordinateCover U hcover hU).I₀) (hij : i ≠ j) :
    localLineBundleNormalizedOverlapIsoOnProperSmoothCurve
        K X f U hnonempty hcover hU h D i j =
      localLineBundleChosenOverlapIsoOnProperSmoothCurve
        K X f U hnonempty hcover hU h D i j := by
  simp [localLineBundleNormalizedOverlapIsoOnProperSmoothCurve,
    LineBundleDescent.normalizeOverlapDiagonal, hij]

/-- Away from the diagonal, the normalized transition's forward map is exactly the raw chosen
overlap morphism used by the triple-naturality theorems. -/
theorem localLineBundleNormalizedOverlapIsoOnProperSmoothCurve_hom_of_ne
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i j : (coordinateCover U hcover hU).I₀) (hij : i ≠ j) :
    (localLineBundleNormalizedOverlapIsoOnProperSmoothCurve
      K X f U hnonempty hcover hU h D i j).hom =
      localLineBundleChosenOverlapHomOnProperSmoothCurve
        K X f U hnonempty hcover hU h D i j := by
  rw [localLineBundleNormalizedOverlapIsoOnProperSmoothCurve_of_ne
    K X f U hnonempty hcover hU h D i j hij]
  exact localLineBundleChosenOverlapIsoOnProperSmoothCurve_hom
    K X f U hnonempty hcover hU h D i j

/-- The off-diagonal comparison remains true after an arbitrary further pullback. This is the
form consumed by distinct-index triple-cocycle assembly. -/
theorem pullHom_localLineBundleNormalizedOverlapIsoOnProperSmoothCurve_of_ne
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i j : (coordinateCover U hcover hU).I₀) (hij : i ≠ j)
    {Y : Scheme.{u}}
    (q : Y ⟶ (LineBundleDescent.overlap
      (coordinateCover U hcover hU) i j).pullback)
    (q₁ : Y ⟶ (coordinateCover U hcover hU).X i)
    (q₂ : Y ⟶ (coordinateCover U hcover hU).X j)
    (hq₁ : q ≫ (LineBundleDescent.overlap
      (coordinateCover U hcover hU) i j).p₁ = q₁)
    (hq₂ : q ≫ (LineBundleDescent.overlap
      (coordinateCover U hcover hU) i j).p₂ = q₂) :
    pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundleNormalizedOverlapIsoOnProperSmoothCurve
          K X f U hnonempty hcover hU h D i j).hom
        q q₁ q₂ hq₁ hq₂ =
      pullHom (F := LineBundleDescent.modulesPseudofunctor)
        (localLineBundleChosenOverlapHomOnProperSmoothCurve
          K X f U hnonempty hcover hU h D i j)
        q q₁ q₂ hq₁ hq₂ := by
  rw [localLineBundleNormalizedOverlapIsoOnProperSmoothCurve_hom_of_ne
    K X f U hnonempty hcover hU h D i j hij]

/-- On the diagonal, normalization selects the canonical self-overlap isomorphism furnished by
the coherent one-object descent datum of the chart immersion. -/
theorem localLineBundleNormalizedOverlapIsoOnProperSmoothCurve_self
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i : (coordinateCover U hcover hU).I₀) :
    localLineBundleNormalizedOverlapIsoOnProperSmoothCurve
        K X f U hnonempty hcover hU h D i i =
      LineBundleDescent.monoSelfOverlapIso
        ((coordinateCover U hcover hU).f i)
        (localLineBundles X U hnonempty hcover hU h D i).obj
        (LineBundleDescent.overlap (coordinateCover U hcover hU) i i) := by
  simp [localLineBundleNormalizedOverlapIsoOnProperSmoothCurve,
    LineBundleDescent.normalizeOverlapDiagonal]

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

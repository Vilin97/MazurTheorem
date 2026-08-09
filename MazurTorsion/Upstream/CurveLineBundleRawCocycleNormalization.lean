/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveLineBundleRawNativeCocycle
import MazurTorsion.Upstream.CurveLineBundleCocycleForcesNormalization

/-!
# Diagonal normalization of the raw divisor cocycle

The native inverse-ideal transition family is isomorphism-valued and satisfies the all-index
cocycle, so its diagonal pullback is the identity.
-/

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor

universe u

/-- Pulling the raw diagonal transition back to the chart makes it idempotent. -/
theorem localLineBundleRawNativeOverlapHomFamily_diagonal_idempotent
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i : (coordinateCover U hcover hU).I₀)
    (hi : (𝟙 ((coordinateCover U hcover hU).X i)) ≫
      (coordinateCover U hcover hU).f i =
        (coordinateCover U hcover hU).f i) :
    let e := Pseudofunctor.DescentData'.pullHom'
      (F := LineBundleDescent.modulesPseudofunctor)
      (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
      (localLineBundleRawNativeOverlapHomFamily
        K X f U hnonempty hcover hU h D)
      ((coordinateCover U hcover hU).f i)
      (𝟙 ((coordinateCover U hcover hU).X i))
      (𝟙 ((coordinateCover U hcover hU).X i))
      hi hi
    e ≫ e = e := by
  dsimp only
  exact Pseudofunctor.DescentData'.comp_pullHom''
    (C := Scheme.{u})
    (F := LineBundleDescent.modulesPseudofunctor)
    (ι := (coordinateCover U hcover hU).I₀)
    (S := X)
    (X := (coordinateCover U hcover hU).X)
    (f := (coordinateCover U hcover hU).f)
    (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
    (obj := localLineBundleRawModuleObjectFamily X U hnonempty hcover hU h D)
    (hom := localLineBundleRawNativeOverlapHomFamily
      K X f U hnonempty hcover hU h D)
    (sq₃ := LineBundleDescent.tripleOverlap (coordinateCover U hcover hU))
    (hom_comp := localLineBundleRawNativeOverlapHomFamily_cocycle
      K X f U hnonempty hcover hU h D)
    (Y := (coordinateCover U hcover hU).X i)
    (q := (coordinateCover U hcover hU).f i)
    (i₁ := i) (i₂ := i) (i₃ := i)
    (f₁ := 𝟙 ((coordinateCover U hcover hU).X i))
    (f₂ := 𝟙 ((coordinateCover U hcover hU).X i))
    (f₃ := 𝟙 ((coordinateCover U hcover hU).X i))
    (hf₁ := hi) (hf₂ := hi) (hf₃ := hi)

/-- The raw divisor transition family is exactly normalized on every diagonal overlap. -/
theorem localLineBundleRawNativeOverlapHomFamily_normalization
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i : (coordinateCover U hcover hU).I₀) :
    Pseudofunctor.DescentData'.pullHom'
      (F := LineBundleDescent.modulesPseudofunctor)
      (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
      (localLineBundleRawNativeOverlapHomFamily
        K X f U hnonempty hcover hU h D)
      ((coordinateCover U hcover hU).f i)
      (𝟙 ((coordinateCover U hcover hU).X i))
      (𝟙 ((coordinateCover U hcover hU).X i)) = 𝟙 _ := by
  let hi : (𝟙 ((coordinateCover U hcover hU).X i)) ≫
      (coordinateCover U hcover hU).f i =
        (coordinateCover U hcover hU).f i := by simp
  let e := Pseudofunctor.DescentData'.pullHom'
    (F := LineBundleDescent.modulesPseudofunctor)
    (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
    (localLineBundleRawNativeOverlapHomFamily
      K X f U hnonempty hcover hU h D)
    ((coordinateCover U hcover hU).f i)
    (𝟙 ((coordinateCover U hcover hU).X i))
    (𝟙 ((coordinateCover U hcover hU).X i))
    hi hi
  have hee : e ≫ e = e := by
    exact localLineBundleRawNativeOverlapHomFamily_diagonal_idempotent
      K X f U hnonempty hcover hU h D i hi
  change e = 𝟙 _
  haveI : IsIso e := by
    dsimp only [e, Pseudofunctor.DescentData'.pullHom']
    apply pullHom_isIso_of_isIso
  apply (cancel_epi e).1
  simpa only [Category.comp_id] using hee

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

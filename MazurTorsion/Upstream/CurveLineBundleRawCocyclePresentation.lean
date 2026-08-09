/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveLineBundleRawCocycleNormalization
import Mathlib.Tactic.IrreducibleDef

/-!
# Sealed presentation of the normalized raw divisor cocycle

This internal module seals the large inverse-ideal overlap isomorphism family before assembly.
It exports the sealed family, its normalization and triple coherence, and the checked equality
identifying it with the concrete raw transition.
-/

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open scoped AlgebraicGeometry

universe u

namespace Internal

noncomputable irreducible_def rawOverlapIso
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i j : (coordinateCover U hcover hU).I₀) :
    (Scheme.Modules.pullback
      (LineBundleDescent.overlap
        (coordinateCover U hcover hU) i j).p₁).obj
        (localLineBundles X U hnonempty hcover hU h D i).obj ≅
      (Scheme.Modules.pullback
        (LineBundleDescent.overlap
          (coordinateCover U hcover hU) i j).p₂).obj
        (localLineBundles X U hnonempty hcover hU h D j).obj :=
  localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
    K X f U hnonempty hcover hU h D i j

theorem rawOverlapIso_normalization
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
      (fun a b ↦ (rawOverlapIso
        K X f U hnonempty hcover hU h D a b).hom)
      ((coordinateCover U hcover hU).f i)
      (𝟙 ((coordinateCover U hcover hU).X i))
      (𝟙 ((coordinateCover U hcover hU).X i)) = 𝟙 _ := by
  have hhom :
      (fun a b ↦ (rawOverlapIso
        K X f U hnonempty hcover hU h D a b).hom) =
        (fun a b ↦ (localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
          K X f U hnonempty hcover hU h D a b).hom) := by
    funext a b
    rw [rawOverlapIso_def]
  rw [hhom]
  exact Internal.localLineBundleRawOverlapIsoFamily_normalization
    K X f U hnonempty hcover hU h D i

theorem rawOverlapIso_cocycle
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i j k : (coordinateCover U hcover hU).I₀) :
    let T := LineBundleDescent.tripleOverlap
      (coordinateCover U hcover hU) i j k
    Pseudofunctor.DescentData'.pullHom'
          (F := LineBundleDescent.modulesPseudofunctor)
          (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
          (fun a b ↦ (rawOverlapIso
            K X f U hnonempty hcover hU h D a b).hom)
          T.p T.p₁ T.p₂ ≫
        Pseudofunctor.DescentData'.pullHom'
          (F := LineBundleDescent.modulesPseudofunctor)
          (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
          (fun a b ↦ (rawOverlapIso
            K X f U hnonempty hcover hU h D a b).hom)
          T.p T.p₂ T.p₃ =
      Pseudofunctor.DescentData'.pullHom'
        (F := LineBundleDescent.modulesPseudofunctor)
        (sq := LineBundleDescent.overlap (coordinateCover U hcover hU))
        (fun a b ↦ (rawOverlapIso
          K X f U hnonempty hcover hU h D a b).hom)
        T.p T.p₁ T.p₃ := by
  have hhom :
      (fun a b ↦ (rawOverlapIso
        K X f U hnonempty hcover hU h D a b).hom) =
        (fun a b ↦ (localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
          K X f U hnonempty hcover hU h D a b).hom) := by
    funext a b
    rw [rawOverlapIso_def]
  rw [hhom]
  exact localLineBundleRawOverlapIsoFamily_cocycle_prime
    K X f U hnonempty hcover hU h D i j k

/-- The sealed overlap family is exactly the checked raw inverse-ideal isomorphism. -/
theorem rawOverlapIso_eq
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i j : (coordinateCover U hcover hU).I₀) :
    rawOverlapIso K X f U hnonempty hcover hU h D i j =
      localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
        K X f U hnonempty hcover hU h D i j := by
  rw [rawOverlapIso_def]

end Internal

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

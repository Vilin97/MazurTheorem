/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveDivisorGlobalTensorAdd
import MazurTorsion.Upstream.CurveDivisorPicardDescent

/-!
# The concrete divisor cocycle system on a proper smooth curve

This file connects the unconditional raw divisor descent construction to the abstract
divisor-to-Picard interface.  It reconstructs a normalized chosen-overlap cocycle from each raw
full descent datum, compares that reconstruction back to the raw datum, and uses the already
constructed global divisor line bundle as its effectivity witness.  Consequently the resulting
concrete cocycle system is unconditionally effective and tensor-additive.

The remaining design boundary is explicit: constructing the Picard homomorphism from this
system still requires a global trivialization of its zero-divisor member.  The named downstream
consumer is the coherent principal-triviality and exact-kernel comparison for this same concrete
system.
-/

noncomputable section

open CategoryTheory MonoidalCategory
open TopologicalSpace
open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

universe u

/-- The standard monoidal structure on sheaves of modules over a scheme. -/
noncomputable local instance schemeModulesMonoidalForPicardEquivalence (Y : Scheme.{u}) :
    MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y

/-- The concrete divisor-indexed cocycle system reconstructed from the raw full descent data. -/
noncomputable def rawDivisorCocycleSystemOnProperSmoothCurve
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i)) :
    DivisorCocycleSystem X U hnonempty hcover hU h :=
  fun D ↦
    LineBundleDescent.LineBundleCocycle.ofDescentDataObjectIso
      (localLineBundles X U hnonempty hcover hU h D)
      (rawDivisorDescentDataOnProperSmoothCurve
        K X f U hnonempty hcover hU h D)
      (fun i ↦ Iso.refl
        ((rawDivisorDescentDataOnProperSmoothCurve
          K X f U hnonempty hcover hU h D).obj i))

/-- Reconstructing the chosen-overlap cocycle does not change the raw full descent datum. -/
noncomputable def rawDivisorCocycleSystemDescentIsoOnProperSmoothCurve
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) :
    (rawDivisorCocycleSystemOnProperSmoothCurve
        K X f U hnonempty hcover hU h D).toDescentData ≅
      rawDivisorDescentDataOnProperSmoothCurve
        K X f U hnonempty hcover hU h D :=
  LineBundleDescent.LineBundleCocycle.ofDescentDataObjectIso_toDescentDataIso
      (localLineBundles X U hnonempty hcover hU h D)
      (rawDivisorDescentDataOnProperSmoothCurve
        K X f U hnonempty hcover hU h D)
      (fun i ↦ Iso.refl
        ((rawDivisorDescentDataOnProperSmoothCurve
          K X f U hnonempty hcover hU h D).obj i)) ≪≫
    (LineBundleDescent.PseudofunctorDescent.changeObjectsIso
      (coordinateCover U hcover hU).f
      (rawDivisorDescentDataOnProperSmoothCurve
        K X f U hnonempty hcover hU h D)
      (fun i ↦
        (localLineBundles X U hnonempty hcover hU h D i).obj)
      (fun i ↦ Iso.refl
        ((rawDivisorDescentDataOnProperSmoothCurve
          K X f U hnonempty hcover hU h D).obj i))).symm

/-- The concrete raw divisor cocycle system is represented by the unconditional global divisor
line bundles. -/
theorem rawDivisorCocycleSystemEffectiveOnProperSmoothCurve
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i)) :
    EffectiveDivisorCocycleSystem X U hnonempty hcover hU h
      (rawDivisorCocycleSystemOnProperSmoothCurve
        K X f U hnonempty hcover hU h) :=
  fun D ↦ ⟨globalDivisorLineBundleOnProperSmoothCurve
      K X f U hnonempty hcover hU h D,
    ⟨globalDivisorLineBundleDescentIsoOnProperSmoothCurve
        K X f U hnonempty hcover hU h D ≪≫
      (rawDivisorCocycleSystemDescentIsoOnProperSmoothCurve
        K X f U hnonempty hcover hU h D).symm⟩⟩

/-- Fully faithful descent canonically compares the line bundle selected by the concrete
cocycle-system effectivity proof with the previously constructed global divisor line bundle. -/
noncomputable def descendedLineBundleIsoGlobalDivisorLineBundleOnProperSmoothCurve
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) :
    (descendedLineBundle X U hnonempty hcover hU h
        (rawDivisorCocycleSystemOnProperSmoothCurve
          K X f U hnonempty hcover hU h)
        (rawDivisorCocycleSystemEffectiveOnProperSmoothCurve
          K X f U hnonempty hcover hU h) D).obj ≅
      (globalDivisorLineBundleOnProperSmoothCurve
        K X f U hnonempty hcover hU h D).obj :=
  (rawDivisorCocycleSystemEffectiveOnProperSmoothCurve
      K X f U hnonempty hcover hU h D).preimageIso
    (LineBundleDescent.moduleDescentFullyFaithfulForOpenCover
      (coordinateCover U hcover hU))
    (rawDivisorCocycleSystemDescentIsoOnProperSmoothCurve
        K X f U hnonempty hcover hU h D ≪≫
      (globalDivisorLineBundleDescentIsoOnProperSmoothCurve
        K X f U hnonempty hcover hU h D).symm)

/-- The concrete effective divisor cocycle system is unconditionally tensor-additive. -/
theorem rawDivisorCocycleSystemTensorAdditiveOnProperSmoothCurve
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i)) :
    DescendedTensorAdditive X U hnonempty hcover hU h
      (rawDivisorCocycleSystemOnProperSmoothCurve
        K X f U hnonempty hcover hU h)
      (rawDivisorCocycleSystemEffectiveOnProperSmoothCurve
        K X f U hnonempty hcover hU h) := by
  intro D E
  exact ⟨descendedLineBundleIsoGlobalDivisorLineBundleOnProperSmoothCurve
      K X f U hnonempty hcover hU h (D + E) ≪≫
    globalDivisorLineBundleAddIsoOnProperSmoothCurve
      K X f U hnonempty hcover hU h D E ≪≫
    MonoidalCategory.tensorIso
      (descendedLineBundleIsoGlobalDivisorLineBundleOnProperSmoothCurve
        K X f U hnonempty hcover hU h D).symm
      (descendedLineBundleIsoGlobalDivisorLineBundleOnProperSmoothCurve
        K X f U hnonempty hcover hU h E).symm⟩

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

end

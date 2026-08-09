/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveLineBundleRawCocyclePrime

/-! # Native object and transition families for the raw divisor cocycle -/

open CategoryTheory CategoryTheory.Limits
open TopologicalSpace
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor

universe u v

/-- The affine divisor modules with their native module-pseudofunctor object type. -/
noncomputable def localLineBundleRawModuleObjectFamily
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i : (coordinateCover U hcover hU).I₀) :
    LineBundleDescent.modulesPseudofunctor.obj
      (.mk (.op ((coordinateCover U hcover hU).X i))) :=
  (localLineBundles X U hnonempty hcover hU h D i).obj

/-- The raw transition family typed against the named overlap and local-module families. -/
noncomputable irreducible_def localLineBundleRawNativeOverlapIsoFamily
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i j : (coordinateCover U hcover hU).I₀) :
    (LineBundleDescent.modulesPseudofunctor.map
      (LineBundleDescent.overlap
        (coordinateCover U hcover hU) i j).p₁.op.toLoc).toFunctor.obj
      (localLineBundleRawModuleObjectFamily X U hnonempty hcover hU h D i) ≅
    (LineBundleDescent.modulesPseudofunctor.map
      (LineBundleDescent.overlap
        (coordinateCover U hcover hU) i j).p₂.op.toLoc).toFunctor.obj
      (localLineBundleRawModuleObjectFamily X U hnonempty hcover hU h D j) := by
  exact localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
    K X f U hnonempty hcover hU h D i j

/-- The morphism family underlying the native raw overlap isomorphisms.  Naming this dependent
function keeps later pullback calculations from repeatedly elaborating the isomorphism family. -/
noncomputable irreducible_def localLineBundleRawNativeOverlapHomFamily
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i j : (coordinateCover U hcover hU).I₀) :
    (LineBundleDescent.modulesPseudofunctor.map
      (LineBundleDescent.overlap
        (coordinateCover U hcover hU) i j).p₁.op.toLoc).toFunctor.obj
      (localLineBundleRawModuleObjectFamily X U hnonempty hcover hU h D i) ⟶
    (LineBundleDescent.modulesPseudofunctor.map
      (LineBundleDescent.overlap
        (coordinateCover U hcover hU) i j).p₂.op.toLoc).toFunctor.obj
      (localLineBundleRawModuleObjectFamily X U hnonempty hcover hU h D j) :=
  (localLineBundleRawNativeOverlapIsoFamily
    K X f U hnonempty hcover hU h D i j).hom

/-- Every map in the named native hom family is invertible. -/
instance localLineBundleRawNativeOverlapHomFamily_isIso
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i j : (coordinateCover U hcover hU).I₀) :
    IsIso (localLineBundleRawNativeOverlapHomFamily
      K X f U hnonempty hcover hU h D i j) := by
  rw [localLineBundleRawNativeOverlapHomFamily_def]
  infer_instance

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

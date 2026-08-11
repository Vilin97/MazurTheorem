/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveDivisorTensorAddDescent
import MazurTorsion.Upstream.CurveDivisorTensorAddFactorwiseChosenOverlap

/-!
# Factorwise chosen-overlap presentation of the tensor-addition descent isomorphism

Conditional on supplied cocycles for `D`, `E`, and `D + E` whose chosen-overlap Homs are the
checked raw geometric transitions, this file gives the chosen-overlap component square of the
existing full descent-data addition isomorphism.  Its target transition is displayed through the
separately supplied cocycles for `D` and `E`.

This is only a chosen-overlap presentation of that existing isomorphism.  It exports no separate
target-Hom equality or arbitrary-refinement formula, constructs no new tensor descent datum, and
claims no new effectivity result.
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open TopologicalSpace
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open scoped AlgebraicGeometry TensorProduct

universe u v

@[reducible]
noncomputable local instance schemeModulesMonoidalForFactorwiseDescent (Y : Scheme.{u}) :
    MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y

noncomputable local instance pullbackMonoidalForFactorwiseDescent
    {X Y : Scheme.{u}} (g : X ⟶ Y) : (Scheme.Modules.pullback g).Monoidal :=
  Scheme.Modules.pullbackMonoidal g

/-- Under raw-Hom alignment of the supplied `D`, `E`, and `D + E` cocycles, the local components
of the existing full descent-data addition isomorphism satisfy the chosen-overlap morphism square
with the target transition displayed factorwise through the `D` and `E` cocycles.  This is the
direct categorical descent consumer of
`localLineBundleAddIso_chosenOverlap_commViaFactorwiseRawTensor`.

This theorem is only a chosen-overlap presentation of the existing full isomorphism: it exports
no standalone target-Hom equality or arbitrary-refinement formula, constructs no new tensor
descent datum, and proves no new effectivity statement. -/
theorem
    localLineBundleAddDescentDataIsoViaTransportedTensorModel_hom_commViaFactorwiseCocycleOverlaps
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X))
    (CD : DivisorCocycle X U hnonempty hcover hU h D)
    (CE : DivisorCocycle X U hnonempty hcover hU h E)
    (CDE : DivisorCocycle X U hnonempty hcover hU h (D + E))
    (hrawD : ∀ i j, (CD.overlapIso i j).hom =
      (localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
        K X f U hnonempty hcover hU h D i j).hom)
    (hrawE : ∀ i j, (CE.overlapIso i j).hom =
      (localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
        K X f U hnonempty hcover hU h E i j).hom)
    (hrawDE : ∀ i j, (CDE.overlapIso i j).hom =
      (localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
        K X f U hnonempty hcover hU h (D + E) i j).hom)
    (i j : (coordinateCover U hcover hU).I₀) :
    let P := LineBundleDescent.overlap (coordinateCover U hcover hU) i j
    let e := localLineBundleAddDescentDataIsoViaTransportedTensorModel
      X U hnonempty hcover hU h D E CDE
    (Scheme.Modules.pullback P.p₁).map (e.hom.hom i) ≫
        ((Functor.Monoidal.μIso (Scheme.Modules.pullback P.p₁)
            (localLineBundles X U hnonempty hcover hU h D i).obj
            (localLineBundles X U hnonempty hcover hU h E i).obj).symm ≪≫
          (CD.overlapIso i j ⊗ᵢ CE.overlapIso i j) ≪≫
          Functor.Monoidal.μIso (Scheme.Modules.pullback P.p₂)
            (localLineBundles X U hnonempty hcover hU h D j).obj
            (localLineBundles X U hnonempty hcover hU h E j).obj).hom =
      (CDE.overlapIso i j).hom ≫
        (Scheme.Modules.pullback P.p₂).map (e.hom.hom j) := by
  letI := hnonempty i
  letI := hnonempty j
  let P := LineBundleDescent.overlap (coordinateCover U hcover hU) i j
  let e := localLineBundleAddDescentDataIsoViaTransportedTensorModel
    X U hnonempty hcover hU h D E CDE
  let add₁ := localLineBundleAddIso X (U i) (hU i) (h i) D E
  let add₂ := localLineBundleAddIso X (U j) (hU j) (h j) D E
  change
    (Scheme.Modules.pullback P.p₁).map add₁.hom ≫
        ((Functor.Monoidal.μIso (Scheme.Modules.pullback P.p₁)
            (localLineBundles X U hnonempty hcover hU h D i).obj
            (localLineBundles X U hnonempty hcover hU h E i).obj).symm ≪≫
          (CD.overlapIso i j ⊗ᵢ CE.overlapIso i j) ≪≫
          Functor.Monoidal.μIso (Scheme.Modules.pullback P.p₂)
            (localLineBundles X U hnonempty hcover hU h D j).obj
            (localLineBundles X U hnonempty hcover hU h E j).obj).hom =
      (CDE.overlapIso i j).hom ≫
        (Scheme.Modules.pullback P.p₂).map add₂.hom
  have hD : CD.overlapIso i j =
      localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
        K X f U hnonempty hcover hU h D i j :=
    Iso.ext (hrawD i j)
  have hE : CE.overlapIso i j =
      localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
        K X f U hnonempty hcover hU h E i j :=
    Iso.ext (hrawE i j)
  rw [hD, hE, hrawDE i j]
  exact localLineBundleAddIso_chosenOverlap_commViaFactorwiseRawTensor
    K X f U hnonempty hcover hU h D E i j

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

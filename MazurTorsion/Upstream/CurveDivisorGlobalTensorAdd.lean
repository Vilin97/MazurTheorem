/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveLineBundleTensorDescent
import MazurTorsion.Upstream.CurveLineBundleFullyFaithful
import MazurTorsion.Upstream.CurveDivisorGlobalLineBundle
import MazurTorsion.Upstream.CurveDivisorRawTensorAddDescent

/-!
# Tensor additivity of the global divisor line bundle

The canonical chartwise tensor descent datum of the global line bundles for two divisors is
compared directly with the raw datum for their sum.  On each chart the comparison tensors the
two effectivity isomorphisms and then inverts the local divisor-addition isomorphism.  The
factorwise descent square and the raw addition square prove compatibility on chosen overlaps,
which lifts to an unconditional isomorphism of full coherent descent data.

The design boundary is explicit: this file consumes fully faithful module descent on the
universe-zero coordinate cover, proved by the compatible-family equalizer in
`CurveLineBundleFullyFaithful`.  The resulting global tensor comparison is unconditional.  Its
named downstream consumer is the divisor-to-Picard homomorphism in
`CurveDivisorPicardEquivalence`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open TopologicalSpace
open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open scoped AlgebraicGeometry TensorProduct

open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

section

universe u

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

open LineBundleDescent

private noncomputable abbrev moduleFiber (Y : Scheme.{u}) :=
  modulesPseudofunctor.obj (.mk (.op Y))

private noncomputable abbrev modulePullback {X Y : Scheme.{u}} (g : X ⟶ Y) :=
  (modulesPseudofunctor.map g.op.toLoc).toFunctor

@[reducible]
noncomputable local instance schemeModulesMonoidalForGlobalTensorAdd
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Scheme.Modules.monoidalCategory X

@[reducible]
noncomputable local instance pullbackMonoidalForGlobalTensorAdd
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).Monoidal :=
  Scheme.Modules.pullbackMonoidal f

@[reducible]
noncomputable local instance (priority := 100) moduleFiberMonoidalForGlobalTensorAdd
    (Y : Scheme.{u}) : MonoidalCategory (moduleFiber Y) :=
  Scheme.Modules.monoidalCategory Y

@[reducible]
noncomputable local instance (priority := 100) modulePullbackMonoidalForGlobalTensorAdd
    {X Y : Scheme.{u}} (g : X ⟶ Y) : (modulePullback g).Monoidal :=
  Scheme.Modules.pullbackMonoidal g

private theorem rawDivisorDescentData_hom_eq_rawOverlap
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i j : (coordinateCover U hcover hU).I₀) :
    let P := overlap (coordinateCover U hcover hU) i j
    (rawDivisorDescentDataOnProperSmoothCurve
      K X f U hnonempty hcover hU h D).hom P.p P.p₁ P.p₂ =
        (localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
          K X f U hnonempty hcover hU h D i j).hom :=
  descentDataOfLineBundleIsoCocycleCondition_hom_on_overlap
    (localLineBundles X U hnonempty hcover hU h D)
    (localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
      K X f U hnonempty hcover hU h D)
    (rawDivisorIsoCocycleConditionOnProperSmoothCurve
      K X f U hnonempty hcover hU h D) i j

private noncomputable def globalDivisorDescentComponentIso
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i : (coordinateCover U hcover hU).I₀) :
    ((modulesPseudofunctor.toDescentData
      (coordinateCover U hcover hU).f).obj
        (globalDivisorLineBundleOnProperSmoothCurve
          K X f U hnonempty hcover hU h D).obj).obj i ≅
      (rawDivisorDescentDataOnProperSmoothCurve
        K X f U hnonempty hcover hU h D).obj i :=
  descentDataIsoComponent
    (globalDivisorLineBundleDescentIsoOnProperSmoothCurve
      K X f U hnonempty hcover hU h D) i

private noncomputable def directRawAddData
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X)) :
    modulesPseudofunctor.DescentData (coordinateCover U hcover hU).f :=
  rawDivisorDescentDataOnProperSmoothCurve
    K X f U hnonempty hcover hU h (D + E)

private noncomputable def directTensorData
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X)) :
    modulesPseudofunctor.DescentData (coordinateCover U hcover hU).f :=
  let cov := coordinateCover U hcover hU
  let LD := globalDivisorLineBundleOnProperSmoothCurve
    K X f U hnonempty hcover hU h D
  let LE := globalDivisorLineBundleOnProperSmoothCurve
    K X f U hnonempty hcover hU h E
  tensorOfObjDescentData cov LD.obj LE.obj

private noncomputable def directFactorComponent
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X))
    (i : (coordinateCover U hcover hU).I₀) :=
  globalDivisorDescentComponentIso
    K X f U hnonempty hcover hU h D i

private noncomputable def directComponents
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X)) :
    ∀ i : (coordinateCover U hcover hU).I₀,
      (directTensorData K X f U hnonempty hcover hU h D E).obj i ≅
        (directRawAddData K X f U hnonempty hcover hU h D E).obj i :=
  let cov := coordinateCover U hcover hU
  let rD := fun i : cov.I₀ ↦ directFactorComponent
    K X f U hnonempty hcover hU h D i
  let rE := fun i : cov.I₀ ↦ directFactorComponent
    K X f U hnonempty hcover hU h E i
  let add := fun i : cov.I₀ ↦ rawLocalLineBundleAddIsoOnProperSmoothCurve
    K X f U hnonempty hcover hU h D E i
  fun i : cov.I₀ ↦ (rD i ⊗ᵢ rE i) ≪≫ (add i).symm


private noncomputable def directCanonicalTensorTransition
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X))
    (i j : (coordinateCover U hcover hU).I₀) :
    let cov := coordinateCover U hcover hU
    let P := overlap cov i j
    (Scheme.Modules.pullback P.p₁).obj
          ((directTensorData K X f U hnonempty hcover hU h D E).obj i) ⟶
      (Scheme.Modules.pullback P.p₂).obj
        ((directTensorData K X f U hnonempty hcover hU h D E).obj j) :=
  let cov := coordinateCover U hcover hU
  let LD := globalDivisorLineBundleOnProperSmoothCurve
    K X f U hnonempty hcover hU h D
  let LE := globalDivisorLineBundleOnProperSmoothCurve
    K X f U hnonempty hcover hU h E
  let P := overlap cov i j
  let cD := ((modulesPseudofunctor.toDescentData cov.f).obj LD.obj).iso
    P.p P.p₁ P.p₂ P.hp₁ P.hp₂
  let cE := ((modulesPseudofunctor.toDescentData cov.f).obj LE.obj).iso
    P.p P.p₁ P.p₂ P.hp₁ P.hp₂
  ((Functor.Monoidal.μIso (Scheme.Modules.pullback P.p₁)
        ((Scheme.Modules.pullback (cov.f i)).obj LD.obj)
        ((Scheme.Modules.pullback (cov.f i)).obj LE.obj)).symm ≪≫
    (cD ⊗ᵢ cE) ≪≫
    Functor.Monoidal.μIso (Scheme.Modules.pullback P.p₂)
      ((Scheme.Modules.pullback (cov.f j)).obj LD.obj)
      ((Scheme.Modules.pullback (cov.f j)).obj LE.obj)).hom

private noncomputable def directRawAddTransition
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X))
    (i j : (coordinateCover U hcover hU).I₀) :
    let cov := coordinateCover U hcover hU
    let P := overlap cov i j
    (Scheme.Modules.pullback P.p₁).obj
          ((directRawAddData K X f U hnonempty hcover hU h D E).obj i) ⟶
      (Scheme.Modules.pullback P.p₂).obj
        ((directRawAddData K X f U hnonempty hcover hU h D E).obj j) :=
  (localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
    K X f U hnonempty hcover hU h (D + E) i j).hom

private theorem directTensorData_hom_eq
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X))
    (i j : (coordinateCover U hcover hU).I₀) :
    let cov := coordinateCover U hcover hU
    let P := overlap cov i j
    (directTensorData K X f U hnonempty hcover hU h D E).hom
        P.p P.p₁ P.p₂ P.hp₁ P.hp₂ =
      directCanonicalTensorTransition
        K X f U hnonempty hcover hU h D E i j := by
  let cov := coordinateCover U hcover hU
  let LD := globalDivisorLineBundleOnProperSmoothCurve
    K X f U hnonempty hcover hU h D
  let LE := globalDivisorLineBundleOnProperSmoothCurve
    K X f U hnonempty hcover hU h E
  exact tensorOfObjDescentData_hom_on_overlap cov LD.obj LE.obj i j

private theorem directRawAddData_hom_eq
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X))
    (i j : (coordinateCover U hcover hU).I₀) :
    let cov := coordinateCover U hcover hU
    let P := overlap cov i j
    (directRawAddData K X f U hnonempty hcover hU h D E).hom
        P.p P.p₁ P.p₂ P.hp₁ P.hp₂ =
      directRawAddTransition
        K X f U hnonempty hcover hU h D E i j :=
  rawDivisorDescentData_hom_eq_rawOverlap
    K X f U hnonempty hcover hU h (D + E) i j

private theorem directModeledCommAt
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X))
    (i j : (coordinateCover U hcover hU).I₀) :
    let cov := coordinateCover U hcover hU
    let P := overlap cov i j
    (Scheme.Modules.pullback P.p₁).map
          (directComponents K X f U hnonempty hcover hU h D E i).hom ≫
        directRawAddTransition
          K X f U hnonempty hcover hU h D E i j =
      directCanonicalTensorTransition
          K X f U hnonempty hcover hU h D E i j ≫
        (Scheme.Modules.pullback P.p₂).map
          (directComponents K X f U hnonempty hcover hU h D E j).hom := by
  let cov := coordinateCover U hcover hU
  let rawD := rawDivisorDescentDataOnProperSmoothCurve
    K X f U hnonempty hcover hU h D
  let rawE := rawDivisorDescentDataOnProperSmoothCurve
    K X f U hnonempty hcover hU h E
  let rawDE := rawDivisorDescentDataOnProperSmoothCurve
    K X f U hnonempty hcover hU h (D + E)
  let effD := rawDivisorEffectiveInvertibleOnProperSmoothCurve
    K X f U hnonempty hcover hU h D
  let effE := rawDivisorEffectiveInvertibleOnProperSmoothCurve
    K X f U hnonempty hcover hU h E
  let LD := effD.lineBundle
  let LE := effE.lineBundle
  let descentD := effD.descentIso
  let descentE := effE.descentIso
  let tD := localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
    K X f U hnonempty hcover hU h D i j
  let tE := localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
    K X f U hnonempty hcover hU h E i j
  let tDE := localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
    K X f U hnonempty hcover hU h (D + E) i j
  exact tensorThenInverseDescentIsoComponents_comm_on_overlap
    (D := rawD) (E := rawE) (R := rawDE)
    cov LD.obj LE.obj descentD descentE i j tD tE tDE
    (rawLocalLineBundleAddIsoOnProperSmoothCurve
      K X f U hnonempty hcover hU h D E i)
    (rawLocalLineBundleAddIsoOnProperSmoothCurve
      K X f U hnonempty hcover hU h D E j)
    (rawDivisorDescentData_hom_eq_rawOverlap
      K X f U hnonempty hcover hU h D i j)
    (rawDivisorDescentData_hom_eq_rawOverlap
      K X f U hnonempty hcover hU h E i j)
    (localLineBundleAddIso_chosenOverlap_commViaFactorwiseRawTensor
      K X f U hnonempty hcover hU h D E i j)

private noncomputable def directPrimeIso
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X)) :=
  let cov := coordinateCover U hcover hU
  let tensorData := directTensorData
    K X f U hnonempty hcover hU h D E
  let rawAddData := directRawAddData
    K X f U hnonempty hcover hU h D E
  let e := directComponents K X f U hnonempty hcover hU h D E
  let rawTransition := fun i j : cov.I₀ ↦
    directRawAddTransition
      K X f U hnonempty hcover hU h D E i j
  let canonicalTransition := fun i j : cov.I₀ ↦
    directCanonicalTensorTransition
      K X f U hnonempty hcover hU h D E i j
  primeIsoOfChosenTransitionModels cov tensorData rawAddData e
    rawTransition canonicalTransition
    (directRawAddData_hom_eq
      K X f U hnonempty hcover hU h D E)
    (directTensorData_hom_eq
      K X f U hnonempty hcover hU h D E)
    (directModeledCommAt
      K X f U hnonempty hcover hU h D E)

private noncomputable def directFullIso
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X)) :
    directTensorData K X f U hnonempty hcover hU h D E ≅
      directRawAddData K X f U hnonempty hcover hU h D E :=
  fullIsoOfChosenOverlaps (coordinateCover U hcover hU)
    (directTensorData K X f U hnonempty hcover hU h D E)
    (directRawAddData K X f U hnonempty hcover hU h D E)
    (directPrimeIso K X f U hnonempty hcover hU h D E)

/-- Unconditional tensor additivity at the level of full coherent descent data: the raw datum
for `D + E` is the canonical restriction datum of the tensor of the two global divisor
modules. -/
noncomputable def rawDivisorAddToGlobalTensorDescentIsoOnProperSmoothCurve
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X)) :
    rawDivisorDescentDataOnProperSmoothCurve
        K X f U hnonempty hcover hU h (D + E) ≅
      (modulesPseudofunctor.toDescentData
        (coordinateCover U hcover hU).f).obj
          ((globalDivisorLineBundleOnProperSmoothCurve
              K X f U hnonempty hcover hU h D).obj ⊗
            (globalDivisorLineBundleOnProperSmoothCurve
              K X f U hnonempty hcover hU h E).obj) :=
  (directFullIso K X f U hnonempty hcover hU h D E).symm ≪≫
    (tensorOfObjDescentIso
      (coordinateCover U hcover hU)
      (globalDivisorLineBundleOnProperSmoothCurve
        K X f U hnonempty hcover hU h D).obj
      (globalDivisorLineBundleOnProperSmoothCurve
        K X f U hnonempty hcover hU h E).obj).symm

/-- Fully faithful module descent lifts the descent-level tensor comparison to the global
divisor modules. -/
noncomputable def globalDivisorLineBundleAddIsoOnProperSmoothCurve_of_fullyFaithful
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X))
    (hfaithful : ModuleDescentFullyFaithfulFor
      (coordinateCover U hcover hU)) :
    (globalDivisorLineBundleOnProperSmoothCurve
        K X f U hnonempty hcover hU h (D + E)).obj ≅
      (globalDivisorLineBundleOnProperSmoothCurve
          K X f U hnonempty hcover hU h D).obj ⊗
        (globalDivisorLineBundleOnProperSmoothCurve
          K X f U hnonempty hcover hU h E).obj :=
  (rawDivisorEffectiveInvertibleOnProperSmoothCurve
    K X f U hnonempty hcover hU h (D + E)).preimageIso hfaithful
      (rawDivisorAddToGlobalTensorDescentIsoOnProperSmoothCurve
        K X f U hnonempty hcover hU h D E)

/-- The global divisor line bundle of a sum is the tensor product of the two global divisor line
bundles.  Fully faithful descent on the coordinate cover is supplied unconditionally by the
compatible-family reconstruction theorem. -/
noncomputable def globalDivisorLineBundleAddIsoOnProperSmoothCurve
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X)) :
    (globalDivisorLineBundleOnProperSmoothCurve
        K X f U hnonempty hcover hU h (D + E)).obj ≅
      (globalDivisorLineBundleOnProperSmoothCurve
          K X f U hnonempty hcover hU h D).obj ⊗
        (globalDivisorLineBundleOnProperSmoothCurve
          K X f U hnonempty hcover hU h E).obj :=
  globalDivisorLineBundleAddIsoOnProperSmoothCurve_of_fullyFaithful
    K X f U hnonempty hcover hU h D E
      (moduleDescentFullyFaithfulForOpenCover
        (coordinateCover U hcover hU))

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

end

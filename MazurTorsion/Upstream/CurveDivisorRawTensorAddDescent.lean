/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveDivisorRawIsoCocycle
import MazurTorsion.Upstream.CurveDivisorTensorAddFactorwiseChosenOverlap

/-!
# Tensor additivity of the raw divisor descent datum

The full raw descent datum for `D + E` is transported across the actual chartwise
isomorphisms `𝒪(D + E) ≅ 𝒪(D) ⊗ 𝒪(E)`.  The resulting datum is therefore coherent on every
common base change by construction.  On each chosen pairwise overlap, its transition is proved
to be exactly the tensor of the raw transitions for `D` and `E`, conjugated by the canonical
pullback tensorators.

This is a descent-level tensor-additivity boundary.  It does not yet lift the resulting
isomorphism to the global effective objects; that step additionally uses fully faithful module
descent.  Its named downstream consumer is `CurveDivisorGlobalTensorAdd`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open TopologicalSpace
open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open scoped AlgebraicGeometry TensorProduct

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

universe u

/-- The standard monoidal structure on module sheaves, used by the local tensor models. -/
noncomputable local instance schemeModulesMonoidalForRawTensorAddDescent (Y : Scheme.{u}) :
    MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y

/-- Pullback of module sheaves is strongly monoidal. -/
noncomputable local instance pullbackMonoidalForRawTensorAddDescent
    {X Y : Scheme.{u}} (g : X ⟶ Y) : (Scheme.Modules.pullback g).Monoidal :=
  Scheme.Modules.pullbackMonoidal g

/-- The chartwise tensor product of the two raw divisor line bundles. -/
noncomputable def rawLocalLineBundleTensorObjectOnProperSmoothCurve
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X))
    (i : (coordinateCover U hcover hU).I₀) :
    ((coordinateCover U hcover hU).X i).Modules :=
  (localLineBundles X U hnonempty hcover hU h D i).obj ⊗
    (localLineBundles X U hnonempty hcover hU h E i).obj

/-- The actual local addition isomorphism, displayed with the raw sum datum as source and the
chartwise tensor object as target. -/
noncomputable def rawLocalLineBundleAddIsoOnProperSmoothCurve
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X))
    (i : (coordinateCover U hcover hU).I₀) :
    (rawDivisorDescentDataOnProperSmoothCurve
        K X f U hnonempty hcover hU h (D + E)).obj i ≅
      rawLocalLineBundleTensorObjectOnProperSmoothCurve
        X U hnonempty hcover hU h D E i := by
  letI := hnonempty i
  exact localLineBundleAddIso X (U i) (hU i) (h i) D E

/-- Transport the raw descent datum for `D + E` to the chartwise tensor objects.  Coherence on
all common base changes is inherited from the already checked raw sum datum. -/
noncomputable def rawDivisorTensorDescentDataOnProperSmoothCurve
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X)) :
    LineBundleDescent.modulesPseudofunctor.DescentData
      (coordinateCover U hcover hU).f :=
  LineBundleDescent.PseudofunctorDescent.changeObjects
    (coordinateCover U hcover hU).f
    (rawDivisorDescentDataOnProperSmoothCurve
      K X f U hnonempty hcover hU h (D + E))
    (rawLocalLineBundleTensorObjectOnProperSmoothCurve
      X U hnonempty hcover hU h D E)
    (rawLocalLineBundleAddIsoOnProperSmoothCurve
      K X f U hnonempty hcover hU h D E)

/-- Full coherent descent-level tensor additivity for the raw divisor datum. -/
noncomputable def rawDivisorAddDescentIsoOnProperSmoothCurve
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X)) :
    rawDivisorDescentDataOnProperSmoothCurve
        K X f U hnonempty hcover hU h (D + E) ≅
      rawDivisorTensorDescentDataOnProperSmoothCurve
        K X f U hnonempty hcover hU h D E :=
  LineBundleDescent.PseudofunctorDescent.changeObjectsIso
    (coordinateCover U hcover hU).f
    (rawDivisorDescentDataOnProperSmoothCurve
      K X f U hnonempty hcover hU h (D + E))
    (rawLocalLineBundleTensorObjectOnProperSmoothCurve
      X U hnonempty hcover hU h D E)
    (rawLocalLineBundleAddIsoOnProperSmoothCurve
      K X f U hnonempty hcover hU h D E)

/-- Solving a commuting isomorphism square for its transported target transition. -/
private theorem conjugated_hom_eq_of_comm
    {C : Type*} [Category C] {A B C' D : C}
    (a : A ≅ B) (s : A ≅ C') (b : C' ≅ D) (t : B ≅ D)
    (h : a.hom ≫ t.hom = s.hom ≫ b.hom) :
    a.inv ≫ s.hom ≫ b.hom = t.hom := by
  rw [← h, ← Category.assoc, a.inv_hom_id, Category.id_comp]

/-- On a chosen overlap, the transported tensor datum uses the already checked whole
pairwise tensor-model transition. -/
theorem rawDivisorTensorDescentData_hom_on_chosenOverlap
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X))
    (i j : (coordinateCover U hcover hU).I₀) :
    let P := LineBundleDescent.overlap (coordinateCover U hcover hU) i j
    (rawDivisorTensorDescentDataOnProperSmoothCurve
      K X f U hnonempty hcover hU h D E).hom P.p P.p₁ P.p₂ =
        (localLineBundleTensorChosenOverlapIsoOfPairwiseModelOnProperSmoothCurve
          K X f U hnonempty hcover hU h D E i j).hom := by
  letI := hnonempty i
  letI := hnonempty j
  let add₁ := localLineBundleAddIso X (U i) (hU i) (h i) D E
  let add₂ := localLineBundleAddIso X (U j) (hU j) (h j) D E
  let P := LineBundleDescent.overlap (coordinateCover U hcover hU) i j
  let raw := localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
    K X f U hnonempty hcover hU h (D + E) i j
  let tensorTransition :=
    localLineBundleTensorChosenOverlapIsoOfPairwiseModelOnProperSmoothCurve
      K X f U hnonempty hcover hU h D E i j
  let pulledAdd₁ := (Scheme.Modules.pullback P.p₁).mapIso add₁
  let pulledAdd₂ := (Scheme.Modules.pullback P.p₂).mapIso add₂
  have hcomm := localLineBundleAddIso_chosenOverlap_commViaTransportedTensorModel
    K X f U hnonempty hcover hU h D E i j
  dsimp only at hcomm
  change pulledAdd₁.hom ≫ tensorTransition.hom =
    raw.hom ≫ pulledAdd₂.hom at hcomm
  have hsource :=
    LineBundleDescent.descentDataOfLineBundleIsoCocycleCondition_hom_on_overlap
    (localLineBundles X U hnonempty hcover hU h (D + E))
    (localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
      K X f U hnonempty hcover hU h (D + E))
    (rawDivisorIsoCocycleConditionOnProperSmoothCurve
      K X f U hnonempty hcover hU h (D + E)) i j
  change (rawDivisorDescentDataOnProperSmoothCurve
      K X f U hnonempty hcover hU h (D + E)).hom P.p P.p₁ P.p₂ =
    raw.hom at hsource
  dsimp only
  unfold rawDivisorTensorDescentDataOnProperSmoothCurve
  unfold LineBundleDescent.PseudofunctorDescent.changeObjects
  change pulledAdd₁.inv ≫
      (rawDivisorDescentDataOnProperSmoothCurve
        K X f U hnonempty hcover hU h (D + E)).hom P.p P.p₁ P.p₂ ≫
        pulledAdd₂.hom = tensorTransition.hom
  rw [hsource]
  exact conjugated_hom_eq_of_comm pulledAdd₁ raw pulledAdd₂ tensorTransition hcomm

/-- On every chosen overlap, the target of raw tensor additivity has precisely the factorwise
tensor transition of `D` and `E`, conjugated by the two canonical pullback tensorators. -/
theorem rawDivisorTensorDescentData_hom_eq_tensorRawOverlap
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X))
    (i j : (coordinateCover U hcover hU).I₀) :
    let P := LineBundleDescent.overlap (coordinateCover U hcover hU) i j
    (rawDivisorTensorDescentDataOnProperSmoothCurve
      K X f U hnonempty hcover hU h D E).hom P.p P.p₁ P.p₂ =
      ((Functor.Monoidal.μIso (Scheme.Modules.pullback P.p₁)
          (localLineBundles X U hnonempty hcover hU h D i).obj
          (localLineBundles X U hnonempty hcover hU h E i).obj).symm ≪≫
        (localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
            K X f U hnonempty hcover hU h D i j ⊗ᵢ
          localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
            K X f U hnonempty hcover hU h E i j) ≪≫
        Functor.Monoidal.μIso (Scheme.Modules.pullback P.p₂)
          (localLineBundles X U hnonempty hcover hU h D j).obj
          (localLineBundles X U hnonempty hcover hU h E j).obj).hom := by
  letI := hnonempty i
  letI := hnonempty j
  let P := LineBundleDescent.overlap (coordinateCover U hcover hU) i j
  have hchosen := rawDivisorTensorDescentData_hom_on_chosenOverlap
    K X f U hnonempty hcover hU h D E i j
  have hfactor := congrArg Iso.hom
    (localLineBundleTensorChosenOverlapIsoOfPairwiseModel_eq_tensorRawOverlapIsoFamily
      K X f U hnonempty hcover hU h D E i j)
  dsimp only at hchosen hfactor ⊢
  exact hchosen.trans hfactor

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

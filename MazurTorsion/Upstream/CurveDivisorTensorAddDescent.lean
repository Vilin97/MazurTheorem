/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveDivisorTensorAddChosenOverlap

/-!
# Descent consumer for tensor addition on curve charts

This file packages the checked chosen-overlap tensor/addition square as genuine descent data,
conditional on an already supplied divisor cocycle for `D + E` whose overlap maps are the raw
geometric transitions.  The target datum is obtained by transporting the source datum across the
actual chartwise addition isomorphisms.  Its chosen transition is therefore the transported whole
tensor-model comparison constructed in `CurveDivisorTensorAddChosenOverlap`.

This does not construct the raw arbitrary-divisor cocycle and does not identify the target with a
factorwise tensor product of separately descended data for `D` and `E`.
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open TopologicalSpace
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor
open scoped AlgebraicGeometry TensorProduct

universe u v

/-- The standard monoidal structure on sheaves of modules over a scheme. -/
noncomputable local instance schemeModulesMonoidalForTensorAddDescent (Y : Scheme.{u}) :
    MonoidalCategory Y.Modules :=
  Scheme.Modules.monoidalCategory Y

/-- Solving a commuting Iso square for its target transition gives the conjugated source
transition used by objectwise transport. -/
private theorem conjugated_hom_eq_of_comm
    {C : Type*} [Category C] {A B C' D : C}
    (a : A ≅ B) (s : A ≅ C') (b : C' ≅ D) (t : B ≅ D)
    (h : a.hom ≫ t.hom = s.hom ≫ b.hom) :
    a.inv ≫ s.hom ≫ b.hom = t.hom := by
  rw [← h, ← Category.assoc, a.inv_hom_id, Category.id_comp]

/-- The chartwise tensor object used by the transported target descent datum. -/
private noncomputable def localLineBundleTensorObjectForDescent
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X))
    (i : (coordinateCover U hcover hU).I₀) :
    ((coordinateCover U hcover hU).X i).Modules :=
  (localLineBundles X U hnonempty hcover hU h D i).obj ⊗
    (localLineBundles X U hnonempty hcover hU h E i).obj

/-- The actual local addition isomorphism, with the source displayed as the local object of a
supplied cocycle for `D + E`. -/
private noncomputable def localLineBundleAddIsoFromCocycle
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X))
    (CDE : DivisorCocycle X U hnonempty hcover hU h (D + E))
    (i : (coordinateCover U hcover hU).I₀) :
    CDE.toDescentData.obj i ≅
      localLineBundleTensorObjectForDescent
        X U hnonempty hcover hU h D E i := by
  letI := hnonempty i
  change (localLineBundles X U hnonempty hcover hU h (D + E) i).obj ≅
    (localLineBundles X U hnonempty hcover hU h D i).obj ⊗
      (localLineBundles X U hnonempty hcover hU h E i).obj
  exact localLineBundleAddIso X (U i) (hU i) (h i) D E

/-- Transport the descent datum for `D + E` across the actual chartwise addition isomorphisms.
The resulting local objects are the chartwise tensors `O(D) ⊗ O(E)`.  Its transitions are
conjugates of those of the supplied source cocycle; no factorwise tensor-descent interpretation
is asserted here. -/
noncomputable def localLineBundleTransportedTensorModelDescentData
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X))
    (CDE : DivisorCocycle X U hnonempty hcover hU h (D + E)) :
    LineBundleDescent.modulesPseudofunctor.DescentData
      (coordinateCover U hcover hU).f :=
  LineBundleDescent.PseudofunctorDescent.changeObjects
    (coordinateCover U hcover hU).f CDE.toDescentData
    (fun i ↦ localLineBundleTensorObjectForDescent
      X U hnonempty hcover hU h D E i)
    (localLineBundleAddIsoFromCocycle
      X U hnonempty hcover hU h D E CDE)

/-- The source cocycle datum is isomorphic to its objectwise transport to the chartwise tensor
objects.  This is a full Mathlib `DescentData` isomorphism, not merely a family of local maps. -/
noncomputable def localLineBundleAddDescentDataIsoViaTransportedTensorModel
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X))
    (CDE : DivisorCocycle X U hnonempty hcover hU h (D + E)) :
    CDE.toDescentData ≅
      localLineBundleTransportedTensorModelDescentData
        X U hnonempty hcover hU h D E CDE :=
  LineBundleDescent.PseudofunctorDescent.changeObjectsIso
    (coordinateCover U hcover hU).f CDE.toDescentData
    (fun i ↦ localLineBundleTensorObjectForDescent
      X U hnonempty hcover hU h D E i)
    (localLineBundleAddIsoFromCocycle
      X U hnonempty hcover hU h D E CDE)

/-- Effectivity of the supplied sum cocycle transfers across the full descent-data isomorphism
to the transported tensor-model datum. -/
theorem localLineBundleTransportedTensorModelEffective_of_sumCocycleEffective
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X))
    (CDE : DivisorCocycle X U hnonempty hcover hU h (D + E))
    (heffective : LineBundleDescent.EffectiveInvertible
      (coordinateCover U hcover hU) CDE.toDescentData) :
    LineBundleDescent.EffectiveInvertible (coordinateCover U hcover hU)
      (localLineBundleTransportedTensorModelDescentData
        X U hnonempty hcover hU h D E CDE) := by
  rcases heffective with ⟨L, ⟨e⟩⟩
  exact ⟨L, ⟨e ≪≫
    localLineBundleAddDescentDataIsoViaTransportedTensorModel
      X U hnonempty hcover hU h D E CDE⟩⟩

/-- If the supplied sum cocycle uses the checked raw overlap family, the chosen transition of
the transported target datum is exactly the public whole tensor-model transition.  This is the
descent-data consumer of
`localLineBundleAddIso_chosenOverlap_commViaTransportedTensorModel`; it deliberately does not
replace the whole comparison by a tensor of two separately transported factor transitions. -/
theorem localLineBundleTransportedTensorModelDescentData_hom_on_chosenOverlap
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D E : WeilDivisor (CodimensionOnePoint X))
    (CDE : DivisorCocycle X U hnonempty hcover hU h (D + E))
    (hraw : ∀ i j, (CDE.overlapIso i j).hom =
      (localLineBundleRawOverlapIsoFamilyOnProperSmoothCurve
        K X f U hnonempty hcover hU h (D + E) i j).hom)
    (i j : (coordinateCover U hcover hU).I₀) :
    let P := LineBundleDescent.overlap (coordinateCover U hcover hU) i j
    (localLineBundleTransportedTensorModelDescentData
      X U hnonempty hcover hU h D E CDE).hom P.p P.p₁ P.p₂ =
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
  have hsource := LineBundleDescent.LineBundleCocycle.toDescentData_hom_on_overlap
    CDE i j
  change CDE.toDescentData.hom P.p P.p₁ P.p₂ =
    (CDE.overlapIso i j).hom at hsource
  have hrawij := hraw i j
  change (CDE.overlapIso i j).hom = raw.hom at hrawij
  dsimp only
  unfold localLineBundleTransportedTensorModelDescentData
  unfold LineBundleDescent.PseudofunctorDescent.changeObjects
  change
    pulledAdd₁.inv ≫ CDE.toDescentData.hom P.p P.p₁ P.p₂ ≫
        pulledAdd₂.hom =
      tensorTransition.hom
  rw [hsource, hrawij]
  exact conjugated_hom_eq_of_comm pulledAdd₁ raw pulledAdd₂ tensorTransition hcomm

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

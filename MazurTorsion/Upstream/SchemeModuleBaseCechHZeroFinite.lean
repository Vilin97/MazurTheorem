/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project, Vasily Ilin, Codex

The ordered/native homology transfer is adapted from the Apache-licensed
degree-one comparison in AINTLIB.
-/

import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleOrderedBaseCechAlternating
import MazurTorsion.Upstream.SchemeModuleBaseCechHZeroComparison
import MazurTorsion.Upstream.SchemeModuleOrderedBaseCechLowDegreeSupport

/-!
# Genuine degree-zero cohomology from ordered Cech finiteness

In degree zero every tuple is strictly increasing, so projection from the
native all-tuples Cech complex followed by alternating extension is the
identity on cochains.  It follows that alternating extension is surjective
on degree-zero homology.  Ordered Cech finite generation can therefore be
transported first to native Cech homology and then, through the canonical
base-linear comparison, to genuine Ext-based sheaf `H⁰`.

This is the named downstream consumer of
`SchemeModuleBaseCechHZeroComparison`.  The final theorem consumes the
existing coherent-support comodel boundary; constructing those comodels for
proper schemes remains a separate obligation.
-/

noncomputable section

universe u

open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

private theorem baseCechToOrdered_comp_orderedToBaseCechAlternating_f_zero
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    baseCechToOrderedF π M U 0 ≫
        orderedToBaseCechAlternatingF π M U 0 =
      𝟙 ((baseCechComplex π M U).X 0) := by
  apply (cancel_mono (baseCechXIsoPi π M U 0).hom).1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext i
  have hi : StrictMono i := by
    rw [Fin.strictMono_iff_lt_succ]
    exact fun k ↦ Fin.elim0 k
  let pᵢ : (baseCechComplex π M U).X 0 ⟶
      baseCechFactor π M U 0 i :=
    Pi.π (fun j : Fin 1 → ι ↦ baseCechFactor π M U 0 j) i
  let qᵢ : orderedBaseCechObject π M U 0 ⟶
      baseCechFactor π M U 0 i :=
    Pi.π (fun j : OrderedCechIndex ι 0 ↦
      baseCechFactor π M U 0 j.1) ⟨i, hi⟩
  have hs : orderedToBaseCechAlternatingF π M U 0 ≫ pᵢ = qᵢ := by
    exact orderedToBaseCechAlternatingF_comp_π_of_strictMono
      π M U 0 i hi
  have hp : baseCechToOrderedF π M U 0 ≫ qᵢ = pᵢ := by
    exact baseCechToOrderedF_comp_π π M U 0 ⟨i, hi⟩
  have hcomponent :
      (baseCechToOrderedF π M U 0 ≫
          orderedToBaseCechAlternatingF π M U 0) ≫ pᵢ = pᵢ := by
    rw [Category.assoc, hs, hp]
  let q : ModuleCat.of Γ(S, (⊤ : S.Opens))
        (∀ j : Fin 1 → ι, baseCechFactor π M U 0 j) ⟶
      ModuleCat.of Γ(S, (⊤ : S.Opens)) (baseCechFactor π M U 0 i) :=
    ModuleCat.ofHom (LinearMap.proj i)
  have happ : ((((baseCechToOrderedF π M U 0 ≫
      orderedToBaseCechAlternatingF π M U 0) ≫
        (baseCechXIsoPi π M U 0).hom) ≫ q).hom x) =
      (((baseCechXIsoPi π M U 0).hom ≫ q).hom x) := by
    rw [Category.assoc, baseCechXIsoPi_hom_comp_proj]
    exact ConcreteCategory.congr_hom hcomponent x
  exact happ

/-- Alternating extension from the ordered Cech complex is surjective on
degree-zero homology. -/
private theorem orderedToBaseCechAlternating_homologyMap_zero_surjective
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    Function.Surjective
      (HomologicalComplex.homologyMap
        (orderedToBaseCechAlternating π M U) 0).hom := by
  let B := baseCechComplex π M U
  let O := orderedBaseCechComplex π M U
  let p := baseCechToOrdered π M U
  let s := orderedToBaseCechAlternating π M U
  intro ξ
  have hπ : Function.Surjective (B.homologyπ 0).hom :=
    (ModuleCat.epi_iff_surjective (B.homologyπ 0)).mp inferInstance
  obtain ⟨xc, rfl⟩ := hπ ξ
  let yc := HomologicalComplex.cyclesMap p 0 |>.hom xc
  refine ⟨(O.homologyπ 0).hom yc, ?_⟩
  have hnat := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (φ := s) (i := 0)) yc
  simp only [ConcreteCategory.comp_apply] at hnat
  rw [hnat]
  have hcycles : (HomologicalComplex.cyclesMap s 0).hom yc = xc := by
    apply (ModuleCat.mono_iff_injective (B.iCycles 0)).mp inferInstance
    have hsi := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (φ := s) (i := 0)) yc
    have hpi := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (φ := p) (i := 0)) xc
    simp only [ConcreteCategory.comp_apply] at hsi hpi
    rw [hsi, hpi]
    exact ConcreteCategory.congr_hom
      (baseCechToOrdered_comp_orderedToBaseCechAlternating_f_zero
        π M U) ((B.iCycles 0).hom xc)
  exact congrArg (B.homologyπ 0).hom hcycles

/-- Finite generation of ordered Cech homology implies finite generation of
native all-tuples Cech homology in degree zero. -/
theorem baseCechComplex_homology_zero_module_finite_of_orderedBaseCechComplex
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    [Module.Finite Γ(S, (⊤ : S.Opens))
      ((orderedBaseCechComplex π M U).homology 0)] :
    Module.Finite Γ(S, (⊤ : S.Opens))
      ((baseCechComplex π M U).homology 0) := by
  let f := HomologicalComplex.homologyMap
    (orderedToBaseCechAlternating π M U) 0
  have hf : Function.Surjective f.hom :=
    orderedToBaseCechAlternating_homologyMap_zero_surjective π M U
  exact Module.Finite.of_surjective f.hom hf

end AlgebraicGeometry.Scheme.Modules

open _root_.AlgebraicGeometry.Scheme.Modules

namespace MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

/-- Ordered degree-zero base-Cech finite generation on an open cover implies
finite generation of genuine sheaf `H⁰` for the canonical base action. -/
theorem hZero_finite_of_orderedBaseCechComplex
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (hU : IsOpenCover U)
    [Module.Finite Γ(S, (⊤ : S.Opens))
      ((orderedBaseCechComplex π M U).homology 0)] :
    letI := baseSectionsHZeroModule π M
    Module.Finite Γ(S, (⊤ : S.Opens)) (H M 0) := by
  letI : Module.Finite Γ(S, (⊤ : S.Opens))
      ((baseCechComplex π M U).homology 0) :=
    baseCechComplex_homology_zero_module_finite_of_orderedBaseCechComplex
      π M U
  letI := baseSectionsHZeroModule π M
  exact Module.Finite.equiv
    (nativeBaseCechHZeroLinearEquivCanonicalOfOpenCover π M U hU)

/-- Coherent closed-support comodels give finite generation of genuine sheaf
`H⁰` with its canonical base action.  This is the degree-zero endpoint of
the checked support codévissage boundary. -/
theorem hZero_finite_of_coherentSupportComodels
    {X S : Scheme.{u}} (π : X ⟶ S)
    [X.IsSeparated] [NoetherianSpace X]
    [IsNoetherianRing Γ(S, (⊤ : S.Opens))]
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (hcomodel : ∀ (N : X.Modules),
      N.IsFiniteType → N.IsQuasicoherent →
        ∃ (E : X.Modules) (f : N ⟶ E),
          IsCoherentLowDegreeSupportComodel π U N E f)
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent] :
    letI := baseSectionsHZeroModule π M
    Module.Finite Γ(S, (⊤ : S.Opens)) (H M 0) := by
  let hlow := orderedBaseCechLowDegreeFinite_of_coherentSupportComodels
    π U hUaff hcomodel M
  letI : Module.Finite Γ(S, (⊤ : S.Opens))
      ((orderedBaseCechComplex π M U).homology 0) := hlow.1
  exact hZero_finite_of_orderedBaseCechComplex π M U hU

end MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

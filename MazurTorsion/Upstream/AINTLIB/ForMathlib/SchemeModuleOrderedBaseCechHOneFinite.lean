/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleOrderedBaseCechHOne

/-!
# Degree-one finiteness from ordered to native Cech complexes

Alternating extension from the ordered Cech complex surjects on degree-one
homology. Thus finite generation of ordered Cech homology transfers to the
native all-tuples Cech complex in degree one.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Alternating extension from the ordered Cech complex is surjective on
degree-one homology. -/
theorem orderedToBaseCechAlternating_homologyMap_surjective
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) :
    Function.Surjective
      (HomologicalComplex.homologyMap
        (orderedToBaseCechAlternating π M U) 1).hom := by
  let B := baseCechComplex π M U
  let O := orderedBaseCechComplex π M U
  let p := baseCechToOrdered π M U
  let s := orderedToBaseCechAlternating π M U
  intro ξ
  have hπ : Function.Surjective (B.homologyπ 1).hom :=
    (ModuleCat.epi_iff_surjective (B.homologyπ 1)).mp inferInstance
  obtain ⟨xc, rfl⟩ := hπ ξ
  let yc := HomologicalComplex.cyclesMap p 1 |>.hom xc
  refine ⟨(O.homologyπ 1).hom yc, ?_⟩
  have hnat := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (φ := s) (i := 1)) yc
  simp only [ConcreteCategory.comp_apply] at hnat
  rw [hnat]
  have hcycles : (HomologicalComplex.cyclesMap s 1).hom yc = xc := by
    apply (ModuleCat.mono_iff_injective (B.iCycles 1)).mp inferInstance
    have hsi := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (φ := s) (i := 1)) yc
    have hpi := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (φ := p) (i := 1)) xc
    simp only [ConcreteCategory.comp_apply] at hsi hpi
    rw [hsi, hpi]
    have hx :
        ((B.d 1 2).hom ((B.iCycles 1).hom xc)) = 0 := by
      rw [← ConcreteCategory.comp_apply, B.iCycles_d]
      rfl
    exact baseCechDegreeOneCocycle_alternating π M U
      ((B.iCycles 1).hom xc) hx
  exact congrArg (B.homologyπ 1).hom hcycles

/-- Finite generation of ordered Cech homology implies finite generation of
native all-tuples Cech homology in degree one. -/
theorem baseCechComplex_homology_one_module_finite_of_orderedBaseCechComplex
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    [Module.Finite Γ(S, (⊤ : S.Opens))
      ((orderedBaseCechComplex π M U).homology 1)] :
    Module.Finite Γ(S, (⊤ : S.Opens))
      ((baseCechComplex π M U).homology 1) := by
  let f := HomologicalComplex.homologyMap
    (orderedToBaseCechAlternating π M U) 1
  have hf : Function.Surjective f.hom :=
    orderedToBaseCechAlternating_homologyMap_surjective π M U
  exact Module.Finite.of_surjective f.hom hf

end AlgebraicGeometry.Scheme.Modules

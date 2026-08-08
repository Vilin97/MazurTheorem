/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleOrderedBaseCechAlternating

/-!
# Finiteness along the ordered Cech retract

The ordered Cech complex is a retract of the native all-tuples Cech complex.
Consequently, finite generation of native Cech homology descends to ordered
Cech homology in every degree.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Finite native base-Cech homology descends to ordered base-Cech homology. -/
theorem orderedBaseCechComplex_homology_module_finite_of_baseCechComplex
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (n : ℕ)
    [Module.Finite Γ(S, (⊤ : S.Opens))
      ((baseCechComplex π M U).homology n)] :
    Module.Finite Γ(S, (⊤ : S.Opens))
      ((orderedBaseCechComplex π M U).homology n) := by
  let p := baseCechToOrdered π M U
  let s := orderedToBaseCechAlternating π M U
  have hsp :
      HomologicalComplex.homologyMap s n ≫
          HomologicalComplex.homologyMap p n =
        𝟙 ((orderedBaseCechComplex π M U).homology n) := by
    rw [← HomologicalComplex.homologyMap_comp]
    change HomologicalComplex.homologyMap
        (orderedToBaseCechAlternating π M U ≫
          baseCechToOrdered π M U) n = _
    rw [orderedToBaseCechAlternating_comp_baseCechToOrdered]
    exact HomologicalComplex.homologyMap_id _ n
  letI : Epi (HomologicalComplex.homologyMap p n) :=
    (SplitEpi.mk (HomologicalComplex.homologyMap s n) hsp).epi
  exact Module.Finite.of_surjective
    (HomologicalComplex.homologyMap p n).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

end AlgebraicGeometry.Scheme.Modules

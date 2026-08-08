/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleOrderedBaseCechHOneFinite
import MazurTorsion.Upstream.SchemeModuleBaseCechHOneModule
import MazurTorsion.Upstream.SchemeModuleOrderedBaseCechLowDegreeSupport

/-!
# Finite generation of native base-Cech degree-one homology

This is the project-facing consumer of the option-free ordered/native Cech
comparison port. It accepts finite generation of the degree-one homology of
the ordered Cech complex for a linearly ordered cover and concludes finite
generation for the native all-tuples base-linear Cech complex.

It also consumes the affine-cover comparison to equip genuine sheaf `H¹` with
the transported global-functions action and transfer finite generation to
that module. It does not establish the ordered input from properness.
-/

noncomputable section

universe u

open _root_.AlgebraicGeometry CategoryTheory TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules

namespace MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

/-- Finite generation of ordered degree-one base-Cech homology transfers to
native all-tuples degree-one base-Cech homology. -/
theorem nativeBaseCechHOne_finite_of_ordered
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (hordered : Module.Finite Γ(S, (⊤ : S.Opens))
      ((Scheme.Modules.orderedBaseCechComplex π M U).homology 1)) :
    Module.Finite Γ(S, (⊤ : S.Opens))
      ((Scheme.Modules.baseCechComplex π M U).homology 1) := by
  letI := hordered
  exact
    baseCechComplex_homology_one_module_finite_of_orderedBaseCechComplex
      π M U

/-- Finite generation of ordered degree-one Cech homology transfers to
genuine Ext-based sheaf `H¹`, equipped with the explicit global-functions
action transported through the affine-cover comparison. -/
theorem genuineSheafHOne_finite_of_ordered_affineOpenCover
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    [M.IsQuasicoherent] {ι : Type u} [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i))
    (hordered : Module.Finite Γ(S, (⊤ : S.Opens))
      ((Scheme.Modules.orderedBaseCechComplex π M U).homology 1)) :
    letI := genuineSheafHOneBaseModule_of_affineOpenCover
      π M U hU hUaff
    Module.Finite Γ(S, (⊤ : S.Opens)) (GenuineSheafHOne M) := by
  letI : Module.Finite Γ(S, (⊤ : S.Opens))
      ((Scheme.Modules.baseCechComplex π M U).homology 1) :=
    nativeBaseCechHOne_finite_of_ordered π M U hordered
  letI := genuineSheafHOneBaseModule_of_affineOpenCover
    π M U hU hUaff
  exact Module.Finite.equiv
    (genuineSheafHOneLinearEquivNativeBaseCech_of_affineOpenCover
      π M U hU hUaff).symm

/-- A coherent support-decreasing comodel construction supplies finite
generation of genuine sheaf `H¹` through low-degree support induction, the
ordered/native comparison, and the explicit transported base action. -/
theorem genuineSheafHOne_finite_of_coherentSupportComodels
    {X S : Scheme.{u}} (π : X ⟶ S)
    [X.IsSeparated] [NoetherianSpace X]
    [IsNoetherianRing Γ(S, (⊤ : S.Opens))]
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent]
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (hcomodel : ∀ (N : X.Modules),
      N.IsFiniteType → N.IsQuasicoherent →
        ∃ (E : X.Modules) (f : N ⟶ E),
          IsCoherentLowDegreeSupportComodel π U N E f) :
    letI := genuineSheafHOneBaseModule_of_affineOpenCover
      π M U hU hUaff
    Module.Finite Γ(S, (⊤ : S.Opens)) (GenuineSheafHOne M) := by
  have hordered : Module.Finite Γ(S, (⊤ : S.Opens))
      ((Scheme.Modules.orderedBaseCechComplex π M U).homology 1) :=
    orderedBaseCechHOne_finite_of_coherentSupportComodels
      π U hUaff hcomodel M
  exact genuineSheafHOne_finite_of_ordered_affineOpenCover
    π M U hU hUaff hordered

end MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleOrderedBaseCechHOneFinite

/-!
# Finite generation of native base-Cech degree-one homology

This is the project-facing consumer of the option-free ordered/native Cech
comparison port. It accepts finite generation of the degree-one homology of
the ordered Cech complex for a linearly ordered cover and concludes finite
generation for the native all-tuples base-linear Cech complex.

It does not assert properness or identify Cech homology with derived
cohomology. Those are later comparison seams.
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

end MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

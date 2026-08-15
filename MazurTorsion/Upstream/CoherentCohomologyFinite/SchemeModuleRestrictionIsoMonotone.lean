/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Restrict

/-!
# Monotonicity of open-local module isomorphisms

An isomorphism of scheme modules over an open remains an isomorphism
after shrinking that open.  The proof uses the canonical comparison
between restriction along a composite and iterated restriction.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}}

/-- An isomorphism after restriction to `V` remains one on `W ≤ V`. -/
theorem isIso_restrict_map_of_le
    {M N : X.Modules} (α : M ⟶ N)
    {W V : X.Opens} (hWV : W ≤ V)
    [IsIso ((restrictFunctor V.ι).map α)] :
    IsIso ((restrictFunctor W.ι).map α) := by
  let j : (W : Scheme.{u}) ⟶ V :=
    X.homOfLE hWV
  let e :
      restrictFunctor W.ι ≅
        restrictFunctor V.ι ⋙ restrictFunctor j :=
    restrictFunctorCongr
        (Scheme.homOfLE_ι X hWV).symm ≪≫
      restrictFunctorComp j V.ι
  haveI :
      IsIso
        ((restrictFunctor V.ι ⋙
          restrictFunctor j).map α) := by
    change
      IsIso
        ((restrictFunctor j).map
          ((restrictFunctor V.ι).map α))
    infer_instance
  exact (NatIso.isIso_map_iff e α).mpr inferInstance

end AlgebraicGeometry.Scheme.Modules

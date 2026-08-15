/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ModuleSupport

/-!
# Strict support drop detected on an open subscheme

For a finite-type quasicoherent module, the closed stalk support is its
actual nonzero-stalk locus.  Consequently, if a coherent residual module
vanishes after restriction to an open subscheme, then every support point
of the ambient module lying in that open witnesses a strict support drop.

This is the topological part of the Noetherian codévissage used with a
projective modification.
-/


open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {U X : Scheme.{u}}

/--
A finite-type quasicoherent module which vanishes on an open subscheme has
no closed-support point in the image of that open subscheme.
-/
theorem not_mem_closedStalkSupport_of_isZero_restrict
    (j : U ⟶ X) [IsOpenImmersion j]
    (K : X.Modules) [K.IsFiniteType] [K.IsQuasicoherent]
    (hK : IsZero (K.restrict j))
    (x : U) :
    j x ∉ closedStalkSupport K := by
  change j x ∉ (closedStalkSupport K : Set X)
  rw [show (closedStalkSupport K : Set X) = stalkSupport K from
    coe_closedStalkSupport_eq_stalkSupport K]
  intro hx
  have hx' : x ∈ j ⁻¹' stalkSupport K := hx
  rw [preimage_stalkSupport_of_openImmersion j K] at hx'
  exact hx' ((underlyingStalkFunctor x).map_isZero hK)

/--
If the support of `K` is contained in the support of `M`, `K` vanishes on
an open subscheme, and that open meets the support of `M`, then the support
of `K` is strictly smaller.
-/
theorem closedStalkSupport_lt_of_le_of_isZero_restrict
    (j : U ⟶ X) [IsOpenImmersion j]
    (K M : X.Modules)
    [K.IsFiniteType] [K.IsQuasicoherent]
    (hKM : closedStalkSupport K ≤ closedStalkSupport M)
    (hK : IsZero (K.restrict j))
    (x : U)
    (hxM : j x ∈ closedStalkSupport M) :
    closedStalkSupport K < closedStalkSupport M := by
  apply lt_of_le_of_ne hKM
  intro hEq
  apply not_mem_closedStalkSupport_of_isZero_restrict j K hK x
  rw [hEq]
  exact hxM

end AlgebraicGeometry.Scheme.Modules

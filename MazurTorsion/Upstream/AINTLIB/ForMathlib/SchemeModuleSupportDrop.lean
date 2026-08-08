/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

Adapted from the Apache-licensed `SchemeModuleSupportComplement.lean` and
`OpenRestrictionSupportDrop.lean` in Vilin97/Clawristotle.
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleSupport

/-!
# Strict support decrease on an open subscheme

A finite-type quasicoherent module vanishes on the open complement of its
closed stalk support. More generally, vanishing on an open meeting a larger
support turns support containment into strict containment.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {U X : Scheme.{u}}

/-- The open complement of the closed stalk support of a scheme module. -/
def closedStalkSupportComplement (M : X.Modules) : X.Opens :=
  ⟨(closedStalkSupport M : Set X)ᶜ,
    (closedStalkSupport M).2.isOpen_compl⟩

/-- A finite-type quasicoherent module vanishes away from its closed stalk support. -/
theorem isZero_restrict_closedStalkSupportComplement
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent] :
    IsZero (M.restrict (closedStalkSupportComplement M).ι) := by
  apply isZero_of_forall_underlyingStalk_isZero
  intro x
  let e :=
    (restrictStalkNatIso (closedStalkSupportComplement M).ι x).app M
  apply e.isZero_iff.mpr
  by_contra hx
  have hxSupport :
      (closedStalkSupportComplement M).ι x ∈ stalkSupport M :=
    hx
  have hxClosed :
      (closedStalkSupportComplement M).ι x ∈
        (closedStalkSupport M : Set X) := by
    rw [coe_closedStalkSupport_eq_stalkSupport M]
    exact hxSupport
  exact x.property hxClosed

/-- A module vanishing on an open has no support point in the image of that open. -/
theorem not_mem_closedStalkSupport_of_isZero_restrict
    (j : U ⟶ X) [IsOpenImmersion j]
    (K : X.Modules) [K.IsFiniteType] [K.IsQuasicoherent]
    (hK : IsZero (K.restrict j)) (x : U) :
    j x ∉ closedStalkSupport K := by
  change j x ∉ (closedStalkSupport K : Set X)
  rw [coe_closedStalkSupport_eq_stalkSupport K]
  intro hx
  have hx' : x ∈ j ⁻¹' stalkSupport K := hx
  rw [preimage_stalkSupport_of_openImmersion j K] at hx'
  exact hx' ((underlyingStalkFunctor x).map_isZero hK)

/-- Support containment is strict if the smaller module vanishes on an open
containing a support point of the larger module. -/
theorem closedStalkSupport_lt_of_le_of_isZero_restrict
    (j : U ⟶ X) [IsOpenImmersion j]
    (K M : X.Modules) [K.IsFiniteType] [K.IsQuasicoherent]
    (hKM : closedStalkSupport K ≤ closedStalkSupport M)
    (hK : IsZero (K.restrict j))
    (x : U) (hxM : j x ∈ closedStalkSupport M) :
    closedStalkSupport K < closedStalkSupport M := by
  apply lt_of_le_of_ne hKM
  intro hEq
  apply not_mem_closedStalkSupport_of_isZero_restrict j K hK x
  rw [hEq]
  exact hxM

end AlgebraicGeometry.Scheme.Modules

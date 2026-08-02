/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Principal.Basic
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Order

/-!
# Finite support of scheme-theoretic orders

This is the global finiteness input needed to package Tau Ceti's existing
local order maps as a principal-divisor order system. The proof is checked
against the exact Tau Ceti pin; the contract remains upstream-facing until
the theorem is installed at its permanent Tau Ceti destination.
-/

public section

open AlgebraicGeometry TopologicalSpace Order

namespace MazurTauCetiChallenge

universe u

/-- The codimension-one points outside a nonempty open of a Noetherian integral
scheme are the generic points of irreducible components of the closed complement. -/
private theorem codimensionOne_outside_open_finite
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (U : X.Opens) [Nonempty U] :
    {x : TauCeti.AlgebraicGeometry.CodimensionOnePoint X | (x : X) ∉ U}.Finite := by
  let Z : Set X := (U : Set X)ᶜ
  have hZ : IsClosed Z := U.isOpen.isClosed_compl
  letI : QuasiSober Z := hZ.isClosedEmbedding_subtypeVal.quasiSober
  have hgp : (genericPoints Z).Finite :=
    genericPoints.finite NoetherianSpace.finite_irreducibleComponents
  rw [← Set.finite_coe_iff]
  let toGeneric :
      {x : TauCeti.AlgebraicGeometry.CodimensionOnePoint X | (x : X) ∉ U} → genericPoints Z :=
    fun x ↦ ⟨⟨x.1.1, x.2⟩, by
      rw [genericPoints]
      refine ⟨isIrreducible_singleton.closure, ?_⟩
      intro T hT hsub
      let p : Z := hT.genericPoint
      have hpGeneric : IsGenericPoint p (closure T) :=
        hT.isGenericPoint_genericPoint_closure
      have hxT : (⟨x.1.1, x.2⟩ : Z) ∈ T :=
        hsub (subset_closure (Set.mem_singleton _))
      have hpx : p ⤳ (⟨x.1.1, x.2⟩ : Z) :=
        hpGeneric.specializes (subset_closure hxT)
      have hxp : x.1.1 ≤ (p : X) := by
        rw [Scheme.le_iff_specializes]
        exact (subtype_specializes_iff p (⟨x.1.1, x.2⟩ : Z)).mp hpx
      letI : PartialOrder X := specializationOrder X
      have hp_eq_x : (p : X) = x.1.1 := by
        apply le_antisymm
        · by_contra hp_not_le
          have hxp_strict : x.1.1 < (p : X) := lt_of_le_not_ge hxp hp_not_le
          have hp_coheight_lt : coheight (p : X) < 1 :=
            (Order.coheight_eq_coe_iff.mp x.1.2).2.2 (p : X) hxp_strict
          have hp_coheight_zero : coheight (p : X) = 0 := by
            exact nonpos_iff_eq_zero.mp (by simpa using hp_coheight_lt)
          have hp_top : (p : X) = ⊤ :=
            (Order.coheight_eq_zero.mp hp_coheight_zero).eq_top
          have htopU : (⊤ : X) ∈ U := by
            change genericPoint X ∈ U
            exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
              (by simpa using (‹Nonempty U› : Nonempty U))
          exact p.2 (hp_top.symm ▸ htopU)
        · exact hxp
      intro y hy
      have hpy : p ⤳ y := hpGeneric.specializes (subset_closure hy)
      have hp_eq_z : p = (⟨x.1.1, x.2⟩ : Z) := Subtype.ext hp_eq_x
      rw [hp_eq_z] at hpy
      exact specializes_iff_mem_closure.mp hpy⟩
  exact @Finite.of_injective _ _ (Set.finite_coe_iff.mpr hgp) toGeneric (by
    intro x y hxy
    exact Subtype.ext (Subtype.ext (congrArg (fun z ↦ (z.1 : X)) hxy)))

/-- A nonzero rational function on a Noetherian integral scheme has
nonzero order at only finitely many codimension-one points. -/
theorem finite_support_orderAt
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (g : Additive X.functionFieldˣ) :
    (Function.support fun x : TauCeti.AlgebraicGeometry.CodimensionOnePoint X =>
      TauCeti.AlgebraicGeometry.SchemeWeilDivisor.orderAt x g).Finite := by
  let f : X.functionField := (Additive.toMul g : X.functionFieldˣ)
  have hf : f ≠ 0 := Units.ne_zero _
  obtain ⟨U, _, f', hU, hrepr, hf'⟩ := exists_isUnit_germ_eq X f hf
  letI : Nonempty U := hU
  refine (codimensionOne_outside_open_finite X U).subset ?_
  intro x hx
  change (x : X) ∉ U
  intro hxU
  apply hx
  change TauCeti.AlgebraicGeometry.SchemeWeilDivisor.orderAt x g = 0
  rw [TauCeti.AlgebraicGeometry.SchemeWeilDivisor.orderAt_apply]
  change X.ord f x = 0
  rw [← hrepr]
  exact X.ord_of_isUnit hf' hxU

/-- The order system unlocked by `finite_support_orderAt`. This definition is
an acceptance consumer for the challenge theorem. -/
noncomputable def orderSystem
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X] :
    TauCeti.AlgebraicGeometry.WeilDivisor.OrderSystem
      (TauCeti.AlgebraicGeometry.CodimensionOnePoint X)
      (Additive X.functionFieldˣ) where
  ord := TauCeti.AlgebraicGeometry.SchemeWeilDivisor.orderAt
  finite_support := finite_support_orderAt X

end MazurTauCetiChallenge

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.EllipticCurve.IntegerPrimeSpecialization
import MazurTorsion.EllipticCurve.TameAdditiveFiltration
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Canonical quotient data for tame additive reduction

The abstract tame-additive filtration only needs two finite targets and a torsion-free formal
kernel.  For a Néron fibre, however, the component map is not arbitrary: its kernel is the
identity subgroup and its target is the quotient by that subgroup.  This file records that more
geometric handoff and constructs the existing algebraic filtration from it.

The formal kernel is also not accepted with an unrelated torsion-freeness hypothesis.  At the
unramified primes five and eleven, the specializations below discharge torsion-freeness using the
exact-pinned formal-group filtration theorem.  What remains explicit is precisely the Néron
geometry: the identity subgroup, its reduction map, identification of its kernel with the formal
filtration, and the order-at-most-four component bound.  Finiteness of the component quotient is
derived from the exact-pin theorem that the formal filtration already has finite index.
-/

noncomputable section

namespace MazurTorsion.EllipticCurve

universe u

/-- The geometric data between local points and the group-theoretic tame-additive filtration.

`identitySubgroup` models the points reducing to the identity component.  The component group is
not a supplied type: it is canonically `G ⧸ identitySubgroup`.  Likewise, the formal kernel is a
fixed subgroup of `G`, required to lie in the identity subgroup and to be exactly the kernel of
`identityReduction` there. -/
structure TameAdditiveReductionData
    (G : Type u) [AddCommGroup G] (formalKernel : AddSubgroup G) where
  identitySubgroup : AddSubgroup G
  formalKernel_le_identity : formalKernel ≤ identitySubgroup
  ResidueAdditive : Type u
  [residueAddCommGroup : AddCommGroup ResidueAdditive]
  [residueFinite : Finite ResidueAdditive]
  identityReduction : identitySubgroup →+ ResidueAdditive
  identityReduction_ker :
    identityReduction.ker = formalKernel.comap identitySubgroup.subtype
  [componentFinite : Finite (G ⧸ identitySubgroup)]
  component_card_le_four : Nat.card (G ⧸ identitySubgroup) ≤ 4

namespace TameAdditiveReductionData

variable {G : Type u} [AddCommGroup G] {formalKernel : AddSubgroup G}

/-- The actual component homomorphism to the quotient by the identity subgroup. -/
def component (D : TameAdditiveReductionData G formalKernel) :
    G →+ G ⧸ D.identitySubgroup :=
  QuotientAddGroup.mk' D.identitySubgroup

@[simp]
theorem component_ker (D : TameAdditiveReductionData G formalKernel) :
    D.component.ker = D.identitySubgroup :=
  QuotientAddGroup.ker_mk' D.identitySubgroup

/-- The kernel of the canonical component map is additively equivalent to the specified
identity subgroup.  Both sides have the same underlying points; the equivalence only transports
the checked kernel equality. -/
def identityKernelAddEquiv (D : TameAdditiveReductionData G formalKernel) :
    D.component.ker ≃+ D.identitySubgroup where
  toFun x := ⟨x, by
    simpa only [component_ker] using x.property⟩
  invFun x := ⟨x, by
    simpa only [component_ker] using x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Reduction on the kernel of the canonical component map. -/
def identityReductionOnComponentKernel
    (D : TameAdditiveReductionData G formalKernel) :=
  letI := D.residueAddCommGroup
  D.identityReduction.comp D.identityKernelAddEquiv.toAddMonoidHom

/-- The formal subgroup inside the kernel of the canonical component map.  It is definitionally
the kernel of identity-component reduction, while `identityReduction_ker` identifies its
underlying local points with the prescribed formal filtration. -/
def formalKernelOnComponentKernel
    (D : TameAdditiveReductionData G formalKernel) :
    AddSubgroup D.component.ker := by
  letI := D.residueAddCommGroup
  exact (D.identityReductionOnComponentKernel).ker

theorem formalKernelOnComponentKernel_coe_mem
    (D : TameAdditiveReductionData G formalKernel)
    (Q : D.formalKernelOnComponentKernel) :
    (((Q : D.component.ker) : G)) ∈ formalKernel := by
  letI := D.residueAddCommGroup
  have hQ : D.identityReduction
      (D.identityKernelAddEquiv (Q : D.component.ker)) = 0 := by
    change D.identityReductionOnComponentKernel (Q : D.component.ker) = 0
    exact Q.property
  change D.identityKernelAddEquiv (Q : D.component.ker) ∈
    D.identityReduction.ker at hQ
  rw [D.identityReduction_ker] at hQ
  exact hQ

/-- The prescribed formal subgroup is exactly the formal subgroup appearing inside the kernel
of the canonical component map.  This equivalence uses
`formalKernel_le_identity`; it is not merely the intersection of two unrelated subgroups. -/
def formalKernelAddEquiv (D : TameAdditiveReductionData G formalKernel) :
    formalKernel ≃+ D.formalKernelOnComponentKernel := by
  letI := D.residueAddCommGroup
  exact
    { toFun := fun P ↦ by
        let P₀ : D.identitySubgroup := ⟨P, D.formalKernel_le_identity P.property⟩
        let P₁ : D.component.ker := D.identityKernelAddEquiv.symm P₀
        refine ⟨P₁, ?_⟩
        change D.identityReductionOnComponentKernel P₁ = 0
        change D.identityReduction P₀ = 0
        have hP₀ : P₀ ∈ formalKernel.comap D.identitySubgroup.subtype := P.property
        rw [← D.identityReduction_ker] at hP₀
        exact hP₀
      invFun := fun Q ↦ ⟨((Q : D.component.ker) : G),
        D.formalKernelOnComponentKernel_coe_mem Q⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }

/-- Construct the algebraic tame-additive filtration from the canonical quotient data and a
torsion-freeness theorem for the prescribed formal subgroup. -/
def toTameAdditiveFiltrationData
    (D : TameAdditiveReductionData G formalKernel)
    (hformal : ∀ Q : formalKernel, IsOfFinAddOrder Q → Q = 0) :
    TameAdditiveFiltrationData G := by
  letI := D.residueAddCommGroup
  letI := D.residueFinite
  letI := D.componentFinite
  exact
    { Component := G ⧸ D.identitySubgroup
      componentAddCommGroup := inferInstance
      componentFinite := D.componentFinite
      ResidueAdditive := D.ResidueAdditive
      residueAddCommGroup := D.residueAddCommGroup
      residueFinite := D.residueFinite
      component := D.component
      identityReduction := D.identityReductionOnComponentKernel
      formalKernel := D.formalKernelOnComponentKernel
      identityReduction_ker := rfl
      component_card_le_four := D.component_card_le_four
      formalKernel_torsionFree := by
        intro Q hQ
        have hP : IsOfFinAddOrder (D.formalKernelAddEquiv.symm Q) :=
          D.formalKernelAddEquiv.symm.toAddMonoidHom.isOfFinAddOrder hQ
        have hPzero := hformal (D.formalKernelAddEquiv.symm Q) hP
        apply D.formalKernelAddEquiv.symm.injective
        simpa only [map_zero] using hPzero }

open MazurTorsion.IntegerPrimeSpecialization
open WeierstrassCurve WeierstrassCurve.Affine

/-- At five, the exact-pinned unramified formal-kernel theorem supplies the only
torsion-freeness input needed by the canonical reduction data. -/
def toTameAdditiveFiltrationDataAtFive
    {W : Affine (atFive.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atFive.adicCompletionIntegers ℚ)}
    (hW : W₀.map
      (algebraMap (atFive.adicCompletionIntegers ℚ) (atFive.adicCompletion ℚ)) = W)
    [W.IsElliptic] [DecidableEq (atFive.adicCompletion ℚ)]
    (D : TameAdditiveReductionData W.Point (filtration hW 0)) :
    TameAdditiveFiltrationData W.Point :=
  D.toTameAdditiveFiltrationData fun Q hQ ↦ by
    apply Subtype.ext
    exact torsion_eq_zero_of_mem_formalKernel_atFive hW Q.property
      ((filtration hW 0).subtype.isOfFinAddOrder hQ)

/-- The same canonical conversion at eleven, used by the squarefree-level order-35 route. -/
def toTameAdditiveFiltrationDataAtEleven
    {W : Affine (atEleven.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atEleven.adicCompletionIntegers ℚ)}
    (hW : W₀.map
      (algebraMap (atEleven.adicCompletionIntegers ℚ) (atEleven.adicCompletion ℚ)) = W)
    [W.IsElliptic] [DecidableEq (atEleven.adicCompletion ℚ)]
    (D : TameAdditiveReductionData W.Point (filtration hW 0)) :
    TameAdditiveFiltrationData W.Point :=
  D.toTameAdditiveFiltrationData fun Q hQ ↦ by
    apply Subtype.ext
    exact torsion_eq_zero_of_mem_formalKernel_atEleven hW Q.property
      ((filtration hW 0).subtype.isOfFinAddOrder hQ)

end TameAdditiveReductionData

open MazurTorsion.IntegerPrimeSpecialization
open WeierstrassCurve WeierstrassCurve.Affine
open IsLocalRing

/-- The five-adic geometric handoff with the reduction target fixed to the actual additive
residue field.  Thus the target is no longer an arbitrary finite group of cardinality five.
A Néron-model consumer must construct the identity subgroup and the displayed reduction
homomorphism, and prove that its kernel is the exact-pinned formal filtration.  Surjectivity onto
the residue field is not required by the downstream torsion contradiction. -/
structure TameAdditiveReductionDataAtFive
    {W : Affine (atFive.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atFive.adicCompletionIntegers ℚ)}
    (hW : W₀.map
      (algebraMap (atFive.adicCompletionIntegers ℚ) (atFive.adicCompletion ℚ)) = W)
    [W.IsElliptic] [DecidableEq (atFive.adicCompletion ℚ)] where
  identitySubgroup : AddSubgroup W.Point
  formalKernel_le_identity : filtration hW 0 ≤ identitySubgroup
  identityReduction : identitySubgroup →+
    ResidueField (atFive.adicCompletionIntegers ℚ)
  identityReduction_ker :
    identityReduction.ker = (filtration hW 0).comap identitySubgroup.subtype
  component_card_le_four : Nat.card (W.Point ⧸ identitySubgroup) ≤ 4

namespace TameAdditiveReductionDataAtFive

variable {W : Affine (atFive.adicCompletion ℚ)}
  {W₀ : WeierstrassCurve (atFive.adicCompletionIntegers ℚ)}
  {hW : W₀.map
    (algebraMap (atFive.adicCompletionIntegers ℚ) (atFive.adicCompletion ℚ)) = W}
  [W.IsElliptic] [DecidableEq (atFive.adicCompletion ℚ)]

private def residueEquivZMod :
    ResidueField (atFive.adicCompletionIntegers ℚ) ≃ ZMod 5 :=
  ((atFive.residueFieldEquivAdicCompletionIntegers (K := ℚ)).symm.trans
    residueFiveAlgEquiv.toRingEquiv).toEquiv

omit [DecidableEq (atFive.adicCompletion ℚ)] in
/-- The additive residue group in the five-adic geometric data has exactly five elements. -/
theorem residue_natCard :
    Nat.card (ResidueField (atFive.adicCompletionIntegers ℚ)) = 5 := by
  rw [Nat.card_congr residueEquivZMod]
  norm_num

/-- Forget only the fact that the reduction target has been fixed to the actual additive residue
field.  The identity subgroup, canonical component quotient, reduction map, and formal-kernel
equality are retained literally. -/
def toReductionData (D : TameAdditiveReductionDataAtFive hW) :
    TameAdditiveReductionData W.Point (filtration hW 0) := by
  letI : Finite (ℤ ⧸ atFive.asIdeal) :=
    Finite.of_equiv (ZMod 5) residueFiveAlgEquiv.toEquiv.symm
  letI : Finite (ResidueField (atFive.adicCompletionIntegers ℚ)) :=
    Finite.of_equiv (ZMod 5) residueEquivZMod.symm
  letI : (filtration hW 0).FiniteIndex := filtration_zero_finiteIndex hW
  letI : D.identitySubgroup.FiniteIndex :=
    AddSubgroup.finiteIndex_of_le D.formalKernel_le_identity
  exact
    { identitySubgroup := D.identitySubgroup
      formalKernel_le_identity := D.formalKernel_le_identity
      ResidueAdditive := ResidueField (atFive.adicCompletionIntegers ℚ)
      identityReduction := D.identityReduction
      identityReduction_ker := D.identityReduction_ker
      componentFinite := AddSubgroup.finite_quotient_of_finiteIndex
      component_card_le_four := D.component_card_le_four }

/-- Construct the final algebraic filtration.  Formal-kernel torsion-freeness is discharged by
the checked unramified theorem, and residue cardinality is fixed by `residue_natCard`. -/
def toTameAdditiveFiltrationData (D : TameAdditiveReductionDataAtFive hW) :
    TameAdditiveFiltrationData W.Point :=
  D.toReductionData.toTameAdditiveFiltrationDataAtFive hW

end TameAdditiveReductionDataAtFive

/-- The analogous eleven-adic handoff used by the order-35 formal-immersion route. -/
structure TameAdditiveReductionDataAtEleven
    {W : Affine (atEleven.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atEleven.adicCompletionIntegers ℚ)}
    (hW : W₀.map
      (algebraMap (atEleven.adicCompletionIntegers ℚ) (atEleven.adicCompletion ℚ)) = W)
    [W.IsElliptic] [DecidableEq (atEleven.adicCompletion ℚ)] where
  identitySubgroup : AddSubgroup W.Point
  formalKernel_le_identity : filtration hW 0 ≤ identitySubgroup
  identityReduction : identitySubgroup →+
    ResidueField (atEleven.adicCompletionIntegers ℚ)
  identityReduction_ker :
    identityReduction.ker = (filtration hW 0).comap identitySubgroup.subtype
  component_card_le_four : Nat.card (W.Point ⧸ identitySubgroup) ≤ 4

namespace TameAdditiveReductionDataAtEleven

variable {W : Affine (atEleven.adicCompletion ℚ)}
  {W₀ : WeierstrassCurve (atEleven.adicCompletionIntegers ℚ)}
  {hW : W₀.map
    (algebraMap (atEleven.adicCompletionIntegers ℚ) (atEleven.adicCompletion ℚ)) = W}
  [W.IsElliptic] [DecidableEq (atEleven.adicCompletion ℚ)]

private def residueEquivZMod :
    ResidueField (atEleven.adicCompletionIntegers ℚ) ≃ ZMod 11 :=
  ((atEleven.residueFieldEquivAdicCompletionIntegers (K := ℚ)).symm.trans
    residueElevenAlgEquiv.toRingEquiv).toEquiv

omit [DecidableEq (atEleven.adicCompletion ℚ)] in
/-- The additive residue group in the eleven-adic geometric data has exactly eleven elements. -/
theorem residue_natCard :
    Nat.card (ResidueField (atEleven.adicCompletionIntegers ℚ)) = 11 := by
  rw [Nat.card_congr residueEquivZMod]
  norm_num

/-- Forget only the fixed eleven-adic reduction target, retaining the canonical component quotient,
reduction map, and exact formal-kernel equality. -/
def toReductionData (D : TameAdditiveReductionDataAtEleven hW) :
    TameAdditiveReductionData W.Point (filtration hW 0) := by
  letI : Finite (ℤ ⧸ atEleven.asIdeal) :=
    Finite.of_equiv (ZMod 11) residueElevenAlgEquiv.toEquiv.symm
  letI : Finite (ResidueField (atEleven.adicCompletionIntegers ℚ)) :=
    Finite.of_equiv (ZMod 11) residueEquivZMod.symm
  letI : (filtration hW 0).FiniteIndex := filtration_zero_finiteIndex hW
  letI : D.identitySubgroup.FiniteIndex :=
    AddSubgroup.finiteIndex_of_le D.formalKernel_le_identity
  exact
    { identitySubgroup := D.identitySubgroup
      formalKernel_le_identity := D.formalKernel_le_identity
      ResidueAdditive := ResidueField (atEleven.adicCompletionIntegers ℚ)
      identityReduction := D.identityReduction
      identityReduction_ker := D.identityReduction_ker
      componentFinite := AddSubgroup.finite_quotient_of_finiteIndex
      component_card_le_four := D.component_card_le_four }

/-- Construct the algebraic filtration using the checked exact-pinned theorem at eleven. -/
def toTameAdditiveFiltrationData (D : TameAdditiveReductionDataAtEleven hW) :
    TameAdditiveFiltrationData W.Point :=
  D.toReductionData.toTameAdditiveFiltrationDataAtEleven hW

end TameAdditiveReductionDataAtEleven

end MazurTorsion.EllipticCurve

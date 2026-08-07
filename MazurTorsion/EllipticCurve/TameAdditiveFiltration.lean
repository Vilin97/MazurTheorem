/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The group-theoretic filtration of a tame additive Néron fibre

This file isolates the exact algebra used after potentially good reduction
has been established. It does not construct a Néron model. The narrow marked
interface uses the actual quotient by a supplied identity subgroup and asks
only that the marked component class have order at most four; a geometric
consumer must prove that Tate--Kodaira statement for canonical nonsingular
reduction. The downstream local modules already identify the formal kernel,
classify the additive special fibre, and import its torsion-freeness theorem.
-/

namespace MazurTorsion.EllipticCurve

universe u v

/-- A homomorphism into a finite group kills a point of exact order `N` when
`N` is coprime to the target cardinality. -/
theorem map_eq_zero_of_addOrderOf_eq_of_coprime_card
    {G : Type u} [AddGroup G] {H : Type v} [AddGroup H] [Finite H]
    (f : G →+ H) {P : G} {N : ℕ}
    (horder : addOrderOf P = N) (hcoprime : N.Coprime (Nat.card H)) :
    f P = 0 := by
  have hdvdN : addOrderOf (f P) ∣ N := by
    rw [← horder]
    exact addOrderOf_map_dvd f P
  have hdvdCard : addOrderOf (f P) ∣ Nat.card H :=
    addOrderOf_dvd_natCard (f P)
  have hdvdGcd : addOrderOf (f P) ∣ Nat.gcd N (Nat.card H) :=
    Nat.dvd_gcd hdvdN hdvdCard
  have hone : addOrderOf (f P) = 1 := by
    apply Nat.dvd_one.mp
    simpa [hcoprime.gcd_eq_one] using hdvdGcd
  exact AddMonoid.addOrderOf_eq_one_iff.mp hone

/-- The marked-point part of the tame Kodaira component classification.

This predicate deliberately records the order of one point in the *actual* quotient by the
specified identity subgroup.  It is strictly narrower than finiteness or a cardinality bound for
the whole component quotient.  For a minimal elliptic equation with additive reduction in tame
residue characteristic, the missing geometric input is that this predicate holds with bound four
for the canonical nonsingular-reduction subgroup. -/
def MarkedComponentOrderAtMost
    {G : Type u} [AddCommGroup G]
    (identitySubgroup : AddSubgroup G) (bound : ℕ) (P : G) : Prop :=
  let component : G →+ G ⧸ identitySubgroup := QuotientAddGroup.mk' identitySubgroup
  IsOfFinAddOrder (component P) ∧ addOrderOf (component P) ≤ bound

/-- The marked component-order predicate is equivalent to a completely pointwise certificate:
some positive multiplier up to the bound sends the marked point into the identity subgroup.  This
is a useful target for a Tate-algorithm proof because it mentions neither finiteness nor the
cardinality of the ambient quotient. -/
theorem markedComponentOrderAtMost_iff_exists_nsmul_mem
    {G : Type u} [AddCommGroup G]
    (identitySubgroup : AddSubgroup G) (bound : ℕ) (P : G) :
    MarkedComponentOrderAtMost identitySubgroup bound P ↔
      ∃ n : ℕ, 0 < n ∧ n ≤ bound ∧ n • P ∈ identitySubgroup := by
  let component : G →+ G ⧸ identitySubgroup :=
    QuotientAddGroup.mk' identitySubgroup
  constructor
  · intro hP
    refine ⟨addOrderOf (component P), addOrderOf_pos_iff.mpr hP.1, hP.2, ?_⟩
    have hzero : addOrderOf (component P) • component P = 0 :=
      addOrderOf_nsmul_eq_zero (component P)
    rw [← component.map_nsmul] at hzero
    exact (QuotientAddGroup.eq_zero_iff _).mp hzero
  · rintro ⟨n, hn, hnle, hnmem⟩
    have hzero : n • component P = 0 := by
      rw [← component.map_nsmul]
      exact (QuotientAddGroup.eq_zero_iff _).mpr hnmem
    exact ⟨isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, hzero⟩,
      addOrderOf_le_of_nsmul_eq_zero hn hzero |>.trans hnle⟩

/-- A marked component class of finite order at most four is killed by the uniform tame exponent
`12`.  This is the exact group-theoretic passage from the pointwise Kodaira assertion to the
canonical identity subgroup; it does not construct or count the full component quotient. -/
theorem twelve_nsmul_mem_of_markedComponentOrderAtMostFour
    {G : Type u} [AddCommGroup G]
    (identitySubgroup : AddSubgroup G) (P : G)
    (hP : MarkedComponentOrderAtMost identitySubgroup 4 P) :
    12 • P ∈ identitySubgroup := by
  let component : G →+ G ⧸ identitySubgroup :=
    QuotientAddGroup.mk' identitySubgroup
  have hpositive : 0 < addOrderOf (component P) :=
    addOrderOf_pos_iff.mpr hP.1
  have hle : addOrderOf (component P) ≤ 4 := hP.2
  have hcases : addOrderOf (component P) = 1 ∨
      addOrderOf (component P) = 2 ∨
      addOrderOf (component P) = 3 ∨
      addOrderOf (component P) = 4 := by
    omega
  have hdiv : addOrderOf (component P) ∣ 12 := by
    rcases hcases with h | h | h | h <;> simp [h]
  have hzero : 12 • component P = 0 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mp hdiv
  rw [← component.map_nsmul] at hzero
  exact (QuotientAddGroup.eq_zero_iff (12 • P)).mp hzero

/-- A cardinality bound for the full component quotient implies the narrower marked-order
certificate.  This lemma is an explicit fallback for callers that already possess the stronger
Néron component theorem; the marked-point consumers do not otherwise require such a bound. -/
theorem markedComponentOrderAtMost_of_quotient_card_le
    {G : Type u} [AddCommGroup G]
    (identitySubgroup : AddSubgroup G)
    [Finite (G ⧸ identitySubgroup)]
    (bound : ℕ) (hcard : Nat.card (G ⧸ identitySubgroup) ≤ bound)
    (P : G) :
    MarkedComponentOrderAtMost identitySubgroup bound P := by
  let component : G →+ G ⧸ identitySubgroup :=
    QuotientAddGroup.mk' identitySubgroup
  exact ⟨isOfFinAddOrder_of_finite (component P),
    (addOrderOf_le_card (x := component P)).trans hcard⟩

/-- The traditional full component-cardinality bound therefore gives the uniform marked
exponent.  Keeping this bridge separate makes the extra strength of that fallback visible in
downstream theorem signatures. -/
theorem twelve_nsmul_mem_of_quotient_card_le_four
    {G : Type u} [AddCommGroup G]
    (identitySubgroup : AddSubgroup G)
    [Finite (G ⧸ identitySubgroup)]
    (hcard : Nat.card (G ⧸ identitySubgroup) ≤ 4)
    (P : G) :
    12 • P ∈ identitySubgroup :=
  twelve_nsmul_mem_of_markedComponentOrderAtMostFour identitySubgroup P
    (markedComponentOrderAtMost_of_quotient_card_le identitySubgroup 4 hcard P)

/-- A component-cardinality bound is stronger than the local torsion argument needs.  It is
enough to know that one integer coprime to the marked order sends the marked point into the
identity subgroup.  Reduction there, followed by the torsion-free formal kernel, then kills the
point.

For a tame additive elliptic fibre the uniform integer used downstream is `12`: it annihilates
every group of order at most four, including the order-three component cases.  Thus the geometric
handoff may prove the narrower statement `12 • P ∈ E₀` without constructing or counting the full
component quotient. -/
theorem point_eq_zero_of_coprime_component_exponent
    {G : Type u} [AddCommGroup G]
    (identitySubgroup : AddSubgroup G)
    {ResidueAdditive : Type v} [AddCommGroup ResidueAdditive]
    [Finite ResidueAdditive]
    (identityReduction : identitySubgroup →+ ResidueAdditive)
    (formalKernel : AddSubgroup identitySubgroup)
    (identityReduction_ker : identityReduction.ker = formalKernel)
    (formalKernel_torsionFree :
      ∀ Q : formalKernel, IsOfFinAddOrder Q → Q = 0)
    {componentExponent N : ℕ} {P : G}
    (hN : N ≠ 0)
    (hcomponentCoprime : N.Coprime componentExponent)
    (hresidueCoprime : N.Coprime (Nat.card ResidueAdditive))
    (hcomponentExponent : componentExponent • P ∈ identitySubgroup)
    (horder : addOrderOf P = N) :
    P = 0 := by
  let component : G →+ G ⧸ identitySubgroup :=
    QuotientAddGroup.mk' identitySubgroup
  have hcomponentN : addOrderOf (component P) ∣ N := by
    rw [← horder]
    exact addOrderOf_map_dvd component P
  have hcomponentExp : componentExponent • component P = 0 := by
    rw [← component.map_nsmul]
    exact (QuotientAddGroup.eq_zero_iff (componentExponent • P)).mpr hcomponentExponent
  have hcomponentDvd : addOrderOf (component P) ∣ componentExponent :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mpr hcomponentExp
  have hcomponentOne : addOrderOf (component P) = 1 := by
    apply Nat.dvd_one.mp
    rw [← hcomponentCoprime.gcd_eq_one]
    exact Nat.dvd_gcd hcomponentN hcomponentDvd
  have hcomponentZero : component P = 0 :=
    AddMonoid.addOrderOf_eq_one_iff.mp hcomponentOne
  have hPidentity : P ∈ identitySubgroup :=
    (QuotientAddGroup.eq_zero_iff P).mp hcomponentZero
  let P₀ : identitySubgroup := ⟨P, hPidentity⟩
  have hP₀order : addOrderOf P₀ = N := by
    rw [← AddSubgroup.addOrderOf_coe P₀]
    simpa [P₀] using horder
  have hresidueZero : identityReduction P₀ = 0 :=
    map_eq_zero_of_addOrderOf_eq_of_coprime_card
      identityReduction hP₀order hresidueCoprime
  have hP₀mem : P₀ ∈ formalKernel := by
    rw [← identityReduction_ker]
    exact hresidueZero
  let Q : formalKernel := ⟨P₀, hP₀mem⟩
  have hQorder : addOrderOf Q = N := by
    rw [← AddSubgroup.addOrderOf_coe Q]
    simpa [Q] using hP₀order
  have hQtorsion : IsOfFinAddOrder Q := addOrderOf_pos_iff.mp (by
    rw [hQorder]
    exact Nat.pos_of_ne_zero hN)
  have hQzero : Q = 0 := formalKernel_torsionFree Q hQtorsion
  have hP₀zero : P₀ = 0 := by
    have h := congrArg (fun x : formalKernel ↦ (x : identitySubgroup)) hQzero
    simpa [Q] using h
  have hPzero := congrArg (fun x : identitySubgroup ↦ (x : G)) hP₀zero
  simpa [P₀] using hPzero

/-- The algebraic data in the filtration of local points of an elliptic
curve with tame additive reduction. The component group is finite of size at
most four; the identity component maps to the additive residue group; and
the kernel of that map is the torsion-free formal kernel. -/
structure TameAdditiveFiltrationData (G : Type u) [AddCommGroup G] where
  Component : Type v
  [componentAddCommGroup : AddCommGroup Component]
  [componentFinite : Finite Component]
  ResidueAdditive : Type v
  [residueAddCommGroup : AddCommGroup ResidueAdditive]
  [residueFinite : Finite ResidueAdditive]
  component : G →+ Component
  identityReduction : component.ker →+ ResidueAdditive
  formalKernel : AddSubgroup component.ker
  identityReduction_ker : identityReduction.ker = formalKernel
  component_card_le_four : Nat.card Component ≤ 4
  formalKernel_torsionFree :
    ∀ Q : formalKernel, IsOfFinAddOrder Q → Q = 0

namespace TameAdditiveFiltrationData

variable {G : Type u} [AddCommGroup G]

/-- If an order is coprime to both finite quotients in the tame additive
filtration, a point of that exact order lies in the torsion-free formal
kernel and hence vanishes. -/
theorem point_eq_zero_of_coprime_card
    (F : TameAdditiveFiltrationData.{u, v} G)
    {P : G} {N : ℕ} (hN : N ≠ 0)
    (hcomponent : N.Coprime (Nat.card F.Component))
    (hresidue : N.Coprime (Nat.card F.ResidueAdditive))
    (horder : addOrderOf P = N) :
    P = 0 := by
  letI : AddCommGroup F.Component := F.componentAddCommGroup
  letI : Finite F.Component := F.componentFinite
  letI : AddCommGroup F.ResidueAdditive := F.residueAddCommGroup
  letI : Finite F.ResidueAdditive := F.residueFinite
  have hcomponentZero : F.component P = 0 :=
    map_eq_zero_of_addOrderOf_eq_of_coprime_card F.component horder hcomponent
  let P₀ : F.component.ker := ⟨P, hcomponentZero⟩
  have hP₀order : addOrderOf P₀ = N := by
    rw [← AddSubgroup.addOrderOf_coe P₀]
    simpa [P₀] using horder
  have hresidueZero : F.identityReduction P₀ = 0 :=
    map_eq_zero_of_addOrderOf_eq_of_coprime_card
      F.identityReduction hP₀order hresidue
  have hP₀mem : P₀ ∈ F.formalKernel := by
    rw [← F.identityReduction_ker]
    exact hresidueZero
  let Q : F.formalKernel := ⟨P₀, hP₀mem⟩
  have hQorder : addOrderOf Q = N := by
    rw [← AddSubgroup.addOrderOf_coe Q]
    simpa [Q] using hP₀order
  have hQtorsion : IsOfFinAddOrder Q := addOrderOf_pos_iff.mp (by
    rw [hQorder]
    exact Nat.pos_of_ne_zero hN)
  have hQzero : Q = 0 := F.formalKernel_torsionFree Q hQtorsion
  have hP₀zero : P₀ = 0 := by
    have h := congrArg (fun x : F.formalKernel ↦ (x : F.component.ker)) hQzero
    simpa [Q] using h
  have hPzero := congrArg (fun x : F.component.ker ↦ (x : G)) hP₀zero
  simpa [P₀] using hPzero

end TameAdditiveFiltrationData

end MazurTorsion.EllipticCurve

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderThirtyFiveFiniteFieldOrder
import MazurTorsion.EllipticCurve.TameAdditiveFiltration
import MazurTorsion.EllipticCurve.NonsingularReductionAdditive
import MazurTorsion.EllipticCurve.TateStarDepthFour
import MazurTorsion.PrimeOrder.TorsionSpecialization

/-!
# Rational points of order thirty-five

This module reserves the permanent library destination for the order-35
challenge. A solution belongs here; the published challenge module can then
become a thin, immutable bridge to that theorem.
-/

namespace MazurTorsion.OrderThirtyFive

universe u v

open WeierstrassCurve
open WeierstrassCurve.Affine
open MazurTorsion.IntegerPrimeSpecialization
open MazurTorsion.EllipticCurve

private instance : Fact (Nat.Prime 11) := ⟨by decide⟩

noncomputable local instance : DecidableEq
    (IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ)) :=
  Classical.decEq _

/-- The checked `F_11` enumeration rules out a specialized point of exact
order 35.  The remaining rational theorem must construct this point through
the squarefree-level formal-immersion and Néron-specialization route. -/
theorem reductionAtEleven_addOrderOf_ne_thirtyFive
    (W : WeierstrassCurve (ZMod 11)) [W.IsElliptic]
    (P : W.toAffine.Point) :
    addOrderOf P ≠ 35 :=
  zmod_eleven_addOrderOf_ne_thirtyFive W P

/-- If an integral model has good reduction at eleven, a rational point on
its generic fibre cannot have exact order 35.  This is the checked join
between unramified specialization and the exhaustive `F_11` certificate. -/
theorem rationalPoint_addOrderOf_ne_thirtyFive_of_goodReductionAtEleven
    {E : Affine ℚ} {W₀ : WeierstrassCurve ℤ}
    (hE : W₀.map (algebraMap ℤ ℚ) = E)
    [E.IsElliptic] [(redCurve atEleven W₀).IsElliptic]
    {P : E.Point} :
    addOrderOf P ≠ 35 := by
  intro horder
  have hP : IsOfFinAddOrder P := addOrderOf_pos_iff.mp (by
    rw [horder]
    norm_num)
  letI : (MazurTorsion.PrimeOrder.reductionCurveAtEleven W₀).IsElliptic :=
    MazurTorsion.PrimeOrder.reductionCurveAtEleven_isElliptic W₀
  apply reductionAtEleven_addOrderOf_ne_thirtyFive
    (MazurTorsion.PrimeOrder.reductionCurveAtEleven W₀)
    (MazurTorsion.PrimeOrder.reductionAtElevenToZMod hE P)
  exact
    (MazurTorsion.PrimeOrder.specializedPointZMod_addOrderOf_eq_atEleven_of_goodReduction
      hE hP).trans horder

/-- A tame additive filtration with eleven-element residue group has no
point of exact order 35. This is the local bad-fibre consumer that the future
Néron-model construction must instantiate. -/
theorem addOrderOf_ne_thirtyFive_of_tameAdditiveFiltrationAtEleven
    {G : Type u} [AddCommGroup G]
    (F : TameAdditiveFiltrationData.{u, v} G)
    (hresidue : Nat.card F.ResidueAdditive = 11)
    (P : G) :
    addOrderOf P ≠ 35 := by
  letI : AddCommGroup F.Component := F.componentAddCommGroup
  letI : Finite F.Component := F.componentFinite
  letI : AddCommGroup F.ResidueAdditive := F.residueAddCommGroup
  letI : Finite F.ResidueAdditive := F.residueFinite
  intro horder
  have hcomponentPos : 0 < Nat.card F.Component := Nat.card_pos
  have hcomponentLe : Nat.card F.Component ≤ 4 := F.component_card_le_four
  have hcomponentCoprime : (35 : ℕ).Coprime (Nat.card F.Component) := by
    have hc : Nat.card F.Component = 1 ∨ Nat.card F.Component = 2 ∨
        Nat.card F.Component = 3 ∨ Nat.card F.Component = 4 := by
      omega
    rcases hc with hc | hc | hc | hc <;> rw [hc] <;> norm_num
  have hresidueCoprime : (35 : ℕ).Coprime (Nat.card F.ResidueAdditive) := by
    rw [hresidue]
    norm_num
  have hzero := F.point_eq_zero_of_coprime_card (by norm_num)
    hcomponentCoprime hresidueCoprime horder
  rw [hzero] at horder
  norm_num at horder

/-- The order-35 additive contradiction through the narrower tame component-exponent handoff.
The universal exponent `12` is coprime to `35`, and the eleven-element additive residue group is
also coprime to `35`; no cardinality or finiteness of the full component quotient is used. -/
theorem addOrderOf_ne_thirtyFive_of_componentExponentTwelveAtEleven
    {G : Type u} [AddCommGroup G]
    (identitySubgroup : AddSubgroup G)
    {ResidueAdditive : Type v} [AddCommGroup ResidueAdditive]
    [Finite ResidueAdditive]
    (identityReduction : identitySubgroup →+ ResidueAdditive)
    (formalKernel : AddSubgroup identitySubgroup)
    (identityReduction_ker : identityReduction.ker = formalKernel)
    (formalKernel_torsionFree :
      ∀ Q : formalKernel, IsOfFinAddOrder Q → Q = 0)
    (hresidue : Nat.card ResidueAdditive = 11)
    (P : G) (hcomponent : 12 • P ∈ identitySubgroup) :
    addOrderOf P ≠ 35 := by
  intro horder
  have hzero := point_eq_zero_of_coprime_component_exponent
    identitySubgroup identityReduction formalKernel identityReduction_ker
    formalKernel_torsionFree (N := 35) (componentExponent := 12)
    (by norm_num) (by norm_num) (by rw [hresidue]; norm_num) hcomponent horder
  rw [hzero] at horder
  norm_num at horder

/-- The order-35 additive-fibre contradiction from the canonical eleven-adic reduction data.
The component is the quotient by the specified identity subgroup, reduction targets the actual
eleven-adic residue field, and formal-kernel torsion-freeness comes from the checked
unramified formal-group theorem. -/
theorem addOrderOf_ne_thirtyFive_of_tameAdditiveReductionDataAtEleven
    {W : Affine (atEleven.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atEleven.adicCompletionIntegers ℚ)}
    (hW : W₀.map
      (algebraMap (atEleven.adicCompletionIntegers ℚ)
        (atEleven.adicCompletion ℚ)) = W)
    [W.IsElliptic] [DecidableEq (atEleven.adicCompletion ℚ)]
    (D : TameAdditiveReductionDataAtEleven hW) (P : W.Point) :
    addOrderOf P ≠ 35 :=
  addOrderOf_ne_thirtyFive_of_tameAdditiveFiltrationAtEleven
    D.toTameAdditiveFiltrationData
    TameAdditiveReductionDataAtEleven.residue_natCard P

/-- The order-35 additive-fibre contradiction using only canonical coordinatewise nonsingular
reduction.  The identity subgroup and its reduction map are constructed, rather than supplied;
the group-law compatibility is checked, and the remaining inputs are the additive classification
of the actual special cubic and the genuine component bound. -/
theorem addOrderOf_ne_thirtyFive_of_nonsingularReductionAtEleven
    {W : Affine (atEleven.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atEleven.adicCompletionIntegers ℚ)}
    (hW : W₀.map
      (algebraMap (atEleven.adicCompletionIntegers ℚ)
        (atEleven.adicCompletion ℚ)) = W)
    [W.IsElliptic] [DecidableEq (atEleven.adicCompletion ℚ)]
    (especial : (adicRedCurve W₀).Point ≃+
      IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ))
    (hcomponent : Nat.card
      (W.Point ⧸ nonsingularReductionSubgroup hW
        (nonsingularReduction_isAdditive hW)) ≤ 4)
    (P : W.Point) :
    addOrderOf P ≠ 35 :=
  addOrderOf_ne_thirtyFive_of_tameAdditiveReductionDataAtEleven hW
    (TameAdditiveReductionDataAtEleven.ofCanonicalNonsingularReduction
      especial hcomponent) P

/-- The canonical eleven-adic additive contradiction through the component-exponent handoff.

This is the first geometric consumer of
`addOrderOf_ne_thirtyFive_of_componentExponentTwelveAtEleven`: coordinatewise nonsingular
reduction supplies the identity subgroup and reduction homomorphism, while the exact-pinned
formal-group theorem supplies torsion-freeness of its kernel.  The remaining component input is
only the marked-point assertion `12 • P ∈ E₀`; no component quotient or cardinality bound is
constructed. -/
theorem
    addOrderOf_ne_thirtyFive_of_nonsingularReduction_of_componentExponentTwelveAtEleven
    {W : Affine (atEleven.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atEleven.adicCompletionIntegers ℚ)}
    (hW : W₀.map
      (algebraMap (atEleven.adicCompletionIntegers ℚ)
        (atEleven.adicCompletion ℚ)) = W)
    [W.IsElliptic] [DecidableEq (atEleven.adicCompletion ℚ)]
    (especial : (adicRedCurve W₀).Point ≃+
      IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ))
    (P : W.Point)
    (hcomponent : 12 • P ∈
      nonsingularReductionSubgroup hW (nonsingularReduction_isAdditive hW)) :
    addOrderOf P ≠ 35 := by
  let residueEquivZMod :
      IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ) ≃ ZMod 11 :=
    ((atEleven.residueFieldEquivAdicCompletionIntegers (K := ℚ)).symm.trans
      residueElevenAlgEquiv.toRingEquiv).toEquiv
  letI : Finite
      (IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ)) :=
    Finite.of_equiv (ZMod 11) residueEquivZMod.symm
  let identitySubgroup : AddSubgroup W.Point :=
    nonsingularReductionSubgroup hW (nonsingularReduction_isAdditive hW)
  let identityReduction : identitySubgroup →+
      IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ) :=
    especial.toAddMonoidHom.comp
      (nonsingularReductionHom hW (nonsingularReduction_isAdditive hW))
  let formalKernel : AddSubgroup identitySubgroup :=
    (filtration hW 0).comap identitySubgroup.subtype
  apply addOrderOf_ne_thirtyFive_of_componentExponentTwelveAtEleven
    identitySubgroup identityReduction formalKernel
  · ext Q
    change especial
      (nonsingularReductionHom hW (nonsingularReduction_isAdditive hW) Q) = 0 ↔ _
    rw [← map_zero especial, especial.injective.eq_iff]
    exact nonsingularReduction_eq_zero_iff hW Q Q.property
  · intro Q hQ
    apply Subtype.ext
    apply Subtype.ext
    exact torsion_eq_zero_of_mem_formalKernel_atEleven hW Q.property
      (identitySubgroup.subtype.isOfFinAddOrder
        (formalKernel.subtype.isOfFinAddOrder hQ))
  · exact TameAdditiveReductionDataAtEleven.residue_natCard
  · exact hcomponent

/-- In the order-one branch of the normalized tame Tate equation at eleven, every local point
belongs to the canonical nonsingular-reduction subgroup.  The checked eleven-adic filtration
therefore excludes a marked point of exact order thirty-five. -/
theorem addOrderOf_ne_thirtyFive_of_firstBlowup_residue_b₆_ne_zeroAtEleven
    {W : Affine (atEleven.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atEleven.adicCompletionIntegers ℚ)}
    (hW : W₀.map
      (algebraMap (atEleven.adicCompletionIntegers ℚ)
        (atEleven.adicCompletion ℚ)) = W)
    [W.IsElliptic] [DecidableEq (atEleven.adicCompletion ℚ)]
    [W₀.IsShortNF]
    (B : FirstBlowupEquationCharts W₀)
    (h2 : (2 : IsLocalRing.ResidueField
      (atEleven.adicCompletionIntegers ℚ)) ≠ 0)
    (h3 : (3 : IsLocalRing.ResidueField
      (atEleven.adicCompletionIntegers ℚ)) ≠ 0)
    (hspecial : W₀.map
      (IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ)) =
        cuspidalShortCurve
          (IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ)))
    (hb₆ : IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ)
      B.coefficients.b₆ ≠ 0)
    (especial : (adicRedCurve W₀).Point ≃+
      IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ))
    (P : W.Point) : addOrderOf P ≠ 35 := by
  apply addOrderOf_ne_thirtyFive_of_nonsingularReduction_of_componentExponentTwelveAtEleven
    hW especial P
  exact
    twelve_nsmul_mem_nonsingularReductionSubgroup_of_firstBlowup_residue_b₆_ne_zero
      hW B h2 h3 hspecial hb₆ P

/-- In the next coefficient branch at eleven, the tangent calculation puts the marked double in
canonical nonsingular reduction.  The established exponent-twelve endpoint therefore excludes
exact order thirty-five. -/
theorem addOrderOf_ne_thirtyFive_of_firstBlowup_residue_b₄_ne_zeroAtEleven
    {W : Affine (atEleven.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atEleven.adicCompletionIntegers ℚ)}
    (hW : W₀.map
      (algebraMap (atEleven.adicCompletionIntegers ℚ)
        (atEleven.adicCompletion ℚ)) = W)
    [W.IsElliptic] [DecidableEq (atEleven.adicCompletion ℚ)]
    [W₀.IsShortNF]
    (B : FirstBlowupEquationCharts W₀)
    (h2 : (2 : IsLocalRing.ResidueField
      (atEleven.adicCompletionIntegers ℚ)) ≠ 0)
    (h3 : (3 : IsLocalRing.ResidueField
      (atEleven.adicCompletionIntegers ℚ)) ≠ 0)
    (hspecial : W₀.map
      (IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ)) =
        cuspidalShortCurve
          (IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ)))
    (hb₄ : IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ)
      B.coefficients.b₄ ≠ 0)
    (especial : (adicRedCurve W₀).Point ≃+
      IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ))
    (P : W.Point) : addOrderOf P ≠ 35 := by
  apply addOrderOf_ne_thirtyFive_of_nonsingularReduction_of_componentExponentTwelveAtEleven
    hW especial P
  exact
    twelve_nsmul_mem_nonsingularReductionSubgroup_of_firstBlowup_residue_b₄_ne_zero
      hW B h2 h3 hspecial hb₄ P

/-- In the exact depth-two `a₆` branch at eleven, the checked tangent--secant calculation puts the
twelfth multiple of the marked point in canonical nonsingular reduction.  This is incompatible
with exact order thirty-five. -/
theorem addOrderOf_ne_thirtyFive_of_a₄_sq_a₆_sq_not_cubeAtEleven
    {W : Affine (atEleven.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atEleven.adicCompletionIntegers ℚ)}
    (hW : W₀.map
      (algebraMap (atEleven.adicCompletionIntegers ℚ)
        (atEleven.adicCompletion ℚ)) = W)
    [W.IsElliptic] [DecidableEq (atEleven.adicCompletion ℚ)]
    [W₀.IsShortNF]
    (h2 : (2 : IsLocalRing.ResidueField
      (atEleven.adicCompletionIntegers ℚ)) ≠ 0)
    (h3 : (3 : IsLocalRing.ResidueField
      (atEleven.adicCompletionIntegers ℚ)) ≠ 0)
    (hspecial : W₀.map
      (IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ)) =
        cuspidalShortCurve
          (IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ)))
    (ha₄sq : W₀.a₄ ∈ IsLocalRing.maximalIdeal
      (atEleven.adicCompletionIntegers ℚ) ^ 2)
    (ha₆sq : W₀.a₆ ∈ IsLocalRing.maximalIdeal
      (atEleven.adicCompletionIntegers ℚ) ^ 2)
    (ha₆notcube : W₀.a₆ ∉ IsLocalRing.maximalIdeal
      (atEleven.adicCompletionIntegers ℚ) ^ 3)
    (especial : (adicRedCurve W₀).Point ≃+
      IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ))
    (P : W.Point) : addOrderOf P ≠ 35 := by
  apply addOrderOf_ne_thirtyFive_of_nonsingularReduction_of_componentExponentTwelveAtEleven
    hW especial P
  exact twelve_nsmul_mem_nonsingularReductionSubgroup_of_a₄_sq_a₆_sq_not_cube
    hW h2 h3 hspecial ha₄sq ha₆sq ha₆notcube P

/-- A simple marked root of the exceptional cubic at eleven forces the marked twelfth multiple
into canonical nonsingular reduction, contradicting exact order thirty-five. -/
theorem addOrderOf_ne_thirtyFive_of_markedExceptionalCubic_simpleRootAtEleven
    {W : Affine (atEleven.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atEleven.adicCompletionIntegers ℚ)}
    {P : W.Point}
    (hW : W₀.map
      (algebraMap (atEleven.adicCompletionIntegers ℚ)
        (atEleven.adicCompletion ℚ)) = W)
    [W.IsElliptic] [DecidableEq (atEleven.adicCompletion ℚ)]
    [W₀.IsShortNF]
    (h2 : (2 : IsLocalRing.ResidueField
      (atEleven.adicCompletionIntegers ℚ)) ≠ 0)
    (h3 : (3 : IsLocalRing.ResidueField
      (atEleven.adicCompletionIntegers ℚ)) ≠ 0)
    (hspecial : W₀.map
      (IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ)) =
        cuspidalShortCurve
          (IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ)))
    (D : MarkedExceptionalCubicData W₀ W P)
    (hsimple : D.derivativeResidue ≠ 0)
    (especial : (adicRedCurve W₀).Point ≃+
      IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ)) :
    addOrderOf P ≠ 35 := by
  apply addOrderOf_ne_thirtyFive_of_nonsingularReduction_of_componentExponentTwelveAtEleven
    hW especial P
  exact
    twelve_nsmul_mem_nonsingularReductionSubgroup_of_markedExceptionalCubic_simpleRoot
      hW h2 h3 hspecial D hsimple

/-- A nonzero repeated marked root of the exceptional cubic at eleven forces the marked twelfth
multiple into canonical nonsingular reduction, contradicting exact order thirty-five. -/
theorem
    addOrderOf_ne_thirtyFive_of_markedExceptionalCubic_repeatedNonzeroRootAtEleven
    {W : Affine (atEleven.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atEleven.adicCompletionIntegers ℚ)}
    {P : W.Point}
    (hW : W₀.map
      (algebraMap (atEleven.adicCompletionIntegers ℚ)
        (atEleven.adicCompletion ℚ)) = W)
    [W.IsElliptic] [DecidableEq (atEleven.adicCompletion ℚ)]
    [W₀.IsShortNF]
    (h2 : (2 : IsLocalRing.ResidueField
      (atEleven.adicCompletionIntegers ℚ)) ≠ 0)
    (h3 : (3 : IsLocalRing.ResidueField
      (atEleven.adicCompletionIntegers ℚ)) ≠ 0)
    (hspecial : W₀.map
      (IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ)) =
        cuspidalShortCurve
          (IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ)))
    (D : MarkedExceptionalCubicData W₀ W P)
    (hrepeated : D.derivativeResidue = 0)
    (hroot_ne : IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ) D.X ≠ 0)
    (especial : (adicRedCurve W₀).Point ≃+
      IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ)) :
    addOrderOf P ≠ 35 := by
  apply addOrderOf_ne_thirtyFive_of_nonsingularReduction_of_componentExponentTwelveAtEleven
    hW especial P
  exact
    twelve_nsmul_mem_nonsingularReductionSubgroup_of_repeatedExceptionalRoot_ne_zero
      hW h2 h3 hspecial D hrepeated hroot_ne

/-- For an order-35 point on the selected eleven-adic short equation, a repeated marked
exceptional root must be zero.  The marked abscissa and both coefficients consequently gain one
power of the same bundled uniformizer. -/
theorem markedExceptionalCubic_zeroRoot_and_deeperDepths_of_orderThirtyFiveAtEleven
    {W : Affine (atEleven.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atEleven.adicCompletionIntegers ℚ)}
    {P : W.Point}
    (hW : W₀.map
      (algebraMap (atEleven.adicCompletionIntegers ℚ)
        (atEleven.adicCompletion ℚ)) = W)
    [W.IsElliptic] [DecidableEq (atEleven.adicCompletion ℚ)]
    [W₀.IsShortNF]
    (h2 : (2 : IsLocalRing.ResidueField
      (atEleven.adicCompletionIntegers ℚ)) ≠ 0)
    (h3 : (3 : IsLocalRing.ResidueField
      (atEleven.adicCompletionIntegers ℚ)) ≠ 0)
    (hspecial : W₀.map
      (IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ)) =
        cuspidalShortCurve
          (IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ)))
    (D : MarkedExceptionalCubicData W₀ W P)
    (hrepeated : D.derivativeResidue = 0)
    (especial : (adicRedCurve W₀).Point ≃+
      IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ))
    (horder : addOrderOf P = 35) :
    IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ) D.X = 0 ∧
      IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ) D.A = 0 ∧
      IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ) D.B = 0 ∧
      D.x ∈ IsLocalRing.maximalIdeal (atEleven.adicCompletionIntegers ℚ) ^ 2 ∧
      W₀.a₄ ∈ IsLocalRing.maximalIdeal (atEleven.adicCompletionIntegers ℚ) ^ 3 ∧
      W₀.a₆ ∈ IsLocalRing.maximalIdeal (atEleven.adicCompletionIntegers ℚ) ^ 4 := by
  have hroot : IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ) D.X = 0 := by
    by_contra hroot_ne
    exact
      (addOrderOf_ne_thirtyFive_of_markedExceptionalCubic_repeatedNonzeroRootAtEleven
        hW h2 h3 hspecial D hrepeated hroot_ne especial) horder
  have hdepth :=
    markedExceptionalCubic_deeper_depths_of_derivative_eq_zero_of_root_eq_zero
      D hrepeated hroot
  exact ⟨hroot, hdepth⟩

/-- Exact depth four of `a₆` on the selected marked exceptional branch puts `12P` in canonical
nonsingular reduction, contradicting exact order thirty-five over the eleven-adic field. -/
theorem addOrderOf_ne_thirtyFive_of_marked_depth_fourAtEleven
    {W : Affine (atEleven.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atEleven.adicCompletionIntegers ℚ)}
    {P : W.Point}
    (hW : W₀.map
      (algebraMap (atEleven.adicCompletionIntegers ℚ)
        (atEleven.adicCompletion ℚ)) = W)
    [W.IsElliptic] [DecidableEq (atEleven.adicCompletion ℚ)]
    [W₀.IsShortNF]
    (h2 : (2 : IsLocalRing.ResidueField
      (atEleven.adicCompletionIntegers ℚ)) ≠ 0)
    (h3 : (3 : IsLocalRing.ResidueField
      (atEleven.adicCompletionIntegers ℚ)) ≠ 0)
    (hspecial : W₀.map
      (IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ)) =
        cuspidalShortCurve
          (IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ)))
    (D : MarkedExceptionalCubicData W₀ W P)
    (hxsq : D.x ∈ IsLocalRing.maximalIdeal
      (atEleven.adicCompletionIntegers ℚ) ^ 2)
    (ha₄cube : W₀.a₄ ∈ IsLocalRing.maximalIdeal
      (atEleven.adicCompletionIntegers ℚ) ^ 3)
    (ha₆four : W₀.a₆ ∈ IsLocalRing.maximalIdeal
      (atEleven.adicCompletionIntegers ℚ) ^ 4)
    (ha₆notfive : W₀.a₆ ∉ IsLocalRing.maximalIdeal
      (atEleven.adicCompletionIntegers ℚ) ^ 5)
    (especial : (adicRedCurve W₀).Point ≃+
      IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ)) :
    addOrderOf P ≠ 35 := by
  apply addOrderOf_ne_thirtyFive_of_nonsingularReduction_of_componentExponentTwelveAtEleven
    hW especial P
  exact twelve_nsmul_mem_nonsingularReductionSubgroup_of_marked_depth_four
    hW h2 h3 hspecial D hxsq ha₄cube ha₆four ha₆notfive

/-- An order-35 marked point forces `a₆` to gain the fifth power of the maximal ideal on the
same selected eleven-adic short model. -/
theorem markedExceptionalCubic_a₆_mem_fifth_of_orderThirtyFiveAtEleven
    {W : Affine (atEleven.adicCompletion ℚ)}
    {W₀ : WeierstrassCurve (atEleven.adicCompletionIntegers ℚ)}
    {P : W.Point}
    (hW : W₀.map
      (algebraMap (atEleven.adicCompletionIntegers ℚ)
        (atEleven.adicCompletion ℚ)) = W)
    [W.IsElliptic] [DecidableEq (atEleven.adicCompletion ℚ)]
    [W₀.IsShortNF]
    (h2 : (2 : IsLocalRing.ResidueField
      (atEleven.adicCompletionIntegers ℚ)) ≠ 0)
    (h3 : (3 : IsLocalRing.ResidueField
      (atEleven.adicCompletionIntegers ℚ)) ≠ 0)
    (hspecial : W₀.map
      (IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ)) =
        cuspidalShortCurve
          (IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ)))
    (D : MarkedExceptionalCubicData W₀ W P)
    (hxsq : D.x ∈ IsLocalRing.maximalIdeal
      (atEleven.adicCompletionIntegers ℚ) ^ 2)
    (ha₄cube : W₀.a₄ ∈ IsLocalRing.maximalIdeal
      (atEleven.adicCompletionIntegers ℚ) ^ 3)
    (ha₆four : W₀.a₆ ∈ IsLocalRing.maximalIdeal
      (atEleven.adicCompletionIntegers ℚ) ^ 4)
    (especial : (adicRedCurve W₀).Point ≃+
      IsLocalRing.ResidueField (atEleven.adicCompletionIntegers ℚ))
    (horder : addOrderOf P = 35) :
    W₀.a₆ ∈ IsLocalRing.maximalIdeal
      (atEleven.adicCompletionIntegers ℚ) ^ 5 := by
  by_contra ha₆notfive
  exact
    (addOrderOf_ne_thirtyFive_of_marked_depth_fourAtEleven
      hW h2 h3 hspecial D hxsq ha₄cube ha₆four ha₆notfive especial) horder

end MazurTorsion.OrderThirtyFive

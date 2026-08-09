/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroModuli

/-!
# The units orbit of generators of a rational cyclic subgroup

For a rational cyclic subgroup `C` of order `N`, its exact generators form a
free transitive `(ZMod N)ˣ`-set.  The action is the canonical one: a unit acts
by the corresponding natural-number multiple in `C`.  This is the algebraic
orbit statement needed to descend a fine `Gamma₁(N)` classifying point to a
generator-independent `Gamma₀(N)` point.

This file constructs no modular-curve target and makes no representability
claim.  It isolates the generator-choice theorem so that a later coarse
quotient cannot hide it in a supplied invariance hypothesis.
-/

namespace MazurTorsion.ModularCurve.XZeroModuli
namespace RationalCyclicSubgroup

universe u

variable {A : Type u} [AddCommGroup A]
  {N : ℕ} [NeZero N]

/-- The chosen generator identifies a rational cyclic subgroup of order `N`
with `ZMod N`. -/
noncomputable def generatorAddEquiv (C : RationalCyclicSubgroup A N) :
    ZMod N ≃+ C.carrier :=
  zmodAddEquivOfGenerator
    (g := C.generator)
    (fun x ↦ by
      rw [show AddSubgroup.zmultiples C.generator = ⊤ from by
        apply AddSubgroup.eq_top_of_card_eq
        rw [Nat.card_zmultiples, C.addOrderOf_generator_subtype]
        exact C.card_eq.symm]
      trivial)
    C.card_eq

@[simp]
theorem generatorAddEquiv_one (C : RationalCyclicSubgroup A N) :
    C.generatorAddEquiv 1 = C.generator :=
  zmodAddEquivOfGenerator_apply_one _ _

/-- An element of `ZMod N` has additive order `N` exactly when the implication
needed here holds: it is a unit.  The proof also covers `N = 1`, where the
zero ring has `0 = 1`. -/
theorem zmod_isUnit_of_addOrderOf_eq_level (z : ZMod N)
    (hz : addOrderOf z = N) : IsUnit z := by
  have hN0 : N ≠ 0 := NeZero.ne N
  have horder : N / N.gcd z.val = N := by
    rw [← ZMod.addOrderOf_coe z.val hN0]
    simpa using hz
  have hmul : N / N.gcd z.val * N.gcd z.val = N :=
    Nat.div_mul_cancel (Nat.gcd_dvd_left N z.val)
  rw [horder] at hmul
  have hgcd : N.gcd z.val = 1 := by
    apply Nat.mul_left_cancel (NeZero.pos N)
    simpa using hmul
  have hcop : z.val.Coprime N := by
    rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm]
    exact hgcd
  have hu : IsUnit (z.val : ZMod N) :=
    (ZMod.isUnit_iff_coprime z.val N).2 hcop
  simpa using hu

/-- An exact generator of `C`, retained as a point of the actual subgroup.
Using the subgroup point rather than only an ambient point makes the units
action closed without any auxiliary membership proof. -/
structure ExactGenerator (C : RationalCyclicSubgroup A N) where
  point : C.carrier
  exactOrder : addOrderOf point = N

namespace ExactGenerator

@[ext]
theorem ext {C : RationalCyclicSubgroup A N} {P Q : C.ExactGenerator}
    (h : P.point = Q.point) : P = Q := by
  cases P
  cases Q
  simp_all

/-- The ambient point represented by an exact subgroup generator. -/
def ambient {C : RationalCyclicSubgroup A N} (P : C.ExactGenerator) : A :=
  P.point

@[simp]
theorem ambient_exactOrder {C : RationalCyclicSubgroup A N}
    (P : C.ExactGenerator) : addOrderOf P.ambient = N :=
  (addOrderOf_injective (AddSubgroup.subtype C.carrier)
    C.carrier.subtype_injective P.point).trans P.exactOrder

/-- Package an ambient exact-order point already known to lie in `C`. -/
def ofAmbient (C : RationalCyclicSubgroup A N) (P : A)
    (hmem : P ∈ C.carrier) (horder : addOrderOf P = N) : C.ExactGenerator where
  point := ⟨P, hmem⟩
  exactOrder :=
    (addOrderOf_injective (AddSubgroup.subtype C.carrier)
      C.carrier.subtype_injective ⟨P, hmem⟩).symm.trans horder

@[simp]
theorem ofAmbient_ambient (C : RationalCyclicSubgroup A N) (P : A)
    (hmem : P ∈ C.carrier) (horder : addOrderOf P = N) :
    (ofAmbient C P hmem horder).ambient = P :=
  rfl

/-- The generator selected by `RationalCyclicSubgroup.generator`, now packaged
as an exact generator. -/
noncomputable def chosen (C : RationalCyclicSubgroup A N) : C.ExactGenerator where
  point := C.generator
  exactOrder := C.addOrderOf_generator_subtype

@[simp]
theorem chosen_ambient (C : RationalCyclicSubgroup A N) :
    (chosen C).ambient = C.generator :=
  rfl

/-- Every exact generator generates precisely the original ambient subgroup. -/
theorem zmultiples_ambient {C : RationalCyclicSubgroup A N}
    (P : C.ExactGenerator) :
    AddSubgroup.zmultiples P.ambient = C.carrier := by
  apply le_antisymm
  · rintro x ⟨k, rfl⟩
    exact C.carrier.zsmul_mem P.point.property k
  · intro x hx
    have htop : AddSubgroup.zmultiples P.point = ⊤ := by
      apply AddSubgroup.eq_top_of_card_eq
      rw [Nat.card_zmultiples, P.exactOrder]
      exact C.card_eq.symm
    have hx' : (⟨x, hx⟩ : C.carrier) ∈
        AddSubgroup.zmultiples P.point := by
      rw [htop]
      trivial
    rcases AddSubgroup.mem_zmultiples_iff.mp hx' with ⟨k, hk⟩
    exact AddSubgroup.mem_zmultiples_iff.mpr
      ⟨k, congrArg Subtype.val hk⟩

end ExactGenerator

/-- The units action on exact generators, transported through the chosen
`ZMod N` coordinate.  `exactGenerator_smul_point` below proves that this
transported definition is the canonical natural-number-multiple action and
therefore does not depend on the coordinate choice. -/
noncomputable instance exactGeneratorMulAction
    (C : RationalCyclicSubgroup A N) :
    MulAction (ZMod N)ˣ C.ExactGenerator where
  smul a P :=
    { point := C.generatorAddEquiv
        (a • C.generatorAddEquiv.symm P.point)
      exactOrder := by
        calc
          addOrderOf (C.generatorAddEquiv
              (a • C.generatorAddEquiv.symm P.point)) =
              addOrderOf (a • C.generatorAddEquiv.symm P.point) :=
            C.generatorAddEquiv.addOrderOf_eq _
          _ = addOrderOf (C.generatorAddEquiv.symm P.point) :=
            (DistribMulAction.toAddEquiv (ZMod N) a).addOrderOf_eq _
          _ = addOrderOf P.point :=
            C.generatorAddEquiv.symm.addOrderOf_eq _
          _ = N := P.exactOrder }
  one_smul P := by
    apply ExactGenerator.ext
    change C.generatorAddEquiv
      ((1 : (ZMod N)ˣ) • C.generatorAddEquiv.symm P.point) = P.point
    simp
  mul_smul a b P := by
    apply ExactGenerator.ext
    change C.generatorAddEquiv
        ((a * b) • C.generatorAddEquiv.symm P.point) =
      C.generatorAddEquiv
        (a • C.generatorAddEquiv.symm
          (C.generatorAddEquiv
            (b • C.generatorAddEquiv.symm P.point)))
    simp [mul_smul]

@[simp]
theorem exactGenerator_smul_point (C : RationalCyclicSubgroup A N)
    (a : (ZMod N)ˣ) (P : C.ExactGenerator) :
    (a • P).point = C.generatorAddEquiv
      (a • C.generatorAddEquiv.symm P.point) :=
  rfl

/-- The transported units action is the intrinsic action by the natural
representative of the unit. -/
theorem exactGenerator_smul_point_eq_nsmul
    (C : RationalCyclicSubgroup A N) (a : (ZMod N)ˣ)
    (P : C.ExactGenerator) :
    (a • P).point = a.val.val • P.point := by
  apply C.generatorAddEquiv.symm.injective
  simp only [exactGenerator_smul_point, AddEquiv.symm_apply_apply,
    map_nsmul]
  rw [Units.smul_def, smul_eq_mul, nsmul_eq_mul,
    ZMod.natCast_zmod_val]

/-- The units action is transitive on exact generators. -/
theorem exists_unit_smul_eq (C : RationalCyclicSubgroup A N)
    (P Q : C.ExactGenerator) :
    ∃ a : (ZMod N)ˣ, a • P = Q := by
  let p : ZMod N := C.generatorAddEquiv.symm P.point
  let q : ZMod N := C.generatorAddEquiv.symm Q.point
  have hporder : addOrderOf p = N := by
    calc
      addOrderOf p = addOrderOf (C.generatorAddEquiv p) :=
        (C.generatorAddEquiv.addOrderOf_eq p).symm
      _ = addOrderOf P.point := by simp [p]
      _ = N := P.exactOrder
  have hqorder : addOrderOf q = N := by
    calc
      addOrderOf q = addOrderOf (C.generatorAddEquiv q) :=
        (C.generatorAddEquiv.addOrderOf_eq q).symm
      _ = addOrderOf Q.point := by simp [q]
      _ = N := Q.exactOrder
  obtain ⟨up, hup⟩ := zmod_isUnit_of_addOrderOf_eq_level p hporder
  obtain ⟨uq, huq⟩ := zmod_isUnit_of_addOrderOf_eq_level q hqorder
  refine ⟨uq * up⁻¹, ?_⟩
  apply ExactGenerator.ext
  apply C.generatorAddEquiv.symm.injective
  simp only [exactGenerator_smul_point, AddEquiv.symm_apply_apply]
  change (↑(uq * up⁻¹) : ZMod N) * p = q
  calc
    (↑(uq * up⁻¹) : ZMod N) * p =
        (↑(uq * up⁻¹) : ZMod N) * (↑up : ZMod N) :=
      congrArg (fun z : ZMod N ↦
        (↑(uq * up⁻¹) : ZMod N) * z) hup.symm
    _ = (↑uq : ZMod N) := by simp
    _ = q := huq

/-- The units action is free at every exact generator. -/
theorem unit_smul_injective (C : RationalCyclicSubgroup A N)
    (P : C.ExactGenerator) :
    Function.Injective (fun a : (ZMod N)ˣ ↦ a • P) := by
  intro a b hab
  apply Units.ext
  have hpoint := congrArg ExactGenerator.point hab
  have hz := congrArg C.generatorAddEquiv.symm hpoint
  simp only [exactGenerator_smul_point,
    AddEquiv.symm_apply_apply] at hz
  let p : ZMod N := C.generatorAddEquiv.symm P.point
  have hporder : addOrderOf p = N := by
    calc
      addOrderOf p = addOrderOf (C.generatorAddEquiv p) :=
        (C.generatorAddEquiv.addOrderOf_eq p).symm
      _ = addOrderOf P.point := by simp [p]
      _ = N := P.exactOrder
  exact (zmod_isUnit_of_addOrderOf_eq_level p hporder).mul_right_cancel hz

/-- Exact generators form a torsor in the concrete sense that between any two
there is a unique acting unit. -/
theorem existsUnique_unit_smul_eq (C : RationalCyclicSubgroup A N)
    (P Q : C.ExactGenerator) :
    ∃! a : (ZMod N)ˣ, a • P = Q := by
  obtain ⟨a, ha⟩ := C.exists_unit_smul_eq P Q
  exact ⟨a, ha, fun b hb ↦ C.unit_smul_injective P (hb.trans ha.symm)⟩

noncomputable instance (C : RationalCyclicSubgroup A N) :
    MulAction.IsPretransitive (ZMod N)ˣ C.ExactGenerator :=
  ⟨C.exists_unit_smul_eq⟩

end RationalCyclicSubgroup
end MazurTorsion.ModularCurve.XZeroModuli

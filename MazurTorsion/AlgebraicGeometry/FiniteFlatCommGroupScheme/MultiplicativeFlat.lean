/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
import MazurTorsion.Algebra.HopfLocalizationAway
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Examples
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.QuasiFiniteFppfHOne

/-!
# The bad-level flat model of `mu_p`

This file constructs the multiplicative factor denoted `mu_p^b` in Mazur's analysis of finite
flat group schemes over `Spec Z`.  Its coordinate ring starts from the group algebra
`Z[C_p]`, the coordinates of `mu_p`, and localizes at

`e = a - q P`,

where `P` is the sum of the group-like basis vectors, `a = level ^ exponent`, and
`a = 1 + p * q`.  The latter identity is supplied by `MuFlatDatum`; for a prime coefficient
and a coprime level, the canonical datum uses Fermat's theorem with `exponent = p - 1`.

The key point is an explicit tensor witness `w` satisfying

`Delta(e) * w = e tensor e`.

Consequently the principal localization inherits a Hopf algebra structure from `Z[C_p]`.
The construction deliberately keeps `coeffPrime` and `level` distinct.  No Cartier-dual or
supported fppf quotient is asserted here.
-/

noncomputable section

open CategoryTheory WithConv
open scoped TensorProduct CategoryTheory

namespace AlgebraicGeometry
namespace QuasiFiniteFlatCommGroupScheme

universe u

/-- Arithmetic input for the bad-level multiplicative model.  The explicit exponent makes the
construction usable both with Fermat's exponent and with sharper congruences available in a
downstream application. -/
structure MuFlatDatum (coeffPrime level : ℕ) where
  exponent : ℕ
  exponent_pos : 0 < exponent
  correction : ℤ
  pow_eq_one_add :
    (level : ℤ) ^ exponent = 1 + (coeffPrime : ℤ) * correction

namespace MuFlatDatum

/-- Fermat's theorem supplies the standard multiplicative-flat datum with exponent `p - 1`.
The coprimality hypothesis is stated over `Z`, exactly as used by the upstream theorem. -/
noncomputable def ofPrimeCoprime {coeffPrime level : ℕ}
    (hprime : Nat.Prime coeffPrime)
    (hcoprime : IsCoprime (level : ℤ) (coeffPrime : ℤ)) :
    MuFlatDatum coeffPrime level := by
  let hdiv : (coeffPrime : ℤ) ∣ (level : ℤ) ^ (coeffPrime - 1) - 1 :=
    Int.prime_dvd_pow_sub_one hprime hcoprime
  exact
    { exponent := coeffPrime - 1
      exponent_pos := Nat.sub_pos_of_lt hprime.one_lt
      correction := hdiv.choose
      pow_eq_one_add := by
        have h := hdiv.choose_spec
        omega }

@[simp]
theorem ofPrimeCoprime_exponent {coeffPrime level : ℕ}
    (hprime : Nat.Prime coeffPrime)
    (hcoprime : IsCoprime (level : ℤ) (coeffPrime : ℤ)) :
    (ofPrimeCoprime hprime hcoprime).exponent = coeffPrime - 1 := rfl

end MuFlatDatum

section Trace

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]

/-- The trace element in the group algebra: the sum of all group-like basis vectors. -/
noncomputable def groupTrace : MonoidAlgebra R G :=
  ∑ g : G, MonoidAlgebra.single g 1

@[simp]
theorem single_mul_groupTrace (g : G) :
    MonoidAlgebra.single g (1 : R) * groupTrace (R := R) (G := G) =
      groupTrace (R := R) (G := G) := by
  classical
  simp only [groupTrace, Finset.mul_sum, MonoidAlgebra.single_mul_single, one_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun _ ↦ rfl)

@[simp]
theorem groupTrace_mul_single (g : G) :
    groupTrace (R := R) (G := G) * MonoidAlgebra.single g (1 : R) =
      groupTrace (R := R) (G := G) := by
  rw [mul_comm, single_mul_groupTrace]

/-- The trace is a quasi-idempotent: `P^2 = |G| P`. -/
theorem groupTrace_sq :
    groupTrace (R := R) (G := G) ^ 2 =
      algebraMap R (MonoidAlgebra R G) (Fintype.card G : R) *
        groupTrace (R := R) (G := G) := by
  classical
  rw [pow_two]
  change (∑ g : G, MonoidAlgebra.single g (1 : R)) *
      groupTrace (R := R) (G := G) = _
  rw [Finset.sum_mul]
  simp only [single_mul_groupTrace]
  simp

end Trace

section MuCoordinates

variable (coeffPrime level : ℕ) [NeZero coeffPrime]

private abbrev MuCharacter := Multiplicative (ZMod coeffPrime)

/-- Integral Hopf coordinates of `mu_p`. -/
abbrev MuCoordinates := MonoidAlgebra ℤ (MuCharacter coeffPrime)

noncomputable instance muCoordinatesModuleFinitePresentation :
    Module.FinitePresentation ℤ (MuCoordinates coeffPrime) :=
  Module.finitePresentation_of_projective ℤ (MuCoordinates coeffPrime)

private abbrev MuTensor :=
  MuCoordinates coeffPrime ⊗[ℤ] MuCoordinates coeffPrime

/-- The trace element `P = sum_g [g]` in `Z[C_p]`. -/
noncomputable def muTrace : MuCoordinates coeffPrime :=
  groupTrace (R := ℤ) (G := MuCharacter coeffPrime)

@[simp]
theorem card_muCharacter : Fintype.card (MuCharacter coeffPrime) = coeffPrime := by
  rw [← Nat.card_eq_fintype_card]
  exact (Nat.card_congr
    (Multiplicative.ofAdd : ZMod coeffPrime ≃ MuCharacter coeffPrime)).trans
      (Nat.card_zmod coeffPrime)

/-- The cyclic trace relation `P^2 = p P`. -/
theorem muTrace_sq :
    muTrace coeffPrime ^ 2 =
      algebraMap ℤ (MuCoordinates coeffPrime) (coeffPrime : ℤ) *
        muTrace coeffPrime := by
  simpa only [muTrace, card_muCharacter, Nat.cast_ofNat] using
    (groupTrace_sq (R := ℤ) (G := MuCharacter coeffPrime))

/-- The counit of the trace is the order of the cyclic character group. -/
@[simp]
theorem counit_muTrace :
    Bialgebra.counitAlgHom ℤ (MuCoordinates coeffPrime) (muTrace coeffPrime) =
      (coeffPrime : ℤ) := by
  classical
  simp [muTrace, groupTrace]

/-- Inversion permutes the group-like basis, so the antipode fixes the trace. -/
@[simp]
theorem antipode_muTrace :
    HopfAlgebra.antipodeAlgHom ℤ (MuCoordinates coeffPrime) (muTrace coeffPrime) =
      muTrace coeffPrime := by
  classical
  change HopfAlgebra.antipode ℤ (muTrace coeffPrime) = muTrace coeffPrime
  simp only [muTrace, groupTrace, map_sum, MonoidAlgebra.antipode_single,
    HopfAlgebra.antipode_one]
  exact Fintype.sum_equiv (Equiv.inv (MuCharacter coeffPrime)) _ _ (fun _ ↦ by rfl)

/-- The scalar appearing in the bad-level congruence. -/
def muFlatScale (datum : MuFlatDatum coeffPrime level) : ℤ :=
  (level : ℤ) ^ datum.exponent

/-- The function cutting out Mazur's multiplicative flat model in `mu_p`. -/
noncomputable def muFlatElement (datum : MuFlatDatum coeffPrime level) :
    MuCoordinates coeffPrime :=
  algebraMap ℤ (MuCoordinates coeffPrime) (muFlatScale coeffPrime level datum) -
    algebraMap ℤ (MuCoordinates coeffPrime) datum.correction * muTrace coeffPrime

/-- A complementary element used to show that the model agrees with all of `mu_p` away from
the level. -/
noncomputable def muFlatComplement (datum : MuFlatDatum coeffPrime level) :
    MuCoordinates coeffPrime :=
  1 + algebraMap ℤ (MuCoordinates coeffPrime) datum.correction * muTrace coeffPrime

omit [NeZero coeffPrime] in
theorem muFlatScale_eq_one_add (datum : MuFlatDatum coeffPrime level) :
    muFlatScale coeffPrime level datum =
      1 + (coeffPrime : ℤ) * datum.correction :=
  datum.pow_eq_one_add

/-- The defining element times its complement is the pullback of a power of the level. -/
theorem muFlatElement_mul_complement (datum : MuFlatDatum coeffPrime level) :
    muFlatElement coeffPrime level datum * muFlatComplement coeffPrime level datum =
      algebraMap ℤ (MuCoordinates coeffPrime) (muFlatScale coeffPrime level datum) := by
  rw [muFlatElement, muFlatComplement, muFlatScale_eq_one_add]
  simp only [map_add, map_one, map_mul, map_natCast]
  rw [← sub_eq_zero]
  calc
    ((1 + algebraMap ℤ (MuCoordinates coeffPrime) (coeffPrime : ℤ) *
              algebraMap ℤ (MuCoordinates coeffPrime) datum.correction -
            algebraMap ℤ (MuCoordinates coeffPrime) datum.correction * muTrace coeffPrime) *
          (1 + algebraMap ℤ (MuCoordinates coeffPrime) datum.correction * muTrace coeffPrime) -
        (1 + algebraMap ℤ (MuCoordinates coeffPrime) (coeffPrime : ℤ) *
          algebraMap ℤ (MuCoordinates coeffPrime) datum.correction)) =
      algebraMap ℤ (MuCoordinates coeffPrime) datum.correction ^ 2 *
        (algebraMap ℤ (MuCoordinates coeffPrime) (coeffPrime : ℤ) * muTrace coeffPrime -
          muTrace coeffPrime ^ 2) := by ring
    _ = 0 := by rw [muTrace_sq]; ring

/-- The full roots-of-unity model over the principal open defined by the indicated level power
lies in the multiplicative-flat principal open.  This is the coordinate-level away-from-level
consumer of `muFlatElement_mul_complement`. -/
theorem basicOpen_levelPower_le_muFlatElement (datum : MuFlatDatum coeffPrime level) :
    PrimeSpectrum.basicOpen
        (algebraMap ℤ (MuCoordinates coeffPrime) (muFlatScale coeffPrime level datum)) ≤
      PrimeSpectrum.basicOpen (muFlatElement coeffPrime level datum) := by
  rw [← muFlatElement_mul_complement]
  exact PrimeSpectrum.basicOpen_mul_le_left _ _

/-- The multiplicative-flat principal open contains all of `mu_p` over `D(level)`. -/
theorem basicOpen_level_le_muFlatElement (datum : MuFlatDatum coeffPrime level) :
    PrimeSpectrum.basicOpen
        (algebraMap ℤ (MuCoordinates coeffPrime) (level : ℤ)) ≤
      PrimeSpectrum.basicOpen (muFlatElement coeffPrime level datum) := by
  rw [← PrimeSpectrum.basicOpen_pow _ datum.exponent datum.exponent_pos]
  simpa [muFlatScale, map_pow] using
    basicOpen_levelPower_le_muFlatElement coeffPrime level datum

/-- Left copy of `P` in the tensor square. -/
noncomputable def muTraceLeft : MuTensor coeffPrime :=
  muTrace coeffPrime ⊗ₜ[ℤ] 1

/-- Right copy of `P` in the tensor square. -/
noncomputable def muTraceRight : MuTensor coeffPrime :=
  1 ⊗ₜ[ℤ] muTrace coeffPrime

/-- Diagonal copy `Delta(P)` in the tensor square. -/
noncomputable def muTraceDiagonal : MuTensor coeffPrime :=
  Bialgebra.comulAlgHom ℤ (MuCoordinates coeffPrime) (muTrace coeffPrime)

private theorem comul_muTrace_eq_sum :
    muTraceDiagonal coeffPrime =
      ∑ g : MuCharacter coeffPrime,
        MonoidAlgebra.single g (1 : ℤ) ⊗ₜ[ℤ] MonoidAlgebra.single g (1 : ℤ) := by
  classical
  simp [muTraceDiagonal, muTrace, groupTrace]

/-- The left trace times the diagonal trace is the product of the two side traces. -/
theorem muTraceLeft_mul_diagonal :
    muTraceLeft coeffPrime * muTraceDiagonal coeffPrime =
      muTraceLeft coeffPrime * muTraceRight coeffPrime := by
  classical
  rw [muTraceLeft, muTraceRight, comul_muTrace_eq_sum]
  simp only [Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul]
  have hmul (g : MuCharacter coeffPrime) :
      muTrace coeffPrime * MonoidAlgebra.single g (1 : ℤ) = muTrace coeffPrime := by
    change groupTrace (R := ℤ) (G := MuCharacter coeffPrime) *
        MonoidAlgebra.single g (1 : ℤ) = groupTrace (R := ℤ) (G := MuCharacter coeffPrime)
    exact groupTrace_mul_single g
  simp only [hmul, mul_one]
  rw [muTrace, groupTrace, TensorProduct.tmul_sum]

/-- The right trace times the diagonal trace is the product of the two side traces. -/
theorem muTraceRight_mul_diagonal :
    muTraceRight coeffPrime * muTraceDiagonal coeffPrime =
      muTraceLeft coeffPrime * muTraceRight coeffPrime := by
  classical
  rw [muTraceRight, muTraceLeft, comul_muTrace_eq_sum]
  simp only [Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one]
  have hmul (g : MuCharacter coeffPrime) :
      muTrace coeffPrime * MonoidAlgebra.single g (1 : ℤ) = muTrace coeffPrime := by
    change groupTrace (R := ℤ) (G := MuCharacter coeffPrime) *
        MonoidAlgebra.single g (1 : ℤ) = groupTrace (R := ℤ) (G := MuCharacter coeffPrime)
    exact groupTrace_mul_single g
  simp only [hmul, one_mul]
  rw [muTrace, groupTrace, TensorProduct.sum_tmul]

/-- The right tensor trace satisfies the same quasi-idempotent relation as `P`. -/
theorem muTraceRight_sq :
    muTraceRight coeffPrime ^ 2 =
      algebraMap ℤ (MuTensor coeffPrime) (coeffPrime : ℤ) *
        muTraceRight coeffPrime := by
  rw [muTraceRight, pow_two, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, ← pow_two, muTrace_sq]
  rw [Algebra.TensorProduct.algebraMap_apply',
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- The diagonal tensor trace satisfies the same quasi-idempotent relation as `P`. -/
theorem muTraceDiagonal_sq :
    muTraceDiagonal coeffPrime ^ 2 =
      algebraMap ℤ (MuTensor coeffPrime) (coeffPrime : ℤ) *
        muTraceDiagonal coeffPrime := by
  rw [muTraceDiagonal, ← map_pow, muTrace_sq]
  simp

private theorem witness_polynomial_identity {B : Type u} [CommRing B]
    (p a q left right diagonal : B)
    (ha : a = 1 + p * q)
    (hright : right ^ 2 = p * right)
    (hdiagonal : diagonal ^ 2 = p * diagonal)
    (hleftDiagonal : left * diagonal = left * right)
    (hrightDiagonal : right * diagonal = left * right) :
    (a - q * diagonal) *
        (a - q * left - q * right - q ^ 2 * (left * right) + a * q * diagonal) =
      (a - q * left) * (a - q * right) := by
  rw [ha]
  rw [← sub_eq_zero]
  calc
    (1 + p * q - q * diagonal) *
          (1 + p * q - q * left - q * right - q ^ 2 * (left * right) +
            (1 + p * q) * q * diagonal) -
        (1 + p * q - q * left) * (1 + p * q - q * right) =
      q ^ 2 * (left * diagonal - left * right) +
        q ^ 2 * (right * diagonal - left * right) +
        q ^ 3 * ((left * diagonal) * right - p * (left * right)) -
        (p * q ^ 3 + q ^ 2) * (diagonal ^ 2 - p * diagonal) := by ring
    _ = 0 := by
      have hright' : left * right * right = p * (left * right) := by
        calc
          left * right * right = left * right ^ 2 := by ring
          _ = left * (p * right) := by rw [hright]
          _ = p * (left * right) := by ring
      rw [hleftDiagonal, hrightDiagonal, hright', hdiagonal]
      ring

/-- Explicit denominator witness for the comultiplication of the multiplicative-flat
principal open. -/
noncomputable def muFlatComulWitness (datum : MuFlatDatum coeffPrime level) :
    MuTensor coeffPrime :=
  let a := algebraMap ℤ (MuTensor coeffPrime) (muFlatScale coeffPrime level datum)
  let q := algebraMap ℤ (MuTensor coeffPrime) datum.correction
  a - q * muTraceLeft coeffPrime - q * muTraceRight coeffPrime -
      q ^ 2 * (muTraceLeft coeffPrime * muTraceRight coeffPrime) +
    a * q * muTraceDiagonal coeffPrime

/-- The checked tensor identity that makes `Delta(e)` invertible after localizing both tensor
factors at `e`. -/
theorem comul_muFlatElement_mul_witness (datum : MuFlatDatum coeffPrime level) :
    Bialgebra.comulAlgHom ℤ (MuCoordinates coeffPrime)
          (muFlatElement coeffPrime level datum) *
        muFlatComulWitness coeffPrime level datum =
      muFlatElement coeffPrime level datum ⊗ₜ[ℤ]
        muFlatElement coeffPrime level datum := by
  let p : MuTensor coeffPrime := algebraMap ℤ _ (coeffPrime : ℤ)
  let a : MuTensor coeffPrime :=
    algebraMap ℤ _ (muFlatScale coeffPrime level datum)
  let q : MuTensor coeffPrime := algebraMap ℤ _ datum.correction
  have ha : a = 1 + p * q := by
    simp only [a, p, q]
    rw [muFlatScale_eq_one_add]
    simp
  have h := witness_polynomial_identity p a q
    (muTraceLeft coeffPrime) (muTraceRight coeffPrime) (muTraceDiagonal coeffPrime)
    ha (muTraceRight_sq coeffPrime) (muTraceDiagonal_sq coeffPrime)
      (muTraceLeft_mul_diagonal coeffPrime) (muTraceRight_mul_diagonal coeffPrime)
  have hcomulScale :
      Bialgebra.comulAlgHom ℤ (MuCoordinates coeffPrime)
          (algebraMap ℤ (MuCoordinates coeffPrime) (muFlatScale coeffPrime level datum)) = a := by
    change Coalgebra.comul (R := ℤ)
        (algebraMap ℤ (MuCoordinates coeffPrime) (muFlatScale coeffPrime level datum)) = a
    rw [Bialgebra.comul_algebraMap]
  have hcomulCorrection :
      Bialgebra.comulAlgHom ℤ (MuCoordinates coeffPrime)
          (algebraMap ℤ (MuCoordinates coeffPrime) datum.correction) = q := by
    change Coalgebra.comul (R := ℤ)
        (algebraMap ℤ (MuCoordinates coeffPrime) datum.correction) = q
    rw [Bialgebra.comul_algebraMap]
  have hcomulTrace :
      Bialgebra.comulAlgHom ℤ (MuCoordinates coeffPrime) (muTrace coeffPrime) =
        muTraceDiagonal coeffPrime := rfl
  rw [muFlatElement]
  simp only [map_sub, map_mul]
  rw [hcomulScale, hcomulCorrection, hcomulTrace]
  change (a - q * muTraceDiagonal coeffPrime) *
      muFlatComulWitness coeffPrime level datum = _
  rw [show muFlatComulWitness coeffPrime level datum =
      a - q * muTraceLeft coeffPrime - q * muTraceRight coeffPrime -
          q ^ 2 * (muTraceLeft coeffPrime * muTraceRight coeffPrime) +
        a * q * muTraceDiagonal coeffPrime by rfl]
  rw [h]
  have hleft : a - q * muTraceLeft coeffPrime =
      muFlatElement coeffPrime level datum ⊗ₜ[ℤ] 1 := by
    simp only [a, q, muTraceLeft, muFlatElement,
      Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, TensorProduct.sub_tmul]
  have hright : a - q * muTraceRight coeffPrime =
      1 ⊗ₜ[ℤ] muFlatElement coeffPrime level datum := by
    simp only [a, q, muTraceRight, muFlatElement,
      Algebra.TensorProduct.algebraMap_apply',
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.tmul_sub]
  rw [hleft, hright, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rfl

/-- Coordinates of the bad-level multiplicative model. -/
abbrev MuFlatCoordinates (datum : MuFlatDatum coeffPrime level) :=
  Localization.Away (muFlatElement coeffPrime level datum)

private abbrev muFlatIota (datum : MuFlatDatum coeffPrime level) :
    MuCoordinates coeffPrime →ₐ[ℤ] MuFlatCoordinates coeffPrime level datum :=
  Algebra.algHom ℤ (MuCoordinates coeffPrime) (MuFlatCoordinates coeffPrime level datum)

private theorem comul_muFlatElement_isUnit (datum : MuFlatDatum coeffPrime level) :
    IsUnit (((Algebra.TensorProduct.map
        (muFlatIota coeffPrime level datum) (muFlatIota coeffPrime level datum)).comp
      (Bialgebra.comulAlgHom ℤ (MuCoordinates coeffPrime)))
        (muFlatElement coeffPrime level datum)) := by
  letI : Module ℤ (MuFlatCoordinates coeffPrime level datum) := Algebra.toModule
  let e := muFlatElement coeffPrime level datum
  have he : IsUnit
      (algebraMap (MuCoordinates coeffPrime) (MuFlatCoordinates coeffPrime level datum) e) :=
    IsLocalization.Away.algebraMap_isUnit e
  have hleft : IsUnit
      (Algebra.TensorProduct.includeLeft
        (R := ℤ) (A := MuFlatCoordinates coeffPrime level datum)
          (B := MuFlatCoordinates coeffPrime level datum)
            (algebraMap (MuCoordinates coeffPrime)
              (MuFlatCoordinates coeffPrime level datum) e)) :=
    he.map (Algebra.TensorProduct.includeLeft
      (R := ℤ) (S := ℤ) (A := MuFlatCoordinates coeffPrime level datum)
        (B := MuFlatCoordinates coeffPrime level datum)).toMonoidHom
  have hright : IsUnit
      (Algebra.TensorProduct.includeRight
        (R := ℤ) (A := MuFlatCoordinates coeffPrime level datum)
          (B := MuFlatCoordinates coeffPrime level datum)
            (algebraMap (MuCoordinates coeffPrime)
              (MuFlatCoordinates coeffPrime level datum) e)) :=
    he.map (Algebra.TensorProduct.includeRight
      (R := ℤ) (A := MuFlatCoordinates coeffPrime level datum)
        (B := MuFlatCoordinates coeffPrime level datum)).toMonoidHom
  have htensor : IsUnit
      ((algebraMap (MuCoordinates coeffPrime) (MuFlatCoordinates coeffPrime level datum) e
          ⊗ₜ[ℤ]
        algebraMap (MuCoordinates coeffPrime) (MuFlatCoordinates coeffPrime level datum) e :
          MuFlatCoordinates coeffPrime level datum ⊗[ℤ]
            MuFlatCoordinates coeffPrime level datum)) := by
    convert hleft.mul hright using 1
    simp [Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul]
  have hm := congrArg
    (Algebra.TensorProduct.map
      (muFlatIota coeffPrime level datum) (muFlatIota coeffPrime level datum))
        (comul_muFlatElement_mul_witness coeffPrime level datum)
  rw [map_mul, Algebra.TensorProduct.map_tmul] at hm
  have hproduct : IsUnit
      ((((Algebra.TensorProduct.map
          (muFlatIota coeffPrime level datum) (muFlatIota coeffPrime level datum)).comp
        (Bialgebra.comulAlgHom ℤ (MuCoordinates coeffPrime))) e) *
          Algebra.TensorProduct.map
            (muFlatIota coeffPrime level datum) (muFlatIota coeffPrime level datum)
              (muFlatComulWitness coeffPrime level datum)) := by
    rw [AlgHom.comp_apply]
    rw [hm]
    exact htensor
  letI : IsDedekindFiniteMonoid
      (MuFlatCoordinates coeffPrime level datum ⊗[ℤ]
        MuFlatCoordinates coeffPrime level datum) := {
    mul_eq_one_symm := fun {x y} hxy ↦ by
      calc
        y * x = x * y := Algebra.TensorProduct.instCommSemiring.mul_comm _ _
        _ = 1 := hxy }
  exact isUnit_of_mul_isUnit_left hproduct

private theorem counit_muFlatElement (datum : MuFlatDatum coeffPrime level) :
    Bialgebra.counitAlgHom ℤ (MuCoordinates coeffPrime)
        (muFlatElement coeffPrime level datum) = 1 := by
  have hscale : Bialgebra.counitAlgHom ℤ (MuCoordinates coeffPrime)
      (algebraMap ℤ (MuCoordinates coeffPrime) (muFlatScale coeffPrime level datum)) =
        muFlatScale coeffPrime level datum :=
    (Bialgebra.counitAlgHom ℤ (MuCoordinates coeffPrime)).commutes _
  have hcorrection : Bialgebra.counitAlgHom ℤ (MuCoordinates coeffPrime)
      (algebraMap ℤ (MuCoordinates coeffPrime) datum.correction) = datum.correction :=
    (Bialgebra.counitAlgHom ℤ (MuCoordinates coeffPrime)).commutes _
  rw [muFlatElement, map_sub, map_mul, hscale, hcorrection, counit_muTrace]
  rw [muFlatScale_eq_one_add]
  ring

private theorem counit_muFlatElement_isUnit (datum : MuFlatDatum coeffPrime level) :
    IsUnit (Bialgebra.counitAlgHom ℤ (MuCoordinates coeffPrime)
      (muFlatElement coeffPrime level datum)) := by
  rw [counit_muFlatElement]
  exact isUnit_one

private theorem antipode_muFlatElement (datum : MuFlatDatum coeffPrime level) :
    HopfAlgebra.antipodeAlgHom ℤ (MuCoordinates coeffPrime)
        (muFlatElement coeffPrime level datum) = muFlatElement coeffPrime level datum := by
  have hscale : HopfAlgebra.antipodeAlgHom ℤ (MuCoordinates coeffPrime)
      (algebraMap ℤ (MuCoordinates coeffPrime) (muFlatScale coeffPrime level datum)) =
        algebraMap ℤ (MuCoordinates coeffPrime) (muFlatScale coeffPrime level datum) :=
    (HopfAlgebra.antipodeAlgHom ℤ (MuCoordinates coeffPrime)).commutes _
  have hcorrection : HopfAlgebra.antipodeAlgHom ℤ (MuCoordinates coeffPrime)
      (algebraMap ℤ (MuCoordinates coeffPrime) datum.correction) =
        algebraMap ℤ (MuCoordinates coeffPrime) datum.correction :=
    (HopfAlgebra.antipodeAlgHom ℤ (MuCoordinates coeffPrime)).commutes _
  rw [muFlatElement, map_sub, map_mul, hscale, hcorrection, antipode_muTrace]

private theorem antipode_muFlatElement_isUnit (datum : MuFlatDatum coeffPrime level) :
    IsUnit (((Algebra.algHom ℤ (MuCoordinates coeffPrime)
        (MuFlatCoordinates coeffPrime level datum)).comp
      (HopfAlgebra.antipodeAlgHom ℤ (MuCoordinates coeffPrime)))
        (muFlatElement coeffPrime level datum)) := by
  rw [AlgHom.comp_apply, antipode_muFlatElement]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- The bialgebra structure on the localized multiplicative-flat coordinates. -/
noncomputable instance muFlatBialgebra (datum : MuFlatDatum coeffPrime level) :
    Bialgebra ℤ (MuFlatCoordinates coeffPrime level datum) :=
  HopfLocalizationAway.bialgebra (muFlatElement coeffPrime level datum)
    (comul_muFlatElement_isUnit coeffPrime level datum)
    (counit_muFlatElement_isUnit coeffPrime level datum)

/-- The Hopf algebra structure on the localized multiplicative-flat coordinates. -/
noncomputable instance muFlatHopfAlgebra (datum : MuFlatDatum coeffPrime level) :
    HopfAlgebra ℤ (MuFlatCoordinates coeffPrime level datum) :=
  HopfLocalizationAway.hopfAlgebra (muFlatElement coeffPrime level datum)
    (comul_muFlatElement_isUnit coeffPrime level datum)
    (counit_muFlatElement_isUnit coeffPrime level datum)
    (antipode_muFlatElement_isUnit coeffPrime level datum)

/-- Downstream compatibility consumer: the descended comultiplication agrees with the original
comultiplication after mapping both tensor factors to the localization. -/
@[simp]
theorem muFlat_comul_algebraMap (datum : MuFlatDatum coeffPrime level)
    (x : MuCoordinates coeffPrime) :
    Bialgebra.comulAlgHom ℤ (MuFlatCoordinates coeffPrime level datum)
        (algebraMap (MuCoordinates coeffPrime) (MuFlatCoordinates coeffPrime level datum) x) =
      Algebra.TensorProduct.map
        (Algebra.algHom ℤ (MuCoordinates coeffPrime)
          (MuFlatCoordinates coeffPrime level datum))
        (Algebra.algHom ℤ (MuCoordinates coeffPrime)
          (MuFlatCoordinates coeffPrime level datum))
          (Bialgebra.comulAlgHom ℤ (MuCoordinates coeffPrime) x) := by
  change HopfLocalizationAway.comul (muFlatElement coeffPrime level datum)
      (comul_muFlatElement_isUnit coeffPrime level datum)
        (algebraMap (MuCoordinates coeffPrime)
          (MuFlatCoordinates coeffPrime level datum) x) = _
  exact HopfLocalizationAway.comul_algebraMap _ _ _

/-- Downstream compatibility consumer: the descended counit agrees with the counit of `mu_p`
on every unlocalized coordinate. -/
@[simp]
theorem muFlat_counit_algebraMap (datum : MuFlatDatum coeffPrime level)
    (x : MuCoordinates coeffPrime) :
    Bialgebra.counitAlgHom ℤ (MuFlatCoordinates coeffPrime level datum)
        (algebraMap (MuCoordinates coeffPrime) (MuFlatCoordinates coeffPrime level datum) x) =
      Bialgebra.counitAlgHom ℤ (MuCoordinates coeffPrime) x := by
  change HopfLocalizationAway.counit (muFlatElement coeffPrime level datum)
      (counit_muFlatElement_isUnit coeffPrime level datum)
        (algebraMap (MuCoordinates coeffPrime)
          (MuFlatCoordinates coeffPrime level datum) x) = _
  exact HopfLocalizationAway.counit_algebraMap _ _ _

/-- Cocommutativity of the localized Hopf algebra, constructed with the localization algebra's
`ℤ`-module structure in a local scope.  This avoids exporting a competing global integer-module
instance for the localized ring. -/
private theorem muFlatCocomm (datum : MuFlatDatum coeffPrime level) :
    letI : Module ℤ (MuFlatCoordinates coeffPrime level datum) := Algebra.toModule
    Coalgebra.IsCocomm ℤ (MuFlatCoordinates coeffPrime level datum) := by
  letI : Module ℤ (MuFlatCoordinates coeffPrime level datum) := Algebra.toModule
  refine { comm_comp_comul := ?_ }
  have h :
      (Algebra.TensorProduct.comm ℤ (MuFlatCoordinates coeffPrime level datum)
        (MuFlatCoordinates coeffPrime level datum)).toAlgHom.comp
          (Bialgebra.comulAlgHom ℤ (MuFlatCoordinates coeffPrime level datum)) =
        Bialgebra.comulAlgHom ℤ (MuFlatCoordinates coeffPrime level datum) := by
    apply IsLocalization.algHom_ext
      (Submonoid.powers (muFlatElement coeffPrime level datum))
    apply AlgHom.ext
    intro x
    simp only [AlgHom.comp_apply]
    change (Algebra.TensorProduct.comm ℤ _ _)
        (HopfLocalizationAway.comul (muFlatElement coeffPrime level datum)
          (comul_muFlatElement_isUnit coeffPrime level datum)
            (algebraMap (MuCoordinates coeffPrime)
              (MuFlatCoordinates coeffPrime level datum) x)) =
      HopfLocalizationAway.comul (muFlatElement coeffPrime level datum)
        (comul_muFlatElement_isUnit coeffPrime level datum)
          (algebraMap (MuCoordinates coeffPrime)
            (MuFlatCoordinates coeffPrime level datum) x)
    rw [HopfLocalizationAway.comul_algebraMap,
      Algebra.TensorProduct.comm_comp_map_apply]
    apply congrArg
      (Algebra.TensorProduct.map
        (Algebra.algHom ℤ (MuCoordinates coeffPrime)
          (MuFlatCoordinates coeffPrime level datum))
        (Algebra.algHom ℤ (MuCoordinates coeffPrime)
          (MuFlatCoordinates coeffPrime level datum)))
    change TensorProduct.comm ℤ _ _ (Coalgebra.comul x) = Coalgebra.comul x
    exact Coalgebra.comm_comul ℤ x
  exact congrArg AlgHom.toLinearMap h

/-- The affine commutative group scheme carried by the multiplicative-flat Hopf localization.
The local module choice is sealed inside the bundled object. -/
noncomputable def muFlatAffine (datum : MuFlatDatum coeffPrime level) :
    AffineCommGroupScheme ℤ := by
  letI : Module ℤ (MuFlatCoordinates coeffPrime level datum) := Algebra.toModule
  exact Opposite.op
    ⟨CommHopfAlgCat.of ℤ (MuFlatCoordinates coeffPrime level datum),
      muFlatCocomm coeffPrime level datum⟩

/-- The localization algebra map preserves the counit and comultiplication.  Its local module
choice is the same one sealed into `muFlatAffine`. -/
private noncomputable def muFlatInclusionBialgHom (datum : MuFlatDatum coeffPrime level) :
    letI : Module ℤ (MuFlatCoordinates coeffPrime level datum) := Algebra.toModule
    MuCoordinates coeffPrime →ₐc[ℤ] MuFlatCoordinates coeffPrime level datum := by
  letI : Module ℤ (MuFlatCoordinates coeffPrime level datum) := Algebra.toModule
  exact BialgHom.ofAlgHom
    (Algebra.algHom ℤ (MuCoordinates coeffPrime) (MuFlatCoordinates coeffPrime level datum))
    (by
      apply AlgHom.ext
      intro x
      change HopfLocalizationAway.counit (muFlatElement coeffPrime level datum)
          (counit_muFlatElement_isUnit coeffPrime level datum)
            (algebraMap (MuCoordinates coeffPrime)
              (MuFlatCoordinates coeffPrime level datum) x) =
        Bialgebra.counitAlgHom ℤ (MuCoordinates coeffPrime) x
      exact HopfLocalizationAway.counit_algebraMap _ _ _)
    (by
      apply AlgHom.ext
      intro x
      change Algebra.TensorProduct.map
          (Algebra.algHom ℤ (MuCoordinates coeffPrime)
            (MuFlatCoordinates coeffPrime level datum))
          (Algebra.algHom ℤ (MuCoordinates coeffPrime)
            (MuFlatCoordinates coeffPrime level datum))
            (Bialgebra.comulAlgHom ℤ (MuCoordinates coeffPrime) x) =
        HopfLocalizationAway.comul (muFlatElement coeffPrime level datum)
          (comul_muFlatElement_isUnit coeffPrime level datum)
            (algebraMap (MuCoordinates coeffPrime)
              (MuFlatCoordinates coeffPrime level datum) x)
      exact (HopfLocalizationAway.comul_algebraMap _ _ _).symm)

/-- The typed affine open-subgroup morphism from the multiplicative-flat model to `mu_p`. -/
noncomputable def muFlatInclusionAffine (datum : MuFlatDatum coeffPrime level) :
    muFlatAffine coeffPrime level datum ⟶
      (FiniteFlatCommGroupScheme.mu ℤ coeffPrime).obj := by
  letI : Module ℤ (MuFlatCoordinates coeffPrime level datum) := Algebra.toModule
  exact (ObjectProperty.homMk (P := cocommutativeHopfProperty ℤ)
    (CommHopfAlgCat.ofHom (muFlatInclusionBialgHom coeffPrime level datum))).op

/-- The underlying affine principal-open scheme of the multiplicative-flat model. -/
noncomputable abbrev muFlatScheme (datum : MuFlatDatum coeffPrime level) : Scheme :=
  Spec (.of (MuFlatCoordinates coeffPrime level datum))

/-- The underlying affine scheme map from the multiplicative-flat principal open to `mu_p`. -/
noncomputable abbrev muFlatInclusionSchemeMap (datum : MuFlatDatum coeffPrime level) :
    muFlatScheme coeffPrime level datum ⟶
      (FiniteFlatCommGroupScheme.mu ℤ coeffPrime).obj.scheme :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (MuCoordinates coeffPrime) (MuFlatCoordinates coeffPrime level datum)))

@[simp]
theorem schemeMap_muFlatInclusionAffine (datum : MuFlatDatum coeffPrime level) :
    AffineCommGroupScheme.schemeMap (muFlatInclusionAffine coeffPrime level datum) =
      muFlatInclusionSchemeMap coeffPrime level datum := rfl

instance muFlatInclusionSchemeMap_isOpenImmersion (datum : MuFlatDatum coeffPrime level) :
    IsOpenImmersion (muFlatInclusionSchemeMap coeffPrime level datum) := by
  change IsOpenImmersion
    (Spec.map (CommRingCat.ofHom
      (algebraMap (MuCoordinates coeffPrime) (MuFlatCoordinates coeffPrime level datum))))
  infer_instance

/-- The affine inclusion has exactly the defining principal-open range. -/
theorem muFlatInclusionSchemeMap_opensRange (datum : MuFlatDatum coeffPrime level) :
    (muFlatInclusionSchemeMap coeffPrime level datum).opensRange =
      PrimeSpectrum.basicOpen (muFlatElement coeffPrime level datum) := by
  change (Spec.map (CommRingCat.ofHom
      (algebraMap (MuCoordinates coeffPrime)
        (MuFlatCoordinates coeffPrime level datum)))).opensRange =
    PrimeSpectrum.basicOpen (muFlatElement coeffPrime level datum)
  exact Scheme.Hom.opensRange_localizationAway
    (R := CommRingCat.of (MuCoordinates coeffPrime))
      (muFlatElement coeffPrime level datum)

/-- Geometric away-from-level consumer: over `D(level)`, the inclusion contains all of
`mu_p`. -/
theorem muFlatInclusionSchemeMap_contains_levelOpen (datum : MuFlatDatum coeffPrime level) :
    PrimeSpectrum.basicOpen
        (algebraMap ℤ (MuCoordinates coeffPrime) (level : ℤ)) ≤
      (muFlatInclusionSchemeMap coeffPrime level datum).opensRange := by
  rw [muFlatInclusionSchemeMap_opensRange]
  exact basicOpen_level_le_muFlatElement coeffPrime level datum

instance muStructureMap_locallyOfFinitePresentation :
    LocallyOfFinitePresentation
      (FiniteFlatCommGroupScheme.mu ℤ coeffPrime).obj.structureMap := by
  change LocallyOfFinitePresentation
    (Spec.map (CommRingCat.ofHom (algebraMap ℤ (MuCoordinates coeffPrime))))
  rw [LocallyOfFinitePresentation.SpecMap_iff]
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

/-- The structural map of the underlying multiplicative-flat affine scheme. -/
noncomputable abbrev muFlatStructureMap (datum : MuFlatDatum coeffPrime level) :
    muFlatScheme coeffPrime level datum ⟶ Spec (.of ℤ) :=
  muFlatInclusionSchemeMap coeffPrime level datum ≫
    (FiniteFlatCommGroupScheme.mu ℤ coeffPrime).obj.structureMap

instance muFlatStructureMap_flat (datum : MuFlatDatum coeffPrime level) :
    Flat (muFlatStructureMap coeffPrime level datum) := by
  dsimp only [muFlatStructureMap]
  infer_instance

instance muFlatStructureMap_locallyQuasiFinite (datum : MuFlatDatum coeffPrime level) :
    LocallyQuasiFinite (muFlatStructureMap coeffPrime level datum) := by
  dsimp only [muFlatStructureMap]
  infer_instance

instance muFlatStructureMap_quasiCompact (datum : MuFlatDatum coeffPrime level) :
    QuasiCompact (muFlatStructureMap coeffPrime level datum) := by
  dsimp only [muFlatStructureMap]
  infer_instance

instance muFlatStructureMap_isSeparated (datum : MuFlatDatum coeffPrime level) :
    IsSeparated (muFlatStructureMap coeffPrime level datum) := by
  dsimp only [muFlatStructureMap]
  infer_instance

instance muFlatStructureMap_locallyOfFinitePresentation
    (datum : MuFlatDatum coeffPrime level) :
    LocallyOfFinitePresentation (muFlatStructureMap coeffPrime level datum) := by
  dsimp only [muFlatStructureMap]
  infer_instance

private theorem muFlatAffine_structureMap_eq (datum : MuFlatDatum coeffPrime level) :
    (muFlatAffine coeffPrime level datum).structureMap =
      muFlatStructureMap coeffPrime level datum := by
  change Spec.map (CommRingCat.ofHom
      (algebraMap ℤ (MuFlatCoordinates coeffPrime level datum))) =
    Spec.map (CommRingCat.ofHom
        (algebraMap (MuCoordinates coeffPrime)
          (MuFlatCoordinates coeffPrime level datum))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℤ (MuCoordinates coeffPrime)))
  rw [← Spec.map_comp, Spec.map_inj]
  ext z
  exact (IsScalarTower.algebraMap_apply ℤ (MuCoordinates coeffPrime)
    (MuFlatCoordinates coeffPrime level datum) z).symm

instance muFlatAffine_flat (datum : MuFlatDatum coeffPrime level) :
    Flat (muFlatAffine coeffPrime level datum).structureMap := by
  rw [muFlatAffine_structureMap_eq]
  exact muFlatStructureMap_flat coeffPrime level datum

instance muFlatAffine_locallyQuasiFinite (datum : MuFlatDatum coeffPrime level) :
    LocallyQuasiFinite (muFlatAffine coeffPrime level datum).structureMap := by
  rw [muFlatAffine_structureMap_eq]
  exact muFlatStructureMap_locallyQuasiFinite coeffPrime level datum

instance muFlatAffine_quasiCompact (datum : MuFlatDatum coeffPrime level) :
    QuasiCompact (muFlatAffine coeffPrime level datum).structureMap := by
  rw [muFlatAffine_structureMap_eq]
  exact muFlatStructureMap_quasiCompact coeffPrime level datum

instance muFlatAffine_isSeparated (datum : MuFlatDatum coeffPrime level) :
    IsSeparated (muFlatAffine coeffPrime level datum).structureMap := by
  rw [muFlatAffine_structureMap_eq]
  exact muFlatStructureMap_isSeparated coeffPrime level datum

instance muFlatAffine_locallyOfFinitePresentation (datum : MuFlatDatum coeffPrime level) :
    LocallyOfFinitePresentation (muFlatAffine coeffPrime level datum).structureMap := by
  rw [muFlatAffine_structureMap_eq]
  exact muFlatStructureMap_locallyOfFinitePresentation coeffPrime level datum

/-- The multiplicative-flat model as a typed flat, quasi-finite, quasi-compact, separated
commutative group scheme of finite presentation over `Spec ℤ`. -/
noncomputable def muFlat (datum : MuFlatDatum coeffPrime level) :
    QuasiFiniteFlatCommGroupScheme (Spec (.of ℤ)) where
  obj := (muFlatAffine coeffPrime level datum).toCommGroupScheme
  property := by
    change Flat (muFlatAffine coeffPrime level datum).structureMap ∧
      LocallyQuasiFinite (muFlatAffine coeffPrime level datum).structureMap ∧
      QuasiCompact (muFlatAffine coeffPrime level datum).structureMap ∧
      IsSeparated (muFlatAffine coeffPrime level datum).structureMap ∧
      LocallyOfFinitePresentation (muFlatAffine coeffPrime level datum).structureMap
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

instance muSchemeStructureMap_locallyOfFinitePresentation :
    LocallyOfFinitePresentation
      (FiniteFlatCommGroupScheme.muScheme ℤ coeffPrime).obj.X.hom := by
  change LocallyOfFinitePresentation
    (FiniteFlatCommGroupScheme.mu ℤ coeffPrime).obj.structureMap
  exact muStructureMap_locallyOfFinitePresentation coeffPrime

/-- The realized typed open-subgroup morphism from the multiplicative-flat model to `mu_p`. -/
noncomputable def muFlatInclusion (datum : MuFlatDatum coeffPrime level) :
    (muFlat coeffPrime level datum).obj ⟶
      (FiniteFlatCommGroupScheme.muScheme ℤ coeffPrime).obj :=
  (AffineCommGroupScheme.realizationFunctor ℤ).map
    (muFlatInclusionAffine coeffPrime level datum)

/-- The open-subgroup inclusion in the quasi-finite flat category. -/
noncomputable def muFlatInclusionMap (datum : MuFlatDatum coeffPrime level) :
    muFlat coeffPrime level datum ⟶
      ofFiniteFlat (FiniteFlatCommGroupScheme.muScheme ℤ coeffPrime) :=
  ObjectProperty.homMk (muFlatInclusion coeffPrime level datum)

@[simp]
theorem muFlatInclusionMap_hom (datum : MuFlatDatum coeffPrime level) :
    (muFlatInclusionMap coeffPrime level datum).hom =
      muFlatInclusion coeffPrime level datum := rfl

@[simp]
theorem muFlatInclusion_left (datum : MuFlatDatum coeffPrime level) :
    (muFlatInclusion coeffPrime level datum).hom.hom.hom.left =
      muFlatInclusionSchemeMap coeffPrime level datum := rfl

instance muFlatInclusion_isOpenImmersion (datum : MuFlatDatum coeffPrime level) :
    IsOpenImmersion (muFlatInclusion coeffPrime level datum).hom.hom.hom.left := by
  rw [muFlatInclusion_left]
  exact muFlatInclusionSchemeMap_isOpenImmersion coeffPrime level datum

/-- The typed realized inclusion has exactly the defining principal-open range. -/
theorem muFlatInclusion_opensRange (datum : MuFlatDatum coeffPrime level) :
    ((muFlatInclusion coeffPrime level datum).hom.hom.hom.left).opensRange =
      PrimeSpectrum.basicOpen (muFlatElement coeffPrime level datum) := by
  change (muFlatInclusionSchemeMap coeffPrime level datum).opensRange =
    PrimeSpectrum.basicOpen (muFlatElement coeffPrime level datum)
  exact muFlatInclusionSchemeMap_opensRange coeffPrime level datum

/-- The typed realized inclusion contains the whole `mu_p` over `D(level)`. -/
theorem muFlatInclusion_contains_levelOpen (datum : MuFlatDatum coeffPrime level) :
    PrimeSpectrum.basicOpen
        (algebraMap ℤ (MuCoordinates coeffPrime) (level : ℤ)) ≤
      ((muFlatInclusion coeffPrime level datum).hom.hom.hom.left).opensRange := by
  change PrimeSpectrum.basicOpen
      (algebraMap ℤ (MuCoordinates coeffPrime) (level : ℤ)) ≤
    (muFlatInclusionSchemeMap coeffPrime level datum).opensRange
  exact muFlatInclusionSchemeMap_contains_levelOpen coeffPrime level datum

end MuCoordinates

section FermatSpecialization

variable {coeffPrime level : ℕ}

/-- The canonical multiplicative-flat group scheme attached to a prime coefficient and a
coprime level, using Fermat's exponent `coeffPrime - 1`.  The nonzero instance is sealed into
the value and need not be supplied separately by downstream users. -/
noncomputable def fermatMuFlat (hprime : Nat.Prime coeffPrime)
    (hcoprime : IsCoprime (level : ℤ) (coeffPrime : ℤ)) :
    letI : NeZero coeffPrime := ⟨hprime.ne_zero⟩
    QuasiFiniteFlatCommGroupScheme (Spec (.of ℤ)) := by
  letI : NeZero coeffPrime := ⟨hprime.ne_zero⟩
  exact muFlat coeffPrime level (MuFlatDatum.ofPrimeCoprime hprime hcoprime)

/-- The canonical Fermat multiplicative-flat model comes with the typed localization inclusion
into `mu_p`; this is the concrete downstream consumer of `MuFlatDatum.ofPrimeCoprime`. -/
noncomputable def fermatMuFlatInclusionMap (hprime : Nat.Prime coeffPrime)
    (hcoprime : IsCoprime (level : ℤ) (coeffPrime : ℤ)) :
    letI : NeZero coeffPrime := ⟨hprime.ne_zero⟩
    fermatMuFlat hprime hcoprime ⟶
      ofFiniteFlat (FiniteFlatCommGroupScheme.muScheme ℤ coeffPrime) := by
  letI : NeZero coeffPrime := ⟨hprime.ne_zero⟩
  exact muFlatInclusionMap coeffPrime level
    (MuFlatDatum.ofPrimeCoprime hprime hcoprime)

@[simp]
theorem fermatMuFlatInclusionMap_hom (hprime : Nat.Prime coeffPrime)
    (hcoprime : IsCoprime (level : ℤ) (coeffPrime : ℤ)) :
    letI : NeZero coeffPrime := ⟨hprime.ne_zero⟩
    (fermatMuFlatInclusionMap hprime hcoprime).hom =
      muFlatInclusion coeffPrime level
        (MuFlatDatum.ofPrimeCoprime hprime hcoprime) := by
  letI : NeZero coeffPrime := ⟨hprime.ne_zero⟩
  rfl

instance fermatMuFlatInclusionMap_isOpenImmersion (hprime : Nat.Prime coeffPrime)
    (hcoprime : IsCoprime (level : ℤ) (coeffPrime : ℤ)) :
    letI : NeZero coeffPrime := ⟨hprime.ne_zero⟩
    IsOpenImmersion
      (fermatMuFlatInclusionMap hprime hcoprime).hom.hom.hom.hom.left := by
  letI : NeZero coeffPrime := ⟨hprime.ne_zero⟩
  change IsOpenImmersion
    (muFlatInclusion coeffPrime level
      (MuFlatDatum.ofPrimeCoprime hprime hcoprime)).hom.hom.hom.left
  exact muFlatInclusion_isOpenImmersion coeffPrime level
    (MuFlatDatum.ofPrimeCoprime hprime hcoprime)

/-- The canonical Fermat inclusion has the same explicit principal-open range. -/
theorem fermatMuFlatInclusion_opensRange (hprime : Nat.Prime coeffPrime)
    (hcoprime : IsCoprime (level : ℤ) (coeffPrime : ℤ)) :
    letI : NeZero coeffPrime := ⟨hprime.ne_zero⟩
    ((fermatMuFlatInclusionMap hprime hcoprime).hom.hom.hom.hom.left).opensRange =
      PrimeSpectrum.basicOpen
        (muFlatElement coeffPrime level (MuFlatDatum.ofPrimeCoprime hprime hcoprime)) := by
  letI : NeZero coeffPrime := ⟨hprime.ne_zero⟩
  change ((muFlatInclusion coeffPrime level
      (MuFlatDatum.ofPrimeCoprime hprime hcoprime)).hom.hom.hom.left).opensRange =
    PrimeSpectrum.basicOpen
      (muFlatElement coeffPrime level (MuFlatDatum.ofPrimeCoprime hprime hcoprime))
  exact muFlatInclusion_opensRange coeffPrime level
    (MuFlatDatum.ofPrimeCoprime hprime hcoprime)

/-- In the canonical Fermat specialization, the typed inclusion contains all of `mu_p` over
the actual level open `D(level)`. -/
theorem fermatMuFlatInclusion_contains_levelOpen (hprime : Nat.Prime coeffPrime)
    (hcoprime : IsCoprime (level : ℤ) (coeffPrime : ℤ)) :
    letI : NeZero coeffPrime := ⟨hprime.ne_zero⟩
    PrimeSpectrum.basicOpen
        (algebraMap ℤ (MuCoordinates coeffPrime) (level : ℤ)) ≤
      ((fermatMuFlatInclusionMap hprime hcoprime).hom.hom.hom.hom.left).opensRange := by
  letI : NeZero coeffPrime := ⟨hprime.ne_zero⟩
  change PrimeSpectrum.basicOpen
      (algebraMap ℤ (MuCoordinates coeffPrime) (level : ℤ)) ≤
    ((muFlatInclusion coeffPrime level
      (MuFlatDatum.ofPrimeCoprime hprime hcoprime)).hom.hom.hom.left).opensRange
  exact muFlatInclusion_contains_levelOpen coeffPrime level
    (MuFlatDatum.ofPrimeCoprime hprime hcoprime)

end FermatSpecialization

end QuasiFiniteFlatCommGroupScheme
end AlgebraicGeometry

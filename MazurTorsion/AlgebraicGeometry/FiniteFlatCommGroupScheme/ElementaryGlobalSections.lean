/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfQuotientEuler

/-!
# Global sections of the elementary admissible factors

This file computes the degree-zero terms needed by the finite-flat Euler estimate over
`Spec ℤ`.  Global sections of a constant finite group scheme over an integral domain are exactly
the constant sections.  For an odd prime, the only integral point of `mu_p` is `1`.  These
computations give honest `FinitePGroup.CertifiedData` for both elementary factors.  A recursive
actual-quotient theorem consumes one kernel certificate, and the two-elementary-factor step is its
checked downstream consumer.

No comparison with fppf `H¹`, Kummer sequence, quasi-finite extension-by-zero factor, or
middle-`H¹` finiteness theorem is asserted here.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

universe u v

/-- The identity object of `Scheme.Over (Spec R)` is isomorphic to the affine self-test object.
This bridges the global-section and affine-Hopf point APIs. -/
noncomputable def baseObjectIsoTestObject (R : Type u) [CommRing R] :
    baseObject (Spec (.of R)) ≅ AffineCommGroupScheme.testObject (R := R) R :=
  AffineCommGroupScheme.baseIsoSelfTestObject R

/-- Pullback along an isomorphism of test objects is a multiplicative equivalence on represented
points. -/
noncomputable def pointMulEquivOfTestIso {S : Scheme.{u}}
    (G : FiniteFlatCommGroupScheme S) {T U : Over S} (e : T ≅ U) :
    G.Point T ≃* G.Point U :=
  CommGroupScheme.pointMulEquivOfOverIso G.toCommGroupScheme e

/-- Global sections of a constant finite group scheme over an integral domain are exactly its
indexing group. -/
noncomputable def constantBasePointMulEquiv_of_noZeroDivisors
    (R : Type u) [CommRing R] [NoZeroDivisors R] [Nontrivial R]
    (G : Type u) [CommGroup G] [Fintype G] :
    BasePoint (constantScheme R G) ≃* G :=
  (pointMulEquivOfTestIso (constantScheme R G)
      (baseObjectIsoTestObject R)).trans
    (constantPointMulEquiv_of_noZeroDivisors R G).symm

/-- Certified `p`-power cardinality transports across a multiplicative equivalence without
changing its length. -/
def FinitePGroup.CertifiedData.congr {p : ℕ} {A : Type u} {B : Type v}
    [CommGroup A] [CommGroup B]
    (D : FinitePGroup.CertifiedData p A) (e : A ≃* B) :
    FinitePGroup.CertifiedData p B := by
  letI : Finite A := D.finite
  exact
    { finite := Finite.of_equiv A e.toEquiv
      length := D.length
      card_eq := (Nat.card_congr e.symm.toEquiv).trans D.card_eq }

/-- The integral global sections of the constant order-`p` factor have cardinality `p`. -/
noncomputable def constantBasePointCertifiedDataInt (p : ℕ) [NeZero p] :
    FinitePGroup.CertifiedData p
      (BasePoint (constantScheme ℤ (Multiplicative (ZMod p)))) where
  finite := Finite.of_equiv (Multiplicative (ZMod p))
    (constantBasePointMulEquiv_of_noZeroDivisors ℤ
      (Multiplicative (ZMod p))).symm.toEquiv
  length := 1
  card_eq := by
    rw [Nat.card_congr
      (constantBasePointMulEquiv_of_noZeroDivisors ℤ
        (Multiplicative (ZMod p))).toEquiv, pow_one]
    exact (Nat.card_congr
      (Multiplicative.ofAdd : ZMod p ≃ Multiplicative (ZMod p))).trans
        (Nat.card_zmod p)

/-- An odd-order integral root of unity is `1`. -/
theorem rootsOfUnity_int_eq_one_of_odd {p : ℕ} (hp : Odd p)
    (x : rootsOfUnity p ℤ) : x = 1 := by
  apply Subtype.ext
  change (x : ℤˣ) = 1
  rcases Int.units_eq_one_or (x : ℤˣ) with hx | hx
  · exact hx
  · exfalso
    have hpow : (x : ℤˣ) ^ p = 1 := x.property
    rw [hx] at hpow
    have hneg : (-1 : ℤˣ) ^ p = -1 := hp.neg_one_pow
    rw [hneg] at hpow
    have hval := congrArg Units.val hpow
    norm_num at hval

/-- The odd-order integral roots of unity form the trivial multiplicative group. -/
noncomputable def rootsOfUnityIntOddMulEquivUnit (p : ℕ) (hp : Odd p) :
    rootsOfUnity p ℤ ≃* Unit where
  toFun _ := Unit.unit
  invFun _ := 1
  left_inv := fun x ↦ (rootsOfUnity_int_eq_one_of_odd hp x).symm
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Global integral points of `mu_p` are trivial for odd `p`. -/
noncomputable def muBasePointMulEquivIntOfOdd (p : ℕ) [NeZero p] (hp : Odd p) :
    BasePoint (muScheme ℤ p) ≃* Unit :=
  (pointMulEquivOfTestIso (muScheme ℤ p)
    (baseObjectIsoTestObject ℤ)).trans <|
  (muPointMulEquiv ℤ p ℤ).trans <|
  rootsOfUnityIntOddMulEquivUnit p hp

/-- The integral global sections of `mu_p` have cardinality `1 = p^0` for odd `p`. -/
noncomputable def muBasePointCertifiedDataIntOfOdd
    (p : ℕ) [NeZero p] (hp : Odd p) :
    FinitePGroup.CertifiedData p (BasePoint (muScheme ℤ p)) where
  finite := Finite.of_equiv Unit
    (muBasePointMulEquivIntOfOdd p hp).symm.toEquiv
  length := 0
  card_eq := by
    rw [Nat.card_congr (muBasePointMulEquivIntOfOdd p hp).toEquiv]
    simp

namespace AdmissibleSimpleFactor

/-- Exponent of `p` in the cardinality of the integral global sections of an elementary
admissible factor. -/
def hZeroLength {p : ℕ} [NeZero p]
    {Q : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (F : AdmissibleSimpleFactor ℤ p Q) : ℕ :=
  match F with
  | .constant _ => 1
  | .multiplicative _ => 0

/-- Concrete degree-zero cardinal certificate for either admissible order-`p` factor over
`Spec ℤ`, for odd `p`. -/
noncomputable def basePointCertifiedDataInt
    {p : ℕ} [NeZero p]
    {Q : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (F : AdmissibleSimpleFactor ℤ p Q) (hp : Odd p) :
    FinitePGroup.CertifiedData p (BasePoint Q) := by
  cases F with
  | constant i =>
      exact (constantBasePointCertifiedDataInt p).congr
        (pointMulEquivOfIso i (baseObject (Spec (.of ℤ)))).symm
  | multiplicative i =>
      exact (muBasePointCertifiedDataIntOfOdd p hp).congr
        (pointMulEquivOfIso i (baseObject (Spec (.of ℤ)))).symm

@[simp]
theorem basePointCertifiedDataInt_length
    {p : ℕ} [NeZero p]
    {Q : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (F : AdmissibleSimpleFactor ℤ p Q) (hp : Odd p) :
    (F.basePointCertifiedDataInt hp).length = F.hZeroLength := by
  cases F <;> rfl

end AdmissibleSimpleFactor

namespace FppfQuotientPresentation

/-- An actual quotient over `Spec ℤ` whose kernel is one admissible elementary factor consumes
that kernel's checked `H⁰` cardinality directly.  This is the recursive extension-step form:
the quotient's `H⁰` and `H¹` data and the middle `H⁰` remain explicit for the next filtration
layer; exactness derives finiteness of the middle `H¹`. -/
theorem fppfHOne_natCard_le_pow_of_admissibleKernelInt
    {p : ℕ} [NeZero p]
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (kernelFactor : AdmissibleSimpleFactor ℤ p D.kernelPresentation.kernel)
    (middleHZeroData : FinitePGroup.CertifiedData p (BasePoint G))
    (quotientHZeroData : FinitePGroup.CertifiedData p (BasePoint D.quotient))
    (kernelHOneData : FinitePGroup.CertifiedData p
      D.kernelPresentation.kernel.FppfHOne.{0})
    (quotientHOneData : FinitePGroup.CertifiedData p D.quotient.FppfHOne.{0})
    (hp : p.Prime) (hp2 : p ≠ 2) (bound : ℕ)
    (hbound :
      middleHZeroData.length + kernelHOneData.length + quotientHOneData.length ≤
        bound + kernelFactor.hZeroLength + quotientHZeroData.length) :
    Nat.card G.FppfHOne.{0} ≤ p ^ bound := by
  have hpOdd : Odd p := hp.odd_of_ne_two hp2
  apply FppfLowDegreeExactSequence.fppfHOne_natCard_le_pow_ofFppfQuotientPresentation
    D (kernelFactor.basePointCertifiedDataInt hpOdd) middleHZeroData
    quotientHZeroData kernelHOneData quotientHOneData hp bound
  simpa using hbound

end FppfQuotientPresentation

namespace AdmissibleFiltrationStep

/-- One actual admissible quotient step over `Spec ℤ` consumes the checked elementary-factor
`H⁰` cardinalities directly.  The remaining endpoint `H¹` certificates and middle `H⁰` stay
explicit; exactness derives finiteness of the middle `H¹`, and this theorem does not assume the
cardinality it is proving. -/
theorem fppfHOne_natCard_le_pow_int
    {p : ℕ} [NeZero p]
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : AdmissibleFiltrationStep ℤ p G)
    (middleHZeroData : FinitePGroup.CertifiedData p (BasePoint G))
    (kernelHOneData : FinitePGroup.CertifiedData p
      D.kernelPresentation.kernel.FppfHOne.{0})
    (quotientHOneData : FinitePGroup.CertifiedData p D.quotient.FppfHOne.{0})
    (hp2 : p ≠ 2) (bound : ℕ)
    (hbound :
      middleHZeroData.length + kernelHOneData.length + quotientHOneData.length ≤
        bound + D.kernelFactor.hZeroLength + D.quotientFactor.hZeroLength) :
    Nat.card G.FppfHOne.{0} ≤ p ^ bound := by
  have hpOdd : Odd p := D.prime.odd_of_ne_two hp2
  apply D.toFppfQuotientPresentation.fppfHOne_natCard_le_pow_of_admissibleKernelInt
    D.kernelFactor middleHZeroData
    (D.quotientFactor.basePointCertifiedDataInt hpOdd) kernelHOneData
    quotientHOneData D.prime hp2 bound
  simpa using hbound

end AdmissibleFiltrationStep

end AlgebraicGeometry.FiniteFlatCommGroupScheme

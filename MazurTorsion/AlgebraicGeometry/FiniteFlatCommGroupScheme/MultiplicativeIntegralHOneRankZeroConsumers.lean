/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfKummerRankZero
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.MultiplicativeFiniteAffineFamilyEffectivity
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.MuKernelPrimeFiberKummerRankZero

/-!
# Integral multiplicative-kernel H¹ rank-zero consumers

The actual integral vanishing of represented `H¹(mu_p)` transports through the multiplicative
factor isomorphism stored in an admissible filtration step.  Substituting that exact length-zero
certificate into the checked finite-flat Kummer criterion gives a rank-zero endpoint with a
simplified honest bound.

The middle `H⁰` certificate, quotient `H¹` certificate, Mordell--Weil torsion-cardinality law,
Kummer homomorphism, and its injectivity remain explicit.  Thus this file supplies no Raynaud,
Néron, quotient-cohomology, torsion, or Mordell--Weil premise that has not been proved elsewhere.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

open CommGroupScheme.MultiplicativeCocycleDescent.FiniteAffineFamilyEffectivity

universe u

namespace AdmissibleSimpleFactor

private theorem hZeroLength_eq_zero_of_isMultiplicative
    {p : ℕ} [NeZero p]
    {Q : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (F : AdmissibleSimpleFactor ℤ p Q) (hF : F.IsMultiplicative) :
    F.hZeroLength = 0 := by
  cases F with
  | constant _ => contradiction
  | multiplicative _ => rfl

end AdmissibleSimpleFactor

namespace AdmissibleFiltrationStep

/-- The integral `H¹` certificate for the actual kernel of an admissible step whose stored
simple-factor presentation is multiplicative.  The transport uses the underlying commutative
group-scheme isomorphism in the `mu_p`-to-kernel direction. -/
noncomputable def multiplicativeKernelFppfHOneCertifiedDataInt
    {p : ℕ} [NeZero p]
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : AdmissibleFiltrationStep ℤ p G)
    (hkernelFactor : D.kernelFactor.IsMultiplicative)
    (hp2 : p ≠ 2) :
    FinitePGroup.CertifiedData p
      D.kernelPresentation.kernel.FppfHOne.{0} :=
  (muSchemeFppfHOne_int_odd_prime_certifiedData p D.prime
      (D.prime.odd_of_ne_two hp2)).congr
    (CommGroupScheme.fppfHOneMulEquivOfIso
      ((finiteFlatCommGroupSchemeProperty _).ι.mapIso
        (D.kernelFactor.multiplicativeIso hkernelFactor))).symm

@[simp]
theorem multiplicativeKernelFppfHOneCertifiedDataInt_length
    {p : ℕ} [NeZero p]
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : AdmissibleFiltrationStep ℤ p G)
    (hkernelFactor : D.kernelFactor.IsMultiplicative)
    (hp2 : p ≠ 2) :
    (D.multiplicativeKernelFppfHOneCertifiedDataInt hkernelFactor hp2).length = 0 :=
  rfl

/-- An integral admissible step with multiplicative kernel feeds the actual finite-flat Kummer
rank-zero criterion.  Only the two zero-length multiplicative contributions have been removed
from the numerical premise; all arithmetic and quotient-cohomology inputs remain explicit. -/
theorem finrank_eq_zero_of_fppfKummer_multiplicativeKernelInt
    {p : ℕ} [NeZero p]
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : AdmissibleFiltrationStep ℤ p G)
    (hkernelFactor : D.kernelFactor.IsMultiplicative)
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) p).ker =
      p ^ torsionLength)
    (middleHZeroData : FinitePGroup.CertifiedData p (BasePoint G))
    (quotientHOneData : FinitePGroup.CertifiedData p
      D.quotient.FppfHOne.{0})
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) p).range) →*
        G.FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hp2 : p ≠ 2)
    (hbound :
      middleHZeroData.length + quotientHOneData.length ≤
        torsionLength + D.quotientFactor.hZeroLength) :
    Module.finrank ℤ A = 0 := by
  let kernelHOneData :=
    D.multiplicativeKernelFppfHOneCertifiedDataInt hkernelFactor hp2
  apply D.finrank_eq_zero_of_fppfKummer_int torsionLength hkernel
    middleHZeroData kernelHOneData quotientHOneData kummer hkummer hp2
  rw [multiplicativeKernelFppfHOneCertifiedDataInt_length,
    D.kernelFactor.hZeroLength_eq_zero_of_isMultiplicative hkernelFactor]
  simpa only [Nat.add_zero, Nat.zero_add] using hbound

/-- Genuine five-primary integral multiplicative-kernel Kummer rank-zero endpoint. -/
theorem finrank_eq_zero_of_fppfKummer_multiplicativeKernelIntAtFive
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : AdmissibleFiltrationStep ℤ 5 G)
    (hkernelFactor : D.kernelFactor.IsMultiplicative)
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) 5).ker =
      5 ^ torsionLength)
    (middleHZeroData : FinitePGroup.CertifiedData 5 (BasePoint G))
    (quotientHOneData : FinitePGroup.CertifiedData 5
      D.quotient.FppfHOne.{0})
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) 5).range) →*
        G.FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hbound :
      middleHZeroData.length + quotientHOneData.length ≤
        torsionLength + D.quotientFactor.hZeroLength) :
    Module.finrank ℤ A = 0 :=
  D.finrank_eq_zero_of_fppfKummer_multiplicativeKernelInt hkernelFactor
    torsionLength hkernel middleHZeroData quotientHOneData kummer hkummer
    (by decide) hbound

/-- Genuine eleven-primary integral multiplicative-kernel Kummer rank-zero endpoint. -/
theorem finrank_eq_zero_of_fppfKummer_multiplicativeKernelIntAtEleven
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : AdmissibleFiltrationStep ℤ 11 G)
    (hkernelFactor : D.kernelFactor.IsMultiplicative)
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) 11).ker =
      11 ^ torsionLength)
    (middleHZeroData : FinitePGroup.CertifiedData 11 (BasePoint G))
    (quotientHOneData : FinitePGroup.CertifiedData 11
      D.quotient.FppfHOne.{0})
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) 11).range) →*
        G.FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hbound :
      middleHZeroData.length + quotientHOneData.length ≤
        torsionLength + D.quotientFactor.hZeroLength) :
    Module.finrank ℤ A = 0 :=
  D.finrank_eq_zero_of_fppfKummer_multiplicativeKernelInt hkernelFactor
    torsionLength hkernel middleHZeroData quotientHOneData kummer hkummer
    (by decide) hbound

end AdmissibleFiltrationStep

end AlgebraicGeometry.FiniteFlatCommGroupScheme

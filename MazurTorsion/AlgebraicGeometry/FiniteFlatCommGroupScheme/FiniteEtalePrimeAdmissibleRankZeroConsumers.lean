/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FiniteEtalePrimeGroupSchemeConstant
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.MultiplicativeIntegralHOneRankZeroConsumers

/-!
# Finite-etale quotient admissible rank-zero consumers

An actual fppf quotient presentation with multiplicative kernel and finite-etale prime-order
quotient is an admissible filtration step: the kernel factor remains an explicit `mu_p`
isomorphism, while finite etaleness and constant order construct the quotient's constant-factor
isomorphism.  The resulting steps feed the genuine integral Kummer rank-zero endpoints at five
and eleven.

Quotient fppf-`H¹`, middle `H⁰`, Mordell--Weil torsion, and Kummer injectivity remain explicit.
No Raynaud extension theorem, Neron comparison, or quotient-cohomology vanishing is asserted.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

universe u

namespace FppfQuotientPresentation

/-- A raw quotient presentation with an actual multiplicative kernel and finite-etale
prime-order quotient is an admissible filtration step. -/
noncomputable def admissibleStepOfMultiplicativeKernelFiniteEtalePrimeQuotientInt
    {p : ℕ} [NeZero p]
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G) (hp : p.Prime)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme ℤ p)
    (hEtale : Etale D.quotient.structureMap)
    (horder : D.quotient.HasConstantOrder p) :
    AdmissibleFiltrationStep ℤ p G where
  toFppfQuotientPresentation := D
  prime := hp
  kernelFactor := .multiplicative kernelIso
  quotientFactor :=
    admissibleSimpleFactorOfFiniteEtalePrimeInt D.quotient hp hEtale horder

@[simp]
theorem admissibleStepOfMultiplicativeKernelFiniteEtalePrimeQuotientInt_quotientLength
    {p : ℕ} [NeZero p]
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G) (hp : p.Prime)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme ℤ p)
    (hEtale : Etale D.quotient.structureMap)
    (horder : D.quotient.HasConstantOrder p) :
    (D.admissibleStepOfMultiplicativeKernelFiniteEtalePrimeQuotientInt
      hp kernelIso hEtale horder).quotientFactor.hZeroLength = 1 :=
  rfl

/-- The actual order-five finite-etale quotient supplies the constant factor in a
multiplicative-kernel admissible step and reaches the integral Kummer rank-zero endpoint. -/
theorem finrank_eq_zero_of_fppfKummer_multiplicativeKernel_finiteEtaleQuotientIntAtFive
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme ℤ 5)
    (hEtale : Etale D.quotient.structureMap)
    (horder : D.quotient.HasConstantOrder 5)
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) 5).ker =
      5 ^ torsionLength)
    (middleHZeroData : FinitePGroup.CertifiedData 5 (BasePoint G))
    (quotientHOneData : FinitePGroup.CertifiedData 5
      D.quotient.FppfHOne.{0})
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) 5).range) →* G.FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hbound : middleHZeroData.length + quotientHOneData.length ≤
      torsionLength + 1) :
    Module.finrank ℤ A = 0 := by
  let step :=
    D.admissibleStepOfMultiplicativeKernelFiniteEtalePrimeQuotientInt
      (by decide) kernelIso hEtale horder
  apply step.finrank_eq_zero_of_fppfKummer_multiplicativeKernelIntAtFive
    (by trivial) torsionLength hkernel middleHZeroData quotientHOneData
      kummer hkummer
  simpa [step] using hbound

/-- The actual order-eleven finite-etale quotient supplies the constant factor in a
multiplicative-kernel admissible step and reaches the integral Kummer rank-zero endpoint. -/
theorem finrank_eq_zero_of_fppfKummer_multiplicativeKernel_finiteEtaleQuotientIntAtEleven
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme ℤ 11)
    (hEtale : Etale D.quotient.structureMap)
    (horder : D.quotient.HasConstantOrder 11)
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) 11).ker =
      11 ^ torsionLength)
    (middleHZeroData : FinitePGroup.CertifiedData 11 (BasePoint G))
    (quotientHOneData : FinitePGroup.CertifiedData 11
      D.quotient.FppfHOne.{0})
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) 11).range) →* G.FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hbound : middleHZeroData.length + quotientHOneData.length ≤
      torsionLength + 1) :
    Module.finrank ℤ A = 0 := by
  let step :=
    D.admissibleStepOfMultiplicativeKernelFiniteEtalePrimeQuotientInt
      (by decide) kernelIso hEtale horder
  apply step.finrank_eq_zero_of_fppfKummer_multiplicativeKernelIntAtEleven
    (by trivial) torsionLength hkernel middleHZeroData quotientHOneData
      kummer hkummer
  simpa [step] using hbound

end FppfQuotientPresentation

end AlgebraicGeometry.FiniteFlatCommGroupScheme

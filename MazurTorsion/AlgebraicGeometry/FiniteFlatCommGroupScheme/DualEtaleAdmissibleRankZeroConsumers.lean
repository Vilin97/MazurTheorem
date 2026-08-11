/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.CartierDualEtalePrimeIdentification
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfQuotientIntegralEndpointData

/-!
# Dual-etale admissible and rank-zero consumers

An actual order-`p` kernel with a finite-free affine realization whose Cartier dual is etale is
genuinely isomorphic to `μ_p`.  Together with a finite-etale order-`p` quotient, this constructs an
admissible filtration step.  The checked low-degree fppf Euler sequence then gives an actual
cardinality bound, and the strongest existing integral Mordell--Weil consumers give rank zero
for exponents five and eleven.

The quotient presentation, both order laws, kernel-dual etaleness, quotient etaleness, and the
quotient global fppf-`H¹` data remain explicit.  The rank-zero endpoints also keep the ambient
Mordell--Weil comparison, fppf properties of multiplication, and actual power-kernel
identification explicit.  No Oort--Tate/Raynaud, Neron, quotient-cohomology, or torsion premise
is manufactured here.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

open AffineFiniteFreeCommGroupScheme

namespace FppfQuotientPresentation

/-- The actual multiplicative kernel isomorphism produced from prime order and etaleness of the
Cartier dual of any finite-free affine realization. -/
def kernelIsoMuOfRealizationCartierDualEtalePrimeInt
    {p : ℕ} [NeZero p]
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (K : AffineFiniteFreeCommGroupScheme ℤ)
    (e : D.kernelPresentation.kernel ≅ K.realize)
    (hp : p.Prime)
    (hkernelOrder : D.kernelPresentation.kernel.HasConstantOrder p)
    (hkernelDualEtale : Etale (cartierDual K).realize.structureMap) :
    D.kernelPresentation.kernel ≅ muScheme ℤ p :=
  isoMuOfRealizationCartierDualEtalePrimeInt
    D.kernelPresentation.kernel K e p hp hkernelOrder hkernelDualEtale

/-- A quotient with dual-etale prime-order kernel and finite-etale prime-order quotient is an
actual admissible filtration step. -/
def admissibleStepOfCartierDualEtaleKernelFiniteEtalePrimeQuotientInt
    {p : ℕ} [NeZero p]
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (K : AffineFiniteFreeCommGroupScheme ℤ)
    (e : D.kernelPresentation.kernel ≅ K.realize)
    (hp : p.Prime)
    (hkernelOrder : D.kernelPresentation.kernel.HasConstantOrder p)
    (hkernelDualEtale : Etale (cartierDual K).realize.structureMap)
    (hEtale : Etale D.quotient.structureMap)
    (horder : D.quotient.HasConstantOrder p) :
    AdmissibleFiltrationStep ℤ p G :=
  D.admissibleStepOfMultiplicativeKernelFiniteEtalePrimeQuotientInt hp
    (D.kernelIsoMuOfRealizationCartierDualEtalePrimeInt
      K e hp hkernelOrder hkernelDualEtale)
    hEtale horder

/-- The actual low-degree fppf Euler bound for a dual-etale multiplicative kernel and a
finite-etale prime-order quotient. -/
theorem
    fppfHOne_natCard_le_prime_of_realizationCartierDualEtaleKernel_finiteEtalePrimeQuotientInt
    {p : ℕ} [NeZero p]
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (K : AffineFiniteFreeCommGroupScheme ℤ)
    (e : D.kernelPresentation.kernel ≅ K.realize)
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hkernelOrder : D.kernelPresentation.kernel.HasConstantOrder p)
    (hkernelDualEtale : Etale (cartierDual K).realize.structureMap)
    (hEtale : Etale D.quotient.structureMap)
    (horder : D.quotient.HasConstantOrder p)
    (quotientHOneData : FinitePGroup.CertifiedData p
      D.quotient.FppfHOne.{0})
    (hquotient : quotientHOneData.length ≤ 1) :
    Nat.card G.FppfHOne.{0} ≤ p := by
  let kernelIso : D.kernelPresentation.kernel ≅ muScheme ℤ p :=
    D.kernelIsoMuOfRealizationCartierDualEtalePrimeInt
      K e hp hkernelOrder hkernelDualEtale
  let step : AdmissibleFiltrationStep ℤ p G :=
    D.admissibleStepOfCartierDualEtaleKernelFiniteEtalePrimeQuotientInt
      K e hp hkernelOrder hkernelDualEtale hEtale horder
  have hkernelFactor : step.kernelFactor.IsMultiplicative := by
    trivial
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hlength :
      (D.middleBasePointCertifiedDataOfMuKernelFiniteEtalePrimeQuotientInt
          kernelIso hp hp2 hEtale horder).length +
        (step.multiplicativeKernelFppfHOneCertifiedDataInt
          hkernelFactor hp2).length + quotientHOneData.length ≤
      1 + (D.kernelBasePointCertifiedDataOfIsoMuInt kernelIso hodd).length +
        (finiteEtaleBasePointCertifiedDataInt
          D.quotient p hEtale horder).length := by
    rw [middleBasePointCertifiedDataOfMuKernelFiniteEtalePrimeQuotientInt_length,
      AdmissibleFiltrationStep.multiplicativeKernelFppfHOneCertifiedDataInt_length,
      kernelBasePointCertifiedDataOfIsoMuInt_length,
      finiteEtaleBasePointCertifiedDataInt_length]
    simpa only [Nat.add_zero] using Nat.add_le_add_left hquotient 1
  simpa only [pow_one] using
    FppfLowDegreeExactSequence.fppfHOne_natCard_le_pow_ofFppfQuotientPresentation
      D (D.kernelBasePointCertifiedDataOfIsoMuInt kernelIso hodd)
      (D.middleBasePointCertifiedDataOfMuKernelFiniteEtalePrimeQuotientInt
        kernelIso hp hp2 hEtale horder)
      (finiteEtaleBasePointCertifiedDataInt D.quotient p hEtale horder)
      (step.multiplicativeKernelFppfHOneCertifiedDataInt hkernelFactor hp2)
      quotientHOneData hp 1 hlength

/-- Integral order-five Euler endpoint. -/
theorem
    fppfHOne_natCard_le_five_of_realizationCartierDualEtaleKernel_finiteEtaleQuotientInt
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (K : AffineFiniteFreeCommGroupScheme ℤ)
    (e : D.kernelPresentation.kernel ≅ K.realize)
    (hkernelOrder : D.kernelPresentation.kernel.HasConstantOrder 5)
    (hkernelDualEtale : Etale (cartierDual K).realize.structureMap)
    (hEtale : Etale D.quotient.structureMap)
    (horder : D.quotient.HasConstantOrder 5)
    (quotientHOneData : FinitePGroup.CertifiedData 5
      D.quotient.FppfHOne.{0})
    (hquotient : quotientHOneData.length ≤ 1) :
    Nat.card G.FppfHOne.{0} ≤ 5 :=
  D.fppfHOne_natCard_le_prime_of_realizationCartierDualEtaleKernel_finiteEtalePrimeQuotientInt
    K e (by decide) (by decide) hkernelOrder hkernelDualEtale hEtale horder
      quotientHOneData hquotient

/-- Integral order-eleven Euler endpoint. -/
theorem
    fppfHOne_natCard_le_eleven_of_realizationCartierDualEtaleKernel_finiteEtaleQuotientInt
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (K : AffineFiniteFreeCommGroupScheme ℤ)
    (e : D.kernelPresentation.kernel ≅ K.realize)
    (hkernelOrder : D.kernelPresentation.kernel.HasConstantOrder 11)
    (hkernelDualEtale : Etale (cartierDual K).realize.structureMap)
    (hEtale : Etale D.quotient.structureMap)
    (horder : D.quotient.HasConstantOrder 11)
    (quotientHOneData : FinitePGroup.CertifiedData 11
      D.quotient.FppfHOne.{0})
    (hquotient : quotientHOneData.length ≤ 1) :
    Nat.card G.FppfHOne.{0} ≤ 11 :=
  D.fppfHOne_natCard_le_prime_of_realizationCartierDualEtaleKernel_finiteEtalePrimeQuotientInt
    K e (by decide) (by decide) hkernelOrder hkernelDualEtale hEtale horder
      quotientHOneData hquotient

/-- The strongest current order-five integral Mordell--Weil endpoint, with the multiplicative
kernel isomorphism derived from dual etaleness. -/
theorem
    finrank_eq_zero_of_powerKernel_mordellWeilIntAtFive_of_dualEtaleKernel
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (K : AffineFiniteFreeCommGroupScheme ℤ)
    (e : D.kernelPresentation.kernel ≅ K.realize)
    (hkernelOrder : D.kernelPresentation.kernel.HasConstantOrder 5)
    (hkernelDualEtale : Etale (cartierDual K).realize.structureMap)
    (hEtale : Etale D.quotient.structureMap)
    (horder : D.quotient.HasConstantOrder 5)
    (B : CommGroupScheme (Spec (.of ℤ)))
    {A : Type} [AddCommGroup A] [AddGroup.FG A]
    (mordellWeilEquiv : A ≃+ Additive (CommGroupScheme.BasePoint B))
    (hflat : Flat (CommGroupScheme.underlyingHom
      (CommGroupScheme.powerEnd B 5)))
    (hsurjective : Surjective (CommGroupScheme.underlyingHom
      (CommGroupScheme.powerEnd B 5)))
    (hlfp : LocallyOfFinitePresentation (CommGroupScheme.underlyingHom
      (CommGroupScheme.powerEnd B 5)))
    (powerKernelIso : G.toCommGroupScheme ≅
      CommGroupScheme.kernel (CommGroupScheme.powerEnd B 5))
    (quotientHOneData : FinitePGroup.CertifiedData 5
      D.quotient.FppfHOne.{0})
    (hbound : quotientHOneData.length ≤ 1) :
    Module.finrank ℤ A = 0 := by
  let kernelIso := isoMuFiveOfRealizationCartierDualEtaleInt
    D.kernelPresentation.kernel K e hkernelOrder hkernelDualEtale
  exact
    D.finrank_eq_zero_of_powerKernel_mordellWeilIntAtFive_of_muKernel_finiteEtaleQuotient
      kernelIso hEtale horder B mordellWeilEquiv hflat hsurjective hlfp
        powerKernelIso quotientHOneData hbound

/-- The strongest current order-eleven integral Mordell--Weil endpoint, with the multiplicative
kernel isomorphism derived from dual etaleness. -/
theorem
    finrank_eq_zero_of_powerKernel_mordellWeilIntAtEleven_of_dualEtaleKernel
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (K : AffineFiniteFreeCommGroupScheme ℤ)
    (e : D.kernelPresentation.kernel ≅ K.realize)
    (hkernelOrder : D.kernelPresentation.kernel.HasConstantOrder 11)
    (hkernelDualEtale : Etale (cartierDual K).realize.structureMap)
    (hEtale : Etale D.quotient.structureMap)
    (horder : D.quotient.HasConstantOrder 11)
    (B : CommGroupScheme (Spec (.of ℤ)))
    {A : Type} [AddCommGroup A] [AddGroup.FG A]
    (mordellWeilEquiv : A ≃+ Additive (CommGroupScheme.BasePoint B))
    (hflat : Flat (CommGroupScheme.underlyingHom
      (CommGroupScheme.powerEnd B 11)))
    (hsurjective : Surjective (CommGroupScheme.underlyingHom
      (CommGroupScheme.powerEnd B 11)))
    (hlfp : LocallyOfFinitePresentation (CommGroupScheme.underlyingHom
      (CommGroupScheme.powerEnd B 11)))
    (powerKernelIso : G.toCommGroupScheme ≅
      CommGroupScheme.kernel (CommGroupScheme.powerEnd B 11))
    (quotientHOneData : FinitePGroup.CertifiedData 11
      D.quotient.FppfHOne.{0})
    (hbound : quotientHOneData.length ≤ 1) :
    Module.finrank ℤ A = 0 := by
  let kernelIso := isoMuElevenOfRealizationCartierDualEtaleInt
    D.kernelPresentation.kernel K e hkernelOrder hkernelDualEtale
  exact
    D.finrank_eq_zero_of_powerKernel_mordellWeilIntAtEleven_of_muKernel_finiteEtaleQuotient
      kernelIso hEtale horder B mordellWeilEquiv hflat hsurjective hlfp
        powerKernelIso quotientHOneData hbound

end FppfQuotientPresentation

end AlgebraicGeometry.FiniteFlatCommGroupScheme

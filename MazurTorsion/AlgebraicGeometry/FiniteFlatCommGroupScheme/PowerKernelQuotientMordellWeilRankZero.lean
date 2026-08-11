/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.CommGroupSchemePowerKummerTorsionRankZero
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FiniteEtalePrimeAdmissibleRankZeroConsumers

/-!
# Quotient propagation to the actual Mordell--Weil power kernel

Endpoint bounds in an actual finite-flat fppf quotient propagate to its middle represented
`H¹`.  If that middle group scheme is genuinely isomorphic to the scheme-theoretic kernel of
multiplication by `p` on an ambient commutative group scheme, the bound transports to the exact
coefficient of the checked power-Kummer boundary.  An explicit comparison of the intended
Mordell--Weil group with ambient global sections then gives rank zero without a caller-supplied
Kummer homomorphism, injectivity proof, or separately restated torsion-cardinality law.

The final theorems consume actual multiplicative-kernel, finite-etale quotient presentations at
five and eleven.  The ambient model, its fppf multiplication law, the Mordell--Weil/global-section
comparison, realization of the finite-flat middle as the actual power kernel, middle global
sections, and quotient `H¹` remain explicit.  Thus no Raynaud extension theorem, Neron model,
quotient-cohomology calculation, or torsion classification is asserted here.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

open CommGroupScheme

universe u

noncomputable local instance powerKernelIsCommMonObjForQuotient
    {S : Scheme.{u}} (G : CommGroupScheme S) (p : ℕ) :
    IsCommMonObj
      (CommGroupScheme.kernelGrp (CommGroupScheme.powerEnd G p)).X :=
  CommGroupScheme.kernelGrp_isComm (CommGroupScheme.powerEnd G p)

noncomputable local instance powerKernelBasePointCommGroupForQuotient
    {S : Scheme.{u}} (G : CommGroupScheme S) (p : ℕ) :
    CommGroup (CommGroupScheme.BasePoint
      (CommGroupScheme.kernel (CommGroupScheme.powerEnd G p))) :=
  CategoryTheory.Hom.commGroup

namespace FppfQuotientPresentation

/-- Endpoint bounds propagate across the actual exact global fppf `H¹` pair of a finite-flat
quotient presentation. -/
noncomputable def middleHOneBoundedDataFromEndpoints
    {S : Scheme.{u}} {p : ℕ} {G : FiniteFlatCommGroupScheme S}
    (D : FppfQuotientPresentation G)
    (kernelHOneData : FinitePGroup.BoundedData p
      D.kernelPresentation.kernel.FppfHOne.{u})
    (quotientHOneData : FinitePGroup.BoundedData p
      D.quotient.FppfHOne.{u}) :
    FinitePGroup.BoundedData p G.FppfHOne.{u} :=
  FinitePGroup.BoundedData.middleOfMulExact kernelHOneData quotientHOneData
    (fppfHOneMap D.kernelPresentation.inclusion) (fppfHOneMap D.project)
    D.exact_fppfHOneMap_inclusion_project

@[simp]
theorem middleHOneBoundedDataFromEndpoints_length
    {S : Scheme.{u}} {p : ℕ} {G : FiniteFlatCommGroupScheme S}
    (D : FppfQuotientPresentation G)
    (kernelHOneData : FinitePGroup.BoundedData p
      D.kernelPresentation.kernel.FppfHOne.{u})
    (quotientHOneData : FinitePGroup.BoundedData p
      D.quotient.FppfHOne.{u}) :
    (D.middleHOneBoundedDataFromEndpoints
      kernelHOneData quotientHOneData).length =
        kernelHOneData.length + quotientHOneData.length :=
  rfl

/-- If the quotient middle is the actual multiplication kernel, its propagated `H¹` bound is
an actual bound on the coefficient of the canonical power-Kummer boundary. -/
noncomputable def powerKernelHOneBoundedDataFromEndpoints
    {S : Scheme.{u}} {p : ℕ} {G : FiniteFlatCommGroupScheme S}
    (D : FppfQuotientPresentation G) (B : CommGroupScheme S)
    (powerKernelIso : G.toCommGroupScheme ≅
      CommGroupScheme.kernel (CommGroupScheme.powerEnd B p))
    (kernelHOneData : FinitePGroup.BoundedData p
      D.kernelPresentation.kernel.FppfHOne.{u})
    (quotientHOneData : FinitePGroup.BoundedData p
      D.quotient.FppfHOne.{u}) :
    FinitePGroup.BoundedData p
      (CommGroupScheme.kernel (CommGroupScheme.powerEnd B p)).FppfHOne.{u} :=
  (D.middleHOneBoundedDataFromEndpoints kernelHOneData quotientHOneData).congr
    (CommGroupScheme.fppfHOneMulEquivOfIso powerKernelIso)

@[simp]
theorem powerKernelHOneBoundedDataFromEndpoints_length
    {S : Scheme.{u}} {p : ℕ} {G : FiniteFlatCommGroupScheme S}
    (D : FppfQuotientPresentation G) (B : CommGroupScheme S)
    (powerKernelIso : G.toCommGroupScheme ≅
      CommGroupScheme.kernel (CommGroupScheme.powerEnd B p))
    (kernelHOneData : FinitePGroup.BoundedData p
      D.kernelPresentation.kernel.FppfHOne.{u})
    (quotientHOneData : FinitePGroup.BoundedData p
      D.quotient.FppfHOne.{u}) :
    (D.powerKernelHOneBoundedDataFromEndpoints B powerKernelIso
      kernelHOneData quotientHOneData).length =
        kernelHOneData.length + quotientHOneData.length :=
  rfl

/-- Quotient endpoint bounds, an actual power-kernel realization, and the actual represented
power boundary force rank zero on a Mordell--Weil carrier identified with ambient global
sections.  The Kummer map, its injectivity, and the torsion equality are all derived. -/
theorem finrank_eq_zero_of_powerKernelQuotient_mordellWeil
    {S : Scheme.{u}} {p : ℕ} (hp : p.Prime)
    {G : FiniteFlatCommGroupScheme S} (D : FppfQuotientPresentation G)
    (B : CommGroupScheme S)
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (mordellWeilEquiv : A ≃+ Additive (CommGroupScheme.BasePoint B))
    (hflat : Flat (CommGroupScheme.underlyingHom
      (CommGroupScheme.powerEnd B p)))
    (hsurjective : Surjective (CommGroupScheme.underlyingHom
      (CommGroupScheme.powerEnd B p)))
    (hlfp : LocallyOfFinitePresentation (CommGroupScheme.underlyingHom
      (CommGroupScheme.powerEnd B p)))
    (powerKernelIso : G.toCommGroupScheme ≅
      CommGroupScheme.kernel (CommGroupScheme.powerEnd B p))
    (middleHZeroData : FinitePGroup.CertifiedData p (BasePoint G))
    (kernelHOneData : FinitePGroup.BoundedData p
      D.kernelPresentation.kernel.FppfHOne.{u})
    (quotientHOneData : FinitePGroup.BoundedData p
      D.quotient.FppfHOne.{u})
    (hbound : kernelHOneData.length + quotientHOneData.length ≤
      middleHZeroData.length) :
    Module.finrank ℤ A = 0 := by
  let pointEquiv := CommGroupScheme.pointMulEquivOfIso powerKernelIso
    (CommGroupScheme.baseObject S)
  let powerKernelHZeroData : FinitePGroup.CertifiedData p
      (CommGroupScheme.BasePoint
        (CommGroupScheme.kernel (CommGroupScheme.powerEnd B p))) := by
    letI : Finite (BasePoint G) := middleHZeroData.finite
    exact
      { finite := Finite.of_equiv (BasePoint G) pointEquiv.toEquiv
        length := middleHZeroData.length
        card_eq := (Nat.card_congr pointEquiv.symm.toEquiv).trans
          middleHZeroData.card_eq }
  let powerKernelHOneData :=
    D.powerKernelHOneBoundedDataFromEndpoints B powerKernelIso
      kernelHOneData quotientHOneData
  apply finrank_eq_zero_of_powerKummer_kernelData_of_basePointEquiv
    hp B mordellWeilEquiv hflat hsurjective hlfp powerKernelHZeroData
      powerKernelHOneData
  simpa [powerKernelHZeroData, powerKernelHOneData] using hbound

end FppfQuotientPresentation

namespace AdmissibleFiltrationStep

/-- For an integral admissible step with multiplicative kernel, quotient `H¹` is the only
cohomological endpoint still needed after identifying the middle with the actual power kernel.
The integral multiplicative `H¹` contribution is genuinely zero. -/
theorem finrank_eq_zero_of_multiplicativeKernel_powerKernel_mordellWeilInt
    {p : ℕ} [NeZero p]
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : AdmissibleFiltrationStep ℤ p G)
    (hkernelFactor : D.kernelFactor.IsMultiplicative)
    (B : CommGroupScheme (Spec (.of ℤ)))
    {A : Type} [AddCommGroup A] [AddGroup.FG A]
    (mordellWeilEquiv : A ≃+ Additive (CommGroupScheme.BasePoint B))
    (hflat : Flat (CommGroupScheme.underlyingHom
      (CommGroupScheme.powerEnd B p)))
    (hsurjective : Surjective (CommGroupScheme.underlyingHom
      (CommGroupScheme.powerEnd B p)))
    (hlfp : LocallyOfFinitePresentation (CommGroupScheme.underlyingHom
      (CommGroupScheme.powerEnd B p)))
    (powerKernelIso : G.toCommGroupScheme ≅
      CommGroupScheme.kernel (CommGroupScheme.powerEnd B p))
    (middleHZeroData : FinitePGroup.CertifiedData p (BasePoint G))
    (quotientHOneData : FinitePGroup.CertifiedData p
      D.quotient.FppfHOne.{0})
    (hp2 : p ≠ 2)
    (hbound : quotientHOneData.length ≤ middleHZeroData.length) :
    Module.finrank ℤ A = 0 := by
  let kernelHOneData :=
    (D.multiplicativeKernelFppfHOneCertifiedDataInt
      hkernelFactor hp2).toBoundedData
  apply D.toFppfQuotientPresentation
    |>.finrank_eq_zero_of_powerKernelQuotient_mordellWeil D.prime B
      mordellWeilEquiv hflat hsurjective hlfp powerKernelIso middleHZeroData
      kernelHOneData quotientHOneData.toBoundedData
  simpa [kernelHOneData] using hbound

end AdmissibleFiltrationStep

namespace FppfQuotientPresentation

/-- An actual multiplicative-kernel, finite-etale order-five quotient that realizes the
scheme-theoretic `[5]`-kernel reaches Mordell--Weil rank zero through the canonical power
boundary. -/
theorem
    finrank_eq_zero_of_multiplicativeKernel_finiteEtaleQuotient_powerKernel_mordellWeilIntAtFive
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme ℤ 5)
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
    (middleHZeroData : FinitePGroup.CertifiedData 5 (BasePoint G))
    (quotientHOneData : FinitePGroup.CertifiedData 5
      D.quotient.FppfHOne.{0})
    (hbound : quotientHOneData.length ≤ middleHZeroData.length) :
    Module.finrank ℤ A = 0 := by
  let step :=
    D.admissibleStepOfMultiplicativeKernelFiniteEtalePrimeQuotientInt
      (by decide) kernelIso hEtale horder
  apply step.finrank_eq_zero_of_multiplicativeKernel_powerKernel_mordellWeilInt
    (by trivial) B mordellWeilEquiv hflat hsurjective hlfp powerKernelIso
      middleHZeroData quotientHOneData (by decide)
  simpa [step] using hbound

/-- The genuine order-eleven counterpart of the actual power-kernel Mordell--Weil endpoint. -/
theorem
    finrank_eq_zero_of_multiplicativeKernel_finiteEtaleQuotient_powerKernel_mordellWeilIntAtEleven
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme ℤ 11)
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
    (middleHZeroData : FinitePGroup.CertifiedData 11 (BasePoint G))
    (quotientHOneData : FinitePGroup.CertifiedData 11
      D.quotient.FppfHOne.{0})
    (hbound : quotientHOneData.length ≤ middleHZeroData.length) :
    Module.finrank ℤ A = 0 := by
  let step :=
    D.admissibleStepOfMultiplicativeKernelFiniteEtalePrimeQuotientInt
      (by decide) kernelIso hEtale horder
  apply step.finrank_eq_zero_of_multiplicativeKernel_powerKernel_mordellWeilInt
    (by trivial) B mordellWeilEquiv hflat hsurjective hlfp powerKernelIso
      middleHZeroData quotientHOneData (by decide)
  simpa [step] using hbound

end FppfQuotientPresentation

end AlgebraicGeometry.FiniteFlatCommGroupScheme

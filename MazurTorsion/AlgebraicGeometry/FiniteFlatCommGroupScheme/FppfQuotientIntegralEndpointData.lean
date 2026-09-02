/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.PowerKernelQuotientMordellWeilRankZero

/-!
# Integral degree-zero data from an actual fppf quotient

For an actual finite-flat fppf quotient, triviality of the kernel's represented global `H¹`
forces every quotient-valued global point to lift: the genuine connecting class is trivial, and
the checked low-degree exactness theorem glues its local lifts.  Pointwise exactness at the
middle then gives the exact product formula for global-point cardinalities.  Thus finite
`p`-power data on the kernel and quotient construct, rather than assume, the middle `H⁰` data.

For an integral multiplicative kernel the required `H¹` triviality is the proved fppf Kummer
calculation for the actual `mu_p` model.  A finite-etale prime-order quotient supplies its actual
integral `H⁰` data.  The resulting length-one middle certificate feeds the order-five and
order-eleven power-kernel Mordell--Weil endpoints without a caller-supplied middle `H⁰`
certificate.

Quotient `H¹`, the ambient Neron/global-section comparison, realization as the actual power
kernel, and the fppf laws for multiplication remain explicit.  No quotient-cohomology, Neron,
Raynaud, or torsion theorem is manufactured here.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

open CommGroupScheme
open CommGroupScheme.MultiplicativeCocycleDescent.FiniteAffineFamilyEffectivity

universe u

namespace FppfQuotientPresentation

/-- If every represented kernel `H¹` class is trivial, the actual quotient projection is
surjective on global represented points. -/
theorem basePointProject_surjective_of_kernelHOne_eq_one
    {S : Scheme.{u}} {G : FiniteFlatCommGroupScheme S}
    (D : FppfQuotientPresentation G)
    (hkernelHOne :
      ∀ z : D.kernelPresentation.kernel.FppfHOne.{u}, z = 1) :
    Function.Surjective (mapPoint D.project (baseObject S)) := by
  intro q
  exact D.exists_project_of_boundaryHom_eq_one q (hkernelHOne (D.boundaryHom q))

/-- Exact cardinality of the global points in an actual quotient with trivial kernel `H¹`.
The middle's finiteness is derived from pointwise exactness and finite endpoint groups. -/
theorem basePoint_natCard_eq_mul_of_kernelHOne_eq_one
    {S : Scheme.{u}} {G : FiniteFlatCommGroupScheme S}
    (D : FppfQuotientPresentation G)
    [Finite (BasePoint D.kernelPresentation.kernel)]
    [Finite (BasePoint D.quotient)]
    (hkernelHOne :
      ∀ z : D.kernelPresentation.kernel.FppfHOne.{u}, z = 1) :
    Nat.card (BasePoint G) =
      Nat.card (BasePoint D.kernelPresentation.kernel) *
        Nat.card (BasePoint D.quotient) := by
  let i := mapPoint D.kernelPresentation.inclusion (baseObject S)
  let q := mapPoint D.project (baseObject S)
  letI : Finite (BasePoint G) :=
    FppfLowDegreeExactSequence.finite_middle_of_mulExact i q
      (D.kernelPresentation.point_mulExact (baseObject S))
  have hcardRange :
      Nat.card (BasePoint G) = Nat.card i.range * Nat.card q.range := by
    calc
      Nat.card (BasePoint G) = Nat.card q.ker * q.ker.index :=
        q.ker.card_mul_index.symm
      _ = Nat.card i.range * Nat.card q.range := by
        rw [Subgroup.index_ker q,
          (D.kernelPresentation.point_mulExact
            (baseObject S)).monoidHom_ker_eq]
  have hiCard :
      Nat.card i.range = Nat.card (BasePoint D.kernelPresentation.kernel) := by
    symm
    exact Nat.card_congr
      (Equiv.ofInjective i
        (D.kernelPresentation.inclusion_point_injective (baseObject S)))
  have hqSurjective : Function.Surjective q :=
    D.basePointProject_surjective_of_kernelHOne_eq_one hkernelHOne
  have hqRange : q.range = ⊤ := MonoidHom.range_eq_top.mpr hqSurjective
  have hqCard : Nat.card q.range = Nat.card (BasePoint D.quotient) := by
    rw [hqRange]
    exact Subgroup.card_top
  rw [hcardRange, hiCard, hqCard]

/-- Actual middle global-point `p`-power data, constructed from endpoint data and triviality of
the represented kernel `H¹`. -/
noncomputable def middleBasePointCertifiedDataOfKernelHOneEqOne
    {S : Scheme.{u}} {p : ℕ} {G : FiniteFlatCommGroupScheme S}
    (D : FppfQuotientPresentation G)
    (kernelHZeroData : FinitePGroup.CertifiedData p
      (BasePoint D.kernelPresentation.kernel))
    (quotientHZeroData : FinitePGroup.CertifiedData p
      (BasePoint D.quotient))
    (hkernelHOne :
      ∀ z : D.kernelPresentation.kernel.FppfHOne.{u}, z = 1) :
    FinitePGroup.CertifiedData p (BasePoint G) := by
  letI : Finite (BasePoint D.kernelPresentation.kernel) :=
    kernelHZeroData.finite
  letI : Finite (BasePoint D.quotient) := quotientHZeroData.finite
  letI : Finite (BasePoint G) :=
    FppfLowDegreeExactSequence.finite_middle_of_mulExact
      (mapPoint D.kernelPresentation.inclusion (baseObject S))
      (mapPoint D.project (baseObject S))
      (D.kernelPresentation.point_mulExact (baseObject S))
  exact
    { finite := inferInstance
      length := kernelHZeroData.length + quotientHZeroData.length
      card_eq := by
        rw [D.basePoint_natCard_eq_mul_of_kernelHOne_eq_one hkernelHOne,
          kernelHZeroData.card_eq, quotientHZeroData.card_eq, pow_add] }

@[simp]
theorem middleBasePointCertifiedDataOfKernelHOneEqOne_length
    {S : Scheme.{u}} {p : ℕ} {G : FiniteFlatCommGroupScheme S}
    (D : FppfQuotientPresentation G)
    (kernelHZeroData : FinitePGroup.CertifiedData p
      (BasePoint D.kernelPresentation.kernel))
    (quotientHZeroData : FinitePGroup.CertifiedData p
      (BasePoint D.quotient))
    (hkernelHOne :
      ∀ z : D.kernelPresentation.kernel.FppfHOne.{u}, z = 1) :
    (D.middleBasePointCertifiedDataOfKernelHOneEqOne kernelHZeroData
      quotientHZeroData hkernelHOne).length =
        kernelHZeroData.length + quotientHZeroData.length :=
  rfl

/-! ### Integral multiplicative kernels -/

/-- An actual kernel identified with integral `mu_p` has trivial represented global `H¹` for
odd `p`. -/
theorem kernelFppfHOne_eq_one_of_isoMuInt
    {p : ℕ} [NeZero p]
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme ℤ p)
    (hodd : Odd p)
    (z : D.kernelPresentation.kernel.FppfHOne.{0}) : z = 1 := by
  let e := CommGroupScheme.fppfHOneMulEquivOfIso
    ((finiteFlatCommGroupSchemeProperty _).ι.mapIso kernelIso)
  apply e.injective
  calc
    e z = 1 := muSchemeFppfHOne_int_eq_one_of_odd p hodd (e z)
    _ = e 1 := (map_one e).symm

/-- The actual integral global points of a kernel identified with `mu_p` have length zero. -/
noncomputable def kernelBasePointCertifiedDataOfIsoMuInt
    {p : ℕ} [NeZero p]
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme ℤ p)
    (hodd : Odd p) :
    FinitePGroup.CertifiedData p
      (BasePoint D.kernelPresentation.kernel) :=
  (muBasePointCertifiedDataIntOfOdd p hodd).congr
    (pointMulEquivOfIso kernelIso (baseObject (Spec (.of ℤ)))).symm

@[simp]
theorem kernelBasePointCertifiedDataOfIsoMuInt_length
    {p : ℕ} [NeZero p]
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme ℤ p)
    (hodd : Odd p) :
    (D.kernelBasePointCertifiedDataOfIsoMuInt kernelIso hodd).length = 0 :=
  rfl

/-- A multiplicative-kernel integral quotient constructs its middle global-point data from the
actual quotient global-point data; no middle certificate is an input. -/
noncomputable def middleBasePointCertifiedDataOfMuKernelInt
    {p : ℕ} [NeZero p]
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme ℤ p)
    (hodd : Odd p)
    (quotientHZeroData : FinitePGroup.CertifiedData p
      (BasePoint D.quotient)) :
    FinitePGroup.CertifiedData p (BasePoint G) :=
  D.middleBasePointCertifiedDataOfKernelHOneEqOne
    (D.kernelBasePointCertifiedDataOfIsoMuInt kernelIso hodd)
    quotientHZeroData (D.kernelFppfHOne_eq_one_of_isoMuInt kernelIso hodd)

@[simp]
theorem middleBasePointCertifiedDataOfMuKernelInt_length
    {p : ℕ} [NeZero p]
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme ℤ p)
    (hodd : Odd p)
    (quotientHZeroData : FinitePGroup.CertifiedData p
      (BasePoint D.quotient)) :
    (D.middleBasePointCertifiedDataOfMuKernelInt kernelIso hodd
      quotientHZeroData).length = quotientHZeroData.length := by
  change 0 + quotientHZeroData.length = quotientHZeroData.length
  exact Nat.zero_add _

/-- A finite-etale prime-order quotient supplies the remaining actual integral `H⁰` endpoint;
the resulting middle power kernel has exactly `p` global points. -/
noncomputable def
    middleBasePointCertifiedDataOfMuKernelFiniteEtalePrimeQuotientInt
    {p : ℕ} [NeZero p]
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme ℤ p)
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hEtale : Etale D.quotient.structureMap)
    (horder : D.quotient.HasConstantOrder p) :
    FinitePGroup.CertifiedData p (BasePoint G) :=
  D.middleBasePointCertifiedDataOfMuKernelInt kernelIso
    (hp.odd_of_ne_two hp2)
    (finiteEtaleBasePointCertifiedDataInt D.quotient p hEtale horder)

@[simp]
theorem
    middleBasePointCertifiedDataOfMuKernelFiniteEtalePrimeQuotientInt_length
    {p : ℕ} [NeZero p]
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme ℤ p)
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hEtale : Etale D.quotient.structureMap)
    (horder : D.quotient.HasConstantOrder p) :
    (D.middleBasePointCertifiedDataOfMuKernelFiniteEtalePrimeQuotientInt
      kernelIso hp hp2 hEtale horder).length = 1 := by
  rfl

/-! ### Five- and eleven-primary power-kernel consumers -/

/-- At five, actual integral endpoint data remove the middle-`H⁰`, torsion-cardinality, and
Kummer-injectivity premises from the finite-etale quotient rank-zero endpoint. -/
theorem finrank_eq_zero_of_powerKernel_mordellWeilIntAtFive_of_muKernel_finiteEtaleQuotient
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
    (quotientHOneData : FinitePGroup.CertifiedData 5
      D.quotient.FppfHOne.{0})
    (hbound : quotientHOneData.length ≤ 1) :
    Module.finrank ℤ A = 0 := by
  apply D.finrank_eq_zero_of_multiplicativeKernel_finiteEtaleQuotient_powerKernel_mordellWeilIntAtFive
    kernelIso hEtale horder B mordellWeilEquiv hflat hsurjective hlfp
      powerKernelIso
      (D.middleBasePointCertifiedDataOfMuKernelFiniteEtalePrimeQuotientInt
        kernelIso (by decide) (by decide) hEtale horder)
      quotientHOneData
  simpa using hbound

/-- The corresponding actual endpoint-data theorem at eleven. -/
theorem
    finrank_eq_zero_of_powerKernel_mordellWeilIntAtEleven_of_muKernel_finiteEtaleQuotient
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
    (quotientHOneData : FinitePGroup.CertifiedData 11
      D.quotient.FppfHOne.{0})
    (hbound : quotientHOneData.length ≤ 1) :
    Module.finrank ℤ A = 0 := by
  apply D.finrank_eq_zero_of_multiplicativeKernel_finiteEtaleQuotient_powerKernel_mordellWeilIntAtEleven
    kernelIso hEtale horder B mordellWeilEquiv hflat hsurjective hlfp
      powerKernelIso
      (D.middleBasePointCertifiedDataOfMuKernelFiniteEtalePrimeQuotientInt
        kernelIso (by decide) (by decide) hEtale horder)
      quotientHOneData
  simpa using hbound

end FppfQuotientPresentation

end AlgebraicGeometry.FiniteFlatCommGroupScheme

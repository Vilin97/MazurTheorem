/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FiniteEtaleIntAlgebraClassification
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FiniteFlatAffineRealizationExistence
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.AdmissibleClosedFiberConnectedEtale
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.ElementaryGlobalSections
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfKummerRankZero

/-!
# Integral points of finite-etale prime-order group schemes

This file upgrades the arithmetic classification of finite-etale integer algebras to an actual
degree-zero statement for represented finite-flat commutative group schemes.  A finite-etale
group scheme over `Spec ℤ` of constant order `p` has exactly `p` integral points.  The resulting
`FinitePGroup.CertifiedData` is consumed by the fppf low-degree Euler estimate.

No local Oort--Tate classification, Raynaud extension theorem, Neron comparison, or global
fppf-`H¹` vanishing is asserted here.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

universe u

namespace ConstantPrimeEtale

/-- Over a nonzero domain, evaluations at distinct coordinates of a finite product are
distinct algebra maps. -/
private theorem evalAlgHom_injective (n : ℕ) :
    Function.Injective (Pi.evalAlgHom ℤ (fun _ : Fin n ↦ ℤ)) := by
  classical
  intro i j hij
  by_contra hne
  let δ : Fin n → ℤ := fun k ↦ if k = i then 1 else 0
  have hδ := DFunLike.congr_fun hij δ
  change δ i = δ j at hδ
  have hji : j = i := by simpa [δ] using hδ
  exact hne hji.symm

/-- Algebra maps out of an integer algebra already identified with a finite product are exactly
evaluations at the product components. -/
noncomputable def algHomEquivFinOfAlgEquiv
    (B : Type u) [CommRing B] [Algebra ℤ B] (n : ℕ)
    (e : B ≃ₐ[ℤ] (Fin n → ℤ)) :
    (B →ₐ[ℤ] ℤ) ≃ Fin n := by
  let evaluation : Fin n → (B →ₐ[ℤ] ℤ) :=
    fun i ↦ (Pi.evalAlgHom ℤ (fun _ : Fin n ↦ ℤ) i).comp
      e.toAlgHom
  refine (Equiv.ofBijective evaluation ⟨?_, ?_⟩).symm
  · intro i j hij
    apply evalAlgHom_injective n
    apply AlgHom.ext
    intro x
    have hx := DFunLike.congr_fun hij (e.symm x)
    simpa [evaluation] using hx
  · intro f
    obtain ⟨i, hi⟩ := AlgHom.eq_piEvalAlgHom (f.comp e.symm.toAlgHom)
    refine ⟨i, ?_⟩
    apply AlgHom.ext
    intro x
    have hx := DFunLike.congr_fun hi (e x)
    simpa [evaluation] using hx.symm

end ConstantPrimeEtale

/-- Integral represented points of a finite-etale group scheme of constant order `p` are
noncanonically enumerable by `Fin p`.  The construction first recovers actual affine Hopf
coordinates, then uses the arithmetic product decomposition of their finite-etale coordinate
algebra. -/
noncomputable def finiteEtaleBasePointEquivFin
    (Q : FiniteFlatCommGroupScheme (Spec (.of ℤ))) (p : ℕ)
    (hEtale : Etale Q.structureMap) (horder : Q.HasConstantOrder p) :
    BasePoint Q ≃ Fin p := by
  let hrealize := exists_affineFiniteFlat_realization Q
  let A := hrealize.choose
  let e : Q ≅ A.realize := hrealize.choose_spec.some
  letI hFiniteAlg :
      @Module.Finite ℤ A.coordinates _ _ Algebra.toModule := A.property.1
  letI hFlatAlg :
      @Module.Flat ℤ A.coordinates _ _ Algebra.toModule := A.property.2
  have hModule : (Algebra.toModule : Module ℤ A.coordinates) =
      AddCommGroup.toIntModule A.coordinates := Subsingleton.elim _ _
  letI : Module.Finite ℤ A.coordinates := hModule ▸ hFiniteAlg
  letI : Module.Flat ℤ A.coordinates := hModule ▸ hFlatAlg
  letI : Module.IsTorsionFree ℤ A.coordinates := Module.Flat.isTorsionFree
  letI : Module.Free ℤ A.coordinates := Module.free_of_finite_type_torsion_free'
  have hAEtale : Etale A.realize.structureMap :=
    etale_structureMap_of_iso e.symm hEtale
  letI hEtaleAlg : Algebra.Etale ℤ A.coordinates := by
    change Etale
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ A.coordinates))) at hAEtale
    rw [HasRingHomProperty.Spec_iff (P := @Etale)] at hAEtale
    exact RingHom.etale_algebraMap.mp hAEtale
  have hAlgebra : (inferInstance : Algebra ℤ A.coordinates) =
      Ring.toIntAlgebra A.coordinates := Subsingleton.elim _ _
  letI : @Algebra.Etale ℤ A.coordinates _ _ (Ring.toIntAlgebra A.coordinates) :=
    hAlgebra ▸ hEtaleAlg
  have hAOrder : A.realize.HasConstantOrder p := by
    change A.realize.orderAt = Function.const (Spec (.of ℤ)) p
    rw [← orderAt_eq_of_iso e]
    exact horder
  let s : Spec (.of ℤ) := Classical.choice inferInstance
  have hs : A.realize.orderAt s = p := by
    simpa [HasConstantOrder] using congrFun hAOrder s
  have hrank : Module.finrank ℤ A.coordinates = p := by
    change (Spec.map (CommRingCat.ofHom
      (algebraMap ℤ A.coordinates))).finrank s = p at hs
    have hstalkAlg : @Module.rankAtStalk ℤ A.coordinates _ _ Algebra.toModule s = p :=
      (Scheme.Hom.finrank_SpecMap_algebraMap ℤ A.coordinates s).symm.trans hs
    have hstalk : Module.rankAtStalk A.coordinates s = p := hModule ▸ hstalkAlg
    exact (congrFun
      (Module.rankAtStalk_eq_finrank_of_free (R := ℤ) (M := A.coordinates)) s).symm.trans
        hstalk
  let pointEquiv : BasePoint Q ≃ (A.coordinates →ₐ[ℤ] ℤ) :=
    (pointMulEquivOfIso e (baseObject (Spec (.of ℤ)))).toEquiv |>.trans
      ((pointMulEquivOfTestIso A.realize (baseObjectIsoTestObject ℤ)).toEquiv |>.trans
        ((A.obj.pointMulEquiv ℤ).toEquiv |>.trans
          (WithConv.equiv (A.coordinates →ₐ[ℤ] ℤ))))
  let eCanonical := ConstantPrimeEtale.intAlgEquivPiFin A.coordinates
  let eCoordinate : @AlgEquiv ℤ A.coordinates
      (Fin (Module.finrank ℤ A.coordinates) → ℤ) _ _ _
      (inferInstance : Algebra ℤ A.coordinates)
      (inferInstance : Algebra ℤ (Fin (Module.finrank ℤ A.coordinates) → ℤ)) := by
    exact hAlgebra.symm ▸ eCanonical
  let algHomEquiv : (A.coordinates →ₐ[ℤ] ℤ) ≃ Fin (Module.finrank ℤ A.coordinates) := by
    exact ConstantPrimeEtale.algHomEquivFinOfAlgEquiv A.coordinates _ eCoordinate
  rw [← hrank]
  exact pointEquiv.trans algHomEquiv

/-- Honest degree-zero cardinal data for a finite-etale group scheme of constant order `p`
over `Spec ℤ`. -/
noncomputable def finiteEtaleBasePointCertifiedDataInt
    (Q : FiniteFlatCommGroupScheme (Spec (.of ℤ))) (p : ℕ)
    (hEtale : Etale Q.structureMap) (horder : Q.HasConstantOrder p) :
    FinitePGroup.CertifiedData p (BasePoint Q) where
  finite := Finite.of_equiv (Fin p)
    (finiteEtaleBasePointEquivFin Q p hEtale horder).symm
  length := 1
  card_eq := by
    rw [Nat.card_congr (finiteEtaleBasePointEquivFin Q p hEtale horder),
      Nat.card_fin, pow_one]

@[simp]
theorem finiteEtaleBasePointCertifiedDataInt_length
    (Q : FiniteFlatCommGroupScheme (Spec (.of ℤ))) (p : ℕ)
    (hEtale : Etale Q.structureMap) (horder : Q.HasConstantOrder p) :
    (finiteEtaleBasePointCertifiedDataInt Q p hEtale horder).length = 1 :=
  rfl

namespace FppfQuotientPresentation

/-- An actual finite-flat quotient presentation whose quotient is finite-etale of constant
prime order supplies the quotient `H⁰` term in the low-degree Euler estimate.  Together with
the remaining explicit endpoint data and an injective Mordell--Weil Kummer map, this forces
rank zero.  In particular, no quotient-global-section certificate is an input. -/
theorem finrank_eq_zero_of_fppfKummer_finiteEtaleQuotientInt
    {p : ℕ} {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) p).ker =
      p ^ torsionLength)
    (hEtale : Etale D.quotient.structureMap)
    (horder : D.quotient.HasConstantOrder p)
    (kernelHZeroData : FinitePGroup.CertifiedData p
      (BasePoint D.kernelPresentation.kernel))
    (middleHZeroData : FinitePGroup.CertifiedData p (BasePoint G))
    (kernelHOneData : FinitePGroup.CertifiedData p
      D.kernelPresentation.kernel.FppfHOne.{0})
    (quotientHOneData : FinitePGroup.CertifiedData p D.quotient.FppfHOne.{0})
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) p).range) →* G.FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hp : p.Prime)
    (hbound :
      middleHZeroData.length + kernelHOneData.length + quotientHOneData.length ≤
        torsionLength + kernelHZeroData.length + 1) :
    Module.finrank ℤ A = 0 := by
  letI : Finite D.kernelPresentation.kernel.FppfHOne.{0} := kernelHOneData.finite
  letI : Finite D.quotient.FppfHOne.{0} := quotientHOneData.finite
  letI : Finite G.FppfHOne.{0} := D.finite_fppfHOne_of_kernel_quotient
  apply finrank_eq_zero_of_injective_kummer_of_card_le_torsion
    p torsionLength hp hkernel kummer hkummer
  apply FppfLowDegreeExactSequence.fppfHOne_natCard_le_pow_ofFppfQuotientPresentation
    D kernelHZeroData middleHZeroData
      (finiteEtaleBasePointCertifiedDataInt D.quotient p hEtale horder)
      kernelHOneData quotientHOneData hp torsionLength
  simpa using hbound

/-- The genuine order-five quotient endpoint of
`finrank_eq_zero_of_fppfKummer_finiteEtaleQuotientInt`. -/
theorem finrank_eq_zero_of_fppfKummer_finiteEtaleQuotientInt_five
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) 5).ker =
      5 ^ torsionLength)
    (hEtale : Etale D.quotient.structureMap)
    (horder : D.quotient.HasConstantOrder 5)
    (kernelHZeroData : FinitePGroup.CertifiedData 5
      (BasePoint D.kernelPresentation.kernel))
    (middleHZeroData : FinitePGroup.CertifiedData 5 (BasePoint G))
    (kernelHOneData : FinitePGroup.CertifiedData 5
      D.kernelPresentation.kernel.FppfHOne.{0})
    (quotientHOneData : FinitePGroup.CertifiedData 5 D.quotient.FppfHOne.{0})
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) 5).range) →* G.FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hbound :
      middleHZeroData.length + kernelHOneData.length + quotientHOneData.length ≤
        torsionLength + kernelHZeroData.length + 1) :
    Module.finrank ℤ A = 0 :=
  finrank_eq_zero_of_fppfKummer_finiteEtaleQuotientInt D torsionLength hkernel
    hEtale horder kernelHZeroData middleHZeroData kernelHOneData quotientHOneData
    kummer hkummer (by decide) hbound

/-- The genuine order-eleven quotient endpoint of
`finrank_eq_zero_of_fppfKummer_finiteEtaleQuotientInt`. -/
theorem finrank_eq_zero_of_fppfKummer_finiteEtaleQuotientInt_eleven
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) 11).ker =
      11 ^ torsionLength)
    (hEtale : Etale D.quotient.structureMap)
    (horder : D.quotient.HasConstantOrder 11)
    (kernelHZeroData : FinitePGroup.CertifiedData 11
      (BasePoint D.kernelPresentation.kernel))
    (middleHZeroData : FinitePGroup.CertifiedData 11 (BasePoint G))
    (kernelHOneData : FinitePGroup.CertifiedData 11
      D.kernelPresentation.kernel.FppfHOne.{0})
    (quotientHOneData : FinitePGroup.CertifiedData 11 D.quotient.FppfHOne.{0})
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) 11).range) →* G.FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hbound :
      middleHZeroData.length + kernelHOneData.length + quotientHOneData.length ≤
        torsionLength + kernelHZeroData.length + 1) :
    Module.finrank ℤ A = 0 :=
  finrank_eq_zero_of_fppfKummer_finiteEtaleQuotientInt D torsionLength hkernel
    hEtale horder kernelHZeroData middleHZeroData kernelHOneData quotientHOneData
    kummer hkummer (by decide) hbound

end FppfQuotientPresentation

end AlgebraicGeometry.FiniteFlatCommGroupScheme

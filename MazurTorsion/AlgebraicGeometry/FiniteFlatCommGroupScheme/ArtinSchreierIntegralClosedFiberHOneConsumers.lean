/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.ArtinSchreierAdmissiblePrimeFiberConsumers

/-!
# Integral closed-fibre consumers of the Artin--Schreier H¹ calculation

An integral fppf quotient presentation with actual `mu_p` kernel and constant order-`p`
quotient base-changes to the multiplicative--constant presentation over `Spec (ZMod p)`.
The exact Artin--Schreier calculation on the constant factor and the Kummer calculation on
`mu_p` therefore bound the represented fppf `H¹` of the actual closed fibre by `p`.

The final declarations specialize this construction to coefficient five and eleven and feed
it to the rank-zero criterion.  The integral quotient presentation, its stored factor
isomorphisms, the closed-fibre Kummer homomorphism and its injectivity, and the torsion
cardinality remain explicit.  No Raynaud classification, Néron model, or Mordell--Weil
comparison is asserted here.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

open CommGroupScheme

universe u

namespace FppfQuotientPresentation

/-- Base change of an actual multiplicative--constant quotient presentation to its
characteristic-`p` fibre has represented fppf `H¹` of `p`-length at most one. -/
noncomputable def baseChangeMiddleHOneBoundedDataOfMuKernelConstantQuotient
    {R : Type} [CommRing R] {p : ℕ} [NeZero p] [Algebra R (ZMod p)]
    {G : FiniteFlatCommGroupScheme (Spec (.of R))}
    (D : FppfQuotientPresentation G) (hp : p.Prime)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme R p)
    (quotientIso : D.quotient ≅
      constantScheme R (Multiplicative (ZMod p))) :
    FinitePGroup.BoundedData p
      (((baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap R (ZMod p))))).obj G).FppfHOne.{0}) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R (ZMod p)))
  let Dp := D.baseChangePresentation f
  exact Dp.middleHOneBoundedDataOfMuKernelConstantQuotientPrimeFiber hp
    ((baseChange f).mapIso kernelIso ≪≫ muBaseChangeIso (R := R) (K := ZMod p) p)
    ((baseChange f).mapIso quotientIso ≪≫
      constantBaseChangeIso (R := R) (K := ZMod p) (Multiplicative (ZMod p)))

@[simp]
theorem baseChangeMiddleHOneBoundedDataOfMuKernelConstantQuotient_length
    {R : Type} [CommRing R] {p : ℕ} [NeZero p] [Algebra R (ZMod p)]
    {G : FiniteFlatCommGroupScheme (Spec (.of R))}
    (D : FppfQuotientPresentation G) (hp : p.Prime)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme R p)
    (quotientIso : D.quotient ≅
      constantScheme R (Multiplicative (ZMod p))) :
    (D.baseChangeMiddleHOneBoundedDataOfMuKernelConstantQuotient hp
      kernelIso quotientIso).length = 1 := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R (ZMod p)))
  let Dp := D.baseChangePresentation f
  exact Dp.middleHOneBoundedDataOfMuKernelConstantQuotientPrimeFiber_length hp
    ((baseChange f).mapIso kernelIso ≪≫ muBaseChangeIso (R := R) (K := ZMod p) p)
    ((baseChange f).mapIso quotientIso ≪≫
      constantBaseChangeIso (R := R) (K := ZMod p) (Multiplicative (ZMod p)))

/-- The actual characteristic-five fibre of an integral multiplicative--constant quotient
presentation has fppf `H¹` length at most one. -/
noncomputable def closedFiberMiddleHOneBoundedDataOfMuKernelConstantQuotientAtFive
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme ℤ 5)
    (quotientIso : D.quotient ≅
      constantScheme ℤ (Multiplicative (ZMod 5))) :
    FinitePGroup.BoundedData 5
      (((baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod 5))))).obj G).FppfHOne.{0}) :=
  D.baseChangeMiddleHOneBoundedDataOfMuKernelConstantQuotient
    (by decide) kernelIso quotientIso

/-- The actual characteristic-eleven fibre of an integral multiplicative--constant quotient
presentation has fppf `H¹` length at most one. -/
noncomputable def closedFiberMiddleHOneBoundedDataOfMuKernelConstantQuotientAtEleven
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme ℤ 11)
    (quotientIso : D.quotient ≅
      constantScheme ℤ (Multiplicative (ZMod 11))) :
    FinitePGroup.BoundedData 11
      (((baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod 11))))).obj G).FppfHOne.{0}) :=
  D.baseChangeMiddleHOneBoundedDataOfMuKernelConstantQuotient
    (by decide) kernelIso quotientIso

@[simp]
theorem closedFiberMiddleHOneBoundedDataOfMuKernelConstantQuotientAtFive_length
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme ℤ 5)
    (quotientIso : D.quotient ≅
      constantScheme ℤ (Multiplicative (ZMod 5))) :
    (D.closedFiberMiddleHOneBoundedDataOfMuKernelConstantQuotientAtFive
      kernelIso quotientIso).length = 1 :=
  D.baseChangeMiddleHOneBoundedDataOfMuKernelConstantQuotient_length
    (by decide) kernelIso quotientIso

@[simp]
theorem closedFiberMiddleHOneBoundedDataOfMuKernelConstantQuotientAtEleven_length
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme ℤ 11)
    (quotientIso : D.quotient ≅
      constantScheme ℤ (Multiplicative (ZMod 11))) :
    (D.closedFiberMiddleHOneBoundedDataOfMuKernelConstantQuotientAtEleven
      kernelIso quotientIso).length = 1 :=
  D.baseChangeMiddleHOneBoundedDataOfMuKernelConstantQuotient_length
    (by decide) kernelIso quotientIso

/-- The closed-fibre bound of a base-changed integral quotient presentation feeds the actual
represented fppf Kummer rank-zero criterion. -/
theorem finrank_eq_zero_of_fppfKummer_baseChangeMuKernelConstantQuotient
    {R : Type} [CommRing R] {p : ℕ} [NeZero p] [Algebra R (ZMod p)]
    {G : FiniteFlatCommGroupScheme (Spec (.of R))}
    (D : FppfQuotientPresentation G) (hp : p.Prime)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme R p)
    (quotientIso : D.quotient ≅
      constantScheme R (Multiplicative (ZMod p)))
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) p).ker =
      p ^ torsionLength)
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) p).range) →*
        ((baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap R (ZMod p))))).obj G).FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hbound : 1 ≤ torsionLength) :
    Module.finrank ℤ A = 0 := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R (ZMod p)))
  let Dp := D.baseChangePresentation f
  exact Dp.finrank_eq_zero_of_fppfKummer_muKernelConstantQuotientPrimeFiber hp
    ((baseChange f).mapIso kernelIso ≪≫ muBaseChangeIso (R := R) (K := ZMod p) p)
    ((baseChange f).mapIso quotientIso ≪≫
      constantBaseChangeIso (R := R) (K := ZMod p) (Multiplicative (ZMod p)))
    torsionLength hkernel kummer hkummer hbound

/-- The characteristic-five fibre of a genuine integral quotient presentation feeds rank zero
with the sharp bound `1 ≤ torsionLength`. -/
theorem finrank_eq_zero_of_fppfKummer_closedFiberMuKernelConstantQuotientAtFive
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme ℤ 5)
    (quotientIso : D.quotient ≅
      constantScheme ℤ (Multiplicative (ZMod 5)))
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) 5).ker =
      5 ^ torsionLength)
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) 5).range) →*
        ((baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod 5))))).obj G).FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hbound : 1 ≤ torsionLength) :
    Module.finrank ℤ A = 0 :=
  D.finrank_eq_zero_of_fppfKummer_baseChangeMuKernelConstantQuotient
    (by decide) kernelIso quotientIso torsionLength hkernel kummer hkummer hbound

/-- The characteristic-eleven fibre of a genuine integral quotient presentation feeds rank
zero with the sharp bound `1 ≤ torsionLength`. -/
theorem finrank_eq_zero_of_fppfKummer_closedFiberMuKernelConstantQuotientAtEleven
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme ℤ 11)
    (quotientIso : D.quotient ≅
      constantScheme ℤ (Multiplicative (ZMod 11)))
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) 11).ker =
      11 ^ torsionLength)
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) 11).range) →*
        ((baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod 11))))).obj G).FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hbound : 1 ≤ torsionLength) :
    Module.finrank ℤ A = 0 :=
  D.finrank_eq_zero_of_fppfKummer_baseChangeMuKernelConstantQuotient
    (by decide) kernelIso quotientIso torsionLength hkernel kummer hkummer hbound

end FppfQuotientPresentation

namespace AdmissibleFiltrationStep

/-- An integral admissible step with stored multiplicative kernel and constant quotient has
closed-fibre fppf `H¹` length at most one at five. -/
noncomputable def
    closedFiberMiddleHOneBoundedDataOfMultiplicativeKernelConstantQuotientAtFive
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : AdmissibleFiltrationStep ℤ 5 G)
    (hkernel : D.kernelFactor.IsMultiplicative)
    (hquotient : D.quotientFactor.IsConstant) :
    FinitePGroup.BoundedData 5
      (((FiniteFlatCommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod 5))))).obj G).FppfHOne.{0}) :=
  D.toFppfQuotientPresentation
    |>.closedFiberMiddleHOneBoundedDataOfMuKernelConstantQuotientAtFive
      (D.kernelFactor.multiplicativeIso hkernel)
      (D.quotientFactor.constantIso hquotient)

/-- An integral admissible step with stored multiplicative kernel and constant quotient has
closed-fibre fppf `H¹` length at most one at eleven. -/
noncomputable def
    closedFiberMiddleHOneBoundedDataOfMultiplicativeKernelConstantQuotientAtEleven
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : AdmissibleFiltrationStep ℤ 11 G)
    (hkernel : D.kernelFactor.IsMultiplicative)
    (hquotient : D.quotientFactor.IsConstant) :
    FinitePGroup.BoundedData 11
      (((FiniteFlatCommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod 11))))).obj G).FppfHOne.{0}) :=
  D.toFppfQuotientPresentation
    |>.closedFiberMiddleHOneBoundedDataOfMuKernelConstantQuotientAtEleven
      (D.kernelFactor.multiplicativeIso hkernel)
      (D.quotientFactor.constantIso hquotient)

@[simp]
theorem
    closedFiberMiddleHOneBoundedDataOfMultiplicativeKernelConstantQuotientAtFive_length
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : AdmissibleFiltrationStep ℤ 5 G)
    (hkernel : D.kernelFactor.IsMultiplicative)
    (hquotient : D.quotientFactor.IsConstant) :
    (D.closedFiberMiddleHOneBoundedDataOfMultiplicativeKernelConstantQuotientAtFive
      hkernel hquotient).length = 1 :=
  D.toFppfQuotientPresentation
    |>.closedFiberMiddleHOneBoundedDataOfMuKernelConstantQuotientAtFive_length
      (D.kernelFactor.multiplicativeIso hkernel)
      (D.quotientFactor.constantIso hquotient)

@[simp]
theorem
    closedFiberMiddleHOneBoundedDataOfMultiplicativeKernelConstantQuotientAtEleven_length
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : AdmissibleFiltrationStep ℤ 11 G)
    (hkernel : D.kernelFactor.IsMultiplicative)
    (hquotient : D.quotientFactor.IsConstant) :
    (D.closedFiberMiddleHOneBoundedDataOfMultiplicativeKernelConstantQuotientAtEleven
      hkernel hquotient).length = 1 :=
  D.toFppfQuotientPresentation
    |>.closedFiberMiddleHOneBoundedDataOfMuKernelConstantQuotientAtEleven_length
      (D.kernelFactor.multiplicativeIso hkernel)
      (D.quotientFactor.constantIso hquotient)

/-- The characteristic-five fibre of an actual integral admissible step feeds the sharp
rank-zero endpoint using only its stored factor isomorphisms. -/
theorem
    finrank_eq_zero_of_fppfKummer_closedFiberMultiplicativeKernelConstantQuotientAtFive
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : AdmissibleFiltrationStep ℤ 5 G)
    (hkernelFactor : D.kernelFactor.IsMultiplicative)
    (hquotientFactor : D.quotientFactor.IsConstant)
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) 5).ker =
      5 ^ torsionLength)
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) 5).range) →*
        ((FiniteFlatCommGroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod 5))))).obj G).FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hbound : 1 ≤ torsionLength) :
    Module.finrank ℤ A = 0 :=
  D.toFppfQuotientPresentation
    |>.finrank_eq_zero_of_fppfKummer_closedFiberMuKernelConstantQuotientAtFive
      (D.kernelFactor.multiplicativeIso hkernelFactor)
      (D.quotientFactor.constantIso hquotientFactor)
      torsionLength hkernel kummer hkummer hbound

/-- The characteristic-eleven fibre of an actual integral admissible step feeds the sharp
rank-zero endpoint using only its stored factor isomorphisms. -/
theorem
    finrank_eq_zero_of_fppfKummer_closedFiberMultiplicativeKernelConstantQuotientAtEleven
    {G : FiniteFlatCommGroupScheme (Spec (.of ℤ))}
    (D : AdmissibleFiltrationStep ℤ 11 G)
    (hkernelFactor : D.kernelFactor.IsMultiplicative)
    (hquotientFactor : D.quotientFactor.IsConstant)
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) 11).ker =
      11 ^ torsionLength)
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) 11).range) →*
        ((FiniteFlatCommGroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod 11))))).obj G).FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hbound : 1 ≤ torsionLength) :
    Module.finrank ℤ A = 0 :=
  D.toFppfQuotientPresentation
    |>.finrank_eq_zero_of_fppfKummer_closedFiberMuKernelConstantQuotientAtEleven
      (D.kernelFactor.multiplicativeIso hkernelFactor)
      (D.quotientFactor.constantIso hquotientFactor)
      torsionLength hkernel kummer hkummer hbound

end AdmissibleFiltrationStep

end AlgebraicGeometry.FiniteFlatCommGroupScheme

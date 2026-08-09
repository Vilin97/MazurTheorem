/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.ArtinSchreierFppfHOne
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.MuKernelPrimeFiberKummerRankZero

/-!
# Sharp prime-fibre bounds for multiplicative--constant admissible steps

Artin--Schreier computes the represented fppf `H¹` of the constant order-`p` group over
`Spec (ZMod p)` with exact `p`-length one.  On the same fibre, the actual `mu_p` model has
trivial represented fppf `H¹`.  Exactness for a genuine finite-flat fppf quotient presentation
therefore gives the middle term `p`-length at most one, rather than the length-two estimate
obtained by treating the two residue and coefficient primes independently.

The concrete five- and eleven-adic endpoints feed this sharp bound to the repository's Kummer
rank-zero criterion.  The geometric quotient presentation, its actual kernel and quotient
isomorphisms, the Mordell--Weil Kummer homomorphism and its injectivity, and the torsion
cardinality remain explicit.  The admissible-filtration wrappers merely recover isomorphisms
already stored by the multiplicative and constant constructors; they do not assert an
Oort--Tate or Raynaud classification.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

open CommGroupScheme

universe u

namespace FppfQuotientPresentation

/-- On the characteristic-`p` fibre, an actual extension of the constant order-`p` group by
`mu_p` has represented fppf `H¹` of `p`-length at most one. -/
noncomputable def middleHOneBoundedDataOfMuKernelConstantQuotientPrimeFiber
    {p : ℕ} [NeZero p]
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod p)))}
    (D : FppfQuotientPresentation G) (hp : p.Prime)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme (ZMod p) p)
    (quotientIso : D.quotient ≅
      constantScheme (ZMod p) (Multiplicative (ZMod p))) :
    FinitePGroup.BoundedData p G.FppfHOne.{0} := by
  letI : Fact p.Prime := ⟨hp⟩
  let kernelHOneData :=
    (muSchemeFppfHOne_zmod_prime_certifiedData p hp).toBoundedData.congr
      (CommGroupScheme.fppfHOneMulEquivOfIso
        ((finiteFlatCommGroupSchemeProperty _).ι.mapIso kernelIso)).symm
  let quotientHOneData :=
    (ArtinSchreier.constantSchemeFppfHOne_zmod_prime_certifiedData p).toBoundedData.congr
      (CommGroupScheme.fppfHOneMulEquivOfIso
        ((finiteFlatCommGroupSchemeProperty _).ι.mapIso quotientIso)).symm
  exact FinitePGroup.BoundedData.middleOfMulExact kernelHOneData quotientHOneData
    (fppfHOneMap D.kernelPresentation.inclusion) (fppfHOneMap D.project)
    D.exact_fppfHOneMap_inclusion_project

@[simp]
theorem middleHOneBoundedDataOfMuKernelConstantQuotientPrimeFiber_length
    {p : ℕ} [NeZero p]
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod p)))}
    (D : FppfQuotientPresentation G) (hp : p.Prime)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme (ZMod p) p)
    (quotientIso : D.quotient ≅
      constantScheme (ZMod p) (Multiplicative (ZMod p))) :
    (D.middleHOneBoundedDataOfMuKernelConstantQuotientPrimeFiber hp
      kernelIso quotientIso).length = 1 := by
  rfl

/-- The sharp multiplicative--constant bound over `Spec (ZMod 5)`. -/
noncomputable def middleHOneBoundedDataOfMuKernelConstantQuotientPrimeFiberAtFive
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod 5)))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme (ZMod 5) 5)
    (quotientIso : D.quotient ≅
      constantScheme (ZMod 5) (Multiplicative (ZMod 5))) :
    FinitePGroup.BoundedData 5 G.FppfHOne.{0} :=
  D.middleHOneBoundedDataOfMuKernelConstantQuotientPrimeFiber
    (by decide) kernelIso quotientIso

/-- The sharp multiplicative--constant bound over `Spec (ZMod 11)`. -/
noncomputable def middleHOneBoundedDataOfMuKernelConstantQuotientPrimeFiberAtEleven
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod 11)))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme (ZMod 11) 11)
    (quotientIso : D.quotient ≅
      constantScheme (ZMod 11) (Multiplicative (ZMod 11))) :
    FinitePGroup.BoundedData 11 G.FppfHOne.{0} :=
  D.middleHOneBoundedDataOfMuKernelConstantQuotientPrimeFiber
    (by decide) kernelIso quotientIso

@[simp]
theorem middleHOneBoundedDataOfMuKernelConstantQuotientPrimeFiberAtFive_length
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod 5)))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme (ZMod 5) 5)
    (quotientIso : D.quotient ≅
      constantScheme (ZMod 5) (Multiplicative (ZMod 5))) :
    (D.middleHOneBoundedDataOfMuKernelConstantQuotientPrimeFiberAtFive
      kernelIso quotientIso).length = 1 :=
  D.middleHOneBoundedDataOfMuKernelConstantQuotientPrimeFiber_length
    (by decide) kernelIso quotientIso

@[simp]
theorem middleHOneBoundedDataOfMuKernelConstantQuotientPrimeFiberAtEleven_length
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod 11)))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme (ZMod 11) 11)
    (quotientIso : D.quotient ≅
      constantScheme (ZMod 11) (Multiplicative (ZMod 11))) :
    (D.middleHOneBoundedDataOfMuKernelConstantQuotientPrimeFiberAtEleven
      kernelIso quotientIso).length = 1 :=
  D.middleHOneBoundedDataOfMuKernelConstantQuotientPrimeFiber_length
    (by decide) kernelIso quotientIso

/-- The same-prime multiplicative--constant bound feeds the actual represented fppf Kummer
criterion. -/
theorem finrank_eq_zero_of_fppfKummer_muKernelConstantQuotientPrimeFiber
    {p : ℕ} [NeZero p]
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod p)))}
    (D : FppfQuotientPresentation G) (hp : p.Prime)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme (ZMod p) p)
    (quotientIso : D.quotient ≅
      constantScheme (ZMod p) (Multiplicative (ZMod p)))
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) p).ker =
      p ^ torsionLength)
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) p).range) →* G.FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hbound : 1 ≤ torsionLength) :
    Module.finrank ℤ A = 0 := by
  let middleHOneData :=
    D.middleHOneBoundedDataOfMuKernelConstantQuotientPrimeFiber hp
      kernelIso quotientIso
  letI : Finite G.FppfHOne.{0} := middleHOneData.finite
  apply finrank_eq_zero_of_injective_kummer_of_card_le_torsion
    p torsionLength hp hkernel kummer hkummer
  exact middleHOneData.card_le.trans
    ((Nat.pow_le_pow_iff_right hp.one_lt).mpr (by
      simpa [middleHOneData] using hbound))

/-- The genuine five-adic multiplicative--constant quotient presentation feeds the Kummer
rank-zero criterion with the sharp hypothesis `1 ≤ torsionLength`. -/
theorem finrank_eq_zero_of_fppfKummer_muKernelConstantQuotientPrimeFiberAtFive
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod 5)))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme (ZMod 5) 5)
    (quotientIso : D.quotient ≅
      constantScheme (ZMod 5) (Multiplicative (ZMod 5)))
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) 5).ker =
      5 ^ torsionLength)
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) 5).range) →* G.FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hbound : 1 ≤ torsionLength) :
    Module.finrank ℤ A = 0 :=
  D.finrank_eq_zero_of_fppfKummer_muKernelConstantQuotientPrimeFiber
    (by decide) kernelIso quotientIso torsionLength hkernel kummer hkummer hbound

/-- The genuine eleven-adic multiplicative--constant quotient presentation feeds the Kummer
rank-zero criterion with the sharp hypothesis `1 ≤ torsionLength`. -/
theorem finrank_eq_zero_of_fppfKummer_muKernelConstantQuotientPrimeFiberAtEleven
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod 11)))}
    (D : FppfQuotientPresentation G)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme (ZMod 11) 11)
    (quotientIso : D.quotient ≅
      constantScheme (ZMod 11) (Multiplicative (ZMod 11)))
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) 11).ker =
      11 ^ torsionLength)
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) 11).range) →* G.FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hbound : 1 ≤ torsionLength) :
    Module.finrank ℤ A = 0 :=
  D.finrank_eq_zero_of_fppfKummer_muKernelConstantQuotientPrimeFiber
    (by decide) kernelIso quotientIso torsionLength hkernel kummer hkummer hbound

end FppfQuotientPresentation

namespace AdmissibleSimpleFactor

/-- The proposition that an admissible simple factor was built from the constant constructor.
This is only a constructor tag, not a classification theorem. -/
def IsConstant
    {R : Type} [CommRing R] {p : ℕ} [NeZero p]
    {Q : FiniteFlatCommGroupScheme (Spec (.of R))}
    (F : AdmissibleSimpleFactor R p Q) : Prop :=
  match F with
  | .constant _ => True
  | .multiplicative _ => False

/-- Recover the constant-factor isomorphism already stored by a constant simple-factor
constructor. -/
def constantIso
    {R : Type} [CommRing R] {p : ℕ} [NeZero p]
    {Q : FiniteFlatCommGroupScheme (Spec (.of R))}
    (F : AdmissibleSimpleFactor R p Q) (hF : F.IsConstant) :
    Q ≅ constantScheme R (Multiplicative (ZMod p)) := by
  cases F with
  | constant e => exact e
  | multiplicative _ => contradiction

end AdmissibleSimpleFactor

namespace AdmissibleFiltrationStep

/-- An actual admissible step whose stored kernel factor is multiplicative and whose stored
quotient factor is constant has the sharp same-prime fppf `H¹` bound. -/
noncomputable def middleHOneBoundedDataOfMultiplicativeKernelConstantQuotientPrimeFiber
    {p : ℕ} [NeZero p]
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod p)))}
    (D : AdmissibleFiltrationStep (ZMod p) p G)
    (hkernel : D.kernelFactor.IsMultiplicative)
    (hquotient : D.quotientFactor.IsConstant) :
    FinitePGroup.BoundedData p G.FppfHOne.{0} :=
  D.toFppfQuotientPresentation
    |>.middleHOneBoundedDataOfMuKernelConstantQuotientPrimeFiber D.prime
      (D.kernelFactor.multiplicativeIso hkernel)
      (D.quotientFactor.constantIso hquotient)

@[simp]
theorem middleHOneBoundedDataOfMultiplicativeKernelConstantQuotientPrimeFiber_length
    {p : ℕ} [NeZero p]
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod p)))}
    (D : AdmissibleFiltrationStep (ZMod p) p G)
    (hkernel : D.kernelFactor.IsMultiplicative)
    (hquotient : D.quotientFactor.IsConstant) :
    (D.middleHOneBoundedDataOfMultiplicativeKernelConstantQuotientPrimeFiber
      hkernel hquotient).length = 1 :=
  D.toFppfQuotientPresentation
    |>.middleHOneBoundedDataOfMuKernelConstantQuotientPrimeFiber_length D.prime
      (D.kernelFactor.multiplicativeIso hkernel)
      (D.quotientFactor.constantIso hquotient)

/-- The stored-factor sharp bound for an actual admissible step over `Spec (ZMod 5)`. -/
noncomputable def
    middleHOneBoundedDataOfMultiplicativeKernelConstantQuotientPrimeFiberAtFive
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod 5)))}
    (D : AdmissibleFiltrationStep (ZMod 5) 5 G)
    (hkernel : D.kernelFactor.IsMultiplicative)
    (hquotient : D.quotientFactor.IsConstant) :
    FinitePGroup.BoundedData 5 G.FppfHOne.{0} :=
  D.middleHOneBoundedDataOfMultiplicativeKernelConstantQuotientPrimeFiber
    hkernel hquotient

/-- The stored-factor sharp bound for an actual admissible step over `Spec (ZMod 11)`. -/
noncomputable def
    middleHOneBoundedDataOfMultiplicativeKernelConstantQuotientPrimeFiberAtEleven
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod 11)))}
    (D : AdmissibleFiltrationStep (ZMod 11) 11 G)
    (hkernel : D.kernelFactor.IsMultiplicative)
    (hquotient : D.quotientFactor.IsConstant) :
    FinitePGroup.BoundedData 11 G.FppfHOne.{0} :=
  D.middleHOneBoundedDataOfMultiplicativeKernelConstantQuotientPrimeFiber
    hkernel hquotient

@[simp]
theorem
    middleHOneBoundedDataOfMultiplicativeKernelConstantQuotientPrimeFiberAtFive_length
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod 5)))}
    (D : AdmissibleFiltrationStep (ZMod 5) 5 G)
    (hkernel : D.kernelFactor.IsMultiplicative)
    (hquotient : D.quotientFactor.IsConstant) :
    (D.middleHOneBoundedDataOfMultiplicativeKernelConstantQuotientPrimeFiberAtFive
      hkernel hquotient).length = 1 :=
  D.middleHOneBoundedDataOfMultiplicativeKernelConstantQuotientPrimeFiber_length
    hkernel hquotient

@[simp]
theorem
    middleHOneBoundedDataOfMultiplicativeKernelConstantQuotientPrimeFiberAtEleven_length
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod 11)))}
    (D : AdmissibleFiltrationStep (ZMod 11) 11 G)
    (hkernel : D.kernelFactor.IsMultiplicative)
    (hquotient : D.quotientFactor.IsConstant) :
    (D.middleHOneBoundedDataOfMultiplicativeKernelConstantQuotientPrimeFiberAtEleven
      hkernel hquotient).length = 1 :=
  D.middleHOneBoundedDataOfMultiplicativeKernelConstantQuotientPrimeFiber_length
    hkernel hquotient

/-- An admissible multiplicative--constant step over `ZMod 5` feeds the sharp Kummer
rank-zero endpoint using only the isomorphisms stored in its factor constructors. -/
theorem
    finrank_eq_zero_of_fppfKummer_multiplicativeKernelConstantQuotientPrimeFiberAtFive
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod 5)))}
    (D : AdmissibleFiltrationStep (ZMod 5) 5 G)
    (hkernelFactor : D.kernelFactor.IsMultiplicative)
    (hquotientFactor : D.quotientFactor.IsConstant)
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) 5).ker =
      5 ^ torsionLength)
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) 5).range) →* G.FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hbound : 1 ≤ torsionLength) :
    Module.finrank ℤ A = 0 :=
  D.toFppfQuotientPresentation
    |>.finrank_eq_zero_of_fppfKummer_muKernelConstantQuotientPrimeFiberAtFive
      (D.kernelFactor.multiplicativeIso hkernelFactor)
      (D.quotientFactor.constantIso hquotientFactor)
      torsionLength hkernel kummer hkummer hbound

/-- An admissible multiplicative--constant step over `ZMod 11` feeds the sharp Kummer
rank-zero endpoint using only the isomorphisms stored in its factor constructors. -/
theorem
    finrank_eq_zero_of_fppfKummer_multiplicativeKernelConstantQuotientPrimeFiberAtEleven
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod 11)))}
    (D : AdmissibleFiltrationStep (ZMod 11) 11 G)
    (hkernelFactor : D.kernelFactor.IsMultiplicative)
    (hquotientFactor : D.quotientFactor.IsConstant)
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) 11).ker =
      11 ^ torsionLength)
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) 11).range) →* G.FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hbound : 1 ≤ torsionLength) :
    Module.finrank ℤ A = 0 :=
  D.toFppfQuotientPresentation
    |>.finrank_eq_zero_of_fppfKummer_muKernelConstantQuotientPrimeFiberAtEleven
      (D.kernelFactor.multiplicativeIso hkernelFactor)
      (D.quotientFactor.constantIso hquotientFactor)
      torsionLength hkernel kummer hkummer hbound

end AdmissibleFiltrationStep

end AlgebraicGeometry.FiniteFlatCommGroupScheme

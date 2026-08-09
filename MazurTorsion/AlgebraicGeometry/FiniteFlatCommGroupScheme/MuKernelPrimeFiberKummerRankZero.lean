/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.AdmissibleFiltration
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfHOneBaseIso
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfKummerRankZero
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.MultiplicativeBadFiberKummerHOne
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.MuSchemePowerKernelComparison

/-!
# Prime-fibre Kummer bounds for multiplicative-kernel extensions

The Hopf-coordinate identification `mu_p ≅ ker((- ^ p) : G_m -> G_m)` transports the checked
Kummer calculation to the actual finite-flat `muScheme`.  Over a prime field of any residue
characteristic, its represented fppf `H¹` has `p`-length at most one.  Exactness for a genuine
fppf quotient presentation then bounds the middle `H¹` by that multiplicative contribution and
the supplied quotient term.

The final theorems specialize the residue characteristic, independently of the coefficient
prime, to `5` and `11` and feed the repository's Kummer rank-zero criterion.  The geometric
quotient presentation, the supplied geometric identification of its kernel with `mu_p`, quotient
cohomology, a Kummer homomorphism and its injectivity, and the torsion-cardinality law remain
explicit.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

open CommGroupScheme
open CommGroupScheme.MultiplicativeKummer

universe u

/-- Over a field, the actual diagonalizable `mu_n` model has the full Kummer description of
its represented fppf `H¹`. -/
noncomputable def muSchemeFppfHOneMulEquivUnitKummerClasses
    (K : Type) [Field K] (n : ℕ) [NeZero n] :
    (muScheme K n).FppfHOne.{0} ≃* UnitKummerClasses K n :=
  (CommGroupScheme.fppfHOneMulEquivOfIso
    (muSchemePowerKernelIso K n)).trans
      (powerKernelFppfHOneMulEquivUnitKummerClasses K n (NeZero.ne n))

/-- Over the prime field `ZMod p`, the represented fppf `H¹` of the repository's actual
`mu_p` scheme has exact cardinality `p ^ 0`. -/
noncomputable def muSchemeFppfHOne_zmod_prime_certifiedData
    (p : ℕ) (hp : p.Prime) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    FinitePGroup.CertifiedData p (muScheme (ZMod p) p).FppfHOne.{0} := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact (powerKernelFppfHOne_zmod_prime_certifiedData p hp).congr
    (CommGroupScheme.fppfHOneMulEquivOfIso
      (muSchemePowerKernelIso (ZMod p) p)).symm

@[simp]
theorem muSchemeFppfHOne_zmod_prime_certifiedData_length
    (p : ℕ) (hp : p.Prime) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    (muSchemeFppfHOne_zmod_prime_certifiedData p hp).length = 0 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rfl

/-- Over any prime field, `H¹(mu_p)` has at most `p` classes. -/
noncomputable def muSchemeFppfHOne_zmod_primes_boundedData
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    FinitePGroup.BoundedData p (muScheme (ZMod q) p).FppfHOne.{0} := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact q.Prime := ⟨hq⟩
  exact (unitKummerClasses_zmod_primes_boundedData p q hp hq).congr
    (muSchemeFppfHOneMulEquivUnitKummerClasses (ZMod q) p).symm

@[simp]
theorem muSchemeFppfHOne_zmod_primes_boundedData_length
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    (muSchemeFppfHOne_zmod_primes_boundedData p q hp hq).length = 1 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rfl

namespace AdmissibleSimpleFactor

/-- The proposition that an admissible simple factor was built from the multiplicative
constructor.  This is a constructor tag, not a second factor isomorphism. -/
def IsMultiplicative
    {R : Type} [CommRing R] {p : ℕ} [NeZero p]
    {Q : FiniteFlatCommGroupScheme (Spec (.of R))}
    (F : AdmissibleSimpleFactor R p Q) : Prop :=
  match F with
  | .constant _ => False
  | .multiplicative _ => True

/-- Recover the `mu_p` isomorphism already stored by a multiplicative simple-factor
constructor. -/
def multiplicativeIso
    {R : Type} [CommRing R] {p : ℕ} [NeZero p]
    {Q : FiniteFlatCommGroupScheme (Spec (.of R))}
    (F : AdmissibleSimpleFactor R p Q) (hF : F.IsMultiplicative) :
    Q ≅ muScheme R p := by
  cases F with
  | constant _ => contradiction
  | multiplicative e => exact e

end AdmissibleSimpleFactor

namespace FppfQuotientPresentation

/-- If the actual kernel of an fppf quotient over a prime field is `mu_p`, exactness bounds
the middle represented `H¹` by one multiplicative contribution and the quotient `H¹`. -/
noncomputable def middleHOneBoundedDataOfMuKernelPrimeFiber
    {coeffPrime residuePrime : ℕ} [NeZero coeffPrime]
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod residuePrime)))}
    (D : FppfQuotientPresentation G)
    (hcoeffPrime : coeffPrime.Prime) (hresiduePrime : residuePrime.Prime)
    (kernelIso : D.kernelPresentation.kernel ≅
      muScheme (ZMod residuePrime) coeffPrime)
    (quotientHOneData : FinitePGroup.BoundedData coeffPrime
      D.quotient.FppfHOne.{0}) :
    FinitePGroup.BoundedData coeffPrime G.FppfHOne.{0} := by
  let kernelHOneData :=
    (muSchemeFppfHOne_zmod_primes_boundedData
      coeffPrime residuePrime hcoeffPrime hresiduePrime).congr
        (CommGroupScheme.fppfHOneMulEquivOfIso
          ((finiteFlatCommGroupSchemeProperty _).ι.mapIso kernelIso)).symm
  exact FinitePGroup.BoundedData.middleOfMulExact kernelHOneData quotientHOneData
    (fppfHOneMap D.kernelPresentation.inclusion) (fppfHOneMap D.project)
    D.exact_fppfHOneMap_inclusion_project

@[simp]
theorem middleHOneBoundedDataOfMuKernelPrimeFiber_length
    {coeffPrime residuePrime : ℕ} [NeZero coeffPrime]
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod residuePrime)))}
    (D : FppfQuotientPresentation G)
    (hcoeffPrime : coeffPrime.Prime) (hresiduePrime : residuePrime.Prime)
    (kernelIso : D.kernelPresentation.kernel ≅
      muScheme (ZMod residuePrime) coeffPrime)
    (quotientHOneData : FinitePGroup.BoundedData coeffPrime
      D.quotient.FppfHOne.{0}) :
    (D.middleHOneBoundedDataOfMuKernelPrimeFiber hcoeffPrime hresiduePrime
      kernelIso quotientHOneData).length = 1 + quotientHOneData.length :=
  by
    calc
      (D.middleHOneBoundedDataOfMuKernelPrimeFiber hcoeffPrime hresiduePrime
          kernelIso quotientHOneData).length =
          (muSchemeFppfHOne_zmod_primes_boundedData coeffPrime residuePrime
            hcoeffPrime hresiduePrime).length + quotientHOneData.length := rfl
      _ = 1 + quotientHOneData.length := by
        rw [muSchemeFppfHOne_zmod_primes_boundedData_length]

/-- At residue characteristic five, a multiplicative-kernel extension has length at most one
plus the supplied quotient length. -/
noncomputable def middleHOneBoundedDataOfMuKernelPrimeFiberAtFive
    {coeffPrime : ℕ} [NeZero coeffPrime]
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod 5)))}
    (D : FppfQuotientPresentation G) (hcoeffPrime : coeffPrime.Prime)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme (ZMod 5) coeffPrime)
    (quotientHOneData : FinitePGroup.BoundedData coeffPrime
      D.quotient.FppfHOne.{0}) :
    FinitePGroup.BoundedData coeffPrime G.FppfHOne.{0} :=
  D.middleHOneBoundedDataOfMuKernelPrimeFiber hcoeffPrime (by decide)
    kernelIso quotientHOneData

/-- At residue characteristic eleven, a multiplicative-kernel extension has length at most one
plus the supplied quotient length. -/
noncomputable def middleHOneBoundedDataOfMuKernelPrimeFiberAtEleven
    {coeffPrime : ℕ} [NeZero coeffPrime]
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod 11)))}
    (D : FppfQuotientPresentation G) (hcoeffPrime : coeffPrime.Prime)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme (ZMod 11) coeffPrime)
    (quotientHOneData : FinitePGroup.BoundedData coeffPrime
      D.quotient.FppfHOne.{0}) :
    FinitePGroup.BoundedData coeffPrime G.FppfHOne.{0} :=
  D.middleHOneBoundedDataOfMuKernelPrimeFiber hcoeffPrime (by decide)
    kernelIso quotientHOneData

@[simp]
theorem middleHOneBoundedDataOfMuKernelPrimeFiberAtFive_length
    {coeffPrime : ℕ} [NeZero coeffPrime]
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod 5)))}
    (D : FppfQuotientPresentation G) (hcoeffPrime : coeffPrime.Prime)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme (ZMod 5) coeffPrime)
    (quotientHOneData : FinitePGroup.BoundedData coeffPrime
      D.quotient.FppfHOne.{0}) :
    (D.middleHOneBoundedDataOfMuKernelPrimeFiberAtFive hcoeffPrime kernelIso
      quotientHOneData).length = 1 + quotientHOneData.length :=
  D.middleHOneBoundedDataOfMuKernelPrimeFiber_length hcoeffPrime (by decide)
    kernelIso quotientHOneData

@[simp]
theorem middleHOneBoundedDataOfMuKernelPrimeFiberAtEleven_length
    {coeffPrime : ℕ} [NeZero coeffPrime]
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod 11)))}
    (D : FppfQuotientPresentation G) (hcoeffPrime : coeffPrime.Prime)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme (ZMod 11) coeffPrime)
    (quotientHOneData : FinitePGroup.BoundedData coeffPrime
      D.quotient.FppfHOne.{0}) :
    (D.middleHOneBoundedDataOfMuKernelPrimeFiberAtEleven hcoeffPrime kernelIso
      quotientHOneData).length = 1 + quotientHOneData.length :=
  D.middleHOneBoundedDataOfMuKernelPrimeFiber_length hcoeffPrime (by decide)
    kernelIso quotientHOneData

/-- The residue-characteristic-five prime-fibre bound feeds the actual Kummer rank-zero
criterion with an independent coefficient prime. -/
theorem finrank_eq_zero_of_fppfKummer_muKernelPrimeFiberAtFive
    {coeffPrime : ℕ} [NeZero coeffPrime]
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod 5)))}
    (D : FppfQuotientPresentation G) (hcoeffPrime : coeffPrime.Prime)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme (ZMod 5) coeffPrime)
    (quotientHOneData : FinitePGroup.BoundedData coeffPrime
      D.quotient.FppfHOne.{0})
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) coeffPrime).ker =
      coeffPrime ^ torsionLength)
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) coeffPrime).range) →* G.FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hbound : 1 + quotientHOneData.length ≤ torsionLength) :
    Module.finrank ℤ A = 0 := by
  let middleHOneData :=
    D.middleHOneBoundedDataOfMuKernelPrimeFiberAtFive hcoeffPrime kernelIso
      quotientHOneData
  letI : Finite G.FppfHOne.{0} := middleHOneData.finite
  apply finrank_eq_zero_of_injective_kummer_of_card_le_torsion
    coeffPrime torsionLength hcoeffPrime hkernel kummer hkummer
  exact middleHOneData.card_le.trans
    ((Nat.pow_le_pow_iff_right hcoeffPrime.one_lt).mpr (by
      simpa [middleHOneData] using hbound))

/-- The residue-characteristic-eleven prime-fibre bound feeds the actual Kummer rank-zero
criterion with an independent coefficient prime. -/
theorem finrank_eq_zero_of_fppfKummer_muKernelPrimeFiberAtEleven
    {coeffPrime : ℕ} [NeZero coeffPrime]
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod 11)))}
    (D : FppfQuotientPresentation G) (hcoeffPrime : coeffPrime.Prime)
    (kernelIso : D.kernelPresentation.kernel ≅ muScheme (ZMod 11) coeffPrime)
    (quotientHOneData : FinitePGroup.BoundedData coeffPrime
      D.quotient.FppfHOne.{0})
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) coeffPrime).ker =
      coeffPrime ^ torsionLength)
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) coeffPrime).range) →* G.FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hbound : 1 + quotientHOneData.length ≤ torsionLength) :
    Module.finrank ℤ A = 0 := by
  let middleHOneData :=
    D.middleHOneBoundedDataOfMuKernelPrimeFiberAtEleven hcoeffPrime kernelIso
      quotientHOneData
  letI : Finite G.FppfHOne.{0} := middleHOneData.finite
  apply finrank_eq_zero_of_injective_kummer_of_card_le_torsion
    coeffPrime torsionLength hcoeffPrime hkernel kummer hkummer
  exact middleHOneData.card_le.trans
    ((Nat.pow_le_pow_iff_right hcoeffPrime.one_lt).mpr (by
      simpa [middleHOneData] using hbound))

end FppfQuotientPresentation

namespace AdmissibleFiltrationStep

/-- An actual admissible filtration step whose stored kernel factor is multiplicative inherits
the prime-fibre `H¹` bound without asking for a second kernel isomorphism. -/
noncomputable def middleHOneBoundedDataOfMultiplicativeKernelPrimeFiber
    {coeffPrime residuePrime : ℕ} [NeZero coeffPrime]
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod residuePrime)))}
    (D : AdmissibleFiltrationStep (ZMod residuePrime) coeffPrime G)
    (hresiduePrime : residuePrime.Prime)
    (hkernel : D.kernelFactor.IsMultiplicative)
    (quotientHOneData : FinitePGroup.BoundedData coeffPrime
      D.quotient.FppfHOne.{0}) :
    FinitePGroup.BoundedData coeffPrime G.FppfHOne.{0} :=
  D.toFppfQuotientPresentation.middleHOneBoundedDataOfMuKernelPrimeFiber
    D.prime hresiduePrime (D.kernelFactor.multiplicativeIso hkernel)
    quotientHOneData

@[simp]
theorem middleHOneBoundedDataOfMultiplicativeKernelPrimeFiber_length
    {coeffPrime residuePrime : ℕ} [NeZero coeffPrime]
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod residuePrime)))}
    (D : AdmissibleFiltrationStep (ZMod residuePrime) coeffPrime G)
    (hresiduePrime : residuePrime.Prime)
    (hkernel : D.kernelFactor.IsMultiplicative)
    (quotientHOneData : FinitePGroup.BoundedData coeffPrime
      D.quotient.FppfHOne.{0}) :
    (D.middleHOneBoundedDataOfMultiplicativeKernelPrimeFiber hresiduePrime
      hkernel quotientHOneData).length = 1 + quotientHOneData.length :=
  D.toFppfQuotientPresentation.middleHOneBoundedDataOfMuKernelPrimeFiber_length
    D.prime hresiduePrime (D.kernelFactor.multiplicativeIso hkernel)
    quotientHOneData

/-- The multiplicative-kernel bound for an actual admissible step over `ZMod 5`. -/
noncomputable def middleHOneBoundedDataOfMultiplicativeKernelPrimeFiberAtFive
    {coeffPrime : ℕ} [NeZero coeffPrime]
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod 5)))}
    (D : AdmissibleFiltrationStep (ZMod 5) coeffPrime G)
    (hkernel : D.kernelFactor.IsMultiplicative)
    (quotientHOneData : FinitePGroup.BoundedData coeffPrime
      D.quotient.FppfHOne.{0}) :
    FinitePGroup.BoundedData coeffPrime G.FppfHOne.{0} :=
  D.middleHOneBoundedDataOfMultiplicativeKernelPrimeFiber
    (by decide) hkernel quotientHOneData

/-- The multiplicative-kernel bound for an actual admissible step over `ZMod 11`. -/
noncomputable def middleHOneBoundedDataOfMultiplicativeKernelPrimeFiberAtEleven
    {coeffPrime : ℕ} [NeZero coeffPrime]
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod 11)))}
    (D : AdmissibleFiltrationStep (ZMod 11) coeffPrime G)
    (hkernel : D.kernelFactor.IsMultiplicative)
    (quotientHOneData : FinitePGroup.BoundedData coeffPrime
      D.quotient.FppfHOne.{0}) :
    FinitePGroup.BoundedData coeffPrime G.FppfHOne.{0} :=
  D.middleHOneBoundedDataOfMultiplicativeKernelPrimeFiber
    (by decide) hkernel quotientHOneData

@[simp]
theorem middleHOneBoundedDataOfMultiplicativeKernelPrimeFiberAtFive_length
    {coeffPrime : ℕ} [NeZero coeffPrime]
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod 5)))}
    (D : AdmissibleFiltrationStep (ZMod 5) coeffPrime G)
    (hkernel : D.kernelFactor.IsMultiplicative)
    (quotientHOneData : FinitePGroup.BoundedData coeffPrime
      D.quotient.FppfHOne.{0}) :
    (D.middleHOneBoundedDataOfMultiplicativeKernelPrimeFiberAtFive hkernel
      quotientHOneData).length = 1 + quotientHOneData.length :=
  D.middleHOneBoundedDataOfMultiplicativeKernelPrimeFiber_length
    (by decide) hkernel quotientHOneData

@[simp]
theorem middleHOneBoundedDataOfMultiplicativeKernelPrimeFiberAtEleven_length
    {coeffPrime : ℕ} [NeZero coeffPrime]
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod 11)))}
    (D : AdmissibleFiltrationStep (ZMod 11) coeffPrime G)
    (hkernel : D.kernelFactor.IsMultiplicative)
    (quotientHOneData : FinitePGroup.BoundedData coeffPrime
      D.quotient.FppfHOne.{0}) :
    (D.middleHOneBoundedDataOfMultiplicativeKernelPrimeFiberAtEleven hkernel
      quotientHOneData).length = 1 + quotientHOneData.length :=
  D.middleHOneBoundedDataOfMultiplicativeKernelPrimeFiber_length
    (by decide) hkernel quotientHOneData

/-- An actual admissible multiplicative-kernel step over `ZMod 5` feeds the rank-zero
criterion without a duplicate kernel-isomorphism premise. -/
theorem finrank_eq_zero_of_fppfKummer_multiplicativeKernelPrimeFiberAtFive
    {coeffPrime : ℕ} [NeZero coeffPrime]
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod 5)))}
    (D : AdmissibleFiltrationStep (ZMod 5) coeffPrime G)
    (hkernelFactor : D.kernelFactor.IsMultiplicative)
    (quotientHOneData : FinitePGroup.BoundedData coeffPrime
      D.quotient.FppfHOne.{0})
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) coeffPrime).ker =
      coeffPrime ^ torsionLength)
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) coeffPrime).range) →* G.FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hbound : 1 + quotientHOneData.length ≤ torsionLength) :
    Module.finrank ℤ A = 0 :=
  D.toFppfQuotientPresentation
    |>.finrank_eq_zero_of_fppfKummer_muKernelPrimeFiberAtFive D.prime
      (D.kernelFactor.multiplicativeIso hkernelFactor) quotientHOneData
      torsionLength hkernel kummer hkummer hbound

/-- An actual admissible multiplicative-kernel step over `ZMod 11` feeds the rank-zero
criterion without a duplicate kernel-isomorphism premise. -/
theorem finrank_eq_zero_of_fppfKummer_multiplicativeKernelPrimeFiberAtEleven
    {coeffPrime : ℕ} [NeZero coeffPrime]
    {G : FiniteFlatCommGroupScheme (Spec (.of (ZMod 11)))}
    (D : AdmissibleFiltrationStep (ZMod 11) coeffPrime G)
    (hkernelFactor : D.kernelFactor.IsMultiplicative)
    (quotientHOneData : FinitePGroup.BoundedData coeffPrime
      D.quotient.FppfHOne.{0})
    {A : Type u} [AddCommGroup A] [AddGroup.FG A]
    (torsionLength : ℕ)
    (hkernel : Nat.card (nsmulAddMonoidHom (α := A) coeffPrime).ker =
      coeffPrime ^ torsionLength)
    (kummer : Multiplicative
      (A ⧸ (nsmulAddMonoidHom (α := A) coeffPrime).range) →* G.FppfHOne.{0})
    (hkummer : Function.Injective kummer)
    (hbound : 1 + quotientHOneData.length ≤ torsionLength) :
    Module.finrank ℤ A = 0 :=
  D.toFppfQuotientPresentation
    |>.finrank_eq_zero_of_fppfKummer_muKernelPrimeFiberAtEleven D.prime
      (D.kernelFactor.multiplicativeIso hkernelFactor) quotientHOneData
      torsionLength hkernel kummer hkummer hbound

end AdmissibleFiltrationStep

end AlgebraicGeometry.FiniteFlatCommGroupScheme

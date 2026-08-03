/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.ElementaryGlobalSections
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.MultiplicativeFlat

/-!
# Global sections of Mazur's bad-level multiplicative factor

The multiplicative-flat model is an open subgroup of `mu_p`.  For odd `p`, every integral
point of `mu_p` is the identity.  Since an open immersion is a monomorphism, the same is true
for the multiplicative-flat model.  We package this one-element group as honest
`FinitePGroup.CertifiedData` of length zero.

The proof uses the realized typed inclusion constructed in `MultiplicativeFlat`; it does not
replace the geometric subgroup with a coordinate-level proxy.  The level hypotheses enter the
canonical Fermat specialization, while uniqueness itself only needs oddness of the coefficient.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme

open FiniteFlatCommGroupScheme

/-- At odd coefficient, every integral global section of the bad-level multiplicative-flat
model is the identity. -/
theorem muFlatBasePoint_eq_one
    (coeffPrime level : ℕ) [NeZero coeffPrime]
    (datum : MuFlatDatum coeffPrime level) (hodd : Odd coeffPrime)
    (x : CommGroupScheme.Point (muFlat coeffPrime level datum).obj
      (baseObject (Spec (.of ℤ)))) : x = 1 := by
  have hx : mapPoint (muFlatInclusionMap coeffPrime level datum)
      (baseObject (Spec (.of ℤ))) x = 1 := by
    apply (muBasePointMulEquivIntOfOdd coeffPrime hodd).injective
    simp
  apply Over.OverMorphism.ext
  apply (cancel_mono
    (muFlatInclusion coeffPrime level datum).hom.hom.hom.left).1
  have hone : mapPoint (muFlatInclusionMap coeffPrime level datum)
      (baseObject (Spec (.of ℤ)))
        (1 : CommGroupScheme.Point (muFlat coeffPrime level datum).obj
          (baseObject (Spec (.of ℤ)))) = 1 := map_one _
  exact congrArg Over.Hom.left (hx.trans hone.symm)

/-- The integral global sections of the odd-coefficient multiplicative-flat model form the
trivial multiplicative group. -/
noncomputable def muFlatBasePointMulEquivUnit
    (coeffPrime level : ℕ) [NeZero coeffPrime]
    (datum : MuFlatDatum coeffPrime level) (hodd : Odd coeffPrime) :
    CommGroupScheme.Point (muFlat coeffPrime level datum).obj
        (baseObject (Spec (.of ℤ))) ≃* Unit where
  toFun _ := Unit.unit
  invFun _ := 1
  left_inv := fun x ↦ (muFlatBasePoint_eq_one coeffPrime level datum hodd x).symm
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The integral global sections of the multiplicative-flat model have cardinality
`1 = coeffPrime ^ 0` at odd coefficient. -/
noncomputable def muFlatBasePointCertifiedDataOfOdd
    (coeffPrime level : ℕ) [NeZero coeffPrime]
    (datum : MuFlatDatum coeffPrime level) (hodd : Odd coeffPrime) :
    FinitePGroup.CertifiedData coeffPrime
      (CommGroupScheme.Point (muFlat coeffPrime level datum).obj
        (baseObject (Spec (.of ℤ)))) where
  finite := Finite.of_equiv Unit
    (muFlatBasePointMulEquivUnit coeffPrime level datum hodd).symm.toEquiv
  length := 0
  card_eq := by
    rw [Nat.card_congr
      (muFlatBasePointMulEquivUnit coeffPrime level datum hodd).toEquiv]
    simp

/-- At odd prime coefficient and coprime level, the canonical Fermat multiplicative-flat model
has certified trivial integral global sections. -/
noncomputable def fermatMuFlatBasePointCertifiedData
    {coeffPrime level : ℕ} (hprime : coeffPrime.Prime)
    (hcoprime : IsCoprime (level : ℤ) (coeffPrime : ℤ))
    (hodd : Odd coeffPrime) :
    letI : NeZero coeffPrime := ⟨hprime.ne_zero⟩
    FinitePGroup.CertifiedData coeffPrime
      (CommGroupScheme.Point (fermatMuFlat hprime hcoprime).obj
        (baseObject (Spec (.of ℤ)))) := by
  letI : NeZero coeffPrime := ⟨hprime.ne_zero⟩
  exact muFlatBasePointCertifiedDataOfOdd coeffPrime level
    (MuFlatDatum.ofPrimeCoprime hprime hcoprime) hodd

/-- At distinct prime coefficient and level, with odd coefficient, the canonical
multiplicative-flat factor has one integral global section, certified as
`coeffPrime ^ 0`.  Distinctness is the exact hypothesis ensuring that the two primes are
coprime, as required by the Fermat model. -/
noncomputable def fermatMuFlatBasePointCertifiedDataOfPrimeLevel
    {coeffPrime level : ℕ} (hprime : coeffPrime.Prime) (hprime2 : coeffPrime ≠ 2)
    (hlevel : level.Prime) (hne : level ≠ coeffPrime) :
    let hcoprime : IsCoprime (level : ℤ) (coeffPrime : ℤ) :=
      ((Nat.coprime_primes hlevel hprime).mpr hne).isCoprime
    letI : NeZero coeffPrime := ⟨hprime.ne_zero⟩
    FinitePGroup.CertifiedData coeffPrime
      (CommGroupScheme.Point (fermatMuFlat hprime hcoprime).obj
        (baseObject (Spec (.of ℤ)))) := by
  let hcoprime : IsCoprime (level : ℤ) (coeffPrime : ℤ) :=
    ((Nat.coprime_primes hlevel hprime).mpr hne).isCoprime
  exact fermatMuFlatBasePointCertifiedData hprime hcoprime
    (hprime.odd_of_ne_two hprime2)

/-- Low-degree endpoint carried by the actual canonical multiplicative-flat model.  This is the
form consumed by `FppfLowDegreeExactSequence`: it preserves the represented global-section
carrier (up to the universe lift used by the low-degree package) and records length zero. -/
noncomputable def fermatMuFlatHZeroFinitePGroupOfPrimeLevel
    {coeffPrime level : ℕ} (hprime : coeffPrime.Prime) (hprime2 : coeffPrime ≠ 2)
    (hlevel : level.Prime) (hne : level ≠ coeffPrime) :
    FinitePGroup.{1} coeffPrime :=
  (fermatMuFlatBasePointCertifiedDataOfPrimeLevel hprime hprime2 hlevel hne).toULiftFinitePGroup

@[simp]
theorem fermatMuFlatHZeroFinitePGroupOfPrimeLevel_length
    {coeffPrime level : ℕ} (hprime : coeffPrime.Prime) (hprime2 : coeffPrime ≠ 2)
    (hlevel : level.Prime) (hne : level ≠ coeffPrime) :
    (fermatMuFlatHZeroFinitePGroupOfPrimeLevel hprime hprime2 hlevel hne).length = 0 :=
  rfl

/-- Low-degree Euler consumer for an actual sequence whose kernel `H⁰` endpoint is the
canonical multiplicative-flat group.  The checked `p⁰` certificate removes the kernel
degree-zero correction from the numerical bound.  All other groups and exactness data remain in
the supplied low-degree sequence. -/
theorem middleHOne_length_le_of_fermatMuFlatKernelHZero
    {coeffPrime level : ℕ} (hprime : coeffPrime.Prime) (hprime2 : coeffPrime ≠ 2)
    (hlevel : level.Prime) (hne : level ≠ coeffPrime)
    (D : FiniteFlatCommGroupScheme.FppfLowDegreeExactSequence.{1} coeffPrime)
    (hkernel : D.kernelHZero =
      fermatMuFlatHZeroFinitePGroupOfPrimeLevel hprime hprime2 hlevel hne)
    (bound : ℕ)
    (hbound :
      D.middleHZero.length + D.kernelHOne.length + D.quotientHOne.length ≤
        bound + D.quotientHZero.length) :
    D.middleHOne.length ≤ bound := by
  apply D.middleHOne_length_le hprime bound
  rw [hkernel]
  simpa using hbound

end AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme

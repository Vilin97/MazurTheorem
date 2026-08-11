/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenTwoDescentUnits
import MazurTorsion.NumberTheory.XOneThirteenTwoDescentModTwoCertificate
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# Unit-squareclass certificates for the `X₁(13)` two-descent field

The sextic field contains a checked square root of `-1`, so it is totally
complex.  Its signature is therefore `(0,3)`, and Dirichlet's theorem gives
unit rank two.

For the two-descent one does not need the stronger assertion that the two
displayed units generate the full integral unit group.  The quotient of the
unit group by squares has three binary coordinates: one from its finite
cyclic torsion subgroup and two from the free rank.  It is enough to check
that the displayed classes of `i`, `u₁`, and `u₂` are independent.

The second half of this file performs the relevant 64-element residue-ring
calculation.  Every one of the seven nonidentity products has a nonzero odd
coefficient modulo `2`, and hence cannot be a square.  A separate integral
power-basis bridge identifies these vectors with the reductions of the
actual units.
-/

namespace MazurTorsion.XOneThirteenTwoDescentUnitSquareclasses

open Module NumberField NumberField.InfinitePlace NumberField.Units Polynomial
open XOneThirteenTwoDescentSextic
open XOneThirteenTwoDescentUnits

noncomputable section

local instance : Fact (Irreducible rationalSextic) :=
  ⟨rationalSextic_irreducible⟩

/-- The sextic two-descent field has degree six. -/
theorem sexticField_finrank : finrank ℚ SexticField = 6 := by
  rw [show finrank ℚ SexticField = rationalSextic.natDegree from
    finrank_quotient_span_eq_natDegree]
  rw [rationalSextic_eq_map, sextic_monic.natDegree_map,
    sextic_isMonicOfDegree.natDegree_eq]

/-- The checked square root of `-1` rules out every real infinite place. -/
instance sexticField_isTotallyComplex : IsTotallyComplex SexticField where
  isComplex w := by
    rw [← not_isReal_iff_isComplex]
    intro hw
    let phi : SexticField →+* ℝ := embedding_of_isReal hw
    have himpossible : (phi sqrtNegOne) ^ 2 = -1 := by
      rw [← map_pow, sqrtNegOne_sq, map_neg, map_one]
    nlinarith [sq_nonneg (phi sqrtNegOne)]

/-- The signature of the sextic field is `(0,3)`. -/
theorem sexticField_nrComplexPlaces : nrComplexPlaces SexticField = 3 := by
  have hsignature := IsTotallyComplex.finrank SexticField
  rw [sexticField_finrank] at hsignature
  omega

/-- Dirichlet's theorem gives free unit rank two. -/
theorem sexticField_unitRank : Units.rank SexticField = 2 := by
  rw [Units.rank, card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero, sexticField_nrComplexPlaces]

/-! ## The seven nontrivial residue products -/

namespace ResidueCertificate

open XOneThirteenTwoDescentModTwoCertificate

/-- The exact reduction of the checked square root of `-1` in the integral
power basis `1,a,...,a⁵`. -/
def sqrtNegOneResidue : V := ![1, 1, 1, 1, 0, 1]

/-- Three bits indexing products of `i`, `u₁`, and `u₂`. -/
abbrev UnitBits := Fin 3 → F2

/-- The fixed residue-ring product `i^e * u₁^f * u₂^g`. -/
def unitResidueRepresentative (bits : UnitBits) : V :=
  quotientMul
    (quotientMul
      (if bits 0 = 0 then one else sqrtNegOneResidue)
      (if bits 1 = 0 then one else u1))
    (if bits 2 = 0 then one else u2)

/-- There are exactly eight products in the three-bit certificate. -/
theorem card_unitBits : Fintype.card UnitBits = 8 := by
  decide

/-- Every nonidentity product of the three displayed unit residues is a
nonsquare in `F₂[a]/(a⁶+a⁴+1)`. -/
theorem nontrivial_unitResidueRepresentative_not_square
    (bits : UnitBits) (hbits : bits ≠ 0) :
    ¬ XOneThirteenTwoDescentModTwoCertificate.IsSquare
      (unitResidueRepresentative bits) := by
  rw [isSquare_iff_odd_coefficients_eq_zero]
  revert hbits
  decide +revert

/-- Equivalently, squarehood of a displayed product forces all three
exponents to vanish. -/
theorem unitBits_eq_zero_of_residue_square
    (bits : UnitBits)
    (hsquare : XOneThirteenTwoDescentModTwoCertificate.IsSquare
      (unitResidueRepresentative bits)) :
    bits = 0 := by
  by_contra hbits
  exact nontrivial_unitResidueRepresentative_not_square bits hbits hsquare

end ResidueCertificate

end


end MazurTorsion.XOneThirteenTwoDescentUnitSquareclasses

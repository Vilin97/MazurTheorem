/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenTwoDescentMinkowski
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients

/-!
# Small-prime inertia certificates for the `X₁(13)` descent field

The defining sextic has irreducible reduction of degree six modulo `3`.
Modulo `2` it is the square of the irreducible cubic
`X³ + X² + 1`.  This file records those finite polynomial certificates;
the residue-field bridge below will turn them into the two inertia hypotheses
used by the Minkowski cutoff.
-/

namespace MazurTorsion.XOneThirteenTwoDescentInertia

open Polynomial
open NumberField RingOfIntegers
open scoped NumberField
open XOneThirteenTwoDescentSextic

noncomputable section

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Irreducible rationalSextic) :=
  ⟨rationalSextic_irreducible⟩

/-- The unique cubic factor needed at the ramified prime `2`. -/
def cubicModTwo : (ZMod 2)[X] := X ^ 3 + X ^ 2 + 1

theorem cubicModTwo_natDegree : cubicModTwo.natDegree = 3 := by
  simp only [cubicModTwo]
  compute_degree!

theorem cubicModTwo_monic : cubicModTwo.Monic := by
  simp only [cubicModTwo]
  monicity!

/-- The cubic factor has no root in `𝔽₂`, hence is irreducible. -/
theorem cubicModTwo_irreducible : Irreducible cubicModTwo := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [cubicModTwo_natDegree]
    norm_num
  · intro x
    unfold Polynomial.IsRoot
    simp only [cubicModTwo, eval_add, eval_pow, eval_X, eval_one]
    fin_cases x <;> decide

/-- The integral defining sextic reduced modulo `2`. -/
def sexticModTwo : (ZMod 2)[X] :=
  sextic.map (Int.castRingHom (ZMod 2))

/-- Exact repeated-factor identity at `2`. -/
theorem sexticModTwo_eq_cubic_sq : sexticModTwo = cubicModTwo ^ 2 := by
  simp [sexticModTwo, sextic, cubicModTwo]
  ring_nf
  reduce_mod_char

/-! ## Passage to residue fields -/

/-- The distinguished sextic root as an algebraic integer. -/
def thetaInteger : 𝓞 SexticField :=
  ⟨theta, by
    refine ⟨sextic, sextic_monic, ?_⟩
    simpa [sextic] using theta_spec⟩

@[simp]
theorem thetaInteger_coe : (thetaInteger : SexticField) = theta := rfl

/-- The integral sextic equation in the full ring of integers. -/
theorem thetaInteger_spec :
    thetaInteger ^ 6 + 2 * thetaInteger ^ 5 + thetaInteger ^ 4 +
      2 * thetaInteger ^ 3 + 6 * thetaInteger ^ 2 +
      4 * thetaInteger + 1 = 0 := by
  apply NumberField.RingOfIntegers.ext
  exact theta_spec

/-- At every prime of the sextic field above `3`, reduction of the integral
root has the irreducible degree-six polynomial already certified in
`XOneThirteenTwoDescentSextic`. -/
theorem inertiaDeg_three_ge_six
    (P : Ideal (𝓞 SexticField))
    (hP : P ∈ Ideal.primesOver
      (Ideal.span ({(3 : ℤ)} : Set ℤ)) (𝓞 SexticField)) :
    6 ≤ P.inertiaDeg ℤ := by
  let p : Ideal ℤ := Ideal.span ({(3 : ℤ)} : Set ℤ)
  have hpMax : p.IsMaximal := by
    simpa [p] using Int.ideal_span_isMaximal_of_prime 3
  have hPMax : P.IsMaximal := Ideal.isMaximal_of_mem_primesOver hP
  letI : p.IsMaximal := hpMax
  letI : P.IsMaximal := hPMax
  have hLies : P.LiesOver p := by simpa [p] using hP.2
  letI : P.LiesOver p := hLies
  have hpNe : p ≠ ⊥ := by simp [p]
  have hPNe : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hpNe hP
  letI : Finite ((𝓞 SexticField) ⧸ P) :=
    Ring.HasFiniteQuotients.finiteQuotient hPNe
  rw [Ideal.inertiaDeg_eq_of_isMaximal p P]
  let e : (ℤ ⧸ p) ≃+* ZMod 3 := by
    simpa [p] using Int.quotientSpanNatEquivZMod 3
  letI : Algebra (ZMod 3) ((𝓞 SexticField) ⧸ P) :=
    ((algebraMap (ℤ ⧸ p) ((𝓞 SexticField) ⧸ P)).comp
      e.symm.toRingHom).toAlgebra
  letI : Module.Finite (ZMod 3) ((𝓞 SexticField) ⧸ P) :=
    Module.Finite.of_finite
  have hfinrank :
      Module.finrank (ℤ ⧸ p) ((𝓞 SexticField) ⧸ P) =
        Module.finrank (ZMod 3) ((𝓞 SexticField) ⧸ P) := by
    apply Algebra.finrank_eq_of_equiv_equiv e
      (RingEquiv.refl ((𝓞 SexticField) ⧸ P))
    ext x
    change algebraMap (ℤ ⧸ p) ((𝓞 SexticField) ⧸ P)
      (e.symm (e x)) = algebraMap (ℤ ⧸ p) ((𝓞 SexticField) ⧸ P) x
    rw [e.symm_apply_apply]
  rw [hfinrank]
  let y : (𝓞 SexticField) ⧸ P := Ideal.Quotient.mk P thetaInteger
  have hy :
      y ^ 6 + 2 * y ^ 5 + y ^ 4 + 2 * y ^ 3 + 6 * y ^ 2 +
        4 * y + 1 = 0 := by
    exact congrArg (Ideal.Quotient.mk P) thetaInteger_spec
  have hroot : Polynomial.aeval y sexticModThree = 0 := by
    simpa [sexticModThree, sextic, aeval_def] using hy
  have hmin : minpoly (ZMod 3) y = sexticModThree :=
    (minpoly.eq_of_irreducible_of_monic sexticModThree_irreducible hroot
      (sextic_monic.map (Int.castRingHom (ZMod 3)))).symm
  have hdegree := minpoly.natDegree_le (A := ZMod 3) y
  rw [hmin, sexticModThree_natDegree] at hdegree
  exact hdegree

/-- At every prime above `2`, the reduced integral root is annihilated by
the irreducible cubic factor.  The quotient by a maximal ideal is a field,
so the square of that cubic value vanishing forces the value itself to
vanish. -/
theorem inertiaDeg_two_ge_three
    (P : Ideal (𝓞 SexticField))
    (hP : P ∈ Ideal.primesOver
      (Ideal.span ({(2 : ℤ)} : Set ℤ)) (𝓞 SexticField)) :
    3 ≤ P.inertiaDeg ℤ := by
  let p : Ideal ℤ := Ideal.span ({(2 : ℤ)} : Set ℤ)
  have hpMax : p.IsMaximal := by
    simpa [p] using Int.ideal_span_isMaximal_of_prime 2
  have hPMax : P.IsMaximal := Ideal.isMaximal_of_mem_primesOver hP
  letI : p.IsMaximal := hpMax
  letI : P.IsMaximal := hPMax
  have hLies : P.LiesOver p := by simpa [p] using hP.2
  letI : P.LiesOver p := hLies
  have hpNe : p ≠ ⊥ := by simp [p]
  have hPNe : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hpNe hP
  letI : Finite ((𝓞 SexticField) ⧸ P) :=
    Ring.HasFiniteQuotients.finiteQuotient hPNe
  rw [Ideal.inertiaDeg_eq_of_isMaximal p P]
  let e : (ℤ ⧸ p) ≃+* ZMod 2 := by
    simpa [p] using Int.quotientSpanNatEquivZMod 2
  letI : Algebra (ZMod 2) ((𝓞 SexticField) ⧸ P) :=
    ((algebraMap (ℤ ⧸ p) ((𝓞 SexticField) ⧸ P)).comp
      e.symm.toRingHom).toAlgebra
  letI : Module.Finite (ZMod 2) ((𝓞 SexticField) ⧸ P) :=
    Module.Finite.of_finite
  have hfinrank :
      Module.finrank (ℤ ⧸ p) ((𝓞 SexticField) ⧸ P) =
        Module.finrank (ZMod 2) ((𝓞 SexticField) ⧸ P) := by
    apply Algebra.finrank_eq_of_equiv_equiv e
      (RingEquiv.refl ((𝓞 SexticField) ⧸ P))
    ext x
    change algebraMap (ℤ ⧸ p) ((𝓞 SexticField) ⧸ P)
      (e.symm (e x)) = algebraMap (ℤ ⧸ p) ((𝓞 SexticField) ⧸ P) x
    rw [e.symm_apply_apply]
  rw [hfinrank]
  let y : (𝓞 SexticField) ⧸ P := Ideal.Quotient.mk P thetaInteger
  have hy :
      y ^ 6 + 2 * y ^ 5 + y ^ 4 + 2 * y ^ 3 + 6 * y ^ 2 +
        4 * y + 1 = 0 := by
    exact congrArg (Ideal.Quotient.mk P) thetaInteger_spec
  have hsextic : Polynomial.aeval y sexticModTwo = 0 := by
    simpa [sexticModTwo, sextic, aeval_def] using hy
  have hcubicSq : (Polynomial.aeval y cubicModTwo) ^ 2 = 0 := by
    rw [← map_pow, ← sexticModTwo_eq_cubic_sq]
    exact hsextic
  have hroot : Polynomial.aeval y cubicModTwo = 0 :=
    (sq_eq_zero_iff).mp hcubicSq
  have hmin : minpoly (ZMod 2) y = cubicModTwo :=
    (minpoly.eq_of_irreducible_of_monic cubicModTwo_irreducible hroot
      cubicModTwo_monic).symm
  have hdegree := minpoly.natDegree_le (A := ZMod 2) y
  rw [hmin, cubicModTwo_natDegree] at hdegree
  exact hdegree

/-- The two residue-field certificates discharge the entire ideal-theoretic
part of the class-number-one criterion. -/
theorem classNumber_eq_one_of_discr_le
    (hdisc : |NumberField.discr SexticField| ≤ 10816) :
    NumberField.classNumber SexticField = 1 := by
  apply
    XOneThirteenTwoDescentMinkowski.classNumber_eq_one_of_discr_le_of_small_prime_inertia
      hdisc
  · exact inertiaDeg_two_ge_three
  · intro P hP
    exact le_trans (by norm_num) (inertiaDeg_three_ge_six P hP)

end

end MazurTorsion.XOneThirteenTwoDescentInertia

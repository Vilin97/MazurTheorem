/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenCyclotomicResultants
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Norm.Transitivity

/-!
# Cyclotomic-thirteen norms and principal prime ideals

This file transports the exact polynomial resultants for `Φ₁₃` to algebra
norms in the thirteenth cyclotomic field and then exhibits a principal prime
ideal above `53`.  It does not make a class-number claim.
-/

namespace MazurTorsion.XOneThirteenCyclotomic

open Algebra IsCyclotomicExtension NumberField Polynomial
open scoped Cyclotomic NumberField

noncomputable section

section PowerBasisNorm

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Evaluating a polynomial at the generator of a separable field power basis
has algebra norm equal to its resultant against the generator's minimal
polynomial. -/
theorem PowerBasis.norm_aeval_eq_resultant [FiniteDimensional K L]
    [Algebra.IsSeparable K L] (pb : PowerBasis K L) (g : K[X]) :
    Algebra.norm K (aeval pb.gen g) = (minpoly K pb.gen).resultant g := by
  let E := AlgebraicClosure L
  apply (algebraMap K E).injective
  letI : DecidableEq E := Classical.decEq E
  rw [Algebra.norm_eq_prod_embeddings]
  have hprod :
      (∏ σ : L →ₐ[K] E, σ (aeval pb.gen g)) =
        (((minpoly K pb.gen).aroots E).map fun y => aeval y g).prod := by
    rw [Fintype.prod_equiv pb.liftEquiv'
      (fun σ => σ (aeval pb.gen g)) (fun y => aeval (y : E) g)]
    · rw [Finset.prod_mem_multiset, Finset.prod_eq_multiset_prod,
        Multiset.toFinset_val, Multiset.dedup_eq_self.mpr]
      · exact nodup_roots (.map (Algebra.IsSeparable.isSeparable K pb.gen))
      · intro x
        rfl
    · intro σ
      rw [← aeval_algHom_apply]
      simp only [PowerBasis.liftEquiv'_apply_coe]
  rw [hprod]
  rw [← resultant_map_map]
  have hres := resultant_eq_prod_eval
    ((minpoly K pb.gen).map (algebraMap K E))
    (g.map (algebraMap K E)) g.natDegree
    (by simp) (IsAlgClosed.splits _)
  simpa [aroots_def, (minpoly.monic pb.isIntegral_gen).leadingCoeff,
    eval_map_algebraMap, aeval_def] using hres.symm

end PowerBasisNorm

section IntegralCyclotomicNorm

variable {n : ℕ} [NeZero n] {K : Type*} [Field K] [NumberField K]
  [IsCyclotomicExtension {n} ℚ K] {ζ : K}

/-- An integral polynomial evaluated at a primitive cyclotomic generator has
integer norm equal to its ordinary resultant against the cyclotomic
polynomial. -/
theorem IsPrimitiveRoot.norm_aeval_toInteger_eq_resultant_cyclotomic
    (hζ : IsPrimitiveRoot ζ n) (g : ℤ[X]) :
    Algebra.norm ℤ (aeval hζ.toInteger g) =
      (Polynomial.cyclotomic n ℤ).resultant g := by
  apply Int.cast_injective (α := ℚ)
  rw [Algebra.coe_norm_int]
  have heval :
      ((aeval hζ.toInteger g : 𝓞 K) : K) =
        aeval ζ (g.map (algebraMap ℤ ℚ)) := by
    change (algebraMap (𝓞 K) K) (aeval hζ.toInteger g) = _
    rw [map_aeval_eq_aeval_map
      (show (algebraMap ℚ K).comp (algebraMap ℤ ℚ) =
          (algebraMap (𝓞 K) K).comp (algebraMap ℤ (𝓞 K)) by
        ext x
        simp) g hζ.toInteger]
    rfl
  rw [heval, ← hζ.powerBasis_gen ℚ,
    PowerBasis.norm_aeval_eq_resultant, hζ.powerBasis_gen ℚ,
    ← hζ.minpoly_eq_cyclotomic_of_irreducible
      (cyclotomic.irreducible_rat (NeZero.pos n))]
  change (cyclotomic n ℚ).resultant (g.map (algebraMap ℤ ℚ)) =
    (algebraMap ℤ ℚ) ((cyclotomic n ℤ).resultant g)
  have hmap := resultant_map_map
    (f := cyclotomic n ℤ) (g := g)
    (m := (cyclotomic n ℤ).natDegree) (n := g.natDegree)
    (algebraMap ℤ ℚ)
  have hinj : Function.Injective (algebraMap ℤ ℚ) :=
    RingHom.injective_int _
  rw [map_cyclotomic] at hmap
  have hcyclotomicDegree :
      (cyclotomic n ℚ).natDegree = (cyclotomic n ℤ).natDegree := by
    simp only [natDegree_cyclotomic]
  have hgDegree :
      (g.map (algebraMap ℤ ℚ)).natDegree = g.natDegree :=
    natDegree_map_eq_of_injective hinj g
  simpa only [hcyclotomicDegree, hgDegree] using hmap

end IntegralCyclotomicNorm

section Thirteen

/-- The thirteenth cyclotomic field over `ℚ`. -/
abbrev ThirteenCyclotomicField := CyclotomicField 13 ℚ

local instance : IsCyclotomicExtension {13} ℚ ThirteenCyclotomicField :=
  CyclotomicField.isCyclotomicExtension 13 ℚ

/-- Mathlib's chosen primitive thirteenth root in the cyclotomic field. -/
noncomputable def zetaThirteen : ThirteenCyclotomicField :=
  IsCyclotomicExtension.zeta 13 ℚ ThirteenCyclotomicField

/-- The chosen root really is primitive of order thirteen. -/
theorem zetaThirteen_spec : IsPrimitiveRoot zetaThirteen 13 :=
  IsCyclotomicExtension.zeta_spec 13 ℚ ThirteenCyclotomicField

/-- The chosen primitive root as an algebraic integer. -/
noncomputable def zetaThirteenInteger : 𝓞 ThirteenCyclotomicField :=
  zetaThirteen_spec.toInteger

/-- Evaluate an integral polynomial at the chosen integral primitive root. -/
noncomputable def evalAtZetaThirteen (g : ℤ[X]) :
    𝓞 ThirteenCyclotomicField :=
  aeval zetaThirteenInteger g

/-- The norm/resultant bridge specialized to the chosen thirteenth root. -/
theorem norm_evalAtZetaThirteen (g : ℤ[X]) :
    Algebra.norm ℤ (evalAtZetaThirteen g) =
      (Polynomial.cyclotomic 13 ℤ).resultant g := by
  unfold evalAtZetaThirteen zetaThirteenInteger
  exact IsPrimitiveRoot.norm_aeval_toInteger_eq_resultant_cyclotomic
    zetaThirteen_spec g

/-- The algebraic integer represented by `1 - ζ`. -/
noncomputable def alphaThirteenInteger : 𝓞 ThirteenCyclotomicField :=
  evalAtZetaThirteen alphaThirteen

/-- The algebraic integer represented by `ζ³ - ζ - 1`. -/
noncomputable def alphaTwentySevenInteger : 𝓞 ThirteenCyclotomicField :=
  evalAtZetaThirteen alphaTwentySeven

/-- The algebraic integer represented by `1 - ζ² + ζ³`. -/
noncomputable def alphaFiftyThreeInteger : 𝓞 ThirteenCyclotomicField :=
  evalAtZetaThirteen alphaFiftyThree

/-- The algebraic integer represented by `1 - ζ + ζ² + ζ⁶`. -/
noncomputable def alphaSeventyNineInteger : 𝓞 ThirteenCyclotomicField :=
  evalAtZetaThirteen alphaSeventyNine

/-- The algebraic integer represented by `-1 + ζ² + ζ⁶`. -/
noncomputable def alphaOneThirtyOneInteger : 𝓞 ThirteenCyclotomicField :=
  evalAtZetaThirteen alphaOneThirtyOne

/-- The algebraic integer represented by `ζ + ζ⁴ + ζ⁵ + ζ⁷`. -/
noncomputable def alphaOneFiftySevenInteger : 𝓞 ThirteenCyclotomicField :=
  evalAtZetaThirteen alphaOneFiftySeven

/-- The exact norm of `1 - ζ`. -/
theorem norm_alphaThirteenInteger :
    Algebra.norm ℤ alphaThirteenInteger = 13 := by
  rw [alphaThirteenInteger, norm_evalAtZetaThirteen,
    ← phiThirteen_eq_cyclotomic]
  exact phiThirteen_resultant_alphaThirteen

/-- The exact norm of `ζ³ - ζ - 1`. -/
theorem norm_alphaTwentySevenInteger :
    Algebra.norm ℤ alphaTwentySevenInteger = 27 := by
  rw [alphaTwentySevenInteger, norm_evalAtZetaThirteen,
    ← phiThirteen_eq_cyclotomic]
  exact phiThirteen_resultant_alphaTwentySeven

/-- The exact norm of `1 - ζ² + ζ³`. -/
theorem norm_alphaFiftyThreeInteger :
    Algebra.norm ℤ alphaFiftyThreeInteger = 53 := by
  rw [alphaFiftyThreeInteger, norm_evalAtZetaThirteen,
    ← phiThirteen_eq_cyclotomic]
  exact phiThirteen_resultant_alphaFiftyThree

/-- The exact norm of `1 - ζ + ζ² + ζ⁶`. -/
theorem norm_alphaSeventyNineInteger :
    Algebra.norm ℤ alphaSeventyNineInteger = 79 := by
  rw [alphaSeventyNineInteger, norm_evalAtZetaThirteen,
    ← phiThirteen_eq_cyclotomic]
  exact phiThirteen_resultant_alphaSeventyNine

/-- The exact norm of `-1 + ζ² + ζ⁶`. -/
theorem norm_alphaOneThirtyOneInteger :
    Algebra.norm ℤ alphaOneThirtyOneInteger = 131 := by
  rw [alphaOneThirtyOneInteger, norm_evalAtZetaThirteen,
    ← phiThirteen_eq_cyclotomic]
  exact phiThirteen_resultant_alphaOneThirtyOne

/-- The exact norm of `ζ + ζ⁴ + ζ⁵ + ζ⁷`. -/
theorem norm_alphaOneFiftySevenInteger :
    Algebra.norm ℤ alphaOneFiftySevenInteger = 157 := by
  rw [alphaOneFiftySevenInteger, norm_evalAtZetaThirteen,
    ← phiThirteen_eq_cyclotomic]
  exact phiThirteen_resultant_alphaOneFiftySeven

/-- The six exact algebra-norm computations, bundled for downstream ideal
calculations. -/
theorem alphaInteger_norm_certificates :
    Algebra.norm ℤ alphaThirteenInteger = 13 ∧
      Algebra.norm ℤ alphaTwentySevenInteger = 27 ∧
      Algebra.norm ℤ alphaFiftyThreeInteger = 53 ∧
      Algebra.norm ℤ alphaSeventyNineInteger = 79 ∧
      Algebra.norm ℤ alphaOneThirtyOneInteger = 131 ∧
      Algebra.norm ℤ alphaOneFiftySevenInteger = 157 :=
  ⟨norm_alphaThirteenInteger,
    norm_alphaTwentySevenInteger,
    norm_alphaFiftyThreeInteger,
    norm_alphaSeventyNineInteger,
    norm_alphaOneThirtyOneInteger,
    norm_alphaOneFiftySevenInteger⟩

/-- The principal ideal generated by `1 - ζ² + ζ³`. -/
noncomputable def fiftyThreeIdeal : Ideal (𝓞 ThirteenCyclotomicField) :=
  Ideal.span {alphaFiftyThreeInteger}

/-- The displayed ideal is principal by construction. -/
theorem fiftyThreeIdeal_isPrincipal : fiftyThreeIdeal.IsPrincipal := by
  unfold fiftyThreeIdeal
  infer_instance

/-- The absolute norm of the displayed principal ideal is `53`. -/
theorem fiftyThreeIdeal_absNorm : Ideal.absNorm fiftyThreeIdeal = 53 := by
  rw [fiftyThreeIdeal, Ideal.absNorm_span_singleton,
    norm_alphaFiftyThreeInteger]
  norm_num

/-- The displayed principal ideal is prime. -/
theorem fiftyThreeIdeal_isPrime : fiftyThreeIdeal.IsPrime := by
  apply Ideal.isPrime_of_irreducible_absNorm
  rw [fiftyThreeIdeal_absNorm]
  rw [Nat.irreducible_iff_prime]
  decide

/-- Contracting the displayed ideal to `ℤ` gives the rational prime ideal
`(53)`. -/
theorem fiftyThreeIdeal_comap :
    fiftyThreeIdeal.comap
        (algebraMap ℤ (𝓞 ThirteenCyclotomicField)) =
      Ideal.span ({(53 : ℤ)} : Set ℤ) := by
  have h := Ideal.span_singleton_absNorm
    (I := fiftyThreeIdeal) (by
      rw [fiftyThreeIdeal_absNorm]
      decide)
  simpa [fiftyThreeIdeal_absNorm] using h.symm

/-- The displayed principal prime ideal lies above `(53)`. -/
theorem fiftyThreeIdeal_liesOver :
    fiftyThreeIdeal.LiesOver (Ideal.span ({(53 : ℤ)} : Set ℤ)) :=
  ⟨fiftyThreeIdeal_comap.symm⟩

/-- A single checked package recording principality, primality, residue
characteristic, and absolute norm of the displayed ideal. -/
theorem fiftyThreeIdeal_certificate :
    fiftyThreeIdeal.IsPrincipal ∧
      fiftyThreeIdeal.IsPrime ∧
      fiftyThreeIdeal.LiesOver (Ideal.span ({(53 : ℤ)} : Set ℤ)) ∧
      Ideal.absNorm fiftyThreeIdeal = 53 :=
  ⟨fiftyThreeIdeal_isPrincipal, fiftyThreeIdeal_isPrime,
    fiftyThreeIdeal_liesOver, fiftyThreeIdeal_absNorm⟩

end Thirteen

end

end MazurTorsion.XOneThirteenCyclotomic

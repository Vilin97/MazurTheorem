/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneThirteenTwoDescentSextic
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.IntermediateField.Basic

/-!
# A quadratic subfield of the `X₁(13)` sextic descent field

The checked element `sqrtNegOne` realizes the Gaussian rational field
`ℚ[X]/(X²+1)` inside the sextic field.  This file constructs the algebra
embedding explicitly and records that its image is an intermediate field of
degree two over `ℚ`.
-/

namespace MazurTorsion.XOneThirteenTwoDescentQuadraticSubfield

open Module Polynomial
open XOneThirteenTwoDescentSextic

noncomputable section

local instance : Fact (Irreducible rationalSextic) :=
  ⟨rationalSextic_irreducible⟩

/-- The polynomial cutting out the Gaussian rational field. -/
def gaussianPolynomial : ℚ[X] := X ^ 2 + 1

theorem gaussianPolynomial_natDegree : gaussianPolynomial.natDegree = 2 := by
  simp only [gaussianPolynomial]
  compute_degree!

/-- The polynomial `X²+1` has no rational root and is irreducible over `ℚ`. -/
theorem gaussianPolynomial_irreducible : Irreducible gaussianPolynomial := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp [gaussianPolynomial_natDegree]
  · intro x hx
    simp only [IsRoot.def, gaussianPolynomial, eval_add, eval_pow, eval_X,
      eval_one] at hx
    nlinarith [sq_nonneg x]

instance gaussianPolynomial_irreducibleFact :
    Fact (Irreducible gaussianPolynomial) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- The Gaussian rational field, presented as an explicit adjoined root. -/
abbrev GaussianRationals := AdjoinRoot gaussianPolynomial

/-- The Gaussian rational field has degree two over `ℚ`. -/
theorem gaussianRationals_finrank : finrank ℚ GaussianRationals = 2 := by
  rw [show finrank ℚ GaussianRationals = gaussianPolynomial.natDegree from
    finrank_quotient_span_eq_natDegree]
  exact gaussianPolynomial_natDegree

private theorem gaussianPolynomial_aeval_sqrtNegOne :
    gaussianPolynomial.eval₂ (algebraMap ℚ SexticField) sqrtNegOne = 0 := by
  simp [gaussianPolynomial, sqrtNegOne_sq]

/-- The explicit `ℚ`-algebra map sending the Gaussian root to the checked
square root of `-1` in the sextic field. -/
def gaussianRationalEmbedding : GaussianRationals →ₐ[ℚ] SexticField :=
  AdjoinRoot.liftAlgHom gaussianPolynomial (Algebra.ofId ℚ SexticField)
    sqrtNegOne gaussianPolynomial_aeval_sqrtNegOne

@[simp]
theorem gaussianRationalEmbedding_root :
    gaussianRationalEmbedding (AdjoinRoot.root gaussianPolynomial) = sqrtNegOne := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The explicit Gaussian-rational map into the sextic field is injective. -/
theorem gaussianRationalEmbedding_injective :
    Function.Injective gaussianRationalEmbedding :=
  gaussianRationalEmbedding.injective

/-- The checked square root of `-1` is not rational. -/
theorem sqrtNegOne_not_rational :
    sqrtNegOne ∉ Set.range (algebraMap ℚ SexticField) := by
  rintro ⟨q, hq⟩
  have hsq : (algebraMap ℚ SexticField q) ^ 2 = -1 := by
    rw [hq]
    exact sqrtNegOne_sq
  have hq_sq : q ^ 2 = -1 := by
    apply (algebraMap ℚ SexticField).injective
    simpa only [map_pow, map_neg, map_one] using hsq
  nlinarith [sq_nonneg q]

/-- The image of the explicit Gaussian-rational embedding, as an
intermediate field of the sextic field. -/
def gaussianRationalSubfield : IntermediateField ℚ SexticField :=
  gaussianRationalEmbedding.fieldRange

theorem sqrtNegOne_mem_gaussianRationalSubfield :
    sqrtNegOne ∈ gaussianRationalSubfield := by
  exact ⟨AdjoinRoot.root gaussianPolynomial, gaussianRationalEmbedding_root⟩

/-- The explicit intermediate field has degree two over `ℚ`. -/
theorem gaussianRationalSubfield_finrank :
    finrank ℚ gaussianRationalSubfield = 2 := by
  rw [← gaussianRationals_finrank]
  exact (LinearEquiv.finrank_eq
    gaussianRationalEmbedding.equivFieldRange.toLinearEquiv).symm

/-- The sextic descent field contains a quadratic extension of `ℚ`. -/
theorem sexticField_contains_quadratic_extension :
    ∃ K : IntermediateField ℚ SexticField, finrank ℚ K = 2 :=
  ⟨gaussianRationalSubfield, gaussianRationalSubfield_finrank⟩

end

end MazurTorsion.XOneThirteenTwoDescentQuadraticSubfield

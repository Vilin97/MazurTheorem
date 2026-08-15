/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Coordinate algebra for the Segre embedding

This is the exact algebraic core found (in partial form) in Atlas Lean.
The map sends the coordinate indexed by `(i,j)` to `Xᵢ ⊗ Xⱼ`; the
standard quadratic Segre relations lie in its kernel and are homogeneous.

Constructing the corresponding closed immersion of Mathlib's `Proj`
schemes still requires a diagonal-graded tensor-product/Proj comparison,
which is not present at the exact pin.
-/

open MvPolynomial
open scoped TensorProduct

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-- The coordinate-algebra map underlying the Segre embedding. -/
def segreCoordinateHom
    (k : Type u) [CommRing k] (m n : ℕ) :
    MvPolynomial (Fin (m + 1) × Fin (n + 1)) k →ₐ[k]
      MvPolynomial (Fin (m + 1)) k ⊗[k]
        MvPolynomial (Fin (n + 1)) k :=
  MvPolynomial.aeval
    (fun p =>
      MvPolynomial.X p.1 ⊗ₜ[k]
        MvPolynomial.X p.2)

@[simp]
lemma segreCoordinateHom_X
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreCoordinateHom k m n
        (MvPolynomial.X (i, j)) =
      MvPolynomial.X i ⊗ₜ[k]
        MvPolynomial.X j := by
  simp [segreCoordinateHom]

/-- The `2 × 2` minor relations vanish under the Segre coordinate
map. -/
lemma segreCoordinateHom_relation
    (k : Type u) [CommRing k] (m n : ℕ)
    (i i' : Fin (m + 1))
    (j j' : Fin (n + 1)) :
    segreCoordinateHom k m n
      (MvPolynomial.X (i, j) *
          MvPolynomial.X (i', j') -
        MvPolynomial.X (i', j) *
          MvPolynomial.X (i, j')) =
      0 := by
  simp only [map_sub, map_mul, segreCoordinateHom_X]
  simp only [Algebra.TensorProduct.tmul_mul_tmul]
  ring_nf

/-- Every defining `2 × 2` minor is homogeneous of degree two in the
standard grading on the source polynomial ring. -/
lemma segreRelation_isHomogeneous
    (k : Type u) [CommRing k] (m n : ℕ)
    (i i' : Fin (m + 1))
    (j j' : Fin (n + 1)) :
    letI :=
      @MvPolynomial.gradedAlgebra
        (Fin (m + 1) × Fin (n + 1)) k _
    (MvPolynomial.X (i, j) *
          MvPolynomial.X (i', j') -
        MvPolynomial.X (i', j) *
          MvPolynomial.X (i, j') :
      MvPolynomial
        (Fin (m + 1) × Fin (n + 1)) k).IsHomogeneous 2 := by
  letI :=
    @MvPolynomial.gradedAlgebra
      (Fin (m + 1) × Fin (n + 1)) k _
  apply MvPolynomial.IsHomogeneous.sub
  · exact
      (MvPolynomial.isHomogeneous_X _ _).mul
        (MvPolynomial.isHomogeneous_X _ _)
  · exact
      (MvPolynomial.isHomogeneous_X _ _).mul
        (MvPolynomial.isHomogeneous_X _ _)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

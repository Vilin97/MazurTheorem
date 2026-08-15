/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.HomogeneousAwayCoefficientAlgebra
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSpaceStandardCover

/-!
# Algebra on a standard projective coordinate chart

The coordinate chart `D₊(Xᵢ)` has coordinate ring given by the
degree-zero homogeneous localization away from `Xᵢ`.  This file defines
the usual ratios `Xⱼ / Xᵢ` and the dehomogenization algebra map obtained
by evaluating every variable at its ratio.
-/

open MvPolynomial
open HomogeneousLocalization

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-- The coordinate ring of the standard chart `D₊(Xᵢ)`. -/
abbrev ProjectiveCoordinateAway
    (k : Type u) [CommRing k] (d : ℕ)
    (i : Fin (d + 1)) :=
  Away (homogeneousGrading k d) (coordinate k i)

instance projectiveCoordinateAwayAlgebra
    (k : Type u) [CommRing k] (d : ℕ)
    (i : Fin (d + 1)) :
    Algebra k (ProjectiveCoordinateAway k d i) :=
  homogeneousAwayCoefficientAlgebra
    k (MvPolynomial (Fin (d + 1)) k)
    (homogeneousGrading k d) (coordinate k i)

/-- The standard chart ring, viewed inside the ordinary localization
of the homogeneous coordinate ring. -/
def projectiveCoordinateAwayValRingHom
    (k : Type u) [CommRing k] (d : ℕ)
    (i : Fin (d + 1)) :
    ProjectiveCoordinateAway k d i →+*
      Localization.Away (coordinate k i) where
  toFun := HomogeneousLocalization.val
  map_zero' := HomogeneousLocalization.val_zero
  map_one' := HomogeneousLocalization.val_one
  map_add' := HomogeneousLocalization.val_add
  map_mul' := HomogeneousLocalization.val_mul

@[simp]
lemma projectiveCoordinateAwayValRingHom_apply
    (k : Type u) [CommRing k] (d : ℕ)
    (i : Fin (d + 1))
    (x : ProjectiveCoordinateAway k d i) :
    projectiveCoordinateAwayValRingHom k d i x =
      HomogeneousLocalization.val x :=
  rfl

/-- The regular function `Xⱼ / Xᵢ` on the standard chart
`D₊(Xᵢ)`. -/
@[reducible]
def projectiveCoordinateRatio
    (k : Type u) [CommRing k] (d : ℕ)
    (i j : Fin (d + 1)) :
    ProjectiveCoordinateAway k d i :=
  Away.mk
    (homogeneousGrading k d)
    (coordinate_mem_degreeOne k i)
    1
    (coordinate k j)
    (by simpa using coordinate_mem_degreeOne k j)

@[simp]
lemma projectiveCoordinateRatio_self
    (k : Type u) [CommRing k] (d : ℕ)
    (i : Fin (d + 1)) :
    projectiveCoordinateRatio k d i i = 1 := by
  apply HomogeneousLocalization.val_injective
  simp [projectiveCoordinateRatio,
    HomogeneousLocalization.Away.val_mk]

/-- Dehomogenize a polynomial on the coordinate chart `D₊(Xᵢ)` by
sending `Xⱼ` to `Xⱼ / Xᵢ`. -/
def projectiveCoordinateDehomogenization
    (k : Type u) [CommRing k] (d : ℕ)
    (i : Fin (d + 1)) :
    MvPolynomial (Fin (d + 1)) k →ₐ[k]
      ProjectiveCoordinateAway k d i :=
  MvPolynomial.aeval
    (projectiveCoordinateRatio k d i)

@[simp]
lemma projectiveCoordinateDehomogenization_X
    (k : Type u) [CommRing k] (d : ℕ)
    (i j : Fin (d + 1)) :
    projectiveCoordinateDehomogenization k d i
        (MvPolynomial.X j) =
      projectiveCoordinateRatio k d i j := by
  simp [projectiveCoordinateDehomogenization]

@[simp]
lemma projectiveCoordinateAway_val_algebraMap
    (k : Type u) [CommRing k] (d : ℕ)
    (i : Fin (d + 1)) (r : k) :
    HomogeneousLocalization.val
        (algebraMap k
          (ProjectiveCoordinateAway k d i) r) =
      algebraMap k
        (Localization.Away (coordinate k i)) r := by
  rw [Algebra.algebraMap_eq_smul_one,
    HomogeneousLocalization.val_smul,
    HomogeneousLocalization.val_one,
    Algebra.smul_def, mul_one]

private lemma projectiveCoordinateRatioProduct_val
    (k : Type u) [CommRing k] (d : ℕ)
    (i : Fin (d + 1))
    (e : Fin (d + 1) →₀ ℕ) :
    e.prod (fun j n =>
      (Localization.mk
        (coordinate k j)
        ⟨coordinate k i ^ 1, ⟨1, rfl⟩⟩ :
        Localization.Away (coordinate k i)) ^ n) =
      (Localization.mk
        (MvPolynomial.monomial e (1 : k))
        ⟨coordinate k i ^ e.degree,
          ⟨e.degree, rfl⟩⟩ :
        Localization.Away (coordinate k i)) := by
  induction e using Finsupp.induction with
  | zero =>
      simp
  | single_add a n e ha hn ih =>
      rw [Finsupp.prod_add_index]
      · rw [Finsupp.prod_single_index (by simp)]
        rw [Localization.mk_pow, ih, Localization.mk_mul]
        congr 1
        · calc
            coordinate k a ^ n *
                MvPolynomial.monomial e (1 : k) =
              MvPolynomial.monomial e (1 : k) *
                coordinate k a ^ n := mul_comm _ _
            _ =
                MvPolynomial.monomial
                  (e + Finsupp.single a n) (1 : k) :=
              (MvPolynomial.monomial_add_single).symm
            _ =
                MvPolynomial.monomial
                  (Finsupp.single a n + e) (1 : k) := by
              rw [add_comm e (Finsupp.single a n)]
        · ext
          simp [map_add, pow_add, mul_comm]
      · simp
      · intro
        simp [pow_add]

/-- Dehomogenizing a monomial is represented by dividing that monomial
by the corresponding power of the chart coordinate. -/
lemma projectiveCoordinateDehomogenization_monomial
    (k : Type u) [CommRing k] (d : ℕ)
    (i : Fin (d + 1))
    (e : Fin (d + 1) →₀ ℕ) (r : k) :
    projectiveCoordinateDehomogenization k d i
        (MvPolynomial.monomial e r) =
      Away.mk
        (homogeneousGrading k d)
        (coordinate_mem_degreeOne k i)
        e.degree
        (MvPolynomial.monomial e r)
        (by
          rw [MvPolynomial.mem_homogeneousSubmodule]
          exact MvPolynomial.isHomogeneous_monomial
            r (by simp)) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk]
  change projectiveCoordinateAwayValRingHom k d i
      (projectiveCoordinateDehomogenization k d i
        (MvPolynomial.monomial e r)) = _
  rw [projectiveCoordinateDehomogenization,
    MvPolynomial.aeval_monomial, map_mul, map_finsuppProd]
  simp_rw [map_pow, projectiveCoordinateAwayValRingHom_apply,
    projectiveCoordinateRatio]
  simp_rw [HomogeneousLocalization.Away.val_mk]
  rw [projectiveCoordinateAway_val_algebraMap,
    projectiveCoordinateRatioProduct_val]
  rw [← Localization.mk_algebraMap, Localization.mk_mul]
  congr 1
  · rw [MvPolynomial.algebraMap_eq,
      MvPolynomial.C_mul_monomial, mul_one]
  · simp

/-- A homogeneous polynomial of degree `n` dehomogenizes to the
homogeneous fraction with denominator `Xᵢⁿ`. -/
lemma projectiveCoordinateDehomogenization_of_homogeneous
    (k : Type u) [CommRing k] (d : ℕ)
    (i : Fin (d + 1))
    (n : ℕ) (p : MvPolynomial (Fin (d + 1)) k)
    (hp : p ∈ homogeneousGrading k d n) :
    projectiveCoordinateDehomogenization k d i p =
      Away.mk
        (homogeneousGrading k d)
        (coordinate_mem_degreeOne k i)
        n p (by simpa using hp) := by
  conv_lhs =>
    rw [MvPolynomial.as_sum p, map_sum]
  apply HomogeneousLocalization.val_injective
  change projectiveCoordinateAwayValRingHom k d i
      (∑ e ∈ p.support,
        projectiveCoordinateDehomogenization k d i
          (MvPolynomial.monomial e
            (MvPolynomial.coeff e p))) = _
  simp only [map_sum, projectiveCoordinateDehomogenization_monomial,
    projectiveCoordinateAwayValRingHom_apply,
    HomogeneousLocalization.Away.val_mk]
  calc
    (∑ e ∈ p.support,
        (Localization.mk
          (MvPolynomial.monomial e
            (MvPolynomial.coeff e p))
          ⟨coordinate k i ^ e.degree,
            ⟨e.degree, rfl⟩⟩ :
          Localization.Away (coordinate k i))) =
        ∑ e ∈ p.support,
          (Localization.mk
            (MvPolynomial.monomial e
              (MvPolynomial.coeff e p))
            ⟨coordinate k i ^ n, ⟨n, rfl⟩⟩ :
            Localization.Away (coordinate k i)) := by
      apply Finset.sum_congr rfl
      intro e he
      have he_degree : e.degree = n := by
        rw [Finsupp.degree_eq_weight_one]
        exact hp (MvPolynomial.mem_support_iff.mp he)
      subst he_degree
      rfl
    _ =
        (Localization.mk
          (∑ e ∈ p.support,
            MvPolynomial.monomial e
              (MvPolynomial.coeff e p))
          ⟨coordinate k i ^ n, ⟨n, rfl⟩⟩ :
          Localization.Away (coordinate k i)) := by
      rw [Localization.mk_sum]
    _ =
        (Localization.mk p
          ⟨coordinate k i ^ n, ⟨n, rfl⟩⟩ :
          Localization.Away (coordinate k i)) := by
      rw [MvPolynomial.support_sum_monomial_coeff]

/-- Dehomogenization onto a standard projective coordinate chart is
surjective. -/
lemma projectiveCoordinateDehomogenization_surjective
    (k : Type u) [CommRing k] (d : ℕ)
    (i : Fin (d + 1)) :
    Function.Surjective
      (projectiveCoordinateDehomogenization k d i) := by
  intro x
  obtain ⟨n, p, hp, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective
      (homogeneousGrading k d)
      (coordinate_mem_degreeOne k i) x
  exact ⟨p,
    projectiveCoordinateDehomogenization_of_homogeneous
      k d i n p (by simpa using hp)⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

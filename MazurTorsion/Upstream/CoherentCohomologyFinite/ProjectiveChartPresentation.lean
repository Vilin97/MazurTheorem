/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineSpaceEmbedding
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveFactorization
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Finite affine presentations inside a projective chart

A surjection `k[x₁, ..., xₙ] → A` extends to a surjection from the
degree-zero coordinate ring of the `X₀`-chart of projective `n`-space.
On spectra, this is a closed immersion into the standard affine chart,
hence a locally closed immersion into projective space.
-/

open CategoryTheory AlgebraicGeometry MvPolynomial

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-- Evaluate homogeneous projective coordinates by sending `X₀` to `1`
and `Xᵢ₊₁` according to an affine polynomial presentation. -/
def homogeneousChartEval
    {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    {n : ℕ} (φ : MvPolynomial (Fin n) k →ₐ[k] A) :
    MvPolynomial (Fin (n + 1)) k →+* A :=
  MvPolynomial.eval₂Hom
    (algebraMap k A)
    (Fin.cases 1 (fun i => φ (MvPolynomial.X i)))

@[simp]
lemma homogeneousChartEval_coordinate_zero
    {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    {n : ℕ} (φ : MvPolynomial (Fin n) k →ₐ[k] A) :
    homogeneousChartEval φ (coordinate k (0 : Fin (n + 1))) = 1 := by
  simp [homogeneousChartEval]

@[simp]
lemma homogeneousChartEval_coordinate_succ
    {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    {n : ℕ} (φ : MvPolynomial (Fin n) k →ₐ[k] A)
    (i : Fin n) :
    homogeneousChartEval φ (coordinate k i.succ) =
      φ (MvPolynomial.X i) := by
  simp [homogeneousChartEval]

/-- The induced map from the coordinate ring of the `X₀`-chart to the
presented affine algebra. -/
def standardChartToAlgebra
    {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    {n : ℕ} (φ : MvPolynomial (Fin n) k →ₐ[k] A) :
    HomogeneousLocalization.Away
        (homogeneousGrading k n) (coordinate k (0 : Fin (n + 1))) →+* A :=
  (Localization.awayLift
      (homogeneousChartEval φ)
      (coordinate k (0 : Fin (n + 1)))
      (by
        rw [homogeneousChartEval_coordinate_zero]
        exact isUnit_one)).comp
    (algebraMap
      (HomogeneousLocalization.Away
        (homogeneousGrading k n) (coordinate k (0 : Fin (n + 1))))
      (Localization.Away (coordinate k (0 : Fin (n + 1)))))

/-- The coefficient-ring map into the coordinate ring of the
`X₀`-chart. -/
def coefficientToStandardChart
    (k : Type u) [CommRing k] (n : ℕ) :
    k →+*
      HomogeneousLocalization.Away
        (homogeneousGrading k n) (coordinate k (0 : Fin (n + 1))) :=
  (HomogeneousLocalization.fromZeroRingHom
      (homogeneousGrading k n)
      (Submonoid.powers (coordinate k (0 : Fin (n + 1))))).comp
    (gradeZeroRingEquiv k n).toRingHom

/-- The `i`-th affine variable, represented on the `X₀`-chart by
`Xᵢ₊₁ / X₀`. -/
def affineVariableInStandardChart
    (k : Type u) [CommRing k] {n : ℕ} (i : Fin n) :
    HomogeneousLocalization.Away
        (homogeneousGrading k n) (coordinate k (0 : Fin (n + 1))) :=
  HomogeneousLocalization.Away.mk
    (homogeneousGrading k n)
    (coordinate_mem_degreeOne k (0 : Fin (n + 1)))
    1
    (coordinate k i.succ)
    (by simpa using coordinate_mem_degreeOne k i.succ)

/-- Map an affine polynomial to the corresponding regular function on
the `X₀`-chart. -/
def affinePolynomialToStandardChart
    (k : Type u) [CommRing k] (n : ℕ) :
    MvPolynomial (Fin n) k →+*
      HomogeneousLocalization.Away
        (homogeneousGrading k n) (coordinate k (0 : Fin (n + 1))) :=
  MvPolynomial.eval₂Hom
    (coefficientToStandardChart k n)
    (affineVariableInStandardChart k)

@[simp]
lemma standardChartToAlgebra_coefficient
    {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    {n : ℕ} (φ : MvPolynomial (Fin n) k →ₐ[k] A) (r : k) :
    standardChartToAlgebra φ
        (coefficientToStandardChart k n r) =
      algebraMap k A r := by
  change
    (Localization.awayLift
      (homogeneousChartEval φ)
      (coordinate k (0 : Fin (n + 1)))
      (by
        rw [homogeneousChartEval_coordinate_zero]
        exact isUnit_one))
      (algebraMap
        (MvPolynomial (Fin (n + 1)) k)
        (Localization.Away (coordinate k (0 : Fin (n + 1))))
        (MvPolynomial.C r)) =
      algebraMap k A r
  rw [IsLocalization.Away.lift_eq]
  simp [homogeneousChartEval]

@[simp]
lemma standardChartToAlgebra_affineVariable
    {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    {n : ℕ} (φ : MvPolynomial (Fin n) k →ₐ[k] A)
    (i : Fin n) :
    standardChartToAlgebra φ
        (affineVariableInStandardChart k i) =
      φ (MvPolynomial.X i) := by
  simp only [standardChartToAlgebra, affineVariableInStandardChart,
    RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  rw [Localization.awayLift_mk
    (v := (1 : A))
    (hv := by
      rw [homogeneousChartEval_coordinate_zero, one_mul])]
  simp [homogeneousChartEval]

/-- Evaluating the affine-chart realization of a polynomial recovers the
given affine polynomial presentation. -/
lemma standardChartToAlgebra_comp_affinePolynomialToStandardChart
    {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    {n : ℕ} (φ : MvPolynomial (Fin n) k →ₐ[k] A) :
    (standardChartToAlgebra φ).comp
        (affinePolynomialToStandardChart k n) =
      φ.toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [affinePolynomialToStandardChart]
  · intro i
    simp [affinePolynomialToStandardChart]

/-- A surjective affine polynomial presentation induces a surjective map
from the standard projective-chart ring. -/
theorem standardChartToAlgebra_surjective
    {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    {n : ℕ} (φ : MvPolynomial (Fin n) k →ₐ[k] A)
    (hφ : Function.Surjective φ) :
    Function.Surjective (standardChartToAlgebra φ) := by
  intro a
  obtain ⟨p, rfl⟩ := hφ a
  refine ⟨affinePolynomialToStandardChart k n p, ?_⟩
  exact RingHom.congr_fun
    (standardChartToAlgebra_comp_affinePolynomialToStandardChart φ) p

/-- The locally closed projective-chart realization is a morphism over
`Spec k`. -/
lemma projectiveChartMap_toSpec
    {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    {n : ℕ} (φ : MvPolynomial (Fin n) k →ₐ[k] A) :
    Spec.map (CommRingCat.ofHom (standardChartToAlgebra φ)) ≫
        Proj.awayι
          (homogeneousGrading k n)
          (coordinate k (0 : Fin (n + 1)))
          (coordinate_mem_degreeOne k (0 : Fin (n + 1)))
          Nat.zero_lt_one ≫
        toSpec k n =
      Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
  rw [toSpec]
  simp only [← Category.assoc, Proj.awayι_toSpecZero,
    ← Spec.map_comp]
  congr 1
  ext r
  exact standardChartToAlgebra_coefficient φ r

/-- A finite affine presentation gives a locally closed immersion into
projective space, factoring as a closed immersion into the `X₀`-chart
followed by its standard open immersion. -/
theorem exists_projectiveChart_immersion_of_finiteType
    (k A : Type u) [CommRing k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] :
    ∃ (n : ℕ)
      (φ : MvPolynomial (Fin n) k →ₐ[k] A)
      (i :
        Spec (CommRingCat.of A) ⟶
          Spec (CommRingCat.of
            (HomogeneousLocalization.Away
              (homogeneousGrading k n)
              (coordinate k (0 : Fin (n + 1))))))
      (j :
        Spec (CommRingCat.of
          (HomogeneousLocalization.Away
            (homogeneousGrading k n)
            (coordinate k (0 : Fin (n + 1))))) ⟶
          scheme k n),
      Function.Surjective φ ∧
      IsClosedImmersion i ∧
      IsOpenImmersion j ∧
      IsImmersion (i ≫ j) ∧
      (i ≫ j) ≫ toSpec k n =
        Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
  obtain ⟨n, φ, hφ⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
      (inferInstance : Algebra.FiniteType k A)
  let i :=
    Spec.map
      (CommRingCat.ofHom (standardChartToAlgebra φ))
  let j :=
    Proj.awayι
      (homogeneousGrading k n)
      (coordinate k (0 : Fin (n + 1)))
      (coordinate_mem_degreeOne k (0 : Fin (n + 1)))
      Nat.zero_lt_one
  have hi : IsClosedImmersion i :=
    IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (standardChartToAlgebra φ))
      (standardChartToAlgebra_surjective φ hφ)
  letI : IsClosedImmersion i := hi
  exact
    ⟨n, φ, i, j, hφ, hi, inferInstance, inferInstance,
      projectiveChartMap_toSpec φ⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ImmersionClosure
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveChartPresentation

/-!
# Projective closures of affine schemes of finite type

An affine algebra of finite type over `k` is a closed subscheme of the
standard affine chart in some projective space.  Its scheme-theoretic
image in projective space is therefore a projective `k`-scheme containing
the original affine scheme as a dense open subscheme.
-/

open CategoryTheory AlgebraicGeometry MvPolynomial

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-- The locally closed immersion associated to an affine polynomial
presentation. -/
def affineChartImmersion
    {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    {n : ℕ} (φ : MvPolynomial (Fin n) k →ₐ[k] A) :
    Spec (CommRingCat.of A) ⟶ scheme k n :=
  Spec.map (CommRingCat.ofHom (standardChartToAlgebra φ)) ≫
    Proj.awayι
      (homogeneousGrading k n)
      (coordinate k (0 : Fin (n + 1)))
      (coordinate_mem_degreeOne k (0 : Fin (n + 1)))
      Nat.zero_lt_one

/-- The affine-chart immersion is a morphism over `Spec k`. -/
@[reassoc]
lemma affineChartImmersion_toSpec
    {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    {n : ℕ} (φ : MvPolynomial (Fin n) k →ₐ[k] A) :
    affineChartImmersion φ ≫ toSpec k n =
      Spec.map (CommRingCat.ofHom (algebraMap k A)) :=
  projectiveChartMap_toSpec φ

/-- A surjective affine presentation makes the associated chart map an
immersion. -/
lemma isImmersion_affineChartImmersion
    {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    {n : ℕ} (φ : MvPolynomial (Fin n) k →ₐ[k] A)
    (hφ : Function.Surjective φ) :
    IsImmersion (affineChartImmersion φ) := by
  letI :
      IsClosedImmersion
        (Spec.map (CommRingCat.ofHom (standardChartToAlgebra φ))) :=
    IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (standardChartToAlgebra φ))
      (standardChartToAlgebra_surjective φ hφ)
  dsimp only [affineChartImmersion]
  infer_instance

/-- The projective closure of an affine-chart realization is its
scheme-theoretic image in projective space. -/
abbrev projectiveClosure
    {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    {n : ℕ} (φ : MvPolynomial (Fin n) k →ₐ[k] A) :
    Scheme.{u} :=
  (affineChartImmersion φ).image

/-- The canonical map from the affine scheme into its projective
closure. -/
noncomputable
abbrev toProjectiveClosure
    {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    {n : ℕ} (φ : MvPolynomial (Fin n) k →ₐ[k] A) :
    Spec (CommRingCat.of A) ⟶ projectiveClosure φ :=
  (affineChartImmersion φ).toImage

/-- The closed immersion of the projective closure into projective
space. -/
abbrev projectiveClosureι
    {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    {n : ℕ} (φ : MvPolynomial (Fin n) k →ₐ[k] A) :
    projectiveClosure φ ⟶ scheme k n :=
  (affineChartImmersion φ).imageι

/-- The structural morphism from the projective closure to the fixed
affine base. -/
def projectiveClosureToSpec
    {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    {n : ℕ} (φ : MvPolynomial (Fin n) k →ₐ[k] A) :
    projectiveClosure φ ⟶ Spec (CommRingCat.of k) :=
  projectiveClosureι φ ≫ toSpec k n

instance quasiCompact_affineChartImmersion
    {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    {n : ℕ} (φ : MvPolynomial (Fin n) k →ₐ[k] A) :
    QuasiCompact (affineChartImmersion φ) := by
  dsimp only [affineChartImmersion]
  infer_instance

/-- The original affine scheme is open in its projective closure. -/
theorem isOpenImmersion_toProjectiveClosure
    {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    {n : ℕ} (φ : MvPolynomial (Fin n) k →ₐ[k] A)
    (hφ : Function.Surjective φ) :
    IsOpenImmersion (toProjectiveClosure φ) := by
  letI : IsImmersion (affineChartImmersion φ) :=
    isImmersion_affineChartImmersion φ hφ
  infer_instance

/-- The original affine scheme is dense in its projective closure. -/
theorem denseRange_toProjectiveClosure
    {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    {n : ℕ} (φ : MvPolynomial (Fin n) k →ₐ[k] A) :
    Dense (Set.range (toProjectiveClosure φ).base) := by
  simpa [DenseRange] using (affineChartImmersion φ).toImage.denseRange

/-- The projective closure is a closed subscheme of projective space. -/
theorem isClosedImmersion_projectiveClosureι
    {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    {n : ℕ} (φ : MvPolynomial (Fin n) k →ₐ[k] A) :
    IsClosedImmersion (projectiveClosureι φ) :=
  inferInstance

/-- The dense-open map followed by the closed embedding recovers the
original chart immersion. -/
@[reassoc]
lemma toProjectiveClosure_projectiveClosureι
    {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    {n : ℕ} (φ : MvPolynomial (Fin n) k →ₐ[k] A) :
    toProjectiveClosure φ ≫ projectiveClosureι φ =
      affineChartImmersion φ :=
  (affineChartImmersion φ).toImage_imageι

/-- The projective closure has its tautological projective
factorization over `Spec k`. -/
theorem isProjectiveFactorization_projectiveClosureToSpec
    {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    {n : ℕ} (φ : MvPolynomial (Fin n) k →ₐ[k] A) :
    IsProjectiveFactorization (projectiveClosureToSpec φ) :=
  ⟨n, projectiveClosureι φ, inferInstance, rfl⟩

/-- The projective closure is proper over the fixed affine base. -/
theorem isProper_projectiveClosureToSpec
    {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    {n : ℕ} (φ : MvPolynomial (Fin n) k →ₐ[k] A) :
    IsProper (projectiveClosureToSpec φ) :=
  (isProjectiveFactorization_projectiveClosureToSpec φ).isProper

/-- The dense affine open has its original structural morphism to
`Spec k`. -/
@[reassoc]
lemma toProjectiveClosure_projectiveClosureToSpec
    {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    {n : ℕ} (φ : MvPolynomial (Fin n) k →ₐ[k] A) :
    toProjectiveClosure φ ≫ projectiveClosureToSpec φ =
      Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
  rw [projectiveClosureToSpec, ← Category.assoc,
    toProjectiveClosure_projectiveClosureι,
    affineChartImmersion_toSpec]

/-- Every affine scheme of finite type over `k` admits a projective
closure over the same base. -/
theorem exists_projectiveClosure_of_finiteType
    (k A : Type u) [CommRing k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] :
    ∃ (n : ℕ) (φ : MvPolynomial (Fin n) k →ₐ[k] A),
      Function.Surjective φ ∧
      IsOpenImmersion (toProjectiveClosure φ) ∧
      Dense (Set.range (toProjectiveClosure φ).base) ∧
      IsClosedImmersion (projectiveClosureι φ) ∧
      IsProjectiveFactorization (projectiveClosureToSpec φ) ∧
      IsProper (projectiveClosureToSpec φ) ∧
      toProjectiveClosure φ ≫ projectiveClosureToSpec φ =
        Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
  obtain ⟨n, φ, hφ⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
      (inferInstance : Algebra.FiniteType k A)
  exact
    ⟨n, φ, hφ, isOpenImmersion_toProjectiveClosure φ hφ,
      denseRange_toProjectiveClosure φ,
      isClosedImmersion_projectiveClosureι φ,
      isProjectiveFactorization_projectiveClosureToSpec φ,
      isProper_projectiveClosureToSpec φ,
      toProjectiveClosure_projectiveClosureToSpec φ⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

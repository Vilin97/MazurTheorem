/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSpaceStandardCover
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Closed embeddings into projective space

This file supplies the small projective-morphism interface needed by the
proper dévissage.  The projective space is exactly the `Proj` used by the
standard-cover and Čech files, not a second model.

Mathlib's properness theorem for `Proj` is relative to the degree-zero part
of the graded ring.  We first identify that ring with the coefficient ring,
then define the usual structural morphism to `Spec k`.
-/

open CategoryTheory AlgebraicGeometry MvPolynomial

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-- The degree-zero part of the standard homogeneous coordinate ring is the
coefficient ring. -/
def gradeZeroRingEquiv (k : Type u) [CommRing k] (d : ℕ) :
    k ≃+* homogeneousGrading k d 0 :=
  RingEquiv.ofBijective
    (algebraMap k (homogeneousGrading k d 0))
    (by
      constructor
      · intro a b hab
        have h := congrArg Subtype.val hab
        simpa using MvPolynomial.C_injective (Fin (d + 1)) k h
      · intro x
        obtain ⟨y, hy⟩ := Submodule.mem_one.mp
          ((MvPolynomial.homogeneousSubmodule_zero
            (σ := Fin (d + 1)) (R := k)).le x.2)
        exact ⟨y, Subtype.ext (by simpa using hy)⟩)

/-- The structural morphism from standard projective space to the spectrum
of its coefficient ring. -/
def toSpec (k : Type u) [CommRing k] (d : ℕ) :
    scheme k d ⟶ Spec (CommRingCat.of k) :=
  Proj.toSpecZero (homogeneousGrading k d) ≫
    Spec.map (CommRingCat.ofHom
      (algebraMap k (homogeneousGrading k d 0)))

instance finiteType_gradeZero_coordinateRing
    (k : Type u) [CommRing k] (d : ℕ) :
    Algebra.FiniteType (homogeneousGrading k d 0)
      (MvPolynomial (Fin (d + 1)) k) := by
  letI := IsScalarTower.of_algebraMap_eq
    (R := k)
    (S := homogeneousGrading k d 0)
    (A := MvPolynomial (Fin (d + 1)) k)
    (fun r => rfl)
  exact Algebra.FiniteType.of_restrictScalars_finiteType
    (R := k)
    (S := homogeneousGrading k d 0)
    (A := MvPolynomial (Fin (d + 1)) k)

instance isIso_specMap_algebraMap_gradeZero
    (k : Type u) [CommRing k] (d : ℕ) :
    IsIso
      (Spec.map (CommRingCat.ofHom
        (algebraMap k (homogeneousGrading k d 0)))) := by
  letI :
      IsIso (CommRingCat.ofHom
        (algebraMap k (homogeneousGrading k d 0))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (gradeZeroRingEquiv k d).bijective
  infer_instance

/-- Standard projective space is proper over its coefficient ring. -/
instance isProper_toSpec (k : Type u) [CommRing k] (d : ℕ) :
    IsProper (toSpec k d) := by
  dsimp only [toSpec]
  infer_instance

/-- A morphism is projective in the concrete sense relevant here when it
factors through a closed immersion into a finite-dimensional standard
projective space over the same affine base. -/
def IsProjectiveFactorization
    {X : Scheme.{u}} {k : Type u} [CommRing k]
    (f : X ⟶ Spec (CommRingCat.of k)) : Prop :=
  ∃ (d : ℕ) (i : X ⟶ scheme k d),
    IsClosedImmersion i ∧ i ≫ toSpec k d = f

namespace IsProjectiveFactorization

variable {X : Scheme.{u}} {k : Type u} [CommRing k]
variable {f : X ⟶ Spec (CommRingCat.of k)}

/-- A projective factorization makes the original morphism proper. -/
theorem isProper (h : IsProjectiveFactorization f) : IsProper f := by
  obtain ⟨d, i, hi, hif⟩ := h
  haveI : IsClosedImmersion i := hi
  rw [← hif]
  infer_instance

/-- Composing a projective morphism with a closed immersion remains
projective. -/
theorem comp_isClosedImmersion (h : IsProjectiveFactorization f)
    {Y : Scheme.{u}} (j : Y ⟶ X) [IsClosedImmersion j] :
    IsProjectiveFactorization (j ≫ f) := by
  obtain ⟨d, i, hi, hif⟩ := h
  haveI : IsClosedImmersion i := hi
  exact ⟨d, j ≫ i, inferInstance, by rw [Category.assoc, hif]⟩

end IsProjectiveFactorization

/-- The structural morphism of projective space has its tautological
projective factorization. -/
theorem isProjectiveFactorization_toSpec
    (k : Type u) [CommRing k] (d : ℕ) :
    IsProjectiveFactorization (toSpec k d) :=
  ⟨d, 𝟙 _, inferInstance, Category.id_comp _⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

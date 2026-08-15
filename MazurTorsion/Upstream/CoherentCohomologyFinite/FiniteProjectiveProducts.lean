/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.BiprojectiveFactorization

/-!
# Finite products of projective models

Assuming the isolated scheme-level Segre interface, projective models over
`Spec k` are closed under binary fiber products and hence under chosen
nonempty finite iterated fiber products.  This closes all formal
category-theoretic bookkeeping around the missing Segre construction.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-- A scheme together with a concrete projective factorization over an
affine coefficient ring. -/
structure StandardProjectiveModel
    (k : Type u) [CommRing k] where
  carrier : Scheme.{u}
  toSpec : carrier ⟶ Spec (CommRingCat.of k)
  projective : IsProjectiveFactorization toSpec

namespace StandardProjectiveModel

variable {k : Type u} [CommRing k]

/-- Every standard projective model is proper over the coefficient
ring. -/
theorem isProper (P : StandardProjectiveModel k) :
    IsProper P.toSpec :=
  P.projective.isProper

/-- The binary fiber product of projective models, conditional only on
the scheme-level Segre interface. -/
def fiberProduct
    (hsegre : StandardSegreEmbeddings k)
    (P Q : StandardProjectiveModel k) :
    StandardProjectiveModel k where
  carrier := pullback P.toSpec Q.toSpec
  toSpec := pullback.fst P.toSpec Q.toSpec ≫ P.toSpec
  projective :=
    isProjectiveFactorization_fiberProduct
      hsegre P.projective Q.projective

/-- A chosen iterated fiber product of a head projective model with a
list of further projective models. -/
def iteratedFiberProduct
    (hsegre : StandardSegreEmbeddings k) :
    StandardProjectiveModel k →
      List (StandardProjectiveModel k) →
        StandardProjectiveModel k
  | P, [] => P
  | P, Q :: tail =>
      iteratedFiberProduct hsegre
        (fiberProduct hsegre P Q) tail

/-- A chosen iterated fiber product of a nonempty finite family of
projective models. -/
def finiteFiberProduct
    (hsegre : StandardSegreEmbeddings k)
    {ι : Type u} [Fintype ι] [Nonempty ι]
    (P : ι → StandardProjectiveModel k) :
    StandardProjectiveModel k := by
  classical
  let i₀ : ι := Classical.choice inferInstance
  exact
    iteratedFiberProduct hsegre (P i₀)
      (((Finset.univ.erase i₀).toList).map P)

/-- The chosen finite fiber product remains projective. -/
theorem finiteFiberProduct_projective
    (hsegre : StandardSegreEmbeddings k)
    {ι : Type u} [Fintype ι] [Nonempty ι]
    (P : ι → StandardProjectiveModel k) :
    IsProjectiveFactorization
      (finiteFiberProduct hsegre P).toSpec :=
  (finiteFiberProduct hsegre P).projective

end StandardProjectiveModel

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

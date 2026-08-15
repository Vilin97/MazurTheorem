/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveSpace

/-!
# Chosen data in a relative projective factorization

The proposition `IsRelativeProjectiveFactorization s f` is existential.
This file gives stable names to a chosen projective dimension, closed
embedding, and the resulting map to absolute projective space.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
namespace IsRelativeProjectiveFactorization

variable {k : Type u} [CommRing k]
  {X S : Scheme.{u}}
  {s : S ⟶ Spec (CommRingCat.of k)}
  {f : X ⟶ S}

/-- A chosen relative projective dimension. -/
def chosenDimension
    (h : IsRelativeProjectiveFactorization s f) : ℕ :=
  h.choose

/-- The chosen closed embedding into relative projective space. -/
def chosenEmbedding
    (h : IsRelativeProjectiveFactorization s f) :
    X ⟶ relativeScheme s h.chosenDimension :=
  h.choose_spec.choose

/-- The chosen embedding is a closed immersion. -/
theorem chosenEmbedding_isClosedImmersion
    (h : IsRelativeProjectiveFactorization s f) :
    IsClosedImmersion h.chosenEmbedding :=
  h.choose_spec.choose_spec.1

attribute [local instance]
  chosenEmbedding_isClosedImmersion

/-- The chosen embedding recovers the original relative morphism after
projection to the base. -/
@[reassoc]
theorem chosenEmbedding_relativeToBase
    (h : IsRelativeProjectiveFactorization s f) :
    h.chosenEmbedding ≫
        relativeToBase s h.chosenDimension =
      f :=
  h.choose_spec.choose_spec.2

/-- The absolute projective-space map underlying the chosen relative
factorization. -/
def chosenProjectiveMap
    (h : IsRelativeProjectiveFactorization s f) :
    X ⟶ scheme k h.chosenDimension :=
  h.chosenEmbedding ≫
    relativeToProjective s h.chosenDimension

/-- The chosen absolute projective map is compatible with the
structural map to the coefficient spectrum. -/
@[reassoc]
theorem chosenProjectiveMap_toSpec
    (h : IsRelativeProjectiveFactorization s f) :
    h.chosenProjectiveMap ≫
        toSpec k h.chosenDimension =
      f ≫ s := by
  rw [chosenProjectiveMap, Category.assoc,
    ← relative_projection_condition]
  exact h.chosenEmbedding_relativeToBase_assoc s

end IsRelativeProjectiveFactorization
end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

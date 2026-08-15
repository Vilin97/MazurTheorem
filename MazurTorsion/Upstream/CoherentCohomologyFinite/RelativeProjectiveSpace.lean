/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveFactorization

/-!
# Standard relative projective space

This file records the base change of standard projective space along a
morphism to an affine base.  It also packages the concrete notion of a
relative projective factorization needed for graph closures.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-- Standard relative projective `d`-space over a scheme equipped with a
morphism to `Spec k`. -/
abbrev relativeScheme
    {k : Type u} [CommRing k] {S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ) :
    Scheme.{u} :=
  pullback s (toSpec k d)

/-- The projection from relative projective space to its base scheme. -/
abbrev relativeToBase
    {k : Type u} [CommRing k] {S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ) :
    relativeScheme s d ⟶ S :=
  pullback.fst s (toSpec k d)

/-- The projection from relative projective space to absolute projective
space. -/
abbrev relativeToProjective
    {k : Type u} [CommRing k] {S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ) :
    relativeScheme s d ⟶ scheme k d :=
  pullback.snd s (toSpec k d)

/-- The defining compatibility of the two projections from relative
projective space. -/
@[reassoc]
lemma relative_projection_condition
    {k : Type u} [CommRing k] {S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ) :
    relativeToBase s d ≫ s =
      relativeToProjective s d ≫ toSpec k d :=
  pullback.condition

instance isProper_relativeToBase
    {k : Type u} [CommRing k] {S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ) :
    IsProper (relativeToBase s d) :=
  inferInstance

/-- A morphism is projective relative to a fixed affine coefficient
ring when it factors as a closed immersion into a standard relative
projective space. -/
def IsRelativeProjectiveFactorization
    {k : Type u} [CommRing k] {X S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (f : X ⟶ S) : Prop :=
  ∃ (d : ℕ) (i : X ⟶ relativeScheme s d),
    IsClosedImmersion i ∧ i ≫ relativeToBase s d = f

namespace IsRelativeProjectiveFactorization

/-- A relative projective factorization is proper. -/
theorem isProper
    {k : Type u} [CommRing k] {X S : Scheme.{u}}
    {s : S ⟶ Spec (CommRingCat.of k)} {f : X ⟶ S}
    (h : IsRelativeProjectiveFactorization s f) :
    IsProper f := by
  obtain ⟨d, i, hi, hif⟩ := h
  letI : IsClosedImmersion i := hi
  rw [← hif]
  infer_instance

/-- Precomposing a relative projective morphism with a closed immersion
preserves its relative projective factorization. -/
theorem comp_isClosedImmersion
    {k : Type u} [CommRing k] {X Y S : Scheme.{u}}
    {s : S ⟶ Spec (CommRingCat.of k)} {f : X ⟶ S}
    (h : IsRelativeProjectiveFactorization s f)
    (j : Y ⟶ X) [IsClosedImmersion j] :
    IsRelativeProjectiveFactorization s (j ≫ f) := by
  obtain ⟨d, i, hi, hif⟩ := h
  letI : IsClosedImmersion i := hi
  exact ⟨d, j ≫ i, inferInstance, by rw [Category.assoc, hif]⟩

end IsRelativeProjectiveFactorization

/-- The projection from standard relative projective space has its
tautological relative projective factorization. -/
theorem isRelativeProjectiveFactorization_relativeToBase
    {k : Type u} [CommRing k] {S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ) :
    IsRelativeProjectiveFactorization s (relativeToBase s d) :=
  ⟨d, 𝟙 _, inferInstance, Category.id_comp _⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

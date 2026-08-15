/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.Birational
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeAffineCoverData

/-!
# Projective modifications over an affine base

This file gives the precise output required from the global assembly step
in Chow's lemma.  It separates the already-formalized finite affine chart
closures from the one remaining geometric assertion: assembling them into
one model which is projective over the coefficient ring.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

open ProjectiveSpace

/-- A projective modification of `X` over `Spec k`: the model is
projective over `k`, the map to `X` is relatively projective, and the two
schemes share a specified dense open. -/
structure ProjectiveModification
    {k : Type u} [CommRing k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) where
  /-- The projective model. -/
  model : Scheme.{u}
  /-- The modification morphism. -/
  toOriginal : model ⟶ X
  /-- The modification is projective over `X`. -/
  relativeProjective :
    IsRelativeProjectiveFactorization f toOriginal
  /-- The model is projective over the fixed coefficient ring. -/
  projectiveOverBase :
    IsProjectiveFactorization (toOriginal ≫ f)
  /-- A common dense open subscheme. -/
  commonOpen : Scheme.{u}
  /-- Its inclusion in the original scheme. -/
  toOriginalOpen : commonOpen ⟶ X
  /-- Its inclusion in the projective model. -/
  toModelOpen : commonOpen ⟶ model
  isOpenImmersion_toOriginalOpen :
    IsOpenImmersion toOriginalOpen
  isOpenImmersion_toModelOpen :
    IsOpenImmersion toModelOpen
  dense_toOriginalOpen :
    Dense (Set.range toOriginalOpen.base)
  dense_toModelOpen :
    Dense (Set.range toModelOpen.base)
  /-- The modification agrees with the identity on the common open. -/
  toModelOpen_toOriginal :
    toModelOpen ≫ toOriginal = toOriginalOpen

namespace ProjectiveModification

variable
    {k : Type u} [CommRing k] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)}

/-- The modification morphism is proper. -/
theorem isProper_toOriginal
    (P : ProjectiveModification f) :
    IsProper P.toOriginal :=
  P.relativeProjective.isProper

/-- The projective model is proper over the coefficient ring. -/
theorem isProper_toBase
    (P : ProjectiveModification f) :
    IsProper (P.toOriginal ≫ f) :=
  P.projectiveOverBase.isProper

/-- A projective modification gives a birational model. -/
theorem isBirational
    (P : ProjectiveModification f) :
    IsBirational X P.model :=
  ⟨P.commonOpen, P.toOriginalOpen, P.toModelOpen,
    P.isOpenImmersion_toOriginalOpen,
    P.isOpenImmersion_toModelOpen,
    P.dense_toOriginalOpen,
    P.dense_toModelOpen⟩

/-- On the common open, the structural morphism of the model agrees
with that of the original scheme. -/
@[reassoc]
lemma toModelOpen_toBase
    (P : ProjectiveModification f) :
    P.toModelOpen ≫ P.toOriginal ≫ f =
      P.toOriginalOpen ≫ f := by
  rw [← Category.assoc, P.toModelOpen_toOriginal]

end ProjectiveModification

/-- The exact remaining Chow-assembly assertion at the current Mathlib
pin.  All local inputs represented here are constructed in
`RelativeAffineCoverData`; an inhabitant must combine their graph
closures into one absolute projective model.

The missing infrastructure is a scheme-level finite Segre embedding (or
an equivalent theorem that a finite product of standard projective spaces
is projective), together with the finite-chart graph-closure assembly. -/
def FiniteAffineCoverProjectiveAssembly
    (k : Type u) [CommRing k] : Prop :=
  ∀ {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))
    [IsProper f]
    (_ : Chow.RelativeAffineCoverData k f),
    Nonempty (ProjectiveModification f)

/-- Once the finite-chart assembly assertion is supplied, every proper
scheme over `Spec k` admits a projective modification.  All cover
existence, finite-type, and fixed-base compatibility hypotheses are
discharged internally. -/
theorem exists_projectiveModification_of_proper
    (k : Type u) [CommRing k]
    (hasAssembly : FiniteAffineCoverProjectiveAssembly k)
    {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] :
    Nonempty (ProjectiveModification f) := by
  obtain ⟨c⟩ :=
    Chow.exists_relativeAffineCoverData k f
  exact hasAssembly f c

end MazurTorsion.AlgebraicGeometry.CoherentCohomology

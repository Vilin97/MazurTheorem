/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Finite affine cover data for Chow constructions

A compact scheme has a finite affine cover.  Each chosen affine chart is
presented canonically as the spectrum of its global sections; the ambient
closed immersion is the identity.  This is the honest content of the
finite-cover helper used in the Atlas Chow development.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.Chow

/-- A finite affine cover, together with a closed immersion of every
chart into an ambient affine scheme. -/
structure AffineCoverData (X : Scheme.{u}) where
  ι : Type u
  [fintype : Fintype ι]
  R : ι → CommRingCat.{u}
  f : (i : ι) → Spec (R i) ⟶ X
  isOpenImmersion : ∀ i, IsOpenImmersion (f i)
  covers : ∀ x : X, ∃ i, x ∈ Set.range (f i).base
  ambientRing : ι → CommRingCat.{u}
  embedding : (i : ι) → Spec (R i) ⟶ Spec (ambientRing i)
  isClosedImmersion : ∀ i, IsClosedImmersion (embedding i)

attribute [instance] AffineCoverData.fintype
  AffineCoverData.isOpenImmersion
  AffineCoverData.isClosedImmersion

/-- The open cover obtained by forgetting the ambient affine
embeddings. -/
def AffineCoverData.toOpenCover {X : Scheme.{u}}
    (c : AffineCoverData X) : X.OpenCover where
  I₀ := c.ι
  X i := Spec (c.R i)
  f := c.f
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨c.covers, fun i => c.isOpenImmersion i⟩

/-- Every compact scheme admits finite affine cover data. -/
theorem exists_affineCoverData (X : Scheme.{u}) [CompactSpace X] :
    Nonempty (AffineCoverData X) := by
  let 𝒰 : X.OpenCover :=
    X.affineCover.finiteSubcover
  refine ⟨{
    ι := 𝒰.I₀
    R := fun i => Γ(𝒰.X i, ⊤)
    f := fun i => (𝒰.X i).isoSpec.inv ≫ 𝒰.f i
    isOpenImmersion := fun _ => inferInstance
    covers := ?_
    ambientRing := fun i => Γ(𝒰.X i, ⊤)
    embedding := fun _ => 𝟙 _
    isClosedImmersion := fun _ => inferInstance }⟩
  intro x
  obtain ⟨y, hy⟩ := 𝒰.covers x
  refine ⟨𝒰.idx x, (𝒰.X (𝒰.idx x)).isoSpec.hom.base y, ?_⟩
  change
    (𝒰.f (𝒰.idx x)).base
      ((𝒰.X (𝒰.idx x)).isoSpec.inv.base
        ((𝒰.X (𝒰.idx x)).isoSpec.hom.base y)) =
      x
  simpa using hy

/-- A quasi-compact morphism with compact target has compact source,
and hence supplies finite affine cover data. -/
theorem exists_affineCoverData_of_quasiCompact
    {S X : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [CompactSpace S] :
    Nonempty (AffineCoverData X) := by
  letI : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace f
  exact exists_affineCoverData X

/-- In particular, a proper morphism to a compact base supplies finite
affine cover data. -/
theorem exists_affineCoverData_of_proper
    {S X : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [CompactSpace S] :
    Nonempty (AffineCoverData X) :=
  exists_affineCoverData_of_quasiCompact f

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.Chow

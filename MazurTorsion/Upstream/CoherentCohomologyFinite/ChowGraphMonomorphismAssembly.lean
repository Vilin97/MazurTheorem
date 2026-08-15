/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ChowGraphAssembly
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveGraphClosureProjectionProper

/-!
# Chow graph assembly reduced to a monomorphism

For a proper scheme `X` over `Spec k`, the second projection of a
projective graph closure is already proper.  Hence it is a closed
immersion precisely when it is a monomorphism.

This file repackages the residual graph datum in Chow's lemma with only
that monomorphism field.  It then connects this sharper formulation to
the existing graph-embedding and projective-modification assembly
interfaces.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

open ProjectiveSpace

/-- The graph datum needed for Chow's lemma after properness of the
second graph-closure projection has been discharged.  The final field is
only the monomorphism condition. -/
structure ChowGraphMonomorphismData
    {k : Type u} [CommRing k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) where
  dimension : ℕ
  domain : Scheme.{u}
  toOriginalOpen : domain ⟶ X
  toProjective : domain ⟶ scheme k dimension
  overBase :
    toOriginalOpen ≫ f =
      toProjective ≫ toSpec k dimension
  isOpenImmersion_toOriginalOpen :
    IsOpenImmersion toOriginalOpen
  quasiCompact_toOriginalOpen :
    QuasiCompact toOriginalOpen
  dense_toOriginalOpen :
    Dense (Set.range toOriginalOpen.base)
  mono_graphClosureToProjective :
    Mono
      (projectiveGraphClosureToProjective
        f dimension toOriginalOpen toProjective overBase)

namespace ChowGraphMonomorphismData

/-- Over a proper base scheme, monomorphic graph data is graph-embedding
data: proper monomorphisms of schemes are closed immersions. -/
def toEmbeddingData
    {k : Type u} [CommRing k] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)} [IsProper f]
    (D : ChowGraphMonomorphismData f) :
    ChowGraphEmbeddingData f := by
  letI :
      Mono
        (projectiveGraphClosureToProjective
          f D.dimension D.toOriginalOpen
            D.toProjective D.overBase) :=
    D.mono_graphClosureToProjective
  exact
    {
      dimension := D.dimension
      domain := D.domain
      toOriginalOpen := D.toOriginalOpen
      toProjective := D.toProjective
      overBase := D.overBase
      isOpenImmersion_toOriginalOpen :=
        D.isOpenImmersion_toOriginalOpen
      quasiCompact_toOriginalOpen :=
        D.quasiCompact_toOriginalOpen
      dense_toOriginalOpen := D.dense_toOriginalOpen
      isClosedImmersion_graphClosureToProjective :=
        isClosedImmersion_projectiveGraphClosureToProjective_of_mono
          f D.dimension D.toOriginalOpen
            D.toProjective D.overBase
    }

/-- Monomorphic graph data over a proper scheme directly yields a
projective modification. -/
def toProjectiveModification
    {k : Type u} [CommRing k] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)} [IsProper f]
    (D : ChowGraphMonomorphismData f) :
    ProjectiveModification f :=
  projectiveModificationOfChowGraph D.toEmbeddingData

end ChowGraphMonomorphismData

/-- The finite-chart residual assertion with the closed-immersion
condition reduced to the monomorphism of the graph projection. -/
def FiniteChartGraphMonomorphismAssembly
    (k : Type u) [CommRing k] : Prop :=
  ∀ {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))
    [IsProper f]
    (_ : Chow.RelativeAffineCoverData k f),
    Nonempty (ChowGraphMonomorphismData f)

/-- Finite-chart monomorphism assembly implies the existing
graph-embedding assembly. -/
theorem finiteChartGraphEmbeddingAssembly_of_monomorphism
    (k : Type u) [CommRing k]
    (hmono : FiniteChartGraphMonomorphismAssembly k) :
    FiniteChartGraphEmbeddingAssembly k := by
  intro X f _ c
  obtain ⟨D⟩ := hmono f c
  exact ⟨D.toEmbeddingData⟩

/-- Finite-chart monomorphism assembly implies the projective
modification assembly used by the cohomological dévissage. -/
theorem finiteAffineCoverProjectiveAssembly_of_graphMonomorphism
    (k : Type u) [CommRing k]
    (hmono : FiniteChartGraphMonomorphismAssembly k) :
    FiniteAffineCoverProjectiveAssembly k :=
  finiteAffineCoverProjectiveAssembly_of_graphEmbedding
    k
    (finiteChartGraphEmbeddingAssembly_of_monomorphism
      k hmono)

/-- Consequently, graph-projection monomorphisms for finite chart
assemblies produce a projective modification of every proper scheme
over the affine base. -/
theorem exists_projectiveModification_of_graphMonomorphismAssembly
    (k : Type u) [CommRing k]
    (hmono : FiniteChartGraphMonomorphismAssembly k)
    {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] :
    Nonempty (ProjectiveModification f) :=
  exists_projectiveModification_of_proper
    k
    (finiteAffineCoverProjectiveAssembly_of_graphMonomorphism
      k hmono)
    f

end MazurTorsion.AlgebraicGeometry.CoherentCohomology

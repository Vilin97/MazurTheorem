/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ChowGraphToProjectiveClosure
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Monomorphisms from target opens covering the range

Monomorphisms of schemes are Zariski-local on the target.  It is enough
that the chosen target opens cover the range of the morphism; outside
their union the source is empty.  This is the form naturally used for
the graph projection in Chow's lemma.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

/-- A scheme morphism is a monomorphism if it is a monomorphism over
each of a family of target opens whose union contains its range. -/
theorem mono_of_targetOpens_cover_range
    {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    {ι : Type u} (W : ι → Y.Opens)
    (hrange :
      Set.range g ⊆ (⨆ i, W i : Y.Opens))
    (hmono : ∀ i, Mono (g ∣_ W i)) :
    Mono g := by
  letI :
      (MorphismProperty.monomorphisms Scheme).RespectsRight
        @IsOpenImmersion :=
    {
      postcomp := by
        intro A B C i hi h hh
        rw [MorphismProperty.monomorphisms.iff] at hh ⊢
        letI : Mono h := hh
        letI : IsOpenImmersion i := hi
        infer_instance
    }
  rw [← MorphismProperty.monomorphisms.iff]
  apply
    IsZariskiLocalAtTarget.of_range_subset_iSup
      (P := MorphismProperty.monomorphisms Scheme)
      W hrange
  intro i
  rw [MorphismProperty.monomorphisms.iff]
  exact hmono i

open ProjectiveSpace

namespace ChowRationalProjectiveMapData

variable
    {k : Type u} [CommRing k] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)}
    (D : ChowRationalProjectiveMapData f)

/-- Target-open data sufficient to prove the Chow graph projection a
monomorphism.  In the finite-chart construction the opens are the
inverse images of the interior affine charts in the individual
projective completions. -/
structure GraphTargetOpenMonomorphismData where
  ι : Type u
  targetOpen : ι → (scheme k D.dimension).Opens
  range_subset :
    Set.range
        (projectiveGraphClosureToProjective
          f D.dimension D.toOriginalOpen
            D.toProjective D.overBase) ⊆
      (⨆ i, targetOpen i :
        (scheme k D.dimension).Opens)
  mono_restrict :
    ∀ i,
      Mono
        (projectiveGraphClosureToProjective
          f D.dimension D.toOriginalOpen
            D.toProjective D.overBase ∣_
          targetOpen i)

namespace GraphTargetOpenMonomorphismData

/-- Target-open monomorphism data prove the global graph projection is
a monomorphism. -/
theorem mono_graphClosureToProjective
    (E : D.GraphTargetOpenMonomorphismData) :
    Mono
      (projectiveGraphClosureToProjective
        f D.dimension D.toOriginalOpen
          D.toProjective D.overBase) :=
  mono_of_targetOpens_cover_range
    (projectiveGraphClosureToProjective
      f D.dimension D.toOriginalOpen
        D.toProjective D.overBase)
    E.targetOpen E.range_subset E.mono_restrict

end GraphTargetOpenMonomorphismData

end ChowRationalProjectiveMapData

end MazurTorsion.AlgebraicGeometry.CoherentCohomology

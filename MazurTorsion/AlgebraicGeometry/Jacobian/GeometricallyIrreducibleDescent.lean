/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Geometric irreducibility descends through surjections

If `q : X ⟶ Y` is surjective and `q ≫ f` is geometrically irreducible, then
`f` is geometrically irreducible.  After an arbitrary field-valued base
change, the pullback of `q` is still surjective, and the continuous image of
an irreducible space is irreducible.

The named downstream consumer is the finite permutation quotient in
`SymmetricPower`.
-/

universe u

open CategoryTheory Limits

namespace MazurTorsion.AlgebraicGeometry.Jacobian

open _root_.AlgebraicGeometry

/-- An isomorphism of schemes is geometrically irreducible. -/
theorem geometricallyIrreducible_of_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    GeometricallyIrreducible f := by
  rw [GeometricallyIrreducible.eq_geometrically,
    geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ y
  letI : IsIso (pullback.snd f y) := inferInstance
  exact (asIso (pullback.snd f y)).hom.homeomorph.irreducibleSpace_iff.mpr
    inferInstance

/-- Geometric irreducibility descends from a surjective source. -/
theorem geometricallyIrreducible_of_comp_surjective
    {X Y S : Scheme.{u}} (q : X ⟶ Y) (f : Y ⟶ S)
    [Surjective q] [GeometricallyIrreducible (q ≫ f)] :
    GeometricallyIrreducible f := by
  rw [GeometricallyIrreducible.eq_geometrically,
    geometrically_iff_of_isClosedUnderIsomorphisms]
  intro K _ s
  let e : pullback q (pullback.fst f s) ≅ pullback (q ≫ f) s :=
    pullbackRightPullbackFstIso f s q
  letI : IrreducibleSpace ↥(pullback (q ≫ f) s) :=
    pullback_of_geometrically
      (GeometricallyIrreducible.geometrically_irreducibleSpace
        (f := q ≫ f)) K s
  letI : IrreducibleSpace ↥(pullback q (pullback.fst f s)) :=
    e.hom.homeomorph.irreducibleSpace_iff.mpr inferInstance
  letI : Surjective (pullback.snd q (pullback.fst f s)) := by
    infer_instance
  have hsurj : Function.Surjective
      ⇑(pullback.snd q (pullback.fst f s)) :=
    (inferInstance : Surjective (pullback.snd q (pullback.fst f s))).1
  exact hsurj.irreducibleSpace
    (pullback.snd q (pullback.fst f s)).continuous

end MazurTorsion.AlgebraicGeometry.Jacobian

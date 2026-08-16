/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Clopen subschemes of affine schemes

A clopen subset of an affine scheme is the basic open cut out by an
idempotent after transport to the canonical spectrum.  In particular its
open subscheme is affine.

The named downstream consumer is the selected orbit-sheet chart in
`SplitFiniteActionSheets`.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.AffineClopen

/-- The inclusion of a clopen subscheme is also a closed immersion. -/
theorem isClosedImmersion_ι_of_isClopen {X : Scheme.{u}}
    {U : X.Opens} (hU : IsClopen (U : Set X)) : IsClosedImmersion U.ι :=
  IsClosedImmersion.of_isPreimmersion U.ι (by
    rw [Scheme.Opens.range_ι]
    exact hU.isClosed)

/-- An open-and-closed subscheme of an affine scheme is affine. -/
theorem isAffineOpen_of_isClopen {X : Scheme.{u}} [IsAffine X]
    {U : X.Opens} (hU : IsClopen (U : Set X)) : IsAffineOpen U := by
  let f : X ⟶ Spec Γ(X, ⊤) := X.isoSpec.hom
  let s : Set (Spec Γ(X, ⊤)) := f '' (U : Set X)
  have hs : IsClopen s := by
    constructor
    · exact f.homeomorph.isClosedMap _ hU.isClosed
    · exact f.homeomorph.isOpenMap _ U.2
  obtain ⟨e, _he, heq⟩ :=
    PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen hs
  have hpre := (IsAffineOpen.Spec_basicOpen e).preimage_of_isIso f
  have heqpre := congrArg
    (fun t : Set (Spec Γ(X, ⊤)) ↦ f ⁻¹' t) heq
  have hleft : f ⁻¹' (f '' (U : Set X)) = (U : Set X) :=
    Set.preimage_image_eq _ f.homeomorph.injective
  have hcarrier := hleft.symm.trans heqpre
  have hopen : U = f ⁻¹ᵁ PrimeSpectrum.basicOpen e := by
    apply SetLike.ext
    exact Set.ext_iff.1 hcarrier
  rw [hopen]
  exact hpre

end MazurTorsion.AlgebraicGeometry.Jacobian.AffineClopen

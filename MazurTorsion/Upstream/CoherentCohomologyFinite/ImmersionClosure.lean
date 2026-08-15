/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Scheme-theoretic closures of quasi-compact immersions

Mathlib's scheme-theoretic image gives the canonical closure of a
quasi-compact immersion.  This file packages the resulting factorization:
the original scheme is a dense open subscheme of its image, and the image
is a closed subscheme of the original target.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

/-- A factorization of a morphism as a dense open immersion followed by a
closed immersion. -/
structure DenseOpenClosedFactorization
    {X Y : Scheme.{u}} (f : X ⟶ Y) where
  /-- The intermediate closed subscheme. -/
  carrier : Scheme.{u}
  /-- The dense open immersion into the closure. -/
  openMap : X ⟶ carrier
  /-- The closed immersion of the closure into the target. -/
  closedMap : carrier ⟶ Y
  isOpenImmersion_openMap : IsOpenImmersion openMap
  dense_openMap : Dense (Set.range openMap.base)
  isClosedImmersion_closedMap : IsClosedImmersion closedMap
  openMap_closedMap : openMap ≫ closedMap = f

/-- The canonical dense-open/closed factorization of a quasi-compact
immersion through its scheme-theoretic image. -/
def schemeTheoreticClosureFactorization
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsImmersion f] [QuasiCompact f] :
    DenseOpenClosedFactorization f where
  carrier := f.image
  openMap := f.toImage
  closedMap := f.imageι
  isOpenImmersion_openMap := inferInstance
  dense_openMap := by
    simpa [DenseRange] using f.toImage.denseRange
  isClosedImmersion_closedMap := inferInstance
  openMap_closedMap := f.toImage_imageι

end MazurTorsion.AlgebraicGeometry.CoherentCohomology

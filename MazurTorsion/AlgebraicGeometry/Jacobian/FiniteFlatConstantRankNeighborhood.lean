/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# Constant-rank neighborhoods for finite flat morphisms

The rank of a finite flat finitely presented morphism is locally constant.
The fiber of its rank function through a chosen base point is therefore an
open-and-closed neighborhood, and restriction to that neighborhood has
constant rank.  This packages the exact shrinking needed before applying a
constant-rank finite-étale splitting theorem.

The named downstream consumer is the finite-divisor fpqc chart construction
in `PointedIncidenceDescent`.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.FiniteFlatConstantRankNeighborhood

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [Flat f] [IsFinite f] [LocallyOfFinitePresentation f]

/-- The open-and-closed locus on which `f` has the same rank as at `y`. -/
noncomputable def rankOpen (y : Y) : Y.Opens :=
  ⟨{z | f.finrank z = f.finrank y},
    f.isLocallyConstant_finrank.isOpen_fiber (f.finrank y)⟩

@[simp]
theorem mem_rankOpen_iff (y z : Y) :
    z ∈ rankOpen f y ↔ f.finrank z = f.finrank y :=
  Iff.rfl

@[simp]
theorem mem_rankOpen (y : Y) : y ∈ rankOpen f y :=
  rfl

/-- The constant-rank neighborhood is also closed. -/
theorem isClosed_rankOpen (y : Y) :
    IsClosed (rankOpen f y : Set Y) :=
  f.isLocallyConstant_finrank.isClosed_fiber (f.finrank y)

/-- Restricting to the rank locus through `y` makes the rank function
constant with value `f.finrank y`. -/
theorem morphismRestrict_finrank (y : Y) :
    (f ∣_ rankOpen f y).finrank = fun _ ↦ f.finrank y := by
  funext z
  rw [Scheme.Hom.finrank_of_isPullback
    (f ⁻¹ᵁ rankOpen f y).ι (f ∣_ rankOpen f y) f
      (rankOpen f y).ι (isPullback_morphismRestrict f (rankOpen f y)).flip]
  exact z.2

end MazurTorsion.AlgebraicGeometry.Jacobian.FiniteFlatConstantRankNeighborhood

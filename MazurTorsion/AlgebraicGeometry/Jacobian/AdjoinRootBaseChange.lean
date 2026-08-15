/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.RingTheory.AdjoinRoot

/-!
# Base change for adjoining a root

This file records the usual base-change equivalence for a polynomial root
algebra with the coefficient tensor factor simplified.  Mathlib's
`AdjoinRoot.tensorAlgEquiv` naturally lands over `B ⊗[A] A`; composing with
the right-unit equivalence gives the more convenient algebra over `B`.

The named downstream consumer is `AffineLineUniversalIncidence`: it identifies
the ordered affine incidence algebra with the pullback of the universal monic
root algebra to ordered-root coordinates.
-/

noncomputable section

open Algebra Polynomial TensorProduct

namespace MazurTorsion.AlgebraicGeometry.Jacobian.AdjoinRootBaseChange

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]

/-- Adjoining a root commutes with extension of scalars, written with the
usual coefficient map `A → B` on the target polynomial. -/
noncomputable def equiv (p : A[X]) :
    B ⊗[A] AdjoinRoot p ≃ₐ[B]
      AdjoinRoot (p.map (algebraMap A B)) :=
  (AdjoinRoot.tensorAlgEquiv p
      (p.map Algebra.TensorProduct.includeRight.toRingHom) rfl).trans
    (AdjoinRoot.mapAlgEquiv
      (Algebra.TensorProduct.rid A B B)
      (p.map Algebra.TensorProduct.includeRight.toRingHom)
      (p.map (algebraMap A B)) (by
        apply Associated.of_eq
        rw [Polynomial.map_map]
        congr 1
        ext a
        simp [Algebra.smul_def]))

@[simp]
theorem equiv_tmul_root (p : A[X]) :
    equiv A B p (1 ⊗ₜ AdjoinRoot.root p) =
      AdjoinRoot.root (p.map (algebraMap A B)) := by
  rw [equiv, AlgEquiv.trans_apply, AdjoinRoot.tensorAlgEquiv_root]
  simp only [AdjoinRoot.coe_mapAlgEquiv, AdjoinRoot.map_root]

end MazurTorsion.AlgebraicGeometry.Jacobian.AdjoinRootBaseChange

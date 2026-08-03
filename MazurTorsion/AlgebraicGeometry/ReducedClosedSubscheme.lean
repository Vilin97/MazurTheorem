/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Properties

/-!
# Factoring reduced schemes through reduced closed subschemes

A quasi-compact morphism from a reduced scheme has radical kernel.  Consequently, if its
set-theoretic range lies in a closed subset of the target, it factors through the reduced induced
scheme structure defined by the closed subset's vanishing ideal sheaf.

The projective Weierstrass cubic is the first downstream consumer: coordinate triples first define
maps to projective space, and this factorization turns the equation's set-theoretic vanishing into
scheme-valued points of the reduced cubic.
-/

noncomputable section

open CategoryTheory
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.ReducedClosedSubscheme

universe u

/-- The kernel ideal sheaf of a quasi-compact morphism out of a reduced scheme is radical. -/
theorem hom_ker_radical_of_isReduced {X Y : Scheme.{u}} [IsReduced X]
    (g : X ⟶ Y) [QuasiCompact g] : g.ker.radical = g.ker := by
  ext U x
  rw [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply,
    RingHom.ker_eq_comap_bot,
    (Ideal.isRadical_bot.comap (g.app U).hom).radical]

/-- A map from a reduced scheme whose range is contained in a closed subset kills that subset's
vanishing ideal sheaf. -/
theorem vanishingIdeal_le_ker_of_range_subset {X Y : Scheme.{u}} [IsReduced X]
    (g : X ⟶ Y) [QuasiCompact g] (Z : TopologicalSpace.Closeds Y)
    (h : Set.range g ⊆ Z) : Scheme.IdealSheafData.vanishingIdeal Z ≤ g.ker := by
  have hsupp : g.ker.support ≤ Z := by
    rw [← SetLike.coe_subset_coe, Scheme.Hom.support_ker]
    exact closure_minimal h Z.isClosed
  exact (Scheme.IdealSheafData.vanishingIdeal_antimono hsupp).trans_eq <| by
    rw [Scheme.IdealSheafData.vanishingIdeal_support,
      hom_ker_radical_of_isReduced]

/-- Factor a quasi-compact map from a reduced scheme through the reduced induced scheme structure
on any closed subset containing its range. -/
noncomputable def lift {X Y : Scheme.{u}} [IsReduced X]
    (g : X ⟶ Y) [QuasiCompact g] (Z : TopologicalSpace.Closeds Y)
    (h : Set.range g ⊆ Z) : X ⟶ (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
  IsClosedImmersion.lift
    (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι g <| by
      rw [(Scheme.IdealSheafData.vanishingIdeal Z).ker_subschemeι]
      exact vanishingIdeal_le_ker_of_range_subset g Z h

@[simp]
theorem lift_comp_subschemeι {X Y : Scheme.{u}} [IsReduced X]
    (g : X ⟶ Y) [QuasiCompact g] (Z : TopologicalSpace.Closeds Y)
    (h : Set.range g ⊆ Z) :
    lift g Z h ≫ (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = g :=
  IsClosedImmersion.lift_fac _ _ _

end MazurTorsion.AlgebraicGeometry.ReducedClosedSubscheme

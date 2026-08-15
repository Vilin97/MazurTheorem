/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.TopologicalSheafBaseLinearClosedEmbeddingExt
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Sites.GlobalSections

/-!
# Degree-zero constant-source Ext and global sections

For a sheaf of modules over a fixed coefficient ring, degree-zero Ext
from the constant rank-one sheaf is the module of global sections.
This file records the comparison as a linear equivalence.
-/


open CategoryTheory Limits Opposite TopologicalSpace

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.TopCat

variable {R : Type u} [CommRing R]
variable {X : TopCat.{u}}

/-- The constant-sheaf/global-sections adjunction is linear on morphisms
out of the rank-one module. -/
noncomputable def constantRankOneHomLinearEquivSections
    (F : X.Sheaf (ModuleCat.{u} R)) :
    (constantRankOneSheaf (R := R) X ⟶ F) ≃ₗ[R]
      F.obj.obj (op (⊤ : Opens X)) := by
  let adj :=
    constantSheafAdj
      (Opens.grothendieckTopology X)
      (ModuleCat.{u} R)
      (isTerminalTop : IsTerminal (⊤ : Opens X))
  let eAdj :
      (constantRankOneSheaf (R := R) X ⟶ F) ≃ₗ[R]
        (ModuleCat.of R R ⟶
          F.obj.obj (op (⊤ : Opens X))) :=
    { toAddEquiv :=
        adj.homAddEquiv
          (ModuleCat.of R R) F
      map_smul' := fun r f => by
        rfl }
  exact
    eAdj.trans ModuleCat.homLinearEquiv |>.trans
      (LinearMap.ringLmapEquivSelf R R
        (F.obj.obj (op (⊤ : Opens X))))

/-- Degree-zero Ext from the constant rank-one sheaf is linearly
equivalent to global sections. -/
noncomputable def constantRankOneExtZeroLinearEquivSections
    (F : X.Sheaf (ModuleCat.{u} R)) :
    Abelian.Ext
        (constantRankOneSheaf (R := R) X) F 0 ≃ₗ[R]
      F.obj.obj (op (⊤ : Opens X)) :=
  (Abelian.Ext.linearEquiv₀ (R := R)).trans
    (constantRankOneHomLinearEquivSections F)

/-- Finite generation of degree-zero constant-source Ext is equivalent
to finite generation of global sections. -/
theorem constantRankOneExtZero_finite_iff_sections
    (F : X.Sheaf (ModuleCat.{u} R)) :
    Module.Finite R
        (Abelian.Ext
          (constantRankOneSheaf (R := R) X) F 0) ↔
      Module.Finite R
        (F.obj.obj (op (⊤ : Opens X))) := by
  let e := constantRankOneExtZeroLinearEquivSections F
  constructor
  · intro h
    letI := h
    exact Module.Finite.equiv e
  · intro h
    letI := h
    exact Module.Finite.equiv e.symm

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.TopCat

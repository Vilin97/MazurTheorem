/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentCategory

/-!
# Components of isomorphisms of cover descent data

An isomorphism in the cover-descent category is chartwise an isomorphism.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.CoverDescentData

variable {D : Scheme.GlueData.{0}}

/-- The component on one chart of an isomorphism of cover descent data. -/
noncomputable def isoApp
    {A B : CoverDescentData D} (e : A ≅ B) (i : D.J) :
    A.chart i ≅ B.chart i where
  hom := e.hom.app i
  inv := e.inv.app i
  hom_inv_id := by
    have h :=
      congrArg (fun f : A ⟶ A => f.app i)
        e.hom_inv_id
    simpa only [comp_app, id_app] using h
  inv_hom_id := by
    have h :=
      congrArg (fun f : B ⟶ B => f.app i)
        e.inv_hom_id
    simpa only [comp_app, id_app] using h

end AlgebraicGeometry.Scheme.Modules.CoverDescentData

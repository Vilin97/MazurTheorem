/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentIso
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleScalarTwistGluedEquivalence

/-!
# Chart restrictions of a glued scalar twist

A scalar twist changes descent transitions but not the module on any
individual chart.
-/


open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.CoverDescentData

variable {D : Scheme.GlueData.{0}}

/-- Restriction of a globally glued scalar twist to one chart is
canonically isomorphic to the original chart restriction. -/
noncomputable def scalarTwistGluedChartIso
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle : CoverUnitCocycleCondition D a)
    (W : D.glued.Modules) (i : D.J) :
    (pullback (D.ι i)).obj
        ((scalarTwistGluedEquivalence
          a hself hcocycle).functor.obj W) ≅
      (pullback (D.ι i)).obj W :=
  isoApp
    (scalarTwistGluedRestrictionIso
      a hself hcocycle W)
    i

end AlgebraicGeometry.Scheme.Modules.CoverDescentData

/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwist
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleDescentEffectiveBridge

/-!
# Local triviality of the Serre twist

Effective descent identifies the restriction of the glued twist with the
unit module on each standard chart.  Transport through the canonical
isomorphism from the glued cover to projective space gives the usual chart
trivialization of `𝒪(m)`.  Pulling this isomorphism back once more gives a
trivialization on every nonempty finite standard intersection.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ModuleDescent
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafScalar

variable (k : Type) [CommRing k] (d : ℕ)

/-- The descended Serre twist restricts to the unit module on each chart of
the glued model. -/
def gluedChartIso (m : ℕ) (i : Fin (d + 1)) :
    (Scheme.Modules.pullback ((glueData k d).ι i)).obj
        (gluedModule k d m) ≅
      SheafOfModules.unit ((glueData k d).U i).ringCatSheaf :=
  restrictionIso
    (glueData k d)
    (fun i =>
      SheafOfModules.unit ((glueData k d).U i).ringCatSheaf)
    (fun i j => transition k d m i j)
    (fun i => transition_self k d m i)
    (fun i j l => transition_cocycle k d m i j l)
    i

/-- Following a standard-chart inclusion by the inverse of the glued-cover
isomorphism recovers the corresponding glued-chart inclusion. -/
lemma chart_comp_fromGlued_inv (i : Fin (d + 1)) :
    (cover k d).f i ≫ inv (cover k d).fromGlued =
      (glueData k d).ι i := by
  rw [← (cover k d).ι_fromGlued i]
  let ιi := (glueData k d).ι i
  change
    (ιi ≫ (cover k d).fromGlued) ≫
        inv (cover k d).fromGlued = ιi
  rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- The Serre twist is trivial on every standard coordinate chart. -/
def chartIso (m : ℕ) (i : Fin (d + 1)) :
    (Scheme.Modules.pullback ((cover k d).f i)).obj
        (O k d m) ≅
      SheafOfModules.unit ((cover k d).X i).ringCatSheaf :=
  (Scheme.Modules.pullbackComp
      ((cover k d).f i)
      (inv (cover k d).fromGlued)).app
        (gluedModule k d m) ≪≫
    (Scheme.Modules.pullbackCongr
      (chart_comp_fromGlued_inv k d i)).app
        (gluedModule k d m) ≪≫
    gluedChartIso k d m i

/-- A standard finite intersection lies in each chart occurring in its
indexing family. -/
lemma standardIntersection_le_chart
    {ι : Type} [Fintype ι]
    (a : ι → Fin (d + 1)) (j : ι) :
    standardIntersection k a ≤ standardChart k (a j) := by
  rw [standardIntersection_eq_iInf]
  exact iInf_le _ j

/-- The inclusion of a standard finite intersection factors through any
one of its constituent standard charts. -/
lemma intersectionHom_comp_chart
    {ι : Type} [Fintype ι]
    (a : ι → Fin (d + 1)) (j : ι) :
    (scheme k d).homOfLE
        (standardIntersection_le_chart k d a j) ≫
      (cover k d).f (a j) =
        (standardIntersection k a).ι := by
  exact (scheme k d).homOfLE_ι
    (standardIntersection_le_chart k d a j)

/-- `𝒪(m)` is trivial on every nonempty finite intersection of standard
charts.  The chosen `j` only selects which chart trivialization is pulled
back. -/
def intersectionIso (m : ℕ)
    {ι : Type} [Fintype ι]
    (a : ι → Fin (d + 1)) (j : ι) :
    (Scheme.Modules.pullback
      (standardIntersection k a).ι).obj (O k d m) ≅
      SheafOfModules.unit
        (standardIntersection k a).toScheme.ringCatSheaf :=
  (Scheme.Modules.pullbackCongr
      (intersectionHom_comp_chart k d a j)).symm.app
        (O k d m) ≪≫
    (Scheme.Modules.pullbackComp
      ((scheme k d).homOfLE
        (standardIntersection_le_chart k d a j))
      ((cover k d).f (a j))).symm.app
        (O k d m) ≪≫
    (Scheme.Modules.pullback
      ((scheme k d).homOfLE
        (standardIntersection_le_chart k d a j))).mapIso
          (chartIso k d m (a j)) ≪≫
    pullbackUnitIso
      ((scheme k d).homOfLE
        (standardIntersection_le_chart k d a j))

/-- Canonical trivialization on a Čech intersection, using its zeroth
coordinate. -/
def cechIntersectionIso (m p : ℕ)
    (a : Fin (p + 1) → Fin (d + 1)) :
    (Scheme.Modules.pullback
      (cechIntersection k a).ι).obj (O k d m) ≅
      SheafOfModules.unit
        (cechIntersection k a).toScheme.ringCatSheaf :=
  intersectionIso k d m a 0

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

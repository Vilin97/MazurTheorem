/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleDescentObject
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleEffectiveDescent

/-!
# Effective descent for the small equalizer interface

`ModuleDescent.glueObject` is the compact construction-level interface used
throughout this project.  The full effective-descent proof is phrased using
`Scheme.Modules.glue`.  The two equalizer constructions are definitionally
the same, and this file transports the chart-restriction isomorphism between
the two APIs.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ModuleDescent

variable (D : Scheme.GlueData.{0})
  (M : ∀ i, (D.U i).Modules)
  (e : ∀ i j,
    (Scheme.Modules.pullback (D.f i j)).obj (M i) ≅
      (Scheme.Modules.pullback
        (D.t i j ≫ D.f j i)).obj (M j))
  (hIdentity : ∀ i, e i i =
    eqToIso (congrArg
      (fun f => (Scheme.Modules.pullback f).obj (M i))
      (show D.f i i = D.t i i ≫ D.f i i by
        rw [D.t_id i, Category.id_comp])))
  (hCocycle : ∀ i j k,
    pullbackTransport
        (pullback.fst (D.f i j) (D.f i k))
        (D.f i j) (D.t i j ≫ D.f j i) (e i j) ≪≫
      (Scheme.Modules.pullbackCongr
        (bridgeMiddle D i j k)).app (M j) ≪≫
      pullbackTransport
        (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
        (D.f j k) (D.t j k ≫ D.f k j) (e j k) ≪≫
      (Scheme.Modules.pullbackCongr
        (bridgeTarget D i j k)).app (M k) =
    (Scheme.Modules.pullbackCongr
      (bridgeSource D i j k)).app (M i) ≪≫
      pullbackTransport
        (pullback.snd (D.f i j) (D.f i k))
        (D.f i k) (D.t i k ≫ D.f k i) (e i k))

/-- The compact and full equalizer constructions of the descended module are
definitionally isomorphic. -/
def glueObjectIsoGlue :
    glueObject D M e hIdentity hCocycle ≅
      Scheme.Modules.glue D M e hIdentity hCocycle :=
  Iso.refl _

/-- Effective descent: restriction of `glueObject` to a chart recovers the
given chartwise module. -/
def restrictionIso (i : D.J) :
    (Scheme.Modules.pullback (D.ι i)).obj
        (glueObject D M e hIdentity hCocycle) ≅
      M i :=
  (Scheme.Modules.pullback (D.ι i)).mapIso
      (glueObjectIsoGlue D M e hIdentity hCocycle) ≪≫
    Scheme.Modules.glueRestrictionIso
      D M e hIdentity hCocycle i

/-- The chart restriction isomorphisms recover the prescribed transition
on every pairwise overlap.  This is the morphism-level compatibility needed
to glue maps out of a descended module. -/
theorem restrictionIso_overlap_compat (i j : D.J) :
    (Scheme.Modules.pullbackComp (D.f i j) (D.ι i)).inv.app
          (glueObject D M e hIdentity hCocycle) ≫
        (Scheme.Modules.pullback (D.f i j)).map
          (restrictionIso D M e hIdentity hCocycle i).hom =
      (Scheme.Modules.pullbackCongr
          (show
            (D.t i j ≫ D.f j i) ≫ D.ι j =
              D.f i j ≫ D.ι i by
            rw [Category.assoc]
            exact D.glue_condition i j)).inv.app
            (glueObject D M e hIdentity hCocycle) ≫
        (Scheme.Modules.pullbackComp
          (D.t i j ≫ D.f j i) (D.ι j)).inv.app
            (glueObject D M e hIdentity hCocycle) ≫
        (Scheme.Modules.pullback
          (D.t i j ≫ D.f j i)).map
            (restrictionIso D M e hIdentity hCocycle j).hom ≫
        (e i j).inv := by
  have hrestriction (q : D.J) :
      (restrictionIso D M e hIdentity hCocycle q).hom =
        Scheme.Modules.glueRestrictionHom
          D M e hIdentity hCocycle q := by
    dsimp only [restrictionIso, glueObjectIsoGlue,
      Scheme.Modules.glueRestrictionIso, Iso.trans_hom,
      Iso.refl_hom]
    exact (CategoryTheory.eq_whisker
      ((Scheme.Modules.pullback (D.ι q)).map_id _) _).trans
        (Category.id_comp _)
  rw [hrestriction i, hrestriction j]
  exact Scheme.Modules.glueRestriction_overlap_compat
    D M e hIdentity hCocycle i j

/-- The overlap compatibility theorem with a caller-supplied proof of the
gluing equation.  This keeps dependent pullback casts syntactically aligned
with downstream named equations. -/
theorem restrictionIso_overlap_compat_of_eq (i j : D.J)
    (h : (D.t i j ≫ D.f j i) ≫ D.ι j = D.f i j ≫ D.ι i) :
    (Scheme.Modules.pullbackComp (D.f i j) (D.ι i)).inv.app
          (glueObject D M e hIdentity hCocycle) ≫
        (Scheme.Modules.pullback (D.f i j)).map
          (restrictionIso D M e hIdentity hCocycle i).hom =
      (Scheme.Modules.pullbackCongr h).inv.app
            (glueObject D M e hIdentity hCocycle) ≫
        (Scheme.Modules.pullbackComp
          (D.t i j ≫ D.f j i) (D.ι j)).inv.app
            (glueObject D M e hIdentity hCocycle) ≫
        (Scheme.Modules.pullback
          (D.t i j ≫ D.f j i)).map
            (restrictionIso D M e hIdentity hCocycle j).hom ≫
        (e i j).inv := by
  exact restrictionIso_overlap_compat
    D M e hIdentity hCocycle i j

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ModuleDescent

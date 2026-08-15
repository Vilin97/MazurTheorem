/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistIntegerTransition
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistLocalTrivialization

/-!
# Integer Serre twists

Integer powers of the standard transition ratios descend to line modules on
projective space.  The negative twists in finite twisted-free
presentations are the special case `OInt (-n)`.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ModuleDescent
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafScalar

variable (k : Type) [CommRing k] (d : ℕ)

/-- The chartwise unit modules in the integer-twist descent datum. -/
def integerChartModules :
    ∀ i, ((glueData k d).U i).Modules :=
  fun i => SheafOfModules.unit ((glueData k d).U i).ringCatSheaf

/-- The integer transition family, named once for effective descent. -/
def integerTransitionFamily (m : ℤ) :
    ∀ i j,
      (Scheme.Modules.pullback ((glueData k d).f i j)).obj
          (integerChartModules k d i) ≅
        (Scheme.Modules.pullback
          ((glueData k d).t i j ≫ (glueData k d).f j i)).obj
          (integerChartModules k d j) :=
  fun i j => integerTransition k d m i j

/-- The identity proof in the named integer descent datum. -/
def integerIdentityFamily (m : ℤ) :=
  fun i => integerTransition_self k d m i

/-- The cocycle proof in the named integer descent datum. -/
def integerCocycleFamily (m : ℤ) :=
  fun i j l => integerTransition_cocycle k d m i j l

/-- The integer Serre twist on the scheme glued from the standard charts. -/
def gluedIntegerModule (m : ℤ) : (glueData k d).glued.Modules :=
  glueObject
    (glueData k d)
    (integerChartModules k d)
    (integerTransitionFamily k d m)
    (integerIdentityFamily k d m)
    (integerCocycleFamily k d m)

/-- The integer Serre twist `𝒪(m)` on projective space. -/
def integerModule (m : ℤ) : (scheme k d).Modules :=
  (Scheme.Modules.pullback (inv (cover k d).fromGlued)).obj
    (gluedIntegerModule k d m)

/-- Short name for the integer Serre twist. -/
abbrev OInt (m : ℤ) : (scheme k d).Modules :=
  integerModule k d m

/-- The negative twist `𝒪(-n)`, indexed by a natural number. -/
abbrev ONeg (n : ℕ) : (scheme k d).Modules :=
  OInt k d (-(n : ℤ))

/-- The integer descended twist restricts to the unit module on every
chart of the glued model. -/
def gluedIntegerChartIso (m : ℤ) (i : Fin (d + 1)) :
    (Scheme.Modules.pullback ((glueData k d).ι i)).obj
        (gluedIntegerModule k d m) ≅
      SheafOfModules.unit ((glueData k d).U i).ringCatSheaf :=
  restrictionIso
    (glueData k d)
    (integerChartModules k d)
    (integerTransitionFamily k d m)
    (integerIdentityFamily k d m)
    (integerCocycleFamily k d m)
    i

/-- Every integer Serre twist is trivial on a standard coordinate chart. -/
def integerChartIso (m : ℤ) (i : Fin (d + 1)) :
    (Scheme.Modules.pullback ((cover k d).f i)).obj
        (OInt k d m) ≅
      SheafOfModules.unit ((cover k d).X i).ringCatSheaf :=
  (Scheme.Modules.pullbackComp
      ((cover k d).f i)
      (inv (cover k d).fromGlued)).app
        (gluedIntegerModule k d m) ≪≫
    (Scheme.Modules.pullbackCongr
      (chart_comp_fromGlued_inv k d i)).app
        (gluedIntegerModule k d m) ≪≫
    gluedIntegerChartIso k d m i

/-- Every integer Serre twist is trivial on a nonempty finite standard
intersection. -/
def integerIntersectionIso (m : ℤ)
    {ι : Type} [Fintype ι]
    (a : ι → Fin (d + 1)) (j : ι) :
    (Scheme.Modules.pullback
      (standardIntersection k a).ι).obj (OInt k d m) ≅
      SheafOfModules.unit
        (standardIntersection k a).toScheme.ringCatSheaf :=
  (Scheme.Modules.pullbackCongr
      (intersectionHom_comp_chart k d a j)).symm.app
        (OInt k d m) ≪≫
    (Scheme.Modules.pullbackComp
      ((scheme k d).homOfLE
        (standardIntersection_le_chart k d a j))
      ((cover k d).f (a j))).symm.app
        (OInt k d m) ≪≫
    (Scheme.Modules.pullback
      ((scheme k d).homOfLE
        (standardIntersection_le_chart k d a j))).mapIso
          (integerChartIso k d m (a j)) ≪≫
    pullbackUnitIso
      ((scheme k d).homOfLE
        (standardIntersection_le_chart k d a j))

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

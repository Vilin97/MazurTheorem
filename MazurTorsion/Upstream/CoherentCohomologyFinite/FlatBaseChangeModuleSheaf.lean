/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FreeModuleSheafOpenCohomology
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-!
# Flat change of coefficients for free module sheaves

Let `R` be a commutative ring which is flat over `ℤ`.  Extension and
restriction of scalars lift to sheaves, and restriction preserves
injective objects.  Consequently, Ext from the free `R`-module sheaf
represented by an open is the ordinary open-indexed cohomology of the
underlying abelian sheaf.

This is the arbitrary-flat-base version of the rational comparison used
earlier in the project.
-/

open CategoryTheory Limits TopologicalSpace


noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.FlatBaseChange

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ExtAdjunction
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ExtChangeOfScalars
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FreeModuleSheafOpenCohomology

variable (R : Type) [CommRing R]

/-- Restriction of scalars from `R` to the canonical integer action. -/
noncomputable abbrev restrictToIntegers :
    ModuleCat.{0} R ⥤ ModuleCat.{0} ℤ :=
  ModuleCat.restrictScalars (algebraMap ℤ R)

/-- Extension of integer scalars to `R`. -/
noncomputable abbrev extendIntegers :
    ModuleCat.{0} ℤ ⥤ ModuleCat.{0} R :=
  ModuleCat.extendScalars (algebraMap ℤ R)

/-- Coextension of integer scalars to `R`. -/
noncomputable abbrev coextendIntegers :
    ModuleCat.{0} ℤ ⥤ ModuleCat.{0} R :=
  ModuleCat.coextendScalars (algebraMap ℤ R)

variable {C : Type} [SmallCategory C]

/-- Restriction of scalars on sheaves of modules. -/
noncomputable abbrev sheafRestrictToIntegers
    (J : GrothendieckTopology C) :
    Sheaf J (ModuleCat.{0} R) ⥤
      Sheaf J (ModuleCat.{0} ℤ) :=
  sheafCompose J (restrictToIntegers R)

/-- Extension of scalars on sheaves of modules. -/
noncomputable abbrev sheafExtendIntegers
    (J : GrothendieckTopology C) :
    Sheaf J (ModuleCat.{0} ℤ) ⥤
      Sheaf J (ModuleCat.{0} R) :=
  Sheaf.composeAndSheafify J (extendIntegers R)

/-- Coextension of scalars on sheaves of modules. -/
noncomputable abbrev sheafCoextendIntegers
    (J : GrothendieckTopology C) :
    Sheaf J (ModuleCat.{0} ℤ) ⥤
      Sheaf J (ModuleCat.{0} R) :=
  sheafCompose J (coextendIntegers R)

/-- The sheaf-level extension/restriction adjunction. -/
noncomputable def sheafExtendRestrictAdjunction
    (J : GrothendieckTopology C) :
    sheafExtendIntegers R J ⊣
      sheafRestrictToIntegers R J :=
  Sheaf.adjunction J
    (ModuleCat.extendRestrictScalarsAdj
      (algebraMap ℤ R))

/-- The sheaf-level restriction/coextension adjunction. -/
noncomputable def sheafRestrictCoextendAdjunction
    (J : GrothendieckTopology C) :
    sheafRestrictToIntegers R J ⊣
      sheafCoextendIntegers R J :=
  MazurTorsion.AlgebraicGeometry.CoherentCohomology.ExtChangeOfScalars.sheafComposeAdjunction
    J
    (ModuleCat.restrictCoextendScalarsAdj
      (algebraMap ℤ R))

/-- Extending the free integer module gives the free `R`-module on the
same set of generators. -/
noncomputable def freeExtendIso :
    ModuleCat.free ℤ ⋙ extendIntegers R ≅
      ModuleCat.free R :=
  ((ModuleCat.adj ℤ).comp
      (ModuleCat.extendRestrictScalarsAdj
        (algebraMap ℤ R))).leftAdjointUniq
    (ModuleCat.adj R)

/-- Extension of scalars commutes with the free module sheaf represented
by an open. -/
noncomputable def freeModuleSheafExtendIso
    {T : TopCat} (V : Opens T) :
    (sheafExtendIntegers R
      (Opens.grothendieckTopology T)).obj
        (freeModuleSheaf (R := ℤ) V) ≅
      freeModuleSheaf (R := R) V := by
  let J := Opens.grothendieckTopology T
  let P := yoneda.obj V ⋙ ModuleCat.free ℤ
  exact
    (presheafToSheafCompComposeAndSheafifyIso
      J (extendIntegers R)).app P ≪≫
      (presheafToSheaf J (ModuleCat.{0} R)).mapIso
        (Functor.isoWhiskerLeft
          (yoneda.obj V) (freeExtendIso R))

noncomputable local instance sheafRestrict_isRightAdjoint
    (J : GrothendieckTopology C) :
    (sheafRestrictToIntegers R J).IsRightAdjoint :=
  (sheafExtendRestrictAdjunction R J).isRightAdjoint

noncomputable local instance sheafRestrict_isLeftAdjoint
    (J : GrothendieckTopology C) :
    (sheafRestrictToIntegers R J).IsLeftAdjoint :=
  (sheafRestrictCoextendAdjunction R J).isLeftAdjoint

noncomputable local instance sheafRestrict_additive
    (J : GrothendieckTopology C) :
    (sheafRestrictToIntegers R J).Additive :=
  (sheafRestrictToIntegers R J).additive_of_preserves_binary_products

noncomputable local instance extend_preservesFiniteLimits
    [Module.Flat ℤ R] :
    PreservesFiniteLimits (extendIntegers R) :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat <|
    (RingHom.flat_algebraMap_iff.mpr inferInstance :
      (algebraMap ℤ R).Flat)

noncomputable local instance sheafRestrict_preservesInjectiveObjects
    [Module.Flat ℤ R]
    (J : GrothendieckTopology C) :
    (sheafRestrictToIntegers R J).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (sheafExtendRestrictAdjunction R J)

/-- Ext from a represented free `R`-module sheaf computes the
open-indexed cohomology of the underlying abelian sheaf. -/
noncomputable def freeModuleSheafExtAddEquivUnderlyingAbHPrime
    [Module.Flat ℤ R]
    {T : TopCat} (V : Opens T)
    (F : Sheaf (Opens.grothendieckTopology T)
      (ModuleCat.{0} R))
    (n : ℕ) :
    Abelian.Ext
        (freeModuleSheaf (R := R) V) F n ≃+
      CategoryTheory.Sheaf.H'
        ((sheafForgetZToAb
          (Opens.grothendieckTopology T)).obj
          ((sheafRestrictToIntegers R
            (Opens.grothendieckTopology T)).obj F))
        n V := by
  let J := Opens.grothendieckTopology T
  let A := freeModuleSheaf (R := ℤ) V
  exact
    (precompIsoAddEquiv
      (freeModuleSheafExtendIso R V) n).trans <|
    (extAddEquiv
      (sheafExtendIntegers R J)
      (sheafRestrictToIntegers R J)
      (sheafExtendRestrictAdjunction R J)
      A F n).trans <|
    (sheafForgetZToAb_extAddEquiv J A
      ((sheafRestrictToIntegers R J).obj F) n).trans <|
      (precompIsoAddEquiv
        (freeModuleSheafForgetIso V) n).symm

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.FlatBaseChange

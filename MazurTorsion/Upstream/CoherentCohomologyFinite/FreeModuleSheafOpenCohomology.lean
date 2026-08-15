/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ExtChangeOfScalars
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteSubsetFreeSheafExtAcyclic
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafOpenCohomology

/-!
# Ext from a free module sheaf on an open

For a rational module sheaf, Ext from the sheafified free module
represented by an open agrees additively with ordinary open-indexed
cohomology of the underlying abelian sheaf.  This is the source-side
change-of-scalars comparison needed by normalized Čech resolutions.
-/

open CategoryTheory TopologicalSpace


noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.FreeModuleSheafOpenCohomology

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.CoefficientRationalization
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ExtChangeOfScalars
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf

/-- Base extension carries a free integer module to the free rational
module on the same generators. -/
noncomputable def freeExtendIso :
    ModuleCat.free ℤ ⋙ extendZToQ ≅ ModuleCat.free ℚ :=
  ((ModuleCat.adj ℤ).comp
      (ModuleCat.extendRestrictScalarsAdj (algebraMap ℤ ℚ))).leftAdjointUniq
    (ModuleCat.adj ℚ)

/-- The inverse of the equivalence between abelian groups and integer
modules has the expected underlying-type functor. -/
noncomputable def liftForgetIso :
    liftAbToZ ⋙ forget (ModuleCat ℤ) ≅
      forget AddCommGrpCat := by
  change
    liftAbToZ ⋙ (forgetZToAb ⋙ forget AddCommGrpCat) ≅
      forget AddCommGrpCat
  exact
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight forgetZToAb.asEquivalence.counitIso
        (forget AddCommGrpCat) ≪≫
      Functor.leftUnitor _

/-- Forgetting the integer-module structure on a free integer module
gives the free abelian group on the same generators. -/
noncomputable def freeForgetIso :
    ModuleCat.free ℤ ⋙ forgetZToAb ≅ AddCommGrpCat.free :=
  (((ModuleCat.adj ℤ).comp
      forgetZToAb.asEquivalence.toAdjunction).ofNatIsoRight
        liftForgetIso).leftAdjointUniq
    AddCommGrpCat.adj

/-- Base extension commutes with the free module sheaf represented by an
open. -/
noncomputable def freeModuleSheafExtendIso
    {T : TopCat} (V : Opens T) :
    (sheafExtendZToQ (Opens.grothendieckTopology T)).obj
        (freeModuleSheaf (R := ℤ) V) ≅
      freeModuleSheaf (R := ℚ) V := by
  let J := Opens.grothendieckTopology T
  let P := yoneda.obj V ⋙ ModuleCat.free ℤ
  exact
    (presheafToSheafCompComposeAndSheafifyIso J extendZToQ).app P ≪≫
      (presheafToSheaf J (ModuleCat ℚ)).mapIso
        (Functor.isoWhiskerLeft (yoneda.obj V) freeExtendIso)

/-- Forgetting scalars identifies the free integer module sheaf
represented by an open with the free abelian sheaf represented there. -/
noncomputable def freeModuleSheafForgetIso
    {T : TopCat} (V : Opens T) :
    (sheafForgetZToAb (Opens.grothendieckTopology T)).obj
        (freeModuleSheaf (R := ℤ) V) ≅
      TopCat.Sheaf.OpenCohomology.freeAbSheaf V := by
  let J := Opens.grothendieckTopology T
  let P := yoneda.obj V ⋙ ModuleCat.free ℤ
  exact
    ((sheafComposeNatIso J forgetZToAb
      (sheafificationAdjunction J (ModuleCat ℤ))
      (sheafificationAdjunction J AddCommGrpCat)).app P).symm ≪≫
      (presheafToSheaf J AddCommGrpCat).mapIso
        (Functor.isoWhiskerLeft (yoneda.obj V) freeForgetIso)

noncomputable local instance sheafRestrictQToZ_isRightAdjoint
    {C : Type} [SmallCategory C] (J : GrothendieckTopology C) :
    (sheafRestrictQToZ J).IsRightAdjoint :=
  (sheafExtendRestrictAdjunction J).isRightAdjoint

noncomputable local instance sheafRestrictQToZ_isLeftAdjoint
    {C : Type} [SmallCategory C] (J : GrothendieckTopology C) :
    (sheafRestrictQToZ J).IsLeftAdjoint :=
  (sheafRestrictCoextendAdjunction J).isLeftAdjoint

noncomputable local instance sheafRestrictQToZ_additive
    {C : Type} [SmallCategory C] (J : GrothendieckTopology C) :
    (sheafRestrictQToZ J).Additive :=
  (sheafRestrictQToZ J).additive_of_preserves_binary_products

noncomputable local instance extendZToQ_preservesFiniteLimits :
    Limits.PreservesFiniteLimits extendZToQ :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat <|
    RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat ℚ (Submonoid.pos ℤ))

noncomputable local instance sheafRestrictQToZ_preservesInjectiveObjects
    {C : Type} [SmallCategory C] (J : GrothendieckTopology C) :
    (sheafRestrictQToZ J).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (sheafExtendRestrictAdjunction J)

/-- Ext from a free rational module sheaf on an open is the open-indexed
cohomology of the underlying abelian sheaf. -/
noncomputable def freeModuleSheafExtAddEquivHPrime
    {T : TopCat} (V : Opens T)
    (F : Sheaf (Opens.grothendieckTopology T) (ModuleCat ℚ))
    (n : ℕ) :
    Abelian.Ext
        (freeModuleSheaf (R := ℚ) V) F n ≃+
      CategoryTheory.Sheaf.H'
        ((UAb (Opens.grothendieckTopology T)).obj F) n V := by
  let J := Opens.grothendieckTopology T
  let A := freeModuleSheaf (R := ℤ) V
  exact
    (ExtAdjunction.precompIsoAddEquiv
      (freeModuleSheafExtendIso V) n).trans <|
    (ExtAdjunction.extAddEquiv
      (sheafExtendZToQ J) (sheafRestrictQToZ J)
      (sheafExtendRestrictAdjunction J) A F n).trans <|
    (sheafForgetZToAb_extAddEquiv J A
      ((sheafRestrictQToZ J).obj F) n).trans <|
    (ExtAdjunction.precompIsoAddEquiv
      (freeModuleSheafForgetIso V) n).symm.trans <|
    ExtAdjunction.postcompIsoAddEquiv
      ((sheafRestrictForgetIso J).app F) n

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.FreeModuleSheafOpenCohomology

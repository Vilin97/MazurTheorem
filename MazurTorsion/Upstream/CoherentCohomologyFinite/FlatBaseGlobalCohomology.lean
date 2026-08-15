/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FlatBaseOpenCohomology

/-!
# Global cohomology over a flat coefficient ring

For a commutative ring `R` flat over `ℤ`, Ext from the constant rank-one
sheaf of `R`-modules computes ordinary global cohomology after forgetting
the coefficient action.  This is the global counterpart of the
open-indexed comparison in `FlatBaseOpenCohomology`.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace


noncomputable section

noncomputable local instance flatGlobalCohomologyAddCommGroup
    {Z : TopCat} (G : Z.Sheaf AddCommGrpCat) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H G n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.FlatBaseChange

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ExtAdjunction
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ExtChangeOfScalars
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf

variable (R : Type) [CommRing R]

/-- Extension of integer scalars commutes with the constant-sheaf
left adjoint on the opens site of a topological space. -/
noncomputable def constantSheafExtendIntegersIso
    {T : TopCat} :
    constantSheaf
          (Opens.grothendieckTopology T)
          (ModuleCat ℤ) ⋙
        sheafExtendIntegers R
          (Opens.grothendieckTopology T) ≅
      extendIntegers R ⋙
        constantSheaf
          (Opens.grothendieckTopology T)
          (ModuleCat R) :=
  ((constantSheafAdj
      (Opens.grothendieckTopology T)
      (ModuleCat ℤ) isTerminalTop).comp
    (sheafExtendRestrictAdjunction R
      (Opens.grothendieckTopology T))).leftAdjointUniq
    ((ModuleCat.extendRestrictScalarsAdj
      (algebraMap ℤ R)).comp
      (constantSheafAdj
        (Opens.grothendieckTopology T)
        (ModuleCat R) isTerminalTop))

/-- Extending the constant rank-one integer-module sheaf gives the
constant rank-one `R`-module sheaf. -/
noncomputable def constantRankOneSheafExtendIntegersIso
    {T : TopCat} :
    (sheafExtendIntegers R
      (Opens.grothendieckTopology T)).obj
        (constantRankOneSheaf (R := ℤ) T) ≅
      constantRankOneSheaf (R := R) T :=
  (constantSheafExtendIntegersIso R).app
      (ModuleCat.of ℤ ℤ) ≪≫
    (constantSheaf
      (Opens.grothendieckTopology T)
      (ModuleCat R)).mapIso (by
        dsimp only [extendIntegers, ModuleCat.extendScalars,
          ModuleCat.ExtendScalars.obj']
        let S :=
          (ModuleCat.restrictScalars
            (algebraMap ℤ R)).obj (ModuleCat.of R R)
        letI : SMul ℤ S := S.isModule.toSMul
        letI : Module ℤ S := S.isModule
        let eS : S ≃ₗ[R] R :=
          LinearEquiv.refl R R
        letI : IsScalarTower ℤ R S :=
          IsScalarTower.of_algebraMap_smul
            (fun z x => by
              change (algebraMap ℤ R z) • x = z • x
              exact
                (ModuleCat.restrictScalars.smul_def
                  (M := ModuleCat.of R R)
                  (algebraMap ℤ R) z x).symm)
        exact
          ((TensorProduct.AlgebraTensorModule.rid
            ℤ R S).trans eS).toModuleIso)

/-- Over a coefficient ring flat over `ℤ`, constant-source module-sheaf
Ext is ordinary cohomology of the underlying abelian sheaf. -/
noncomputable def constantBaseModuleSheafExtAddEquivUnderlyingAbH
    [Module.Flat ℤ R]
    {T : TopCat}
    (F : Sheaf
      (Opens.grothendieckTopology T)
      (ModuleCat R))
    (n : ℕ) :
    Abelian.Ext
        (constantRankOneSheaf (R := R) T)
        F n ≃+
      CategoryTheory.Sheaf.H
        ((sheafForgetZToAb
          (Opens.grothendieckTopology T)).obj
          ((sheafRestrictToIntegers R
            (Opens.grothendieckTopology T)).obj F))
        n := by
  let J := Opens.grothendieckTopology T
  let A := constantRankOneSheaf (R := ℤ) T
  letI :
      (sheafRestrictToIntegers R J).IsRightAdjoint :=
    (sheafExtendRestrictAdjunction R J).isRightAdjoint
  letI :
      (sheafRestrictToIntegers R J).IsLeftAdjoint :=
    (sheafRestrictCoextendAdjunction R J).isLeftAdjoint
  letI :
      (sheafRestrictToIntegers R J).Additive :=
    (sheafRestrictToIntegers R J).additive_of_preserves_binary_products
  letI :
      PreservesFiniteLimits (extendIntegers R) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat <|
      (RingHom.flat_algebraMap_iff.mpr inferInstance :
        (algebraMap ℤ R).Flat)
  letI :
      (sheafRestrictToIntegers R J).PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (sheafExtendRestrictAdjunction R J)
  exact
    (precompIsoAddEquiv
      (constantRankOneSheafExtendIntegersIso R) n).trans <|
    (extAddEquiv
      (sheafExtendIntegers R J)
      (sheafRestrictToIntegers R J)
      (sheafExtendRestrictAdjunction R J)
      A F n).trans <|
    (sheafForgetZToAb_extAddEquiv J A
      ((sheafRestrictToIntegers R J).obj F) n).trans <|
      (precompIsoAddEquiv
        (constantZForgetIso J) n).symm.trans <|
        (precompIsoAddEquiv
          (constantAbZULiftIso J) n).symm

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.FlatBaseChange

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.FlatBaseOpenCohomology

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ExtAdjunction
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FlatBaseChange

variable {R : Type} [CommRing R] [Module.Flat ℤ R]
variable {X : Scheme.{0}}
  [X.Over (Spec (CommRingCat.of R))]

/-- Constant-source base-linear Ext of a scheme module is ordinary
global cohomology of its underlying abelian sheaf. -/
noncomputable def constantBaseModuleSheafExtAddEquivH
    (M : X.Modules) (n : ℕ) :
    Abelian.Ext
        (constantRankOneSheaf (R := R) X)
        (moduleSheaf (k := R) M) n ≃+
      CategoryTheory.Sheaf.H M.sheaf n :=
  (constantBaseModuleSheafExtAddEquivUnderlyingAbH
    R (moduleSheaf (k := R) M) n).trans
      (postcompIsoAddEquiv
        (moduleSheafUnderlyingAbIso M) n)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.FlatBaseOpenCohomology

/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.Rationalization
import MazurTorsion.Upstream.CoherentCohomologyFinite.ExtAdjunction
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAffineCover
import MazurTorsion.Upstream.LeanPool.GrothendieckVanishing.CohomologyAPI
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Topology.Sheaves.Abelian

/-!
# Rationalized cohomology of finite coproducts

Finite coproducts in a sheaf category are biproducts.  Ext commutes with
finite biproducts in its covariant variable, and rationalization commutes
with finite products.  Hence degreewise finite-dimensional rationalized
cohomology is closed under finite coproducts.
-/


open CategoryTheory Limits TopologicalSpace TensorProduct

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

noncomputable local instance finiteCoproductCohomologyAddCommGroup
    {Z : TopCat.{0}}
    (G : Z.Sheaf AddCommGrpCat.{0}) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H G n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

noncomputable local instance extAddCommGroup
    {C : Type} [Category C] [Abelian C] [HasExt C]
    {A B : C} {n : ℕ} :
    AddCommGroup (Abelian.Ext A B n) :=
  CategoryTheory.Abelian.Ext.instAddCommGroup

/--
Rationalized module-sheaf cohomology is finite-dimensional on one side of
an isomorphism exactly when it is finite-dimensional on the other.
-/
theorem rationalized_moduleSheafH_finite_congr
    {X : AlgebraicGeometry.Scheme.{0}} {A B : X.Modules}
    (e : A ≅ B) (n : ℕ) :
    Module.Finite ℚ (ℚ ⊗[ℤ] A.sheaf.H n) ↔
      Module.Finite ℚ (ℚ ⊗[ℤ] B.sheaf.H n) := by
  let eH :
      A.sheaf.H n ≃+ B.sheaf.H n :=
    ExtAdjunction.postcompIsoAddEquiv
      ((AlgebraicGeometry.Scheme.Modules.toUnderlyingSheaf X).mapIso e)
      n
  exact
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.rationalization_finite_congr eH

/--
A finite coproduct of abelian sheaves with finite-dimensional rationalized
cohomology has finite-dimensional rationalized cohomology.
-/
theorem rationalized_sheafH_finite_coproduct
    {X : TopCat.{0}} {ι : Type} [Finite ι]
    (F : ι → TopCat.Sheaf AddCommGrpCat.{0} X)
    (n : ℕ)
    (hfinite :
      ∀ i, Module.Finite ℚ (ℚ ⊗[ℤ] (F i).H n)) :
    Module.Finite ℚ
      (ℚ ⊗[ℤ] (∐ F).H n) := by
  classical
  letI := Fintype.ofFinite ι
  letI :
      HasExt.{0}
        (TopCat.Sheaf AddCommGrpCat.{0} X) :=
    hasExt_of_enoughInjectives _
  letI :
      ∀ i, Module.Finite ℚ
        (ℚ ⊗[ℤ] (F i).H n) :=
    hfinite
  let c :
      Bicone F :=
    Bicone.ofColimitCocone
      (colimit.isColimit (Discrete.functor F))
  let hc : c.IsBilimit :=
    biconeIsBilimitOfColimitCoconeOfIsColimit
      (colimit.isColimit (Discrete.functor F))
  let constantZ :=
    (constantSheaf
      (Opens.grothendieckTopology X)
      AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of (ULift ℤ))
  let eExt :
      Abelian.Ext constantZ c.pt n ≃+
        ∀ i, Abelian.Ext constantZ (F i) n :=
    @Abelian.Ext.addEquivBiproduct
      (TopCat.Sheaf AddCommGrpCat.{0} X)
      inferInstance inferInstance inferInstance
      constantZ ι inferInstance F c hc n
  let eRat :
      ℚ ⊗[ℤ] Abelian.Ext constantZ c.pt n ≃ₗ[ℚ]
        ℚ ⊗[ℤ] (∀ i, Abelian.Ext constantZ (F i) n) :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.rationalizationMapAddEquiv eExt
  let ePi :
      ℚ ⊗[ℤ] (∀ i, Abelian.Ext constantZ (F i) n) ≃ₗ[ℚ]
        ∀ i, ℚ ⊗[ℤ] Abelian.Ext constantZ (F i) n :=
    TensorProduct.piRight ℤ ℚ ℚ
      (fun i => Abelian.Ext constantZ (F i) n)
  have htarget :
      Module.Finite ℚ
        (∀ i, ℚ ⊗[ℤ] Abelian.Ext constantZ (F i) n) := by
    infer_instance
  letI := htarget
  exact Module.Finite.equiv (eRat.trans ePi).symm

/--
The corresponding finite-coproduct result for sheaves of modules on a
scheme.  The forgetful functor to sheaves of abelian groups preserves
colimits, so the preceding sheaf-theoretic result applies.
-/
theorem rationalized_moduleSheafH_finite_coproduct
    {X : AlgebraicGeometry.Scheme.{0}} {ι : Type} [Finite ι]
    (F : ι → X.Modules)
    (n : ℕ)
    (hfinite :
      ∀ i, Module.Finite ℚ (ℚ ⊗[ℤ] (F i).sheaf.H n)) :
    Module.Finite ℚ
      (ℚ ⊗[ℤ] (∐ F).sheaf.H n) := by
  classical
  letI := Fintype.ofFinite ι
  let U :=
    AlgebraicGeometry.Scheme.Modules.toUnderlyingSheaf X
  let K : Discrete ι ⥤ X.Modules :=
    Discrete.functor F
  let hU :
      IsColimit (U.mapCocone (colimit.cocone K)) :=
    isColimitOfPreserves U (colimit.isColimit K)
  let eSheaf :
      U.obj (colimit K) ≅ colimit (K ⋙ U) :=
    hU.coconePointUniqueUpToIso
      (colimit.isColimit (K ⋙ U))
  let eSheaf' :
      (∐ F).sheaf ≅ ∐ fun i => (F i).sheaf :=
    eSheaf ≪≫
      HasColimit.isoOfNatIso
        (Discrete.compNatIsoDiscrete F U)
  let eH :
      (∐ F).sheaf.H n ≃+
        (∐ fun i => (F i).sheaf).H n :=
    ExtAdjunction.postcompIsoAddEquiv eSheaf' n
  have htarget :
      Module.Finite ℚ
        (ℚ ⊗[ℤ] (∐ fun i => (F i).sheaf).H n) :=
    rationalized_sheafH_finite_coproduct
      (fun i => (F i).sheaf) n hfinite
  exact
    (MazurTorsion.AlgebraicGeometry.CoherentCohomology.rationalization_finite_congr eH).mpr
      htarget

end MazurTorsion.AlgebraicGeometry.CoherentCohomology

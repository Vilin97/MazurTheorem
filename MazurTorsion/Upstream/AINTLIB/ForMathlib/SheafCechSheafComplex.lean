/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SheafCechSheafDifferential

/-!
# The sheaf-level Cech complex

This file packages the sheaf-level Cech terms and differentials as the native Cech complex
associated to the presheaf of restriction-pushforward factors. In particular, the relation
that two consecutive differentials compose to zero follows from the native cosimplicial
construction.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}
variable (F : Sheaf AddCommGrpCat.{u} X)

/-- The presheaf on opens whose value at `A` is the pushforward of the restriction of `F`
to `A`. -/
noncomputable def cechFactorPresheaf :
    (Opens X)ᵒᵖ ⥤ Sheaf AddCommGrpCat.{u} X where
  obj A := (restrict AddCommGrpCat A.unop.isOpenEmbedding ⋙
    pushforward AddCommGrpCat A.unop.inclusion').obj F
  map f := cechTermFactorRestriction F (leOfHom f.unop)
  map_id A := by
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    change F.obj.map _ = 𝟙 _
    rw [← F.obj.map_id]
    exact congrArg F.obj.map (Subsingleton.elim _ _)
  map_comp f g := by
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    change F.obj.map _ = F.obj.map _ ≫ F.obj.map _
    rw [← F.obj.map_comp]
    exact congrArg F.obj.map (Subsingleton.elim _ _)

variable {ι : Type u} (U : ι → Opens X)

/-- The sheaf-level Cech complex associated to the open family `U`. -/
noncomputable def cechComplex : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℕ :=
  (cechComplexFunctor U).obj (cechFactorPresheaf F)

/-- The degree-`n` object of the sheaf-level Cech complex is `cechTerm F U n`. -/
theorem cechComplex_X (n : ℕ) : (cechComplex F U).X n = cechTerm F U n := rfl

private theorem nativeCoface_eq_cechCoface (n : ℕ) (k : Fin (n + 2)) :
    ((FormalCoproduct.cosimplicialObjectFunctor
      (FormalCoproduct.mk _ U).cech).obj (cechFactorPresheaf F)).δ k =
      cechCoface F U n k := by
  rw [CosimplicialObject.δ,
    FormalCoproduct.cosimplicialObjectFunctor_obj_map,
    FormalCoproduct.cech_map]
  rfl

/-- The native differential of `cechComplex F U` is the alternating-sum map
`cechDifferential F U n`. -/
theorem cechComplex_d (n : ℕ) :
    (cechComplex F U).d n (n + 1) = cechDifferential F U n := by
  change ((FormalCoproduct.cochainComplexFunctor
    (FormalCoproduct.mk _ U).cech).obj (cechFactorPresheaf F)).d n (n + 1) = _
  rw [FormalCoproduct.cochainComplexFunctor_obj_d]
  refine (CochainComplex.of_d _ _ n).trans ?_
  rw [AlgebraicTopology.AlternatingCofaceMapComplex.objD, cechDifferential]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg (fun f => (-1 : ℤ) ^ (k : ℕ) • f)
    (nativeCoface_eq_cechCoface F U n k)

/-- Consecutive sheaf-level Cech differentials compose to zero. -/
theorem cechDifferential_comp (n : ℕ) :
    cechDifferential F U n ≫ cechDifferential F U (n + 1) = 0 := by
  rw [← cechComplex_d F U n, ← cechComplex_d F U (n + 1)]
  exact (cechComplex F U).d_comp_d n (n + 1) (n + 2)

end TopCat.Sheaf

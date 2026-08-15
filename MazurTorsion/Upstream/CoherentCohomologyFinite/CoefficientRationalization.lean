/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleSheaf
import Mathlib.Algebra.Algebra.Epi
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Rational coefficients on abelian-sheaf cohomology

An `𝒪_X`-module on a scheme over `ℚ` is, after restricting scalars, a sheaf
of rational vector spaces.  This file transports that rational action to
`Ext` in the category of abelian sheaves and proves that the rational tensor
appearing in the LeanEval statement is redundant.

This deliberately does not identify the result with `Ext` computed in the
category of sheaves of rational vector spaces.  Such an identification is a
derived extension/restriction-of-scalars theorem, which is not currently
available in Mathlib.
-/

open CategoryTheory TensorProduct

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.CoefficientRationalization

section DirectAction

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

noncomputable abbrev UAb : Sheaf J (ModuleCat.{u} ℚ) ⥤ Sheaf J AddCommGrpCat.{u} :=
  sheafCompose J (forget₂ (ModuleCat.{u} ℚ) AddCommGrpCat.{u})

/-- Objectwise scalar multiplication as an endomorphism of a sheaf of
rational vector spaces. -/
noncomputable def scalarHom (F : Sheaf J (ModuleCat.{u} ℚ)) (q : ℚ) :
    F ⟶ F :=
  ⟨{ app := fun U => q • 𝟙 (F.obj.obj U)
     naturality := by
       intro U V i
       ext x
       simp }⟩

noncomputable def scalarEnd (F : Sheaf J (ModuleCat.{u} ℚ)) (q : ℚ) :
    (UAb J).obj F ⟶ (UAb J).obj F :=
  (UAb J).map (scalarHom J F q)

@[simp]
lemma scalarEnd_zero (F : Sheaf J (ModuleCat.{u} ℚ)) :
    scalarEnd J F 0 = 0 := by
  ext U x
  change (0 : ℚ) • (show F.obj.obj U from x) = 0
  exact zero_smul ℚ (show F.obj.obj U from x)

@[simp]
lemma scalarEnd_one (F : Sheaf J (ModuleCat.{u} ℚ)) :
    scalarEnd J F 1 = 𝟙 _ := by
  ext U x
  change (1 : ℚ) • (show F.obj.obj U from x) =
    (show F.obj.obj U from x)
  exact one_smul ℚ (show F.obj.obj U from x)

@[simp]
lemma scalarEnd_add (F : Sheaf J (ModuleCat.{u} ℚ)) (q r : ℚ) :
    scalarEnd J F (q + r) = scalarEnd J F q + scalarEnd J F r := by
  ext U x
  change (q + r) • (show F.obj.obj U from x) =
    q • (show F.obj.obj U from x) + r • (show F.obj.obj U from x)
  exact add_smul q r (show F.obj.obj U from x)

@[simp]
lemma scalarEnd_mul (F : Sheaf J (ModuleCat.{u} ℚ)) (q r : ℚ) :
    scalarEnd J F (q * r) = scalarEnd J F r ≫ scalarEnd J F q := by
  ext U x
  change (q * r) • (show F.obj.obj U from x) =
    q • (r • (show F.obj.obj U from x))
  exact mul_smul q r (show F.obj.obj U from x)

variable [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
variable {X : Sheaf J AddCommGrpCat.{u}} (F : Sheaf J (ModuleCat.{u} ℚ)) (n : ℕ)

noncomputable instance rationalExtSMul :
    SMul ℚ (Abelian.Ext X ((UAb J).obj F) n) where
  smul q x := x.comp (Abelian.Ext.mk₀ (scalarEnd J F q)) (add_zero n)

lemma rationalExt_smul_def (q : ℚ) (x : Abelian.Ext X ((UAb J).obj F) n) :
    q • x = x.comp (Abelian.Ext.mk₀ (scalarEnd J F q)) (add_zero n) :=
  rfl

noncomputable instance rationalExtModule :
    Module ℚ (Abelian.Ext X ((UAb J).obj F) n) where
  one_smul x := by simp [rationalExt_smul_def]
  mul_smul q r x := by
    simp only [rationalExt_smul_def, scalarEnd_mul]
    rw [← Abelian.Ext.mk₀_comp_mk₀]
    exact
      (Abelian.Ext.comp_assoc x
        (Abelian.Ext.mk₀ (scalarEnd J F r))
        (Abelian.Ext.mk₀ (scalarEnd J F q))
        (add_zero n) (zero_add 0) (add_zero n)).symm
  smul_zero q := by simp [rationalExt_smul_def]
  smul_add q x y := by simp [rationalExt_smul_def, Abelian.Ext.add_comp]
  add_smul q r x := by
    simp [rationalExt_smul_def, Abelian.Ext.mk₀_add, Abelian.Ext.comp_add]
  zero_smul x := by simp [rationalExt_smul_def]

/--
The rationalization in the LeanEval carrier is redundant once the target
sheaf is known to come from a sheaf of rational vector spaces.
-/
noncomputable def rationalizationLinearEquiv :
    ℚ ⊗[ℤ] Abelian.Ext X ((UAb J).obj F) n ≃ₗ[ℚ]
      Abelian.Ext X ((UAb J).obj F) n :=
  TensorProduct.lid' ℤ ℚ _

theorem rationalization_moduleFinite
    [Module.Finite ℚ (Abelian.Ext X ((UAb J).obj F) n)] :
    Module.Finite ℚ (ℚ ⊗[ℤ] Abelian.Ext X ((UAb J).obj F) n) :=
  Module.Finite.equiv (rationalizationLinearEquiv J F n).symm

end DirectAction

namespace Geometric

open _root_.AlgebraicGeometry Opposite TopologicalSpace

variable {X : Scheme.{0}} [X.Over (Spec (CommRingCat.of ℚ))]

noncomputable local instance geometricHasExt :
    HasExt.{0}
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) :=
  hasExt_of_enoughInjectives _

noncomputable local instance geometricCohomologyAddCommGroup
    (M : X.Modules) (n : ℕ) : AddCommGroup (M.sheaf.H n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

noncomputable def baseAlgebraMap (U : X.Opens) : ℚ →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv ≫
    (X ↘ Spec (CommRingCat.of ℚ)).appTop ≫
    X.presheaf.map (homOfLE le_top).op).hom

lemma baseAlgebraMap_naturality {U V : X.Opensᵒᵖ} (i : U ⟶ V) :
    ((X.presheaf.map i).hom).comp (baseAlgebraMap U.unop) =
      baseAlgebraMap V.unop := by
  rw [baseAlgebraMap, baseAlgebraMap, ← CommRingCat.hom_comp]
  congr 1
  simp only [Category.assoc, ← X.presheaf.map_comp]
  congr 1

lemma baseAlgebraMap_apply_res {U V : X.Opensᵒᵖ} (i : U ⟶ V) (r : ℚ) :
    (X.presheaf.map i).hom (baseAlgebraMap U.unop r) =
      baseAlgebraMap V.unop r :=
  DFunLike.congr_fun (baseAlgebraMap_naturality i) r

@[reducible] noncomputable def sectionsModule (M : X.Modules) (U : X.Opens) :
    Module ℚ Γ(M, U) :=
  Module.compHom _ (baseAlgebraMap U)

attribute [local instance] sectionsModule

private noncomputable def smulSection (M : X.Modules) (W : X.Opens)
    (s : Γ(X, W)) (z : Γ(M, W)) : Γ(M, W) :=
  s • z

noncomputable def modulePresheaf (M : X.Modules) : X.Opensᵒᵖ ⥤ ModuleCat.{0} ℚ where
  obj U := ModuleCat.of ℚ Γ(M, U.unop)
  map {U V} i := ModuleCat.ofHom
    { toFun := M.presheaf.map i
      map_add' := map_add _
      map_smul' := fun r x => by
        change M.presheaf.map i ((baseAlgebraMap U.unop r) • x) =
          smulSection M V.unop (baseAlgebraMap V.unop r) (M.presheaf.map i x)
        exact (Scheme.Modules.map_smul M i.unop (baseAlgebraMap U.unop r) x).trans
          (congrArg
            (fun (s : Γ(X, V.unop)) => smulSection M V.unop s (M.presheaf.map i x))
            (baseAlgebraMap_apply_res i r)) }
  map_id U := by
    ext x
    exact congrFun (congrArg (fun (φ : M.presheaf.obj U ⟶ M.presheaf.obj U) =>
      (ConcreteCategory.hom φ : _ → _)) (M.presheaf.map_id U)) x
  map_comp {U V W} f g := by
    ext x
    exact congrFun (congrArg (fun (φ : M.presheaf.obj U ⟶ M.presheaf.obj W) =>
      (ConcreteCategory.hom φ : _ → _)) (M.presheaf.map_comp f g)) x

lemma modulePresheaf_isSheaf (M : X.Modules) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (modulePresheaf M) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _
    (CategoryTheory.forget (ModuleCat.{0} ℚ))]
  convert (Presheaf.isSheaf_iff_isSheaf_forget _ _
    (CategoryTheory.forget AddCommGrpCat.{0})).mp (Scheme.Modules.isSheaf M) using 1
  all_goals rfl

noncomputable def moduleSheaf (M : X.Modules) :
    Sheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ) :=
  ⟨modulePresheaf M, modulePresheaf_isSheaf M⟩

noncomputable def moduleSheaf_forgetCompare (M : X.Modules) :
    (UAb (Opens.grothendieckTopology X)).obj (moduleSheaf M) ≅ M.sheaf :=
  Iso.refl _

@[reducible] noncomputable def cohomologyModule (M : X.Modules) (n : ℕ) :
    Module ℚ (M.sheaf.H n) :=
  rationalExtModule (Opens.grothendieckTopology X) (moduleSheaf M) n

noncomputable def cohomologyRationalizationLinearEquiv (M : X.Modules) (n : ℕ) :
    letI := cohomologyModule M n
    ℚ ⊗[ℤ] M.sheaf.H n ≃ₗ[ℚ] M.sheaf.H n := by
  letI := cohomologyModule M n
  exact rationalizationLinearEquiv
    (Opens.grothendieckTopology X) (moduleSheaf M) n

theorem rationalizedCohomology_moduleFinite (M : X.Modules) (n : ℕ)
    [letI := cohomologyModule M n; Module.Finite ℚ (M.sheaf.H n)] :
    Module.Finite ℚ (ℚ ⊗[ℤ] M.sheaf.H n) := by
  letI := cohomologyModule M n
  exact Module.Finite.equiv (cohomologyRationalizationLinearEquiv M n).symm

end Geometric

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.CoefficientRationalization

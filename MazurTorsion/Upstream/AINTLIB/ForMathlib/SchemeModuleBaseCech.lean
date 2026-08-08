/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Category.ModuleCat.Products
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleBaseCechBasic
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleSheaf

/-!
# Base-linear Cech complexes of scheme modules

Retain the module structure over the global functions on the base in the
native Cech complex of a scheme module, and compare its underlying additive
complex with the existing sheaf-valued Cech complex.
-/

open AlgebraicTopology CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- A degree of the base-linear Cech complex is the concrete dependent
product of its intersection-section factors. This declaration is moved here
from AINTLIB's `SchemeModuleBaseCechFlat` so the comparison core remains
independent of its flatness dependency tail. -/
noncomputable def baseCechXIsoPi {X S : Scheme.{u}} (π : X ⟶ S)
    (M : X.Modules) {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    (baseCechComplex π M U).X n ≅
      ModuleCat.of Γ(S, (⊤ : S.Opens))
        (∀ i : Fin (n + 1) → ι, baseCechFactor π M U n i) :=
  ModuleCat.piIsoPi _

private abbrev moduleForget (R : Type u) [Ring R] :=
  forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}

/-- Forget the module structure over the global functions on a scheme. -/
abbrev baseModuleForget (S : Scheme.{u}) :=
  moduleForget Γ(S, (⊤ : S.Opens))

/-- Forgetting the base module structure recovers the underlying additive
presheaf of the scheme module. -/
private noncomputable def baseModulePresheafForgetIso {X S : Scheme.{u}}
    (π : X ⟶ S) (M : X.Modules) :
    baseModulePresheaf π M ⋙ baseModuleForget S ≅ M.sheaf.obj :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

private def discreteModuleForgetIso
    (R : Type u) [Ring R] {I : Type u} (P : I → ModuleCat.{u} R) :
    Discrete.functor P ⋙ moduleForget R ≅
      Discrete.functor (fun i => (moduleForget R).obj (P i)) :=
  Discrete.natIso fun x => eqToIso (show
    (Discrete.functor P ⋙ moduleForget R).obj x =
      (Discrete.functor fun i => (moduleForget R).obj (P i)).obj x
    from rfl)

private theorem discreteModuleForgetIso_comp_hom_app
    (R : Type u) [Ring R] {I : Type u} (P : I → ModuleCat.{u} R)
    (i : I) :
    (moduleForget R).map (Pi.π P i) ≫
        (discreteModuleForgetIso R P).hom.app (Discrete.mk i) =
      (moduleForget R).map (Pi.π P i) := by
  rfl

/-- Forgetting the module structure commutes with products. -/
private noncomputable def modulePiForgetIso
    (R : Type u) [Ring R] {I : Type u} (P : I → ModuleCat.{u} R) :
    (moduleForget R).obj (∏ᶜ P) ≅
      ∏ᶜ fun i => (moduleForget R).obj (P i) :=
  preservesLimitIso (moduleForget R) (Discrete.functor P) ≪≫
    HasLimit.isoOfNatIso (discreteModuleForgetIso R P)

/-- The comparison from a forgotten module product to the additive product
commutes with every product projection. -/
@[reassoc]
private theorem modulePiForgetIso_hom_π
    (R : Type u) [Ring R] {I : Type u}
    (P : I → ModuleCat.{u} R) (i : I) :
    (modulePiForgetIso R P).hom ≫
        Pi.π (fun i => (moduleForget R).obj (P i)) i =
      (moduleForget R).map
        (Pi.π P i) := by
  dsimp only [modulePiForgetIso]
  rw [Iso.trans_hom]
  change (preservesLimitIso (moduleForget R) (Discrete.functor P)).hom ≫
      ((HasLimit.isoOfNatIso (discreteModuleForgetIso R P)).hom ≫
        limit.π (Discrete.functor fun i => (moduleForget R).obj (P i))
          (Discrete.mk i)) = _
  rw [
    HasLimit.isoOfNatIso_hom_π
      (discreteModuleForgetIso R P) (Discrete.mk i)]
  rw [preservesLimitIso_hom_π_assoc]
  exact discreteModuleForgetIso_comp_hom_app R P i

private theorem modulePiForgetIso_naturality
    (R : Type u) [Ring R] {I J : Type u}
    (P : I → ModuleCat.{u} R) (Q : J → ModuleCat.{u} R)
    (f : J → I) (φ : ∀ j, P (f j) ⟶ Q j) :
    (moduleForget R).map
          (Pi.lift fun j => Pi.π P (f j) ≫ φ j) ≫
        (modulePiForgetIso R Q).hom =
      (modulePiForgetIso R P).hom ≫
        Pi.lift (fun j =>
          Pi.π (fun i => (moduleForget R).obj (P i)) (f j) ≫
            (moduleForget R).map (φ j)) := by
  apply Pi.hom_ext
  intro j
  simp only [Category.assoc, modulePiForgetIso_hom_π,
    Pi.lift_π, ← Functor.map_comp]
  rw [modulePiForgetIso_hom_π_assoc, ← Functor.map_comp]

private noncomputable def evalOpForgetIsoApp
    {C : Type u} [Category.{u} C] (R : Type u) [Ring R]
    (P : Cᵒᵖ ⥤ ModuleCat.{u} R) (V : (FormalCoproduct C)ᵒᵖ) :
    (((FormalCoproduct.evalOp C (ModuleCat.{u} R)).obj P ⋙
        moduleForget R).obj V) ≅
      (((FormalCoproduct.evalOp C AddCommGrpCat.{u}).obj
        (P ⋙ moduleForget R)).obj V) := by
  change (moduleForget R).obj
      (∏ᶜ fun i : V.unop.I => P.obj (op (V.unop.obj i))) ≅
    ∏ᶜ fun i : V.unop.I =>
      (moduleForget R).obj (P.obj (op (V.unop.obj i)))
  exact modulePiForgetIso R fun i => P.obj (op (V.unop.obj i))

/-- Evaluation of a module-valued presheaf on a formal coproduct commutes with
forgetting to additive groups. -/
private noncomputable def evalOpForgetIso
    {C : Type u} [Category.{u} C] (R : Type u) [Ring R]
    (P : Cᵒᵖ ⥤ ModuleCat.{u} R) :
    (FormalCoproduct.evalOp C (ModuleCat.{u} R)).obj P ⋙
        moduleForget R ≅
      (FormalCoproduct.evalOp C AddCommGrpCat.{u}).obj
        (P ⋙ moduleForget R) :=
  NatIso.ofComponents (evalOpForgetIsoApp R P) (by
        intro V W f
        exact modulePiForgetIso_naturality R
          (fun i : V.unop.I => P.obj (op (V.unop.obj i)))
          (fun i : W.unop.I => P.obj (op (W.unop.obj i)))
          f.unop.f (fun i => P.map (f.unop.φ i).op))

/-- The evaluation comparison from a forgotten module product to the additive
product commutes with every projection. -/
@[reassoc]
private theorem evalOpForgetIso_hom_π
    {C : Type u} [Category.{u} C] (R : Type u) [Ring R]
    (P : Cᵒᵖ ⥤ ModuleCat.{u} R)
    (V : (FormalCoproduct C)ᵒᵖ) (i : V.unop.I) :
    (evalOpForgetIso R P).hom.app V ≫
        Pi.π (fun j => (moduleForget R).obj
          (P.obj (op (V.unop.obj j)))) i =
      (moduleForget R).map
        (Pi.π (fun j => P.obj (op (V.unop.obj j))) i) :=
  modulePiForgetIso_hom_π R
    (fun j => P.obj (op (V.unop.obj j))) i

/-- Forgetting the base module structure degreewise in the Cech cosimplicial
object recovers the cosimplicial object of the underlying sheaf. -/
noncomputable def baseCechCosimplicialIso
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) :
    ((FormalCoproduct.cosimplicialObjectFunctor
      (FormalCoproduct.mk _ U).cech).obj (baseModulePresheaf π M) ⋙
        baseModuleForget S) ≅
      (FormalCoproduct.cosimplicialObjectFunctor
        (FormalCoproduct.mk _ U).cech).obj M.sheaf.obj :=
  Functor.isoWhiskerLeft (FormalCoproduct.mk _ U).cech.rightOp
      (evalOpForgetIso Γ(S, (⊤ : S.Opens)) (baseModulePresheaf π M)) ≪≫
    Functor.isoWhiskerLeft (FormalCoproduct.mk _ U).cech.rightOp
      ((FormalCoproduct.evalOp X.Opens AddCommGrpCat.{u}).mapIso
        (baseModulePresheafForgetIso π M))

private theorem baseCechComplex_d_succ
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (i : ℕ) :
    (baseCechComplex π M U).d i (i + 1) =
      AlternatingCofaceMapComplex.objD
        ((FormalCoproduct.cosimplicialObjectFunctor
          (FormalCoproduct.mk _ U).cech).obj (baseModulePresheaf π M)) i := by
  change ((FormalCoproduct.cochainComplexFunctor
    (FormalCoproduct.mk _ U).cech).obj (baseModulePresheaf π M)).d
      i (i + 1) = _
  rw [FormalCoproduct.cochainComplexFunctor_obj_d]
  exact (CochainComplex.of_d _ _ i).trans rfl

private theorem cechComplex_d_succ
    {X : Scheme.{u}} (M : X.Modules) {ι : Type u}
    (U : ι → X.Opens) (i : ℕ) :
    ((cechComplexFunctor U).obj M.sheaf.obj).d i (i + 1) =
      AlternatingCofaceMapComplex.objD
        ((FormalCoproduct.cosimplicialObjectFunctor
          (FormalCoproduct.mk _ U).cech).obj M.sheaf.obj) i := by
  change ((FormalCoproduct.cochainComplexFunctor
    (FormalCoproduct.mk _ U).cech).obj M.sheaf.obj).d i (i + 1) = _
  rw [FormalCoproduct.cochainComplexFunctor_obj_d]
  exact (CochainComplex.of_d _ _ i).trans rfl

private theorem baseCechCosimplicialIso_comm_d
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (i : ℕ) :
    (baseCechCosimplicialIso π M U).hom.app (SimplexCategory.mk i) ≫
        AlternatingCofaceMapComplex.objD
          ((FormalCoproduct.cosimplicialObjectFunctor
            (FormalCoproduct.mk _ U).cech).obj M.sheaf.obj) i =
      (baseModuleForget S).map
          (AlternatingCofaceMapComplex.objD
            ((FormalCoproduct.cosimplicialObjectFunctor
              (FormalCoproduct.mk _ U).cech).obj
                (baseModulePresheaf π M)) i) ≫
        (baseCechCosimplicialIso π M U).hom.app
          (SimplexCategory.mk (i + 1)) := by
  simp only [AlternatingCofaceMapComplex.objD, Functor.map_sum,
    Functor.map_zsmul, Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg ((-1 : ℤ) ^ (k : ℕ) • ·)
    ((baseCechCosimplicialIso π M U).hom.naturality
      (SimplexCategory.δ k)).symm

/-- Forgetting the base module structure on `baseCechComplex` gives the native
additive Cech complex of the underlying sheaf. -/
noncomputable def baseCechComplexForgetIso
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) :
    (((baseModuleForget S).mapHomologicalComplex (.up ℕ)).obj
      (baseCechComplex π M U)) ≅
        (cechComplexFunctor U).obj M.sheaf.obj :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (baseCechCosimplicialIso π M U).app (SimplexCategory.mk n)) (by
      intro i j hij
      simp only [ComplexShape.up_Rel] at hij
      subst j
      rw [Functor.mapHomologicalComplex_obj_d]
      rw [baseCechComplex_d_succ, cechComplex_d_succ]
      exact baseCechCosimplicialIso_comm_d π M U i)

@[simp]
theorem baseCechComplexForgetIso_hom_f
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    (baseCechComplexForgetIso π M U).hom.f n =
      (baseCechCosimplicialIso π M U).hom.app (SimplexCategory.mk n) :=
  rfl

end

end AlgebraicGeometry.Scheme.Modules

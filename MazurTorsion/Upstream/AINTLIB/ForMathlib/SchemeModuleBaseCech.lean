/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Vasily Ilin
-/
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Homology.Linear
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
private noncomputable def baseCechCosimplicialIso
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

@[reassoc]
private theorem baseCechCosimplicialIso_hom_π
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (q : SimplexCategory)
    (i : (unop ((FormalCoproduct.mk _ U).cech.rightOp.obj q)).I) :
    (baseCechCosimplicialIso π M U).hom.app q ≫
        Pi.π (fun j => M.presheaf.obj
          (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj q)).obj j))) i =
      (baseModuleForget S).map
        (Pi.π (fun j => (baseModulePresheaf π M).obj
          (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj q)).obj j))) i) := by
  change
    ((Functor.isoWhiskerLeft (FormalCoproduct.mk _ U).cech.rightOp
          (evalOpForgetIso Γ(S, (⊤ : S.Opens))
            (baseModulePresheaf π M))).hom.app q ≫
        (Functor.isoWhiskerLeft (FormalCoproduct.mk _ U).cech.rightOp
          ((FormalCoproduct.evalOp X.Opens AddCommGrpCat.{u}).mapIso
            (baseModulePresheafForgetIso π M))).hom.app q) ≫ _ = _
  erw [Category.assoc]
  have hsecond :
      (Functor.isoWhiskerLeft (FormalCoproduct.mk _ U).cech.rightOp
          ((FormalCoproduct.evalOp X.Opens AddCommGrpCat.{u}).mapIso
            (baseModulePresheafForgetIso π M))).hom.app q ≫
        Pi.π (fun j => M.presheaf.obj
          (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj q)).obj j))) i =
      Pi.π (fun j =>
        (baseModulePresheaf π M ⋙ baseModuleForget S).obj
          (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj q)).obj j))) i := by
    change Limits.Pi.map (fun j =>
        (baseModulePresheafForgetIso π M).hom.app
          (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj q)).obj j))) ≫ _ = _
    erw [Limits.Pi.map_π]
    rfl
  erw [hsecond]
  change (evalOpForgetIso Γ(S, (⊤ : S.Opens))
      (baseModulePresheaf π M)).hom.app
        ((FormalCoproduct.mk _ U).cech.rightOp.obj q) ≫ _ = _
  exact evalOpForgetIso_hom_π Γ(S, (⊤ : S.Opens))
    (baseModulePresheaf π M)
    ((FormalCoproduct.mk _ U).cech.rightOp.obj q) i

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
private theorem baseCechComplexForgetIso_hom_f
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ) :
    (baseCechComplexForgetIso π M U).hom.f n =
      (baseCechCosimplicialIso π M U).hom.app (SimplexCategory.mk n) :=
  rfl

@[reassoc]
private theorem baseCechComplexFunctor_map_f_π
    {X S : Scheme.{u}} (π : X ⟶ S) {M N : X.Modules} (f : M ⟶ N)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (i : (unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
      (SimplexCategory.mk n))).I) :
    ((baseCechComplexFunctor π U).map f).f n ≫
        Pi.π (fun j => ((baseModulePresheafFunctor π).obj N).obj
          (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
            (SimplexCategory.mk n))).obj j))) i =
      Pi.π (fun j => ((baseModulePresheafFunctor π).obj M).obj
          (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
            (SimplexCategory.mk n))).obj j))) i ≫
        ((baseModulePresheafFunctor π).map f).app
          (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
            (SimplexCategory.mk n))).obj i)) := by
  change Limits.Pi.map (fun j => ((baseModulePresheafFunctor π).map f).app
      (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
        (SimplexCategory.mk n))).obj j))) ≫ _ = _
  exact Limits.Pi.map_π _ i

/-- A coefficient endomorphism that is scalar multiplication on every
base-linear section module induces scalar multiplication on the entire Cech
complex. -/
theorem baseCechComplexFunctor_map_eq_smul_id
    {X S : Scheme.{u}} (π : X ⟶ S) (M : X.Modules) (f : M ⟶ M)
    {ι : Type u} (U : ι → X.Opens) (r : Γ(S, ⊤))
    (h : ∀ V, ((baseModulePresheafFunctor π).map f).app V =
      r • 𝟙 (((baseModulePresheafFunctor π).obj M).obj V)) :
    ((baseCechComplexFunctor π U).map f :
      baseCechComplex π M U ⟶ baseCechComplex π M U) =
      r • 𝟙 (baseCechComplex π M U) := by
  let K := (cechComplexFunctor U).obj
    ((baseModulePresheafFunctor π).obj M)
  change (cechComplexFunctor U).map
      ((baseModulePresheafFunctor π).map f) = r • 𝟙 K
  apply HomologicalComplex.Hom.ext
  funext n
  let P := fun j : Fin (n + 1) → ι => baseCechFactor π M U n j
  let e : K.X n ≅ ModuleCat.of Γ(S, ⊤) (∀ j, P j) :=
    baseCechXIsoPi π M U n
  apply (cancel_mono e.hom).1
  ext x
  rename_i i
  let p := Pi.π P i
  let proj := ModuleCat.ofHom
    (LinearMap.proj i : (∀ j, P j) →ₗ[Γ(S, ⊤)] P i)
  have he : e.hom ≫ proj = p := by
    exact ModuleCat.piIsoPi_hom_ker_subtype P i
  have hi := baseCechComplexFunctor_map_f_π π f U n i
  change ((cechComplexFunctor U).map
      ((baseModulePresheafFunctor π).map f)).f n ≫ p =
    p ≫ ((baseModulePresheafFunctor π).map f).app _ at hi
  rw [h] at hi
  change _ = p ≫ (r • 𝟙 (P i)) at hi
  erw [← he] at hi
  have hs : (r • 𝟙 (K.X n)) ≫ e.hom = r • e.hom := by
    simpa only [Category.id_comp] using
      Linear.smul_comp (K.X n) (K.X n) _ r (𝟙 (K.X n)) e.hom
  have hcat :
      ((((cechComplexFunctor U).map
          ((baseModulePresheafFunctor π).map f)).f n ≫ e.hom) ≫ proj) =
        (((r • 𝟙 K).f n ≫ e.hom) ≫ proj) := by
    calc
      _ = ((cechComplexFunctor U).map
            ((baseModulePresheafFunctor π).map f)).f n ≫
          (e.hom ≫ proj) := Category.assoc _ _ _
      _ = ((cechComplexFunctor U).map
            ((baseModulePresheafFunctor π).map f)).f n ≫
          (e.hom ≫ proj) := rfl
      _ = (e.hom ≫ proj) ≫ (r • 𝟙 (P i)) := hi
      _ = e.hom ≫ (proj ≫ (r • 𝟙 (P i))) :=
        Category.assoc _ _ _
      _ = e.hom ≫ (r • proj) := by
        rw [Linear.comp_smul, Category.comp_id]
      _ = r • (e.hom ≫ proj) := by rw [Linear.comp_smul]
      _ = (r • e.hom) ≫ proj := by rw [Linear.smul_comp]
      _ = ((r • 𝟙 (K.X n)) ≫ e.hom) ≫ proj := by
        exact congrArg (fun q => q ≫ proj) hs.symm
      _ = (((r • 𝟙 K).f n ≫ e.hom) ≫ proj) := rfl
  exact ConcreteCategory.congr_hom hcat x

@[reassoc]
private theorem cechComplexFunctor_map_f_π
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    {ι : Type u} (U : ι → X.Opens) (n : ℕ)
    (i : (unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
      (SimplexCategory.mk n))).I) :
    ((cechComplexFunctor U).map f.sheafHom.hom).f n ≫
        Pi.π (fun j => N.presheaf.obj
          (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
            (SimplexCategory.mk n))).obj j))) i =
      Pi.π (fun j => M.presheaf.obj
          (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
            (SimplexCategory.mk n))).obj j))) i ≫
        f.sheafHom.hom.app
          (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
            (SimplexCategory.mk n))).obj i)) := by
  change Limits.Pi.map (fun j => f.sheafHom.hom.app
      (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
        (SimplexCategory.mk n))).obj j))) ≫ _ = _
  exact Limits.Pi.map_π _ i

/-- The additive comparison obtained by forgetting the base action is
natural in the coefficient module. -/
theorem baseCechComplexForgetIso_naturality
    {X S : Scheme.{u}} (π : X ⟶ S) {M N : X.Modules} (f : M ⟶ N)
    {ι : Type u} (U : ι → X.Opens) :
    (((baseModuleForget S).mapHomologicalComplex (.up ℕ)).map
          ((baseCechComplexFunctor π U).map f)) ≫
        (baseCechComplexForgetIso π N U).hom =
      (baseCechComplexForgetIso π M U).hom ≫
        (cechComplexFunctor U).map f.sheafHom.hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  erw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f,
    baseCechComplexForgetIso_hom_f,
    baseCechComplexForgetIso_hom_f]
  apply Pi.hom_ext
  intro i
  change
    ((baseModuleForget S).map
          (((baseCechComplexFunctor π U).map f).f n) ≫
        (baseCechCosimplicialIso π N U).hom.app
          (SimplexCategory.mk n)) ≫
      Pi.π (fun j => N.presheaf.obj
        (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
          (SimplexCategory.mk n))).obj j))) i =
    ((baseCechCosimplicialIso π M U).hom.app
          (SimplexCategory.mk n) ≫
        ((cechComplexFunctor U).map f.sheafHom.hom).f n) ≫
      Pi.π (fun j => N.presheaf.obj
        (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
          (SimplexCategory.mk n))).obj j))) i
  let V := op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
    (SimplexCategory.mk n))).obj i)
  let PM := fun j => ((baseModulePresheafFunctor π).obj M).obj
    (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
      (SimplexCategory.mk n))).obj j))
  let PN := fun j => ((baseModulePresheafFunctor π).obj N).obj
    (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
      (SimplexCategory.mk n))).obj j))
  let QM := fun j => M.presheaf.obj
    (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
      (SimplexCategory.mk n))).obj j))
  let QN := fun j => N.presheaf.obj
    (op ((unop ((FormalCoproduct.mk _ U).cech.rightOp.obj
      (SimplexCategory.mk n))).obj j))
  let a := ((baseCechComplexFunctor π U).map f).f n
  let bM := (baseCechCosimplicialIso π M U).hom.app
    (SimplexCategory.mk n)
  let bN := (baseCechCosimplicialIso π N U).hom.app
    (SimplexCategory.mk n)
  let c := ((cechComplexFunctor U).map f.sheafHom.hom).f n
  let pM := Pi.π PM i
  let pN := Pi.π PN i
  let qM := Pi.π QM i
  let qN := Pi.π QN i
  let d := ((baseModulePresheafFunctor π).map f).app V
  let d' := f.sheafHom.hom.app V
  have hbM : bM ≫ qM = (baseModuleForget S).map pM := by
    exact baseCechCosimplicialIso_hom_π π M U _ i
  have hbN : bN ≫ qN = (baseModuleForget S).map pN := by
    exact baseCechCosimplicialIso_hom_π π N U _ i
  have ha : a ≫ pN = pM ≫ d := by
    exact baseCechComplexFunctor_map_f_π π f U n i
  have hc : c ≫ qN = qM ≫ d' := by
    exact cechComplexFunctor_map_f_π f U n i
  have hd : (baseModuleForget S).map d = d' := rfl
  have hleft : ((baseModuleForget S).map a ≫ bN) ≫ qN =
      (baseModuleForget S).map a ≫ (baseModuleForget S).map pN :=
    (Category.assoc _ _ _).trans
      (congrArg (fun q => (baseModuleForget S).map a ≫ q) hbN)
  have hmiddle :
      (baseModuleForget S).map a ≫ (baseModuleForget S).map pN =
        (baseModuleForget S).map pM ≫ (baseModuleForget S).map d :=
    ((baseModuleForget S).map_comp a pN).symm.trans
      ((congrArg (baseModuleForget S).map ha).trans
        ((baseModuleForget S).map_comp pM d))
  have hright :
      (baseModuleForget S).map pM ≫ (baseModuleForget S).map d =
        (bM ≫ c) ≫ qN :=
    (congrArg (fun q => (baseModuleForget S).map pM ≫ q) hd).trans
      ((congrArg (fun q => q ≫ d') hbM.symm).trans
        ((Category.assoc bM qM d').trans
          ((congrArg (fun q => bM ≫ q) hc.symm).trans
            (Category.assoc bM c qN).symm)))
  change ((baseModuleForget S).map a ≫ bN) ≫ qN =
    (bM ≫ c) ≫ qN
  exact hleft.trans (hmiddle.trans hright)

end

end AlgebraicGeometry.Scheme.Modules

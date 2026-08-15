/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleSheaf

/-!
# A scheme module as a sheaf of modules over its base ring

If `X` is a scheme over `Spec k`, every section module of an
`𝒪_X`-module carries a compatible `k`-module structure.  This file packages
those structures as a `ModuleCat k`-valued sheaf.

Unlike the rational-coefficient wrapper in
`CoefficientRationalization.lean`, this construction is uniform in the
commutative base ring.  It is the coefficient object needed for relative
projective-space Čech calculations.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing

variable {k : Type u} [CommRing k]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]

/-- The structural `k`-algebra map on an open of a scheme over `Spec k`. -/
noncomputable def algebraMapOnOpen (U : X.Opens) : k →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    (X ↘ Spec (CommRingCat.of k)).appTop ≫
    X.presheaf.map (homOfLE le_top).op).hom

lemma algebraMapOnOpen_naturality {U V : X.Opensᵒᵖ} (i : U ⟶ V) :
    ((X.presheaf.map i).hom).comp (algebraMapOnOpen (k := k) U.unop) =
      algebraMapOnOpen (k := k) V.unop := by
  rw [algebraMapOnOpen, algebraMapOnOpen, ← CommRingCat.hom_comp]
  congr 1
  simp only [Category.assoc, ← X.presheaf.map_comp]
  congr 1

lemma algebraMapOnOpen_apply_restriction
    {U V : X.Opensᵒᵖ} (i : U ⟶ V) (r : k) :
    (X.presheaf.map i).hom (algebraMapOnOpen (k := k) U.unop r) =
      algebraMapOnOpen (k := k) V.unop r :=
  DFunLike.congr_fun (algebraMapOnOpen_naturality (k := k) i) r

/-- The base-ring module structure on sections of a scheme module. -/
@[reducible]
noncomputable def sectionsModule (M : X.Modules) (U : X.Opens) :
    Module k Γ(M, U) :=
  Module.compHom _ (algebraMapOnOpen (k := k) U)

attribute [local instance] sectionsModule

private noncomputable def smulSection
    (M : X.Modules) (U : X.Opens)
    (s : Γ(X, U)) (x : Γ(M, U)) : Γ(M, U) :=
  s • x

/-- The presheaf of `k`-modules underlying a scheme module over `Spec k`. -/
noncomputable def modulePresheaf (M : X.Modules) :
    X.Opensᵒᵖ ⥤ ModuleCat.{u} k where
  obj U := ModuleCat.of k Γ(M, U.unop)
  map {U V} i := ModuleCat.ofHom
    { toFun := M.presheaf.map i
      map_add' := map_add _
      map_smul' := fun r x => by
        change
          M.presheaf.map i ((algebraMapOnOpen (k := k) U.unop r) • x) =
            smulSection M V.unop (algebraMapOnOpen (k := k) V.unop r)
              (M.presheaf.map i x)
        exact
          (Scheme.Modules.map_smul M i.unop
            (algebraMapOnOpen (k := k) U.unop r) x).trans
            (congrArg
              (fun s : Γ(X, V.unop) =>
                smulSection M V.unop s (M.presheaf.map i x))
              (algebraMapOnOpen_apply_restriction (k := k) i r)) }
  map_id U := by
    ext x
    exact congrFun
      (congrArg
        (fun φ : M.presheaf.obj U ⟶ M.presheaf.obj U =>
          (ConcreteCategory.hom φ : _ → _))
        (M.presheaf.map_id U)) x
  map_comp {U V W} f g := by
    ext x
    exact congrFun
      (congrArg
        (fun φ : M.presheaf.obj U ⟶ M.presheaf.obj W =>
          (ConcreteCategory.hom φ : _ → _))
        (M.presheaf.map_comp f g)) x

lemma modulePresheaf_isSheaf (M : X.Modules) :
    Presheaf.IsSheaf
      (Opens.grothendieckTopology X) (modulePresheaf (k := k) M) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _
    (CategoryTheory.forget (ModuleCat.{u} k))]
  convert
    (Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget AddCommGrpCat.{u})).mp
      (Scheme.Modules.isSheaf M) using 1
  all_goals rfl

/-- A scheme module, regarded as a sheaf of modules over its base ring. -/
noncomputable def moduleSheaf (M : X.Modules) :
    Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} k) :=
  ⟨modulePresheaf (k := k) M, modulePresheaf_isSheaf (k := k) M⟩

@[simp]
lemma moduleSheaf_obj (M : X.Modules) (U : X.Opensᵒᵖ) :
    (moduleSheaf (k := k) M).obj.obj U = ModuleCat.of k Γ(M, U.unop) :=
  rfl

@[simp]
lemma moduleSheaf_map_apply
    (M : X.Modules) {U V : X.Opensᵒᵖ} (i : U ⟶ V)
    (x : Γ(M, U.unop)) :
    (moduleSheaf (k := k) M).obj.map i x = M.presheaf.map i x :=
  rfl

/-- Forgetting the base-ring action recovers the underlying abelian sheaf. -/
noncomputable def moduleSheafForgetIso (M : X.Modules) :
    (sheafCompose
      (Opens.grothendieckTopology X)
      (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u})).obj
        (moduleSheaf (k := k) M) ≅
      (SheafOfModules.toSheaf X.ringCatSheaf).obj M :=
  Iso.refl _

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing

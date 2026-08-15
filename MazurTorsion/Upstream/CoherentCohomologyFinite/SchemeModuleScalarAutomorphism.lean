/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Scalar automorphisms of scheme modules

A global function acts on every module sheaf by multiplication after
restriction to each open.  A global unit therefore gives a canonical
module-sheaf automorphism.
-/


open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

@[instance_reducible] private noncomputable def scalarSectionModule
    (M : X.Modules) (U : X.Opensᵒᵖ) :
    Module Γ(X, U.unop) (M.val.obj U) := by
  change Module (X.ringCatSheaf.obj.obj U) (M.val.obj U)
  infer_instance

attribute [local instance] scalarSectionModule

@[instance_reducible] private noncomputable def scalarOpenSectionModule
    (M : X.Modules) (U : X.Opens) :
    Module Γ(X, U) (M.val.obj (.op U)) := by
  change Module (X.ringCatSheaf.obj.obj (.op U))
    (M.val.obj (.op U))
  infer_instance

attribute [local instance] scalarOpenSectionModule

/-- The restriction of a global function to an open. -/
noncomputable def globalFunctionAt
    (a : Γ(X, ⊤)) (U : X.Opensᵒᵖ) :
    Γ(X, U.unop) :=
  X.presheaf.map (homOfLE le_top).op a

lemma globalFunctionAt_naturality
    (a : Γ(X, ⊤)) {U V : X.Opensᵒᵖ}
    (i : U ⟶ V) :
    X.presheaf.map i (globalFunctionAt a U) =
      globalFunctionAt a V := by
  change
    X.presheaf.map i
        (X.presheaf.map (homOfLE le_top).op a) =
      X.presheaf.map (homOfLE le_top).op a
  rw [← CategoryTheory.comp_apply,
    ← X.presheaf.map_comp]
  congr 1

/-- Multiplication by a global function as an endomorphism of an
arbitrary scheme module. -/
noncomputable def scalarEndomorphism
    (M : X.Modules) (a : Γ(X, ⊤)) :
    M ⟶ M where
  val :=
    { app := fun U =>
        ModuleCat.ofHom
          (LinearMap.lsmul
            Γ(X, U.unop)
            (M.val.obj U)
            (globalFunctionAt a U))
      naturality := fun {U V} i => by
        ext x
        have hglobal :
            (X.ringCatSheaf.obj.map i).hom
                (globalFunctionAt a U) =
              globalFunctionAt a V :=
          globalFunctionAt_naturality a i
        rw [← hglobal]
        change
          (X.ringCatSheaf.obj.map i).hom
                (globalFunctionAt a U) •
              M.val.map i x =
            M.val.map i
              (globalFunctionAt a U • x)
        exact
          (M.val.map_smul i
            (globalFunctionAt a U) x).symm }

@[simp]
lemma scalarEndomorphism_app
    (M : X.Modules) (a : Γ(X, ⊤))
    (U : X.Opens) (x : Γ(M, U)) :
    (scalarEndomorphism M a).app U x =
      globalFunctionAt a (.op U) • x :=
  by
    change
      (LinearMap.lsmul Γ(X, U) (M.val.obj (.op U))
        (globalFunctionAt a (.op U))) x =
        globalFunctionAt a (.op U) • x
    rfl

/-- Multiplication by one is the identity. -/
@[simp]
lemma scalarEndomorphism_one (M : X.Modules) :
    scalarEndomorphism M (1 : Γ(X, ⊤)) =
      𝟙 M := by
  apply hom_ext
  intro U
  ext x
  simp [globalFunctionAt]

/-- Composition of scalar endomorphisms is multiplication of their
global functions. -/
lemma scalarEndomorphism_comp
    (M : X.Modules) (a b : Γ(X, ⊤)) :
    scalarEndomorphism M a ≫
        scalarEndomorphism M b =
      scalarEndomorphism M (a * b) := by
  apply hom_ext
  intro U
  ext x
  simp only [Hom.comp_app,
    ConcreteCategory.comp_apply,
    scalarEndomorphism_app,
    globalFunctionAt]
  rw [smul_smul, map_mul, mul_comm]

/-- Scalar multiplication commutes with every morphism of module
sheaves. -/
lemma scalarEndomorphism_naturality
    {M N : X.Modules} (φ : M ⟶ N)
    (a : Γ(X, ⊤)) :
    scalarEndomorphism M a ≫ φ =
      φ ≫ scalarEndomorphism N a := by
  apply hom_ext
  intro U
  ext x
  simp

/-- Pushforward regards multiplication by the pulled-back global
function as multiplication by the original global function. -/
lemma pushforward_scalarEndomorphism
    {T S : Scheme.{u}} (f : T ⟶ S)
    (M : T.Modules) (a : Γ(S, ⊤)) :
    (pushforward f).map
        (scalarEndomorphism M (f.appTop a)) =
      scalarEndomorphism
        ((pushforward f).obj M) a := by
  apply hom_ext
  intro U
  ext x
  simp only [pushforward_map_app, scalarEndomorphism_app]
  change
    globalFunctionAt (f.appTop a)
          (.op (f ⁻¹ᵁ U)) •
        (show Γ(M, f ⁻¹ᵁ U) from x) =
      (f.app U).hom
          (globalFunctionAt a (.op U)) •
        (show Γ(M, f ⁻¹ᵁ U) from x)
  have h := ConcreteCategory.congr_hom
    (f.toRingCatSheafHom.hom.naturality
      (homOfLE (le_top : U ≤ ⊤)).op) a
  have hscalar :
      (f.app U).hom
          (globalFunctionAt a (.op U)) =
        globalFunctionAt (f.appTop a)
          (.op (f ⁻¹ᵁ U)) :=
    by exact h
  rw [hscalar]

/-- Pullback carries multiplication by a global function to
multiplication by its pullback. -/
lemma pullback_scalarEndomorphism
    {T S : Scheme.{u}} (f : T ⟶ S)
    (M : S.Modules) (a : Γ(S, ⊤)) :
    (pullback f).map
        (scalarEndomorphism M a) =
      scalarEndomorphism
        ((pullback f).obj M) (f.appTop a) := by
  let N := (pullback f).obj M
  let adj := pullbackPushforwardAdjunction f
  apply (adj.homEquiv M N).injective
  let η : M ⟶ (pushforward f).obj N :=
    adj.homEquiv M N (𝟙 N)
  calc
    adj.homEquiv M N
          ((pullback f).map
            (scalarEndomorphism M a)) =
        scalarEndomorphism M a ≫ η := by
      exact
        (congrArg (adj.homEquiv M N)
          (Category.comp_id
            ((pullback f).map
              (scalarEndomorphism M a)))).symm |>.trans
          (adj.homEquiv_naturality_left
            (scalarEndomorphism M a) (𝟙 N))
    _ = η ≫
        scalarEndomorphism
          ((pushforward f).obj N) a :=
      scalarEndomorphism_naturality η a
    _ = η ≫
        (pushforward f).map
          (scalarEndomorphism N (f.appTop a)) := by
      rw [pushforward_scalarEndomorphism]
    _ = adj.homEquiv M N
        (scalarEndomorphism N (f.appTop a)) := by
      exact
        (adj.homEquiv_naturality_right
          (𝟙 N)
          (scalarEndomorphism N
            (f.appTop a))).symm |>.trans
          (congrArg (adj.homEquiv M N)
            (Category.id_comp
              (scalarEndomorphism N
                (f.appTop a))))

/-- A global unit acts by an automorphism of every scheme module. -/
noncomputable def scalarIso
    (M : X.Modules) (a : Γ(X, ⊤)ˣ) :
    M ≅ M where
  hom := scalarEndomorphism M a.val
  inv := scalarEndomorphism M a.inv
  hom_inv_id := by
    rw [scalarEndomorphism_comp,
      a.val_inv, scalarEndomorphism_one]
  inv_hom_id := by
    rw [scalarEndomorphism_comp,
      a.inv_val, scalarEndomorphism_one]

@[simp]
lemma scalarIso_hom
    (M : X.Modules) (a : Γ(X, ⊤)ˣ) :
    (scalarIso M a).hom =
      scalarEndomorphism M a.val :=
  rfl

@[simp]
lemma scalarIso_inv
    (M : X.Modules) (a : Γ(X, ⊤)ˣ) :
    (scalarIso M a).inv =
      scalarEndomorphism M a.inv :=
  rfl

@[simp]
lemma scalarIso_one (M : X.Modules) :
    scalarIso M (1 : Γ(X, ⊤)ˣ) =
      Iso.refl M :=
  Iso.ext (by simp)

/-- Multiplication of units corresponds to composition of the scalar
automorphisms. -/
lemma scalarIso_mul
    (M : X.Modules) (a b : Γ(X, ⊤)ˣ) :
    scalarIso M a ≪≫ scalarIso M b =
      scalarIso M (a * b) :=
  Iso.ext (by
    simp only [Iso.trans_hom, scalarIso_hom,
      Units.val_mul]
    exact scalarEndomorphism_comp M a.val b.val)

/-- Pullback of global units along a scheme morphism. -/
def pullbackGlobalUnit
    {T S : Scheme.{u}} (f : T ⟶ S) :
    Γ(S, ⊤)ˣ →* Γ(T, ⊤)ˣ :=
  Units.map
    (Scheme.Hom.appTop f).hom.toMonoidHom

@[simp]
lemma pullbackGlobalUnit_val
    {T S : Scheme.{u}} (f : T ⟶ S)
    (a : Γ(S, ⊤)ˣ) :
    (pullbackGlobalUnit f a).val =
      f.appTop a.val :=
  rfl

/-- Pullback of a scalar automorphism is the scalar automorphism
defined by the pulled-back unit. -/
lemma pullback_scalarIso
    {T S : Scheme.{u}} (f : T ⟶ S)
    (M : S.Modules) (a : Γ(S, ⊤)ˣ) :
    (pullback f).mapIso (scalarIso M a) =
      scalarIso ((pullback f).obj M)
        (pullbackGlobalUnit f a) :=
  Iso.ext (by
    change
      (pullback f).map
          (scalarEndomorphism M a.val) =
        scalarEndomorphism
          ((pullback f).obj M)
          (f.appTop a.val)
    exact pullback_scalarEndomorphism f M a.val)

end AlgebraicGeometry.Scheme.Modules

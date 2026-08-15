/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeModuleScalarAutomorphism
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleEffectiveDescent

/-!
# Scalar automorphisms and pullback base change

This file records the two functoriality facts needed when a descent
transition is modified by a scalar automorphism:

* scalar automorphisms commute with every module-sheaf isomorphism;
* base-change transport of a scalar-modified transition is the transported
  transition followed by the pulled-back scalar.
-/


open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Scalar automorphisms commute with every isomorphism of module sheaves. -/
lemma scalarIso_naturality {M N : X.Modules} (e : M ≅ N)
    (a : Γ(X, ⊤)ˣ) :
    scalarIso M a ≪≫ e = e ≪≫ scalarIso N a :=
  Iso.ext (scalarEndomorphism_naturality e.hom a.val)

private lemma trans_scalarIso_trans
    {M₀ M₁ M₂ : X.Modules}
    (e₁ : M₀ ≅ M₁) (e₂ : M₁ ≅ M₂)
    (a : Γ(X, ⊤)ˣ) :
    (e₁ ≪≫ scalarIso M₁ a) ≪≫ e₂ =
      (e₁ ≪≫ e₂) ≪≫ scalarIso M₂ a := by
  calc
    (e₁ ≪≫ scalarIso M₁ a) ≪≫ e₂ =
        e₁ ≪≫ (scalarIso M₁ a ≪≫ e₂) :=
      Iso.trans_assoc _ _ _
    _ = e₁ ≪≫ (e₂ ≪≫ scalarIso M₂ a) :=
      congrArg (fun e => e₁ ≪≫ e)
        (scalarIso_naturality e₂ a)
    _ = (e₁ ≪≫ e₂) ≪≫ scalarIso M₂ a :=
      (Iso.trans_assoc _ _ _).symm

/-- Two scalar-modified arrows in an isomorphism chain contribute the
product of their scalars at the target of the chain. -/
lemma scalarIso_twisted_chain
    {M₀ M₁ M₂ M₃ M₄ : X.Modules}
    (e₁ : M₀ ≅ M₁) (e₂ : M₁ ≅ M₂)
    (e₃ : M₂ ≅ M₃) (e₄ : M₃ ≅ M₄)
    (a b : Γ(X, ⊤)ˣ) :
    (((((e₁ ≪≫ scalarIso M₁ a) ≪≫ e₂) ≪≫ e₃) ≪≫
          scalarIso M₃ b) ≪≫ e₄) =
      ((((e₁ ≪≫ e₂) ≪≫ e₃) ≪≫ e₄) ≪≫
        scalarIso M₄ (a * b)) := by
  have h₁₂ :
      (e₁ ≪≫ scalarIso M₁ a) ≪≫ e₂ =
        (e₁ ≪≫ e₂) ≪≫ scalarIso M₂ a :=
    trans_scalarIso_trans e₁ e₂ a
  have h₁₂₃ :
      (((e₁ ≪≫ scalarIso M₁ a) ≪≫ e₂) ≪≫ e₃) =
        ((e₁ ≪≫ e₂) ≪≫ e₃) ≪≫ scalarIso M₃ a := by
    calc
      ((e₁ ≪≫ scalarIso M₁ a) ≪≫ e₂) ≪≫ e₃ =
          ((e₁ ≪≫ e₂) ≪≫ scalarIso M₂ a) ≪≫ e₃ :=
        congrArg (fun e => e ≪≫ e₃) h₁₂
      _ = ((e₁ ≪≫ e₂) ≪≫ e₃) ≪≫ scalarIso M₃ a :=
        trans_scalarIso_trans (e₁ ≪≫ e₂) e₃ a
  have hproduct :
      ((((e₁ ≪≫ scalarIso M₁ a) ≪≫ e₂) ≪≫ e₃) ≪≫
          scalarIso M₃ b) =
        ((e₁ ≪≫ e₂) ≪≫ e₃) ≪≫
          scalarIso M₃ (a * b) := by
    calc
      (((e₁ ≪≫ scalarIso M₁ a) ≪≫ e₂) ≪≫ e₃) ≪≫
            scalarIso M₃ b =
          (((e₁ ≪≫ e₂) ≪≫ e₃) ≪≫
            scalarIso M₃ a) ≪≫ scalarIso M₃ b :=
        congrArg (fun e => e ≪≫ scalarIso M₃ b) h₁₂₃
      _ = ((e₁ ≪≫ e₂) ≪≫ e₃) ≪≫
          (scalarIso M₃ a ≪≫ scalarIso M₃ b) :=
        Iso.trans_assoc _ _ _
      _ = ((e₁ ≪≫ e₂) ≪≫ e₃) ≪≫
          scalarIso M₃ (a * b) :=
        congrArg (fun e => ((e₁ ≪≫ e₂) ≪≫ e₃) ≪≫ e)
          (scalarIso_mul M₃ a b)
  calc
    ((((e₁ ≪≫ scalarIso M₁ a) ≪≫ e₂) ≪≫ e₃) ≪≫
          scalarIso M₃ b) ≪≫ e₄ =
        (((e₁ ≪≫ e₂) ≪≫ e₃) ≪≫
          scalarIso M₃ (a * b)) ≪≫ e₄ :=
      congrArg (fun e => e ≪≫ e₄) hproduct
    _ = (((e₁ ≪≫ e₂) ≪≫ e₃) ≪≫ e₄) ≪≫
        scalarIso M₄ (a * b) :=
      trans_scalarIso_trans ((e₁ ≪≫ e₂) ≪≫ e₃) e₄ (a * b)

/-- Pulling back a transition followed by a scalar is the pulled-back
transition followed by the scalar attached to the pulled-back unit. -/
lemma pullbackBaseChangeTransport_trans_scalarIso
    {W V Yi Yj : Scheme.{u}} (p : W ⟶ V)
    (a : V ⟶ Yi) (b : V ⟶ Yj)
    {Mi : Yi.Modules} {Mj : Yj.Modules}
    (g : (pullback a).obj Mi ≅ (pullback b).obj Mj)
    (z : Γ(V, ⊤)ˣ) :
    pullbackBaseChangeTransport p a b
        (g ≪≫ scalarIso ((pullback b).obj Mj) z) =
      pullbackBaseChangeTransport p a b g ≪≫
        scalarIso ((pullback (p ≫ b)).obj Mj)
          (pullbackGlobalUnit p z) := by
  unfold pullbackBaseChangeTransport
  rw [Functor.mapIso_trans, pullback_scalarIso]
  have hscalar :
      scalarIso
          ((pullback p).obj ((pullback b).obj Mj))
          (pullbackGlobalUnit p z) ≪≫
        (pullbackComp p b).app Mj =
      (pullbackComp p b).app Mj ≪≫
        scalarIso ((pullback (p ≫ b)).obj Mj)
          (pullbackGlobalUnit p z) :=
    scalarIso_naturality ((pullbackComp p b).app Mj)
      (pullbackGlobalUnit p z)
  calc
    (pullbackComp p a).symm.app Mi ≪≫
          ((pullback p).mapIso g ≪≫
            scalarIso
              ((pullback p).obj ((pullback b).obj Mj))
              (pullbackGlobalUnit p z)) ≪≫
          (pullbackComp p b).app Mj =
        (pullbackComp p a).symm.app Mi ≪≫
          (pullback p).mapIso g ≪≫
          (scalarIso
              ((pullback p).obj ((pullback b).obj Mj))
              (pullbackGlobalUnit p z) ≪≫
            (pullbackComp p b).app Mj) := by
              simp only [Iso.trans_assoc]
    _ = (pullbackComp p a).symm.app Mi ≪≫
          (pullback p).mapIso g ≪≫
          ((pullbackComp p b).app Mj ≪≫
            scalarIso ((pullback (p ≫ b)).obj Mj)
              (pullbackGlobalUnit p z)) := by
              exact congrArg
                (fun e =>
                  (pullbackComp p a).symm.app Mi ≪≫
                    (pullback p).mapIso g ≪≫ e)
                hscalar
    _ = ((pullbackComp p a).symm.app Mi ≪≫
          (pullback p).mapIso g ≪≫
          (pullbackComp p b).app Mj) ≪≫
        scalarIso ((pullback (p ≫ b)).obj Mj)
          (pullbackGlobalUnit p z) := by
            rfl

end AlgebraicGeometry.Scheme.Modules

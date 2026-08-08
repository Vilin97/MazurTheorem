/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime

/-!
# An invertible overlap cocycle is normalized

An isomorphism-valued overlap family satisfying the triple cocycle is automatically normalized.
Its diagonal pullback is idempotent by the cocycle, hence is the identity because it is
invertible.  The result is stated independently of the divisor construction so that concrete
descent constructions can consume one stable categorical interface.
-/

open CategoryTheory CategoryTheory.Limits

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u v

/-- Pulling a cocycle to a diagonal overlap makes its diagonal transition idempotent. -/
theorem diagonal_pullHom_idempotent_of_cocycle
    {C : Type u} [Category.{v} C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}
    {ι : Type*} {S : C} {Y : ι → C} {g : ∀ i, Y i ⟶ S}
    {sq : ∀ i j, ChosenPullback (g i) (g j)}
    {sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)}
    {obj : ∀ i, F.obj (.mk (.op (Y i)))}
    (hom : ∀ i j,
      (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ⟶
        (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j))
    (hcocycle : ∀ i j k,
      Pseudofunctor.DescentData'.pullHom' hom
            (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₂ ≫
          Pseudofunctor.DescentData'.pullHom' hom
            (sq₃ i j k).p (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
        Pseudofunctor.DescentData'.pullHom' hom
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₃)
    (i : ι) :
    let e := Pseudofunctor.DescentData'.pullHom' hom
      (g i) (𝟙 (Y i)) (𝟙 (Y i))
    e ≫ e = e := by
  dsimp only
  exact Pseudofunctor.DescentData'.comp_pullHom'' hom hcocycle
    (g i) (𝟙 (Y i)) (𝟙 (Y i)) (𝟙 (Y i))
      (by simp) (by simp) (by simp)

/-- Pulling back an isomorphism-valued transition again produces an isomorphism. -/
theorem pullHom_isIso_of_isIso
    {C : Type u} [Category.{v} C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}
    {X₁ X₂ Y Y' : C}
    {M₁ : F.obj (.mk (.op X₁))} {M₂ : F.obj (.mk (.op X₂))}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (e : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.map f₂.op.toLoc).toFunctor.obj M₂) [IsIso e]
    (p : Y' ⟶ Y) (pf₁ : Y' ⟶ X₁) (pf₂ : Y' ⟶ X₂)
    (hp₁ : p ≫ f₁ = pf₁) (hp₂ : p ≫ f₂ = pf₂) :
    IsIso (pullHom e p pf₁ pf₂ hp₁ hp₂) := by
  unfold pullHom
  infer_instance

/-- An isomorphism-valued overlap cocycle is normalized on every diagonal overlap. -/
theorem normalization_of_iso_cocycle
    {C : Type u} [Category.{v} C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}
    {ι : Type*} {S : C} {Y : ι → C} {g : ∀ i, Y i ⟶ S}
    {sq : ∀ i j, ChosenPullback (g i) (g j)}
    {sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)}
    {obj : ∀ i, F.obj (.mk (.op (Y i)))}
    (overlapIso : ∀ i j,
      (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ≅
        (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j))
    (hcocycle : ∀ i j k,
      Pseudofunctor.DescentData'.pullHom' (fun i j ↦ (overlapIso i j).hom)
            (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₂ ≫
          Pseudofunctor.DescentData'.pullHom' (fun i j ↦ (overlapIso i j).hom)
            (sq₃ i j k).p (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
        Pseudofunctor.DescentData'.pullHom' (fun i j ↦ (overlapIso i j).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₃)
    (i : ι) :
    Pseudofunctor.DescentData'.pullHom' (fun i j ↦ (overlapIso i j).hom)
      (g i) (𝟙 (Y i)) (𝟙 (Y i)) = 𝟙 _ := by
  let e := Pseudofunctor.DescentData'.pullHom'
    (fun i j ↦ (overlapIso i j).hom) (g i) (𝟙 (Y i)) (𝟙 (Y i))
  have hee : e ≫ e = e := diagonal_pullHom_idempotent_of_cocycle
    (fun i j ↦ (overlapIso i j).hom) hcocycle i
  change e = 𝟙 _
  haveI : IsIso e := by
    dsimp only [e, Pseudofunctor.DescentData'.pullHom']
    apply pullHom_isIso_of_isIso
  apply (cancel_epi e).1
  simpa only [Category.comp_id] using hee

/-- The full triple-cocycle property for an isomorphism-valued overlap family. -/
def IsIsoOverlapCocycle
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat)
    {ι : Type*} {S : C} {Y : ι → C} {g : ∀ i, Y i ⟶ S}
    (sq : ∀ i j, ChosenPullback (g i) (g j))
    (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
    (obj : ∀ i, F.obj (.mk (.op (Y i))))
    (overlapIso : ∀ i j,
    (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ≅
      (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j)) :=
  ∀ i j k,
    Pseudofunctor.DescentData'.pullHom' (fun i j ↦ (overlapIso i j).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₂ ≫
        Pseudofunctor.DescentData'.pullHom' (fun i j ↦ (overlapIso i j).hom)
          (sq₃ i j k).p (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
      Pseudofunctor.DescentData'.pullHom' (fun i j ↦ (overlapIso i j).hom)
        (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₃

/-- An isomorphism-valued overlap family together with its full triple cocycle. -/
structure IsoOverlapCocycle
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat)
    {ι : Type*} {S : C} {Y : ι → C} {g : ∀ i, Y i ⟶ S}
    (sq : ∀ i j, ChosenPullback (g i) (g j))
    (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
    (obj : ∀ i, F.obj (.mk (.op (Y i)))) where
  overlapIso : ∀ i j,
    (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ≅
      (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j)
  cocycle : IsIsoOverlapCocycle F sq sq₃ obj overlapIso

namespace IsoOverlapCocycle

/-- The normalization forced by a packaged isomorphism-valued cocycle. -/
theorem normalization
    {C : Type u} [Category.{v} C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}
    {ι : Type*} {S : C} {Y : ι → C} {g : ∀ i, Y i ⟶ S}
    {sq : ∀ i j, ChosenPullback (g i) (g j)}
    {sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)}
    {obj : ∀ i, F.obj (.mk (.op (Y i)))}
    (d : IsoOverlapCocycle F sq sq₃ obj) (i : ι) :
    Pseudofunctor.DescentData'.pullHom' (fun i j ↦ (d.overlapIso i j).hom)
      (g i) (𝟙 (Y i)) (𝟙 (Y i)) = 𝟙 _ := by
  have hc := d.cocycle
  unfold IsIsoOverlapCocycle at hc
  exact normalization_of_iso_cocycle d.overlapIso hc i

end IsoOverlapCocycle

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

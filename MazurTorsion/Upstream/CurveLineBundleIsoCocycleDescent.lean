/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveLineBundleDescent

/-!
# Descent from a named-face isomorphism cocycle

This module isolates a stable interface between geometric overlap calculations and Mathlib's
chosen-pullback descent data.  Its cocycle certificate is stated using the three named maps from
a chosen triple pullback to its pairwise pullbacks.  Consequently, its equality witnesses are
part of the interface instead of being independently synthesized by `pullHom'` at every
concrete use site.

The generic conversion below changes no objects or transition maps: it rewrites the named-face
equation into Mathlib's `DescentData'` equation and then extends it to full descent data.  The
module makes no effectivity, fully faithful descent, tensor-compatibility, or Picard-equivalence
claim.  Its named downstream consumer is `CurveDivisorGlobalLineBundle`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace MazurTorsion.AlgebraicGeometry.LineBundleDescent

open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe t v' v u' u

namespace CocycleConstructor

/-- The remaining argument of a partially applied structure constructor. -/
abbrev Argument {P : Sort*} {A : Sort*} (_ctor : P → A) := P

/-- Complete a partially applied structure constructor. -/
def complete {P : Sort*} {A : Sort*} (ctor : P → A) (h : Argument ctor) : A :=
  ctor h

end CocycleConstructor

/-- The triple-cocycle equation expressed on the three named pairwise faces of a chosen triple
pullback. Unlike the default arguments of `pullHom'`, all six projection witnesses are fixed by
the chosen pullback data. -/
structure IsoCocycleCondition
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    {ι : Type t} {S : C} {Y : ι → C} (g : ∀ i, Y i ⟶ S)
    (sq : ∀ i j, ChosenPullback (g i) (g j))
    (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
    (obj : ∀ i, F.obj (.mk (.op (Y i))))
    (overlapIso : ∀ i j,
      (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ≅
        (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j)) : Prop where
  /-- The two composites on every named triple overlap agree. -/
  equation (i j k : ι) :
    Pseudofunctor.DescentData'.pullHom'
          (F := F) (sq := sq) (fun i j ↦ (overlapIso i j).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₂
          (hf₁ := (sq₃ i j k).w₁) (hf₂ := (sq₃ i j k).w₂) ≫
        Pseudofunctor.DescentData'.pullHom'
          (F := F) (sq := sq) (fun i j ↦ (overlapIso i j).hom)
          (sq₃ i j k).p (sq₃ i j k).p₂ (sq₃ i j k).p₃
          (hf₁ := (sq₃ i j k).w₂) (hf₂ := (sq₃ i j k).w₃) =
      Pseudofunctor.DescentData'.pullHom'
        (F := F) (sq := sq) (fun i j ↦ (overlapIso i j).hom)
        (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₃
        (hf₁ := (sq₃ i j k).w₁) (hf₂ := (sq₃ i j k).w₃)

/-- The condition constructor with all geometric data fixed, exposing only its exact equation
argument. -/
theorem isoCocycleConditionConstructor
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    {ι : Type t} {S : C} {Y : ι → C} (g : ∀ i, Y i ⟶ S)
    (sq : ∀ i j, ChosenPullback (g i) (g j))
    (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
    (obj : ∀ i, F.obj (.mk (.op (Y i))))
    (overlapIso : ∀ i j,
      (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ≅
        (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j)) :
    CocycleConstructor.Argument
        (@IsoCocycleCondition.mk C _ F ι S Y g sq sq₃ obj overlapIso) →
      IsoCocycleCondition F g sq sq₃ obj overlapIso :=
  @IsoCocycleCondition.mk C _ F ι S Y g sq sq₃ obj overlapIso

/-- A named-face cocycle implies the `pullHom'` cocycle expected by Mathlib's chosen-pullback
descent datum. -/
theorem pullHom'_cocycle_of_isoCocycleCondition
    {C : Type u} [Category.{v} C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
    {ι : Type t} {S : C} {Y : ι → C} {g : ∀ i, Y i ⟶ S}
    {sq : ∀ i j, ChosenPullback (g i) (g j)}
    {sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)}
    {obj : ∀ i, F.obj (.mk (.op (Y i)))}
    {overlapIso : ∀ i j,
      (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ≅
        (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j)}
    (h : IsoCocycleCondition F g sq sq₃ obj overlapIso) (i j k : ι) :
    Pseudofunctor.DescentData'.pullHom'
          (F := F) (sq := sq) (fun i j ↦ (overlapIso i j).hom)
          (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₂ ≫
        Pseudofunctor.DescentData'.pullHom'
          (F := F) (sq := sq) (fun i j ↦ (overlapIso i j).hom)
          (sq₃ i j k).p (sq₃ i j k).p₂ (sq₃ i j k).p₃ =
      Pseudofunctor.DescentData'.pullHom'
        (F := F) (sq := sq) (fun i j ↦ (overlapIso i j).hom)
        (sq₃ i j k).p (sq₃ i j k).p₁ (sq₃ i j k).p₃ :=
  h.equation i j k

/-- A named-face isomorphism cocycle is automatically normalized on every diagonal. -/
theorem normalization_of_isoCocycleCondition
    {C : Type u} [Category.{v} C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
    {ι : Type t} {S : C} {Y : ι → C} {g : ∀ i, Y i ⟶ S}
    {sq : ∀ i j, ChosenPullback (g i) (g j)}
    {sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)}
    {obj : ∀ i, F.obj (.mk (.op (Y i)))}
    {overlapIso : ∀ i j,
      (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ≅
        (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j)}
    (h : IsoCocycleCondition F g sq sq₃ obj overlapIso) (i : ι) :
    Pseudofunctor.DescentData'.pullHom'
      (F := F) (sq := sq) (fun i j ↦ (overlapIso i j).hom)
      (g i) (𝟙 (Y i)) (𝟙 (Y i)) = 𝟙 _ :=
  normalization_of_iso_cocycle overlapIso
    (pullHom'_cocycle_of_isoCocycleCondition h) i

/-- Convert a named-face isomorphism cocycle to chosen-pullback descent data without changing
its local objects or overlap maps. -/
noncomputable def descentDataPrimeOfIsoCocycleCondition
    {C : Type u} [Category.{v} C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
    {ι : Type t} {S : C} {Y : ι → C} {g : ∀ i, Y i ⟶ S}
    {sq : ∀ i j, ChosenPullback (g i) (g j)}
    {sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)}
    (obj : ∀ i, F.obj (.mk (.op (Y i))))
    (overlapIso : ∀ i j,
      (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ≅
        (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j))
    (h : IsoCocycleCondition F g sq sq₃ obj overlapIso) :
    F.DescentData' sq sq₃ :=
  DescentDataPrime.ofIso obj overlapIso
    (normalization_of_isoCocycleCondition h)
    (pullHom'_cocycle_of_isoCocycleCondition h)

/-- Extend a named-face isomorphism cocycle to coherent descent data on every common
refinement. -/
noncomputable def descentDataOfIsoCocycleCondition
    {C : Type u} [Category.{v} C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
    {ι : Type t} {S : C} {Y : ι → C} {g : ∀ i, Y i ⟶ S}
    {sq : ∀ i j, ChosenPullback (g i) (g j)}
    {sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)}
    (obj : ∀ i, F.obj (.mk (.op (Y i))))
    (overlapIso : ∀ i j,
      (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ≅
        (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j))
    (h : IsoCocycleCondition F g sq sq₃ obj overlapIso) :
    F.DescentData g :=
  (descentDataPrimeOfIsoCocycleCondition obj overlapIso h).descentData

@[simp]
lemma descentDataOfIsoCocycleCondition_obj
    {C : Type u} [Category.{v} C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
    {ι : Type t} {S : C} {Y : ι → C} {g : ∀ i, Y i ⟶ S}
    {sq : ∀ i j, ChosenPullback (g i) (g j)}
    {sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)}
    (obj : ∀ i, F.obj (.mk (.op (Y i))))
    (overlapIso : ∀ i j,
      (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ≅
        (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j))
    (h : IsoCocycleCondition F g sq sq₃ obj overlapIso) (i : ι) :
    (descentDataOfIsoCocycleCondition obj overlapIso h).obj i = obj i :=
  rfl

@[simp]
lemma descentDataOfIsoCocycleCondition_hom_on_overlap
    {C : Type u} [Category.{v} C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
    {ι : Type t} {S : C} {Y : ι → C} {g : ∀ i, Y i ⟶ S}
    {sq : ∀ i j, ChosenPullback (g i) (g j)}
    {sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k)}
    (obj : ∀ i, F.obj (.mk (.op (Y i))))
    (overlapIso : ∀ i j,
      (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ≅
        (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j))
    (h : IsoCocycleCondition F g sq sq₃ obj overlapIso) (i j : ι) :
    (descentDataOfIsoCocycleCondition obj overlapIso h).hom
        (sq i j).p (sq i j).p₁ (sq i j).p₂ = (overlapIso i j).hom := by
  exact Pseudofunctor.DescentData'.pullHom'_eq_hom
    (descentDataPrimeOfIsoCocycleCondition obj overlapIso h) i j

open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry

/-- The named-face cocycle condition specialized to line bundles on a universe-zero scheme
open cover. This is the elaboration boundary consumed by concrete geometric transition maps. -/
structure LineBundleIsoCocycleCondition
    {X : Scheme.{u}} (cov : X.OpenCover.{0})
    (L : ∀ i : cov.I₀, InvertibleSheaf (cov.X i))
    (overlapIso : ∀ i j,
      (modulesPseudofunctor.map (overlap cov i j).p₁.op.toLoc).toFunctor.obj (L i).obj ≅
        (modulesPseudofunctor.map (overlap cov i j).p₂.op.toLoc).toFunctor.obj (L j).obj) :
    Prop where
  /-- The two composites on every named triple overlap agree. -/
  equation (i j k : cov.I₀) :
    Pseudofunctor.DescentData'.pullHom'
          (F := modulesPseudofunctor) (sq := overlap cov)
          (fun i j ↦ (overlapIso i j).hom)
          (tripleOverlap cov i j k).p
          (tripleOverlap cov i j k).p₁
          (tripleOverlap cov i j k).p₂
          (hf₁ := (tripleOverlap cov i j k).w₁)
          (hf₂ := (tripleOverlap cov i j k).w₂) ≫
        Pseudofunctor.DescentData'.pullHom'
          (F := modulesPseudofunctor) (sq := overlap cov)
          (fun i j ↦ (overlapIso i j).hom)
          (tripleOverlap cov i j k).p
          (tripleOverlap cov i j k).p₂
          (tripleOverlap cov i j k).p₃
          (hf₁ := (tripleOverlap cov i j k).w₂)
          (hf₂ := (tripleOverlap cov i j k).w₃) =
      Pseudofunctor.DescentData'.pullHom'
        (F := modulesPseudofunctor) (sq := overlap cov)
        (fun i j ↦ (overlapIso i j).hom)
        (tripleOverlap cov i j k).p
        (tripleOverlap cov i j k).p₁
        (tripleOverlap cov i j k).p₃
        (hf₁ := (tripleOverlap cov i j k).w₁)
        (hf₂ := (tripleOverlap cov i j k).w₃)

/-- The specialized condition constructor with the local line bundles and overlap family fixed.
-/
theorem lineBundleIsoCocycleConditionConstructor
    {X : Scheme.{u}} (cov : X.OpenCover.{0})
    (L : ∀ i : cov.I₀, InvertibleSheaf (cov.X i))
    (overlapIso : ∀ i j,
      (modulesPseudofunctor.map (overlap cov i j).p₁.op.toLoc).toFunctor.obj (L i).obj ≅
        (modulesPseudofunctor.map (overlap cov i j).p₂.op.toLoc).toFunctor.obj (L j).obj) :
    CocycleConstructor.Argument
        (@LineBundleIsoCocycleCondition.mk X cov L overlapIso) →
      LineBundleIsoCocycleCondition cov L overlapIso :=
  @LineBundleIsoCocycleCondition.mk X cov L overlapIso

/-- Forget the line-bundle façade and recover the generic named-face cocycle certificate. -/
theorem LineBundleIsoCocycleCondition.toIsoCocycleCondition
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    {L : ∀ i : cov.I₀, InvertibleSheaf (cov.X i)}
    {overlapIso : ∀ i j,
      (modulesPseudofunctor.map (overlap cov i j).p₁.op.toLoc).toFunctor.obj (L i).obj ≅
        (modulesPseudofunctor.map (overlap cov i j).p₂.op.toLoc).toFunctor.obj (L j).obj}
    (h : LineBundleIsoCocycleCondition cov L overlapIso) :
    IsoCocycleCondition modulesPseudofunctor cov.f (overlap cov) (tripleOverlap cov)
      (fun i ↦ (L i).obj) overlapIso :=
  ⟨h.equation⟩

/-- Full coherent module descent data attached to a named-face line-bundle cocycle. -/
noncomputable def descentDataOfLineBundleIsoCocycleCondition
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    (L : ∀ i : cov.I₀, InvertibleSheaf (cov.X i))
    (overlapIso : ∀ i j,
      (modulesPseudofunctor.map (overlap cov i j).p₁.op.toLoc).toFunctor.obj (L i).obj ≅
        (modulesPseudofunctor.map (overlap cov i j).p₂.op.toLoc).toFunctor.obj (L j).obj)
    (h : LineBundleIsoCocycleCondition cov L overlapIso) :
    modulesPseudofunctor.DescentData cov.f :=
  descentDataOfIsoCocycleCondition (fun i ↦ (L i).obj) overlapIso
    h.toIsoCocycleCondition

@[simp]
lemma descentDataOfLineBundleIsoCocycleCondition_obj
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    (L : ∀ i : cov.I₀, InvertibleSheaf (cov.X i))
    (overlapIso : ∀ i j,
      (modulesPseudofunctor.map (overlap cov i j).p₁.op.toLoc).toFunctor.obj (L i).obj ≅
        (modulesPseudofunctor.map (overlap cov i j).p₂.op.toLoc).toFunctor.obj (L j).obj)
    (h : LineBundleIsoCocycleCondition cov L overlapIso) (i : cov.I₀) :
    (descentDataOfLineBundleIsoCocycleCondition L overlapIso h).obj i = (L i).obj :=
  rfl

/-- A named-face line-bundle cocycle as coherent locally invertible descent data. -/
noncomputable def invertibleDescentDataOfLineBundleIsoCocycleCondition
    {X : Scheme.{u}} {cov : X.OpenCover.{0}}
    (L : ∀ i : cov.I₀, InvertibleSheaf (cov.X i))
    (overlapIso : ∀ i j,
      (modulesPseudofunctor.map (overlap cov i j).p₁.op.toLoc).toFunctor.obj (L i).obj ≅
        (modulesPseudofunctor.map (overlap cov i j).p₂.op.toLoc).toFunctor.obj (L j).obj)
    (h : LineBundleIsoCocycleCondition cov L overlapIso) :
    InvertibleDescentData cov where
  toDescentData := descentDataOfLineBundleIsoCocycleCondition L overlapIso h
  localInvertible i := (L i).property

end MazurTorsion.AlgebraicGeometry.LineBundleDescent

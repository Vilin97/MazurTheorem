/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.PermutationPower

/-!
# Finite products of finite étale objects in a slice

Finite étale morphisms are stable under base change and composition.  Hence
objects finite étale over a fixed scheme are closed under finite products in
the slice category.  This file packages that categorical argument for the
finite family of point neighborhoods used in `FiniteSupportEtaleCoordinates`.
-/

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.FiniteEtaleRelativeProduct

variable (S : Scheme.{u})

/-- The object property of being finite étale over a fixed base scheme. -/
abbrev finiteEtaleOver : ObjectProperty (Over S) :=
  fun X ↦ IsFinite X.hom ∧ Etale X.hom

instance finiteEtaleOver_isClosedUnderIsomorphisms :
    (finiteEtaleOver S).IsClosedUnderIsomorphisms := by
  constructor
  intro X Y e hX
  let eleft : Y.left ≅ X.left := (Over.forget _).mapIso e.symm
  letI : IsFinite X.hom := hX.1
  letI : Etale X.hom := hX.2
  have heq : eleft.hom ≫ X.hom = Y.hom := by
    change e.inv.left ≫ X.hom = Y.hom
    exact e.inv.w
  constructor
  · rw [← heq]
    infer_instance
  · rw [← heq]
    infer_instance

/-- The relative binary product of finite étale objects is finite étale. -/
theorem binaryProduct_isFiniteEtale (X Y : Over S)
    (hX : finiteEtaleOver S X) (hY : finiteEtaleOver S Y) :
    finiteEtaleOver S (X ⨯ Y) := by
  letI : IsFinite X.hom := hX.1
  letI : Etale X.hom := hX.2
  letI : IsFinite Y.hom := hY.1
  letI : Etale Y.hom := hY.2
  letI : IsFinite (pullback.fst X.hom Y.hom) :=
    MorphismProperty.pullback_fst (P := @IsFinite) X.hom Y.hom hY.1
  letI : Etale (pullback.fst X.hom Y.hom) :=
    MorphismProperty.pullback_fst (P := @Etale) X.hom Y.hom hY.2
  have hcomp :
      (Over.prodLeftIsoPullback X Y).hom ≫
          (pullback.fst X.hom Y.hom ≫ X.hom) =
        (X ⨯ Y).hom := by
    rw [← Category.assoc, Over.prodLeftIsoPullback_hom_fst]
    exact (Limits.prod.fst : X ⨯ Y ⟶ X).w
  constructor
  · rw [← hcomp]
    infer_instance
  · rw [← hcomp]
    infer_instance

instance finiteEtaleOver_isClosedUnderBinaryProducts :
    (finiteEtaleOver S).IsClosedUnderBinaryProducts := by
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
  rintro _ ⟨F, hF⟩
  let X := F.obj ⟨WalkingPair.left⟩
  let Y := F.obj ⟨WalkingPair.right⟩
  let e : limit F ≅ X ⨯ Y := HasLimit.isoOfNatIso (diagramIsoPair F)
  apply (finiteEtaleOver S).prop_of_iso e.symm
  exact binaryProduct_isFiniteEtale S X Y
    (hF ⟨WalkingPair.left⟩) (hF ⟨WalkingPair.right⟩)

instance finiteEtaleOver_isClosedUnderEmpty :
    (finiteEtaleOver S).IsClosedUnderLimitsOfShape (Discrete PEmpty) := by
  constructor
  intro X p
  let hX : IsTerminal X :=
    (ObjectProperty.limitsOfShape_isEmpty_iff (finiteEtaleOver S) _ X).mp p |>.some
  let T : Over S := Over.mk (𝟙 S)
  let hT : IsTerminal T := IsTerminal.ofUniqueHom
    (fun Z ↦ Over.homMk Z.hom)
    (fun Z f ↦ Over.OverMorphism.ext (by simpa [T] using f.w))
  let e : X ≅ T := hX.uniqueUpToIso hT
  apply (finiteEtaleOver S).prop_of_iso e.symm
  change IsFinite (𝟙 S) ∧ Etale (𝟙 S)
  exact ⟨inferInstance, inferInstance⟩

instance finiteEtaleOver_isClosedUnderFiniteProducts :
    (finiteEtaleOver S).IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

/-- A finite relative product of finite étale objects is finite étale over
the common base. -/
theorem product_isFiniteEtale {ι : Type} [Finite ι]
    (X : ι → Over S) (hX : ∀ i, finiteEtaleOver S (X i)) :
    finiteEtaleOver S (∏ᶜ X) :=
  (finiteEtaleOver S).prop_product hX

/-- The object property of having a point on the underlying scheme. -/
abbrev nonemptyOver : ObjectProperty (Over S) :=
  fun X ↦ Nonempty X.left

instance nonemptyOver_isClosedUnderIsomorphisms :
    (nonemptyOver S).IsClosedUnderIsomorphisms := by
  constructor
  intro X Y e hX
  exact ⟨e.hom.left (Classical.choice hX)⟩

instance nonemptyOver_isClosedUnderBinaryProducts [Subsingleton S] :
    (nonemptyOver S).IsClosedUnderBinaryProducts := by
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
  rintro _ ⟨F, hF⟩
  let X := F.obj ⟨WalkingPair.left⟩
  let Y := F.obj ⟨WalkingPair.right⟩
  let e : limit F ≅ X ⨯ Y := HasLimit.isoOfNatIso (diagramIsoPair F)
  apply (nonemptyOver S).prop_of_iso e.symm
  let x : X.left := Classical.choice (hF ⟨WalkingPair.left⟩)
  let y : Y.left := Classical.choice (hF ⟨WalkingPair.right⟩)
  obtain ⟨p, _, _⟩ := Scheme.Pullback.exists_preimage_pullback
    x y (Subsingleton.elim (X.hom x) (Y.hom y))
  exact ⟨(Over.prodLeftIsoPullback X Y).inv p⟩

instance nonemptyOver_isClosedUnderEmpty [Nonempty S] :
    (nonemptyOver S).IsClosedUnderLimitsOfShape (Discrete PEmpty) := by
  constructor
  intro X p
  let hX : IsTerminal X :=
    (ObjectProperty.limitsOfShape_isEmpty_iff (nonemptyOver S) _ X).mp p |>.some
  let T : Over S := Over.mk (𝟙 S)
  let hT : IsTerminal T := IsTerminal.ofUniqueHom
    (fun Z ↦ Over.homMk Z.hom)
    (fun Z f ↦ Over.OverMorphism.ext (by simpa [T] using f.w))
  let e : X ≅ T := hX.uniqueUpToIso hT
  apply (nonemptyOver S).prop_of_iso e.symm
  change Nonempty S
  exact inferInstance

instance nonemptyOver_isClosedUnderFiniteProducts [Nonempty S] [Subsingleton S] :
    (nonemptyOver S).IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

/-- Over a nonempty one-point base, a finite relative product of nonempty
schemes is nonempty. -/
theorem product_nonempty [Nonempty S] [Subsingleton S]
    {ι : Type} [Finite ι] (X : ι → Over S)
    (hX : ∀ i, Nonempty (X i).left) : Nonempty (∏ᶜ X).left :=
  (nonemptyOver S).prop_product hX

/-- A prescribed finite family of points over a one-point base lifts to the
relative product, with all product projections equal to the prescribed
points. -/
theorem exists_fin_product_point [Nonempty S] [Subsingleton S]
    (n : ℕ) (X : Fin n → Over S) (x : ∀ i, (X i).left) :
    ∃ p : (∏ᶜ X).left, ∀ i, (Pi.π X i).left p = x i := by
  induction n with
  | zero =>
      let p : (∏ᶜ X).left := Classical.choice
        (product_nonempty S X (fun i ↦ Fin.elim0 i))
      exact ⟨p, fun i ↦ Fin.elim0 i⟩
  | succ n ih =>
      let tail : Fin n → Over S := fun i ↦ X i.succ
      obtain ⟨pTail, hpTail⟩ := ih tail (fun i ↦ x i.succ)
      obtain ⟨r, hrHead, hrTail⟩ := Scheme.Pullback.exists_preimage_pullback
        (x 0) pTail
          (Subsingleton.elim ((X 0).hom (x 0)) ((∏ᶜ tail).hom pTail))
      let q : (X 0 ⨯ ∏ᶜ tail).left :=
        (Over.prodLeftIsoPullback (X 0) (∏ᶜ tail)).inv r
      have hqHead :
          (Limits.prod.fst : X 0 ⨯ ∏ᶜ tail ⟶ X 0).left q = x 0 := by
        change (((Over.prodLeftIsoPullback (X 0) (∏ᶜ tail)).inv ≫
          (Limits.prod.fst : X 0 ⨯ ∏ᶜ tail ⟶ X 0).left) r) = x 0
        rw [Over.prodLeftIsoPullback_inv_fst]
        exact hrHead
      have hqTail :
          (Limits.prod.snd : X 0 ⨯ ∏ᶜ tail ⟶ ∏ᶜ tail).left q = pTail := by
        change (((Over.prodLeftIsoPullback (X 0) (∏ᶜ tail)).inv ≫
          (Limits.prod.snd : X 0 ⨯ ∏ᶜ tail ⟶ ∏ᶜ tail).left) r) = pTail
        rw [Over.prodLeftIsoPullback_inv_snd]
        exact hrTail
      let c₁ : Fan tail := Fan.mk (∏ᶜ tail) (fun i ↦ Pi.π tail i)
      let hc₁ : IsLimit c₁ := limit.isLimit (Discrete.functor tail)
      let c₂ : BinaryFan (X 0) c₁.pt :=
        BinaryFan.mk Limits.prod.fst Limits.prod.snd
      let hc₂ : IsLimit c₂ := Limits.prodIsProd (X 0) c₁.pt
      let c : Fan X := extendFan c₁ c₂
      let hc : IsLimit c := extendFanIsLimit X hc₁ hc₂
      let e : ∏ᶜ X ≅ c.pt :=
        IsLimit.conePointUniqueUpToIso (limit.isLimit (Discrete.functor X)) hc
      let q' : c.pt.left := q
      refine ⟨e.inv.left q', ?_⟩
      intro i
      have heπ : e.inv ≫ Pi.π X i = c.π.app ⟨i⟩ :=
        IsLimit.conePointUniqueUpToIso_inv_comp
          (limit.isLimit (Discrete.functor X)) hc ⟨i⟩
      have heval := congrArg (fun f : c.pt ⟶ X i ↦ f.left q') heπ
      change (Pi.π X i).left (e.inv.left q') = x i
      change (e.inv ≫ Pi.π X i).left q' = x i
      rw [heval]
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · change (Limits.prod.fst : X 0 ⨯ ∏ᶜ tail ⟶ X 0).left q' = x 0
        change (Limits.prod.fst : X 0 ⨯ ∏ᶜ tail ⟶ X 0).left q = x 0
        exact hqHead
      · change (Pi.π tail j).left
          ((Limits.prod.snd : X 0 ⨯ ∏ᶜ tail ⟶ ∏ᶜ tail).left q') = x j.succ
        have hqTail' :
            (Limits.prod.snd : X 0 ⨯ ∏ᶜ tail ⟶ ∏ᶜ tail).left q' = pTail := by
          change (Limits.prod.snd : X 0 ⨯ ∏ᶜ tail ⟶ ∏ᶜ tail).left q = pTail
          exact hqTail
        rw [hqTail']
        exact hpTail j

end MazurTorsion.AlgebraicGeometry.Jacobian.FiniteEtaleRelativeProduct

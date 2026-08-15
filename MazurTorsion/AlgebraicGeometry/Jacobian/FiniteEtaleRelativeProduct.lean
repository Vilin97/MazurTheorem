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
open IsLocalRing

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

/-- A finite family of prescribed points lying over the same base point
lifts to the relative product.  The resulting product point lies over that
base point and has the prescribed value under every projection. -/
theorem exists_fin_product_point_over
    (n : ℕ) (X : Fin n → Over S) (s : S)
    (x : ∀ i, (X i).left) (hx : ∀ i, (X i).hom (x i) = s) :
    ∃ p : (∏ᶜ X).left,
      (∏ᶜ X).hom p = s ∧ ∀ i, (Pi.π X i).left p = x i := by
  induction n with
  | zero =>
      let T : Over S := Over.mk (𝟙 S)
      let toProduct : T ⟶ ∏ᶜ X := Pi.lift (fun i ↦ Fin.elim0 i)
      let p : (∏ᶜ X).left := toProduct.left s
      have hp : (∏ᶜ X).hom p = s := by
        change (toProduct.left ≫ (∏ᶜ X).hom) s = s
        rw [toProduct.w]
        rfl
      exact ⟨p, hp, fun i ↦ Fin.elim0 i⟩
  | succ n ih =>
      let tail : Fin n → Over S := fun i ↦ X i.succ
      obtain ⟨pTail, hpTailBase, hpTail⟩ :=
        ih tail (fun i ↦ x i.succ) (fun i ↦ hx i.succ)
      obtain ⟨r, hrHead, hrTail⟩ := Scheme.Pullback.exists_preimage_pullback
        (x 0) pTail ((hx 0).trans hpTailBase.symm)
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
      have hqBase : (X 0 ⨯ ∏ᶜ tail).hom q = s := by
        have h := congrArg
          (fun a : (X 0 ⨯ ∏ᶜ tail).left ⟶ S ↦ a q)
          (Limits.prod.fst : X 0 ⨯ ∏ᶜ tail ⟶ X 0).w
        rw [← h]
        change (X 0).hom
          ((Limits.prod.fst : X 0 ⨯ ∏ᶜ tail ⟶ X 0).left q) = s
        rw [hqHead, hx 0]
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
      have hpBase : (∏ᶜ X).hom (e.inv.left q') = s := by
        have h := congrArg (fun a : c.pt.left ⟶ S ↦ a q') e.inv.w
        exact h.trans hqBase
      refine ⟨e.inv.left q', hpBase, ?_⟩
      intro i
      have heπ : e.inv ≫ Pi.π X i = c.π.app ⟨i⟩ :=
        IsLimit.conePointUniqueUpToIso_inv_comp
          (limit.isLimit (Discrete.functor X)) hc ⟨i⟩
      have heval := congrArg (fun a : c.pt ⟶ X i ↦ a.left q') heπ
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

/-- If a point of every factor has a preimage, then the original point of
the relative product has a preimage under the product morphism.  The proof
base-changes every factor to the spectrum of the target point's local ring;
this retains the residue-field correlation carried by the product point. -/
theorem exists_fin_product_preimage
    (n : ℕ) (X Y : Fin n → Over S) (f : ∀ i, Y i ⟶ X i)
    (z : (∏ᶜ X).left) (y : ∀ i, (Y i).left)
    (hy : ∀ i, (f i).left (y i) = (Pi.π X i).left z) :
    ∃ w : (∏ᶜ Y).left,
      (Limits.Pi.map f).left w = z ∧
        ∀ i, (Pi.π Y i).left w = y i := by
  let Z : Scheme.{u} := Spec ((∏ᶜ X).left.presheaf.stalk z)
  let zMap : Z ⟶ (∏ᶜ X).left := (∏ᶜ X).left.fromSpecStalk z
  let zClosedPoint : Z :=
    closedPoint ((∏ᶜ X).left.presheaf.stalk z)
  have zMap_zClosedPoint : zMap zClosedPoint = z := by
    dsimp only [zMap, zClosedPoint, Z]
    exact Scheme.fromSpecStalk_closedPoint
  let zOver : Over S := Over.mk (zMap ≫ (∏ᶜ X).hom)
  let coordinate (i : Fin n) : zOver ⟶ X i :=
    Over.homMk (zMap ≫ (Pi.π X i).left) (by
      change zMap ≫ (Pi.π X i).left ≫ (X i).hom =
        zMap ≫ (∏ᶜ X).hom
      exact congrArg (fun q ↦ zMap ≫ q) (Pi.π X i).w)
  let pullbackObject (i : Fin n) : Scheme.{u} :=
    pullback (f i).left (coordinate i).left
  let pulled (i : Fin n) : Over Z :=
    Over.mk (pullback.snd (f i).left (coordinate i).left)
  have existsPulledPoint (i : Fin n) :
      ∃ p : (pulled i).left,
        pullback.fst (f i).left (coordinate i).left p = y i ∧
          pullback.snd (f i).left (coordinate i).left p =
            zClosedPoint := by
    apply Scheme.Pullback.exists_preimage_pullback
    change (f i).left (y i) =
      (zMap ≫ (Pi.π X i).left)
        zClosedPoint
    rw [Scheme.Hom.comp_apply, zMap_zClosedPoint]
    exact hy i
  let pulledPoint (i : Fin n) : (pulled i).left :=
    Classical.choose (existsPulledPoint i)
  have pulledPoint_fst (i : Fin n) :
      pullback.fst (f i).left (coordinate i).left (pulledPoint i) = y i := by
    exact (Classical.choose_spec (existsPulledPoint i)).1
  have pulledPoint_snd (i : Fin n) :
      (pulled i).hom (pulledPoint i) =
        zClosedPoint := by
    exact (Classical.choose_spec (existsPulledPoint i)).2
  obtain ⟨q, hqBase, hqProjection⟩ :=
    exists_fin_product_point_over Z n pulled
      zClosedPoint
      pulledPoint pulledPoint_snd
  let QOverS : Over S := Over.mk ((∏ᶜ pulled).hom ≫ zOver.hom)
  let qToZ : QOverS ⟶ zOver := Over.homMk (∏ᶜ pulled).hom rfl
  let qToY (i : Fin n) : QOverS ⟶ Y i :=
    Over.homMk ((Pi.π pulled i).left ≫
      pullback.fst (f i).left (coordinate i).left) (by
        change (Pi.π pulled i).left ≫
            pullback.fst (f i).left (coordinate i).left ≫ (Y i).hom =
          (∏ᶜ pulled).hom ≫ zOver.hom
        have hInner :
            pullback.fst (f i).left (coordinate i).left ≫ (Y i).hom =
              pullback.snd (f i).left (coordinate i).left ≫ zOver.hom := by
          calc
            pullback.fst (f i).left (coordinate i).left ≫ (Y i).hom =
                pullback.fst (f i).left (coordinate i).left ≫
                  ((f i).left ≫ (X i).hom) := congrArg
              (fun a ↦ pullback.fst (f i).left (coordinate i).left ≫ a)
                (f i).w.symm
            _ = (pullback.fst (f i).left (coordinate i).left ≫
                  (f i).left) ≫ (X i).hom := (Category.assoc _ _ _).symm
            _ = (pullback.snd (f i).left (coordinate i).left ≫
                  (coordinate i).left) ≫ (X i).hom := congrArg
              (fun a ↦ a ≫ (X i).hom) pullback.condition
            _ = pullback.snd (f i).left (coordinate i).left ≫
                  ((coordinate i).left ≫ (X i).hom) :=
              Category.assoc _ _ _
            _ = pullback.snd (f i).left (coordinate i).left ≫
                  zOver.hom := congrArg
              (fun a ↦ pullback.snd (f i).left (coordinate i).left ≫ a)
                (coordinate i).w
        calc
          (Pi.π pulled i).left ≫
              pullback.fst (f i).left (coordinate i).left ≫ (Y i).hom =
            (Pi.π pulled i).left ≫
              (pullback.fst (f i).left (coordinate i).left ≫
                (Y i).hom) := rfl
          _ = (Pi.π pulled i).left ≫
              (pullback.snd (f i).left (coordinate i).left ≫
                zOver.hom) := congrArg
            (fun a ↦ (Pi.π pulled i).left ≫ a) hInner
          _ = ((Pi.π pulled i).left ≫
              pullback.snd (f i).left (coordinate i).left) ≫
                zOver.hom := (Category.assoc _ _ _).symm
          _ = (∏ᶜ pulled).hom ≫ zOver.hom := congrArg
            (fun a ↦ a ≫ zOver.hom) (Pi.π pulled i).w)
  let mapY : QOverS ⟶ ∏ᶜ Y := Pi.lift qToY
  let zToProduct : zOver ⟶ ∏ᶜ X := Over.homMk zMap rfl
  have hqToY (i : Fin n) : qToY i ≫ f i = qToZ ≫ coordinate i := by
    apply Over.OverMorphism.ext
    change (Pi.π pulled i).left ≫
        pullback.fst (f i).left (coordinate i).left ≫ (f i).left =
      (∏ᶜ pulled).hom ≫ (coordinate i).left
    have h := pullback.condition (f := (f i).left) (g := (coordinate i).left)
    calc
      (Pi.π pulled i).left ≫
          pullback.fst (f i).left (coordinate i).left ≫ (f i).left =
        (Pi.π pulled i).left ≫
          (pullback.fst (f i).left (coordinate i).left ≫ (f i).left) :=
        rfl
      _ = (Pi.π pulled i).left ≫
          (pullback.snd (f i).left (coordinate i).left ≫
            (coordinate i).left) := congrArg
        (fun a ↦ (Pi.π pulled i).left ≫ a) h
      _ = ((Pi.π pulled i).left ≫
          pullback.snd (f i).left (coordinate i).left) ≫
            (coordinate i).left := (Category.assoc _ _ _).symm
      _ = (∏ᶜ pulled).hom ≫ (coordinate i).left := congrArg
        (fun a ↦ a ≫ (coordinate i).left) (Pi.π pulled i).w
  have hmap : mapY ≫ Limits.Pi.map f = qToZ ≫ zToProduct := by
    apply Pi.hom_ext
    intro i
    rw [Category.assoc, Limits.Pi.map_π, ← Category.assoc,
      Pi.lift_π, hqToY]
    rfl
  refine ⟨mapY.left q, ?_, ?_⟩
  · have hmapLeft := congrArg Over.Hom.left hmap
    have hmapPoint := congrArg
      (fun a : QOverS.left ⟶ (∏ᶜ X).left ↦ a q) hmapLeft
    change (Limits.Pi.map f).left (mapY.left q) = z
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hmapPoint]
    change zMap ((∏ᶜ pulled).hom q) = z
    rw [hqBase, zMap_zClosedPoint]
  · intro i
    change (mapY ≫ Pi.π Y i).left q = y i
    rw [Pi.lift_π]
    change pullback.fst (f i).left (coordinate i).left
      ((Pi.π pulled i).left q) = y i
    rw [hqProjection]
    exact pulledPoint_fst i

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

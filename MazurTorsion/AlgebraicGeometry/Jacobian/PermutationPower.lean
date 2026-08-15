/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeQuotient

/-!
# Permutation actions on relative powers

This file constructs the canonical action of `Equiv.Perm ι` on the relative
power of a scheme over a base.  It also records functoriality of the power map
as the equivariance statement consumed by the symmetric-power quotient.
-/

universe u

open CategoryTheory Limits

namespace MazurTorsion.AlgebraicGeometry.Jacobian.PermutationPower

open _root_.AlgebraicGeometry

variable (S : Scheme.{u}) (ι : Type) [Finite ι]

/-- The `ι`-fold relative power of `X` over `S`. -/
noncomputable abbrev power (X : Over S) : Over S :=
  ∏ᶜ fun _ : ι => X

/-- Reindexing the relative power by a permutation. -/
noncomputable def permutationHom (X : Over S) (g : Equiv.Perm ι) :
    power S ι X ⟶ power S ι X :=
  Limits.Pi.lift (fun i => Pi.π (fun _ : ι => X) (g i))

@[reassoc]
theorem permutationHom_comp_π (X : Over S) (g : Equiv.Perm ι) (i : ι) :
    permutationHom S ι X g ≫ Pi.π (fun _ : ι => X) i =
      Pi.π (fun _ : ι => X) (g i) := by
  exact Limits.Pi.lift_π (fun i => Pi.π (fun _ : ι => X) (g i)) i

theorem permutationHom_one (X : Over S) :
    permutationHom S ι X 1 = 𝟙 (power S ι X) := by
  apply Limits.Pi.hom_ext
  intro i
  rw [permutationHom_comp_π, Category.id_comp]
  rfl

theorem permutationHom_mul (X : Over S) (g h : Equiv.Perm ι) :
    permutationHom S ι X (g * h) =
      permutationHom S ι X g ≫ permutationHom S ι X h := by
  apply Limits.Pi.hom_ext
  intro i
  rw [Category.assoc, permutationHom_comp_π, permutationHom_comp_π,
    permutationHom_comp_π]
  rfl

/-- The permutation action on the underlying scheme of a relative power. -/
noncomputable def action (X : Over S) :
    SchemeAction (Equiv.Perm ι) (power S ι X).left where
  hom g := (permutationHom S ι X g).left
  hom_one := congrArg Over.Hom.left (permutationHom_one S ι X)
  hom_mul g h := congrArg Over.Hom.left (permutationHom_mul S ι X g h)

/-- Every permutation acts over the base. -/
theorem action_hom_comp_structureMap (X : Over S) (g : Equiv.Perm ι) :
    (action S ι X).hom g ≫ (power S ι X).hom = (power S ι X).hom := by
  exact (permutationHom S ι X g).w

/-- The map on relative powers induced componentwise by a morphism over the
base. -/
noncomputable def map {X Y : Over S} (f : X ⟶ Y) :
    power S ι X ⟶ power S ι Y :=
  Limits.Pi.map (fun _ : ι => f)

@[reassoc]
theorem map_comp_π {X Y : Over S} (f : X ⟶ Y) (i : ι) :
    map S ι f ≫ Pi.π (fun _ : ι => Y) i =
      Pi.π (fun _ : ι => X) i ≫ f := by
  change Limits.Pi.map (fun _ : ι => f) ≫ Pi.π (fun _ : ι => Y) i = _
  exact Limits.Pi.map_π (fun _ : ι => f) i

/-- Componentwise maps commute with permutation actions. -/
theorem action_equivariant {X Y : Over S} (f : X ⟶ Y) (g : Equiv.Perm ι) :
    (action S ι X).hom g ≫ (map S ι f).left =
      (map S ι f).left ≫ (action S ι Y).hom g := by
  have h : permutationHom S ι X g ≫ map S ι f =
      map S ι f ≫ permutationHom S ι Y g := by
    apply Limits.Pi.hom_ext
    intro i
    calc
      (permutationHom S ι X g ≫ map S ι f) ≫ Pi.π (fun _ : ι => Y) i =
          permutationHom S ι X g ≫ (Pi.π (fun _ : ι => X) i ≫ f) := by
            rw [Category.assoc, map_comp_π]
      _ = (permutationHom S ι X g ≫ Pi.π (fun _ : ι => X) i) ≫ f :=
        (Category.assoc _ _ _).symm
      _ = Pi.π (fun _ : ι => X) (g i) ≫ f := by
        rw [permutationHom_comp_π]
      _ = map S ι f ≫ Pi.π (fun _ : ι => Y) (g i) :=
        (map_comp_π S ι f (g i)).symm
      _ = (map S ι f ≫ permutationHom S ι Y g) ≫
          Pi.π (fun _ : ι => Y) i := by
        rw [Category.assoc, permutationHom_comp_π]
  simpa [action] using congrArg Over.Hom.left h

section FiniteMaps

/-- The product of two finite morphisms in a slice category is finite on
underlying schemes. -/
theorem binaryMap_isFinite {X₁ X₂ Y₁ Y₂ : Over S}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    [IsFinite f₁.left] [IsFinite f₂.left] :
    IsFinite (Limits.prod.map f₁ f₂).left := by
  let m := pullback.map X₁.hom X₂.hom Y₁.hom Y₂.hom
    f₁.left f₂.left (𝟙 S)
    ((Category.comp_id _).trans f₁.w.symm) ((Category.comp_id _).trans f₂.w.symm)
  have hm : IsFinite m := MorphismProperty.pullbackMap (P := @IsFinite)
    (f := X₁.hom) (g := X₂.hom) (f' := Y₁.hom) (g' := Y₂.hom)
    (i₁ := f₁.left) (i₂ := f₂.left) inferInstance inferInstance f₁.w.symm f₂.w.symm
  have heq : (Limits.prod.map f₁ f₂).left =
      (Over.prodLeftIsoPullback X₁ X₂).hom ≫ m ≫
        (Over.prodLeftIsoPullback Y₁ Y₂).inv := by
    rw [← cancel_mono (Over.prodLeftIsoPullback Y₁ Y₂).hom]
    apply pullback.hom_ext
    · simp only [Category.assoc, Over.prodLeftIsoPullback_hom_fst,
        Over.prodLeftIsoPullback_inv_fst]
      rw [show (Limits.prod.map f₁ f₂).left ≫ (Limits.prod.fst : (Y₁ ⨯ Y₂) ⟶ Y₁).left =
          (Limits.prod.fst : (X₁ ⨯ X₂) ⟶ X₁).left ≫ f₁.left from
        congrArg Over.Hom.left (Limits.prod.map_fst f₁ f₂)]
      dsimp [m, pullback.map]
      rw [pullback.lift_fst]
      simp
    · simp only [Category.assoc, Over.prodLeftIsoPullback_hom_snd,
        Over.prodLeftIsoPullback_inv_snd]
      rw [show (Limits.prod.map f₁ f₂).left ≫ (Limits.prod.snd : (Y₁ ⨯ Y₂) ⟶ Y₂).left =
          (Limits.prod.snd : (X₁ ⨯ X₂) ⟶ X₂).left ≫ f₂.left from
        congrArg Over.Hom.left (Limits.prod.map_snd f₁ f₂)]
      dsimp [m, pullback.map]
      rw [pullback.lift_snd]
      simp
  rw [heq]
  infer_instance

/-- Finiteness of an arrow over `S`, expressed as a morphism property on the
slice category. -/
abbrev overIsFinite : MorphismProperty (Over S) :=
  MorphismProperty.inverseImage (@IsFinite : MorphismProperty Scheme) (Over.forget S)

instance overIsFinite_respectsIso : (overIsFinite S).RespectsIso := by
  apply MorphismProperty.RespectsIso.inverseImage

/-- The object property on the arrow category selecting finite arrows over
`S`. -/
abbrev finiteArrow : ObjectProperty (Arrow (Over S)) :=
  (overIsFinite S).commaObj (Functor.id (Over S)) (Functor.id (Over S))

instance finiteArrow_isClosedUnderIsomorphisms :
    (finiteArrow S).IsClosedUnderIsomorphisms := by
  constructor
  intro X Y e h
  change overIsFinite S Y.hom
  change overIsFinite S X.hom at h
  letI := overIsFinite_respectsIso S
  exact ((overIsFinite S).comma_iso_iff e).mp h

instance finiteArrow_isClosedUnderEmpty :
    (finiteArrow S).IsClosedUnderLimitsOfShape (Discrete PEmpty) := by
  constructor
  rintro X p
  let t : IsTerminal X :=
    (ObjectProperty.limitsOfShape_isEmpty_iff (finiteArrow S) _ X).mp p |>.some
  let T : Arrow (Over S) := Arrow.mk (𝟙 (⊤_ (Over S)))
  let hT : IsTerminal T := IsTerminal.ofUniqueHom
      (fun X => Arrow.homMk (terminal.from X.left) (terminal.from X.right)
        (by apply terminal.hom_ext))
      (fun X f => by
        apply Arrow.hom_ext
        · exact terminal.hom_ext _ _
        · exact terminal.hom_ext _ _)
  let e : X ≅ T := t.uniqueUpToIso hT
  apply (finiteArrow_isClosedUnderIsomorphisms S).of_iso e.symm
  change IsFinite (𝟙 (⊤_ (Over S)).left)
  infer_instance

instance finiteArrow_isClosedUnderBinaryProducts :
    (finiteArrow S).IsClosedUnderBinaryProducts := by
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
  rintro X ⟨F, hF⟩
  let A := F.obj ⟨WalkingPair.left⟩
  let B := F.obj ⟨WalkingPair.right⟩
  let AB : Arrow (Over S) := Arrow.mk (Limits.prod.map A.hom B.hom)
  let fstAB : AB ⟶ A := Arrow.homMk Limits.prod.fst Limits.prod.fst (by
    change Limits.prod.fst ≫ A.hom = Limits.prod.map A.hom B.hom ≫ Limits.prod.fst
    rw [Limits.prod.map_fst])
  let sndAB : AB ⟶ B := Arrow.homMk Limits.prod.snd Limits.prod.snd (by
    change Limits.prod.snd ≫ B.hom = Limits.prod.map A.hom B.hom ≫ Limits.prod.snd
    rw [Limits.prod.map_snd])
  let c : BinaryFan A B := BinaryFan.mk fstAB sndAB
  let liftAB : ∀ {T : Arrow (Over S)}, (T ⟶ A) → (T ⟶ B) → (T ⟶ AB) :=
    fun {T} f g => Arrow.homMk
        (Limits.prod.lift f.left g.left)
        (Limits.prod.lift f.right g.right) (by
          change Limits.prod.lift f.left g.left ≫
              Limits.prod.map A.hom B.hom =
            T.hom ≫ Limits.prod.lift f.right g.right
          apply Limits.prod.hom_ext
          · calc
              (Limits.prod.lift f.left g.left ≫
                    Limits.prod.map A.hom B.hom) ≫ Limits.prod.fst =
                  Limits.prod.lift f.left g.left ≫
                    (Limits.prod.map A.hom B.hom ≫ Limits.prod.fst) :=
                Category.assoc _ _ _
              _ = Limits.prod.lift f.left g.left ≫
                    (Limits.prod.fst ≫ A.hom) := by rw [Limits.prod.map_fst]
              _ = (Limits.prod.lift f.left g.left ≫ Limits.prod.fst) ≫
                    A.hom := (Category.assoc _ _ _).symm
              _ = f.left ≫ A.hom := by rw [Limits.prod.lift_fst]
              _ = T.hom ≫ f.right := f.w
              _ = T.hom ≫
                    (Limits.prod.lift f.right g.right ≫ Limits.prod.fst) := by
                rw [Limits.prod.lift_fst]
              _ = (T.hom ≫ Limits.prod.lift f.right g.right) ≫
                    Limits.prod.fst := (Category.assoc _ _ _).symm
          · calc
              (Limits.prod.lift f.left g.left ≫
                    Limits.prod.map A.hom B.hom) ≫ Limits.prod.snd =
                  Limits.prod.lift f.left g.left ≫
                    (Limits.prod.map A.hom B.hom ≫ Limits.prod.snd) :=
                Category.assoc _ _ _
              _ = Limits.prod.lift f.left g.left ≫
                    (Limits.prod.snd ≫ B.hom) := by rw [Limits.prod.map_snd]
              _ = (Limits.prod.lift f.left g.left ≫ Limits.prod.snd) ≫
                    B.hom := (Category.assoc _ _ _).symm
              _ = g.left ≫ B.hom := by rw [Limits.prod.lift_snd]
              _ = T.hom ≫ g.right := g.w
              _ = T.hom ≫
                    (Limits.prod.lift f.right g.right ≫ Limits.prod.snd) := by
                rw [Limits.prod.lift_snd]
              _ = (T.hom ≫ Limits.prod.lift f.right g.right) ≫
                    Limits.prod.snd := (Category.assoc _ _ _).symm)
  have hc : IsLimit c := BinaryFan.IsLimit.mk c liftAB
    (by
      intro T f g
      change liftAB f g ≫ fstAB = f
      apply Arrow.hom_ext
      · change Limits.prod.lift f.left g.left ≫ Limits.prod.fst = f.left
        exact Limits.prod.lift_fst _ _
      · change Limits.prod.lift f.right g.right ≫ Limits.prod.fst = f.right
        exact Limits.prod.lift_fst _ _)
    (by
      intro T f g
      change liftAB f g ≫ sndAB = g
      apply Arrow.hom_ext
      · change Limits.prod.lift f.left g.left ≫ Limits.prod.snd = g.left
        exact Limits.prod.lift_snd _ _
      · change Limits.prod.lift f.right g.right ≫ Limits.prod.snd = g.right
        exact Limits.prod.lift_snd _ _)
    (by
      intro T f g m hm₁ hm₂
      apply Arrow.hom_ext
      · change m.left = Limits.prod.lift f.left g.left
        apply Limits.prod.hom_ext
        · rw [Limits.prod.lift_fst]
          have h := congrArg Arrow.Hom.left hm₁
          change m.left ≫ Limits.prod.fst = f.left at h
          exact h
        · rw [Limits.prod.lift_snd]
          have h := congrArg Arrow.Hom.left hm₂
          change m.left ≫ Limits.prod.snd = g.left at h
          exact h
      · change m.right = Limits.prod.lift f.right g.right
        apply Limits.prod.hom_ext
        · rw [Limits.prod.lift_fst]
          have h := congrArg Arrow.Hom.right hm₁
          change m.right ≫ Limits.prod.fst = f.right at h
          exact h
        · rw [Limits.prod.lift_snd]
          have h := congrArg Arrow.Hom.right hm₂
          change m.right ≫ Limits.prod.snd = g.right at h
          exact h)
  let e : limit F ≅ AB :=
    HasLimit.isoOfNatIso (diagramIsoPair F) ≪≫
      IsLimit.conePointUniqueUpToIso (limit.isLimit (pair A B)) hc
  apply (finiteArrow_isClosedUnderIsomorphisms S).of_iso e.symm
  change IsFinite (Limits.prod.map A.hom B.hom).left
  have hA : IsFinite A.hom.left := hF ⟨WalkingPair.left⟩
  have hB : IsFinite B.hom.left := hF ⟨WalkingPair.right⟩
  exact binaryMap_isFinite S A.hom B.hom

instance finiteArrow_isClosedUnderFiniteProducts :
    (finiteArrow S).IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

/-- A componentwise map on a finite relative power is finite when the
original map is finite. -/
theorem map_isFinite {X Y : Over S} (f : X ⟶ Y) [IsFinite f.left] :
    IsFinite (map S ι f).left := by
  let A : ι → Arrow (Over S) := fun _ => Arrow.mk f
  let Z : Arrow (Over S) := Arrow.mk (map S ι f)
  let p (i : ι) : Z ⟶ A i := Arrow.homMk
    (Pi.π (fun _ : ι => X) i) (Pi.π (fun _ : ι => Y) i) (by
      change Pi.π (fun _ : ι => X) i ≫ f =
        map S ι f ≫ Pi.π (fun _ : ι => Y) i
      rw [map_comp_π])
  let c : Fan A := Fan.mk Z p
  let q (s : Fan A) (i : ι) : s.pt ⟶ A i := s.proj i
  let liftZ (s : Fan A) : s.pt ⟶ Z := Arrow.homMk
    (Pi.lift fun i => (q s i).left) (Pi.lift fun i => (q s i).right) (by
      change (Pi.lift fun i => (q s i).left) ≫ map S ι f =
        s.pt.hom ≫ Pi.lift fun i => (q s i).right
      apply Pi.hom_ext
      intro i
      calc
        ((Pi.lift fun i => (q s i).left) ≫ map S ι f) ≫
              Pi.π (fun _ : ι => Y) i =
            (Pi.lift fun i => (q s i).left) ≫
              (map S ι f ≫ Pi.π (fun _ : ι => Y) i) :=
          Category.assoc _ _ _
        _ = (Pi.lift fun i => (q s i).left) ≫
              (Pi.π (fun _ : ι => X) i ≫ f) := by rw [map_comp_π]
        _ = ((Pi.lift fun i => (q s i).left) ≫
              Pi.π (fun _ : ι => X) i) ≫ f := (Category.assoc _ _ _).symm
        _ = (q s i).left ≫ f := by simp [A]
        _ = s.pt.hom ≫ (q s i).right := (q s i).w
        _ = (s.pt.hom ≫ Pi.lift fun i => (q s i).right) ≫
              Pi.π (fun _ : ι => Y) i := by
          simp [A])
  have hc : IsLimit c := Fan.IsLimit.mk c liftZ
    (by
      intro s i
      apply Arrow.hom_ext
      · change (Pi.lift fun j => (q s j).left) ≫
            Pi.π (fun _ : ι => X) i = (q s i).left
        exact Pi.lift_π _ _
      · change (Pi.lift fun j => (q s j).right) ≫
            Pi.π (fun _ : ι => Y) i = (q s i).right
        exact Pi.lift_π _ _)
    (by
      intro s m hm
      apply Arrow.hom_ext
      · change m.left = Pi.lift fun i => (q s i).left
        apply Pi.hom_ext
        intro i
        have h := congrArg Arrow.Hom.left (hm i)
        change m.left ≫ Pi.π (fun _ : ι => X) i = (q s i).left at h
        simpa [A] using h
      · change m.right = Pi.lift fun i => (q s i).right
        apply Pi.hom_ext
        intro i
        have h := congrArg Arrow.Hom.right (hm i)
        change m.right ≫ Pi.π (fun _ : ι => Y) i = (q s i).right at h
        simpa [A] using h)
  change finiteArrow S Z
  exact (finiteArrow S).prop_of_isLimit_fan hc
    (fun _ => show IsFinite f.left from inferInstance)

end FiniteMaps

end MazurTorsion.AlgebraicGeometry.Jacobian.PermutationPower

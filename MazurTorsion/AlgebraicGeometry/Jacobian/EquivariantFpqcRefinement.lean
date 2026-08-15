/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteEtaleRelativeProduct
import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteGroupQuotient

/-!
# Finite equivariant refinements of fpqc covers

Given a finite group action on `Y` and a cover `Z ⟶ Y`, take the relative
product of all target translates of the cover.  This common refinement is
again affine finite étale and surjective under the corresponding hypotheses.
Right translation of its factors gives self-maps covering the original
action, with the group law checked on every product projection.

The named downstream consumer is the block-stable occurrence chart in
`GeometricAssignedAffineChart`.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.EquivariantFpqcRefinement

open FiniteEtaleRelativeProduct

/-- Objects whose structure morphism is surjective. -/
abbrev surjectiveOver (S : Scheme.{u}) : ObjectProperty (Over S) :=
  fun X ↦ Surjective X.hom

instance surjectiveOver_isClosedUnderIsomorphisms (S : Scheme.{u}) :
    (surjectiveOver S).IsClosedUnderIsomorphisms := by
  constructor
  intro X Y e hX
  let eleft : Y.left ≅ X.left := (Over.forget S).mapIso e.symm
  letI : Surjective X.hom := hX
  have heq : eleft.hom ≫ X.hom = Y.hom := by
    change e.inv.left ≫ X.hom = Y.hom
    exact e.inv.w
  change Surjective Y.hom
  rw [← heq]
  infer_instance

/-- The relative binary product of surjective scheme morphisms is
surjective. -/
theorem binaryProduct_surjective (S : Scheme.{u}) (X Y : Over S)
    (hX : Surjective X.hom) (hY : Surjective Y.hom) :
    Surjective (X ⨯ Y).hom := by
  letI : Surjective X.hom := hX
  letI : Surjective Y.hom := hY
  letI : Surjective (pullback.fst X.hom Y.hom) :=
    MorphismProperty.pullback_fst (P := @Surjective) X.hom Y.hom hY
  have hcomp :
      (Over.prodLeftIsoPullback X Y).hom ≫
          (pullback.fst X.hom Y.hom ≫ X.hom) =
        (X ⨯ Y).hom := by
    rw [← Category.assoc, Over.prodLeftIsoPullback_hom_fst]
    exact (Limits.prod.fst : X ⨯ Y ⟶ X).w
  rw [← hcomp]
  infer_instance

instance surjectiveOver_isClosedUnderBinaryProducts (S : Scheme.{u}) :
    (surjectiveOver S).IsClosedUnderBinaryProducts := by
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
  rintro _ ⟨F, hF⟩
  let X := F.obj ⟨WalkingPair.left⟩
  let Y := F.obj ⟨WalkingPair.right⟩
  let e : limit F ≅ X ⨯ Y := HasLimit.isoOfNatIso (diagramIsoPair F)
  apply (surjectiveOver_isClosedUnderIsomorphisms S).of_iso e.symm
  exact binaryProduct_surjective S X Y
    (hF ⟨WalkingPair.left⟩) (hF ⟨WalkingPair.right⟩)

instance surjectiveOver_isClosedUnderEmpty (S : Scheme.{u}) :
    (surjectiveOver S).IsClosedUnderLimitsOfShape (Discrete PEmpty) := by
  constructor
  intro X p
  let hX : IsTerminal X :=
    (ObjectProperty.limitsOfShape_isEmpty_iff
      (surjectiveOver S) _ X).mp p |>.some
  let T : Over S := Over.mk (𝟙 S)
  let hT : IsTerminal T := IsTerminal.ofUniqueHom
    (fun Z ↦ Over.homMk Z.hom)
    (fun Z f ↦ Over.OverMorphism.ext (by simpa [T] using f.w))
  let e : X ≅ T := hX.uniqueUpToIso hT
  apply (surjectiveOver_isClosedUnderIsomorphisms S).of_iso e.symm
  change Surjective (𝟙 S)
  infer_instance

instance surjectiveOver_isClosedUnderFiniteProducts (S : Scheme.{u}) :
    (surjectiveOver S).IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

/-- A finite relative product of surjective scheme morphisms is
surjective. -/
theorem product_surjective (S : Scheme.{u}) {ι : Type} [Finite ι]
    (X : ι → Over S) (hX : ∀ i, Surjective (X i).hom) :
    Surjective (∏ᶜ X).hom :=
  (surjectiveOver S).prop_product hX

variable {G : Type} [Group G] [Finite G]
variable {Y Z : Scheme.{u}} (τ : SchemeAction G Y) (q : Z ⟶ Y)

/-- The cover translated by `g` on its target. -/
noncomputable def translate (g : G) : Over Y :=
  Over.mk (q ≫ τ.hom g)

/-- The common refinement of all target translates of the cover. -/
noncomputable abbrev refinement : Over Y :=
  ∏ᶜ fun g : G ↦ translate τ q g

instance translate_isFinite [IsFinite q] (g : G) :
    IsFinite (translate τ q g).hom := by
  change IsFinite (q ≫ τ.hom g)
  infer_instance

instance translate_etale [Etale q] (g : G) :
    Etale (translate τ q g).hom := by
  change Etale (q ≫ τ.hom g)
  infer_instance

instance translate_surjective [Surjective q] (g : G) :
    Surjective (translate τ q g).hom := by
  change Surjective (q ≫ τ.hom g)
  infer_instance

instance translate_quasiCompact [QuasiCompact q] (g : G) :
    QuasiCompact (translate τ q g).hom := by
  change QuasiCompact (q ≫ τ.hom g)
  infer_instance

instance refinement_isFinite [IsFinite q] [Etale q] :
    IsFinite (refinement τ q).hom := by
  change IsFinite (∏ᶜ fun g : G ↦ translate τ q g).hom
  exact (product_isFiniteEtale Y (fun g : G ↦ translate τ q g)
    (fun _ ↦ ⟨inferInstance, inferInstance⟩)).1

instance refinement_etale [IsFinite q] [Etale q] :
    Etale (refinement τ q).hom := by
  change Etale (∏ᶜ fun g : G ↦ translate τ q g).hom
  exact (product_isFiniteEtale Y (fun g : G ↦ translate τ q g)
    (fun _ ↦ ⟨inferInstance, inferInstance⟩)).2

instance refinement_surjective [Surjective q] :
    Surjective (refinement τ q).hom := by
  change Surjective (∏ᶜ fun g : G ↦ translate τ q g).hom
  exact product_surjective Y (fun g : G ↦ translate τ q g)
    (fun _ ↦ inferInstance)

instance refinement_isAffine [IsAffine Y] [IsAffine Z] :
    IsAffine (refinement τ q).left := by
  change IsAffine (∏ᶜ fun g : G ↦ translate τ q g).left
  exact product_isAffine Y (fun g : G ↦ translate τ q g)
    (fun _ ↦ by change IsAffine Z; infer_instance)

/-- The common translate refinement of an affine finite étale surjective
cover is again affine, finite étale, and fpqc. -/
theorem refinement_isAffine_finiteEtale_fpqc
    [IsAffine Y] [IsAffine Z] [IsFinite q] [Etale q] [Surjective q] :
    IsAffine (refinement τ q).left ∧
      IsFinite (refinement τ q).hom ∧ Etale (refinement τ q).hom ∧
        Flat (refinement τ q).hom ∧ Surjective (refinement τ q).hom ∧
          QuasiCompact (refinement τ q).hom :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance⟩

/-- Regard the common refinement as lying over the target translated by
`h`. -/
noncomputable abbrev actionSource (h : G) : Over Y :=
  ⟨(refinement τ q).left, ⟨⟨⟩⟩,
    (refinement τ q).hom ≫ τ.hom h⟩

/-- The `g`-th leg of the action by `h` is the factor indexed by
`g * h⁻¹`. -/
noncomputable def actionLeg (h g : G) :
    actionSource τ q h ⟶ translate τ q g :=
  Over.homMk
    (Pi.π (fun k : G ↦ translate τ q k) (g * h⁻¹)).left (by
      have hk := (Pi.π (fun k : G ↦ translate τ q k) (g * h⁻¹)).w
      change
        (Pi.π (fun k : G ↦ translate τ q k) (g * h⁻¹)).left ≫
            q ≫ τ.hom (g * h⁻¹) =
          (refinement τ q).hom at hk
      change
        (Pi.π (fun k : G ↦ translate τ q k) (g * h⁻¹)).left ≫
            q ≫ τ.hom g =
          (refinement τ q).hom ≫ τ.hom h
      have hgh : (g * h⁻¹) * h = g := by simp
      calc
        _ = (Pi.π (fun k : G ↦ translate τ q k) (g * h⁻¹)).left ≫
              q ≫ τ.hom ((g * h⁻¹) * h) := by rw [hgh]
        _ = (Pi.π (fun k : G ↦ translate τ q k) (g * h⁻¹)).left ≫
              q ≫ (τ.hom (g * h⁻¹) ≫ τ.hom h) := by rw [τ.hom_mul]
        _ = ((Pi.π (fun k : G ↦ translate τ q k) (g * h⁻¹)).left ≫
              q ≫ τ.hom (g * h⁻¹)) ≫ τ.hom h := by
          exact congrArg (fun r => r ≫ τ.hom h)
            (Category.assoc
              (Pi.π (fun k : G ↦ translate τ q k) (g * h⁻¹)).left
              q (τ.hom (g * h⁻¹)))
        _ = (refinement τ q).hom ≫ τ.hom h := by rw [hk])

/-- Right translation of factors defines the action map on the common
refinement. -/
noncomputable def actionHom (h : G) : actionSource τ q h ⟶ refinement τ q :=
  Pi.lift (actionLeg τ q h)

/-- The action source has the same underlying scheme as the refinement. -/
theorem actionSource_left (h : G) :
    (actionSource τ q h).left = (refinement τ q).left :=
  rfl

theorem eqToHom_actionSource_left_symm (h : G) :
    eqToHom (actionSource_left τ q h).symm =
      𝟙 (refinement τ q).left := by
  rfl

/-- The underlying self-map of the common refinement. -/
noncomputable def rawActionHom (h : G) :
    (refinement τ q).left ⟶ (refinement τ q).left :=
  eqToHom (actionSource_left τ q h).symm ≫ (actionHom τ q h).left

/-- The underlying projection to the common source scheme of every
translated factor. -/
noncomputable def projection (g : G) : (refinement τ q).left ⟶ Z :=
  (Pi.π (fun k : G ↦ translate τ q k) g).left

/-- The identity-indexed projection exhibits the common refinement as a
refinement of the original cover. -/
theorem projection_one_comp_cover :
    projection τ q 1 ≫ q = (refinement τ q).hom := by
  have h := (Pi.π (fun k : G ↦ translate τ q k) 1).w
  change projection τ q 1 ≫ q ≫ τ.hom 1 =
    (refinement τ q).hom at h
  rw [τ.hom_one, Category.comp_id] at h
  exact h

@[reassoc]
theorem actionHom_comp_projection (h g : G) :
    rawActionHom τ q h ≫
        projection τ q g = projection τ q (g * h⁻¹) := by
  simp only [rawActionHom, Category.assoc]
  rw [eqToHom_refl, Category.id_comp]
  exact congrArg Over.Hom.left (Pi.lift_π (actionLeg τ q h) g)

/-- The action self-map covers the corresponding target action. -/
theorem rawActionHom_comp_cover (h : G) :
    rawActionHom τ q h ≫ (refinement τ q).hom =
      (refinement τ q).hom ≫ τ.hom h := by
  unfold rawActionHom
  rw [eqToHom_actionSource_left_symm, Category.id_comp]
  exact (actionHom τ q h).w

/-- Change the target twist from `h * k` to `k` by the action map for
`h`. -/
noncomputable def actionTransition (h k : G) :
    actionSource τ q (h * k) ⟶ actionSource τ q k :=
  Over.homMk (rawActionHom τ q h) (by
    calc
      rawActionHom τ q h ≫ (actionSource τ q k).hom =
          rawActionHom τ q h ≫
            ((refinement τ q).hom ≫ τ.hom k) := rfl
      _ = (rawActionHom τ q h ≫ (refinement τ q).hom) ≫
            τ.hom k := (Category.assoc _ _ _).symm
      _ = ((refinement τ q).hom ≫ τ.hom h) ≫ τ.hom k := by
        rw [rawActionHom_comp_cover]
      _ = (actionSource τ q (h * k)).hom := by
        change ((refinement τ q).hom ≫ τ.hom h) ≫ τ.hom k =
          (refinement τ q).hom ≫ τ.hom (h * k)
        rw [τ.hom_mul, Category.assoc])

/-- The right-translation maps satisfy multiplication on every product
projection. -/
theorem rawActionHom_mul_comp_projection (h k g : G) :
    rawActionHom τ q (h * k) ≫ projection τ q g =
      (rawActionHom τ q h ≫ rawActionHom τ q k) ≫
        projection τ q g := by
  have hidx : g * (h * k)⁻¹ = (g * k⁻¹) * h⁻¹ := by
    simp only [mul_inv_rev, mul_assoc]
  calc
    _ = projection τ q (g * (h * k)⁻¹) :=
      actionHom_comp_projection τ q (h * k) g
    _ = projection τ q ((g * k⁻¹) * h⁻¹) := by
      exact congrArg (projection τ q) hidx
    _ = rawActionHom τ q h ≫ projection τ q (g * k⁻¹) :=
      (actionHom_comp_projection τ q h (g * k⁻¹)).symm
    _ = rawActionHom τ q h ≫
          (rawActionHom τ q k ≫ projection τ q g) := by
      exact congrArg (fun r => rawActionHom τ q h ≫ r)
        (actionHom_comp_projection τ q k g).symm
    _ = (rawActionHom τ q h ≫ rawActionHom τ q k) ≫
          projection τ q g := (Category.assoc _ _ _).symm

end MazurTorsion.AlgebraicGeometry.Jacobian.EquivariantFpqcRefinement

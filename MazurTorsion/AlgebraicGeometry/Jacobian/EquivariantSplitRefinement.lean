/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.EquivariantFpqcRefinement
import MazurTorsion.AlgebraicGeometry.Jacobian.SplitFiniteBaseChange

/-!
# Split finite covers on an equivariant fpqc refinement

An affine finite cover split by one fpqc chart remains split after pulling
that chart to the common refinement of all its finite-group translates.
This file packages the transported slice isomorphism and the canonical map
from its source back to the original finite cover.

The named downstream consumer is the block-stable occurrence chart in
`GeometricAssignedAffineChart`.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.EquivariantSplitRefinement

open EquivariantFpqcRefinement
open SplitFiniteBaseChange

variable {G : Type} [Group G] [Finite G]
variable {R : Type u} [CommRing R]
variable {X Y : Scheme.{u}} (τ : SchemeAction G Y)
variable (f : X ⟶ Y) (q : Spec (.of R) ⟶ Y)

/-- The base change of the originally split source from the chosen cover to
the common translate refinement. -/
noncomputable abbrev splitSource : Over (refinement τ q).left :=
  (Over.pullback (projection τ q 1)).obj
    (Over.mk (pullback.snd f q))

/-- Pulling a chosen split presentation along the identity projection keeps
the source split over the common translate refinement. -/
noncomputable def splitIso (m : ℕ)
    (E : pullback f q ≅ Spec (.of (Fin m → R)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection R m =
      pullback.snd f q) :
    splitSource τ f q ≅ splitFinite (refinement τ q).left m :=
  baseChangeSplitChartIso R (refinement τ q).left
    (projection τ q 1) m (Over.mk (pullback.snd f q)) E hE

/-- The transported split isomorphism respects the structural map to the
common refinement. -/
@[reassoc]
theorem splitIso_hom_comp_projection (m : ℕ)
    (E : pullback f q ≅ Spec (.of (Fin m → R)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection R m =
      pullback.snd f q) :
    (splitIso τ f q m E hE).hom.left ≫
        (splitFinite (refinement τ q).left m).hom =
      (splitSource τ f q).hom :=
  baseChangeSplitChartIso_hom_comp_projection R
    (refinement τ q).left (projection τ q 1) m
    (Over.mk (pullback.snd f q)) E hE

/-- The twice-pulled source maps canonically back to the original source. -/
noncomputable def splitSourceToOriginal :
    (splitSource τ f q).left ⟶ X :=
  pullback.fst (pullback.snd f q) (projection τ q 1) ≫
    pullback.fst f q

/-- The map to the original source lies over the common-refinement map to
the original target. -/
@[reassoc]
theorem splitSourceToOriginal_comp :
    splitSourceToOriginal τ f q ≫ f =
      (splitSource τ f q).hom ≫ (refinement τ q).hom := by
  rw [splitSourceToOriginal, Category.assoc, pullback.condition]
  change
    pullback.fst (pullback.snd f q) (projection τ q 1) ≫
          pullback.snd f q ≫ q =
      pullback.snd (pullback.snd f q) (projection τ q 1) ≫
        (refinement τ q).hom
  rw [← Category.assoc, pullback.condition, Category.assoc,
    projection_one_comp_cover]

omit [Finite G] in
/-- Restricting an equivariant morphism to a stable target open and its
stable source preimage preserves equivariance. -/
theorem restrictPreimage_equivariant
    (σ : SchemeAction G X)
    (hf : ∀ g : G, σ.hom g ≫ f = f ≫ τ.hom g)
    {U : Y.Opens} (hU : τ.IsStableOpen U)
    (hpre : σ.IsStableOpen (f ⁻¹ᵁ U)) (g : G) :
    (σ.restrict hpre).hom g ≫ (f ∣_ U) =
      (f ∣_ U) ≫ (τ.restrict hU).hom g := by
  have hfU : (f ∣_ U) ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f :=
    morphismRestrict_ι f U
  have hs : (σ.restrict hpre).hom g ≫ (f ⁻¹ᵁ U).ι =
      (f ⁻¹ᵁ U).ι ≫ σ.hom g := by
    simpa only [SchemeAction.restrict_hom] using
      Scheme.Hom.resLE_comp_ι (σ.hom g) (hpre.le_preimage g)
  have ht : (τ.restrict hU).hom g ≫ U.ι = U.ι ≫ τ.hom g := by
    simpa only [SchemeAction.restrict_hom] using
      Scheme.Hom.resLE_comp_ι (τ.hom g) (hU.le_preimage g)
  apply (cancel_mono U.ι).mp
  calc
    ((σ.restrict hpre).hom g ≫ (f ∣_ U)) ≫ U.ι =
        (σ.restrict hpre).hom g ≫ ((f ∣_ U) ≫ U.ι) :=
      Category.assoc _ _ _
    _ = (σ.restrict hpre).hom g ≫ ((f ⁻¹ᵁ U).ι ≫ f) := by
      rw [hfU]
    _ = ((σ.restrict hpre).hom g ≫ (f ⁻¹ᵁ U).ι) ≫ f :=
      (Category.assoc _ _ _).symm
    _ = ((f ⁻¹ᵁ U).ι ≫ σ.hom g) ≫ f := by rw [hs]
    _ = (f ⁻¹ᵁ U).ι ≫ (σ.hom g ≫ f) := Category.assoc _ _ _
    _ = (f ⁻¹ᵁ U).ι ≫ (f ≫ τ.hom g) := by rw [hf]
    _ = ((f ⁻¹ᵁ U).ι ≫ f) ≫ τ.hom g :=
      (Category.assoc _ _ _).symm
    _ = ((f ∣_ U) ≫ U.ι) ≫ τ.hom g := by rw [hfU]
    _ = (f ∣_ U) ≫ (U.ι ≫ τ.hom g) := Category.assoc _ _ _
    _ = (f ∣_ U) ≫ ((τ.restrict hU).hom g ≫ U.ι) := by rw [ht]
    _ = ((f ∣_ U) ≫ (τ.restrict hU).hom g) ≫ U.ι :=
      (Category.assoc _ _ _).symm

/-- The direct pullback of the original source to the common refinement,
written using the identity-indexed projection.  Unlike the iterated
`splitSource`, this presentation is convenient for inducing an action from
an equivariant source morphism. -/
noncomputable abbrev directSource : Over (refinement τ q).left :=
  Over.mk (pullback.snd f (projection τ q 1 ≫ q))

/-- Pullback associativity identifies the iterated transported source with
the direct pullback source. -/
noncomputable def splitSourceDirectIso :
    splitSource τ f q ≅ directSource τ f q :=
  Over.isoMk
    (pullbackLeftPullbackSndIso f q (projection τ q 1))
    (pullbackLeftPullbackSndIso_hom_snd f q (projection τ q 1))

/-- The direct source therefore inherits the finite split presentation. -/
noncomputable def directSplitIso (m : ℕ)
    (E : pullback f q ≅ Spec (.of (Fin m → R)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection R m =
      pullback.snd f q) :
    directSource τ f q ≅ splitFinite (refinement τ q).left m :=
  (splitSourceDirectIso τ f q).symm ≪≫ splitIso τ f q m E hE

/-- A point of the original finite source and a point of the common
refinement with the same image determine an actual sheet in the transported
split presentation.  The conclusion retains both the chosen source point and
the chosen refinement point exactly. -/
theorem exists_splitSheet_over_point (m : ℕ)
    (E : pullback f q ≅ Spec (.of (Fin m → R)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection R m =
      pullback.snd f q)
    (x : X) (s : (refinement τ q).left)
    (hxs : f x = (refinement τ q).hom s) :
    ∃ j : Fin m,
      pullback.fst f (projection τ q 1 ≫ q)
          ((directSplitIso τ f q m E hE).inv.left
            ((sheetInclusion (refinement τ q).left m j).left s)) = x := by
  obtain ⟨w, hwx, hws⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback f (projection τ q 1 ≫ q)) x s (by
      rw [projection_one_comp_cover]
      exact hxs)
  let y : (splitFinite (refinement τ q).left m).left :=
    (directSplitIso τ f q m E hE).hom.left w
  let j : Fin m := splitPointSheet (refinement τ q).left m
    (splitFinite (refinement τ q).left m) (Iso.refl _) y
  have hstruct : (splitFinite (refinement τ q).left m).hom y = s := by
    have hw := congrArg (fun e ↦ e w)
      (directSplitIso τ f q m E hE).hom.w
    change (splitFinite (refinement τ q).left m).hom y =
      pullback.snd f (projection τ q 1 ≫ q) w at hw
    exact hw.trans hws
  have hy := splitPoint_decomposition (refinement τ q).left m
    (splitFinite (refinement τ q).left m) (Iso.refl _) y
  have hbase : splitPointBase (refinement τ q).left m
      (splitFinite (refinement τ q).left m) (Iso.refl _) y = s := by
    have hp := congrArg
      (splitFinite (refinement τ q).left m).hom hy
    have hj := congrArg
      (fun e ↦ e (splitPointBase (refinement τ q).left m
        (splitFinite (refinement τ q).left m) (Iso.refl _) y))
      (sheetInclusion (refinement τ q).left m j).w
    change (splitFinite (refinement τ q).left m).hom
        ((sheetInclusion (refinement τ q).left m j).left
          (splitPointBase (refinement τ q).left m
            (splitFinite (refinement τ q).left m) (Iso.refl _) y)) =
      splitPointBase (refinement τ q).left m
        (splitFinite (refinement τ q).left m) (Iso.refl _) y at hj
    rw [hj] at hp
    exact hp.symm.trans hstruct
  change y = (sheetInclusion (refinement τ q).left m j).left
      (splitPointBase (refinement τ q).left m
        (splitFinite (refinement τ q).left m) (Iso.refl _) y) at hy
  rw [hbase] at hy
  refine ⟨j, ?_⟩
  rw [← hy]
  have hback := congrArg (fun e ↦ e w)
    (congrArg Over.Hom.left
      (directSplitIso τ f q m E hE).hom_inv_id)
  change (directSplitIso τ f q m E hE).inv.left y = w at hback
  rw [hback, hwx]

/-- The identity-indexed presentation of the refinement map is equivariant
for the genuine refinement action. -/
theorem directBase_equivariant (g : G) :
    (refinementAction τ q).hom g ≫ (projection τ q 1 ≫ q) =
      (projection τ q 1 ≫ q) ≫ τ.hom g := by
  change rawActionHom τ q g ≫ (projection τ q 1 ≫ q) =
    (projection τ q 1 ≫ q) ≫ τ.hom g
  rw [projection_one_comp_cover, rawActionHom_comp_cover]

variable (σ : SchemeAction G X)
variable (hf : ∀ g : G, σ.hom g ≫ f = f ≫ τ.hom g)

/-- The action induced on the direct pullback of an equivariant source
morphism. -/
noncomputable def directActionHom (g : G) :
    (directSource τ f q).left ⟶ (directSource τ f q).left :=
  pullback.map f (projection τ q 1 ≫ q)
    f (projection τ q 1 ≫ q)
    (σ.hom g) ((refinementAction τ q).hom g) (τ.hom g)
    (hf g).symm (directBase_equivariant τ q g).symm

/-- The induced action map covers the source action. -/
@[reassoc]
theorem directActionHom_fst (g : G) :
    directActionHom τ f q σ hf g ≫
        pullback.fst f (projection τ q 1 ≫ q) =
      pullback.fst f (projection τ q 1 ≫ q) ≫ σ.hom g := by
  exact pullback.lift_fst _ _ _

/-- The induced action map covers the genuine action on the common
refinement. -/
@[reassoc]
theorem directActionHom_snd (g : G) :
    directActionHom τ f q σ hf g ≫
        pullback.snd f (projection τ q 1 ≫ q) =
      pullback.snd f (projection τ q 1 ≫ q) ≫
        (refinementAction τ q).hom g := by
  exact pullback.lift_snd _ _ _

/-- The direct pullback of an equivariant source carries the induced group
action. -/
noncomputable def directAction :
    SchemeAction G (directSource τ f q).left where
  hom := directActionHom τ f q σ hf
  hom_one := by
    apply pullback.hom_ext
    · rw [directActionHom_fst, σ.hom_one, Category.comp_id,
        Category.id_comp]
    · rw [directActionHom_snd, (refinementAction τ q).hom_one,
        Category.comp_id, Category.id_comp]
  hom_mul g h := by
    apply pullback.hom_ext
    · rw [directActionHom_fst, Category.assoc, directActionHom_fst,
        ← Category.assoc, directActionHom_fst, Category.assoc, σ.hom_mul]
    · rw [directActionHom_snd, Category.assoc, directActionHom_snd,
        ← Category.assoc, directActionHom_snd, Category.assoc,
        (refinementAction τ q).hom_mul]

/-- Transport the induced action through a chosen split presentation. -/
noncomputable def splitAction (m : ℕ)
    (E : pullback f q ≅ Spec (.of (Fin m → R)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection R m =
      pullback.snd f q) :
    SchemeAction G (splitFinite (refinement τ q).left m).left :=
  (directAction τ f q σ hf).transport
    ((Over.forget (refinement τ q).left).mapIso
      (directSplitIso τ f q m E hE))

/-- The transported action on the split finite source covers the action on
the common refinement. -/
theorem splitAction_equivariant (m : ℕ)
    (E : pullback f q ≅ Spec (.of (Fin m → R)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection R m =
      pullback.snd f q) (g : G) :
    (splitAction τ f q σ hf m E hE).hom g ≫
        (splitFinite (refinement τ q).left m).hom =
      (splitFinite (refinement τ q).left m).hom ≫
        (refinementAction τ q).hom g := by
  change
    (directSplitIso τ f q m E hE).inv.left ≫
          (directAction τ f q σ hf).hom g ≫
          (directSplitIso τ f q m E hE).hom.left ≫
          (splitFinite (refinement τ q).left m).hom =
      (splitFinite (refinement τ q).left m).hom ≫
        (refinementAction τ q).hom g
  calc
    _ = (directSplitIso τ f q m E hE).inv.left ≫
          (directAction τ f q σ hf).hom g ≫
            ((directSplitIso τ f q m E hE).hom.left ≫
              (splitFinite (refinement τ q).left m).hom) := by
        rfl
    _ = (directSplitIso τ f q m E hE).inv.left ≫
          (directAction τ f q σ hf).hom g ≫
            (directSource τ f q).hom := by
        rw [(directSplitIso τ f q m E hE).hom.w]
    _ = (directSplitIso τ f q m E hE).inv.left ≫
          ((directAction τ f q σ hf).hom g ≫
            (directSource τ f q).hom) := by
        rfl
    _ = (directSplitIso τ f q m E hE).inv.left ≫
          ((directSource τ f q).hom ≫
            (refinementAction τ q).hom g) := by
        change
          (directSplitIso τ f q m E hE).inv.left ≫
              (directActionHom τ f q σ hf g ≫
                pullback.snd f (projection τ q 1 ≫ q)) =
            (directSplitIso τ f q m E hE).inv.left ≫
              (pullback.snd f (projection τ q 1 ≫ q) ≫
                (refinementAction τ q).hom g)
        rw [directActionHom_snd]
    _ = ((directSplitIso τ f q m E hE).inv.left ≫
          (directSource τ f q).hom) ≫
            (refinementAction τ q).hom g := by
        simp only [Category.assoc]
    _ = (splitFinite (refinement τ q).left m).hom ≫
          (refinementAction τ q).hom g := by
        rw [(directSplitIso τ f q m E hE).inv.w]

/-- The map from the transported split presentation back to the original
finite source is equivariant. -/
theorem splitAction_toOriginal_equivariant (m : ℕ)
    (E : pullback f q ≅ Spec (.of (Fin m → R)))
    (hE : E.hom ≫ EtaleSplitChart.splitProjection R m =
      pullback.snd f q) (g : G) :
    (splitAction τ f q σ hf m E hE).hom g ≫
          (directSplitIso τ f q m E hE).inv.left ≫
          pullback.fst f (projection τ q 1 ≫ q) =
      (directSplitIso τ f q m E hE).inv.left ≫
          pullback.fst f (projection τ q 1 ≫ q) ≫ σ.hom g := by
  change
    (directSplitIso τ f q m E hE).inv.left ≫
        (directAction τ f q σ hf).hom g ≫
        (directSplitIso τ f q m E hE).hom.left ≫
        (directSplitIso τ f q m E hE).inv.left ≫
        pullback.fst f (projection τ q 1 ≫ q) = _
  have he := congrArg Over.Hom.left
    (directSplitIso τ f q m E hE).hom_inv_id
  change (directSplitIso τ f q m E hE).hom.left ≫
    (directSplitIso τ f q m E hE).inv.left =
      𝟙 (directSource τ f q).left at he
  calc
    _ = (directSplitIso τ f q m E hE).inv.left ≫
        (directAction τ f q σ hf).hom g ≫
          (((directSplitIso τ f q m E hE).hom.left ≫
            (directSplitIso τ f q m E hE).inv.left) ≫
              pullback.fst f (projection τ q 1 ≫ q)) := by
        simp only [Category.assoc]
    _ = (directSplitIso τ f q m E hE).inv.left ≫
        (directAction τ f q σ hf).hom g ≫
          pullback.fst f (projection τ q 1 ≫ q) := by
        rw [he, Category.id_comp]
    _ = (directSplitIso τ f q m E hE).inv.left ≫
        pullback.fst f (projection τ q 1 ≫ q) ≫ σ.hom g := by
        change (directSplitIso τ f q m E hE).inv.left ≫
          directActionHom τ f q σ hf g ≫
            pullback.fst f (projection τ q 1 ≫ q) = _
        rw [directActionHom_fst]

end MazurTorsion.AlgebraicGeometry.Jacobian.EquivariantSplitRefinement

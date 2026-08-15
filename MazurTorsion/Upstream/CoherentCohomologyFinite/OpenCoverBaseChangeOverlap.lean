/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Pair and triple overlaps under base change of an open cover

For an open cover `𝒰` of `S` and a morphism `f : T ⟶ S`, every chart of
the pulled-back cover maps to the corresponding chart of `𝒰`.  This file
packages the induced maps on pair and triple overlaps and records their
projection compatibilities.
-/


open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Cover

variable {S T : Scheme.{u}} (𝒰 : S.OpenCover) (f : T ⟶ S)

/-- The first projection from a pairwise overlap, with the cover indices
exposed in its public type. -/
abbrev overlapFst (𝒰 : S.OpenCover) (i j : 𝒰.I₀) :
    𝒰.gluedCover.V (i, j) ⟶ 𝒰.X i :=
  𝒰.gluedCover.f i j

/-- The second projection from a pairwise overlap, with the cover indices
exposed in its public type. -/
abbrev overlapSnd (𝒰 : S.OpenCover) (i j : 𝒰.I₀) :
    𝒰.gluedCover.V (i, j) ⟶ 𝒰.X j :=
  pullback.snd (𝒰.f i) (𝒰.f j)

/-- The target-chart leg used by glue-data transitions, with the cover
indices exposed in its public type. -/
abbrev overlapTarget (𝒰 : S.OpenCover) (i j : 𝒰.I₀) :
    𝒰.gluedCover.V (i, j) ⟶ 𝒰.X j :=
  𝒰.gluedCover.t i j ≫ 𝒰.gluedCover.f j i

local instance pulledBackOpenCoverMapIsOpenImmersion
    (i : 𝒰.I₀) : IsOpenImmersion ((𝒰.pullback₁ f).f i) :=
  Scheme.Cover.map_prop (𝒰.pullback₁ f) i

local instance openCoverGluedCoverMapIsOpenImmersion
    {X : Scheme.{u}} (𝒱 : X.OpenCover) (i j : 𝒱.I₀) :
    IsOpenImmersion (𝒱.gluedCover.f i j) := by
  change IsOpenImmersion (pullback.fst (𝒱.f i) (𝒱.f j))
  infer_instance

local instance pulledBackOpenCoverGluedCoverMapIsOpenImmersion
    (i j : 𝒰.I₀) :
    IsOpenImmersion ((gluedCover (𝒰.pullback₁ f)).f i j) := by
  change IsOpenImmersion
    (pullback.fst ((𝒰.pullback₁ f).f i) ((𝒰.pullback₁ f).f j))
  infer_instance

/-- The canonical map from an overlap of the pulled-back cover to the
corresponding overlap of the original cover. -/
def baseChangeOverlapMap (i j : 𝒰.I₀) :
    (gluedCover (𝒰.pullback₁ f)).V (i, j) ⟶
      𝒰.gluedCover.V (i, j) := by
  refine pullback.lift
    (pullback.fst
      ((𝒰.pullback₁ f).f i) ((𝒰.pullback₁ f).f j) ≫
        𝒰.pullbackHom f i)
    (pullback.snd
      ((𝒰.pullback₁ f).f i) ((𝒰.pullback₁ f).f j) ≫
        𝒰.pullbackHom f j) ?_
  calc
    (pullback.fst
          ((𝒰.pullback₁ f).f i) ((𝒰.pullback₁ f).f j) ≫
        𝒰.pullbackHom f i) ≫ 𝒰.f i =
      pullback.fst
          ((𝒰.pullback₁ f).f i) ((𝒰.pullback₁ f).f j) ≫
        (𝒰.pullbackHom f i ≫ 𝒰.f i) :=
      Category.assoc _ _ _
    _ = pullback.fst
          ((𝒰.pullback₁ f).f i) ((𝒰.pullback₁ f).f j) ≫
        ((𝒰.pullback₁ f).f i ≫ f) :=
      CategoryTheory.whisker_eq _ (𝒰.pullbackHom_map f i)
    _ = pullback.snd
          ((𝒰.pullback₁ f).f i) ((𝒰.pullback₁ f).f j) ≫
        ((𝒰.pullback₁ f).f j ≫ f) :=
      pullback.condition_assoc
        (f := (𝒰.pullback₁ f).f i)
        (g := (𝒰.pullback₁ f).f j) f
    _ = pullback.snd
          ((𝒰.pullback₁ f).f i) ((𝒰.pullback₁ f).f j) ≫
        (𝒰.pullbackHom f j ≫ 𝒰.f j) :=
      CategoryTheory.whisker_eq _ (𝒰.pullbackHom_map f j).symm
    _ = (pullback.snd
          ((𝒰.pullback₁ f).f i) ((𝒰.pullback₁ f).f j) ≫
        𝒰.pullbackHom f j) ≫ 𝒰.f j :=
      (Category.assoc _ _ _).symm

@[simp, reassoc]
theorem baseChangeOverlapMap_fst (i j : 𝒰.I₀) :
    baseChangeOverlapMap 𝒰 f i j ≫
        pullback.fst (𝒰.f i) (𝒰.f j) =
      pullback.fst
          ((𝒰.pullback₁ f).f i)
          ((𝒰.pullback₁ f).f j) ≫
        𝒰.pullbackHom f i :=
  pullback.lift_fst _ _ _

@[simp, reassoc]
theorem baseChangeOverlapMap_snd (i j : 𝒰.I₀) :
    baseChangeOverlapMap 𝒰 f i j ≫
        pullback.snd (𝒰.f i) (𝒰.f j) =
      pullback.snd
          ((𝒰.pullback₁ f).f i)
          ((𝒰.pullback₁ f).f j) ≫
        𝒰.pullbackHom f j :=
  pullback.lift_snd _ _ _

@[simp, reassoc]
theorem baseChangeOverlapMap_gluedCover_f (i j : 𝒰.I₀) :
    baseChangeOverlapMap 𝒰 f i j ≫
        𝒰.gluedCover.f i j =
      (gluedCover (𝒰.pullback₁ f)).f i j ≫
        𝒰.pullbackHom f i := by
  change
    baseChangeOverlapMap 𝒰 f i j ≫
        pullback.fst (𝒰.f i) (𝒰.f j) =
      pullback.fst
          ((𝒰.pullback₁ f).f i)
          ((𝒰.pullback₁ f).f j) ≫
        𝒰.pullbackHom f i
  exact baseChangeOverlapMap_fst 𝒰 f i j

@[simp, reassoc]
theorem baseChangeOverlapMap_overlapFst (i j : 𝒰.I₀) :
    baseChangeOverlapMap 𝒰 f i j ≫ overlapFst 𝒰 i j =
      overlapFst (𝒰.pullback₁ f) i j ≫
        𝒰.pullbackHom f i :=
  baseChangeOverlapMap_gluedCover_f 𝒰 f i j

@[simp, reassoc]
theorem baseChangeOverlapMap_overlapSnd (i j : 𝒰.I₀) :
    baseChangeOverlapMap 𝒰 f i j ≫ overlapSnd 𝒰 i j =
      overlapSnd (𝒰.pullback₁ f) i j ≫
        𝒰.pullbackHom f j :=
  baseChangeOverlapMap_snd 𝒰 f i j

/-- The map on triple overlaps induced by the pair-overlap maps on its two
legs out of the distinguished `i`-chart. -/
def baseChangeTripleOverlapMap (i j k : 𝒰.I₀) :
    pullback
        ((gluedCover (𝒰.pullback₁ f)).f i j)
        ((gluedCover (𝒰.pullback₁ f)).f i k) ⟶
      pullback
        (𝒰.gluedCover.f i j)
        (𝒰.gluedCover.f i k) := by
  refine pullback.lift
    (pullback.fst
        ((gluedCover (𝒰.pullback₁ f)).f i j)
        ((gluedCover (𝒰.pullback₁ f)).f i k) ≫
      baseChangeOverlapMap 𝒰 f i j)
    (pullback.snd
        ((gluedCover (𝒰.pullback₁ f)).f i j)
        ((gluedCover (𝒰.pullback₁ f)).f i k) ≫
      baseChangeOverlapMap 𝒰 f i k) ?_
  let p :=
    pullback.fst
      ((gluedCover (𝒰.pullback₁ f)).f i j)
      ((gluedCover (𝒰.pullback₁ f)).f i k)
  let q :=
    pullback.snd
      ((gluedCover (𝒰.pullback₁ f)).f i j)
      ((gluedCover (𝒰.pullback₁ f)).f i k)
  let c :
      (𝒰.pullback₁ f).X i ⟶
        𝒰.gluedCover.U i :=
    𝒰.pullbackHom f i
  have hij :=
    baseChangeOverlapMap_gluedCover_f 𝒰 f i j
  have hik :=
    baseChangeOverlapMap_gluedCover_f 𝒰 f i k
  calc
    p ≫ (baseChangeOverlapMap 𝒰 f i j ≫
          𝒰.gluedCover.f i j) =
        p ≫ ((gluedCover (𝒰.pullback₁ f)).f i j ≫
          c) :=
      congrArg
        (fun e :
          (gluedCover (𝒰.pullback₁ f)).V (i, j) ⟶
            𝒰.gluedCover.U i => p ≫ e)
        hij
    _ = q ≫ ((gluedCover (𝒰.pullback₁ f)).f i k ≫
          c) :=
      pullback.condition_assoc
        (f := (gluedCover (𝒰.pullback₁ f)).f i j)
        (g := (gluedCover (𝒰.pullback₁ f)).f i k)
        c
    _ = q ≫ (baseChangeOverlapMap 𝒰 f i k ≫
          𝒰.gluedCover.f i k) :=
      congrArg
        (fun e :
          (gluedCover (𝒰.pullback₁ f)).V (i, k) ⟶
            𝒰.gluedCover.U i => q ≫ e)
        hik.symm

@[simp, reassoc]
theorem baseChangeTripleOverlapMap_fst (i j k : 𝒰.I₀) :
    baseChangeTripleOverlapMap 𝒰 f i j k ≫
        pullback.fst
          (𝒰.gluedCover.f i j)
          (𝒰.gluedCover.f i k) =
      pullback.fst
          ((gluedCover (𝒰.pullback₁ f)).f i j)
          ((gluedCover (𝒰.pullback₁ f)).f i k) ≫
        baseChangeOverlapMap 𝒰 f i j :=
  pullback.lift_fst _ _ _

@[simp, reassoc]
theorem baseChangeTripleOverlapMap_snd (i j k : 𝒰.I₀) :
    baseChangeTripleOverlapMap 𝒰 f i j k ≫
        pullback.snd
          (𝒰.gluedCover.f i j)
          (𝒰.gluedCover.f i k) =
      pullback.snd
          ((gluedCover (𝒰.pullback₁ f)).f i j)
          ((gluedCover (𝒰.pullback₁ f)).f i k) ≫
        baseChangeOverlapMap 𝒰 f i k :=
  pullback.lift_snd _ _ _

@[simp, reassoc]
theorem gluedCoverTripleTo₂₃_fst (i j k : 𝒰.I₀) :
    𝒰.gluedCover.t' i j k ≫
        pullback.fst
          (𝒰.gluedCover.f j k)
          (𝒰.gluedCover.f j i) ≫
        pullback.fst (𝒰.f j) (𝒰.f k) =
      pullback.fst
          (𝒰.gluedCover.f i j)
          (𝒰.gluedCover.f i k) ≫
        pullback.snd (𝒰.f i) (𝒰.f j) := by
  change
    𝒰.gluedCoverT' i j k ≫
        pullback.fst
          (pullback.fst (𝒰.f j) (𝒰.f k))
          (pullback.fst (𝒰.f j) (𝒰.f i)) ≫
        pullback.fst (𝒰.f j) (𝒰.f k) =
      pullback.fst
          (pullback.fst (𝒰.f i) (𝒰.f j))
          (pullback.fst (𝒰.f i) (𝒰.f k)) ≫
        pullback.snd (𝒰.f i) (𝒰.f j)
  exact 𝒰.gluedCoverT'_fst_fst i j k

@[simp, reassoc]
theorem gluedCoverTripleTo₂₃_snd (i j k : 𝒰.I₀) :
    𝒰.gluedCover.t' i j k ≫
        pullback.fst
          (𝒰.gluedCover.f j k)
          (𝒰.gluedCover.f j i) ≫
        pullback.snd (𝒰.f j) (𝒰.f k) =
      pullback.snd
          (𝒰.gluedCover.f i j)
          (𝒰.gluedCover.f i k) ≫
        pullback.snd (𝒰.f i) (𝒰.f k) := by
  change
    𝒰.gluedCoverT' i j k ≫
        pullback.fst
          (pullback.fst (𝒰.f j) (𝒰.f k))
          (pullback.fst (𝒰.f j) (𝒰.f i)) ≫
        pullback.snd (𝒰.f j) (𝒰.f k) =
      pullback.snd
          (pullback.fst (𝒰.f i) (𝒰.f j))
          (pullback.fst (𝒰.f i) (𝒰.f k)) ≫
        pullback.snd (𝒰.f i) (𝒰.f k)
  exact 𝒰.gluedCoverT'_fst_snd i j k

/-- The triple-overlap map commutes with the canonical route from the
`ijk` triple overlap to the `jk` pair overlap. -/
theorem baseChangeTripleOverlapMap_to₂₃ (i j k : 𝒰.I₀) :
    baseChangeTripleOverlapMap 𝒰 f i j k ≫
        (𝒰.gluedCover.t' i j k ≫
          pullback.fst
            (𝒰.gluedCover.f j k)
            (𝒰.gluedCover.f j i)) =
      ((gluedCover (𝒰.pullback₁ f)).t' i j k ≫
          pullback.fst
            ((gluedCover (𝒰.pullback₁ f)).f j k)
            ((gluedCover (𝒰.pullback₁ f)).f j i)) ≫
        baseChangeOverlapMap 𝒰 f j k := by
  apply pullback.hom_ext
  · have hU := gluedCoverTripleTo₂₃_fst 𝒰 i j k
    have hV :=
      gluedCoverTripleTo₂₃_fst
        (𝒰.pullback₁ f) i j k
    have htriple :=
      baseChangeTripleOverlapMap_fst 𝒰 f i j k
    have hij :=
      baseChangeOverlapMap_snd 𝒰 f i j
    have hjk :=
      baseChangeOverlapMap_gluedCover_f 𝒰 f j k
    have hleft :
        (baseChangeTripleOverlapMap 𝒰 f i j k ≫
            (𝒰.gluedCover.t' i j k ≫
              pullback.fst
                (𝒰.gluedCover.f j k)
                (𝒰.gluedCover.f j i))) ≫
              pullback.fst (𝒰.f j) (𝒰.f k) =
          (pullback.fst
              ((gluedCover (𝒰.pullback₁ f)).f i j)
              ((gluedCover (𝒰.pullback₁ f)).f i k) ≫
            pullback.snd
              ((𝒰.pullback₁ f).f i)
              ((𝒰.pullback₁ f).f j)) ≫
            𝒰.pullbackHom f j := by
      calc
        (baseChangeTripleOverlapMap 𝒰 f i j k ≫
            (𝒰.gluedCover.t' i j k ≫
              pullback.fst
                (𝒰.gluedCover.f j k)
                (𝒰.gluedCover.f j i))) ≫
              pullback.fst (𝒰.f j) (𝒰.f k) =
          baseChangeTripleOverlapMap 𝒰 f i j k ≫
            ((𝒰.gluedCover.t' i j k ≫
              pullback.fst
                (𝒰.gluedCover.f j k)
                (𝒰.gluedCover.f j i)) ≫
              pullback.fst (𝒰.f j) (𝒰.f k)) :=
            Category.assoc _ _ _
        _ = baseChangeTripleOverlapMap 𝒰 f i j k ≫
            (pullback.fst
                (𝒰.gluedCover.f i j)
                (𝒰.gluedCover.f i k) ≫
              pullback.snd (𝒰.f i) (𝒰.f j)) :=
            congrArg
              (fun e =>
                baseChangeTripleOverlapMap 𝒰 f i j k ≫ e)
              hU
        _ = (baseChangeTripleOverlapMap 𝒰 f i j k ≫
              pullback.fst
                (𝒰.gluedCover.f i j)
                (𝒰.gluedCover.f i k)) ≫
              pullback.snd (𝒰.f i) (𝒰.f j) :=
            (Category.assoc _ _ _).symm
        _ = (pullback.fst
                ((gluedCover (𝒰.pullback₁ f)).f i j)
                ((gluedCover (𝒰.pullback₁ f)).f i k) ≫
              baseChangeOverlapMap 𝒰 f i j) ≫
              pullback.snd (𝒰.f i) (𝒰.f j) :=
            congrArg
              (fun e =>
                e ≫ pullback.snd (𝒰.f i) (𝒰.f j))
              htriple
        _ = pullback.fst
                ((gluedCover (𝒰.pullback₁ f)).f i j)
                ((gluedCover (𝒰.pullback₁ f)).f i k) ≫
              (baseChangeOverlapMap 𝒰 f i j ≫
                pullback.snd (𝒰.f i) (𝒰.f j)) :=
            Category.assoc _ _ _
        _ = pullback.fst
                ((gluedCover (𝒰.pullback₁ f)).f i j)
                ((gluedCover (𝒰.pullback₁ f)).f i k) ≫
              (pullback.snd
                  ((𝒰.pullback₁ f).f i)
                  ((𝒰.pullback₁ f).f j) ≫
                𝒰.pullbackHom f j) :=
            congrArg
              (fun e =>
                pullback.fst
                    ((gluedCover (𝒰.pullback₁ f)).f i j)
                    ((gluedCover (𝒰.pullback₁ f)).f i k) ≫ e)
              hij
        _ = (pullback.fst
                ((gluedCover (𝒰.pullback₁ f)).f i j)
                ((gluedCover (𝒰.pullback₁ f)).f i k) ≫
              pullback.snd
                ((𝒰.pullback₁ f).f i)
                ((𝒰.pullback₁ f).f j)) ≫
              𝒰.pullbackHom f j :=
            (Category.assoc _ _ _).symm
    have hright :
        (((gluedCover (𝒰.pullback₁ f)).t' i j k ≫
              pullback.fst
                ((gluedCover (𝒰.pullback₁ f)).f j k)
                ((gluedCover (𝒰.pullback₁ f)).f j i)) ≫
            baseChangeOverlapMap 𝒰 f j k) ≫
              pullback.fst (𝒰.f j) (𝒰.f k) =
          (pullback.fst
              ((gluedCover (𝒰.pullback₁ f)).f i j)
              ((gluedCover (𝒰.pullback₁ f)).f i k) ≫
            pullback.snd
              ((𝒰.pullback₁ f).f i)
              ((𝒰.pullback₁ f).f j)) ≫
            𝒰.pullbackHom f j := by
      calc
        (((gluedCover (𝒰.pullback₁ f)).t' i j k ≫
              pullback.fst
                ((gluedCover (𝒰.pullback₁ f)).f j k)
                ((gluedCover (𝒰.pullback₁ f)).f j i)) ≫
            baseChangeOverlapMap 𝒰 f j k) ≫
              pullback.fst (𝒰.f j) (𝒰.f k) =
          ((gluedCover (𝒰.pullback₁ f)).t' i j k ≫
              pullback.fst
                ((gluedCover (𝒰.pullback₁ f)).f j k)
                ((gluedCover (𝒰.pullback₁ f)).f j i)) ≫
            (baseChangeOverlapMap 𝒰 f j k ≫
              pullback.fst (𝒰.f j) (𝒰.f k)) :=
            Category.assoc _ _ _
        _ = ((gluedCover (𝒰.pullback₁ f)).t' i j k ≫
              pullback.fst
                ((gluedCover (𝒰.pullback₁ f)).f j k)
                ((gluedCover (𝒰.pullback₁ f)).f j i)) ≫
            ((gluedCover (𝒰.pullback₁ f)).f j k ≫
              𝒰.pullbackHom f j) :=
            congrArg
              (fun e =>
                ((gluedCover (𝒰.pullback₁ f)).t' i j k ≫
                  pullback.fst
                    ((gluedCover (𝒰.pullback₁ f)).f j k)
                    ((gluedCover (𝒰.pullback₁ f)).f j i)) ≫ e)
              hjk
        _ = (((gluedCover (𝒰.pullback₁ f)).t' i j k ≫
                pullback.fst
                  ((gluedCover (𝒰.pullback₁ f)).f j k)
                  ((gluedCover (𝒰.pullback₁ f)).f j i)) ≫
              (gluedCover (𝒰.pullback₁ f)).f j k) ≫
              𝒰.pullbackHom f j :=
            (Category.assoc _ _ _).symm
        _ = (pullback.fst
                ((gluedCover (𝒰.pullback₁ f)).f i j)
                ((gluedCover (𝒰.pullback₁ f)).f i k) ≫
              pullback.snd
                ((𝒰.pullback₁ f).f i)
                ((𝒰.pullback₁ f).f j)) ≫
              𝒰.pullbackHom f j :=
            congrArg
              (fun e => e ≫ 𝒰.pullbackHom f j)
              hV
    exact hleft.trans hright.symm
  · have hU := gluedCoverTripleTo₂₃_snd 𝒰 i j k
    have hV :=
      gluedCoverTripleTo₂₃_snd
        (𝒰.pullback₁ f) i j k
    have htriple :=
      baseChangeTripleOverlapMap_snd 𝒰 f i j k
    have hik :=
      baseChangeOverlapMap_snd 𝒰 f i k
    have hjk :=
      baseChangeOverlapMap_snd 𝒰 f j k
    have hleft :
        (baseChangeTripleOverlapMap 𝒰 f i j k ≫
            (𝒰.gluedCover.t' i j k ≫
              pullback.fst
                (𝒰.gluedCover.f j k)
                (𝒰.gluedCover.f j i))) ≫
              pullback.snd (𝒰.f j) (𝒰.f k) =
          (pullback.snd
              ((gluedCover (𝒰.pullback₁ f)).f i j)
              ((gluedCover (𝒰.pullback₁ f)).f i k) ≫
            pullback.snd
              ((𝒰.pullback₁ f).f i)
              ((𝒰.pullback₁ f).f k)) ≫
            𝒰.pullbackHom f k := by
      calc
        (baseChangeTripleOverlapMap 𝒰 f i j k ≫
            (𝒰.gluedCover.t' i j k ≫
              pullback.fst
                (𝒰.gluedCover.f j k)
                (𝒰.gluedCover.f j i))) ≫
              pullback.snd (𝒰.f j) (𝒰.f k) =
          baseChangeTripleOverlapMap 𝒰 f i j k ≫
            ((𝒰.gluedCover.t' i j k ≫
              pullback.fst
                (𝒰.gluedCover.f j k)
                (𝒰.gluedCover.f j i)) ≫
              pullback.snd (𝒰.f j) (𝒰.f k)) :=
            Category.assoc _ _ _
        _ = baseChangeTripleOverlapMap 𝒰 f i j k ≫
            (pullback.snd
                (𝒰.gluedCover.f i j)
                (𝒰.gluedCover.f i k) ≫
              pullback.snd (𝒰.f i) (𝒰.f k)) :=
            congrArg
              (fun e =>
                baseChangeTripleOverlapMap 𝒰 f i j k ≫ e)
              hU
        _ = (baseChangeTripleOverlapMap 𝒰 f i j k ≫
              pullback.snd
                (𝒰.gluedCover.f i j)
                (𝒰.gluedCover.f i k)) ≫
              pullback.snd (𝒰.f i) (𝒰.f k) :=
            (Category.assoc _ _ _).symm
        _ = (pullback.snd
                ((gluedCover (𝒰.pullback₁ f)).f i j)
                ((gluedCover (𝒰.pullback₁ f)).f i k) ≫
              baseChangeOverlapMap 𝒰 f i k) ≫
              pullback.snd (𝒰.f i) (𝒰.f k) :=
            congrArg
              (fun e =>
                e ≫ pullback.snd (𝒰.f i) (𝒰.f k))
              htriple
        _ = pullback.snd
                ((gluedCover (𝒰.pullback₁ f)).f i j)
                ((gluedCover (𝒰.pullback₁ f)).f i k) ≫
              (baseChangeOverlapMap 𝒰 f i k ≫
                pullback.snd (𝒰.f i) (𝒰.f k)) :=
            Category.assoc _ _ _
        _ = pullback.snd
                ((gluedCover (𝒰.pullback₁ f)).f i j)
                ((gluedCover (𝒰.pullback₁ f)).f i k) ≫
              (pullback.snd
                  ((𝒰.pullback₁ f).f i)
                  ((𝒰.pullback₁ f).f k) ≫
                𝒰.pullbackHom f k) :=
            congrArg
              (fun e =>
                pullback.snd
                    ((gluedCover (𝒰.pullback₁ f)).f i j)
                    ((gluedCover (𝒰.pullback₁ f)).f i k) ≫ e)
              hik
        _ = (pullback.snd
                ((gluedCover (𝒰.pullback₁ f)).f i j)
                ((gluedCover (𝒰.pullback₁ f)).f i k) ≫
              pullback.snd
                ((𝒰.pullback₁ f).f i)
                ((𝒰.pullback₁ f).f k)) ≫
              𝒰.pullbackHom f k :=
            (Category.assoc _ _ _).symm
    have hright :
        (((gluedCover (𝒰.pullback₁ f)).t' i j k ≫
              pullback.fst
                ((gluedCover (𝒰.pullback₁ f)).f j k)
                ((gluedCover (𝒰.pullback₁ f)).f j i)) ≫
            baseChangeOverlapMap 𝒰 f j k) ≫
              pullback.snd (𝒰.f j) (𝒰.f k) =
          (pullback.snd
              ((gluedCover (𝒰.pullback₁ f)).f i j)
              ((gluedCover (𝒰.pullback₁ f)).f i k) ≫
            pullback.snd
              ((𝒰.pullback₁ f).f i)
              ((𝒰.pullback₁ f).f k)) ≫
            𝒰.pullbackHom f k := by
      calc
        (((gluedCover (𝒰.pullback₁ f)).t' i j k ≫
              pullback.fst
                ((gluedCover (𝒰.pullback₁ f)).f j k)
                ((gluedCover (𝒰.pullback₁ f)).f j i)) ≫
            baseChangeOverlapMap 𝒰 f j k) ≫
              pullback.snd (𝒰.f j) (𝒰.f k) =
          ((gluedCover (𝒰.pullback₁ f)).t' i j k ≫
              pullback.fst
                ((gluedCover (𝒰.pullback₁ f)).f j k)
                ((gluedCover (𝒰.pullback₁ f)).f j i)) ≫
            (baseChangeOverlapMap 𝒰 f j k ≫
              pullback.snd (𝒰.f j) (𝒰.f k)) :=
            Category.assoc _ _ _
        _ = ((gluedCover (𝒰.pullback₁ f)).t' i j k ≫
              pullback.fst
                ((gluedCover (𝒰.pullback₁ f)).f j k)
                ((gluedCover (𝒰.pullback₁ f)).f j i)) ≫
            (pullback.snd
                ((𝒰.pullback₁ f).f j)
                ((𝒰.pullback₁ f).f k) ≫
              𝒰.pullbackHom f k) :=
            congrArg
              (fun e =>
                ((gluedCover (𝒰.pullback₁ f)).t' i j k ≫
                  pullback.fst
                    ((gluedCover (𝒰.pullback₁ f)).f j k)
                    ((gluedCover (𝒰.pullback₁ f)).f j i)) ≫ e)
              hjk
        _ = (((gluedCover (𝒰.pullback₁ f)).t' i j k ≫
                pullback.fst
                  ((gluedCover (𝒰.pullback₁ f)).f j k)
                  ((gluedCover (𝒰.pullback₁ f)).f j i)) ≫
              pullback.snd
                ((𝒰.pullback₁ f).f j)
                ((𝒰.pullback₁ f).f k)) ≫
              𝒰.pullbackHom f k :=
            (Category.assoc _ _ _).symm
        _ = (pullback.snd
                ((gluedCover (𝒰.pullback₁ f)).f i j)
                ((gluedCover (𝒰.pullback₁ f)).f i k) ≫
              pullback.snd
                ((𝒰.pullback₁ f).f i)
                ((𝒰.pullback₁ f).f k)) ≫
              𝒰.pullbackHom f k :=
            congrArg
              (fun e => e ≫ 𝒰.pullbackHom f k)
              hV
    exact hleft.trans hright.symm

end AlgebraicGeometry.Scheme.Cover

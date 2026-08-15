/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverIsoOverlap
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverPullbackComposition

/-!
# Unit cocycles and composition of pulled-back open covers

The canonical isomorphism from an iterated pullback cover to the cover
pulled back along the composite intertwines the two canonical maps on
pairwise overlaps.  Hence pulling back a unit cocycle in two stages is
the same as pulling it back along the composite and transporting it
across that cover isomorphism.
-/

open CategoryTheory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Cover

open AlgebraicGeometry.Scheme.Modules

variable {S T R : Scheme.{0}}
  (𝒰 : S.OpenCover) (f : T ⟶ S) (g : R ⟶ T)

/-- The overlap map obtained from the cover isomorphism and direct base
change, with the original cover indices exposed in its type. -/
def directCompositeOverlapMap (i j : 𝒰.I₀) :
    (gluedCover ((𝒰.pullback₁ f).pullback₁ g)).V (i, j) ⟶
      𝒰.gluedCover.V (i, j) :=
  coverIsoOverlapMap (pullbackPullbackIso 𝒰 f g) i j ≫
    baseChangeOverlapMap 𝒰 (g ≫ f) i j

/-- The overlap map obtained by two successive base changes, with the
original cover indices exposed in its type. -/
def successiveCompositeOverlapMap (i j : 𝒰.I₀) :
    (gluedCover ((𝒰.pullback₁ f).pullback₁ g)).V (i, j) ⟶
      𝒰.gluedCover.V (i, j) :=
  baseChangeOverlapMap (𝒰.pullback₁ f) g i j ≫
    baseChangeOverlapMap 𝒰 f i j

theorem directCompositeOverlapMap_fst (i j : 𝒰.I₀) :
    directCompositeOverlapMap 𝒰 f g i j ≫ overlapFst 𝒰 i j =
      overlapFst ((𝒰.pullback₁ f).pullback₁ g) i j ≫
        ((pullbackPullbackIso 𝒰 f g).hom.h₀ i ≫
          𝒰.pullbackHom (g ≫ f) i) := by
  have hfst :
      coverIsoOverlapMap (pullbackPullbackIso 𝒰 f g) i j ≫
          overlapFst (𝒰.pullback₁ (g ≫ f)) i j =
        overlapFst ((𝒰.pullback₁ f).pullback₁ g) i j ≫
          (pullbackPullbackIso 𝒰 f g).hom.h₀ i := by
    simpa only [pullbackPullbackIso_hom_s₀] using
      coverIsoOverlapMap_overlapFst
        (pullbackPullbackIso 𝒰 f g) i j
  calc
    directCompositeOverlapMap 𝒰 f g i j ≫ overlapFst 𝒰 i j =
      coverIsoOverlapMap (pullbackPullbackIso 𝒰 f g) i j ≫
        (baseChangeOverlapMap 𝒰 (g ≫ f) i j ≫
          overlapFst 𝒰 i j) :=
      Category.assoc _ _ _
    _ = coverIsoOverlapMap (pullbackPullbackIso 𝒰 f g) i j ≫
        (overlapFst (𝒰.pullback₁ (g ≫ f)) i j ≫
          𝒰.pullbackHom (g ≫ f) i) :=
      CategoryTheory.whisker_eq _
        (baseChangeOverlapMap_overlapFst 𝒰 (g ≫ f) i j)
    _ = (coverIsoOverlapMap (pullbackPullbackIso 𝒰 f g) i j ≫
          overlapFst (𝒰.pullback₁ (g ≫ f)) i j) ≫
        𝒰.pullbackHom (g ≫ f) i :=
      (Category.assoc _ _ _).symm
    _ = (overlapFst ((𝒰.pullback₁ f).pullback₁ g) i j ≫
          (pullbackPullbackIso 𝒰 f g).hom.h₀ i) ≫
        𝒰.pullbackHom (g ≫ f) i :=
      congrArg (fun q => q ≫ 𝒰.pullbackHom (g ≫ f) i) hfst
    _ = overlapFst ((𝒰.pullback₁ f).pullback₁ g) i j ≫
        ((pullbackPullbackIso 𝒰 f g).hom.h₀ i ≫
          𝒰.pullbackHom (g ≫ f) i) :=
      Category.assoc _ _ _

theorem successiveCompositeOverlapMap_fst (i j : 𝒰.I₀) :
    successiveCompositeOverlapMap 𝒰 f g i j ≫ overlapFst 𝒰 i j =
      overlapFst ((𝒰.pullback₁ f).pullback₁ g) i j ≫
        (Cover.pullbackHom (𝒰.pullback₁ f) g i ≫
          𝒰.pullbackHom f i) := by
  calc
    successiveCompositeOverlapMap 𝒰 f g i j ≫ overlapFst 𝒰 i j =
      baseChangeOverlapMap (𝒰.pullback₁ f) g i j ≫
        (baseChangeOverlapMap 𝒰 f i j ≫ overlapFst 𝒰 i j) :=
      Category.assoc _ _ _
    _ = baseChangeOverlapMap (𝒰.pullback₁ f) g i j ≫
        (overlapFst (𝒰.pullback₁ f) i j ≫
          𝒰.pullbackHom f i) :=
      CategoryTheory.whisker_eq _
        (baseChangeOverlapMap_overlapFst 𝒰 f i j)
    _ = (baseChangeOverlapMap (𝒰.pullback₁ f) g i j ≫
          overlapFst (𝒰.pullback₁ f) i j) ≫
        𝒰.pullbackHom f i :=
      (Category.assoc _ _ _).symm
    _ = (overlapFst ((𝒰.pullback₁ f).pullback₁ g) i j ≫
          Cover.pullbackHom (𝒰.pullback₁ f) g i) ≫
        𝒰.pullbackHom f i :=
      congrArg (fun q => q ≫ 𝒰.pullbackHom f i)
        (baseChangeOverlapMap_overlapFst
          (𝒰.pullback₁ f) g i j)
    _ = overlapFst ((𝒰.pullback₁ f).pullback₁ g) i j ≫
        (Cover.pullbackHom (𝒰.pullback₁ f) g i ≫
          𝒰.pullbackHom f i) :=
      Category.assoc _ _ _

theorem directCompositeOverlapMap_snd (i j : 𝒰.I₀) :
    directCompositeOverlapMap 𝒰 f g i j ≫ overlapSnd 𝒰 i j =
      overlapSnd ((𝒰.pullback₁ f).pullback₁ g) i j ≫
        ((pullbackPullbackIso 𝒰 f g).hom.h₀ j ≫
          𝒰.pullbackHom (g ≫ f) j) := by
  have hsnd :
      coverIsoOverlapMap (pullbackPullbackIso 𝒰 f g) i j ≫
          overlapSnd (𝒰.pullback₁ (g ≫ f)) i j =
        overlapSnd ((𝒰.pullback₁ f).pullback₁ g) i j ≫
          (pullbackPullbackIso 𝒰 f g).hom.h₀ j := by
    simpa only [pullbackPullbackIso_hom_s₀] using
      coverIsoOverlapMap_overlapSnd
        (pullbackPullbackIso 𝒰 f g) i j
  calc
    directCompositeOverlapMap 𝒰 f g i j ≫ overlapSnd 𝒰 i j =
      coverIsoOverlapMap (pullbackPullbackIso 𝒰 f g) i j ≫
        (baseChangeOverlapMap 𝒰 (g ≫ f) i j ≫
          overlapSnd 𝒰 i j) :=
      Category.assoc _ _ _
    _ = coverIsoOverlapMap (pullbackPullbackIso 𝒰 f g) i j ≫
        (overlapSnd (𝒰.pullback₁ (g ≫ f)) i j ≫
          𝒰.pullbackHom (g ≫ f) j) :=
      CategoryTheory.whisker_eq _
        (baseChangeOverlapMap_overlapSnd 𝒰 (g ≫ f) i j)
    _ = (coverIsoOverlapMap (pullbackPullbackIso 𝒰 f g) i j ≫
          overlapSnd (𝒰.pullback₁ (g ≫ f)) i j) ≫
        𝒰.pullbackHom (g ≫ f) j :=
      (Category.assoc _ _ _).symm
    _ = (overlapSnd ((𝒰.pullback₁ f).pullback₁ g) i j ≫
          (pullbackPullbackIso 𝒰 f g).hom.h₀ j) ≫
        𝒰.pullbackHom (g ≫ f) j :=
      congrArg (fun q => q ≫ 𝒰.pullbackHom (g ≫ f) j) hsnd
    _ = overlapSnd ((𝒰.pullback₁ f).pullback₁ g) i j ≫
        ((pullbackPullbackIso 𝒰 f g).hom.h₀ j ≫
          𝒰.pullbackHom (g ≫ f) j) :=
      Category.assoc _ _ _

theorem successiveCompositeOverlapMap_snd (i j : 𝒰.I₀) :
    successiveCompositeOverlapMap 𝒰 f g i j ≫ overlapSnd 𝒰 i j =
      overlapSnd ((𝒰.pullback₁ f).pullback₁ g) i j ≫
        (Cover.pullbackHom (𝒰.pullback₁ f) g j ≫
          𝒰.pullbackHom f j) := by
  calc
    successiveCompositeOverlapMap 𝒰 f g i j ≫ overlapSnd 𝒰 i j =
      baseChangeOverlapMap (𝒰.pullback₁ f) g i j ≫
        (baseChangeOverlapMap 𝒰 f i j ≫ overlapSnd 𝒰 i j) :=
      Category.assoc _ _ _
    _ = baseChangeOverlapMap (𝒰.pullback₁ f) g i j ≫
        (overlapSnd (𝒰.pullback₁ f) i j ≫
          𝒰.pullbackHom f j) :=
      CategoryTheory.whisker_eq _
        (baseChangeOverlapMap_overlapSnd 𝒰 f i j)
    _ = (baseChangeOverlapMap (𝒰.pullback₁ f) g i j ≫
          overlapSnd (𝒰.pullback₁ f) i j) ≫
        𝒰.pullbackHom f j :=
      (Category.assoc _ _ _).symm
    _ = (overlapSnd ((𝒰.pullback₁ f).pullback₁ g) i j ≫
          Cover.pullbackHom (𝒰.pullback₁ f) g j) ≫
        𝒰.pullbackHom f j :=
      congrArg (fun q => q ≫ 𝒰.pullbackHom f j)
        (baseChangeOverlapMap_overlapSnd
          (𝒰.pullback₁ f) g i j)
    _ = overlapSnd ((𝒰.pullback₁ f).pullback₁ g) i j ≫
        (Cover.pullbackHom (𝒰.pullback₁ f) g j ≫
          𝒰.pullbackHom f j) :=
      Category.assoc _ _ _

/-- On pairwise overlaps, the canonical iterated-pullback cover
isomorphism intertwines the direct and successive base-change maps. -/
theorem pullbackPullbackIso_overlap_baseChangeMap
    (i j : 𝒰.I₀) :
    coverIsoOverlapMap (pullbackPullbackIso 𝒰 f g) i j ≫
        baseChangeOverlapMap 𝒰 (g ≫ f) i j =
      baseChangeOverlapMap (𝒰.pullback₁ f) g i j ≫
        baseChangeOverlapMap 𝒰 f i j := by
  change directCompositeOverlapMap 𝒰 f g i j =
    successiveCompositeOverlapMap 𝒰 f g i j
  apply pullback.hom_ext
  · exact (directCompositeOverlapMap_fst 𝒰 f g i j).trans <|
      (CategoryTheory.whisker_eq _
        (pullbackPullbackIso_hom_h₀_pullbackHom
          𝒰 f g i)).trans
      (successiveCompositeOverlapMap_fst 𝒰 f g i j).symm
  · exact (directCompositeOverlapMap_snd 𝒰 f g i j).trans <|
      (CategoryTheory.whisker_eq _
        (pullbackPullbackIso_hom_h₀_pullbackHom
          𝒰 f g j)).trans
      (successiveCompositeOverlapMap_snd 𝒰 f g i j).symm

/-- Pulling back a cover-unit family successively along `f` and `g`
agrees with pulling it back along `g ≫ f` and transporting across the
canonical isomorphism of the two pulled-back covers. -/
theorem pullbackCoverUnitAlongIso_pullbackPullbackIso
    (a : ∀ i j : 𝒰.I₀,
      Γ(𝒰.gluedCover.V (i, j), ⊤)ˣ) :
    pullbackCoverUnitAlongIso
        (pullbackPullbackIso 𝒰 f g)
        (baseChangeCoverUnit 𝒰 (g ≫ f) a) =
      baseChangeCoverUnit (𝒰.pullback₁ f) g
        (baseChangeCoverUnit 𝒰 f a) := by
  have h :
      (fun i j : 𝒰.I₀ =>
        pullbackGlobalUnit
          (coverIsoOverlapMap
            (pullbackPullbackIso 𝒰 f g) i j)
          (pullbackGlobalUnit
            (baseChangeOverlapMap 𝒰 (g ≫ f) i j)
            (a i j))) =
        (fun i j : 𝒰.I₀ =>
          pullbackGlobalUnit
            (baseChangeOverlapMap (𝒰.pullback₁ f) g i j)
            (pullbackGlobalUnit
              (baseChangeOverlapMap 𝒰 f i j)
              (a i j))) := by
    funext i j
    calc
      pullbackGlobalUnit
          (coverIsoOverlapMap
            (pullbackPullbackIso 𝒰 f g) i j)
          (pullbackGlobalUnit
            (baseChangeOverlapMap 𝒰 (g ≫ f) i j)
            (a i j)) =
        pullbackGlobalUnit
          (directCompositeOverlapMap 𝒰 f g i j)
          (a i j) :=
        pullbackGlobalUnit_comp _ _ _
      _ = pullbackGlobalUnit
          (successiveCompositeOverlapMap 𝒰 f g i j)
          (a i j) :=
        congrArg (fun q => pullbackGlobalUnit q (a i j))
          (pullbackPullbackIso_overlap_baseChangeMap
            𝒰 f g i j)
      _ = pullbackGlobalUnit
          (baseChangeOverlapMap (𝒰.pullback₁ f) g i j)
          (pullbackGlobalUnit
            (baseChangeOverlapMap 𝒰 f i j)
            (a i j)) :=
        (pullbackGlobalUnit_comp _ _ _).symm
  exact h

end AlgebraicGeometry.Scheme.Cover

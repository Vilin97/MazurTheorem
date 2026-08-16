/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.ClosedComponentNeighborhood

/-!
# The equal-coordinate locus inside a relative product

For morphisms `X → S` and `B → S` over `S → G`, the fiber product
`X ×[S] B` maps naturally into `X ×[G] B`.  It is the pullback of the
diagonal `S → S ×[G] S`; hence it is a closed subscheme whenever `S → G`
is separated.

The named downstream consumer is `EtaleGraphNeighborhood`, which combines
this closed immersion with the graph/complement splitting for an étale
coordinate map.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.EqualCoordinateClosedImmersion

variable {G S X B : Scheme.{u}} (s : S ⟶ G) (f : X ⟶ S) (q : B ⟶ S)

/-- The relative ambient product before imposing equality of the two
`S`-coordinates. -/
noncomputable abbrev ambient : Scheme.{u} :=
  pullback (f ≫ s) (q ≫ s)

/-- Include the equal-coordinate fiber product in the relative ambient
product. -/
noncomputable abbrev equalCoordinateInclusion :
    pullback f q ⟶ ambient s f q :=
  pullback.lift (pullback.fst f q) (pullback.snd f q)
    (pullback.condition_assoc (f := f) (g := q) s)

@[reassoc]
theorem equalCoordinateInclusion_fst :
    equalCoordinateInclusion s f q ≫ pullback.fst (f ≫ s) (q ≫ s) =
      pullback.fst f q :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem equalCoordinateInclusion_snd :
    equalCoordinateInclusion s f q ≫ pullback.snd (f ≫ s) (q ≫ s) =
      pullback.snd f q :=
  pullback.lift_snd _ _ _

/-- Record the two `S`-coordinates of a point of the relative ambient
product. -/
noncomputable abbrev ambientPair : ambient s f q ⟶ pullback s s :=
  pullback.lift (pullback.fst (f ≫ s) (q ≫ s) ≫ f)
    (pullback.snd (f ≫ s) (q ≫ s) ≫ q) (by
      simpa only [Category.assoc] using
        pullback.condition (f := f ≫ s) (g := q ≫ s))

@[reassoc]
theorem ambientPair_fst :
    ambientPair s f q ≫ pullback.fst s s =
      pullback.fst (f ≫ s) (q ≫ s) ≫ f :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem ambientPair_snd :
    ambientPair s f q ≫ pullback.snd s s =
      pullback.snd (f ≫ s) (q ≫ s) ≫ q :=
  pullback.lift_snd _ _ _

/-- The equal-coordinate inclusion is the base change of the diagonal of
`S → G`. -/
theorem equalCoordinate_square : IsPullback
    (pullback.fst f q ≫ f) (equalCoordinateInclusion s f q)
    (pullback.diagonal s) (ambientPair s f q) := by
  refine ⟨⟨?_⟩, ⟨?_⟩⟩
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullback.diagonal_fst,
        Category.comp_id]
      rw [ambientPair_fst]
      rw [← Category.assoc, equalCoordinateInclusion_fst]
    · simp only [Category.assoc, pullback.diagonal_snd,
        Category.comp_id]
      rw [ambientPair_snd]
      rw [← Category.assoc, equalCoordinateInclusion_snd]
      exact pullback.condition (f := f) (g := q)
  · let lift (t : PullbackCone (pullback.diagonal s) (ambientPair s f q)) :
        t.pt ⟶ pullback f q :=
      pullback.lift
        (t.snd ≫ pullback.fst (f ≫ s) (q ≫ s))
        (t.snd ≫ pullback.snd (f ≫ s) (q ≫ s)) (by
          have h₁ := t.condition =≫ pullback.fst s s
          have h₂ := t.condition =≫ pullback.snd s s
          simp only [Category.assoc, pullback.diagonal_fst,
            pullback.diagonal_snd, Category.comp_id] at h₁ h₂
          rw [ambientPair_fst] at h₁
          rw [ambientPair_snd] at h₂
          simpa only [Category.assoc] using h₁.symm.trans h₂)
    refine PullbackCone.IsLimit.mk _ lift ?_ ?_ ?_
    · intro t
      have h := t.condition =≫ pullback.fst s s
      simp only [Category.assoc, pullback.diagonal_fst,
        Category.comp_id] at h
      rw [ambientPair_fst] at h
      have hl : lift t ≫ pullback.fst f q =
          t.snd ≫ pullback.fst (f ≫ s) (q ≫ s) := by
        dsimp only [lift]
        exact pullback.lift_fst _ _ _
      rw [← Category.assoc, hl, Category.assoc]
      exact h.symm
    · intro t
      dsimp only [lift]
      apply pullback.hom_ext
      · rw [Category.assoc, equalCoordinateInclusion_fst,
          pullback.lift_fst]
      · rw [Category.assoc, equalCoordinateInclusion_snd,
          pullback.lift_snd]
    · intro t m hm₁ hm₂
      apply pullback.hom_ext
      · have h := hm₂ =≫ pullback.fst (f ≫ s) (q ≫ s)
        rw [Category.assoc, equalCoordinateInclusion_fst] at h
        dsimp only [lift]
        rw [pullback.lift_fst]
        exact h
      · have h := hm₂ =≫ pullback.snd (f ≫ s) (q ≫ s)
        rw [Category.assoc, equalCoordinateInclusion_snd] at h
        dsimp only [lift]
        rw [pullback.lift_snd]
        exact h

instance equalCoordinateInclusion_closed [IsSeparated s] :
    IsClosedImmersion (equalCoordinateInclusion s f q) := by
  exact IsClosedImmersion.isStableUnderBaseChange.of_isPullback
    (equalCoordinate_square s f q) inferInstance

end MazurTorsion.AlgebraicGeometry.Jacobian.EqualCoordinateClosedImmersion

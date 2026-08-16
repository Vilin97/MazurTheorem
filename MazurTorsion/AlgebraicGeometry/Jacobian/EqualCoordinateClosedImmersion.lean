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

/-- The base-changed copy of `S` over `B` in which the morphism `q` defines
a tautological section. -/
noncomputable abbrev relativeTarget : Scheme.{u} :=
  pullback s (q ≫ s)

/-- The tautological section of the base-changed target selected by `q`. -/
noncomputable abbrev relativeSection : B ⟶ relativeTarget s q :=
  pullback.lift q (𝟙 B) (by simp)

@[reassoc]
theorem relativeSection_fst :
    relativeSection s q ≫ pullback.fst s (q ≫ s) = q :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem relativeSection_snd :
    relativeSection s q ≫ pullback.snd s (q ≫ s) = 𝟙 B :=
  pullback.lift_snd _ _ _

/-- Record the `S`-coordinate of the `X` factor together with the unchanged
`B` factor of the relative ambient product. -/
noncomputable abbrev ambientToRelativeTarget :
    ambient s f q ⟶ relativeTarget s q :=
  pullback.lift
    (pullback.fst (f ≫ s) (q ≫ s) ≫ f)
    (pullback.snd (f ≫ s) (q ≫ s)) (by
      simpa only [Category.assoc] using
        pullback.condition (f := f ≫ s) (g := q ≫ s))

@[reassoc]
theorem ambientToRelativeTarget_fst :
    ambientToRelativeTarget s f q ≫ pullback.fst s (q ≫ s) =
      pullback.fst (f ≫ s) (q ≫ s) ≫ f :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem ambientToRelativeTarget_snd :
    ambientToRelativeTarget s f q ≫ pullback.snd s (q ≫ s) =
      pullback.snd (f ≫ s) (q ≫ s) :=
  pullback.lift_snd _ _ _

/-- The equal-coordinate locus is exactly the inverse image of the
tautological relative section. -/
theorem equalCoordinate_relativeSection_square : IsPullback
    (equalCoordinateInclusion s f q) (pullback.snd f q)
    (ambientToRelativeTarget s f q) (relativeSection s q) := by
  refine ⟨⟨?_⟩, ⟨?_⟩⟩
  · apply pullback.hom_ext
    · simp only [Category.assoc, ambientToRelativeTarget_fst,
        relativeSection_fst]
      rw [← Category.assoc, equalCoordinateInclusion_fst]
      exact pullback.condition
    · simp only [Category.assoc, ambientToRelativeTarget_snd,
        relativeSection_snd, Category.comp_id]
      exact equalCoordinateInclusion_snd s f q
  · let lift
        (t : PullbackCone
          (ambientToRelativeTarget s f q) (relativeSection s q)) :
        t.pt ⟶ pullback f q :=
      pullback.lift
        (t.fst ≫ pullback.fst (f ≫ s) (q ≫ s))
        t.snd (by
          have h := t.condition =≫ pullback.fst s (q ≫ s)
          simpa only [Category.assoc, ambientToRelativeTarget_fst,
            relativeSection_fst] using h)
    refine PullbackCone.IsLimit.mk _ lift ?_ ?_ ?_
    · intro t
      apply pullback.hom_ext
      · rw [Category.assoc, equalCoordinateInclusion_fst,
          pullback.lift_fst]
      · rw [Category.assoc, equalCoordinateInclusion_snd,
          pullback.lift_snd]
        have h := t.condition =≫ pullback.snd s (q ≫ s)
        simpa only [Category.assoc, ambientToRelativeTarget_snd,
          relativeSection_snd, Category.comp_id] using h.symm
    · intro t
      dsimp only [lift]
      exact pullback.lift_snd _ _ _
    · intro t m hm₁ hm₂
      apply pullback.hom_ext
      · have h := hm₁ =≫ pullback.fst (f ≫ s) (q ≫ s)
        rw [Category.assoc, equalCoordinateInclusion_fst] at h
        dsimp only [lift]
        rw [pullback.lift_fst]
        exact h
      · dsimp only [lift]
        rw [pullback.lift_snd]
        exact hm₂

/-- The ideal sheaf of the equal-coordinate locus is the inverse image of
the ideal sheaf of the tautological relative section. -/
theorem relativeSection_ker_comap_ambientToRelativeTarget
    [IsSeparated s] :
    (relativeSection s q).ker.comap (ambientToRelativeTarget s f q) =
      (equalCoordinateInclusion s f q).ker := by
  let sectionHom := relativeSection s q
  let familyHom := pullback.snd s (q ≫ s)
  letI : IsSeparated familyHom := by
    dsimp only [familyHom]
    infer_instance
  letI : IsClosedImmersion sectionHom := by
    haveI : IsClosedImmersion (sectionHom ≫ familyHom) := by
      rw [show sectionHom ≫ familyHom = 𝟙 B from
        relativeSection_snd s q]
      infer_instance
    exact IsClosedImmersion.of_comp sectionHom familyHom
  let h := equalCoordinate_relativeSection_square s f q
  calc
    sectionHom.ker.comap (ambientToRelativeTarget s f q) =
        (pullback.fst
          (ambientToRelativeTarget s f q) sectionHom).ker :=
      (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion
        sectionHom (ambientToRelativeTarget s f q)).symm
    _ = (h.isoPullback.hom ≫
        pullback.fst
          (ambientToRelativeTarget s f q) sectionHom).ker :=
      (Scheme.Hom.ker_comp_of_isIso h.isoPullback.hom
        (pullback.fst
          (ambientToRelativeTarget s f q) sectionHom)).symm
    _ = (equalCoordinateInclusion s f q).ker := by
      rw [h.isoPullback_hom_fst]

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

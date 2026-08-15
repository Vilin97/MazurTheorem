/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveGraphClosureOverDomain

/-!
# The base-open part of a projective graph closure

The open base-change map from projective space over `U` to projective
space over `X` is itself the pullback of `U ⟶ X`.  Its range is
therefore exactly the inverse image of the open range of `U` under the
projection to `X`.

Combining this with scheme-theoretic image commuting with open
restriction identifies the inverse image of `U` in the projective graph
closure with `U` itself.  In particular, an affine graph domain gives
an affine open in its graph closure.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-- The open base-change factor is the pullback of the original open
immersion along the projection from relative projective space. -/
theorem isPullback_relativeProjectiveGraphOpenFactor
    {k : Type u} [CommRing k] {U X : Scheme.{u}}
    (s : X ⟶ Spec (CommRingCat.of k)) {d : ℕ}
    (u : U ⟶ X) (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d) :
    IsPullback
      (relativeProjectiveGraphOpenFactor s u p h)
      (pullback.fst (p ≫ toSpec k d) (toSpec k d))
      (relativeToBase s d)
      u := by
  let rightSquare :
      IsPullback
        (relativeToProjective s d)
        (relativeToBase s d)
        (toSpec k d)
        s :=
    (IsPullback.of_hasPullback s (toSpec k d)).flip
  let outerRectangle :
      IsPullback
        (relativeProjectiveGraphOpenFactor s u p h ≫
          relativeToProjective s d)
        (pullback.fst (p ≫ toSpec k d) (toSpec k d))
        (toSpec k d)
        (u ≫ s) := by
    convert
      (IsPullback.of_hasPullback
        (p ≫ toSpec k d) (toSpec k d)).flip using 1
    · simp [relativeProjectiveGraphOpenFactor, pullback.map,
        pullback.lift_snd]
  exact
    outerRectangle.of_right
      (by
        simp [relativeProjectiveGraphOpenFactor, pullback.map,
          pullback.lift_fst])
      rightSquare

/-- The range of the open base-change factor is precisely the inverse
image of the original open range under the relative projection. -/
theorem relativeProjectiveGraphOpenFactor_opensRange
    {k : Type u} [CommRing k] {U X : Scheme.{u}}
    (s : X ⟶ Spec (CommRingCat.of k)) {d : ℕ}
    (u : U ⟶ X) [IsOpenImmersion u]
    (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d) :
    (relativeProjectiveGraphOpenFactor s u p h).opensRange =
      relativeToBase s d ⁻¹ᵁ u.opensRange := by
  have H :=
    IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
      (isPullback_relativeProjectiveGraphOpenFactor s u p h).flip
      (⊤ : U.Opens)
  simpa using H

/-- The inverse image of the original open in the projective graph
closure is canonically isomorphic to the graph domain. -/
def domainIsoProjectiveGraphClosureBaseRestriction
    {k : Type u} [CommRing k] {U X : Scheme.{u}}
    (s : X ⟶ Spec (CommRingCat.of k)) {d : ℕ}
    (u : U ⟶ X) [IsOpenImmersion u] [QuasiCompact u]
    (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d) :
    U ≅
      (projectiveGraphClosureToBase s d u p h ⁻¹ᵁ
        u.opensRange).toScheme := by
  let targetOpen :=
    (relativeProjectiveGraphOpenFactor s u p h).opensRange
  have htarget :
      targetOpen =
        relativeToBase s d ⁻¹ᵁ u.opensRange :=
    relativeProjectiveGraphOpenFactor_opensRange s u p h
  have hpreimage :
      projectiveGraphClosureι s d u p h ⁻¹ᵁ targetOpen =
        projectiveGraphClosureToBase s d u p h ⁻¹ᵁ
          u.opensRange := by
    rw [htarget, ← Scheme.Hom.comp_preimage]
    rfl
  exact
    domainIsoPullbackProjectiveGraphClosure s u p h ≪≫
      pullbackSymmetry targetOpen.ι
        (projectiveGraphClosureι s d u p h) ≪≫
      pullbackRestrictIsoRestrict
        (projectiveGraphClosureι s d u p h) targetOpen ≪≫
      (projectiveGraphClosure s d u p h).isoOfEq hpreimage

/-- If the graph domain is affine, then the inverse image of its open
range in the projective graph closure is affine. -/
theorem isAffine_projectiveGraphClosure_baseRestriction
    {k : Type u} [CommRing k] {U X : Scheme.{u}}
    (s : X ⟶ Spec (CommRingCat.of k)) {d : ℕ}
    (u : U ⟶ X) [IsOpenImmersion u] [QuasiCompact u]
    (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d)
    [IsAffine U] :
    IsAffine
      ((projectiveGraphClosureToBase s d u p h ⁻¹ᵁ
        u.opensRange).toScheme) := by
  let e :=
    domainIsoProjectiveGraphClosureBaseRestriction s u p h
  exact IsAffine.of_isIso e.inv

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

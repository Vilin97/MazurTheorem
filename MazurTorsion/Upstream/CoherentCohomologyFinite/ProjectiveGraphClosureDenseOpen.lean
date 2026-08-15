/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveGraphClosureBaseRestriction

/-!
# The dense-open comparison for a projective graph closure

The inverse image of the graph domain in a projective graph closure is
not merely isomorphic to that domain.  The canonical isomorphism
commutes with the maps to the corresponding open of the base.  Thus the
first graph-closure projection is an isomorphism over the original open
subscheme.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-- The canonical identification of the graph domain with the inverse
image of its open range commutes with the maps to that open range. -/
@[reassoc]
theorem domainIsoProjectiveGraphClosureBaseRestriction_hom_restrict
    {k : Type u} [CommRing k] {U X : Scheme.{u}}
    (s : X ⟶ Spec (CommRingCat.of k)) {d : ℕ}
    (u : U ⟶ X) [IsOpenImmersion u] [QuasiCompact u]
    (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d) :
    (domainIsoProjectiveGraphClosureBaseRestriction
        s u p h).hom ≫
        (projectiveGraphClosureToBase s d u p h ∣_
          u.opensRange) =
      u.isoOpensRange.hom := by
  rw [← cancel_mono u.opensRange.ι]
  simp only [Category.assoc, morphismRestrict_ι,
    Scheme.Hom.isoOpensRange_hom_ι]
  simp only [domainIsoProjectiveGraphClosureBaseRestriction,
    domainIsoPullbackProjectiveGraphClosure,
    Iso.trans_hom, Category.assoc,
    Scheme.isoOfEq_hom_ι_assoc,
    pullbackRestrictIsoRestrict_hom_ι_assoc,
    pullbackSymmetry_hom_comp_fst_assoc,
    SchemeTheoreticImage.sourceMorphismRestrictIsoPullbackImage_hom_snd_assoc,
    toProjectiveGraphClosure_toBase]
  change U.topIso.inv ≫ U.topIso.hom ≫ u = u
  simp

/-- The restriction of the first graph-closure projection to the
original open range is an isomorphism. -/
theorem isIso_projectiveGraphClosureToBase_restrict_opensRange
    {k : Type u} [CommRing k] {U X : Scheme.{u}}
    (s : X ⟶ Spec (CommRingCat.of k)) {d : ℕ}
    (u : U ⟶ X) [IsOpenImmersion u] [QuasiCompact u]
    (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d) :
    IsIso
      (projectiveGraphClosureToBase s d u p h ∣_
        u.opensRange) := by
  let e :=
    domainIsoProjectiveGraphClosureBaseRestriction s u p h
  apply
    (isIso_comp_left_iff e.hom
      (projectiveGraphClosureToBase s d u p h ∣_
        u.opensRange)).mp
  rw [domainIsoProjectiveGraphClosureBaseRestriction_hom_restrict]
  infer_instance

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

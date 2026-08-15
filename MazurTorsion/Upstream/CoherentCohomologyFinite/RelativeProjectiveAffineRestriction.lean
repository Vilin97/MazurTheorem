/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveModification

/-!
# Restricting relative projective factorizations

A closed immersion into relative projective space remains such after
restricting the base to an open subscheme.  We record the concrete
isomorphism between the restricted relative projective space and the
corresponding pullback over the open base.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-- Restricting relative projective space to an open of its base gives
relative projective space over that open. -/
def relativeSchemeRestrictIso
    {k : Type u} [CommRing k] {S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ)
    (U : S.Opens) :
    ((relativeToBase s d) ⁻¹ᵁ U).toScheme ≅
      relativeScheme (U.ι ≫ s) d :=
  (pullbackRestrictIsoRestrict (relativeToBase s d) U).symm ≪≫
    pullbackSymmetry (relativeToBase s d) U.ι ≪≫
    pullbackRightPullbackFstIso s (toSpec k d) U.ι

/-- The relative-projective restriction isomorphism commutes with the
projections to the open base. -/
@[reassoc]
theorem relativeSchemeRestrictIso_hom_relativeToBase
    {k : Type u} [CommRing k] {S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ)
    (U : S.Opens) :
    (relativeSchemeRestrictIso s d U).hom ≫
        relativeToBase (U.ι ≫ s) d =
      morphismRestrict (relativeToBase s d) U := by
  simp [relativeSchemeRestrictIso, morphismRestrict]

namespace IsRelativeProjectiveFactorization

/-- A relative projective factorization restricts to every open
subscheme of its base. -/
theorem restrict
    {k : Type u} [CommRing k] {Y S : Scheme.{u}}
    {s : S ⟶ Spec (CommRingCat.of k)}
    {f : Y ⟶ S}
    (h : IsRelativeProjectiveFactorization s f)
    (U : S.Opens) :
    IsRelativeProjectiveFactorization
      (U.ι ≫ s) (morphismRestrict f U) := by
  obtain ⟨d, i, hi, hif⟩ := h
  letI : IsClosedImmersion i := hi
  let V : (relativeScheme s d).Opens :=
    (relativeToBase s d) ⁻¹ᵁ U
  have hpreimage :
      f ⁻¹ᵁ U = i ⁻¹ᵁ V := by
    dsimp only [V]
    rw [← Scheme.Hom.comp_preimage, hif]
  let e :
      (f ⁻¹ᵁ U).toScheme ≅
        (i ⁻¹ᵁ V).toScheme :=
    Y.isoOfEq hpreimage
  let j :
      (f ⁻¹ᵁ U).toScheme ⟶
        relativeScheme (U.ι ≫ s) d :=
    e.hom ≫ morphismRestrict i V ≫
      (relativeSchemeRestrictIso s d U).hom
  have hj : IsClosedImmersion j := by
    dsimp only [j]
    infer_instance
  refine ⟨d, j, hj, ?_⟩
  dsimp only [j]
  rw [Category.assoc, Category.assoc,
    relativeSchemeRestrictIso_hom_relativeToBase]
  rw [← cancel_mono U.ι]
  simp only [Category.assoc, morphismRestrict_ι]
  change
    e.hom ≫ (morphismRestrict i V) ≫ V.ι ≫
        relativeToBase s d =
      (f ⁻¹ᵁ U).ι ≫ f
  simp only [morphismRestrict_ι_assoc]
  dsimp only [e]
  simp only [Scheme.isoOfEq_hom_ι_assoc]
  rw [hif]

end IsRelativeProjectiveFactorization

/-- The relative projective factorization of a projective modification
restricts over every open of the original scheme. -/
theorem ProjectiveModification.relativeProjective_restrict
    {k : Type u} [CommRing k] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)}
    (P : MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveModification f)
    (U : X.Opens) :
    IsRelativeProjectiveFactorization
      (U.ι ≫ f) (morphismRestrict P.toOriginal U) :=
  P.relativeProjective.restrict U

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

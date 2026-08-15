/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineOpenProjectiveMapCompatibility
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveFactorizationChoice

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-!
# An affine-base projective map from chosen relative factorization data

Restriction of a chosen relative projective factorization to an affine
base open preserves its projective dimension.  After identifying the
relative projective space with ordinary projective space over the ring
of sections, the resulting projective map is compatible with coefficient
extension back to the original projective space.
-/

@[reassoc]
theorem relativeSchemeRestrictIso_hom_relativeToProjective
    {k : Type u} [CommRing k] {S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ)
    (U : S.Opens) :
    (relativeSchemeRestrictIso s d U).hom ≫
        relativeToProjective (U.ι ≫ s) d =
      ((relativeToBase s d) ⁻¹ᵁ U).ι ≫
        relativeToProjective s d := by
  simp [relativeSchemeRestrictIso]
  rw [← Category.assoc,
    pullbackRestrictIsoRestrict_inv_fst]

namespace IsRelativeProjectiveFactorization

variable {k : Type u} [CommRing k]
  {Y S : Scheme.{u}}
  {s : S ⟶ Spec (CommRingCat.of k)}
  {f : Y ⟶ S}

def chosenRestrictionAmbientOpen
    (h : IsRelativeProjectiveFactorization s f)
    (U : S.Opens) :
    (relativeScheme s h.chosenDimension).Opens :=
  relativeToBase s h.chosenDimension ⁻¹ᵁ U

theorem chosenRestrictionSourcePreimage
    (h : IsRelativeProjectiveFactorization s f)
    (U : S.Opens) :
    f ⁻¹ᵁ U =
      h.chosenEmbedding ⁻¹ᵁ
        h.chosenRestrictionAmbientOpen U := by
  rw [chosenRestrictionAmbientOpen,
    ← Scheme.Hom.comp_preimage,
    h.chosenEmbedding_relativeToBase]

def chosenRestrictionSourceIso
    (h : IsRelativeProjectiveFactorization s f)
    (U : S.Opens) :
    (f ⁻¹ᵁ U).toScheme ≅
      (h.chosenEmbedding ⁻¹ᵁ
        h.chosenRestrictionAmbientOpen U).toScheme :=
  Y.isoOfEq (h.chosenRestrictionSourcePreimage U)

def chosenRestrictedEmbedding
    (h : IsRelativeProjectiveFactorization s f)
    (U : S.Opens) :
    (f ⁻¹ᵁ U).toScheme ⟶
      relativeScheme (U.ι ≫ s) h.chosenDimension :=
  (h.chosenRestrictionSourceIso U).hom ≫
    (h.chosenEmbedding ∣_
      h.chosenRestrictionAmbientOpen U) ≫
    (relativeSchemeRestrictIso
      s h.chosenDimension U).hom

theorem chosenRestrictedEmbedding_isClosedImmersion
    (h : IsRelativeProjectiveFactorization s f)
    (U : S.Opens) :
    IsClosedImmersion (h.chosenRestrictedEmbedding U) := by
  letI : IsClosedImmersion h.chosenEmbedding :=
    h.chosenEmbedding_isClosedImmersion
  let hsource : IsClosedImmersion
      (h.chosenRestrictionSourceIso U).hom :=
    inferInstance
  let hrestriction : IsClosedImmersion
      (h.chosenEmbedding ∣_ h.chosenRestrictionAmbientOpen U) :=
    inferInstance
  let hrelative : IsClosedImmersion
      (relativeSchemeRestrictIso s h.chosenDimension U).hom :=
    inferInstance
  let htail : IsClosedImmersion
      ((h.chosenEmbedding ∣_ h.chosenRestrictionAmbientOpen U) ≫
        (relativeSchemeRestrictIso s h.chosenDimension U).hom) :=
    @IsClosedImmersion.comp _ _ _ _ _ hrestriction hrelative
  dsimp only [chosenRestrictedEmbedding]
  exact @IsClosedImmersion.comp _ _ _ _ _ hsource htail

attribute [local instance]
  chosenRestrictedEmbedding_isClosedImmersion

@[reassoc]
theorem chosenRestrictedEmbedding_relativeToBase
    (h : IsRelativeProjectiveFactorization s f)
    (U : S.Opens) :
    h.chosenRestrictedEmbedding U ≫
        relativeToBase
          (U.ι ≫ s) h.chosenDimension =
      morphismRestrict f U := by
  dsimp only [chosenRestrictedEmbedding,
    chosenRestrictionAmbientOpen]
  rw [Category.assoc, Category.assoc,
    relativeSchemeRestrictIso_hom_relativeToBase]
  rw [← cancel_mono U.ι]
  simp only [Category.assoc, morphismRestrict_ι]
  change
    (h.chosenRestrictionSourceIso U).hom ≫
        (h.chosenEmbedding ∣_
          h.chosenRestrictionAmbientOpen U) ≫
        (h.chosenRestrictionAmbientOpen U).ι ≫
        relativeToBase s h.chosenDimension =
      (f ⁻¹ᵁ U).ι ≫ f
  simp only [morphismRestrict_ι_assoc]
  dsimp only [chosenRestrictionSourceIso]
  simp only [Scheme.isoOfEq_hom_ι_assoc]
  rw [h.chosenEmbedding_relativeToBase]

@[reassoc]
theorem chosenRestrictedEmbedding_relativeToProjective
    (h : IsRelativeProjectiveFactorization s f)
    (U : S.Opens) :
    h.chosenRestrictedEmbedding U ≫
        relativeToProjective
          (U.ι ≫ s) h.chosenDimension =
      (f ⁻¹ᵁ U).ι ≫ h.chosenProjectiveMap := by
  dsimp only [chosenRestrictedEmbedding,
    chosenRestrictionAmbientOpen]
  rw [Category.assoc, Category.assoc,
    relativeSchemeRestrictIso_hom_relativeToProjective]
  change
    (h.chosenRestrictionSourceIso U).hom ≫
        (h.chosenEmbedding ∣_
          h.chosenRestrictionAmbientOpen U) ≫
        (h.chosenRestrictionAmbientOpen U).ι ≫
        relativeToProjective s h.chosenDimension =
      (f ⁻¹ᵁ U).ι ≫ h.chosenEmbedding ≫
        relativeToProjective s h.chosenDimension
  simp only [morphismRestrict_ι_assoc]
  dsimp only [chosenRestrictionSourceIso]
  simp only [Scheme.isoOfEq_hom_ι_assoc]

def chosenAffineProjectiveEmbedding
    (h : IsRelativeProjectiveFactorization s f)
    (U : S.Opens) (hU : IsAffineOpen U) :
    letI : Algebra k Γ(S, U) :=
      (affineOpenCoefficientMap s U hU).hom.toAlgebra
    (f ⁻¹ᵁ U).toScheme ⟶
      scheme Γ(S, U) h.chosenDimension := by
  letI : Algebra k Γ(S, U) :=
    (affineOpenCoefficientMap s U hU).hom.toAlgebra
  exact
    h.chosenRestrictedEmbedding U ≫
      (relativeSchemeAffineProjectiveIso
        s h.chosenDimension U hU).hom

theorem chosenAffineProjectiveEmbedding_isClosedImmersion
    (h : IsRelativeProjectiveFactorization s f)
    (U : S.Opens) (hU : IsAffineOpen U) :
    letI : Algebra k Γ(S, U) :=
      (affineOpenCoefficientMap s U hU).hom.toAlgebra
    IsClosedImmersion
      (h.chosenAffineProjectiveEmbedding U hU) := by
  letI : Algebra k Γ(S, U) :=
    (affineOpenCoefficientMap s U hU).hom.toAlgebra
  dsimp only [chosenAffineProjectiveEmbedding]
  infer_instance

attribute [local instance]
  chosenAffineProjectiveEmbedding_isClosedImmersion

@[reassoc]
theorem chosenAffineProjectiveEmbedding_toSpec
    (h : IsRelativeProjectiveFactorization s f)
    (U : S.Opens) (hU : IsAffineOpen U) :
    letI : Algebra k Γ(S, U) :=
      (affineOpenCoefficientMap s U hU).hom.toAlgebra
    h.chosenAffineProjectiveEmbedding U hU ≫
        toSpec Γ(S, U) h.chosenDimension =
      morphismRestrict f U ≫ hU.isoSpec.hom := by
  letI : Algebra k Γ(S, U) :=
    (affineOpenCoefficientMap s U hU).hom.toAlgebra
  dsimp only [chosenAffineProjectiveEmbedding]
  rw [Category.assoc,
    relativeSchemeAffineProjectiveIso_hom_toSpec]
  rw [← Category.assoc,
    h.chosenRestrictedEmbedding_relativeToBase]

@[reassoc]
theorem chosenAffineProjectiveEmbedding_coefficientMap
    (h : IsRelativeProjectiveFactorization s f)
    (U : S.Opens) (hU : IsAffineOpen U) :
    letI : Algebra k Γ(S, U) :=
      (affineOpenCoefficientMap s U hU).hom.toAlgebra
    h.chosenAffineProjectiveEmbedding U hU ≫
        coefficientMap
          (algebraMap k Γ(S, U))
          h.chosenDimension =
      (f ⁻¹ᵁ U).ι ≫ h.chosenProjectiveMap := by
  letI : Algebra k Γ(S, U) :=
    (affineOpenCoefficientMap s U hU).hom.toAlgebra
  dsimp only [chosenAffineProjectiveEmbedding]
  rw [Category.assoc,
    relativeSchemeAffineProjectiveIso_hom_coefficientMap]
  exact
    h.chosenRestrictedEmbedding_relativeToProjective U

end IsRelativeProjectiveFactorization

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeTheoreticImageOpenRestriction
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeTheoreticImageClosedFactor

/-!
# Closed factors for target-open restrictions of scheme images

Let `r : U ⟶ Y` and `q : Y ⟶ T`.  The inverse image of an open
`W ⊆ T` in the scheme-theoretic image of `r` is the scheme-theoretic
image of `r` restricted over `q ⁻¹ W`.  If this restricted morphism
factors through a scheme closed both in the ambient open and over `W`,
then the induced projection of the global image to `W` is closed.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

/-- The local scheme-theoretic image over an open of a further target. -/
abbrev targetOpenImage
    {U Y T : Scheme.{u}}
    (r : U ⟶ Y) (q : Y ⟶ T) (W : T.Opens) :
    Scheme.{u} :=
  (r ∣_ (q ⁻¹ᵁ W)).image

/-- The local image maps canonically to the chosen target open. -/
def targetOpenImageToTarget
    {U Y T : Scheme.{u}}
    (r : U ⟶ Y) (q : Y ⟶ T) (W : T.Opens) :
    targetOpenImage r q W ⟶ W.toScheme :=
  (r ∣_ (q ⁻¹ᵁ W)).imageι ≫
    (q ∣_ W)

/-- The local image is canonically the corresponding open restriction
of the global scheme-theoretic image. -/
def targetOpenImageIsoImageRestriction
    {U Y T : Scheme.{u}}
    (r : U ⟶ Y) [QuasiCompact r]
    (q : Y ⟶ T) (W : T.Opens) :
    targetOpenImage r q W ≅
      ((r.imageι ≫ q) ⁻¹ᵁ W).toScheme := by
  have htarget :
      r.imageι ⁻¹ᵁ (q ⁻¹ᵁ W) =
        (r.imageι ≫ q) ⁻¹ᵁ W := by
    rw [← Scheme.Hom.comp_preimage]
  exact
    SchemeTheoreticImage.imageMorphismRestrictIsoPullback
        r (q ⁻¹ᵁ W) ≪≫
      pullbackSymmetry (q ⁻¹ᵁ W).ι r.imageι ≪≫
      pullbackRestrictIsoRestrict r.imageι (q ⁻¹ᵁ W) ≪≫
      r.image.isoOfEq htarget

/-- The local-to-global image isomorphism commutes with the maps to the
ambient scheme. -/
@[reassoc]
theorem targetOpenImageIsoImageRestriction_hom_toAmbient
    {U Y T : Scheme.{u}}
    (r : U ⟶ Y) [QuasiCompact r]
    (q : Y ⟶ T) (W : T.Opens) :
    (targetOpenImageIsoImageRestriction r q W).hom ≫
          ((r.imageι ≫ q) ⁻¹ᵁ W).ι ≫
        r.imageι =
      (r ∣_ (q ⁻¹ᵁ W)).imageι ≫
        (q ⁻¹ᵁ W).ι := by
  simp only [targetOpenImageIsoImageRestriction,
    Iso.trans_hom, Category.assoc,
    Scheme.isoOfEq_hom_ι_assoc,
    pullbackRestrictIsoRestrict_hom_ι_assoc,
    pullbackSymmetry_hom_comp_fst_assoc]
  rw [← pullback.condition]
  rw [← Category.assoc,
    SchemeTheoreticImage.imageMorphismRestrictIsoPullback_hom_fst]

/-- The preceding isomorphism commutes with the maps to the target
open. -/
@[reassoc]
theorem targetOpenImageIsoImageRestriction_hom_toTarget
    {U Y T : Scheme.{u}}
    (r : U ⟶ Y) [QuasiCompact r]
    (q : Y ⟶ T) (W : T.Opens) :
    (targetOpenImageIsoImageRestriction r q W).hom ≫
        ((r.imageι ≫ q) ∣_ W) =
      targetOpenImageToTarget r q W := by
  rw [← cancel_mono W.ι]
  simp only [Category.assoc, morphismRestrict_ι]
  change
    (targetOpenImageIsoImageRestriction r q W).hom ≫
          ((r.imageι ≫ q) ⁻¹ᵁ W).ι ≫
          r.imageι ≫ q =
      (r ∣_ (q ⁻¹ᵁ W)).imageι ≫
        (q ∣_ W) ≫ W.ι
  simp only [targetOpenImageIsoImageRestriction,
    Iso.trans_hom, Category.assoc,
    Scheme.isoOfEq_hom_ι_assoc,
    pullbackRestrictIsoRestrict_hom_ι_assoc,
    pullbackSymmetry_hom_comp_fst_assoc,
    ← pullback.condition_assoc,
    SchemeTheoreticImage.imageMorphismRestrictIsoPullback_hom_fst_assoc]
  rw [morphismRestrict_ι]

/-- A closed factor for the restriction of `r` over one target open. -/
structure TargetOpenClosedFactor
    {U Y T : Scheme.{u}}
    (r : U ⟶ Y) (q : Y ⟶ T) (W : T.Opens) where
  carrier : Scheme.{u}
  sourceToFactor :
    (r ⁻¹ᵁ (q ⁻¹ᵁ W)).toScheme ⟶ carrier
  factorToAmbientOpen :
    carrier ⟶ (q ⁻¹ᵁ W).toScheme
  graphRestrict_factor :
    r ∣_ (q ⁻¹ᵁ W) =
      sourceToFactor ≫ factorToAmbientOpen
  isClosedImmersion_factorToAmbientOpen :
    IsClosedImmersion factorToAmbientOpen
  factorToTargetOpen :
    carrier ⟶ W.toScheme
  factorToAmbientOpen_toTarget :
    factorToAmbientOpen ≫ (q ∣_ W) =
      factorToTargetOpen
  isClosedImmersion_factorToTargetOpen :
    IsClosedImmersion factorToTargetOpen

attribute [instance]
  TargetOpenClosedFactor.isClosedImmersion_factorToAmbientOpen
  TargetOpenClosedFactor.isClosedImmersion_factorToTargetOpen

namespace TargetOpenClosedFactor

/-- The local scheme-theoretic image maps as a closed subscheme into
the chosen factor. -/
def imageToFactor
    {U Y T : Scheme.{u}}
    {r : U ⟶ Y} {q : Y ⟶ T} {W : T.Opens}
    (D : TargetOpenClosedFactor r q W) :
    targetOpenImage r q W ⟶ D.carrier :=
  SchemeTheoreticImage.toClosedFactor
    (r ∣_ (q ⁻¹ᵁ W))
    D.sourceToFactor D.factorToAmbientOpen
    D.graphRestrict_factor

instance isClosedImmersion_imageToFactor
    {U Y T : Scheme.{u}}
    {r : U ⟶ Y} {q : Y ⟶ T} {W : T.Opens}
    (D : TargetOpenClosedFactor r q W) :
    IsClosedImmersion D.imageToFactor :=
  SchemeTheoreticImage.isClosedImmersion_toClosedFactor
    (r ∣_ (q ⁻¹ᵁ W))
    D.sourceToFactor D.factorToAmbientOpen
    D.graphRestrict_factor

/-- The local image projection factors through the chosen closed map
to the target open. -/
theorem imageToTarget_eq
    {U Y T : Scheme.{u}}
    {r : U ⟶ Y} {q : Y ⟶ T} {W : T.Opens}
    (D : TargetOpenClosedFactor r q W) :
    targetOpenImageToTarget r q W =
      D.imageToFactor ≫ D.factorToTargetOpen := by
  rw [targetOpenImageToTarget,
    ← D.factorToAmbientOpen_toTarget]
  unfold imageToFactor
  rw [SchemeTheoreticImage.toClosedFactor_comp_assoc]

/-- A closed factor makes the corresponding restriction of the global
scheme-image projection a closed immersion. -/
theorem isClosedImmersion_imageProjection_restrict
    {U Y T : Scheme.{u}}
    {r : U ⟶ Y} [QuasiCompact r]
    {q : Y ⟶ T} {W : T.Opens}
    (D : TargetOpenClosedFactor r q W) :
    IsClosedImmersion ((r.imageι ≫ q) ∣_ W) := by
  letI :
      IsClosedImmersion
        (targetOpenImageToTarget r q W) := by
    rw [D.imageToTarget_eq]
    infer_instance
  let e :
      Arrow.mk (targetOpenImageToTarget r q W) ≅
        Arrow.mk ((r.imageι ≫ q) ∣_ W) :=
    Arrow.isoMk'
      (targetOpenImageToTarget r q W)
      ((r.imageι ≫ q) ∣_ W)
      (targetOpenImageIsoImageRestriction r q W)
      (Iso.refl W.toScheme)
      (by
        simpa using
          targetOpenImageIsoImageRestriction_hom_toTarget
            r q W)
  exact
    (MorphismProperty.arrow_mk_iso_iff
      @IsClosedImmersion e).1 inferInstance

end TargetOpenClosedFactor

end MazurTorsion.AlgebraicGeometry.CoherentCohomology

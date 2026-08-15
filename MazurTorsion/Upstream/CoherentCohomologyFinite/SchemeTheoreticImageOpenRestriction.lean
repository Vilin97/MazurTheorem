/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Scheme-theoretic images and restriction to an open

For a quasi-compact morphism, its ideal-sheaf kernel commutes with
restriction to an open subset of the target.  Consequently, the
scheme-theoretic image of the restricted morphism is the pullback of the
global scheme-theoretic image.

This is the base-change fact used to identify a graph closure with its
original graph over the open where the rational map is defined.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

namespace SchemeTheoreticImage

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]

/-- Transporting a closed subscheme along equality of its ideal data
commutes with the closed immersion into the ambient scheme. -/
@[reassoc]
theorem eqToIso_subscheme_hom_subschemeι
    {S : Scheme.{u}} {I J : S.IdealSheafData}
    (h : I = J) :
    (eqToIso
      (congrArg
        (fun K : S.IdealSheafData => K.subscheme) h)).hom ≫
        J.subschemeι =
      I.subschemeι := by
  subst h
  simp

/-- The ideal defining a scheme-theoretic image commutes with
restriction to an open subset of the target. -/
theorem ker_morphismRestrict
    (U : Y.Opens) :
    (f ∣_ U).ker = f.ker.comap U.ι := by
  apply Scheme.IdealSheafData.ext
  funext V
  rw [Scheme.ker_morphismRestrict_ideal,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  ext x
  simp
  rfl

/-- The scheme-theoretic image after restriction to an open is the
pullback of the global scheme-theoretic image to that open. -/
def imageMorphismRestrictIsoPullback
    (U : Y.Opens) :
    (f ∣_ U).image ≅ pullback U.ι f.imageι :=
  eqToIso
      (congrArg
        (fun I : U.toScheme.IdealSheafData => I.subscheme)
        (ker_morphismRestrict f U)) ≪≫
    f.ker.comapIso U.ι

/-- Under the open-restriction image isomorphism, the first pullback
projection is the closed immersion of the restricted
scheme-theoretic image. -/
@[reassoc]
theorem imageMorphismRestrictIsoPullback_hom_fst
    (U : Y.Opens) :
    (imageMorphismRestrictIsoPullback f U).hom ≫
        pullback.fst U.ι f.imageι =
      (f ∣_ U).imageι := by
  simp only [imageMorphismRestrictIsoPullback,
    Iso.trans_hom, Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst]
  rw [eqToIso_subscheme_hom_subschemeι]
  exact ker_morphismRestrict f U

/-- If the restriction of a morphism to an open is already a closed
immersion, then the pullback of its global scheme-theoretic image over
that open is canonically isomorphic to the restricted source. -/
def sourceMorphismRestrictIsoPullbackImage
    (U : Y.Opens) [IsClosedImmersion (f ∣_ U)] :
    (f ⁻¹ᵁ U).toScheme ≅ pullback U.ι f.imageι :=
  asIso (f ∣_ U).toImage ≪≫
    imageMorphismRestrictIsoPullback f U

/-- Under the preceding isomorphism, the projection to the target open
is the restricted morphism. -/
@[reassoc]
theorem sourceMorphismRestrictIsoPullbackImage_hom_fst
    (U : Y.Opens) [IsClosedImmersion (f ∣_ U)] :
    (sourceMorphismRestrictIsoPullbackImage f U).hom ≫
        pullback.fst U.ι f.imageι =
      f ∣_ U := by
  simp only [sourceMorphismRestrictIsoPullbackImage,
    imageMorphismRestrictIsoPullback, Iso.trans_hom,
    asIso_hom, Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst]
  rw [eqToIso_subscheme_hom_subschemeι,
    Scheme.Hom.toImage_imageι]
  exact ker_morphismRestrict f U

/-- Under the same isomorphism, the projection to the global
scheme-theoretic image is the restricted-source inclusion followed by
the canonical map to the image. -/
@[reassoc]
theorem sourceMorphismRestrictIsoPullbackImage_hom_snd
    (U : Y.Opens) [IsClosedImmersion (f ∣_ U)] :
    (sourceMorphismRestrictIsoPullbackImage f U).hom ≫
        pullback.snd U.ι f.imageι =
      (f ⁻¹ᵁ U).ι ≫ f.toImage := by
  rw [← cancel_mono f.imageι]
  rw [Category.assoc, pullback.condition.symm,
    ← Category.assoc,
    sourceMorphismRestrictIsoPullbackImage_hom_fst,
    morphismRestrict_ι,
    Category.assoc, Scheme.Hom.toImage_imageι]

end SchemeTheoreticImage

end MazurTorsion.AlgebraicGeometry.CoherentCohomology

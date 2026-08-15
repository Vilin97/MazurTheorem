/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineOpenProjectiveFactorization

/-!
# Projective-map compatibility over an affine base open

The identification of relative projective space over an affine open
with ordinary projective space over its section ring commutes with the
map back to projective space over the original coefficient ring.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-- The coefficient-base-change pullback isomorphism commutes with the
projection to the original projective space. -/
@[reassoc]
lemma coefficientRelativeSchemeIso_hom_relativeToProjective
    (k R : Type u) [CommRing k] [CommRing R]
    [Algebra k R] (d : ℕ) :
    (coefficientRelativeSchemeIso k R d).hom ≫
        relativeToProjective
          (Spec.map
            (CommRingCat.ofHom (algebraMap k R))) d =
      coefficientMap (algebraMap k R) d := by
  simp [coefficientRelativeSchemeIso]

/-- Changing an affine base to its spectrum presentation leaves the
projective projection unchanged. -/
@[reassoc]
lemma relativeSchemeAffineBaseIso_hom_relativeToProjective
    {k : Type u} [CommRing k] {S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ)
    (U : S.Opens) (hU : IsAffineOpen U) :
    (relativeSchemeAffineBaseIso s d U hU).hom ≫
        relativeToProjective
          (Spec.map
            (affineOpenCoefficientMap s U hU)) d =
      relativeToProjective (U.ι ≫ s) d := by
  simp only [relativeSchemeAffineBaseIso,
    asIso_hom, relativeToProjective, pullback.map]
  rw [pullback.lift_snd]
  simp

/-- The affine-projective identification followed by coefficient
extension is the original relative-projective projection. -/
@[reassoc]
lemma relativeSchemeAffineProjectiveIso_hom_coefficientMap
    {k : Type u} [CommRing k] {S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ)
    (U : S.Opens) (hU : IsAffineOpen U) :
    letI : Algebra k Γ(S, U) :=
      (affineOpenCoefficientMap s U hU).hom.toAlgebra
    (relativeSchemeAffineProjectiveIso s d U hU).hom ≫
        coefficientMap (algebraMap k Γ(S, U)) d =
      relativeToProjective (U.ι ≫ s) d := by
  letI : Algebra k Γ(S, U) :=
    (affineOpenCoefficientMap s U hU).hom.toAlgebra
  have hprojectiveIso :
      relativeSchemeAffineProjectiveIso s d U hU =
        relativeSchemeAffineBaseIso s d U hU ≪≫
          (coefficientRelativeSchemeIso k Γ(S, U) d).symm := by
    rfl
  rw [hprojectiveIso]
  have hhom :
      (relativeSchemeAffineBaseIso s d U hU ≪≫
          (coefficientRelativeSchemeIso k Γ(S, U) d).symm).hom =
        (relativeSchemeAffineBaseIso s d U hU).hom ≫
          (coefficientRelativeSchemeIso k Γ(S, U) d).inv := by
    rfl
  rw [hhom]
  rw [← coefficientRelativeSchemeIso_hom_relativeToProjective
    k Γ(S, U) d]
  simp only [Category.assoc,
    Iso.inv_hom_id_assoc]
  exact
    relativeSchemeAffineBaseIso_hom_relativeToProjective
      s d U hU

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

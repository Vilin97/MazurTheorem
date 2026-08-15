/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSpaceBaseChange
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveAffineRestriction

/-!
# Projective factorizations over affine opens

A relative projective factorization over a scheme becomes an ordinary
projective-space factorization after restricting to an affine open and
identifying that open with the spectrum of its section ring.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-- The coefficient map associated to an affine open of a scheme over
`Spec k`. -/
def affineOpenCoefficientMap
    {k : Type u} [CommRing k] {S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k))
    (U : S.Opens) (hU : IsAffineOpen U) :
    CommRingCat.of k ⟶ CommRingCat.of Γ(S, U) :=
  Spec.preimage (hU.isoSpec.inv ≫ U.ι ≫ s)

/-- Absolute projective space after coefficient extension is the
corresponding relative projective space. -/
def coefficientRelativeSchemeIso
    (k R : Type u) [CommRing k] [CommRing R]
    [Algebra k R] (d : ℕ) :
    scheme R d ≅
      relativeScheme
        (Spec.map
          (CommRingCat.ofHom (algebraMap k R))) d :=
  (isPullback_coefficientMap k R d).isoPullback ≪≫
    pullbackSymmetry
      (toSpec k d)
      (Spec.map
        (CommRingCat.ofHom (algebraMap k R)))

@[reassoc]
lemma coefficientRelativeSchemeIso_hom_relativeToBase
    (k R : Type u) [CommRing k] [CommRing R]
    [Algebra k R] (d : ℕ) :
    (coefficientRelativeSchemeIso k R d).hom ≫
        relativeToBase
          (Spec.map
            (CommRingCat.ofHom (algebraMap k R))) d =
      toSpec R d := by
  simp [coefficientRelativeSchemeIso]

/-- Changing an affine base to its canonical spectrum presentation
induces an isomorphism of relative projective spaces. -/
def relativeSchemeAffineBaseIso
    {k : Type u} [CommRing k] {S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ)
    (U : S.Opens) (hU : IsAffineOpen U) :
    relativeScheme (U.ι ≫ s) d ≅
      relativeScheme
        (Spec.map
          (affineOpenCoefficientMap s U hU)) d :=
  asIso
    (pullback.map
      (U.ι ≫ s) (toSpec k d)
      (Spec.map
        (affineOpenCoefficientMap s U hU))
      (toSpec k d)
      hU.isoSpec.hom (𝟙 _) (𝟙 _)
      (by
        simp only [Category.comp_id,
          affineOpenCoefficientMap,
          Spec.map_preimage,
          Iso.hom_inv_id_assoc])
      (by simp))

@[reassoc]
lemma relativeSchemeAffineBaseIso_hom_relativeToBase
    {k : Type u} [CommRing k] {S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ)
    (U : S.Opens) (hU : IsAffineOpen U) :
    (relativeSchemeAffineBaseIso s d U hU).hom ≫
        relativeToBase
          (Spec.map
            (affineOpenCoefficientMap s U hU)) d =
      relativeToBase (U.ι ≫ s) d ≫
        hU.isoSpec.hom := by
  change
    (relativeSchemeAffineBaseIso s d U hU).hom ≫
        pullback.fst
          (Spec.map
            (affineOpenCoefficientMap s U hU))
          (toSpec k d) =
      pullback.fst (U.ι ≫ s) (toSpec k d) ≫
        hU.isoSpec.hom
  simp [relativeSchemeAffineBaseIso, pullback.map,
    pullback.lift_fst]

/-- Relative projective space over an affine open, expressed as
absolute projective space over the open's section ring. -/
def relativeSchemeAffineProjectiveIso
    {k : Type u} [CommRing k] {S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ)
    (U : S.Opens) (hU : IsAffineOpen U) :
    letI : Algebra k Γ(S, U) :=
      (affineOpenCoefficientMap s U hU).hom.toAlgebra
    relativeScheme (U.ι ≫ s) d ≅
      scheme Γ(S, U) d := by
  letI : Algebra k Γ(S, U) :=
    (affineOpenCoefficientMap s U hU).hom.toAlgebra
  exact
    relativeSchemeAffineBaseIso s d U hU ≪≫
      (coefficientRelativeSchemeIso
        k Γ(S, U) d).symm

@[reassoc]
lemma relativeSchemeAffineProjectiveIso_hom_toSpec
    {k : Type u} [CommRing k] {S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ)
    (U : S.Opens) (hU : IsAffineOpen U) :
    letI : Algebra k Γ(S, U) :=
      (affineOpenCoefficientMap s U hU).hom.toAlgebra
    (relativeSchemeAffineProjectiveIso
        s d U hU).hom ≫
        toSpec Γ(S, U) d =
      relativeToBase (U.ι ≫ s) d ≫
        hU.isoSpec.hom := by
  letI : Algebra k Γ(S, U) :=
    (affineOpenCoefficientMap s U hU).hom.toAlgebra
  dsimp only [relativeSchemeAffineProjectiveIso,
    Iso.trans_hom]
  change
    ((relativeSchemeAffineBaseIso s d U hU).hom ≫
        (coefficientRelativeSchemeIso k Γ(S, U) d).inv) ≫
      toSpec Γ(S, U) d = _
  rw [Category.assoc,
    ← coefficientRelativeSchemeIso_hom_relativeToBase
      k Γ(S, U) d]
  simp only [Iso.inv_hom_id_assoc]
  exact
    relativeSchemeAffineBaseIso_hom_relativeToBase
      s d U hU

namespace IsRelativeProjectiveFactorization

/-- Restricting a relative projective factorization to an affine open
gives an ordinary projective-space factorization over the section
ring of that open. -/
theorem isProjectiveFactorization_affineOpen
    {k : Type u} [CommRing k] {Y S : Scheme.{u}}
    {s : S ⟶ Spec (CommRingCat.of k)}
    {f : Y ⟶ S}
    (h : IsRelativeProjectiveFactorization s f)
    (U : S.Opens) (hU : IsAffineOpen U) :
    letI : Algebra k Γ(S, U) :=
      (affineOpenCoefficientMap s U hU).hom.toAlgebra
    IsProjectiveFactorization
      (morphismRestrict f U ≫ hU.isoSpec.hom) := by
  letI : Algebra k Γ(S, U) :=
    (affineOpenCoefficientMap s U hU).hom.toAlgebra
  obtain ⟨d, j, hj, hjf⟩ := h.restrict U
  let i :
      (f ⁻¹ᵁ U).toScheme ⟶
        scheme Γ(S, U) d :=
    j ≫
      (relativeSchemeAffineProjectiveIso
        s d U hU).hom
  have hi : IsClosedImmersion i := by
    dsimp only [i]
    letI : IsClosedImmersion j := hj
    infer_instance
  refine ⟨d, i, hi, ?_⟩
  dsimp only [i]
  rw [Category.assoc,
    relativeSchemeAffineProjectiveIso_hom_toSpec]
  rw [← Category.assoc, hjf]

end IsRelativeProjectiveFactorization

/-- A projective modification restricts over every affine open to a
closed immersion into projective space over that open's section
ring. -/
theorem ProjectiveModification.isProjectiveFactorization_restrict_affineOpen
    {k : Type u} [CommRing k] {X : Scheme.{u}}
    {s : X ⟶ Spec (CommRingCat.of k)}
    (P : MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveModification s)
    (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra k Γ(X, U) :=
      (affineOpenCoefficientMap s U hU).hom.toAlgebra
    IsProjectiveFactorization
      (morphismRestrict P.toOriginal U ≫
        hU.isoSpec.hom) :=
  P.relativeProjective.isProjectiveFactorization_affineOpen
    U hU

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

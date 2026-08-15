/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.BaseRingOpenSectionTransport
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentSectionsOverBase

/-!
# Coefficient scalars in the projective Laurent chart

Mathlib identifies a projective basic open with the spectrum of the
degree-zero homogeneous localization.  This file proves that the induced
ring equivalence respects the coefficient-ring action used by
`BaseRing.moduleSheaf`.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace


noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing
open MazurTorsion.AlgebraicGeometry.CoherentCohomology
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

variable (k : Type) [CommRing k] (d : ℕ)

local instance projectiveSpaceOverCoefficientRing :
    (scheme k d).Over (Spec (CommRingCat.of k)) :=
  ⟨toSpec k d⟩

/-- Pulling a coefficient section from an open in projective space to
the corresponding open subscheme agrees with the structural coefficient
section there. -/
lemma openSubscheme_topIso_inv_algebraMapOnOpen
    (U : (scheme k d).Opens) (r : k) :
    letI : U.toScheme.Over (Spec (CommRingCat.of k)) :=
      ⟨U.ι ≫ toSpec k d⟩
    U.topIso.inv.hom (algebraMapOnOpen (k := k) U r) =
      algebraMapOnOpen (k := k) (X := U.toScheme) ⊤ r := by
  letI : U.toScheme.Over (Spec (CommRingCat.of k)) :=
    ⟨U.ι ≫ toSpec k d⟩
  let f := toSpec k d
  let e₂ : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U := by simp
  have hopenApp :
      U.ι.appLE U ⊤ e₂ = U.topIso.inv := by
    rfl
  change
    U.topIso.inv.hom
        ((f.appLE ⊤ U le_top).hom
          ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom r)) =
      ((U.ι ≫ f).appLE ⊤ ⊤ le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom r)
  rw [← hopenApp]
  have hcomp :=
    Scheme.Hom.appLE_comp_appLE U.ι f
      (⊤ : (Spec (CommRingCat.of k)).Opens) U
      (⊤ : U.toScheme.Opens) le_top e₂
  exact congrArg
    (fun q =>
      q.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom r))
    hcomp

/-- Pulling a coefficient section from a standard intersection to its open
subscheme agrees with the structural coefficient section there. -/
lemma standardIntersection_topIso_inv_algebraMapOnOpen
    (I : Finset (Fin (d + 1))) [Nonempty ↥I] (r : k) :
    let U := standardIntersection k (fun i : ↥I => i.1)
    letI : U.toScheme.Over (Spec (CommRingCat.of k)) :=
      ⟨U.ι ≫ toSpec k d⟩
    U.topIso.inv.hom (algebraMapOnOpen (k := k) U r) =
      algebraMapOnOpen (k := k) (X := U.toScheme) ⊤ r := by
  dsimp only
  let U := standardIntersection k (fun i : ↥I => i.1)
  letI : U.toScheme.Over (Spec (CommRingCat.of k)) :=
    ⟨U.ι ≫ toSpec k d⟩
  let f := toSpec k d
  let e₂ : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U := by simp
  have hopenApp :
      U.ι.appLE U ⊤ e₂ = U.topIso.inv := by
    rfl
  change
    U.topIso.inv.hom
        ((f.appLE ⊤ U le_top).hom
          ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom r)) =
      ((U.ι ≫ f).appLE ⊤ ⊤ le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom r)
  rw [← hopenApp]
  have hcomp :=
    Scheme.Hom.appLE_comp_appLE U.ι f
      (⊤ : (Spec (CommRingCat.of k)).Opens) U
      (⊤ : U.toScheme.Opens) le_top e₂
  exact congrArg
    (fun q =>
      q.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom r))
    hcomp

/-- The coefficient algebra structure introduced on the standard
homogeneous localization is the expected map through the degree-zero
graded piece. -/
lemma homogeneousAway_algebraMap_eq_fromZero
    (I : Finset (Fin (d + 1))) (r : k) :
    algebraMap k
        (HomogeneousLocalization.Away
          (homogeneousGrading k d)
          (variableProduct (k := k) I)) r =
      HomogeneousLocalization.fromZeroRingHom
        (homogeneousGrading k d)
        (Submonoid.powers (variableProduct (k := k) I))
        (algebraMap k (homogeneousGrading k d 0) r) := by
  apply HomogeneousLocalization.val_injective
  rw [Algebra.algebraMap_eq_smul_one]
  rw [HomogeneousLocalization.val_smul]
  rw [HomogeneousLocalization.val_one, Algebra.smul_def, mul_one]
  simp only [HomogeneousLocalization.fromZeroRingHom,
    RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    HomogeneousLocalization.val_mk]
  rw [IsScalarTower.algebraMap_apply k
    (MvPolynomial (Fin (d + 1)) k)
    (Localization.Away (variableProduct (k := k) I))]
  exact
    (Localization.mk_one_eq_algebraMap
      (M := Submonoid.powers (variableProduct (k := k) I))
      (MvPolynomial.C r)).symm

/-- On a nonempty projective basic open, the canonical section associated
to a degree-zero element is the pullback of that element along
`Proj.toSpecZero`. -/
lemma awayToSection_fromZero
    (I : Finset (Fin (d + 1))) [Nonempty ↥I]
    (z : homogeneousGrading k d 0) :
    Proj.awayToSection
        (homogeneousGrading k d)
        (variableProduct (k := k) I)
        (HomogeneousLocalization.fromZeroRingHom
          (homogeneousGrading k d)
          (Submonoid.powers (variableProduct (k := k) I)) z) =
      (Proj.toSpecZero (homogeneousGrading k d)).appLE
          ⊤
          (Proj.basicOpen (homogeneousGrading k d)
            (variableProduct (k := k) I))
          le_top
        ((Scheme.ΓSpecIso
          (CommRingCat.of (homogeneousGrading k d 0))).inv.hom z) := by
  let 𝒜 := homogeneousGrading k d
  let f := variableProduct (k := k) I
  let U := Proj.basicOpen 𝒜 f
  let hf : f ∈ 𝒜 I.card := variableProduct_mem_degreeCard I
  let hpos : 0 < I.card := by
    let j : ↥I := Classical.choice inferInstance
    exact Finset.card_pos.mpr ⟨j.1, j.2⟩
  let e₁ : U ≤ (Proj.toSpecZero 𝒜) ⁻¹ᵁ
      (⊤ : (Spec (CommRingCat.of (𝒜 0))).Opens) := by
    simp
  let e₂ : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U := by simp
  have hopen :
      U.ι ≫ Proj.toSpecZero 𝒜 =
        Proj.basicOpenToSpec 𝒜 f ≫
          Spec.map (CommRingCat.ofHom
            (HomogeneousLocalization.fromZeroRingHom 𝒜
              (Submonoid.powers f))) := by
    apply (cancel_epi (Proj.basicOpenIsoSpec 𝒜 f hf hpos).inv).mp
    rw [← Proj.basicOpenIsoSpec_hom 𝒜 f hf hpos]
    rw [← Category.assoc, Proj.basicOpenIsoSpec_inv_ι,
      Proj.awayι_toSpecZero, Iso.inv_hom_id_assoc]
  have haway :
      Proj.awayToSection 𝒜 f ≫ U.topIso.inv =
        (Scheme.ΓSpecIso
          (CommRingCat.of
            (HomogeneousLocalization.Away 𝒜 f))).inv ≫
          (Proj.basicOpenToSpec 𝒜 f).appTop := by
    apply (cancel_epi
      (Scheme.ΓSpecIso
        (CommRingCat.of
          (HomogeneousLocalization.Away 𝒜 f))).hom).mp
    rw [Iso.hom_inv_id_assoc]
    exact (Proj.basicOpenToSpec_app_top 𝒜 f).symm
  have hopenApp :
      U.ι.appLE U ⊤ e₂ = U.topIso.inv := by
    rfl
  have hrestrict :
      (Proj.toSpecZero 𝒜).appLE ⊤ U e₁ ≫ U.topIso.inv =
        (U.ι ≫ Proj.toSpecZero 𝒜).appTop := by
    rw [← hopenApp]
    exact
      (Scheme.Hom.appLE_comp_appLE U.ι
        (Proj.toSpecZero 𝒜)
        (⊤ : (Spec (CommRingCat.of (𝒜 0))).Opens) U
        (⊤ : U.toScheme.Opens) e₁ e₂).trans
        (Scheme.Hom.appLE_eq_app _)
  have hcat :
      CommRingCat.ofHom
          (HomogeneousLocalization.fromZeroRingHom 𝒜
            (Submonoid.powers f)) ≫
          (Scheme.ΓSpecIso
            (CommRingCat.of
              (HomogeneousLocalization.Away 𝒜 f))).inv ≫
          (Proj.basicOpenToSpec 𝒜 f).appTop =
        (Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv ≫
          (U.ι ≫ Proj.toSpecZero 𝒜).appTop := by
    rw [Scheme.ΓSpecIso_inv_naturality_assoc]
    rw [← Scheme.Hom.comp_appTop]
    rw [← hopen]
  apply
    ((ConcreteCategory.isIso_iff_bijective U.topIso.inv).mp
      inferInstance).1
  change
    (Proj.awayToSection 𝒜 f ≫ U.topIso.inv).hom
        ((HomogeneousLocalization.fromZeroRingHom 𝒜
          (Submonoid.powers f)) z) =
      ((Proj.toSpecZero 𝒜).appLE ⊤ U e₁ ≫ U.topIso.inv).hom
        ((Scheme.ΓSpecIso
          (CommRingCat.of (𝒜 0))).inv.hom z)
  rw [haway, hrestrict]
  simpa only [CommRingCat.comp_apply,
    ConcreteCategory.comp_apply,
    CommRingCat.hom_ofHom] using
    congrArg (fun q => q.hom z) hcat

/-- Mathlib's ring equivalence from the homogeneous localization to
sections on a projective basic open preserves coefficient scalars. -/
lemma basicOpenIsoAway_hom_algebraMap
    (I : Finset (Fin (d + 1))) [Nonempty ↥I] (r : k) :
    let f := variableProduct (k := k) I
    (Proj.basicOpenIsoAway
        (homogeneousGrading k d) f
        (variableProduct_mem_degreeCard I)
        (by
          let j : ↥I := Classical.choice inferInstance
          exact Finset.card_pos.mpr ⟨j.1, j.2⟩)).hom.hom
        (algebraMap k
          (HomogeneousLocalization.Away
            (homogeneousGrading k d) f) r) =
      algebraMapOnOpen (k := k)
        (Proj.basicOpen (homogeneousGrading k d)
          (variableProduct (k := k) I)) r := by
  dsimp only
  let U := Proj.basicOpen (homogeneousGrading k d)
    (variableProduct (k := k) I)
  let e : U ≤ (toSpec k d) ⁻¹ᵁ
      (⊤ : (Spec (CommRingCat.of k)).Opens) := by
    simp
  let eRaw : U ≤
      (Proj.toSpecZero (homogeneousGrading k d) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap k (homogeneousGrading k d 0)))) ⁻¹ᵁ
        (⊤ : (Spec (CommRingCat.of k)).Opens) := by
    simp
  change
    Proj.awayToSection
        (homogeneousGrading k d)
        (variableProduct (k := k) I)
        (algebraMap k
          (HomogeneousLocalization.Away
            (homogeneousGrading k d)
            (variableProduct (k := k) I)) r) =
      (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (toSpec k d).appLE
          ⊤
          U e).hom r)
  rw [homogeneousAway_algebraMap_eq_fromZero]
  change _ =
    (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (Proj.toSpecZero (homogeneousGrading k d) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap k (homogeneousGrading k d 0)))).appLE
        ⊤ U eRaw).hom r)
  rw [Scheme.Hom.comp_appLE]
  erw [← Scheme.ΓSpecIso_inv_naturality_assoc]
  simpa only [CommRingCat.comp_apply,
    ConcreteCategory.comp_apply,
    CommRingCat.hom_ofHom,
    Scheme.Hom.preimage_top] using
    awayToSection_fromZero k d I
      (algebraMap k (homogeneousGrading k d 0) r)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

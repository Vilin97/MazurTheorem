/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Naturality of `Proj.fromOfGlobalSections` under `Proj.map`

A morphism `X ⟶ Proj ℬ` out of a scheme is built by `Proj.fromOfGlobalSections ℬ f hf` from a
ring hom `f : B →+* Γ(X, ⊤)` whose image of the irrelevant ideal generates the unit ideal.
For a graded ring hom `g : 𝒜 →+*ᵍ ℬ` (with the irrelevant-ideal hypothesis of `Proj.map`),
composing with the contravariant `Proj.map g` precomposes the coordinate reader `f` by `g`:
`fromOfGlobalSections ℬ f hf ≫ Proj.map g hg = fromOfGlobalSections 𝒜 (f ∘ g) hf'`.

Geometrically: rescaling the homogeneous coordinates does not move a point, so a point of
`Proj ℬ` given by `f`, pushed through `Proj.map g`, is the point of `Proj 𝒜` read off by `f ∘ g`.

This is the scheme-level input for identifying `Proj`-endomorphisms of a Weierstrass model on
the section at infinity (T-W7.0b, `negModelHom_zero`).

## Main results

* `Proj.fromOfGlobalSections_map`: the naturality square above.
* `Proj.toBasicOpenOfGlobalSections_map`: the per-chart form it is glued from.
* `Proj.irrelevant_map_comp_toRingHom_eq_top`: the hypothesis transport supplying the
  irrelevant-ideal condition on `f ∘ g` from the one on `f`.

AINTLIB ModularCurves (T-W7.0b infrastructure); upstream candidate.
-/

open HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory Graded
open AlgebraicGeometry ProjectiveSpectrum Proj Limits

namespace AlgebraicGeometry.Proj

universe u

variable {A B : Type u} {σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  {X : Scheme.{u}}

/-- Hypothesis transport for `fromOfGlobalSections_map`: if `f` sends `ℬ`'s irrelevant ideal
to a generating set and the graded hom `g` covers (`ℬ₊ ≤ 𝒜₊.map g`), then `f ∘ g` sends
`𝒜`'s irrelevant ideal to a generating set. -/
lemma irrelevant_map_comp_toRingHom_eq_top {C : Type u} [CommRing C]
    (g : 𝒜 →+*ᵍ ℬ) (hg : ℬ₊ ≤ 𝒜₊.map g)
    (f : B →+* C) (hf : (HomogeneousIdeal.irrelevant ℬ).toIdeal.map f = ⊤) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (f.comp g.toRingHom) = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← hf, ← Ideal.map_map]
  refine Ideal.map_mono ?_
  have h := toIdeal_le_toIdeal_iff.mpr hg
  rwa [HomogeneousIdeal.toIdeal_map] at h

/-- The per-chart form of `fromOfGlobalSections_map`: on the basic open `D(g t)`, the point
map `toBasicOpenOfGlobalSections ℬ f` followed by `Proj.map g` agrees with
`toBasicOpenOfGlobalSections 𝒜 (f ∘ g)`. -/
lemma toBasicOpenOfGlobalSections_map
    (g : 𝒜 →+*ᵍ ℬ) (hg : ℬ₊ ≤ 𝒜₊.map g)
    (f : B →+* Γ(X, ⊤)) {t : A} {d : ℕ} (hdpos : 0 < d) (ht : t ∈ 𝒜 d) :
    toBasicOpenOfGlobalSections ℬ f (rfl : f (g t) = f (g t)) hdpos (g.map_mem ht) ≫
        (basicOpen ℬ (g t)).ι ≫ map g hg =
      toBasicOpenOfGlobalSections 𝒜 (f.comp g.toRingHom) rfl hdpos ht ≫ (basicOpen 𝒜 t).ι := by
  simp only [toBasicOpenOfGlobalSections, Category.assoc, basicOpenIsoSpec_inv_ι,
    basicOpenIsoSpec_inv_ι_assoc, RingHom.comp_apply, GradedRingHom.coe_toRingHom]
  rw [awayι_comp_map g hg hdpos t ht, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  congr 3
  refine congrArg (· ≫ awayι 𝒜 t ht hdpos) (congrArg Spec.map (congrArg CommRingCat.ofHom ?_))
  ext y
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective y
  simp only [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.map, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk',
    GradedRingHom.coe_toRingHom]

/-- **Naturality of `Proj.fromOfGlobalSections` under `Proj.map`.** For a graded ring hom
`g : 𝒜 →+*ᵍ ℬ`, composing the point map `fromOfGlobalSections ℬ f` with the (contravariant)
`Proj.map g` precomposes the coordinate reader `f` by `g`. -/
theorem fromOfGlobalSections_map
    (g : 𝒜 →+*ᵍ ℬ) (hg : ℬ₊ ≤ 𝒜₊.map g)
    (f : B →+* Γ(X, ⊤)) (hf : (HomogeneousIdeal.irrelevant ℬ).toIdeal.map f = ⊤)
    (hf' : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (f.comp g.toRingHom) = ⊤) :
    fromOfGlobalSections ℬ f hf ≫ map g hg =
      fromOfGlobalSections 𝒜 (f.comp g.toRingHom) hf' := by
  refine (openCoverOfMapIrrelevantEqTop 𝒜 (f.comp g.toRingHom) hf').hom_ext _ _ fun s ↦ ?_
  obtain ⟨i, r, hi, hr⟩ := s
  have eL : (X.basicOpen (f (g.toRingHom r))).ι ≫ fromOfGlobalSections ℬ f hf =
      toBasicOpenOfGlobalSections ℬ f rfl hi (g.map_mem hr) ≫ (basicOpen ℬ (g.toRingHom r)).ι := by
    rw [← fromOfGlobalSections_resLE ℬ f hf hi (g.map_mem hr), Scheme.Hom.resLE_comp_ι]
  have eR : (X.basicOpen ((f.comp g.toRingHom) r)).ι ≫
      fromOfGlobalSections 𝒜 (f.comp g.toRingHom) hf' =
      toBasicOpenOfGlobalSections 𝒜 (f.comp g.toRingHom) rfl hi hr ≫ (basicOpen 𝒜 r).ι := by
    rw [← fromOfGlobalSections_resLE 𝒜 (f.comp g.toRingHom) hf' hi hr, Scheme.Hom.resLE_comp_ι]
  simp only [openCoverOfMapIrrelevantEqTop, Scheme.openCoverOfIsOpenCover_f]
  change (X.basicOpen (f (g.toRingHom r))).ι ≫ fromOfGlobalSections ℬ f hf ≫ map g hg =
       (X.basicOpen ((f.comp g.toRingHom) r)).ι ≫ fromOfGlobalSections 𝒜 (f.comp g.toRingHom) hf'
  rw [reassoc_of% eL, eR]
  exact toBasicOpenOfGlobalSections_map g hg f hi hr

end AlgebraicGeometry.Proj

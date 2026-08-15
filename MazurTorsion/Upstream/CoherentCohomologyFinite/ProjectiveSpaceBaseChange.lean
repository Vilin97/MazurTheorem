/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSpaceCoefficientBaseChange

/-!
# Base change for standard projective space

The affine coefficient-extension calculation on standard charts
globalizes to the usual pullback square for projective space.
-/

open CategoryTheory Limits AlgebraicGeometry
open HomogeneousIdeal HomogeneousLocalization

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

variable {A B σ τ : Type u}
  [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ}
  [GradedRing 𝒜] [GradedRing ℬ]

/-- `Proj.map` on an affine chart, allowing the image denominator to
be identified propositionally with a preferred target denominator. -/
lemma isPullback_homogeneousAwayMapTo_projMap
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : ℬ₊ ≤ 𝒜₊.map f)
    {n : ℕ} (s : A) (t : B) (hst : f s = t)
    (hs : s ∈ 𝒜 n) (ht : t ∈ ℬ n) (hn : 0 < n) :
    IsPullback
      (Spec.map
        (CommRingCat.ofHom
          (homogeneousAwayMapTo f s t hst)))
      (Proj.awayι ℬ t ht hn)
      (Proj.awayι 𝒜 s hs hn)
      (Proj.map f hf) := by
  subst t
  simpa [homogeneousAwayMapTo, Away.map] using
    (isPullback_awayMap_projMap f hf hs hn)

@[simp]
lemma singletonProduct_mem_degreeOne
    (k : Type u) [CommRing k] {d : ℕ}
    (i : Fin (d + 1)) :
    variableProduct (k := k) {i} ∈
      homogeneousGrading k d 1 := by
  classical
  simpa using
    (variableProduct_mem_degreeCard
      (k := k) ({i} : Finset (Fin (d + 1))))

/-- The coordinate charts, kept in the syntactic
`variableProduct {i}` form used by the Laurent calculation. -/
noncomputable def singletonProductAffineOpenCover
    (k : Type u) [CommRing k] (d : ℕ) :
    (scheme k d).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan
    (homogeneousGrading k d)
    (fun i : Fin (d + 1) =>
      variableProduct (k := k) {i})
    (m := fun _ => 1)
    (singletonProduct_mem_degreeOne k)
    (fun _ => Nat.zero_lt_one)
    (by
      classical
      simpa [variableProduct] using
        (irrelevant_le_coordinateIdeal k d))

/-- The scheme carried by a singleton-product cover member. -/
def singletonProductAffineOpenCoverChartIso
    (k : Type u) [CommRing k] (d : ℕ)
    (i : Fin (d + 1)) :
    Spec
        (CommRingCat.of
          (Away
            (homogeneousGrading k d)
            (variableProduct (k := k) {i}))) ≅
      (singletonProductAffineOpenCover k d).openCover.X i :=
  Iso.refl _

/-- A singleton-product affine chart has its expected structural map
to the coefficient spectrum. -/
lemma singletonProductAffineOpenCover_toSpec
    (k : Type u) [CommRing k] (d : ℕ)
    (i : Fin (d + 1)) :
    (singletonProductAffineOpenCover k d).f i ≫
        toSpec k d =
      Spec.map
        (CommRingCat.ofHom
          (algebraMap k
            (Away
              (homogeneousGrading k d)
              (variableProduct (k := k) {i})))) := by
  change
    Proj.awayι
        (homogeneousGrading k d)
        (variableProduct (k := k) {i})
        (singletonProduct_mem_degreeOne k i)
        Nat.zero_lt_one ≫
      toSpec k d =
        Spec.map
          (CommRingCat.ofHom
            (algebraMap k
              (Away
                (homogeneousGrading k d)
                (variableProduct (k := k) {i}))))
  rw [toSpec]
  simp only [← Category.assoc, Proj.awayι_toSpecZero,
    ← Spec.map_comp]
  congr 1
  rw [← CommRingCat.ofHom_comp]
  congr 1
  apply RingHom.ext
  intro r
  change
    (HomogeneousLocalization.fromZeroRingHom
      (homogeneousGrading k d)
      (Submonoid.powers
        (variableProduct (k := k) {i})))
        ((algebraMap k
          (homogeneousGrading k d 0)) r) =
      algebraMap k
        (Away
          (homogeneousGrading k d)
          (variableProduct (k := k) {i})) r
  rw [homogeneousAway_algebraMap_eq_mk
    (variableProduct (k := k) {i})
    (singletonProduct_mem_degreeOne k i) r]
  rfl

/-- The coefficient-extension square on a singleton-product
projective chart. -/
lemma isPullback_coefficientSingletonProductAway
    (k R : Type u) [CommRing k] [CommRing R]
    [Algebra k R] {d : ℕ} (i : Fin (d + 1)) :
    IsPullback
      (Spec.map
        (CommRingCat.ofHom
          (algebraMap R
            (Away
              (homogeneousGrading R d)
              (variableProduct (k := R) {i})))))
      (Spec.map
        (CommRingCat.ofHom
          (coefficientVariableProductAwayMap
            (algebraMap k R) {i})))
      (Spec.map
        (CommRingCat.ofHom (algebraMap k R)))
      (Spec.map
        (CommRingCat.ofHom
          (algebraMap k
            (Away
              (homogeneousGrading k d)
              (variableProduct (k := k) {i}))))) :=
  isPullback_coefficientVariableProductAway
    k R ({i} : Finset (Fin (d + 1)))

/-- The singleton-product chart is the inverse image of the
corresponding chart under coefficient extension. -/
lemma isPullback_coefficientSingletonProductAway_projMap
    (k R : Type u) [CommRing k] [CommRing R]
    [Algebra k R] (d : ℕ) (i : Fin (d + 1)) :
    IsPullback
      (Spec.map
        (CommRingCat.ofHom
          (coefficientVariableProductAwayMap
            (algebraMap k R) {i})))
      ((singletonProductAffineOpenCover R d).f i)
      ((singletonProductAffineOpenCover k d).f i)
      (coefficientMap (algebraMap k R) d) := by
  simpa [singletonProductAffineOpenCover, coefficientMap,
    Proj.affineOpenCoverOfIrrelevantLESpan,
    coefficientVariableProductAwayMap] using
    (isPullback_homogeneousAwayMapTo_projMap
      (coefficientGradedHom (algebraMap k R) d)
      (coefficientIrrelevantLE (algebraMap k R) d)
      (variableProduct (k := k) {i})
      (variableProduct (k := R) {i})
      (coefficientGradedHom_variableProduct
        (algebraMap k R) {i})
      (singletonProduct_mem_degreeOne k i)
      (singletonProduct_mem_degreeOne R i)
      Nat.zero_lt_one)

/-- Standard projective space commutes with extension of its
coefficient ring. -/
theorem isPullback_coefficientMap
    (k R : Type u) [CommRing k] [CommRing R]
    [Algebra k R] (d : ℕ) :
    IsPullback
      (coefficientMap (algebraMap k R) d)
      (toSpec R d)
      (toSpec k d)
      (Spec.map
        (CommRingCat.ofHom (algebraMap k R))) := by
  refine Scheme.isPullback_of_openCover
    (coefficientMap (algebraMap k R) d)
    (toSpec R d)
    (toSpec k d)
    (Spec.map (CommRingCat.ofHom (algebraMap k R)))
    (singletonProductAffineOpenCover k d).openCover
    (fun i => ?_)
  change Fin (d + 1) at i
  change
    IsPullback
      (pullback.snd
        (coefficientMap (algebraMap k R) d)
        ((singletonProductAffineOpenCover k d).f i))
      (pullback.fst
          (coefficientMap (algebraMap k R) d)
          ((singletonProductAffineOpenCover k d).f i) ≫
        toSpec R d)
      ((singletonProductAffineOpenCover k d).f i ≫
        toSpec k d)
      (Spec.map
        (CommRingCat.ofHom (algebraMap k R)))
  let hChart :=
    isPullback_coefficientSingletonProductAway_projMap
      k R d i
  let e := hChart.flip.isoPullback
  refine
    (isPullback_coefficientSingletonProductAway
      k R i).flip.of_iso
      e (singletonProductAffineOpenCoverChartIso k d i)
      (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_
  · dsimp only [e]
    exact (Category.comp_id _).trans
      hChart.flip.isoPullback_hom_snd.symm
  · dsimp only [e]
    exact
      (singletonProductAffineOpenCover_toSpec R d i).symm.trans
        (CategoryTheory.eq_whisker
          hChart.flip.isoPullback_hom_fst
          (toSpec R d)).symm
  · simp only [singletonProductAffineOpenCoverChartIso,
      Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact
      (singletonProductAffineOpenCover_toSpec
        k d i).symm
  · simp

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

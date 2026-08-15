/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SegreProductChartTransitionAlgebra
import MazurTorsion.Upstream.CoherentCohomologyFinite.SegreChartwiseComparison


/-!
# Geometry of product-chart transitions

The algebraic transition homomorphism gives a morphism from the
localization model of a pairwise overlap to the second product chart.
Its two projective-space components agree with those of the canonical
map to the first chart.  Hence both chart presentations give the same
map to the binary product of projective spaces.
-/

open CategoryTheory Limits AlgebraicGeometry HomogeneousLocalization

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

lemma homogeneousAwayMap_coefficient
    {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
    {𝒜 : ℕ → Submodule k A} [GradedRing 𝒜]
    {d e : ℕ} {f g x : A}
    [Algebra k (Away 𝒜 f)] [Algebra k (Away 𝒜 x)]
    (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e)
    (hx : x = f * g)
    (hsource : ∀ r : k,
      algebraMap k (Away 𝒜 f) r =
        Away.mk 𝒜 hf 0 (algebraMap k A r)
          (by simpa using
            SetLike.algebraMap_mem_graded 𝒜 r))
    (htarget : ∀ r : k,
      algebraMap k (Away 𝒜 x) r =
        Away.mk 𝒜 (hx ▸ SetLike.mul_mem_graded hf hg) 0
          (algebraMap k A r)
          (by simpa using
            SetLike.algebraMap_mem_graded 𝒜 r))
    (r : k) :
    awayMap 𝒜 hg hx
        (algebraMap k (Away 𝒜 f) r) =
      algebraMap k (Away 𝒜 x) r := by
  rw [hsource]
  rw [HomogeneousLocalization.awayMap_mk]
  rw [htarget]
  apply HomogeneousLocalization.val_injective
  simp

lemma projectiveChartOverlap_ratio_transition
    (k : Type u) [CommRing k] (d : ℕ)
    (i a c : Fin (d + 1)) :
    projectiveSecondChartToOverlapAway k d i a
          (projectiveCoordinateRatio k d a c) *
        projectiveFirstChartToOverlapAway k d i a
          (projectiveCoordinateRatio k d i a) =
      projectiveFirstChartToOverlapAway k d i a
        (projectiveCoordinateRatio k d i c) := by
  apply HomogeneousLocalization.val_injective
  simp only [projectiveSecondChartToOverlapAway,
    projectiveFirstChartToOverlapAway,
    projectiveCoordinateRatio,
    HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.val_mul,
    HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff,
    Localization.r_eq_r']
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Submonoid.coe_mul,
    Subtype.coe_mk, one_mul, pow_one]
  ring

/-- The first Segre-image chart maps to the common double homogeneous
localization. -/
def segreImageFirstChartToOverlapAway
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    SegreImageChartRing k m n i j →+*
      SegreImageChartOverlapRing k m n i a j b :=
  awayMap
    (segreImageGrading k m n)
    (segreImageCoordinate_mem_degreeOne k m n
      (segrePairIndex m n a b))
    rfl

/-- The second Segre-image chart maps to the same double homogeneous
localization, with the denominator factors commuted. -/
def segreImageSecondChartToOverlapAway
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    SegreImageChartRing k m n a b →+*
      SegreImageChartOverlapRing k m n i a j b :=
  awayMap
    (segreImageGrading k m n)
    (segreImageCoordinate_mem_degreeOne k m n
      (segrePairIndex m n i j))
    (mul_comm
      (segreImageCoordinate k m n (segrePairIndex m n i j))
      (segreImageCoordinate k m n (segrePairIndex m n a b)))

lemma segreImageChartOverlap_leftRatio_transition
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a c : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreImageSecondChartToOverlapAway k m n i a j b
          (segreImageChartRatio k m n a c b b) *
        segreImageFirstChartToOverlapAway k m n i a j b
          (segreImageChartRatio k m n i a j j) =
      segreImageFirstChartToOverlapAway k m n i a j b
        (segreImageChartRatio k m n i c j j) := by
  apply HomogeneousLocalization.val_injective
  simp only [segreImageSecondChartToOverlapAway,
    segreImageFirstChartToOverlapAway,
    segreImageChartRatio,
    HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.val_mul,
    HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff,
    Localization.r_eq_r']
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Submonoid.coe_mul,
    one_mul, pow_one]
  rw [← segreImageCoordinate_cross_relation
    k m n i c j b]
  have hanchor :=
    segreImageCoordinate_cross_relation
      k m n i a j b
  calc
    _ =
        segreImageCoordinate k m n (segrePairIndex m n i j) *
          segreImageCoordinate k m n (segrePairIndex m n a b) *
          (segreImageCoordinate k m n (segrePairIndex m n c j) *
            (segreImageCoordinate k m n (segrePairIndex m n a j) *
              segreImageCoordinate k m n (segrePairIndex m n i b)) *
            segreImageCoordinate k m n (segrePairIndex m n a b)) := by
      ring
    _ = _ := by
      rw [hanchor]
      ring

lemma segreImageChartOverlap_rightRatio_transition
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b c : Fin (n + 1)) :
    segreImageSecondChartToOverlapAway k m n i a j b
          (segreImageChartRatio k m n a a b c) *
        segreImageFirstChartToOverlapAway k m n i a j b
          (segreImageChartRatio k m n i i j b) =
      segreImageFirstChartToOverlapAway k m n i a j b
        (segreImageChartRatio k m n i i j c) := by
  apply HomogeneousLocalization.val_injective
  simp only [segreImageSecondChartToOverlapAway,
    segreImageFirstChartToOverlapAway,
    segreImageChartRatio,
    HomogeneousLocalization.awayMap_mk,
    HomogeneousLocalization.val_mul,
    HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff,
    Localization.r_eq_r']
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Submonoid.coe_mul,
    one_mul, pow_one]
  rw [← segreImageCoordinate_cross_relation
    k m n i a j c]
  have hanchor :=
    segreImageCoordinate_cross_relation
      k m n i a j b
  calc
    _ =
        segreImageCoordinate k m n (segrePairIndex m n i j) *
          segreImageCoordinate k m n (segrePairIndex m n a b) *
          (segreImageCoordinate k m n (segrePairIndex m n i c) *
            (segreImageCoordinate k m n (segrePairIndex m n a j) *
              segreImageCoordinate k m n (segrePairIndex m n i b)) *
            segreImageCoordinate k m n (segrePairIndex m n a b)) := by
      ring
    _ = _ := by
      rw [hanchor]
      ring

/-- The localized Segre chart equivalence extends its first-chart
coordinate-ring equivalence. -/
lemma segreStandardChartOverlapRingEquiv_firstAwayMap
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1))
    (x : SegreImageChartRing k m n i j) :
    segreStandardChartOverlapRingEquiv k m n i a j b
        (segreImageFirstChartToOverlapAway
          k m n i a j b x) =
      algebraMap
        (SegreProductChartRing k m n i j)
        (SegreProductChartOverlapRing k m n i a j b)
        (segreChartForwardAlgHom k m n i j x) := by
  letI :=
    (HomogeneousLocalization.awayMap
      (segreImageGrading k m n)
      (segreImageCoordinate_mem_degreeOne k m n
        (segrePairIndex m n a b))
      (rfl :
        segreImageCoordinate k m n (segrePairIndex m n i j) *
            segreImageCoordinate k m n (segrePairIndex m n a b) =
          segreImageCoordinate k m n (segrePairIndex m n i j) *
            segreImageCoordinate k m n (segrePairIndex m n a b))).toAlgebra
  letI :
      IsLocalization.Away
        (segreImageChartRatio k m n i a j b)
        (SegreImageChartOverlapRing k m n i a j b) := by
    rw [segreImageChartRatio_eq_isLocalizationElem]
    exact
      Away.isLocalization_mul
        (segreImageCoordinate_mem_degreeOne k m n
          (segrePairIndex m n i j))
        (segreImageCoordinate_mem_degreeOne k m n
          (segrePairIndex m n a b))
        rfl Nat.one_ne_zero
  have hmap :
      (Submonoid.powers
        (segreImageChartRatio k m n i a j b)).map
          (segreStandardChartAlgEquiv
            k m n i j).toRingEquiv.toMonoidHom =
        Submonoid.powers
          (segreProductChartTransition k m n i a j b) := by
    rw [Submonoid.map_powers]
    apply congrArg
    exact
      segreChartForwardAlgHom_transition
        k m n i a j b
  change
    IsLocalization.ringEquivOfRingEquiv
        (SegreImageChartOverlapRing k m n i a j b)
        (SegreProductChartOverlapRing k m n i a j b)
        (segreStandardChartAlgEquiv
          k m n i j).toRingEquiv
        hmap
        ((algebraMap
          (SegreImageChartRing k m n i j)
          (SegreImageChartOverlapRing k m n i a j b)) x) =
      algebraMap
        (SegreProductChartRing k m n i j)
        (SegreProductChartOverlapRing k m n i a j b)
        ((segreStandardChartAlgEquiv
          k m n i j).toRingEquiv x)
  exact
    IsLocalization.ringEquivOfRingEquiv_eq
      hmap x

lemma segreProductOverlap_leftRatio_transition
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a c : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreProductSecondLeftRingHom k m n i a j b
          (projectiveCoordinateRatio k m a c) *
        segreProductOverlapLeftRingHom k m n i a j b
          (projectiveCoordinateRatio k m i a) =
      segreProductOverlapLeftRingHom k m n i a j b
        (projectiveCoordinateRatio k m i c) := by
  change
    segreProductLeftOverlapLift k m n i a j b
          (projectiveSecondChartToOverlapAway k m i a
            (projectiveCoordinateRatio k m a c)) *
        segreProductOverlapLeftRingHom k m n i a j b
          (projectiveCoordinateRatio k m i a) =
      segreProductOverlapLeftRingHom k m n i a j b
        (projectiveCoordinateRatio k m i c)
  rw [
    ← DFunLike.congr_fun
      (segreProductLeftOverlapLift_comp_first
        k m n i a j b)
      (projectiveCoordinateRatio k m i a),
    ← DFunLike.congr_fun
      (segreProductLeftOverlapLift_comp_first
        k m n i a j b)
      (projectiveCoordinateRatio k m i c),
    RingHom.comp_apply,
    ← map_mul,
    projectiveChartOverlap_ratio_transition]
  rfl

lemma segreProductOverlap_rightRatio_transition
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b c : Fin (n + 1)) :
    segreProductSecondRightRingHom k m n i a j b
          (projectiveCoordinateRatio k n b c) *
        segreProductOverlapRightRingHom k m n i a j b
          (projectiveCoordinateRatio k n j b) =
      segreProductOverlapRightRingHom k m n i a j b
        (projectiveCoordinateRatio k n j c) := by
  change
    segreProductRightOverlapLift k m n i a j b
          (projectiveSecondChartToOverlapAway k n j b
            (projectiveCoordinateRatio k n b c)) *
        segreProductOverlapRightRingHom k m n i a j b
          (projectiveCoordinateRatio k n j b) =
      segreProductOverlapRightRingHom k m n i a j b
        (projectiveCoordinateRatio k n j c)
  rw [
    ← DFunLike.congr_fun
      (segreProductRightOverlapLift_comp_first
        k m n i a j b)
      (projectiveCoordinateRatio k n j b),
    ← DFunLike.congr_fun
      (segreProductRightOverlapLift_comp_first
        k m n i a j b)
      (projectiveCoordinateRatio k n j c),
    RingHom.comp_apply,
    ← map_mul,
    projectiveChartOverlap_ratio_transition]
  rfl

lemma segreStandardChartOverlapRingEquiv_firstLeftRatio
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a c : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreStandardChartOverlapRingEquiv k m n i a j b
        (segreImageFirstChartToOverlapAway k m n i a j b
          (segreImageChartRatio k m n i c j j)) =
      segreProductOverlapLeftRingHom k m n i a j b
        (projectiveCoordinateRatio k m i c) := by
  rw [
    segreStandardChartOverlapRingEquiv_firstAwayMap,
    ← segreLeftChartToImageAlgHom_ratio
      k m n i c j,
    segreChartForwardAlgHom_left_ratio]
  rfl

lemma segreStandardChartOverlapRingEquiv_firstRightRatio
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b c : Fin (n + 1)) :
    segreStandardChartOverlapRingEquiv k m n i a j b
        (segreImageFirstChartToOverlapAway k m n i a j b
          (segreImageChartRatio k m n i i j c)) =
      segreProductOverlapRightRingHom k m n i a j b
        (projectiveCoordinateRatio k n j c) := by
  rw [
    segreStandardChartOverlapRingEquiv_firstAwayMap,
    ← segreRightChartToImageAlgHom_ratio
      k m n i j c,
    segreChartForwardAlgHom_right_ratio]
  rfl

lemma segreStandardChartOverlapRingEquiv_secondLeftRatio
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a c : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreStandardChartOverlapRingEquiv k m n i a j b
        (segreImageSecondChartToOverlapAway k m n i a j b
          (segreImageChartRatio k m n a c b b)) =
      segreProductSecondLeftRingHom k m n i a j b
        (projectiveCoordinateRatio k m a c) := by
  apply
    (segreProductOverlapLeftRatio_isUnit
      k m n i a j b).mul_right_cancel
  calc
    _ =
        segreStandardChartOverlapRingEquiv k m n i a j b
            (segreImageSecondChartToOverlapAway
              k m n i a j b
              (segreImageChartRatio k m n a c b b)) *
          segreStandardChartOverlapRingEquiv k m n i a j b
            (segreImageFirstChartToOverlapAway
              k m n i a j b
              (segreImageChartRatio k m n i a j j)) := by
      rw [
        segreStandardChartOverlapRingEquiv_firstLeftRatio
          k m n i a a j b]
    _ =
        segreStandardChartOverlapRingEquiv k m n i a j b
          (segreImageSecondChartToOverlapAway
                k m n i a j b
                (segreImageChartRatio k m n a c b b) *
            segreImageFirstChartToOverlapAway
              k m n i a j b
              (segreImageChartRatio k m n i a j j)) := by
      rw [map_mul]
    _ =
        segreStandardChartOverlapRingEquiv k m n i a j b
          (segreImageFirstChartToOverlapAway
            k m n i a j b
            (segreImageChartRatio k m n i c j j)) := by
      rw [segreImageChartOverlap_leftRatio_transition]
    _ =
        segreProductOverlapLeftRingHom k m n i a j b
          (projectiveCoordinateRatio k m i c) :=
      segreStandardChartOverlapRingEquiv_firstLeftRatio
        k m n i a c j b
    _ =
        segreProductSecondLeftRingHom k m n i a j b
              (projectiveCoordinateRatio k m a c) *
            segreProductOverlapLeftRingHom k m n i a j b
              (projectiveCoordinateRatio k m i a) :=
      (segreProductOverlap_leftRatio_transition
        k m n i a c j b).symm

lemma segreStandardChartOverlapRingEquiv_secondRightRatio
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b c : Fin (n + 1)) :
    segreStandardChartOverlapRingEquiv k m n i a j b
        (segreImageSecondChartToOverlapAway k m n i a j b
          (segreImageChartRatio k m n a a b c)) =
      segreProductSecondRightRingHom k m n i a j b
        (projectiveCoordinateRatio k n b c) := by
  apply
    (segreProductOverlapRightRatio_isUnit
      k m n i a j b).mul_right_cancel
  calc
    _ =
        segreStandardChartOverlapRingEquiv k m n i a j b
            (segreImageSecondChartToOverlapAway
              k m n i a j b
              (segreImageChartRatio k m n a a b c)) *
          segreStandardChartOverlapRingEquiv k m n i a j b
            (segreImageFirstChartToOverlapAway
              k m n i a j b
              (segreImageChartRatio k m n i i j b)) := by
      rw [
        segreStandardChartOverlapRingEquiv_firstRightRatio
          k m n i a j b b]
    _ =
        segreStandardChartOverlapRingEquiv k m n i a j b
          (segreImageSecondChartToOverlapAway
                k m n i a j b
                (segreImageChartRatio k m n a a b c) *
            segreImageFirstChartToOverlapAway
              k m n i a j b
              (segreImageChartRatio k m n i i j b)) := by
      rw [map_mul]
    _ =
        segreStandardChartOverlapRingEquiv k m n i a j b
          (segreImageFirstChartToOverlapAway
            k m n i a j b
            (segreImageChartRatio k m n i i j c)) := by
      rw [segreImageChartOverlap_rightRatio_transition]
    _ =
        segreProductOverlapRightRingHom k m n i a j b
          (projectiveCoordinateRatio k n j c) :=
      segreStandardChartOverlapRingEquiv_firstRightRatio
        k m n i a j b c
    _ =
        segreProductSecondRightRingHom k m n i a j b
              (projectiveCoordinateRatio k n b c) *
            segreProductOverlapRightRingHom k m n i a j b
              (projectiveCoordinateRatio k n j b) :=
      (segreProductOverlap_rightRatio_transition
        k m n i a j b c).symm

lemma segreImageAway_algebraMap_eq_fromZero
    (k : Type u) [CommRing k] (m n : ℕ)
    {d : ℕ} (f : SegreCoordinateRing k m n)
    (hf : f ∈ segreImageGrading k m n d)
    (r : k) :
    algebraMap k
        (Away (segreImageGrading k m n) f) r =
      HomogeneousLocalization.fromZeroRingHom
        (segreImageGrading k m n)
        (Submonoid.powers f)
        (algebraMap k (segreImageGrading k m n 0) r) := by
  rw [homogeneousAway_algebraMap_eq_mk f hf r]
  apply HomogeneousLocalization.val_injective
  change
    Localization.mk
        (algebraMap k (SegreCoordinateRing k m n) r) 1 =
      Localization.mk
        ((algebraMap k (segreImageGrading k m n 0) r :
          segreImageGrading k m n 0) : SegreCoordinateRing k m n) 1
  congr 1

lemma segreImageFirstChartToOverlapAway_algebraMap
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1))
    (r : k) :
    segreImageFirstChartToOverlapAway k m n i a j b
        (algebraMap k (SegreImageChartRing k m n i j) r) =
      algebraMap k
        (SegreImageChartOverlapRing k m n i a j b) r := by
  rw [segreImageAway_algebraMap_eq_fromZero
    k m n
    (segreImageCoordinate k m n (segrePairIndex m n i j))
    (segreImageCoordinate_mem_degreeOne k m n
      (segrePairIndex m n i j)) r]
  rw [segreImageAway_algebraMap_eq_fromZero
    k m n
    (segreImageCoordinate k m n (segrePairIndex m n i j) *
      segreImageCoordinate k m n (segrePairIndex m n a b))
    (SetLike.mul_mem_graded
      (segreImageCoordinate_mem_degreeOne k m n
        (segrePairIndex m n i j))
      (segreImageCoordinate_mem_degreeOne k m n
        (segrePairIndex m n a b))) r]
  exact
    HomogeneousLocalization.awayMap_fromZeroRingHom
      (segreImageGrading k m n)
      (segreImageCoordinate_mem_degreeOne k m n
        (segrePairIndex m n a b))
      rfl
      (algebraMap k (segreImageGrading k m n 0) r)

lemma segreImageSecondChartToOverlapAway_algebraMap
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1))
    (r : k) :
    segreImageSecondChartToOverlapAway k m n i a j b
        (algebraMap k (SegreImageChartRing k m n a b) r) =
      algebraMap k
        (SegreImageChartOverlapRing k m n i a j b) r := by
  rw [segreImageAway_algebraMap_eq_fromZero
    k m n
    (segreImageCoordinate k m n (segrePairIndex m n a b))
    (segreImageCoordinate_mem_degreeOne k m n
      (segrePairIndex m n a b)) r]
  rw [segreImageAway_algebraMap_eq_fromZero
    k m n
    (segreImageCoordinate k m n (segrePairIndex m n i j) *
      segreImageCoordinate k m n (segrePairIndex m n a b))
    (SetLike.mul_mem_graded
      (segreImageCoordinate_mem_degreeOne k m n
        (segrePairIndex m n i j))
      (segreImageCoordinate_mem_degreeOne k m n
        (segrePairIndex m n a b))) r]
  exact
    HomogeneousLocalization.awayMap_fromZeroRingHom
      (segreImageGrading k m n)
      (segreImageCoordinate_mem_degreeOne k m n
        (segrePairIndex m n i j))
      (mul_comm
        (segreImageCoordinate k m n (segrePairIndex m n i j))
        (segreImageCoordinate k m n (segrePairIndex m n a b)))
      (algebraMap k (segreImageGrading k m n 0) r)

lemma segreStandardChartOverlapRingEquiv_algebraMap
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1))
    (r : k) :
    segreStandardChartOverlapRingEquiv k m n i a j b
        (algebraMap k
          (SegreImageChartOverlapRing k m n i a j b) r) =
      algebraMap k
        (SegreProductChartOverlapRing k m n i a j b) r := by
  rw [← segreImageFirstChartToOverlapAway_algebraMap
    k m n i a j b r]
  rw [segreStandardChartOverlapRingEquiv_firstAwayMap]
  rw [(segreChartForwardAlgHom k m n i j).commutes]
  change
    algebraMap
        (SegreProductChartRing k m n i j)
        (SegreProductChartOverlapRing k m n i a j b)
        (algebraMap k
          (SegreProductChartRing k m n i j) r) =
      algebraMap k
        (SegreProductChartOverlapRing k m n i a j b) r
  exact
    (IsScalarTower.algebraMap_apply
      k
      (SegreProductChartRing k m n i j)
      (SegreProductChartOverlapRing k m n i a j b)
      r).symm

/-- The overlap equivalence as an equivalence of coefficient
algebras. -/
def segreStandardChartOverlapAlgEquiv
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    SegreImageChartOverlapRing k m n i a j b ≃ₐ[k]
      SegreProductChartOverlapRing k m n i a j b :=
  { segreStandardChartOverlapRingEquiv k m n i a j b with
    commutes' :=
      segreStandardChartOverlapRingEquiv_algebraMap
        k m n i a j b }

/-- The second Segre-image chart, mapped to the product overlap ring. -/
def segreStandardSecondChartOverlapAlgHom
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    SegreImageChartRing k m n a b →ₐ[k]
      SegreProductChartOverlapRing k m n i a j b where
  __ :=
    (segreStandardChartOverlapRingEquiv
      k m n i a j b).toRingHom.comp
      (segreImageSecondChartToOverlapAway
        k m n i a j b)
  commutes' r := by
    change
      segreStandardChartOverlapRingEquiv k m n i a j b
          (segreImageSecondChartToOverlapAway k m n i a j b
            (algebraMap k
              (SegreImageChartRing k m n a b) r)) =
        algebraMap k
          (SegreProductChartOverlapRing k m n i a j b) r
    rw [segreImageSecondChartToOverlapAway_algebraMap,
      segreStandardChartOverlapRingEquiv_algebraMap]

lemma segreStandardSecondChartOverlapAlgHom_comp_left
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreStandardSecondChartOverlapAlgHom
        k m n i a j b).comp
        (segreLeftChartToImageAlgHom
          k m n a b) =
      segreProductSecondLeftAlgHom
        k m n i a j b := by
  apply
    (AlgHom.cancel_right
      (projectiveCoordinateDehomogenization_surjective
        k m a)).mp
  ext c
  simp only [AlgHom.comp_apply,
    projectiveCoordinateDehomogenization_X]
  change
    segreStandardChartOverlapRingEquiv k m n i a j b
        (segreImageSecondChartToOverlapAway k m n i a j b
          (segreLeftChartToImageAlgHom k m n a b
            (projectiveCoordinateRatio k m a c))) =
      segreProductSecondLeftRingHom k m n i a j b
        (projectiveCoordinateRatio k m a c)
  rw [segreLeftChartToImageAlgHom_ratio,
    segreStandardChartOverlapRingEquiv_secondLeftRatio]

lemma segreStandardSecondChartOverlapAlgHom_comp_right
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreStandardSecondChartOverlapAlgHom
        k m n i a j b).comp
        (segreRightChartToImageAlgHom
          k m n a b) =
      segreProductSecondRightAlgHom
        k m n i a j b := by
  apply
    (AlgHom.cancel_right
      (projectiveCoordinateDehomogenization_surjective
        k n b)).mp
  ext c
  simp only [AlgHom.comp_apply,
    projectiveCoordinateDehomogenization_X]
  change
    segreStandardChartOverlapRingEquiv k m n i a j b
        (segreImageSecondChartToOverlapAway k m n i a j b
          (segreRightChartToImageAlgHom k m n a b
            (projectiveCoordinateRatio k n b c))) =
      segreProductSecondRightRingHom k m n i a j b
        (projectiveCoordinateRatio k n b c)
  rw [segreRightChartToImageAlgHom_ratio,
    segreStandardChartOverlapRingEquiv_secondRightRatio]

lemma segreStandardSecondChartOverlapAlgHom_comp_inverse
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreStandardSecondChartOverlapAlgHom
        k m n i a j b).comp
        (segreChartInverseAlgHom k m n a b) =
      segreProductSecondChartAlgHom
        k m n i a j b := by
  apply Algebra.TensorProduct.ext
  · ext x
    change
      segreStandardSecondChartOverlapAlgHom k m n i a j b
          (segreChartInverseAlgHom k m n a b
            ((Algebra.TensorProduct.includeLeft :
              ProjectiveCoordinateAway k m a →ₐ[k]
                SegreProductChartRing k m n a b) x)) =
        segreProductSecondChartAlgHom k m n i a j b
          ((Algebra.TensorProduct.includeLeft :
            ProjectiveCoordinateAway k m a →ₐ[k]
              SegreProductChartRing k m n a b) x)
    rw [show
      segreChartInverseAlgHom k m n a b
          ((Algebra.TensorProduct.includeLeft :
            ProjectiveCoordinateAway k m a →ₐ[k]
              SegreProductChartRing k m n a b) x) =
        segreLeftChartToImageAlgHom k m n a b x by
      simp [segreChartInverseAlgHom]]
    rw [show
      segreProductSecondChartAlgHom k m n i a j b
          ((Algebra.TensorProduct.includeLeft :
            ProjectiveCoordinateAway k m a →ₐ[k]
              SegreProductChartRing k m n a b) x) =
        segreProductSecondLeftAlgHom k m n i a j b x by
      exact
        DFunLike.congr_fun
          (segreProductSecondChartAlgHom_comp_left
            k m n i a j b) x]
    exact
      DFunLike.congr_fun
        (segreStandardSecondChartOverlapAlgHom_comp_left
          k m n i a j b) x
  · ext y
    change
      segreStandardSecondChartOverlapAlgHom k m n i a j b
          (segreChartInverseAlgHom k m n a b
            ((Algebra.TensorProduct.includeRight :
              ProjectiveCoordinateAway k n b →ₐ[k]
                SegreProductChartRing k m n a b) y)) =
        segreProductSecondChartAlgHom k m n i a j b
          ((Algebra.TensorProduct.includeRight :
            ProjectiveCoordinateAway k n b →ₐ[k]
              SegreProductChartRing k m n a b) y)
    rw [show
      segreChartInverseAlgHom k m n a b
          ((Algebra.TensorProduct.includeRight :
            ProjectiveCoordinateAway k n b →ₐ[k]
              SegreProductChartRing k m n a b) y) =
        segreRightChartToImageAlgHom k m n a b y by
      simp [segreChartInverseAlgHom]]
    rw [show
      segreProductSecondChartAlgHom k m n i a j b
          ((Algebra.TensorProduct.includeRight :
            ProjectiveCoordinateAway k n b →ₐ[k]
              SegreProductChartRing k m n a b) y) =
        segreProductSecondRightAlgHom k m n i a j b y by
      exact
        DFunLike.congr_fun
          (segreProductSecondChartAlgHom_comp_right
            k m n i a j b) y]
    exact
      DFunLike.congr_fun
        (segreStandardSecondChartOverlapAlgHom_comp_right
          k m n i a j b) y

/-- The second-chart transition followed by the localized Segre
equivalence is exactly dehomogenization on the second product chart. -/
lemma segreStandardSecondChartOverlapAlgHom_eq
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreStandardSecondChartOverlapAlgHom k m n i a j b =
      (segreProductSecondChartAlgHom k m n i a j b).comp
        (segreChartForwardAlgHom k m n a b) := by
  ext x
  have hx :=
    DFunLike.congr_fun
      (segreChartInverseAlgHom_comp_forward
        k m n a b) x
  have hx' :
      segreChartInverseAlgHom k m n a b
          (segreChartForwardAlgHom k m n a b x) =
        x := by
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using hx
  calc
    _ =
        segreStandardSecondChartOverlapAlgHom k m n i a j b
          (segreChartInverseAlgHom k m n a b
            (segreChartForwardAlgHom k m n a b x)) := by
      exact
        congrArg
          (segreStandardSecondChartOverlapAlgHom
            k m n i a j b) hx'.symm
    _ =
        segreProductSecondChartAlgHom k m n i a j b
          (segreChartForwardAlgHom k m n a b x) :=
      DFunLike.congr_fun
        (segreStandardSecondChartOverlapAlgHom_comp_inverse
          k m n i a j b)
        (segreChartForwardAlgHom k m n a b x)
    _ = _ := rfl

/-- The affine-spectrum isomorphism from the product overlap ring to
the double Segre-image chart. -/
def segreProductOverlapIsoImageDoubleChart
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    Spec
        (CommRingCat.of
          (SegreProductChartOverlapRing k m n i a j b)) ≅
      Spec
        (CommRingCat.of
          (SegreImageChartOverlapRing k m n i a j b)) :=
  Scheme.Spec.mapIso
    (segreStandardChartOverlapRingEquiv
      k m n i a j b).toCommRingCatIso.op

/-- The double Segre-image chart maps to its first standard chart. -/
def segreImageOverlapToFirstChart
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    Spec
        (CommRingCat.of
          (SegreImageChartOverlapRing k m n i a j b)) ⟶
      Spec
        (CommRingCat.of
          (SegreImageChartRing k m n i j)) :=
  Spec.map
    (CommRingCat.ofHom
      (segreImageFirstChartToOverlapAway
        k m n i a j b))

/-- The double Segre-image chart maps to its second standard chart. -/
def segreImageOverlapToSecondChart
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    Spec
        (CommRingCat.of
          (SegreImageChartOverlapRing k m n i a j b)) ⟶
      Spec
        (CommRingCat.of
          (SegreImageChartRing k m n a b)) :=
  Spec.map
    (CommRingCat.ofHom
      (segreImageSecondChartToOverlapAway
        k m n i a j b))

/-- The double Segre-image chart maps canonically into its `Proj`. -/
def segreImageOverlapToProj
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    Spec
        (CommRingCat.of
          (SegreImageChartOverlapRing k m n i a j b)) ⟶
      Proj (segreImageGrading k m n) :=
  Proj.awayι
    (segreImageGrading k m n)
    (segreImageCoordinate k m n (segrePairIndex m n i j) *
      segreImageCoordinate k m n (segrePairIndex m n a b))
    (SetLike.mul_mem_graded
      (segreImageCoordinate_mem_degreeOne k m n
        (segrePairIndex m n i j))
      (segreImageCoordinate_mem_degreeOne k m n
        (segrePairIndex m n a b)))
    (by omega)

@[reassoc]
lemma segreProductOverlapIsoImageDoubleChart_hom_first
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreProductOverlapIsoImageDoubleChart
        k m n i a j b).hom ≫
        segreImageOverlapToFirstChart k m n i a j b =
      segreProductChartLocalizationMap k m n i a j b ≫
        Spec.map
          (CommRingCat.ofHom
            (segreChartForwardAlgHom
              k m n i j).toRingHom) := by
  simp only [segreProductOverlapIsoImageDoubleChart,
    segreImageOverlapToFirstChart,
    Scheme.Spec_map, Functor.mapIso_hom, Iso.op_hom,
    Quiver.Hom.unop_op, segreProductChartLocalizationMap,
    ← Spec.map_comp]
  congr 1
  ext x
  exact
    segreStandardChartOverlapRingEquiv_firstAwayMap
      k m n i a j b x

@[reassoc]
lemma segreProductOverlapIsoImageDoubleChart_hom_second
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreProductOverlapIsoImageDoubleChart
        k m n i a j b).hom ≫
      segreImageOverlapToSecondChart k m n i a j b =
      Spec.map
          (CommRingCat.ofHom
            (segreProductSecondChartAlgHom
              k m n i a j b).toRingHom) ≫
        Spec.map
          (CommRingCat.ofHom
            (segreChartForwardAlgHom
              k m n a b).toRingHom) := by
  simp only [segreProductOverlapIsoImageDoubleChart,
    segreImageOverlapToSecondChart,
    Scheme.Spec_map, Functor.mapIso_hom, Iso.op_hom,
    Quiver.Hom.unop_op,
    ← Spec.map_comp]
  congr 1
  ext x
  exact
    DFunLike.congr_fun
      (segreStandardSecondChartOverlapAlgHom_eq
        k m n i a j b) x

@[reassoc]
lemma segreImageOverlapToFirstChart_toProj
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreImageOverlapToFirstChart k m n i a j b ≫
        Proj.awayι
          (segreImageGrading k m n)
          (segreImageCoordinate k m n
            (segrePairIndex m n i j))
          (segreImageCoordinate_mem_degreeOne k m n
            (segrePairIndex m n i j))
          Nat.zero_lt_one =
      segreImageOverlapToProj k m n i a j b := by
  exact
    Proj.SpecMap_awayMap_awayι
      (segreImageGrading k m n)
      (segreImageCoordinate_mem_degreeOne k m n
        (segrePairIndex m n i j))
      Nat.zero_lt_one
      (segreImageCoordinate_mem_degreeOne k m n
        (segrePairIndex m n a b))
      rfl

/-- The localization model of a product-chart overlap, mapped to the
affine spectrum model of the second product chart. -/
def segreProductOverlapToSecondChartSpec
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    Spec
        (CommRingCat.of
          (SegreProductChartOverlapRing k m n i a j b)) ⟶
      Spec
        (CommRingCat.of
          (SegreProductChartRing k m n a b)) :=
  Spec.map
    (CommRingCat.ofHom
      (segreProductSecondChartAlgHom
        k m n i a j b).toRingHom)

/-- The localization model of a product-chart overlap, mapped to the
second member of the standard product cover. -/
def segreProductChartOverlapToSecondChart
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    Spec
        (CommRingCat.of
          (SegreProductChartOverlapRing k m n i a j b)) ⟶
      (segreProductStandardOpenCover k m n).X (a, b) :=
  segreProductOverlapToSecondChartSpec k m n i a j b ≫
    (segreProductStandardChartIsoSpec k m n a b).inv

/-- The first product-chart presentation of the overlap induces the
canonical double-chart morphism to the Segre-image `Proj`. -/
@[reassoc]
lemma segreProductChartOverlapToChart_toProj
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreProductChartOverlapToChart k m n i a j b ≫
        segreProductStandardChartToProj k m n i j =
      (segreProductOverlapIsoImageDoubleChart
          k m n i a j b).hom ≫
        segreImageOverlapToProj k m n i a j b := by
  change
    (segreProductChartLocalizationMap k m n i a j b ≫
        (segreProductStandardChartIsoSpec k m n i j).inv) ≫
      ((segreProductStandardChartIsoSpec k m n i j).hom ≫
        Spec.map
          (CommRingCat.ofHom
            (segreChartForwardAlgHom k m n i j).toRingHom) ≫
        Proj.awayι
          (segreImageGrading k m n)
          (segreImageCoordinate k m n
            (segrePairIndex m n i j))
          (segreImageCoordinate_mem_degreeOne k m n
            (segrePairIndex m n i j))
          Nat.zero_lt_one) =
      (segreProductOverlapIsoImageDoubleChart
          k m n i a j b).hom ≫
        segreImageOverlapToProj k m n i a j b
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← segreImageOverlapToFirstChart_toProj]
  rw [segreProductOverlapIsoImageDoubleChart_hom_first_assoc]

/-- The chartwise Segre maps agree on the explicit localization model
of every pairwise overlap. -/
lemma segreProductChartToProj_overlap_compatible
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreProductChartOverlapToChart k m n i a j b ≫
        segreProductStandardChartToProj k m n i j =
      segreProductChartOverlapToSecondChart k m n i a j b ≫
        segreProductStandardChartToProj k m n a b := by
  rw [segreProductChartOverlapToChart_toProj]
  symm
  change
    (segreProductOverlapToSecondChartSpec k m n i a j b ≫
        (segreProductStandardChartIsoSpec k m n a b).inv) ≫
      ((segreProductStandardChartIsoSpec k m n a b).hom ≫
        Spec.map
          (CommRingCat.ofHom
            (segreChartForwardAlgHom k m n a b).toRingHom) ≫
        Proj.awayι
          (segreImageGrading k m n)
          (segreImageCoordinate k m n
            (segrePairIndex m n a b))
          (segreImageCoordinate_mem_degreeOne k m n
            (segrePairIndex m n a b))
          Nat.zero_lt_one) =
      (segreProductOverlapIsoImageDoubleChart
          k m n i a j b).hom ≫
        segreImageOverlapToProj k m n i a j b
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simp only [segreProductOverlapToSecondChartSpec]
  rw [←
    segreProductOverlapIsoImageDoubleChart_hom_second_assoc]
  have hsecond :
      segreImageOverlapToSecondChart k m n i a j b ≫
          Proj.awayι
            (segreImageGrading k m n)
            (segreImageCoordinate k m n
              (segrePairIndex m n a b))
            (segreImageCoordinate_mem_degreeOne k m n
              (segrePairIndex m n a b))
            Nat.zero_lt_one =
        segreImageOverlapToProj k m n i a j b := by
    change
      Spec.map
            (CommRingCat.ofHom
              (awayMap
                (segreImageGrading k m n)
                (segreImageCoordinate_mem_degreeOne k m n
                  (segrePairIndex m n i j))
                (mul_comm
                  (segreImageCoordinate k m n
                    (segrePairIndex m n i j))
                  (segreImageCoordinate k m n
                    (segrePairIndex m n a b))))) ≫
          Proj.awayι
            (segreImageGrading k m n)
            (segreImageCoordinate k m n
              (segrePairIndex m n a b))
            (segreImageCoordinate_mem_degreeOne k m n
              (segrePairIndex m n a b))
            Nat.zero_lt_one =
        Proj.awayι
          (segreImageGrading k m n)
          (segreImageCoordinate k m n
              (segrePairIndex m n i j) *
            segreImageCoordinate k m n
              (segrePairIndex m n a b))
          (SetLike.mul_mem_graded
            (segreImageCoordinate_mem_degreeOne k m n
              (segrePairIndex m n i j))
            (segreImageCoordinate_mem_degreeOne k m n
              (segrePairIndex m n a b)))
          (by omega)
    rw [Proj.awayι, Proj.awayι, Iso.eq_inv_comp,
      Proj.basicOpenIsoSpec_hom,
      Proj.basicOpenToSpec_SpecMap_awayMap_assoc,
      ← Proj.basicOpenIsoSpec_hom _ _ _ _,
      Iso.hom_inv_id_assoc, Scheme.homOfLE_ι]
    · exact
        segreImageCoordinate_mem_degreeOne k m n
          (segrePairIndex m n a b)
    · exact Nat.zero_lt_one
  exact
    congrArg
      (fun q =>
        (segreProductOverlapIsoImageDoubleChart
          k m n i a j b).hom ≫ q)
      hsecond

@[reassoc]
lemma segreProductChartOverlapToChart_fst
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreProductChartOverlapToChart k m n i a j b ≫
        (segreProductStandardOpenCover k m n).f (i, j) ≫
        pullback.fst (toSpec k m) (toSpec k n) =
      Spec.map
          (CommRingCat.ofHom
            (segreProductOverlapLeftRingHom
              k m n i a j b)) ≫
        (standardAffineCover k m).f i := by
  change
    (segreProductChartLocalizationMap k m n i a j b ≫
        (segreProductStandardChartIsoSpec k m n i j).inv) ≫
        (segreProductStandardOpenCover k m n).f (i, j) ≫
        pullback.fst (toSpec k m) (toSpec k n) =
      _
  simp only [Category.assoc,
    segreProductStandardChartIsoSpec_inv_fst]
  simp only [segreProductChartLocalizationMap]
  have hSpec :
      Spec.map
          (CommRingCat.ofHom
            (algebraMap
              (SegreProductChartRing k m n i j)
              (SegreProductChartOverlapRing k m n i a j b))) ≫
        Spec.map
          (CommRingCat.ofHom
            (Algebra.TensorProduct.includeLeftRingHom :
              ProjectiveCoordinateAway k m i →+*
                SegreProductChartRing k m n i j)) =
      Spec.map
        (CommRingCat.ofHom
          (segreProductOverlapLeftRingHom k m n i a j b)) := by
    rw [← Spec.map_comp]
    rfl
  exact CategoryTheory.eq_whisker hSpec
    ((standardAffineCover k m).f i)

@[reassoc]
lemma segreProductChartOverlapToChart_snd
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreProductChartOverlapToChart k m n i a j b ≫
        (segreProductStandardOpenCover k m n).f (i, j) ≫
        pullback.snd (toSpec k m) (toSpec k n) =
      Spec.map
          (CommRingCat.ofHom
            (segreProductOverlapRightRingHom
              k m n i a j b)) ≫
        (standardAffineCover k n).f j := by
  change
    (segreProductChartLocalizationMap k m n i a j b ≫
        (segreProductStandardChartIsoSpec k m n i j).inv) ≫
        (segreProductStandardOpenCover k m n).f (i, j) ≫
        pullback.snd (toSpec k m) (toSpec k n) =
      _
  simp only [Category.assoc,
    segreProductStandardChartIsoSpec_inv_snd]
  simp only [segreProductChartLocalizationMap]
  have hSpec :
      Spec.map
          (CommRingCat.ofHom
            (algebraMap
              (SegreProductChartRing k m n i j)
              (SegreProductChartOverlapRing k m n i a j b))) ≫
        Spec.map
          (CommRingCat.ofHom
            ((Algebra.TensorProduct.includeRight :
              ProjectiveCoordinateAway k n j →ₐ[k]
                SegreProductChartRing k m n i j).toRingHom)) =
      Spec.map
        (CommRingCat.ofHom
          (segreProductOverlapRightRingHom k m n i a j b)) := by
    rw [← Spec.map_comp]
    rfl
  exact CategoryTheory.eq_whisker hSpec
    ((standardAffineCover k n).f j)

@[reassoc]
lemma segreProductChartOverlapToSecondChart_fst
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreProductChartOverlapToSecondChart k m n i a j b ≫
        (segreProductStandardOpenCover k m n).f (a, b) ≫
        pullback.fst (toSpec k m) (toSpec k n) =
      Spec.map
          (CommRingCat.ofHom
            (segreProductSecondLeftRingHom
              k m n i a j b)) ≫
        (standardAffineCover k m).f a := by
  change
    (segreProductOverlapToSecondChartSpec k m n i a j b ≫
        (segreProductStandardChartIsoSpec k m n a b).inv) ≫
        (segreProductStandardOpenCover k m n).f (a, b) ≫
        pullback.fst (toSpec k m) (toSpec k n) =
      _
  simp only [Category.assoc,
    segreProductStandardChartIsoSpec_inv_fst]
  simp only [segreProductOverlapToSecondChartSpec]
  have hcat :
      CommRingCat.ofHom
            (Algebra.TensorProduct.includeLeftRingHom :
              ProjectiveCoordinateAway k m a →+*
                SegreProductChartRing k m n a b) ≫
          CommRingCat.ofHom
            (segreProductSecondChartAlgHom
              k m n i a j b).toRingHom =
        CommRingCat.ofHom
          (segreProductSecondLeftRingHom
            k m n i a j b) := by
    ext x
    exact
      DFunLike.congr_fun
        (segreProductSecondChartAlgHom_comp_left
          k m n i a j b) x
  have hSpec :
      Spec.map
          (CommRingCat.ofHom
            (segreProductSecondChartAlgHom
              k m n i a j b).toRingHom) ≫
        Spec.map
          (CommRingCat.ofHom
            (Algebra.TensorProduct.includeLeftRingHom :
              ProjectiveCoordinateAway k m a →+*
                SegreProductChartRing k m n a b)) =
      Spec.map
        (CommRingCat.ofHom
          (segreProductSecondLeftRingHom k m n i a j b)) := by
    rw [← Spec.map_comp, hcat]
  exact CategoryTheory.eq_whisker hSpec
    ((standardAffineCover k m).f a)

@[reassoc]
lemma segreProductChartOverlapToSecondChart_snd
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreProductChartOverlapToSecondChart k m n i a j b ≫
        (segreProductStandardOpenCover k m n).f (a, b) ≫
        pullback.snd (toSpec k m) (toSpec k n) =
      Spec.map
          (CommRingCat.ofHom
            (segreProductSecondRightRingHom
              k m n i a j b)) ≫
        (standardAffineCover k n).f b := by
  change
    (segreProductOverlapToSecondChartSpec k m n i a j b ≫
        (segreProductStandardChartIsoSpec k m n a b).inv) ≫
        (segreProductStandardOpenCover k m n).f (a, b) ≫
        pullback.snd (toSpec k m) (toSpec k n) =
      _
  simp only [Category.assoc,
    segreProductStandardChartIsoSpec_inv_snd]
  simp only [segreProductOverlapToSecondChartSpec]
  have hcat :
      CommRingCat.ofHom
            ((Algebra.TensorProduct.includeRight :
              ProjectiveCoordinateAway k n b →ₐ[k]
                SegreProductChartRing k m n a b).toRingHom) ≫
          CommRingCat.ofHom
            (segreProductSecondChartAlgHom
              k m n i a j b).toRingHom =
        CommRingCat.ofHom
          (segreProductSecondRightRingHom
            k m n i a j b) := by
    ext x
    exact
      DFunLike.congr_fun
        (segreProductSecondChartAlgHom_comp_right
          k m n i a j b) x
  have hSpec :
      Spec.map
          (CommRingCat.ofHom
            (segreProductSecondChartAlgHom
              k m n i a j b).toRingHom) ≫
        Spec.map
          (CommRingCat.ofHom
            ((Algebra.TensorProduct.includeRight :
              ProjectiveCoordinateAway k n b →ₐ[k]
                SegreProductChartRing k m n a b).toRingHom)) =
      Spec.map
        (CommRingCat.ofHom
          (segreProductSecondRightRingHom k m n i a j b)) := by
    rw [← Spec.map_comp, hcat]
  exact CategoryTheory.eq_whisker hSpec
    ((standardAffineCover k n).f b)

/-- The two affine-chart presentations of the localization model map
identically to the binary product of projective spaces. -/
lemma segreProductChartOverlap_transition
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreProductChartOverlapToChart k m n i a j b ≫
        (segreProductStandardOpenCover k m n).f (i, j) =
      segreProductChartOverlapToSecondChart k m n i a j b ≫
        (segreProductStandardOpenCover k m n).f (a, b) := by
  apply pullback.hom_ext
  · simp only [Category.assoc,
      segreProductChartOverlapToChart_fst,
      segreProductChartOverlapToSecondChart_fst]
    exact
      segreProductOverlapLeftChartTransition_toProj
        k m n i a j b
  · simp only [Category.assoc,
      segreProductChartOverlapToChart_snd,
      segreProductChartOverlapToSecondChart_snd]
    exact
      segreProductOverlapRightChartTransition_toProj
        k m n i a j b

/-- Under the explicit localization presentation of the actual
pullback overlap, its second pullback projection is the transition map
to the second product chart. -/
@[reassoc]
lemma segreProductStandardOverlapIso_hom_toSecondChart
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreProductStandardOverlapIso k m n i a j b).hom ≫
        segreProductChartOverlapToSecondChart k m n i a j b =
      pullback.snd
        ((segreProductStandardOpenCover k m n).f (i, j))
        ((segreProductStandardOpenCover k m n).f (a, b)) := by
  rw [← cancel_mono
    ((segreProductStandardOpenCover k m n).f (a, b))]
  rw [Category.assoc,
    ← segreProductChartOverlap_transition,
    ← Category.assoc,
    segreProductStandardOverlapIso_hom_toChart,
    pullback.condition]

/-- The chartwise Segre morphisms satisfy the cocycle condition on
the actual pullback overlaps of the standard product cover. -/
lemma segreProductStandardChartToProj_compatible
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    pullback.fst
          ((segreProductStandardOpenCover k m n).f (i, j))
          ((segreProductStandardOpenCover k m n).f (a, b)) ≫
        segreProductStandardChartToProj k m n i j =
      pullback.snd
          ((segreProductStandardOpenCover k m n).f (i, j))
          ((segreProductStandardOpenCover k m n).f (a, b)) ≫
        segreProductStandardChartToProj k m n a b := by
  calc
    _ =
        ((segreProductStandardOverlapIso
              k m n i a j b).hom ≫
            segreProductChartOverlapToChart
              k m n i a j b) ≫
          segreProductStandardChartToProj k m n i j := by
      rw [segreProductStandardOverlapIso_hom_toChart]
    _ =
        (segreProductStandardOverlapIso
              k m n i a j b).hom ≫
          (segreProductChartOverlapToChart
              k m n i a j b ≫
            segreProductStandardChartToProj
              k m n i j) := by
      rw [Category.assoc]
    _ =
        (segreProductStandardOverlapIso
              k m n i a j b).hom ≫
          (segreProductChartOverlapToSecondChart
              k m n i a j b ≫
            segreProductStandardChartToProj
              k m n a b) := by
      rw [segreProductChartToProj_overlap_compatible]
    _ =
        ((segreProductStandardOverlapIso
              k m n i a j b).hom ≫
            segreProductChartOverlapToSecondChart
              k m n i a j b) ≫
          segreProductStandardChartToProj k m n a b := by
      rw [Category.assoc]
    _ = _ := by
      rw [segreProductStandardOverlapIso_hom_toSecondChart]

/-- The global morphism from the binary product to the `Proj` of the
Segre-image coordinate ring, obtained by gluing its standard affine
chart presentations. -/
def segreProductToImageProj
    (k : Type u) [CommRing k] (m n : ℕ) :
    binaryProjectiveScheme k m n ⟶
      Proj (segreImageGrading k m n) :=
  (segreProductStandardOpenCover k m n).glueMorphisms
    (fun q =>
      segreProductStandardChartToProj
        k m n q.1 q.2)
    (fun q r =>
      segreProductStandardChartToProj_compatible
        k m n q.1 r.1 q.2 r.2)

/-- The glued Segre morphism restricts to the prescribed morphism on
every standard product chart. -/
@[reassoc]
lemma segreProductStandardOpenCover_f_segreProductToImageProj
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreProductStandardOpenCover k m n).f (i, j) ≫
        segreProductToImageProj k m n =
      segreProductStandardChartToProj k m n i j := by
  apply Scheme.Cover.ι_glueMorphisms

/-- The standard affine cover of the Segre image, reindexed by pairs
of projective coordinates.  This index agrees definitionally with the
standard product cover and avoids transports in the inverse gluing. -/
def segreImagePairAffineOpenCover
    (k : Type u) [CommRing k] (m n : ℕ) :
    (@AlgebraicGeometry.Proj
      (SegreCoordinateRing k m n)
      (Submodule k (SegreCoordinateRing k m n))
      inferInstance
      inferInstance
      (segreCoordinateRingSubmoduleAddSubgroupClass k m n)
      (segreImageGrading k m n)
      (segreImageGradingGradedRing k m n)).AffineOpenCover := by
  exact Proj.affineOpenCoverOfIrrelevantLESpan
    (segreImageGrading k m n)
    (fun q : Fin (m + 1) × Fin (n + 1) =>
      segreImageCoordinate k m n
        (segrePairIndex m n q.1 q.2))
    (m := fun _ => 1)
    (fun q : Fin (m + 1) × Fin (n + 1) =>
      segreImageCoordinate_mem_degreeOne k m n
        (segrePairIndex m n q.1 q.2))
    (fun _ => Nat.zero_lt_one)
    (by
      refine
        (segreImageIrrelevant_le_coordinateIdeal
          k m n).trans ?_
      rw [Ideal.span_le]
      rintro _ ⟨p, rfl⟩
      apply Ideal.subset_span
      refine ⟨segreIndexEquiv m n p, ?_⟩
      simp [segrePairIndex])

/-- The standard Segre-image chart, in its affine-spectrum
presentation.  Naming this isomorphism fixes all localization-ring
instances used by the inverse gluing. -/
def segreImagePairChartIsoSpec
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreImageStandardChart k m n
        (segrePairIndex m n i j)).toScheme ≅
      Spec
        (CommRingCat.of
          (SegreImageChartRing k m n i j)) :=
  Proj.basicOpenIsoSpec
    (segreImageGrading k m n)
    (segreImageCoordinate k m n
      (segrePairIndex m n i j))
    (segreImageCoordinate_mem_degreeOne k m n
      (segrePairIndex m n i j))
    Nat.zero_lt_one

/-- The affine-spectrum presentation followed by the chart inclusion
is the canonical homogeneous basic-open immersion. -/
@[reassoc]
lemma segreImagePairChartIsoSpec_inv_ι
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreImagePairChartIsoSpec k m n i j).inv ≫
        (segreImageStandardChart k m n
          (segrePairIndex m n i j)).ι =
      Proj.awayι
        (segreImageGrading k m n)
        (segreImageCoordinate k m n
          (segrePairIndex m n i j))
        (segreImageCoordinate_mem_degreeOne k m n
          (segrePairIndex m n i j))
        Nat.zero_lt_one := by
  rfl

/-- The inverse chart map from a pair-indexed standard affine chart
of the Segre image to the binary product. -/
def segreImagePairChartToProduct
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Spec
        (CommRingCat.of
          (SegreImageChartRing k m n i j)) ⟶
      binaryProjectiveScheme k m n :=
  (segreImagePairChartIsoSpec k m n i j).inv ≫
    (segreProductStandardChartIsoImageChart
      k m n i j).inv ≫
    (segreProductStandardOpenCover k m n).f (i, j)

/-- Each pair-indexed inverse chart map is a left inverse to the
glued Segre map, up to the corresponding target-chart inclusion. -/
@[reassoc]
lemma segreImagePairChartToProduct_segreProductToImageProj_awayι
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreImagePairChartToProduct k m n i j ≫
        segreProductToImageProj k m n =
      Proj.awayι
        (segreImageGrading k m n)
        (segreImageCoordinate k m n
          (segrePairIndex m n i j))
        (segreImageCoordinate_mem_degreeOne k m n
          (segrePairIndex m n i j))
        Nat.zero_lt_one := by
  rw [segreImagePairChartToProduct,
    Category.assoc, Category.assoc,
    segreProductStandardOpenCover_f_segreProductToImageProj,
    ← segreProductStandardChartIsoImageChart_hom_ι]
  calc
    _ =
        (segreImagePairChartIsoSpec k m n i j).inv ≫
          (segreImageStandardChart k m n
            (segrePairIndex m n i j)).ι := by
      simpa only [Category.assoc] using
        congrArg
          (fun z =>
            (segreImagePairChartIsoSpec
              k m n i j).inv ≫ z)
          (Iso.inv_hom_id_assoc
            (segreProductStandardChartIsoImageChart
              k m n i j)
            (segreImageStandardChart k m n
              (segrePairIndex m n i j)).ι)
    _ = _ :=
      segreImagePairChartIsoSpec_inv_ι
        k m n i j

/-- Each pair-indexed inverse chart map is a left inverse to the
glued Segre map, expressed using the corresponding member of the
pair-indexed target cover. -/
@[reassoc]
lemma segreImagePairChartToProduct_segreProductToImageProj
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreImagePairChartToProduct k m n i j ≫
        segreProductToImageProj k m n =
      (segreImagePairAffineOpenCover k m n).f (i, j) := by
  change
    segreImagePairChartToProduct k m n i j ≫
        segreProductToImageProj k m n =
      Proj.awayι
        (segreImageGrading k m n)
        (segreImageCoordinate k m n
          (segrePairIndex m n i j))
        (segreImageCoordinate_mem_degreeOne k m n
          (segrePairIndex m n i j))
        Nat.zero_lt_one
  exact
    segreImagePairChartToProduct_segreProductToImageProj_awayι
      k m n i j

/-- On the double-chart model, the inverse of the Segre chart
equivalence followed by the first product-chart presentation is the
first target-chart restriction followed by its inverse chart map. -/
@[reassoc]
lemma segreImageOverlapToFirstProductChart
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreProductOverlapIsoImageDoubleChart
        k m n i a j b).inv ≫
        segreProductChartOverlapToChart
          k m n i a j b =
      segreImageOverlapToFirstChart k m n i a j b ≫
        (segreImagePairChartIsoSpec k m n i j).inv ≫
        (segreProductStandardChartIsoImageChart
          k m n i j).inv := by
  rw [← cancel_mono
    (segreProductStandardChartIsoImageChart
      k m n i j).hom]
  simp only [Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  dsimp only [segreProductChartOverlapToChart,
    segreProductStandardChartIsoImageChart,
    segreImagePairChartIsoSpec]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  change
    (segreProductOverlapIsoImageDoubleChart
          k m n i a j b).inv ≫
        segreProductChartLocalizationMap k m n i a j b ≫
        Spec.map
          (CommRingCat.ofHom
            (segreChartForwardAlgHom
              k m n i j).toRingHom) ≫
        (segreImagePairChartIsoSpec
          k m n i j).inv =
      segreImageOverlapToFirstChart k m n i a j b ≫
        (segreImagePairChartIsoSpec
          k m n i j).inv
  rw [←
    segreProductOverlapIsoImageDoubleChart_hom_first_assoc]
  simp

/-- The analogous identification for the second product-chart
presentation of the same double-chart model. -/
@[reassoc]
lemma segreImageOverlapToSecondProductChart
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreProductOverlapIsoImageDoubleChart
        k m n i a j b).inv ≫
        segreProductChartOverlapToSecondChart
          k m n i a j b =
      segreImageOverlapToSecondChart k m n i a j b ≫
        (segreImagePairChartIsoSpec k m n a b).inv ≫
        (segreProductStandardChartIsoImageChart
          k m n a b).inv := by
  rw [← cancel_mono
    (segreProductStandardChartIsoImageChart
      k m n a b).hom]
  simp only [Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  dsimp only [segreProductChartOverlapToSecondChart,
    segreProductOverlapToSecondChartSpec,
    segreProductStandardChartIsoImageChart,
    segreImagePairChartIsoSpec]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  change
    (segreProductOverlapIsoImageDoubleChart
          k m n i a j b).inv ≫
        Spec.map
          (CommRingCat.ofHom
            (segreProductSecondChartAlgHom
              k m n i a j b).toRingHom) ≫
        Spec.map
          (CommRingCat.ofHom
            (segreChartForwardAlgHom
              k m n a b).toRingHom) ≫
        (segreImagePairChartIsoSpec
          k m n a b).inv =
      segreImageOverlapToSecondChart k m n i a j b ≫
        (segreImagePairChartIsoSpec
          k m n a b).inv
  rw [←
    segreProductOverlapIsoImageDoubleChart_hom_second_assoc]
  simp

/-- The canonical affine-spectrum presentation of the overlap of two
pair-indexed standard charts of the Segre image. -/
def segreImagePairOverlapIso
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    pullback
        (Proj.awayι
          (segreImageGrading k m n)
          (segreImageCoordinate k m n
            (segrePairIndex m n i j))
          (segreImageCoordinate_mem_degreeOne k m n
            (segrePairIndex m n i j))
          Nat.zero_lt_one)
        (Proj.awayι
          (segreImageGrading k m n)
          (segreImageCoordinate k m n
            (segrePairIndex m n a b))
          (segreImageCoordinate_mem_degreeOne k m n
            (segrePairIndex m n a b))
          Nat.zero_lt_one) ≅
      Spec
        (CommRingCat.of
          (SegreImageChartOverlapRing
            k m n i a j b)) :=
  Proj.pullbackAwayιIso
    (segreImageGrading k m n)
    (segreImageCoordinate_mem_degreeOne k m n
      (segrePairIndex m n i j))
    Nat.zero_lt_one
    (segreImageCoordinate_mem_degreeOne k m n
      (segrePairIndex m n a b))
    Nat.zero_lt_one
    rfl

/-- The first pullback projection of a target-chart overlap is the
canonical first-chart localization map. -/
@[reassoc]
lemma segreImagePairOverlapIso_inv_fst
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreImagePairOverlapIso k m n i a j b).inv ≫
        pullback.fst
          (Proj.awayι
            (segreImageGrading k m n)
            (segreImageCoordinate k m n
              (segrePairIndex m n i j))
            (segreImageCoordinate_mem_degreeOne k m n
              (segrePairIndex m n i j))
            Nat.zero_lt_one)
          (Proj.awayι
            (segreImageGrading k m n)
            (segreImageCoordinate k m n
              (segrePairIndex m n a b))
            (segreImageCoordinate_mem_degreeOne k m n
              (segrePairIndex m n a b))
            Nat.zero_lt_one) =
      segreImageOverlapToFirstChart k m n i a j b := by
  exact
    Proj.pullbackAwayιIso_inv_fst
      (segreImageGrading k m n)
      (segreImageCoordinate_mem_degreeOne k m n
        (segrePairIndex m n i j))
      Nat.zero_lt_one
      (segreImageCoordinate_mem_degreeOne k m n
        (segrePairIndex m n a b))
      Nat.zero_lt_one
      rfl

/-- The second pullback projection of a target-chart overlap is the
canonical second-chart localization map. -/
@[reassoc]
lemma segreImagePairOverlapIso_inv_snd
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    (segreImagePairOverlapIso k m n i a j b).inv ≫
        pullback.snd
          (Proj.awayι
            (segreImageGrading k m n)
            (segreImageCoordinate k m n
              (segrePairIndex m n i j))
            (segreImageCoordinate_mem_degreeOne k m n
              (segrePairIndex m n i j))
            Nat.zero_lt_one)
          (Proj.awayι
            (segreImageGrading k m n)
            (segreImageCoordinate k m n
              (segrePairIndex m n a b))
            (segreImageCoordinate_mem_degreeOne k m n
              (segrePairIndex m n a b))
            Nat.zero_lt_one) =
      segreImageOverlapToSecondChart k m n i a j b := by
  exact
    Proj.pullbackAwayιIso_inv_snd
      (segreImageGrading k m n)
      (segreImageCoordinate_mem_degreeOne k m n
        (segrePairIndex m n i j))
      Nat.zero_lt_one
      (segreImageCoordinate_mem_degreeOne k m n
        (segrePairIndex m n a b))
      Nat.zero_lt_one
      rfl

/-- The inverse chart maps agree on every pairwise overlap of the
explicit homogeneous basic-open charts. -/
lemma segreImagePairChartToProduct_compatible_awayι
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    pullback.fst
          (Proj.awayι
            (segreImageGrading k m n)
            (segreImageCoordinate k m n
              (segrePairIndex m n i j))
            (segreImageCoordinate_mem_degreeOne k m n
              (segrePairIndex m n i j))
            Nat.zero_lt_one)
          (Proj.awayι
            (segreImageGrading k m n)
            (segreImageCoordinate k m n
              (segrePairIndex m n a b))
            (segreImageCoordinate_mem_degreeOne k m n
              (segrePairIndex m n a b))
            Nat.zero_lt_one) ≫
        segreImagePairChartToProduct k m n i j =
      pullback.snd
          (Proj.awayι
            (segreImageGrading k m n)
            (segreImageCoordinate k m n
              (segrePairIndex m n i j))
            (segreImageCoordinate_mem_degreeOne k m n
              (segrePairIndex m n i j))
            Nat.zero_lt_one)
          (Proj.awayι
            (segreImageGrading k m n)
            (segreImageCoordinate k m n
              (segrePairIndex m n a b))
            (segreImageCoordinate_mem_degreeOne k m n
              (segrePairIndex m n a b))
            Nat.zero_lt_one) ≫
        segreImagePairChartToProduct k m n a b := by
  rw [← cancel_epi
    (segreImagePairOverlapIso
      k m n i a j b).inv]
  rw [segreImagePairOverlapIso_inv_fst_assoc,
    segreImagePairOverlapIso_inv_snd_assoc]
  simp only [segreImagePairChartToProduct,
    Category.assoc]
  rw [← segreImageOverlapToFirstProductChart_assoc,
    ← segreImageOverlapToSecondProductChart_assoc]
  exact
    congrArg
      (fun z =>
        (segreProductOverlapIsoImageDoubleChart
          k m n i a j b).inv ≫ z)
      (segreProductChartOverlap_transition
        k m n i a j b)

/-- The inverse chart maps satisfy the cocycle condition on the actual
pair-indexed affine cover of the Segre image. -/
lemma segreImagePairChartToProduct_compatible
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    pullback.fst
          ((segreImagePairAffineOpenCover
            k m n).openCover.f (i, j))
          ((segreImagePairAffineOpenCover
            k m n).openCover.f (a, b)) ≫
        segreImagePairChartToProduct k m n i j =
      pullback.snd
          ((segreImagePairAffineOpenCover
            k m n).openCover.f (i, j))
          ((segreImagePairAffineOpenCover
            k m n).openCover.f (a, b)) ≫
        segreImagePairChartToProduct k m n a b := by
  change
    pullback.fst
          (Proj.awayι
            (segreImageGrading k m n)
            (segreImageCoordinate k m n
              (segrePairIndex m n i j))
            (segreImageCoordinate_mem_degreeOne k m n
              (segrePairIndex m n i j))
            Nat.zero_lt_one)
          (Proj.awayι
            (segreImageGrading k m n)
            (segreImageCoordinate k m n
              (segrePairIndex m n a b))
            (segreImageCoordinate_mem_degreeOne k m n
              (segrePairIndex m n a b))
            Nat.zero_lt_one) ≫
        segreImagePairChartToProduct k m n i j =
      pullback.snd
          (Proj.awayι
            (segreImageGrading k m n)
            (segreImageCoordinate k m n
              (segrePairIndex m n i j))
            (segreImageCoordinate_mem_degreeOne k m n
              (segrePairIndex m n i j))
            Nat.zero_lt_one)
          (Proj.awayι
            (segreImageGrading k m n)
            (segreImageCoordinate k m n
              (segrePairIndex m n a b))
            (segreImageCoordinate_mem_degreeOne k m n
              (segrePairIndex m n a b))
            Nat.zero_lt_one) ≫
        segreImagePairChartToProduct k m n a b
  exact
    segreImagePairChartToProduct_compatible_awayι
      k m n i a j b

/-- The global inverse to the glued Segre morphism, obtained by gluing
the inverse affine-chart maps on the pair-indexed target cover. -/
def segreImageProjToProduct
    (k : Type u) [CommRing k] (m n : ℕ) :
    Proj (segreImageGrading k m n) ⟶
      binaryProjectiveScheme k m n :=
  (segreImagePairAffineOpenCover k m n).openCover.glueMorphisms
    (fun q =>
      segreImagePairChartToProduct
        k m n q.1 q.2)
    (fun q r =>
      segreImagePairChartToProduct_compatible
        k m n q.1 r.1 q.2 r.2)

/-- The glued inverse restricts to the prescribed inverse morphism on
every pair-indexed target chart. -/
@[reassoc]
lemma segreImagePairOpenCover_f_segreImageProjToProduct
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreImagePairAffineOpenCover
          k m n).openCover.f (i, j) ≫
        segreImageProjToProduct k m n =
      segreImagePairChartToProduct k m n i j := by
  apply Scheme.Cover.ι_glueMorphisms

/-- The isomorphism from a standard product chart to the corresponding
pair-indexed affine-spectrum chart of the Segre image. -/
def segreProductStandardChartIsoPairChart
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreProductStandardOpenCover
        k m n).X (i, j) ≅
      Spec
        (CommRingCat.of
          (SegreImageChartRing k m n i j)) :=
  segreProductStandardChartIsoImageChart k m n i j ≪≫
    segreImagePairChartIsoSpec k m n i j

/-- The product-to-target chart isomorphism followed by the canonical
homogeneous basic-open immersion is the prescribed local Segre
morphism. -/
@[reassoc]
lemma segreProductStandardChartIsoPairChart_hom_awayι
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreProductStandardChartIsoPairChart
          k m n i j).hom ≫
        Proj.awayι
          (segreImageGrading k m n)
          (segreImageCoordinate k m n
            (segrePairIndex m n i j))
          (segreImageCoordinate_mem_degreeOne k m n
            (segrePairIndex m n i j))
          Nat.zero_lt_one =
      segreProductStandardChartToProj k m n i j := by
  rw [← segreImagePairChartIsoSpec_inv_ι]
  simp only [segreProductStandardChartIsoPairChart,
    Iso.trans_hom, Category.assoc,
    Iso.hom_inv_id_assoc,
    segreProductStandardChartIsoImageChart_hom_ι]

/-- The same factorization, expressed through the corresponding member
of the pair-indexed target cover. -/
@[reassoc]
lemma segreProductStandardChartIsoPairChart_hom_f
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreProductStandardChartIsoPairChart
          k m n i j).hom ≫
        (segreImagePairAffineOpenCover
          k m n).openCover.f (i, j) =
      segreProductStandardChartToProj k m n i j := by
  change
    (segreProductStandardChartIsoPairChart
          k m n i j).hom ≫
        Proj.awayι
          (segreImageGrading k m n)
          (segreImageCoordinate k m n
            (segrePairIndex m n i j))
          (segreImageCoordinate_mem_degreeOne k m n
            (segrePairIndex m n i j))
          Nat.zero_lt_one =
      segreProductStandardChartToProj k m n i j
  exact
    segreProductStandardChartIsoPairChart_hom_awayι
      k m n i j

/-- The inverse local chart map is the inverse product-to-target
chart isomorphism followed by the source-cover inclusion. -/
lemma segreImagePairChartToProduct_eq
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreImagePairChartToProduct k m n i j =
      (segreProductStandardChartIsoPairChart
          k m n i j).inv ≫
        (segreProductStandardOpenCover
          k m n).f (i, j) := by
  rfl

/-- On a homogeneous target chart, the global inverse restricts to
the explicit inverse chart map. -/
@[reassoc]
lemma segreImagePairAwayι_segreImageProjToProduct
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Proj.awayι
          (segreImageGrading k m n)
          (segreImageCoordinate k m n
            (segrePairIndex m n i j))
          (segreImageCoordinate_mem_degreeOne k m n
            (segrePairIndex m n i j))
          Nat.zero_lt_one ≫
        segreImageProjToProduct k m n =
      segreImagePairChartToProduct k m n i j := by
  change
    (segreImagePairAffineOpenCover
          k m n).openCover.f (i, j) ≫
        segreImageProjToProduct k m n =
      segreImagePairChartToProduct k m n i j
  exact
    segreImagePairOpenCover_f_segreImageProjToProduct
      k m n i j

/-- The two global composites are the identity after restriction to
each pair-indexed target chart. -/
lemma segreImagePairAwayι_inverse_right
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Proj.awayι
          (segreImageGrading k m n)
          (segreImageCoordinate k m n
            (segrePairIndex m n i j))
          (segreImageCoordinate_mem_degreeOne k m n
            (segrePairIndex m n i j))
          Nat.zero_lt_one ≫
        (segreImageProjToProduct k m n ≫
          segreProductToImageProj k m n) =
      Proj.awayι
          (segreImageGrading k m n)
          (segreImageCoordinate k m n
            (segrePairIndex m n i j))
          (segreImageCoordinate_mem_degreeOne k m n
            (segrePairIndex m n i j))
          Nat.zero_lt_one ≫
        𝟙 (Proj (segreImageGrading k m n)) := by
  rw [segreImagePairAwayι_segreImageProjToProduct_assoc,
    segreImagePairChartToProduct_segreProductToImageProj_awayι,
    Category.comp_id]

/-- The other composite is the identity after restriction to each
standard product chart. -/
lemma segreProductStandardChart_inverse_left
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreProductStandardOpenCover k m n).f (i, j) ≫
        (segreProductToImageProj k m n ≫
          segreImageProjToProduct k m n) =
      (segreProductStandardOpenCover k m n).f (i, j) ≫
        𝟙 (binaryProjectiveScheme k m n) := by
  rw [segreProductStandardOpenCover_f_segreProductToImageProj_assoc,
    ← segreProductStandardChartIsoPairChart_hom_awayι_assoc,
    segreImagePairAwayι_segreImageProjToProduct,
    segreImagePairChartToProduct_eq,
    Iso.hom_inv_id_assoc,
    Category.comp_id]

/-- The glued inverse is a right inverse to the glued Segre
morphism. -/
lemma segreImageProjToProduct_segreProductToImageProj
    (k : Type u) [CommRing k] (m n : ℕ) :
    segreImageProjToProduct k m n ≫
        segreProductToImageProj k m n =
      𝟙 (Proj (segreImageGrading k m n)) := by
  apply
    (segreImagePairAffineOpenCover
      k m n).openCover.hom_ext
  intro q
  exact
    segreImagePairAwayι_inverse_right
      k m n q.1 q.2

/-- The glued inverse is also a left inverse to the glued Segre
morphism. -/
lemma segreProductToImageProj_segreImageProjToProduct
    (k : Type u) [CommRing k] (m n : ℕ) :
    segreProductToImageProj k m n ≫
        segreImageProjToProduct k m n =
      𝟙 (binaryProjectiveScheme k m n) := by
  apply
    (segreProductStandardOpenCover
      k m n).hom_ext
  intro q
  exact
    segreProductStandardChart_inverse_left
      k m n q.1 q.2

/-- The glued Segre morphism is an isomorphism, with inverse given by
the glued inverse chart maps. -/
instance isIso_segreProductToImageProj
    (k : Type u) [CommRing k] (m n : ℕ) :
    IsIso (segreProductToImageProj k m n) :=
  IsIso.mk'
    ⟨segreImageProjToProduct k m n,
      segreImageProjToProduct_segreProductToImageProj
        k m n,
      segreProductToImageProj_segreImageProjToProduct
        k m n⟩

/-- The affine chart map induced by the Segre graded coordinate map,
with its target denominator fixed explicitly. -/
def segreImageChartMapFromAmbient
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    ProjectiveCoordinateAway
        k (segreDimension m n)
        (segrePairIndex m n i j) →+*
      SegreImageChartRing k m n i j :=
  homogeneousAwayMapTo
    (segreImageGradedHom k m n)
    (coordinate k (segrePairIndex m n i j))
    (segreImageCoordinate k m n
      (segrePairIndex m n i j))
    rfl

/-- The affine map induced by the Segre graded coordinate map
preserves coefficients on every standard homogeneous localization. -/
lemma segreImageChartMapFromAmbient_algebraMap
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1))
    (r : k) :
    segreImageChartMapFromAmbient k m n i j
          (algebraMap k
            (ProjectiveCoordinateAway
              k (segreDimension m n)
              (segrePairIndex m n i j)) r) =
      algebraMap k
        (SegreImageChartRing k m n i j) r := by
  rw [homogeneousAway_algebraMap_eq_mk
    (𝒜 := homogeneousGrading k (segreDimension m n))
    (coordinate k (segrePairIndex m n i j))
    (coordinate_mem_degreeOne k
      (segrePairIndex m n i j)) r]
  have hCoordinate :
      segreImageGradedHom k m n
          (coordinate k (segrePairIndex m n i j)) =
        segreImageCoordinate k m n
          (segrePairIndex m n i j) := rfl
  have hCoefficient :
      algebraMap k
          (MvPolynomial (Fin (segreDimension m n + 1)) k) r ∈
        homogeneousGrading k (segreDimension m n) 0 := by
    simpa using
      SetLike.algebraMap_mem_graded
        (homogeneousGrading k (segreDimension m n)) r
  change
    homogeneousAwayMapTo
          (segreImageGradedHom k m n)
          (coordinate k (segrePairIndex m n i j))
          (segreImageCoordinate k m n
            (segrePairIndex m n i j))
          hCoordinate
          (Away.mk
            (homogeneousGrading k (segreDimension m n))
            (coordinate_mem_degreeOne k
              (segrePairIndex m n i j))
            0
            (algebraMap k
              (MvPolynomial
                (Fin (segreDimension m n + 1)) k) r)
            hCoefficient) =
      algebraMap k
        (SegreImageChartRing k m n i j) r
  have hMap :=
    homogeneousAwayMapTo_mk
      (segreImageGradedHom k m n)
      (coordinate k (segrePairIndex m n i j))
      (segreImageCoordinate k m n (segrePairIndex m n i j))
      hCoordinate
      (coordinate_mem_degreeOne k (segrePairIndex m n i j))
      (segreImageCoordinate_mem_degreeOne
        k m n (segrePairIndex m n i j))
      0
      (algebraMap k
        (MvPolynomial (Fin (segreDimension m n + 1)) k) r)
      hCoefficient
  refine hMap.trans ?_
  rw [homogeneousAway_algebraMap_eq_mk
    (𝒜 := segreImageGrading k m n)
    (segreImageCoordinate k m n
      (segrePairIndex m n i j))
    (segreImageCoordinate_mem_degreeOne
      k m n (segrePairIndex m n i j)) r]
  congr 1
  exact
    (segreRangeCoordinateHom k m n).commutes r

/-- The standard affine square for the Segre coordinate map,
specialized to a pair-indexed degree-one coordinate.  Keeping this
specialization separate avoids expensive elaboration of the general
`Proj.awayι_comp_map` theorem inside larger composites. -/
@[reassoc]
lemma segreImagePairAwayι_comp_map
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Proj.awayι
          (segreImageGrading k m n)
          (segreImageCoordinate k m n
            (segrePairIndex m n i j))
          (segreImageCoordinate_mem_degreeOne k m n
            (segrePairIndex m n i j))
          Nat.zero_lt_one ≫
        Proj.map
          (segreImageGradedHom k m n)
          (segreImageIrrelevantLE k m n) =
      Spec.map
          (CommRingCat.ofHom
            (segreImageChartMapFromAmbient
              k m n i j)) ≫
        Proj.awayι
          (homogeneousGrading k
            (segreDimension m n))
          (coordinate k (segrePairIndex m n i j))
          (coordinate_mem_degreeOne k
            (segrePairIndex m n i j))
          Nat.zero_lt_one := by
  convert
    @Proj.awayι_comp_map
      (MvPolynomial
        (Fin (segreDimension m n + 1)) k)
      (SegreCoordinateRing k m n)
      (Submodule k
        (MvPolynomial
          (Fin (segreDimension m n + 1)) k))
      (Submodule k
        (SegreCoordinateRing k m n))
      inferInstance
      inferInstance
      inferInstance
      inferInstance
      inferInstance
      inferInstance
      (homogeneousGrading k
        (segreDimension m n))
      (segreImageGrading k m n)
      inferInstance
      inferInstance
      (segreImageGradedHom k m n)
      (segreImageIrrelevantLE k m n)
      1
      Nat.zero_lt_one
      (coordinate k (segrePairIndex m n i j))
      (coordinate_mem_degreeOne k
        (segrePairIndex m n i j)) using 1
  all_goals rfl

/-- On a standard Segre-image chart, the composite with the ambient
projective structural map is the coefficient-algebra structural map. -/
@[reassoc]
lemma segreImagePairAwayι_toSpec
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    Proj.awayι
          (segreImageGrading k m n)
          (segreImageCoordinate k m n
            (segrePairIndex m n i j))
          (segreImageCoordinate_mem_degreeOne k m n
            (segrePairIndex m n i j))
          Nat.zero_lt_one ≫
        Proj.map
          (segreImageGradedHom k m n)
          (segreImageIrrelevantLE k m n) ≫
        toSpec k (segreDimension m n) =
      Spec.map
        (CommRingCat.ofHom
          (algebraMap k
            (SegreImageChartRing k m n i j))) := by
  rw [← Category.assoc]
  rw [segreImagePairAwayι_comp_map]
  rw [Category.assoc]
  have hAmbient :=
    standardAffineOpenCover_toSpec
      k (segreDimension m n)
        (segrePairIndex m n i j)
  change
    Proj.awayι
          (homogeneousGrading k (segreDimension m n))
          (coordinate k (segrePairIndex m n i j))
          (coordinate_mem_degreeOne k
            (segrePairIndex m n i j))
          Nat.zero_lt_one ≫
        toSpec k (segreDimension m n) =
      Spec.map
        (CommRingCat.ofHom
          (algebraMap k
            (ProjectiveCoordinateAway
              k (segreDimension m n)
              (segrePairIndex m n i j)))) at hAmbient
  rw [hAmbient]
  rw [← Spec.map_comp]
  congr 1
  ext r
  simpa only [CommRingCat.hom_comp, RingHom.coe_comp,
      Function.comp_apply, CommRingCat.hom_ofHom] using
    congrArg HomogeneousLocalization.val
      (segreImageChartMapFromAmbient_algebraMap
        k m n i j r)

/-- The affine-spectrum presentation of a standard product chart
identifies its structural map with the coefficient-algebra map. -/
@[reassoc]
lemma segreProductStandardChartIsoSpec_hom_toSpec
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    (segreProductStandardChartIsoSpec k m n i j).hom ≫
        Spec.map
          (CommRingCat.ofHom
            (algebraMap k
              (SegreProductChartRing k m n i j))) =
      (segreProductStandardOpenCover k m n).f (i, j) ≫
        binaryProjectiveToSpec k m n := by
  apply
    (cancel_epi
      (segreProductStandardChartIsoSpec
        k m n i j).inv).mp
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [binaryProjectiveToSpec]
  rw [segreProductStandardChartIsoSpec_inv_fst_assoc]
  have hLeft :=
    standardAffineOpenCover_toSpec k m i
  change
    (standardAffineCover k m).f i ≫ toSpec k m =
      Spec.map
        (CommRingCat.ofHom
          (algebraMap k
            (ProjectiveCoordinateAway k m i))) at hLeft
  symm
  calc
    ((Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom :
            ProjectiveCoordinateAway k m i →+*
              SegreProductChartRing k m n i j)) ≫
        (standardAffineCover k m).f i) ≫ toSpec k m) =
      Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom :
            ProjectiveCoordinateAway k m i →+*
              SegreProductChartRing k m n i j)) ≫
        ((standardAffineCover k m).f i ≫ toSpec k m) :=
      Category.assoc _ _ _
    _ = Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom :
            ProjectiveCoordinateAway k m i →+*
              SegreProductChartRing k m n i j)) ≫
        Spec.map
          (CommRingCat.ofHom
            (algebraMap k (ProjectiveCoordinateAway k m i))) :=
      CategoryTheory.whisker_eq _ hLeft
    _ = Spec.map
          (CommRingCat.ofHom
            (algebraMap k (SegreProductChartRing k m n i j))) := by
      rw [← Spec.map_comp]
      congr 1

/-- Every explicit product-chart Segre morphism is compatible with
the structural maps to the coefficient spectrum. -/
@[reassoc]
lemma segreProductStandardChartToProj_overBase
    (k : Type u) [CommRing k] (m n : ℕ)
    (i : Fin (m + 1)) (j : Fin (n + 1)) :
    segreProductStandardChartToProj k m n i j ≫
          Proj.map
            (segreImageGradedHom k m n)
            (segreImageIrrelevantLE k m n) ≫
        toSpec k (segreDimension m n) =
      (segreProductStandardOpenCover k m n).f (i, j) ≫
        binaryProjectiveToSpec k m n := by
  have hCoefficients :
      CommRingCat.ofHom
            (algebraMap k
              (SegreImageChartRing k m n i j)) ≫
          CommRingCat.ofHom
            (segreChartForwardAlgHom
              k m n i j).toRingHom =
        CommRingCat.ofHom
          (algebraMap k
            (SegreProductChartRing k m n i j)) := by
    ext r
    exact
      (segreChartForwardAlgHom k m n i j).commutes r
  simp only [segreProductStandardChartToProj,
    Category.assoc]
  rw [segreImagePairAwayι_toSpec]
  rw [← Spec.map_comp, hCoefficients]
  exact
    segreProductStandardChartIsoSpec_hom_toSpec
      k m n i j

/-- The globally glued Segre morphism is a morphism over `Spec k`. -/
@[reassoc]
lemma segreProductToImageProj_overBase
    (k : Type u) [CommRing k] (m n : ℕ) :
    segreProductToImageProj k m n ≫
          Proj.map
            (segreImageGradedHom k m n)
            (segreImageIrrelevantLE k m n) ≫
        toSpec k (segreDimension m n) =
      binaryProjectiveToSpec k m n := by
  apply
    (segreProductStandardOpenCover
      k m n).hom_ext
  intro q
  rcases q with ⟨i, j⟩
  have hChart :=
    segreProductStandardOpenCover_f_segreProductToImageProj
      k m n i j
  calc
    _ = ((segreProductStandardOpenCover k m n).f (i, j) ≫
          segreProductToImageProj k m n) ≫
        (Proj.map
            (segreImageGradedHom k m n)
            (segreImageIrrelevantLE k m n) ≫
          toSpec k (segreDimension m n)) := by
      simp only [Category.assoc]
    _ = segreProductStandardChartToProj k m n i j ≫
        (Proj.map
            (segreImageGradedHom k m n)
            (segreImageIrrelevantLE k m n) ≫
          toSpec k (segreDimension m n)) :=
      CategoryTheory.eq_whisker hChart _
    _ = _ := segreProductStandardChartToProj_overBase
      k m n i j

/-- The explicit glued Segre morphism, packaged with its base
compatibility and standard-chart isomorphism checks. -/
def segreChartwiseProjMorphism
    (k : Type u) [CommRing k] (m n : ℕ) :
    SegreChartwiseProjMorphism k m n where
  hom := segreProductToImageProj k m n
  overBase :=
    segreProductToImageProj_overBase k m n
  isIso_restrict := fun _ => by
    infer_instance

/-- The standard Segre chartwise comparison exists over every
commutative coefficient ring and in every pair of dimensions. -/
theorem standardSegreChartwiseProjMorphisms
    (k : Type u) [CommRing k] :
    StandardSegreChartwiseProjMorphisms k := by
  intro m n
  exact
    ⟨segreChartwiseProjMorphism k m n⟩

/-- Products of two standard projective spaces have their canonical
closed Segre embeddings over every commutative coefficient ring. -/
theorem standardSegreEmbeddings
    (k : Type u) [CommRing k] :
    StandardSegreEmbeddings k :=
  standardSegreEmbeddings_of_chartwise
    k
    (standardSegreChartwiseProjMorphisms k)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

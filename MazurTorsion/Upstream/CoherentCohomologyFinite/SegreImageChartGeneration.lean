/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SegreStandardChartInverse

/-!
# Generators of a standard Segre-image chart

The degree-zero localization of the Segre coordinate algebra is generated
by the coordinate ratios `Zₐ_b / Zᵢ_j`.  This is the algebraic input needed
to identify the explicit forward and inverse maps on a standard chart.
-/

open MvPolynomial
open HomogeneousLocalization
open scoped TensorProduct

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-- The rank-one quadratic relation among four Segre coordinates. -/
lemma segreImageCoordinate_cross_relation
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreImageCoordinate k m n (segrePairIndex m n a j) *
        segreImageCoordinate k m n (segrePairIndex m n i b) =
      segreImageCoordinate k m n (segrePairIndex m n a b) *
        segreImageCoordinate k m n (segrePairIndex m n i j) := by
  apply Subtype.ext
  simp [segreImageCoordinate, segrePairIndex,
    Algebra.TensorProduct.tmul_mul_tmul]
  ac_rfl

/-- The product of the two anchor ratios is the corresponding Segre
coordinate ratio. -/
lemma segreImageChartRatio_mul_anchorRatios
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreImageChartRatio k m n i a j j *
        segreImageChartRatio k m n i i j b =
      segreImageChartRatio k m n i a j b := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul,
    segreImageChartRatio, HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff,
    Localization.r_eq_r']
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Submonoid.coe_mul,
    Subtype.coe_mk, one_mul]
  rw [segreImageCoordinate_cross_relation]
  ring

/-- The degree-zero piece of the Segre image consists only of
coefficients. -/
lemma segreImageGrading_zero_eq_algebraMap
    (k : Type u) [CommRing k] (m n : ℕ)
    (x : segreImageGrading k m n 0) :
    ∃ r : k,
      (x : SegreCoordinateRing k m n) =
        algebraMap k (SegreCoordinateRing k m n) r := by
  obtain ⟨p, hp⟩ :=
    segreRangeCoordinateHom_surjective k m n
      (x : SegreCoordinateRing k m n)
  let p₀ :=
    DirectSum.decompose
      (homogeneousGrading k (segreDimension m n)) p 0
  have hp₀ :
      segreRangeCoordinateHom k m n p₀ =
        (x : SegreCoordinateRing k m n) := by
    calc
      segreRangeCoordinateHom k m n p₀ =
          DirectSum.decompose
            (segreImageGrading k m n)
            (segreRangeCoordinateHom k m n p) 0 :=
        map_directSumDecompose
          (homogeneousGrading k (segreDimension m n))
          (segreImageGrading k m n)
          (segreImageGradedHom k m n)
      _ =
          DirectSum.decompose
            (segreImageGrading k m n)
            (x : SegreCoordinateRing k m n) 0 := by
        rw [hp]
      _ = (x : SegreCoordinateRing k m n) :=
        DirectSum.decompose_of_mem_same
          (segreImageGrading k m n) x.2
  obtain ⟨r, hr⟩ :=
    Submodule.mem_one.mp
      ((MvPolynomial.homogeneousSubmodule_zero
        (σ := Fin (segreDimension m n + 1))
        (R := k)).le
        (DirectSum.decompose
          (homogeneousGrading k (segreDimension m n))
          p 0).2)
  refine ⟨r, ?_⟩
  rw [← hp₀]
  have hp₀C :
      (p₀ : MvPolynomial
        (Fin (segreDimension m n + 1)) k) =
        MvPolynomial.C r := by
    simpa [p₀] using hr.symm
  rw [hp₀C]
  simp

/-- The Segre coordinates generate their image algebra over its
degree-zero piece. -/
lemma segreImageCoordinate_adjoin_eq_top
    (k : Type u) [CommRing k] (m n : ℕ) :
    Algebra.adjoin
        (segreImageGrading k m n 0)
        (Set.range (segreImageCoordinate k m n)) =
      (⊤ : Subalgebra
        (segreImageGrading k m n 0)
        (SegreCoordinateRing k m n)) := by
  apply top_unique
  intro x hx
  clear hx
  obtain ⟨p, rfl⟩ :=
    segreRangeCoordinateHom_surjective k m n x
  induction p using MvPolynomial.induction_on with
  | C r =>
      let r₀ : segreImageGrading k m n 0 :=
        ⟨algebraMap k (SegreCoordinateRing k m n) r,
          SetLike.algebraMap_mem_graded
            (segreImageGrading k m n) r⟩
      simpa [r₀] using
        algebraMap_mem
          (Algebra.adjoin
            (segreImageGrading k m n 0)
            (Set.range (segreImageCoordinate k m n))) r₀
  | add p q hp hq =>
      simpa only [map_add] using
        add_mem hp hq
  | mul_X p s hp =>
      rw [map_mul]
      exact mul_mem hp
        (Algebra.subset_adjoin
          ⟨s, rfl⟩)

/-- The ratio of an arbitrary standard Segre coordinate by the fixed
chart coordinate. -/
@[reducible]
def segreImageCoordinateRatio
    (k : Type u) [CommRing k] (m n : ℕ)
    (anchor s : Fin (segreDimension m n + 1)) :
    Away
      (segreImageGrading k m n)
      (segreImageCoordinate k m n anchor) :=
  Away.mk
    (segreImageGrading k m n)
    (segreImageCoordinate_mem_degreeOne k m n anchor)
    1
    (segreImageCoordinate k m n s)
    (by
      simpa using
        segreImageCoordinate_mem_degreeOne k m n s)

@[simp]
lemma segreImageCoordinateRatio_segrePairIndex
    (k : Type u) [CommRing k] (m n : ℕ)
    (i a : Fin (m + 1)) (j b : Fin (n + 1)) :
    segreImageCoordinateRatio k m n
        (segrePairIndex m n i j)
        (segrePairIndex m n a b) =
      segreImageChartRatio k m n i a j b :=
  rfl

lemma segreImageCoordinate_prod_pow_mem
    (k : Type u) [CommRing k] (m n : ℕ)
    (e : Fin (segreDimension m n + 1) → ℕ) :
    (∏ s, segreImageCoordinate k m n s ^ e s) ∈
      segreImageGrading k m n
        ((∑ s, e s) • 1) := by
  simpa using
    SetLike.prod_pow_mem_graded
      (segreImageGrading k m n)
      (fun _ => 1)
      (segreImageCoordinate k m n)
      e
      (fun s _ =>
        segreImageCoordinate_mem_degreeOne k m n s)

lemma segreImageCoordinateRatio_prod_pow
    (k : Type u) [CommRing k] (m n : ℕ)
    (anchor : Fin (segreDimension m n + 1))
    (q : ℕ)
    (e : Fin (segreDimension m n + 1) → ℕ)
    (he : ∑ s, e s = q) :
    ∏ s, segreImageCoordinateRatio k m n anchor s ^ e s =
      Away.mk
        (segreImageGrading k m n)
        (segreImageCoordinate_mem_degreeOne k m n anchor)
        q
        (∏ s, segreImageCoordinate k m n s ^ e s)
        (by
          simpa [he] using
            segreImageCoordinate_prod_pow_mem k m n e) := by
  apply HomogeneousLocalization.val_injective
  change
    algebraMap
        (Away
          (segreImageGrading k m n)
          (segreImageCoordinate k m n anchor))
        (Localization.Away
          (segreImageCoordinate k m n anchor))
        (∏ s,
          segreImageCoordinateRatio k m n anchor s ^ e s) =
      _
  simp only [map_prod, map_pow,
    HomogeneousLocalization.algebraMap_apply,
    segreImageCoordinateRatio,
    HomogeneousLocalization.Away.val_mk,
    Localization.mk_prod, Localization.mk_pow]
  congr 1
  apply Subtype.ext
  simp only [SubmonoidClass.coe_finsetProd,
    SubmonoidClass.coe_pow, pow_one]
  calc
    ∏ x, segreImageCoordinate k m n anchor ^ e x =
        segreImageCoordinate k m n anchor ^ ∑ x, e x := by
      simpa using
        Finset.prod_pow_eq_pow_sum Finset.univ e
          (segreImageCoordinate k m n anchor)
    _ = segreImageCoordinate k m n anchor ^ q := by
      rw [he]

/-- The bounded monomial fractions appearing in Mathlib's general
homogeneous-localization generation theorem. -/
def segreImageChartMonomialGenerators
    (k : Type u) [CommRing k] (m n : ℕ)
    (anchor : Fin (segreDimension m n + 1)) :
    Set
      (Away
        (segreImageGrading k m n)
        (segreImageCoordinate k m n anchor)) :=
  degreeOneAwayMonomialGenerators
    (segreImageCoordinate k m n anchor)
    (segreImageCoordinate_mem_degreeOne k m n anchor)
    (Fin (segreDimension m n + 1))
    (segreImageCoordinate k m n)
    (fun s =>
      segreImageCoordinate_mem_degreeOne k m n s)

/-- The bounded monomial fractions generate over the degree-zero
component. -/
lemma segreImageChartMonomialGenerators_adjoin_eq_top
    (k : Type u) [CommRing k] (m n : ℕ)
    (anchor : Fin (segreDimension m n + 1)) :
    Algebra.adjoin
        (segreImageGrading k m n 0)
        (segreImageChartMonomialGenerators
          k m n anchor) =
      (⊤ : Subalgebra
        (segreImageGrading k m n 0)
        (Away
          (segreImageGrading k m n)
          (segreImageCoordinate k m n anchor))) :=
  degreeOneAwayMonomialGenerators_adjoin_eq_top
    (segreImageCoordinate k m n anchor)
    (segreImageCoordinate_mem_degreeOne k m n anchor)
    (Fin (segreDimension m n + 1))
    (segreImageCoordinate k m n)
    (fun s =>
      segreImageCoordinate_mem_degreeOne k m n s)
    (segreImageCoordinate_adjoin_eq_top k m n)

/-- The standard coordinate ratios generate the degree-zero chart
algebra over the coefficient ring. -/
lemma segreImageCoordinateRatio_adjoin_eq_top
    (k : Type u) [CommRing k] (m n : ℕ)
    (anchor : Fin (segreDimension m n + 1)) :
    Algebra.adjoin k
        (Set.range
          (segreImageCoordinateRatio k m n anchor)) =
      (⊤ : Subalgebra k
        (Away
          (segreImageGrading k m n)
          (segreImageCoordinate k m n anchor))) := by
  apply top_unique
  intro x hx
  clear hx
  have hx' :
      x ∈ Algebra.adjoin
        (segreImageGrading k m n 0)
        (segreImageChartMonomialGenerators
          k m n anchor) := by
    rw [segreImageChartMonomialGenerators_adjoin_eq_top]
    trivial
  induction hx' using Algebra.adjoin_induction with
  | mem z hz =>
      change z ∈
        { Away.mk
            (segreImageGrading k m n)
            (segreImageCoordinate_mem_degreeOne
              k m n anchor)
            a
            (∏ s,
              segreImageCoordinate k m n s ^ e s)
            (he ▸
              SetLike.prod_pow_mem_graded
                (segreImageGrading k m n)
                (fun _ => 1)
                (segreImageCoordinate k m n)
                e
                (fun s _ =>
                  segreImageCoordinate_mem_degreeOne
                    k m n s)) |
          (a : ℕ)
          (e : Fin (segreDimension m n + 1) → ℕ)
          (he : ∑ s, e s • 1 = a • 1)
          (_ : ∀ s, e s ≤ 1) } at hz
      obtain ⟨a, e, he, _, rfl⟩ := hz
      have he' : ∑ s, e s = a := by
        simpa using he
      rw [← segreImageCoordinateRatio_prod_pow
        k m n anchor a e he']
      apply prod_mem
      intro s _
      exact pow_mem
        (Algebra.subset_adjoin (R := k)
          (show
            segreImageCoordinateRatio
                k m n anchor s ∈
              Set.range
                (segreImageCoordinateRatio
                  k m n anchor) from
            ⟨s, rfl⟩))
        (e s)
  | algebraMap r₀ =>
      obtain ⟨r, hr⟩ :=
        segreImageGrading_zero_eq_algebraMap
          k m n r₀
      have hcoeff :
          algebraMap
              (segreImageGrading k m n 0)
              (Away
                (segreImageGrading k m n)
                (segreImageCoordinate k m n anchor))
              r₀ =
            algebraMap k
              (Away
                (segreImageGrading k m n)
                (segreImageCoordinate k m n anchor))
              r := by
        calc
          _ = Away.mk
                (segreImageGrading k m n)
                (segreImageCoordinate_mem_degreeOne
                  k m n anchor)
                0
                (r₀ : SegreCoordinateRing k m n)
                r₀.2 := rfl
          _ = Away.mk
                (segreImageGrading k m n)
                (segreImageCoordinate_mem_degreeOne
                  k m n anchor)
                0
                (algebraMap k
                  (SegreCoordinateRing k m n) r)
                (by
                  simpa using
                    SetLike.algebraMap_mem_graded
                      (segreImageGrading k m n) r) := by
            refine HomogeneousLocalization.val_injective
              (Submonoid.powers
                (segreImageCoordinate k m n anchor)) ?_
            exact congrArg
              (fun z : SegreCoordinateRing k m n =>
                Localization.mk z
                  (1 : Submonoid.powers
                    (segreImageCoordinate k m n anchor))) hr
          _ = _ :=
            (homogeneousAway_algebraMap_eq_mk
              (segreImageCoordinate k m n anchor)
              (segreImageCoordinate_mem_degreeOne
                k m n anchor) r).symm
      have hrmem :
          algebraMap k
              (Away
                (segreImageGrading k m n)
                (segreImageCoordinate k m n anchor)) r ∈
            Algebra.adjoin k
              (Set.range
                (segreImageCoordinateRatio k m n anchor)) :=
        algebraMap_mem _ r
      exact (congrArg
        (fun z => z ∈
          Algebra.adjoin k
            (Set.range
              (segreImageCoordinateRatio k m n anchor)))
        hcoeff).mpr hrmem
  | add x y hx hy hx' hy' =>
      exact add_mem hx' hy'
  | mul x y hx hy hx' hy' =>
      exact mul_mem hx' hy'

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

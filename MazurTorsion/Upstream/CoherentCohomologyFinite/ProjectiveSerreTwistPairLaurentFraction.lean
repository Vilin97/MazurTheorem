/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistLaurentChartIndependence

/-!
# Pairwise Serre transition fractions in Laurent coordinates

For two distinct projective coordinates, this file writes the ratio
`Xᵢ / Xⱼ` directly in the homogeneous localization away from the
squarefree product `XᵢXⱼ` and computes its Laurent exponent.
-/

open scoped BigOperators


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
open MazurTorsion.AlgebraicGeometry.CoherentCohomology
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

noncomputable section

lemma castAwayMk
    {R A : Type} [CommRing R] [CommRing A] [Module R A]
    {𝒜 : ℕ → Submodule R A} [GradedRing 𝒜]
    {f g a : A} {q r n : ℕ}
    (hfg : f = g)
    (hf : f ∈ 𝒜 q) (hg : g ∈ 𝒜 r)
    (ha : a ∈ 𝒜 (n • q)) (hb : a ∈ 𝒜 (n • r)) :
    RingEquiv.cast hfg (HomogeneousLocalization.Away.mk 𝒜 hf n a ha) =
      HomogeneousLocalization.Away.mk 𝒜 hg n a hb := by
  cases hfg
  change
    HomogeneousLocalization.Away.mk 𝒜 hf n a ha =
      HomogeneousLocalization.Away.mk 𝒜 hg n a hb
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk]

def coordinatePair
    {d : ℕ} (i j : Fin (d + 1)) : Finset (Fin (d + 1)) :=
  {i, j}

/-- The first coordinate as an element of its coordinate pair. -/
def coordinatePairLeft
    {d : ℕ} (i j : Fin (d + 1)) :
    ↥(coordinatePair i j) :=
  ⟨i, by simp [coordinatePair]⟩

/-- The second coordinate as an element of its coordinate pair. -/
def coordinatePairRight
    {d : ℕ} (i j : Fin (d + 1)) :
    ↥(coordinatePair i j) :=
  ⟨j, by simp [coordinatePair]⟩

/-- A pair chosen from a finite intersection is contained in that
intersection. -/
lemma coordinatePair_subset
    {d : ℕ} {I : Finset (Fin (d + 1))}
    (i j : ↥I) :
    coordinatePair i.1 j.1 ⊆ I := by
  intro x hx
  simp only [coordinatePair, Finset.mem_insert,
    Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact i.2
  · exact j.2

lemma variableProduct_coordinatePair
    {k : Type} [CommRing k] {d : ℕ}
    {i j : Fin (d + 1)} (hij : i ≠ j) :
    variableProduct (k := k) (coordinatePair i j) =
      coordinate k i * coordinate k j := by
  simp [coordinatePair, variableProduct, hij, coordinate]

def awayFractionOnCoordinatePair
    {k : Type} [CommRing k] {d : ℕ}
    (i j : Fin (d + 1)) (hij : i ≠ j) :
    HomogeneousLocalization.Away
      (homogeneousGrading k d)
      (variableProduct (k := k) (coordinatePair i j)) :=
  HomogeneousLocalization.Away.mk
    (homogeneousGrading k d)
    (variableProduct_mem_degreeCard (coordinatePair i j))
    1 (coordinate k i * coordinate k i)
    (by
      rw [MvPolynomial.mem_homogeneousSubmodule]
      simpa [coordinatePair, hij] using
        MvPolynomial.IsHomogeneous.mul
          (MvPolynomial.isHomogeneous_X k i)
          (MvPolynomial.isHomogeneous_X k i))

/-- The ratio `Xᵢ / Xⱼ`, expressed over the squarefree coordinate pair,
maps to the Laurent exponent `eᵢ - eⱼ`. -/
lemma homogeneousAwayToLaurent_awayFractionOnCoordinatePair
    {k : Type} [CommRing k] {d : ℕ}
    (i j : Fin (d + 1)) (hij : i ≠ j) :
    homogeneousAwayToLaurent
        (k := k) (d := d) (coordinatePair i j)
        (awayFractionOnCoordinatePair i j hij) =
      AddMonoidAlgebra.single
        (coordinateShift i 1 - coordinateShift j 1) (1 : k) := by
  change
    localizationToLaurent (k := k) (coordinatePair i j)
        (HomogeneousLocalization.val
          (awayFractionOnCoordinatePair i j hij)) =
      AddMonoidAlgebra.single
        (coordinateShift i 1 - coordinateShift j 1) (1 : k)
  unfold awayFractionOnCoordinatePair
  rw [HomogeneousLocalization.Away.val_mk,
    localizationToLaurent_mk]
  simp only [map_mul, MvPolynomial.X,
    polynomialToLaurent_monomial,
    variableProductInverse, AddMonoidAlgebra.single_pow,
    AddMonoidAlgebra.single_mul_single]
  congr 1
  · funext x
    by_cases hxi : x = i
    · subst x
      simp [coordinatePair, indicatorExponent, coordinateShift, hij]
    · by_cases hxj : x = j
      · subst x
        simp [coordinatePair, indicatorExponent, coordinateShift, hxi]
      · simp [coordinatePair, indicatorExponent, coordinateShift,
          hxi, hxj]
  · simp

/-- The inverse ratio `Xⱼ / Xᵢ` over the same squarefree coordinate
pair. -/
def awayFractionInvOnCoordinatePair
    {k : Type} [CommRing k] {d : ℕ}
    (i j : Fin (d + 1)) (hij : i ≠ j) :
    HomogeneousLocalization.Away
      (homogeneousGrading k d)
      (variableProduct (k := k) (coordinatePair i j)) :=
  HomogeneousLocalization.Away.mk
    (homogeneousGrading k d)
    (variableProduct_mem_degreeCard (coordinatePair i j))
    1 (coordinate k j * coordinate k j)
    (by
      rw [MvPolynomial.mem_homogeneousSubmodule]
      simpa [coordinatePair, hij] using
        MvPolynomial.IsHomogeneous.mul
          (MvPolynomial.isHomogeneous_X k j)
          (MvPolynomial.isHomogeneous_X k j))

/-- The preceding inverse ratio has Laurent exponent `eⱼ - eᵢ`. -/
lemma homogeneousAwayToLaurent_awayFractionInvOnCoordinatePair
    {k : Type} [CommRing k] {d : ℕ}
    (i j : Fin (d + 1)) (hij : i ≠ j) :
    homogeneousAwayToLaurent
        (k := k) (d := d) (coordinatePair i j)
        (awayFractionInvOnCoordinatePair i j hij) =
      AddMonoidAlgebra.single
        (coordinateShift j 1 - coordinateShift i 1) (1 : k) := by
  change
    localizationToLaurent (k := k) (coordinatePair i j)
        (HomogeneousLocalization.val
          (awayFractionInvOnCoordinatePair i j hij)) =
      AddMonoidAlgebra.single
        (coordinateShift j 1 - coordinateShift i 1) (1 : k)
  unfold awayFractionInvOnCoordinatePair
  rw [HomogeneousLocalization.Away.val_mk,
    localizationToLaurent_mk]
  simp only [map_mul, MvPolynomial.X,
    polynomialToLaurent_monomial,
    variableProductInverse, AddMonoidAlgebra.single_pow,
    AddMonoidAlgebra.single_mul_single]
  congr 1
  · funext x
    by_cases hxj : x = j
    · subst x
      simp [coordinatePair, indicatorExponent, coordinateShift, hij.symm]
    · by_cases hxi : x = i
      · subst x
        simp [coordinatePair, indicatorExponent, coordinateShift, hxj]
      · simp [coordinatePair, indicatorExponent, coordinateShift,
          hxi, hxj]
  · simp

/-- The direct pairwise fraction and its reversed fraction multiply to
one. -/
lemma awayFractionOnCoordinatePair_mul_inv
    {k : Type} [CommRing k] {d : ℕ}
    (i j : Fin (d + 1)) (hij : i ≠ j) :
    awayFractionOnCoordinatePair (k := k) i j hij *
        awayFractionInvOnCoordinatePair (k := k) i j hij =
      1 := by
  apply homogeneousAwayToLaurent_injective (coordinatePair i j)
  rw [map_mul,
    homogeneousAwayToLaurent_awayFractionOnCoordinatePair,
    homogeneousAwayToLaurent_awayFractionInvOnCoordinatePair]
  rw [AddMonoidAlgebra.single_mul_single]
  rw [sub_add_sub_cancel]
  rw [sub_self, map_one]
  simpa using
    (AddMonoidAlgebra.one_def :
      (1 : LaurentAlgebra k (Fin (d + 1))) =
        AddMonoidAlgebra.single 0 (1 : k)).symm

/-- The pairwise coordinate ratio as a unit in the squarefree
homogeneous localization. -/
def awayUnitOnCoordinatePair
    {k : Type} [CommRing k] {d : ℕ}
    (i j : Fin (d + 1)) (hij : i ≠ j) :
    (HomogeneousLocalization.Away
      (homogeneousGrading k d)
      (variableProduct (k := k) (coordinatePair i j)))ˣ where
  val := awayFractionOnCoordinatePair i j hij
  inv := awayFractionInvOnCoordinatePair i j hij
  val_inv := awayFractionOnCoordinatePair_mul_inv i j hij
  inv_val := by
    rw [mul_comm]
    exact awayFractionOnCoordinatePair_mul_inv i j hij

/-- Casting the original product-denominator transition unit to the
squarefree coordinate-pair denominator gives the direct pair unit. -/
lemma awayUnitOnCoordinatePair_eq_map_awayUnit
    {k : Type} [CommRing k] {d : ℕ}
    (i j : Fin (d + 1)) (hij : i ≠ j) :
    awayUnitOnCoordinatePair (k := k) i j hij =
      Units.map
        (RingEquiv.cast
          (variableProduct_coordinatePair
            (k := k) hij).symm).toMonoidHom
        (awayUnit k d i j) := by
  apply Units.ext
  change
    awayFractionOnCoordinatePair (k := k) i j hij =
      RingEquiv.cast
        (variableProduct_coordinatePair
          (k := k) hij).symm
        (awayFraction k d i j)
  unfold awayFractionOnCoordinatePair awayFraction
  symm
  apply castAwayMk

/-- Laurent monomial units depend multiplicatively on their exponent. -/
def laurentMonomialUnitHom
    {k ι : Type} [CommRing k] [Fintype ι] :
    Multiplicative (ProjectiveExponent ι) →*
      (LaurentAlgebra k ι)ˣ where
  toFun a := laurentMonomialUnit (k := k) a.toAdd
  map_one' := by
    change laurentMonomialUnit (k := k) 0 = 1
    apply Units.ext
    change
      (AddMonoidAlgebra.single 0 (1 : k) : LaurentAlgebra k ι) = 1
    exact
      (AddMonoidAlgebra.one_def :
        (1 : LaurentAlgebra k ι) =
          AddMonoidAlgebra.single 0 (1 : k)).symm
  map_mul' a b := by
    change
      laurentMonomialUnit (k := k)
          (a.toAdd + b.toAdd) =
        laurentMonomialUnit (k := k) a.toAdd *
          laurentMonomialUnit (k := k) b.toAdd
    apply Units.ext
    simp only [laurentMonomialUnit_val, Units.val_mul]
    rw [AddMonoidAlgebra.single_mul_single]
    simp

/-- Integer powers of a Laurent monomial unit multiply its exponent. -/
lemma laurentMonomialUnit_zpow
    {k ι : Type} [CommRing k] [Fintype ι]
    (a : ProjectiveExponent ι) (m : ℤ) :
    laurentMonomialUnit (k := k) a ^ m =
      laurentMonomialUnit (k := k) (m • a) := by
  have h :=
    (laurentMonomialUnitHom (k := k) (ι := ι)).map_zpow
      (Multiplicative.ofAdd a) m
  change
    laurentMonomialUnit (k := k)
        ((Multiplicative.ofAdd a ^ m).toAdd) =
      laurentMonomialUnit (k := k) a ^ m at h
  simpa using h.symm

/-- Concentrating the integer `m` at one coordinate is scalar
multiplication of the corresponding unit coordinate exponent. -/
lemma coordinateShift_eq_zsmul_one
    {ι : Type} [DecidableEq ι]
    (i : ι) (m : ℤ) :
    coordinateShift i m = m • coordinateShift i 1 := by
  funext x
  by_cases hxi : x = i <;>
    simp [coordinateShift, hxi]

/-- Negating the powered ratio exponent reverses its two coordinates. -/
lemma neg_zsmul_coordinateShift_sub
    {ι : Type} [DecidableEq ι]
    (i j : ι) (m : ℤ) :
    -(m •
        (coordinateShift i 1 - coordinateShift j 1)) =
      coordinateShift j m - coordinateShift i m := by
  funext x
  by_cases hxi : x = i
  · subst x
    by_cases hij : i = j
    · subst j
      simp [coordinateShift]
    · simp [coordinateShift, hij]
  · by_cases hxj : x = j
    · subst x
      simp [coordinateShift, hxi]
    · simp [coordinateShift, hxi, hxj]

/-- The inverse `m`-th power of the pairwise transition unit maps to
the Laurent chart-change monomial `Xⱼ^m Xᵢ⁻ᵐ`. -/
lemma homogeneousAwayToLaurent_awayUnitOnCoordinatePair_zpow_inv
    {k : Type} [CommRing k] {d : ℕ}
    (i j : Fin (d + 1)) (hij : i ≠ j) (m : ℤ) :
    homogeneousAwayToLaurent
        (k := k) (d := d) (coordinatePair i j)
        (((awayUnitOnCoordinatePair
          (k := k) i j hij) ^ m).inv :
          HomogeneousLocalization.Away
            (homogeneousGrading k d)
            (variableProduct (k := k)
              (coordinatePair i j))) =
      AddMonoidAlgebra.single
        (coordinateShift j m - coordinateShift i m) (1 : k) := by
  let F :=
    Units.map
      (homogeneousAwayToLaurent
        (k := k) (d := d)
        (coordinatePair i j)).toMonoidHom
  have hF :
      F (awayUnitOnCoordinatePair (k := k) i j hij) =
        laurentMonomialUnit
          (k := k)
          (coordinateShift i 1 - coordinateShift j 1) := by
    apply Units.ext
    exact
      homogeneousAwayToLaurent_awayFractionOnCoordinatePair
        (k := k) i j hij
  change
    ((F (((awayUnitOnCoordinatePair
      (k := k) i j hij) ^ m)⁻¹) :
      (LaurentAlgebra k (Fin (d + 1)))ˣ) :
        LaurentAlgebra k (Fin (d + 1))) =
      AddMonoidAlgebra.single
        (coordinateShift j m - coordinateShift i m) (1 : k)
  rw [map_inv, map_zpow, hF,
    laurentMonomialUnit_zpow]
  change
    AddMonoidAlgebra.single
        (-(m •
          (coordinateShift i 1 - coordinateShift j 1))) (1 : k) =
      AddMonoidAlgebra.single
        (coordinateShift j m - coordinateShift i m) (1 : k)
  rw [neg_zsmul_coordinateShift_sub]

/-- In the squarefree pair localization, the inverse powered transition
unit is exactly the named chart-change fraction. -/
lemma awayUnitOnCoordinatePair_zpow_inv_eq_chartChangeFraction
    {k : Type} [CommRing k] {d : ℕ}
    (i j : Fin (d + 1)) (hij : i ≠ j) (m : ℤ) :
    (((awayUnitOnCoordinatePair
        (k := k) i j hij) ^ m).inv :
      HomogeneousLocalization.Away
        (homogeneousGrading k d)
        (variableProduct (k := k) (coordinatePair i j))) =
      chartChangeFraction (k := k) d (coordinatePair i j)
        (coordinatePairLeft i j)
        (coordinatePairRight i j) m := by
  apply homogeneousAwayToLaurent_injective (coordinatePair i j)
  rw [
    homogeneousAwayToLaurent_awayUnitOnCoordinatePair_zpow_inv,
    homogeneousAwayToLaurent_chartChangeFraction]
  rfl

/-- Extending the pair chart-change fraction to any Laurent intersection
containing the pair gives the chart-change fraction on that intersection. -/
lemma homogeneousAwayRestriction_pairChartChangeFraction
    {k : Type} [CommRing k]
    {d : ℕ} {I : Finset (Fin (d + 1))}
    (i j : ↥I) (m : ℤ) :
    homogeneousAwayRestriction (k := k)
        (coordinatePair_subset i j)
        (chartChangeFraction (k := k) d (coordinatePair i.1 j.1)
          (coordinatePairLeft i.1 j.1)
          (coordinatePairRight i.1 j.1) m) =
      chartChangeFraction (k := k) d I i j m := by
  rw [chartChangeFraction,
    homogeneousAwayRestriction_degreeZeroFraction,
    chartChangeFraction]
  congr 1

end

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

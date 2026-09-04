/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassProjectiveProductDoublingOutputCharts

/-!
# A secant-and-doubling cover of every projective-pair chart

The raw secant coordinates vanish on equivalent projective inputs, exactly
where the projective group law chooses doubling.  This file proves that the
two secant output-coordinate opens together with the two first-input doubling
output-coordinate opens cover every affine tensor-product pair chart.

The proof is primewise.  It maps both universal inputs to the fraction field
of a prime quotient, invokes nonsingularity of the elliptic projective group
law there, and reflects the resulting nonvanishing statement back to the
original prime.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped WeierstrassCurve.Projective

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassProjectiveCubic

universe u

variable {K : Type u} [Field K]

private lemma nonsingular_of_equation_of_ne_zero
    {F : Type u} [Field F] (W : WeierstrassCurve F) [W.IsElliptic]
    {P : Fin 3 → F} (hP : W.toProjective.Equation P) (hP0 : P ≠ 0) :
    W.toProjective.Nonsingular P := by
  by_cases hPz : P (2 : Fin 3) = 0
  · have hPx : P (0 : Fin 3) = 0 :=
      W.toProjective.X_eq_zero_of_Z_eq_zero hP hPz
    have hPy : P (1 : Fin 3) ≠ 0 := by
      intro hPy
      apply hP0
      funext i
      fin_cases i
      · simpa using hPx
      · simpa using hPy
      · simpa using hPz
    rw [W.toProjective.nonsingular_of_Z_eq_zero hPz]
    refine ⟨hP, Or.inr ?_⟩
    simpa [hPx] using pow_ne_zero 2 hPy
  · rw [W.toProjective.nonsingular_of_Z_ne_zero hPz,
      ← W.toAffine.equation_iff_nonsingular,
      ← W.toProjective.equation_of_Z_ne_zero hPz]
    exact hP

private lemma ne_zero_of_nonsingular
    {F : Type u} [Field F] (W : WeierstrassCurve F)
    {P : Fin 3 → F} (hP : W.toProjective.Nonsingular P) : P ≠ 0 := by
  intro h
  subst P
  rw [W.toProjective.nonsingular_iff] at hP
  simp at hP

private lemma Y_or_Z_ne_zero_of_equation_of_ne_zero
    {F : Type u} [Field F] (W : WeierstrassCurve F)
    {P : Fin 3 → F} (hP : W.toProjective.Equation P) (hP0 : P ≠ 0) :
    P (1 : Fin 3) ≠ 0 ∨ P (2 : Fin 3) ≠ 0 := by
  by_cases hPz : P (2 : Fin 3) = 0
  · left
    intro hPy
    apply hP0
    have hPx : P (0 : Fin 3) = 0 :=
      W.toProjective.X_eq_zero_of_Z_eq_zero hP hPz
    funext i
    fin_cases i
    · simpa using hPx
    · simpa using hPy
    · simpa using hPz
  · exact Or.inr hPz

private theorem add_or_dbl_Y_or_Z_ne_zero
    {F : Type u} [Field F] (W : WeierstrassCurve F) [W.IsElliptic]
    {P Q : Fin 3 → F}
    (hP : W.toProjective.Equation P) (hQ : W.toProjective.Equation Q)
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) :
    W.toProjective.addXYZ P Q (1 : Fin 3) ≠ 0 ∨
      W.toProjective.addXYZ P Q (2 : Fin 3) ≠ 0 ∨
      W.toProjective.dblXYZ P (1 : Fin 3) ≠ 0 ∨
      W.toProjective.dblXYZ P (2 : Fin 3) ≠ 0 := by
  have hPns := nonsingular_of_equation_of_ne_zero W hP hP0
  have hQns := nonsingular_of_equation_of_ne_zero W hQ hQ0
  by_cases hPQ : P ≈ Q
  · have hsum := WeierstrassCurve.Projective.nonsingular_add hPns hQns
    rw [WeierstrassCurve.Projective.add_of_equiv hPQ] at hsum
    have hyz := Y_or_Z_ne_zero_of_equation_of_ne_zero W hsum.1
      (ne_zero_of_nonsingular W hsum)
    exact Or.inr (Or.inr hyz)
  · have hsum := WeierstrassCurve.Projective.nonsingular_add hPns hQns
    rw [WeierstrassCurve.Projective.add_of_not_equiv hPQ] at hsum
    have hyz := Y_or_Z_ne_zero_of_equation_of_ne_zero W hsum.1
      (ne_zero_of_nonsingular W hsum)
    exact hyz.imp id (fun h ↦ Or.inl h)

/-- The `Y` and `Z` output opens for the secant and first-input doubling
triples jointly cover every projective-pair chart. -/
theorem projectivePairChartAdditionAndDoublingOutputOpens_cover
    (W : WeierstrassCurve K) [W.IsElliptic] (ij : Bool × Bool) :
    PrimeSpectrum.basicOpen
        (projectivePairChartAdditionCoordinates W ij (1 : Fin 3)) ⊔
      (PrimeSpectrum.basicOpen
          (projectivePairChartAdditionCoordinates W ij (2 : Fin 3)) ⊔
        (PrimeSpectrum.basicOpen
            (projectivePairChartFirstDoublingCoordinates W ij (1 : Fin 3)) ⊔
          PrimeSpectrum.basicOpen
            (projectivePairChartFirstDoublingCoordinates W ij (2 : Fin 3)))) = ⊤ := by
  apply top_unique
  intro p _
  change projectivePairChartAdditionCoordinates W ij (1 : Fin 3) ∉ p.asIdeal ∨
    projectivePairChartAdditionCoordinates W ij (2 : Fin 3) ∉ p.asIdeal ∨
    projectivePairChartFirstDoublingCoordinates W ij (1 : Fin 3) ∉ p.asIdeal ∨
    projectivePairChartFirstDoublingCoordinates W ij (2 : Fin 3) ∉ p.asIdeal
  by_contra hcover
  push Not at hcover
  rcases hcover with ⟨hAY, hAZ, hDY, hDZ⟩
  let R := projectivePairChartCoordinateRing W ij
  let Q := R ⧸ p.asIdeal
  letI : CommRing Q := Ideal.Quotient.commRing p.asIdeal
  letI : IsDomain Q :=
    (Ideal.Quotient.isDomain_iff_prime p.asIdeal).mpr inferInstance
  let F := FractionRing Q
  let q₀ : R →+* Q := Ideal.Quotient.mk p.asIdeal
  let q : R →+* F := (algebraMap Q F).comp q₀
  let g : K →+* F := q.comp (algebraMap K R)
  let P₁ : Fin 3 → F := q ∘ projectivePairChartFirstUniversalPoint W ij
  let P₂ : Fin 3 → F := q ∘ projectivePairChartSecondUniversalPoint W ij
  have hP₁ : (W.map g).toProjective.Equation P₁ := by
    simpa [g, P₁, R, projectivePairChartMappedCurve,
      WeierstrassCurve.map_map] using
      (projectivePairChartFirstUniversalPoint_equation W ij).map q
  have hP₂ : (W.map g).toProjective.Equation P₂ := by
    simpa [g, P₂, R, projectivePairChartMappedCurve,
      WeierstrassCurve.map_map] using
      (projectivePairChartSecondUniversalPoint_equation W ij).map q
  have hP₁0 : P₁ ≠ 0 := by
    intro h
    have hz : P₁ (coveringCoordinate ij.1) = 0 :=
      congrFun h (coveringCoordinate ij.1)
    have hone : P₁ (coveringCoordinate ij.1) = 1 := by
      simp [P₁]
    exact one_ne_zero (hone.symm.trans hz)
  have hP₂0 : P₂ ≠ 0 := by
    intro h
    have hz : P₂ (coveringCoordinate ij.2) = 0 :=
      congrFun h (coveringCoordinate ij.2)
    have hone : P₂ (coveringCoordinate ij.2) = 1 := by
      simp [P₂]
    exact one_ne_zero (hone.symm.trans hz)
  have hfield := add_or_dbl_Y_or_Z_ne_zero (W.map g)
    hP₁ hP₂ hP₁0 hP₂0
  have hcurve :
      W.map g = (projectivePairChartMappedCurve W ij).map q := by
    change W.map (q.comp (algebraMap K R)) =
      (W.map (algebraMap K R)).map q
    rw [WeierstrassCurve.map_map]
  have hAmap : (W.map g).toProjective.addXYZ P₁ P₂ =
      q ∘ projectivePairChartAdditionCoordinates W ij := by
    rw [hcurve]
    simp [P₁, P₂, projectivePairChartAdditionCoordinates]
  have hDmap : (W.map g).toProjective.dblXYZ P₁ =
      q ∘ projectivePairChartFirstDoublingCoordinates W ij := by
    rw [hcurve]
    simp [P₁, projectivePairChartFirstDoublingCoordinates]
  rw [hAmap, hDmap] at hfield
  simp only [Function.comp_apply] at hfield
  have hq_of_mem (a : R) (ha : a ∈ p.asIdeal) : q a = 0 := by
    change algebraMap Q F (q₀ a) = 0
    rw [show q₀ a = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr ha,
      map_zero]
  rcases hfield with h | h | h | h
  · exact h (hq_of_mem _ hAY)
  · exact h (hq_of_mem _ hAZ)
  · exact h (hq_of_mem _ hDY)
  · exact h (hq_of_mem _ hDZ)

end WeierstrassProjectiveCubic
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli

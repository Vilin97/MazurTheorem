/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.EllipticCurve.IntegerPrimeSpecialization
import MazurTorsion.EllipticCurve.VariableChange
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.NormNum

/-!
# The nonsingular group of an additive special Weierstrass cubic

Over the residue fields at five and eleven, a Weierstrass cubic with vanishing discriminant and
`c₄` is cuspidal.  This file proves the precise group-theoretic form needed by the tame additive
reduction consumer: its group of nonsingular points is additively equivalent to the residue field.

The proof normalizes the equation to short Weierstrass form, where the two invariant equalities
force the equation to be `Y² = X³`.  The cardinality of that one concrete nonsingular point type is
then checked by finite enumeration over `ZMod 5` and `ZMod 11`.  Prime cardinality supplies the
additive group equivalence; no Hasse bound or ellipticity assumption is used.
-/

noncomputable section

open IsLocalRing

namespace MazurTorsion.EllipticCurve

open MazurTorsion.IntegerPrimeSpecialization
open WeierstrassCurve WeierstrassCurve.Affine
open IsDedekindDomain.HeightOneSpectrum

/-- The standard cuspidal short Weierstrass equation `Y² = X³`. -/
def cuspidalShortCurve (F : Type*) [CommRing F] : WeierstrassCurve F :=
  ⟨0, 0, 0, 0, 0⟩

/-- The standard cusp has five nonsingular projective points over `F₅`. -/
theorem card_cuspidalShortCurve_five :
    Fintype.card (cuspidalShortCurve (ZMod 5)).toAffine.Point = 5 := by
  decide

/-- The standard cusp has eleven nonsingular projective points over `F₁₁`. -/
theorem card_cuspidalShortCurve_eleven :
    Fintype.card (cuspidalShortCurve (ZMod 11)).toAffine.Point = 11 := by
  decide

private theorem short_eq_cuspidal_five
    (W : WeierstrassCurve (ZMod 5)) [W.IsShortNF]
    (hΔ : W.Δ = 0) (hc₄ : W.c₄ = 0) :
    W = cuspidalShortCurve (ZMod 5) := by
  have hc₄' : (-48 : ZMod 5) * W.a₄ = 0 := by
    rw [← W.c₄_of_isShortNF]
    exact hc₄
  have ha₄ : W.a₄ = 0 :=
    (mul_eq_zero.mp hc₄').resolve_left (by decide)
  have hΔ' : (-16 : ZMod 5) * (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2) = 0 := by
    rw [← W.Δ_of_isShortNF]
    exact hΔ
  have hinner : (4 : ZMod 5) * W.a₄ ^ 3 + 27 * W.a₆ ^ 2 = 0 :=
    (mul_eq_zero.mp hΔ').resolve_left (by decide)
  rw [ha₄, zero_pow (by decide), mul_zero, zero_add] at hinner
  have ha₆sq : W.a₆ ^ 2 = 0 :=
    (mul_eq_zero.mp hinner).resolve_left (by decide)
  have ha₆ : W.a₆ = 0 := sq_eq_zero_iff.mp ha₆sq
  ext <;> simp [cuspidalShortCurve, ha₄, ha₆]

private theorem short_eq_cuspidal_eleven
    (W : WeierstrassCurve (ZMod 11)) [W.IsShortNF]
    (hΔ : W.Δ = 0) (hc₄ : W.c₄ = 0) :
    W = cuspidalShortCurve (ZMod 11) := by
  have hc₄' : (-48 : ZMod 11) * W.a₄ = 0 := by
    rw [← W.c₄_of_isShortNF]
    exact hc₄
  have ha₄ : W.a₄ = 0 :=
    (mul_eq_zero.mp hc₄').resolve_left (by decide)
  have hΔ' : (-16 : ZMod 11) * (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2) = 0 := by
    rw [← W.Δ_of_isShortNF]
    exact hΔ
  have hinner : (4 : ZMod 11) * W.a₄ ^ 3 + 27 * W.a₆ ^ 2 = 0 :=
    (mul_eq_zero.mp hΔ').resolve_left (by decide)
  rw [ha₄, zero_pow (by decide), mul_zero, zero_add] at hinner
  have ha₆sq : W.a₆ ^ 2 = 0 :=
    (mul_eq_zero.mp hinner).resolve_left (by decide)
  have ha₆ : W.a₆ = 0 := sq_eq_zero_iff.mp ha₆sq
  ext <;> simp [cuspidalShortCurve, ha₄, ha₆]

/-- A Weierstrass cubic over `F₅` with vanishing discriminant and `c₄` has exactly five
nonsingular projective points. -/
theorem natCard_point_eq_five_of_cuspidal
    (W : WeierstrassCurve (ZMod 5)) (hΔ : W.Δ = 0) (hc₄ : W.c₄ = 0) :
    Nat.card W.toAffine.Point = 5 := by
  letI : Invertible (2 : ZMod 5) := invertibleOfNonzero (by decide)
  letI : Invertible (3 : ZMod 5) := invertibleOfNonzero (by decide)
  let C : WeierstrassCurve.VariableChange (ZMod 5) := W.toShortNF
  let Wshort : WeierstrassCurve (ZMod 5) := C • W
  haveI : Wshort.IsShortNF := by
    dsimp only [Wshort, C]
    infer_instance
  have hΔshort : Wshort.Δ = 0 := by
    change (C • W).Δ = 0
    rw [variableChange_Δ, hΔ, mul_zero]
  have hc₄short : Wshort.c₄ = 0 := by
    change (C • W).c₄ = 0
    rw [variableChange_c₄, hc₄, mul_zero]
  have hshort : Wshort = cuspidalShortCurve (ZMod 5) :=
    short_eq_cuspidal_five Wshort hΔshort hc₄short
  calc
    Nat.card W.toAffine.Point = Nat.card Wshort.toAffine.Point :=
      Nat.card_congr (Point.equivVariableChange W C).symm.toEquiv
    _ = Nat.card (cuspidalShortCurve (ZMod 5)).toAffine.Point :=
      Nat.card_congr (Point.congr (congrArg WeierstrassCurve.toAffine hshort)).toEquiv
    _ = Fintype.card (cuspidalShortCurve (ZMod 5)).toAffine.Point :=
      Nat.card_eq_fintype_card
    _ = 5 := card_cuspidalShortCurve_five

/-- A Weierstrass cubic over `F₁₁` with vanishing discriminant and `c₄` has exactly eleven
nonsingular projective points. -/
theorem natCard_point_eq_eleven_of_cuspidal
    (W : WeierstrassCurve (ZMod 11)) (hΔ : W.Δ = 0) (hc₄ : W.c₄ = 0) :
    Nat.card W.toAffine.Point = 11 := by
  letI : Invertible (2 : ZMod 11) := invertibleOfNonzero (by decide)
  letI : Invertible (3 : ZMod 11) := invertibleOfNonzero (by decide)
  let C : WeierstrassCurve.VariableChange (ZMod 11) := W.toShortNF
  let Wshort : WeierstrassCurve (ZMod 11) := C • W
  haveI : Wshort.IsShortNF := by
    dsimp only [Wshort, C]
    infer_instance
  have hΔshort : Wshort.Δ = 0 := by
    change (C • W).Δ = 0
    rw [variableChange_Δ, hΔ, mul_zero]
  have hc₄short : Wshort.c₄ = 0 := by
    change (C • W).c₄ = 0
    rw [variableChange_c₄, hc₄, mul_zero]
  have hshort : Wshort = cuspidalShortCurve (ZMod 11) :=
    short_eq_cuspidal_eleven Wshort hΔshort hc₄short
  calc
    Nat.card W.toAffine.Point = Nat.card Wshort.toAffine.Point :=
      Nat.card_congr (Point.equivVariableChange W C).symm.toEquiv
    _ = Nat.card (cuspidalShortCurve (ZMod 11)).toAffine.Point :=
      Nat.card_congr (Point.congr (congrArg WeierstrassCurve.toAffine hshort)).toEquiv
    _ = Fintype.card (cuspidalShortCurve (ZMod 11)).toAffine.Point :=
      Nat.card_eq_fintype_card
    _ = 11 := card_cuspidalShortCurve_eleven

/-- The nonsingular point group of a cuspidal Weierstrass cubic over `F₅` is the additive group
of `F₅`. -/
noncomputable def pointAddEquivZModFiveOfCuspidal
    (W : WeierstrassCurve (ZMod 5)) (hΔ : W.Δ = 0) (hc₄ : W.c₄ = 0) :
    W.toAffine.Point ≃+ ZMod 5 := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact addEquivOfPrimeCardEq
    (natCard_point_eq_five_of_cuspidal W hΔ hc₄) (by norm_num)

/-- The nonsingular point group of a cuspidal Weierstrass cubic over `F₁₁` is the additive
group of `F₁₁`. -/
noncomputable def pointAddEquivZModElevenOfCuspidal
    (W : WeierstrassCurve (ZMod 11)) (hΔ : W.Δ = 0) (hc₄ : W.c₄ = 0) :
    W.toAffine.Point ≃+ ZMod 11 := by
  letI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact addEquivOfPrimeCardEq
    (natCard_point_eq_eleven_of_cuspidal W hΔ hc₄) (by norm_num)

local instance cuspidalDecidableEqResidueAtFive : DecidableEq
    (ResidueField (atFive.adicCompletionIntegers ℚ)) :=
  Classical.decEq _

local instance cuspidalDecidableEqResidueAtEleven : DecidableEq
    (ResidueField (atEleven.adicCompletionIntegers ℚ)) :=
  Classical.decEq _

/-- The nonsingular point group of the actual five-adic special fibre is the additive residue
field when its discriminant and `c₄` vanish. -/
noncomputable def specialFiberPointAddEquivAtFiveOfCuspidal
    (W₀ : WeierstrassCurve (atFive.adicCompletionIntegers ℚ))
    (hΔ : (adicRedCurve W₀).Δ = 0) (hc₄ : (adicRedCurve W₀).c₄ = 0) :
    (adicRedCurve W₀).Point ≃+
      ResidueField (atFive.adicCompletionIntegers ℚ) := by
  classical
  let e₅ : ResidueField (atFive.adicCompletionIntegers ℚ) ≃+* ZMod 5 :=
    (atFive.residueFieldEquivAdicCompletionIntegers (K := ℚ)).symm.trans
      residueFiveAlgEquiv.toRingEquiv
  letI : Algebra (atFive.adicCompletionIntegers ℚ) (ZMod 5) :=
    (e₅.toRingHom.comp
      (IsLocalRing.residue (atFive.adicCompletionIntegers ℚ))).toAlgebra
  let e₅Alg : ResidueField (atFive.adicCompletionIntegers ℚ) ≃ₐ[
      atFive.adicCompletionIntegers ℚ] ZMod 5 :=
    { e₅ with
      commutes' := fun _ ↦ rfl }
  let W₅ : WeierstrassCurve (ZMod 5) :=
    W₀.map (algebraMap (atFive.adicCompletionIntegers ℚ) (ZMod 5))
  let redPointEquiv : (adicRedCurve W₀).Point ≃+ W₅.toAffine.Point :=
    Point.mapEquiv (W' := W₀.toAffine) e₅Alg
  have hΔred :
      IsLocalRing.residue (atFive.adicCompletionIntegers ℚ) W₀.Δ = 0 := by
    simpa only [adicRedCurve, WeierstrassCurve.map_Δ] using hΔ
  have hc₄red :
      IsLocalRing.residue (atFive.adicCompletionIntegers ℚ) W₀.c₄ = 0 := by
    simpa only [adicRedCurve, WeierstrassCurve.map_c₄] using hc₄
  have hΔ₅ : W₅.Δ = 0 := by
    dsimp only [W₅]
    rw [WeierstrassCurve.map_Δ]
    change e₅ (IsLocalRing.residue (atFive.adicCompletionIntegers ℚ) W₀.Δ) = 0
    rw [hΔred, map_zero]
  have hc₄₅ : W₅.c₄ = 0 := by
    dsimp only [W₅]
    rw [WeierstrassCurve.map_c₄]
    change e₅ (IsLocalRing.residue (atFive.adicCompletionIntegers ℚ) W₀.c₄) = 0
    rw [hc₄red, map_zero]
  exact redPointEquiv.trans
    ((pointAddEquivZModFiveOfCuspidal W₅ hΔ₅ hc₄₅).trans e₅.toAddEquiv.symm)

/-- The analogous checked cuspidal classification for the actual eleven-adic special fibre. -/
noncomputable def specialFiberPointAddEquivAtElevenOfCuspidal
    (W₀ : WeierstrassCurve (atEleven.adicCompletionIntegers ℚ))
    (hΔ : (adicRedCurve W₀).Δ = 0) (hc₄ : (adicRedCurve W₀).c₄ = 0) :
    (adicRedCurve W₀).Point ≃+
      ResidueField (atEleven.adicCompletionIntegers ℚ) := by
  classical
  let e₁₁ : ResidueField (atEleven.adicCompletionIntegers ℚ) ≃+* ZMod 11 :=
    (atEleven.residueFieldEquivAdicCompletionIntegers (K := ℚ)).symm.trans
      residueElevenAlgEquiv.toRingEquiv
  letI : Algebra (atEleven.adicCompletionIntegers ℚ) (ZMod 11) :=
    (e₁₁.toRingHom.comp
      (IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ))).toAlgebra
  let e₁₁Alg : ResidueField (atEleven.adicCompletionIntegers ℚ) ≃ₐ[
      atEleven.adicCompletionIntegers ℚ] ZMod 11 :=
    { e₁₁ with
      commutes' := fun _ ↦ rfl }
  let W₁₁ : WeierstrassCurve (ZMod 11) :=
    W₀.map (algebraMap (atEleven.adicCompletionIntegers ℚ) (ZMod 11))
  let redPointEquiv : (adicRedCurve W₀).Point ≃+ W₁₁.toAffine.Point :=
    Point.mapEquiv (W' := W₀.toAffine) e₁₁Alg
  have hΔred :
      IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ) W₀.Δ = 0 := by
    simpa only [adicRedCurve, WeierstrassCurve.map_Δ] using hΔ
  have hc₄red :
      IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ) W₀.c₄ = 0 := by
    simpa only [adicRedCurve, WeierstrassCurve.map_c₄] using hc₄
  have hΔ₁₁ : W₁₁.Δ = 0 := by
    dsimp only [W₁₁]
    rw [WeierstrassCurve.map_Δ]
    change e₁₁ (IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ) W₀.Δ) = 0
    rw [hΔred, map_zero]
  have hc₄₁₁ : W₁₁.c₄ = 0 := by
    dsimp only [W₁₁]
    rw [WeierstrassCurve.map_c₄]
    change e₁₁ (IsLocalRing.residue (atEleven.adicCompletionIntegers ℚ) W₀.c₄) = 0
    rw [hc₄red, map_zero]
  exact redPointEquiv.trans
    ((pointAddEquivZModElevenOfCuspidal W₁₁ hΔ₁₁ hc₄₁₁).trans
      e₁₁.toAddEquiv.symm)

end MazurTorsion.EllipticCurve

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/

import MazurTorsion.ModularCurve.OrderThirtyFiveQuotientFormalImmersion
import MazurTorsion.ModularCurve.XZeroThirtyFiveCuspLocalRingAtEleven

/-!
# The explicit level-35 cusp local ring feeds Neron specialization

This file records the geometric comparison needed to use the checked
hyperelliptic quotient formula on a represented integral modular chart.  The
comparison identifies the actual local ring of the branch `(t,y) = (0,1)` in
characteristic eleven with the local ring selected by a represented affine
structural section.  It also identifies the geometric `q`-parameter and makes
the full local quotient-coordinate square commute.

The resulting arithmetic consumer derives the represented DVR structure, the
irreducibility of its `q`-parameter, the cleared quotient expansion, and
membership of the target parameter in its maximal ideal.  It then invokes the
existing q-expansion/formal-immersion/Neron chain.  In particular no formal
immersion, tangent nonvanishing, or quotient collision is an input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Ideal.Fiber
open MazurTorsion.ModularCurve.AffineCuspQExpansion

namespace MazurTorsion.ModularCurve.XZeroThirtyFiveLocalQuotientAtEleven

/-- Evaluation coordinates for the target cusp `(W,Z) = (1,3)`. -/
def targetCuspCoordinates : Fin 2 → ResidueField :=
  Fin.cases 1 (Fin.cases 3 Fin.elim0)

@[simp]
theorem targetCuspCoordinates_zero : targetCuspCoordinates 0 = 1 := rfl

@[simp]
theorem targetCuspCoordinates_one : targetCuspCoordinates 1 = 3 := rfl

/-- Evaluation of the ambient target polynomial ring at `(W,Z) = (1,3)`. -/
def targetCuspPolynomialEvaluation :
    MvPolynomial (Fin 2) ResidueField →+* ResidueField :=
  MvPolynomial.eval₂Hom (RingHom.id ResidueField) targetCuspCoordinates

/-- The selected target cusp lies on the checked elliptic quotient model. -/
theorem targetCuspPolynomialEvaluation_targetEquation :
    targetCuspPolynomialEvaluation targetEquation = 0 := by
  norm_num [targetCuspPolynomialEvaluation, targetCuspCoordinates,
    targetEquation, targetPolynomial]

/-- Evaluation at `(W,Z) = (1,3)` descends to the target coordinate ring. -/
def targetCuspRetraction : TargetCoordinateRing →+* ResidueField :=
  Ideal.Quotient.lift targetIdeal targetCuspPolynomialEvaluation (by
    intro P hP
    have hle : targetIdeal ≤ RingHom.ker targetCuspPolynomialEvaluation := by
      rw [targetIdeal, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
      exact targetCuspPolynomialEvaluation_targetEquation
    exact RingHom.mem_ker.mp (hle hP))

@[simp]
theorem targetCuspRetraction_targetW : targetCuspRetraction targetW = 1 := by
  simp [targetCuspRetraction, targetW, targetCuspPolynomialEvaluation]

@[simp]
theorem targetCuspRetraction_targetZ : targetCuspRetraction targetZ = 3 := by
  simp [targetCuspRetraction, targetZ, targetCuspPolynomialEvaluation]

/-- Target-cusp evaluation is onto the common explicit residue field. -/
theorem targetCuspRetraction_surjective :
    Function.Surjective targetCuspRetraction := by
  intro a
  refine ⟨Ideal.Quotient.mk targetIdeal (MvPolynomial.C a), ?_⟩
  simp [targetCuspRetraction, targetCuspPolynomialEvaluation]

/-- The actual cusp prime on the target elliptic chart. -/
def targetCuspPrime : Ideal TargetCoordinateRing :=
  RingHom.ker targetCuspRetraction

instance targetCuspPrime_isPrime : targetCuspPrime.IsPrime :=
  RingHom.ker_isPrime _

instance targetCuspPrime_isMaximal : targetCuspPrime.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective targetCuspRetraction
    targetCuspRetraction_surjective

/-- The actual local ring of the target cusp. -/
abbrev TargetCuspLocalRing := Localization.AtPrime targetCuspPrime

/-- The target local parameter `W-1`. -/
def targetParameter : TargetCuspLocalRing :=
  algebraMap TargetCoordinateRing TargetCuspLocalRing (targetW - 1)

/-- The explicit target parameter lies in the target cusp maximal ideal. -/
theorem targetParameter_mem_maximalIdeal :
    targetParameter ∈ IsLocalRing.maximalIdeal TargetCuspLocalRing := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  exact Ideal.mem_map_of_mem _ (by
    rw [targetCuspPrime, RingHom.mem_ker, map_sub, map_one,
      targetCuspRetraction_targetW, sub_self])

/-- The inverse quotient denominator evaluates to `-1` at the selected source
cusp. -/
theorem chartCuspRetraction_denominatorInverse :
    chartCuspRetraction denominatorInverse = -1 := by
  have hmul := congrArg chartCuspRetraction denominator_mul_inverse
  have hD : chartCuspRetraction D = -1 := by simp [D]
  have hmul' : chartCuspRetraction D *
      chartCuspRetraction denominatorInverse = 1 := by
    simpa only [map_mul, map_one] using hmul
  calc
    chartCuspRetraction denominatorInverse =
        -(chartCuspRetraction D *
          chartCuspRetraction denominatorInverse) := by rw [hD]; ring
    _ = -1 := by rw [hmul']

@[simp]
theorem chartCuspRetraction_quotientW :
    chartCuspRetraction quotientW = 1 := by
  simp [quotientW, chartCuspRetraction_denominatorInverse]

@[simp]
theorem chartCuspRetraction_quotientZ :
    chartCuspRetraction quotientZ = 3 := by
  norm_num [quotientZ, D, chartCuspRetraction_denominatorInverse]

/-- The explicit quotient map carries the source cusp to `(W,Z)=(1,3)`. -/
theorem chartCuspRetraction_comp_quotientCoordinateMap :
    chartCuspRetraction.comp quotientCoordinateMap = targetCuspRetraction := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [targetCuspRetraction, targetCuspPolynomialEvaluation,
      quotientCoordinateMap, targetEvaluation]
  · intro i
    fin_cases i
    · simp [targetW]
    · simp [targetZ]

/-- The target cusp prime is exactly the inverse image of the source cusp
prime under the explicit quotient map. -/
theorem targetCuspPrime_eq_comap_quotientCoordinateMap :
    targetCuspPrime = cuspPrime.comap quotientCoordinateMap := by
  ext a
  change targetCuspRetraction a = 0 ↔
    chartCuspRetraction (quotientCoordinateMap a) = 0
  rw [← RingHom.congr_fun chartCuspRetraction_comp_quotientCoordinateMap a]

/-- The local-ring map induced by the checked explicit quotient map. -/
def explicitLocalQuotientMap : TargetCuspLocalRing →+* CuspLocalRing :=
  Localization.localRingHom targetCuspPrime cuspPrime quotientCoordinateMap
    targetCuspPrime_eq_comap_quotientCoordinateMap

/-- The explicit local quotient map sends `W-1` to the localized checked
quotient parameter. -/
theorem explicitLocalQuotientMap_targetParameter :
    explicitLocalQuotientMap targetParameter =
      algebraMap SourceChart CuspLocalRing
        (quotientCoordinateMap (targetW - 1)) := by
  exact Localization.localRingHom_to_map targetCuspPrime cuspPrime
    quotientCoordinateMap targetCuspPrime_eq_comap_quotientCoordinateMap _

/-- The checked quotient identity in the actual source and target cusp local
rings. -/
theorem explicitLocalQuotientMap_targetParameter_cleared :
    explicitLocalQuotientMap targetParameter *
        (1 + qParameter - qParameter ^ 2) =
      algebraMap ResidueField CuspLocalRing (-7) * qParameter := by
  rw [explicitLocalQuotientMap_targetParameter]
  simpa only [map_mul, map_add, map_one, map_sub, map_pow, map_neg,
    map_ofNat, qParameter,
    IsScalarTower.algebraMap_apply ResidueField SourceChart CuspLocalRing] using
    congrArg (algebraMap SourceChart CuspLocalRing)
      quotientCoordinateMap_targetW_sub_one_cleared

end MazurTorsion.ModularCurve.XZeroThirtyFiveLocalQuotientAtEleven

namespace MazurTorsion.OrderThirtyFive

open MazurTorsion.EllipticCurve
open MazurTorsion.IntegerPrimeSpecialization
open MazurTorsion.ModularCurve
open WeierstrassCurve.Affine

namespace ExplicitChart

open MazurTorsion.ModularCurve.XZeroThirtyFiveLocalQuotientAtEleven

private abbrev ElevenBase := atEleven.adicCompletionIntegers ℚ

private abbrev ElevenPrime : Ideal ElevenBase :=
  affineCuspSpecialFiberIdealAtEleven

/-- The target local ring of the represented special-fibre map at the cusp. -/
private abbrev RepresentedTargetLocalRing
    {S T : Type*} [CommRing S] [CommRing T]
    [Algebra ElevenBase S] [Algebra ElevenBase T]
    (C : AffineStructuralSection (R := ElevenBase) (T := T))
    (g : S →ₐ[ElevenBase] T) :=
  Localization.AtPrime
    ((C.fiberPrime ElevenPrime).comap (Ideal.Fiber.map ElevenPrime g))

/-- A comparison between the checked hyperelliptic cusp germ and the local
ring of a represented affine structural section.

`quotientSquare` is an equality of local coordinate-ring maps, rather than an
equality only on the parameter `W - 1`. -/
structure LocalComparison
    {S T : Type*} [CommRing S] [CommRing T]
    [Algebra ElevenBase S] [Algebra ElevenBase T]
    (C : AffineStructuralSection (R := ElevenBase) (T := T))
    (g : S →ₐ[ElevenBase] T) where
  sourceLocalEquiv : CuspLocalRing ≃+* C.FiberLocalRing ElevenPrime
  targetLocalEquiv : TargetCuspLocalRing ≃+* RepresentedTargetLocalRing C g
  quotientSquare :
    sourceLocalEquiv.toRingHom.comp explicitLocalQuotientMap =
      (localizedMap ElevenPrime g (C.fiberPrime ElevenPrime)).toRingHom.comp
        targetLocalEquiv.toRingHom

namespace LocalComparison

variable
    {S T : Type*} [CommRing S] [CommRing T]
    [Algebra ElevenBase S] [Algebra ElevenBase T]
    {C : AffineStructuralSection (R := ElevenBase) (T := T)}
    {g : S →ₐ[ElevenBase] T}

/-- The represented q-parameter transported from the actual hyperelliptic
cusp local ring. -/
def representedQ (comparison : LocalComparison C g) :
    C.FiberLocalRing ElevenPrime :=
  comparison.sourceLocalEquiv qParameter

/-- The represented target parameter transported from the actual target cusp
local ring. -/
def sourceParameter (comparison : LocalComparison C g) :
    RepresentedTargetLocalRing C g :=
  comparison.targetLocalEquiv targetParameter

/-- Mapping the checked hyperelliptic identity through the local comparison
gives exactly the cleared formula expected by the represented q-expansion
consumer. -/
theorem clearedLocalFormula (comparison : LocalComparison C g) :
    localizedMap ElevenPrime g (C.fiberPrime ElevenPrime)
          comparison.sourceParameter *
        (1 + comparison.representedQ - comparison.representedQ ^ 2) =
      algebraMap ElevenPrime.ResidueField
          (C.FiberLocalRing ElevenPrime) (-7) * comparison.representedQ := by
  have h := congrArg comparison.sourceLocalEquiv
    explicitLocalQuotientMap_targetParameter_cleared
  have hsquare := RingHom.congr_fun comparison.quotientSquare
    targetParameter
  rw [map_mul, map_add, map_one, map_sub, map_pow] at h
  rw [hsquare] at h
  simpa only [representedQ, sourceParameter, map_neg, map_natCast] using h

/-- The represented target parameter lies in its maximal ideal, by transport
of `W-1` from the actual target cusp local ring. -/
theorem sourceParameter_mem_maximalIdeal
    (comparison : LocalComparison C g) :
    comparison.sourceParameter ∈
      IsLocalRing.maximalIdeal (RepresentedTargetLocalRing C g) := by
  letI : IsLocalHom comparison.targetLocalEquiv.toRingHom := inferInstance
  exact map_nonunit comparison.targetLocalEquiv.toRingHom targetParameter
    targetParameter_mem_maximalIdeal

end LocalComparison

/-- The actual level-35 hyperelliptic cusp comparison reaches the arithmetic
order-35 exclusion through the checked q-expansion, formal-immersion, and
Neron-specialization chain.

The only specialization hypotheses are the existing global Neron inputs.
Local Domain/DVR structure and irreducibility are transported from the actual
hyperelliptic cusp local ring through `comparison.sourceLocalEquiv`. -/
theorem rationalPoint_orderThirtyFive_ne_of_explicitCuspLocalComparison
    {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {A : CommGroupScheme (Spec (.of (atEleven.adicCompletion ℚ)))}
    (Ner : NeronModel ElevenBase (atEleven.adicCompletion ℚ) A)
    {S T : Type*} [CommRing S] [CommRing T]
    [Algebra ElevenBase S] [Algebra ElevenBase T]
    [IsNoetherianRing S] [IsNoetherianRing T]
    (C : AffineStructuralSection (R := ElevenBase) (T := T))
    (g : S →ₐ[ElevenBase] T)
    [IsNoetherianRing (ElevenPrime.Fiber T)]
    (comparison : LocalComparison C g)
    (targetOpen : Spec (.of S) ⟶ Ner.model.X.left)
    [IsOpenImmersion targetOpen]
    (quotientMap : sourceOver ElevenBase T ⟶ Ner.model.X)
    (hfactor :
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ targetOpen = quotientMap.left)
    (modularSection :
      Over.mk (𝟙 (Spec (.of ElevenBase))) ⟶ sourceOver ElevenBase T)
    (hgeneric_ne :
      fractionSpecMap ElevenBase (atEleven.adicCompletion ℚ) ≫
          modularSection.left ≠
        fractionSpecMap ElevenBase (atEleven.adicCompletion ℚ) ≫
          C.overSection.left)
    (hspecializes : ¬ atEleven.valuation ℚ E.j ≤ 1 →
      restrictBaseSection (residueSpecMap ElevenBase)
          (sourceOver ElevenBase T) modularSection =
        restrictBaseSection (residueSpecMap ElevenBase)
          (sourceOver ElevenBase T) C.overSection)
    (htorsion : IsOfFinOrder
      (Ner.basePointRestriction (modularSection ≫ quotientMap) /
        Ner.basePointRestriction (C.overSection ≫ quotientMap)))
    (hinjective : ∀ z :
        Over.mk (𝟙 (Spec (.of (atEleven.adicCompletion ℚ)))) ⟶ A.X,
      IsOfFinOrder z →
        Ner.basePointSpecialization (residueSpecMap ElevenBase) z = 1 →
        z = 1)
    (P : E.toAffine.Point) :
    addOrderOf P ≠ 35 := by
  letI : IsDomain (C.FiberLocalRing ElevenPrime) :=
    comparison.sourceLocalEquiv.symm.toMulEquiv.isDomain _
  letI : IsDiscreteValuationRing (C.FiberLocalRing ElevenPrime) :=
    comparison.sourceLocalEquiv.isDiscreteValuationRing
  have hq : Irreducible comparison.representedQ := by
    exact qParameter_irreducible.map comparison.sourceLocalEquiv.toMulEquiv
  exact
    rationalPoint_orderThirtyFive_ne_of_explicitQuotientQExpansionNeronSpecializationAtEleven
      Ner C g targetOpen quotientMap hfactor modularSection
      comparison.representedQ hq comparison.sourceParameter
      comparison.sourceParameter_mem_maximalIdeal
      comparison.clearedLocalFormula hgeneric_ne hspecializes htorsion
      hinjective P

end ExplicitChart

end MazurTorsion.OrderThirtyFive

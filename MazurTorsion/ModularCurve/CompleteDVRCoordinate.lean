/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.QExpansionFirstCoefficient
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.PowerSeries.Evaluation

/-!
# A power-series coordinate on a complete equicharacteristic DVR

Let `A` be a complete discrete valuation ring containing a field `K`.  If the image of `K`
surjects onto the residue field of `A` and `q` is a uniformizer, evaluation at `q` constructs an
isomorphism

`K⟦X⟧ ≃ A`.

The proof uses the adic topology only internally.  Evaluation is the continuous extension of
polynomial evaluation.  Its surjectivity follows from completeness and surjectivity modulo the
maximal ideal; its injectivity follows from the unit-times-a-power-of-`X` factorization in the DVR
`K⟦X⟧`.  Thus the resulting coordinate is constructed from coefficient-field and uniformizer
data, rather than assumed as an additional completed-stalk equivalence.

The final theorem in this file is a downstream consumer: it feeds the constructed coordinate into
the normalized first-`q`-coefficient formal-immersion criterion.
-/

namespace MazurTorsion.ModularCurve

open _root_.AlgebraicGeometry
open CategoryTheory
open Ideal

universe u

namespace CompleteDVRCoordinate

variable {K A : Type*} [Field K] [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A] [Algebra K A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- Continuous evaluation of `K⟦X⟧` at a uniformizer of a complete DVR.

The topologies are installed locally: `K` has the discrete topology and `A` its maximal-ideal-adic
topology.  Completeness of the latter is exactly the supplied `IsAdicComplete` instance. -/
noncomputable def powerSeriesEval (q : A) (hq : Irreducible q) : PowerSeries K →+* A := by
  letI : WithIdeal K := ⟨⊥⟩
  letI : WithIdeal A := ⟨IsLocalRing.maximalIdeal A⟩
  letI : DiscreteTopology K := is_bot_adic_iff.mp rfl
  let hcomplete : CompleteSpace A ∧ T2Space A :=
    (IsAdic.isAdicComplete_iff (I := IsLocalRing.maximalIdeal A) rfl).mp inferInstance
  letI : CompleteSpace A := hcomplete.1
  letI : T2Space A := hcomplete.2
  exact PowerSeries.eval₂Hom (φ := algebraMap K A) continuous_of_discreteTopology
    (WithIdeal.isTopologicallyNilpotent_of_mem
      (hq.maximalIdeal_eq.symm ▸ Ideal.mem_span_singleton_self q))

@[simp]
theorem powerSeriesEval_C (q : A) (hq : Irreducible q) (c : K) :
    powerSeriesEval (K := K) q hq (PowerSeries.C c) = algebraMap K A c := by
  simp [powerSeriesEval, PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_C]

@[simp]
theorem powerSeriesEval_X (q : A) (hq : Irreducible q) :
    powerSeriesEval (K := K) q hq (PowerSeries.X : PowerSeries K) = q := by
  simp [powerSeriesEval, PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_X]

/-- Evaluation at a uniformizer maps the `X`-adic ideal to the maximal ideal. -/
theorem map_span_X (q : A) (hq : Irreducible q) :
    (Ideal.span {(PowerSeries.X : PowerSeries K)}).map
        (powerSeriesEval (K := K) q hq) = IsLocalRing.maximalIdeal A := by
  rw [Ideal.map_span]
  simp [hq.maximalIdeal_eq]

/-- Coefficient-field surjectivity modulo the maximal ideal lifts to surjectivity of evaluation.

This is the completeness step: `surjective_of_mk_map_comp_surjective` successively lifts a residue
class through all adic powers and takes the limit in `A`. -/
theorem powerSeriesEval_surjective
    (q : A) (hq : Irreducible q)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)).comp (algebraMap K A))) :
    Function.Surjective (powerSeriesEval (K := K) q hq) := by
  let f := powerSeriesEval (K := K) q hq
  let I : Ideal (PowerSeries K) := Ideal.span {(PowerSeries.X : PowerSeries K)}
  have hmap : I.map f = IsLocalRing.maximalIdeal A := by
    simpa [I, f] using map_span_X (K := K) q hq
  letI : IsHausdorff (I.map f) A := hmap ▸ inferInstance
  apply surjective_of_mk_map_comp_surjective (I := I) f
  have hcoeff' : Function.Surjective
      ((Ideal.Quotient.mk (I.map f)).comp (algebraMap K A)) :=
    hmap.symm ▸ hcoeff
  intro y
  obtain ⟨c, hc⟩ := hcoeff' y
  exact ⟨PowerSeries.C c, by simpa [f] using hc⟩

/-- Evaluation at a nonzero uniformizer into a domain is injective. -/
theorem powerSeriesEval_injective (q : A) (hq : Irreducible q) :
    Function.Injective (powerSeriesEval (K := K) q hq) := by
  intro x y hxy
  rw [← sub_eq_zero]
  by_contra hsub
  obtain ⟨n, v, hv⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hsub
      (PowerSeries.X_irreducible (R := K))
  have hzero : powerSeriesEval (K := K) q hq (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  rw [hv, map_mul, map_pow, powerSeriesEval_X] at hzero
  exact (mul_ne_zero
    (IsUnit.ne_zero (IsUnit.map (powerSeriesEval (K := K) q hq) v.isUnit))
    (pow_ne_zero n hq.ne_zero)) hzero

/-- The power-series coordinate constructed from a coefficient field and a uniformizer of a
complete equicharacteristic DVR.  The orientation is the one used for completed stalks. -/
noncomputable def ringEquiv
    (q : A) (hq : Irreducible q)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)).comp (algebraMap K A))) :
    A ≃+* PowerSeries K :=
  (RingEquiv.ofBijective (powerSeriesEval (K := K) q hq)
    ⟨powerSeriesEval_injective (K := K) q hq,
      powerSeriesEval_surjective (K := K) q hq hcoeff⟩).symm

@[simp]
theorem ringEquiv_symm_apply
    (q : A) (hq : Irreducible q)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)).comp (algebraMap K A)))
    (F : PowerSeries K) :
    (ringEquiv q hq hcoeff).symm F = powerSeriesEval q hq F :=
  rfl

@[simp]
theorem ringEquiv_uniformizer
    (q : A) (hq : Irreducible q)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)).comp (algebraMap K A))) :
    ringEquiv q hq hcoeff q = (PowerSeries.X : PowerSeries K) := by
  apply (ringEquiv q hq hcoeff).symm.injective
  simp

@[simp]
theorem ringEquiv_algebraMap
    (q : A) (hq : Irreducible q)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)).comp (algebraMap K A)))
    (c : K) :
    ringEquiv q hq hcoeff (algebraMap K A c) = PowerSeries.C c := by
  apply (ringEquiv q hq hcoeff).symm.injective
  simp

end CompleteDVRCoordinate

namespace DegreeOneCotangentCertificate

variable {X Y : Scheme.{u}}

/-- A normalized expansion in a coefficient-field/uniformizer coordinate proves formal immersion.

Unlike `isFormalImmersionAt_of_smoothRelativeCurve_rationalPoint_of_normalizedQExpansion`, this
consumer does not take a completed-stalk equivalence as input.  It constructs that equivalence from
the complete-DVR structure, the coefficient field, and the chosen uniformizer. -/
theorem isFormalImmersionAt_of_completeDVR_normalizedQExpansion
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 π]
    (Y : Scheme.{u}) [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (g : Spec (.of K) ⟶ X)
    [IsIso (X.descResidueField (Scheme.stalkClosedPointTo g))]
    [IsIso (Y.descResidueField (Scheme.stalkClosedPointTo (g ≫ f)))]
    (hx : g (IsLocalRing.closedPoint K) ≠ genericPoint X)
    [IsDomain (Scheme.CompletedStalk X (g (IsLocalRing.closedPoint K)))]
    [IsDiscreteValuationRing (Scheme.CompletedStalk X (g (IsLocalRing.closedPoint K)))]
    [Algebra K (Scheme.CompletedStalk X (g (IsLocalRing.closedPoint K)))]
    [IsAdicComplete
      (IsLocalRing.maximalIdeal
        (Scheme.CompletedStalk X (g (IsLocalRing.closedPoint K))))
      (Scheme.CompletedStalk X (g (IsLocalRing.closedPoint K)))]
    (q : Scheme.CompletedStalk X (g (IsLocalRing.closedPoint K)))
    (hq : Irreducible q)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal
            (Scheme.CompletedStalk X (g (IsLocalRing.closedPoint K))))).comp
        (algebraMap K (Scheme.CompletedStalk X (g (IsLocalRing.closedPoint K))))))
    (a : IsLocalRing.maximalIdeal
      (Y.presheaf.stalk (f (g (IsLocalRing.closedPoint K)))))
    (c : K) (hc : c ≠ 0) (F : PowerSeries K)
    (hqExpansion :
      CompleteDVRCoordinate.ringEquiv q hq hcoeff
        (algebraMap
          (X.presheaf.stalk (g (IsLocalRing.closedPoint K)))
          (Scheme.CompletedStalk X (g (IsLocalRing.closedPoint K)))
          ((f.stalkMap (g (IsLocalRing.closedPoint K))).hom a)) =
        PowerSeries.C c * PowerSeries.X + PowerSeries.X ^ 2 * F) :
    AlgebraicGeometry.IsFormalImmersionAt f (g (IsLocalRing.closedPoint K)) := by
  exact isFormalImmersionAt_of_smoothRelativeCurve_rationalPoint_of_normalizedQExpansion
    K X π Y f g hx (CompleteDVRCoordinate.ringEquiv q hq hcoeff) a c hc F hqExpansion

/-- A normalized expansion in the constructed complete-DVR coordinate separates actual local
scheme points.  This is the collision endpoint of the coordinate construction: equality after
restriction to the quotient stalk, together with the first `q`-coefficient calculation, gives
equality of the canonical morphisms from a Noetherian local spectrum. -/
theorem specMap_fromStalk_eq_of_completeDVR_normalizedQExpansion
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 π]
    (Y : Scheme.{u}) [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (g : Spec (.of K) ⟶ X)
    [IsIso (X.descResidueField (Scheme.stalkClosedPointTo g))]
    [IsIso (Y.descResidueField (Scheme.stalkClosedPointTo (g ≫ f)))]
    (hx : g (IsLocalRing.closedPoint K) ≠ genericPoint X)
    [IsDomain (Scheme.CompletedStalk X (g (IsLocalRing.closedPoint K)))]
    [IsDiscreteValuationRing (Scheme.CompletedStalk X (g (IsLocalRing.closedPoint K)))]
    [Algebra K (Scheme.CompletedStalk X (g (IsLocalRing.closedPoint K)))]
    [IsAdicComplete
      (IsLocalRing.maximalIdeal
        (Scheme.CompletedStalk X (g (IsLocalRing.closedPoint K))))
      (Scheme.CompletedStalk X (g (IsLocalRing.closedPoint K)))]
    (q : Scheme.CompletedStalk X (g (IsLocalRing.closedPoint K)))
    (hq : Irreducible q)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal
            (Scheme.CompletedStalk X (g (IsLocalRing.closedPoint K))))).comp
        (algebraMap K (Scheme.CompletedStalk X (g (IsLocalRing.closedPoint K))))))
    (targetParameter : IsLocalRing.maximalIdeal
      (Y.presheaf.stalk (f (g (IsLocalRing.closedPoint K)))))
    (c : K) (hc : c ≠ 0) (F : PowerSeries K)
    (hqExpansion :
      CompleteDVRCoordinate.ringEquiv q hq hcoeff
        (algebraMap
          (X.presheaf.stalk (g (IsLocalRing.closedPoint K)))
          (Scheme.CompletedStalk X (g (IsLocalRing.closedPoint K)))
          ((f.stalkMap (g (IsLocalRing.closedPoint K))).hom targetParameter)) =
        PowerSeries.C c * PowerSeries.X + PowerSeries.X ^ 2 * F)
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (a b : X.presheaf.stalk (g (IsLocalRing.closedPoint K)) →+* R)
    [IsLocalHom a] [IsLocalHom b]
    (hrestrict :
      a.comp (f.stalkMap (g (IsLocalRing.closedPoint K))).hom =
        b.comp (f.stalkMap (g (IsLocalRing.closedPoint K))).hom) :
    Spec.map (CommRingCat.ofHom a) ≫
        X.fromSpecStalk (g (IsLocalRing.closedPoint K)) =
      Spec.map (CommRingCat.ofHom b) ≫
        X.fromSpecStalk (g (IsLocalRing.closedPoint K)) := by
  have hformal :=
    isFormalImmersionAt_of_completeDVR_normalizedQExpansion
      K X π Y f g hx q hq hcoeff targetParameter c hc F hqExpansion
  exact hformal.specMap_fromStalk_ext_of_isNoetherian a b hrestrict

end DegreeOneCotangentCertificate

end MazurTorsion.ModularCurve

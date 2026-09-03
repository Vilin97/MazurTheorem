/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Kubert.OrderTwentyFiveCanonicalHyperplaneLocal
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.OrderOfVanishing.Basic
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.ProductFormula.Smooth

/-!
# Local orders from the order-25 canonical cusp factors

For a local algebra over a field, the order of a section is the module
length of its principal quotient.  At a rational point the residue extension
has length one, so a finite-dimensional presentation of that quotient
computes the order as an ordinary vector-space dimension.

This file proves that bridge and applies it to the six cusp-labelled Artin
factors of the canonical coordinate hyperplanes.  The resulting theorems
give the exact local orders `1, 2, 3, 3, 1, 2`.  Their only geometric inputs
are a rational coefficient-field certificate and the corresponding
stalk-quotient algebra equivalence.  Constructing those equivalences from a
represented smooth canonical curve is the remaining boundary.
-/

noncomputable section

open Polynomial
open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.SchemeWeilDivisor

namespace MazurTorsion.Kubert

private theorem residueExtension_length_eq_one_of_coefficientField_surjective
    {K R : Type*} [Field K] [CommRing R] [IsLocalRing R]
    [Algebra K R] [IsLocalHom (algebraMap K R)]
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)).comp
        (algebraMap K R))) :
    Module.length (IsLocalRing.ResidueField K)
      (IsLocalRing.ResidueField R) = 1 := by
  have hresidue : Function.Surjective
      (algebraMap (IsLocalRing.ResidueField K)
        (IsLocalRing.ResidueField R)) := by
    intro y
    obtain ⟨k, hk⟩ := hcoeff y
    refine ⟨IsLocalRing.residue K k, ?_⟩
    rw [IsLocalRing.ResidueField.algebraMap_residue]
    exact hk
  rw [Module.length_eq_one_iff,
    isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective hresidue]
  infer_instance

/-- A finite-dimensional presentation of a principal quotient computes the
local order when the coefficient field surjects onto the residue field. -/
theorem ringOrd_eq_finrank_of_rationalLocalQuotient
    {K R A : Type*} [Field K] [CommRing R] [IsLocalRing R]
    [Algebra K R] [IsLocalHom (algebraMap K R)]
    [CommRing A] [Algebra K A] [Module.Finite K A]
    (s : R)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)).comp
        (algebraMap K R)))
    (e : (R ⧸ Ideal.span {s}) ≃ₐ[K] A) :
    Ring.ord R s = Module.finrank K A := by
  rw [Ring.ord]
  have hrestrict :=
    IsLocalRing.length_restrictScalars K R (R ⧸ Ideal.span {s})
  rw [residueExtension_length_eq_one_of_coefficientField_surjective hcoeff,
    mul_one] at hrestrict
  calc
    Module.length R (R ⧸ Ideal.span {s}) =
        Module.length K (R ⧸ Ideal.span {s}) := hrestrict.symm
    _ = Module.length K A := e.toLinearEquiv.length_eq
    _ = Module.finrank K A := Module.length_eq_finrank K A

/-- On a smooth integral curve, the same quotient presentation computes the
integer-valued scheme-theoretic order of the corresponding rational
function. -/
theorem orderAt_eq_finrank_of_rationalLocalQuotient
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    [Module.Finite K A]
    (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (x : CodimensionOnePoint X)
    [Algebra K (X.presheaf.stalk x.1)]
    [IsLocalHom (algebraMap K (X.presheaf.stalk x.1))]
    (a : X.presheaf.stalk x.1) (ha : a ≠ 0)
    (g : Additive X.functionFieldˣ)
    (hg : ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
      algebraMap (X.presheaf.stalk x.1) X.functionField a)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (X.presheaf.stalk x.1))).comp
        (algebraMap K (X.presheaf.stalk x.1))))
    (e : (X.presheaf.stalk x.1 ⧸ Ideal.span {a}) ≃ₐ[K] A) :
    orderAt x g = Module.finrank K A := by
  rw [orderAt_eq_ord_stalk_of_smoothRelativeDimension_one
    K X f x ha g hg]
  rw [ringOrd_eq_finrank_of_rationalLocalQuotient a hcoeff e]
  simp

/-! ## Exact orders of the six local factors -/

/-- The `w`-section has order one at canonical cusp 1 once its local
quotient is identified with the corresponding reduced factor. -/
theorem orderTwentyFiveCanonicalCuspOneW_ringOrd
    {K R : Type*} [Field K] [CommRing R] [IsLocalRing R]
    [Algebra K R] [IsLocalHom (algebraMap K R)]
    (w : R)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)).comp
        (algebraMap K R)))
    (e : (R ⧸ Ideal.span {w}) ≃ₐ[K]
      OrderTwentyFiveCanonicalCuspOneWFatRing K) :
    Ring.ord R w = 1 := by
  letI : Module.Finite K
      (OrderTwentyFiveCanonicalCuspOneWFatRing K) :=
    (monic_X_add_C (1 : K)).finite_adjoinRoot
  rw [ringOrd_eq_finrank_of_rationalLocalQuotient w hcoeff e]
  norm_num [(orderTwentyFiveCanonical_hyperplaneLocalFactorLengths
    (K := K)).1]

/-- The `w`-section has order two at canonical cusp 3. -/
theorem orderTwentyFiveCanonicalCuspThreeW_ringOrd
    {K R : Type*} [Field K] [CommRing R] [IsLocalRing R]
    [Algebra K R] [IsLocalHom (algebraMap K R)]
    (w : R)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)).comp
        (algebraMap K R)))
    (e : (R ⧸ Ideal.span {w}) ≃ₐ[K]
      OrderTwentyFiveCanonicalCuspThreeWFatRing K) :
    Ring.ord R w = 2 := by
  letI : Module.Finite K
      (OrderTwentyFiveCanonicalCuspThreeWFatRing K) :=
    (monic_X.pow 2).finite_adjoinRoot
  rw [ringOrd_eq_finrank_of_rationalLocalQuotient w hcoeff e]
  norm_num [(orderTwentyFiveCanonical_hyperplaneLocalFactorLengths
    (K := K)).2.1]

/-- The `w`-section has order three at canonical cusp 4. -/
theorem orderTwentyFiveCanonicalCuspFourW_ringOrd
    {K R : Type*} [Field K] [CommRing R] [IsLocalRing R]
    [Algebra K R] [IsLocalHom (algebraMap K R)]
    (w : R)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)).comp
        (algebraMap K R)))
    (e : (R ⧸ Ideal.span {w}) ≃ₐ[K]
      OrderTwentyFiveCanonicalCuspFourWFatRing K) :
    Ring.ord R w = 3 := by
  letI : Module.Finite K
      (OrderTwentyFiveCanonicalCuspFourWFatRing K) :=
    (monic_X.pow 3).finite_adjoinRoot
  rw [ringOrd_eq_finrank_of_rationalLocalQuotient w hcoeff e]
  norm_num [(orderTwentyFiveCanonical_hyperplaneLocalFactorLengths
    (K := K)).2.2.1]

/-- The `z`-section has order three at canonical cusp 0. -/
theorem orderTwentyFiveCanonicalCuspZeroZ_ringOrd
    {K R : Type*} [Field K] [CommRing R] [IsLocalRing R]
    [Algebra K R] [IsLocalHom (algebraMap K R)]
    (z : R)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)).comp
        (algebraMap K R)))
    (e : (R ⧸ Ideal.span {z}) ≃ₐ[K]
      OrderTwentyFiveCanonicalCuspZeroZFatRing K) :
    Ring.ord R z = 3 := by
  letI : Module.Finite K
      (OrderTwentyFiveCanonicalCuspZeroZFatRing K) :=
    (monic_X.pow 3).finite_adjoinRoot
  rw [ringOrd_eq_finrank_of_rationalLocalQuotient z hcoeff e]
  norm_num [(orderTwentyFiveCanonical_hyperplaneLocalFactorLengths
    (K := K)).2.2.2.1]

/-- The `z`-section has order one at canonical cusp 2. -/
theorem orderTwentyFiveCanonicalCuspTwoZ_ringOrd
    {K R : Type*} [Field K] [CommRing R] [IsLocalRing R]
    [Algebra K R] [IsLocalHom (algebraMap K R)]
    (z : R)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)).comp
        (algebraMap K R)))
    (e : (R ⧸ Ideal.span {z}) ≃ₐ[K]
      OrderTwentyFiveCanonicalCuspTwoZFatRing K) :
    Ring.ord R z = 1 := by
  letI : Module.Finite K
      (OrderTwentyFiveCanonicalCuspTwoZFatRing K) :=
    (monic_X_sub_C (1 : K)).finite_adjoinRoot
  rw [ringOrd_eq_finrank_of_rationalLocalQuotient z hcoeff e]
  norm_num [(orderTwentyFiveCanonical_hyperplaneLocalFactorLengths
    (K := K)).2.2.2.2.1]

/-- The `z`-section has order two at canonical cusp 4. -/
theorem orderTwentyFiveCanonicalCuspFourZ_ringOrd
    {K R : Type*} [Field K] [CommRing R] [IsLocalRing R]
    [Algebra K R] [IsLocalHom (algebraMap K R)]
    (z : R)
    (hcoeff : Function.Surjective
      ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)).comp
        (algebraMap K R)))
    (e : (R ⧸ Ideal.span {z}) ≃ₐ[K]
      OrderTwentyFiveCanonicalCuspFourZFatRing K) :
    Ring.ord R z = 2 := by
  letI : Module.Finite K
      (OrderTwentyFiveCanonicalCuspFourZFatRing K) :=
    (monic_X.pow 2).finite_adjoinRoot
  rw [ringOrd_eq_finrank_of_rationalLocalQuotient z hcoeff e]
  norm_num [(orderTwentyFiveCanonical_hyperplaneLocalFactorLengths
    (K := K)).2.2.2.2.2]

end MazurTorsion.Kubert

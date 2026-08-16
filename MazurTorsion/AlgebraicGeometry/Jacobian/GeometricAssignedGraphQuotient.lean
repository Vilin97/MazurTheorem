/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedRootCoordinates

/-!
# The graph quotient at an assigned geometric support

The coherent-support specialization of the universal split-component graph
ideal is not merely a collection of compatible individual equations.  Its
full quotient is canonically the product of the transported sheetwise monic
root algebras.  Consequently it is finite free of rank equal to the original
symmetric-power degree.

The named downstream consumer is `PointedIncidenceDescent`: after the
restricted curve-level incidence ideal is transported to this affine split
model, these results supply the finite-flat rank calculation needed for fpqc
descent.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedGraphQuotient

open FiniteEtaleCoproductPower
open FiniteSupportCoordinateMaps
open FiniteSupportEtaleCoordinates
open GeometricAssignedRootCoordinates
open GeometricSupportAssignedSplitChart
open SmoothCurveEtaleCoordinate
open SplitComponentGraphBaseChange
open SplitComponentGraphIdeal
open SplitFiniteBaseChange
open SplitFiniteSymmetricQuotient

variable (K : Type u) [Field K]
variable (C : Over (Spec (.of K))) [SmoothOfRelativeDimension 1 C.hom]
variable (d : ℕ)
variable (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
variable (V : (geometricDistinctCommonBase K C d z).left.Opens)
variable (T : Type u) [CommRing T] (q : Spec (.of T) ⟶ V.toScheme)
variable (r : Fin (geometricDistinctSupportCard K C d z) → ℕ)
variable
  (E : ∀ j, pullback
      (restrictedPulledComponentToBase K C
        (geometricDistinctSupportCard K C d z)
        (geometricDistinctSupportOrderedPoint K C d z)
        (geometricDistinctCharts K C d z)
        (geometricDistinctNeighborhoods K C d z) V j) q ≅
    Spec (.of (Fin (r j) → T)))
variable
  (hE : ∀ j, (E j).hom ≫ EtaleSplitChart.splitProjection T (r j) =
    pullback.snd
      (restrictedPulledComponentToBase K C
        (geometricDistinctSupportCard K C d z)
        (geometricDistinctSupportOrderedPoint K C d z)
        (geometricDistinctCharts K C d z)
        (geometricDistinctNeighborhoods K C d z) V j) q)
variable
  (w : (assignedComponentProductOverGround K C d z V
    (Spec (.of T)) q).left)

/-- The concrete evaluated graph product is definitionally the arbitrary
coefficient change of the universal split-component graph product. -/
theorem evaluatedOrderedGraphIdeal_eq_baseChangedOrderedGraphIdeal :
    evaluatedOrderedGraphIdeal K C d z V T q r E hE w =
      baseChangedOrderedGraphIdeal Γ(Spec (.of K), ⊤) d
        (sheetCount K C d z r)
        (selectedComponent K C d z V T q r E hE
          (productPoint K C d z V T q w))
        Γ(base K C d z V T q, ⊤)
        (rootCoordinateHom K C d z V T q r E hE w) := by
  exact
    (orderedAmbientCoordinateHom_map_orderedGraphIdeal
      K C d z V T q r E hE w).symm.trans
      (orderedAmbientBaseChangeHom_map_orderedGraphIdeal
        Γ(Spec (.of K), ⊤) d (sheetCount K C d z r)
        (selectedComponent K C d z V T q r E hE
          (productPoint K C d z V T q w))
        Γ(base K C d z V T q, ⊤)
        (rootCoordinateHom K C d z V T q r E hE w))

/-- The affine algebra cut out by the full evaluated graph product. -/
abbrev evaluatedGraphQuotientAlgebra : Type u :=
  evaluatedOrderedAmbientAlgebra K C d z V T q r ⧸
    evaluatedOrderedGraphIdeal K C d z V T q r E hE w

/-- The evaluated graph quotient is the product of the transported
sheetwise monic root algebras. -/
noncomputable def evaluatedGraphQuotientEquivProductRoot
    [Nontrivial Γ(base K C d z V T q, ⊤)] :
    evaluatedGraphQuotientAlgebra K C d z V T q r E hE w ≃ₐ[
      Γ(base K C d z V T q, ⊤)]
      baseChangedProductRootAlgebra Γ(Spec (.of K), ⊤) d
        (sheetCount K C d z r)
        (selectedComponent K C d z V T q r E hE
          (productPoint K C d z V T q w))
        Γ(base K C d z V T q, ⊤)
        (rootCoordinateHom K C d z V T q r E hE w) :=
  (Ideal.quotientEquivAlgOfEq Γ(base K C d z V T q, ⊤)
      (evaluatedOrderedGraphIdeal_eq_baseChangedOrderedGraphIdeal
        K C d z V T q r E hE w)).trans
    (baseChangedGraphQuotientEquivOrderedRoot
      Γ(Spec (.of K), ⊤) d (sheetCount K C d z r)
      (selectedComponent K C d z V T q r E hE
        (productPoint K C d z V T q w))
      Γ(base K C d z V T q, ⊤)
      (rootCoordinateHom K C d z V T q r E hE w))

/-- The evaluated graph quotient is a finite free module over the coherent
support base. -/
noncomputable instance evaluatedGraphQuotient_free
    [Nontrivial Γ(base K C d z V T q, ⊤)] :
    Module.Free Γ(base K C d z V T q, ⊤)
      (evaluatedGraphQuotientAlgebra K C d z V T q r E hE w) :=
  Module.Free.of_equiv
    (evaluatedGraphQuotientEquivProductRoot
      K C d z V T q r E hE w).symm.toLinearEquiv

noncomputable instance evaluatedGraphQuotient_finite
    [Nontrivial Γ(base K C d z V T q, ⊤)] :
    Module.Finite Γ(base K C d z V T q, ⊤)
      (evaluatedGraphQuotientAlgebra K C d z V T q r E hE w) :=
  Module.Finite.equiv
    (evaluatedGraphQuotientEquivProductRoot
      K C d z V T q r E hE w).symm.toLinearEquiv

/-- The evaluated graph-product quotient has total rank `d`. -/
theorem evaluatedGraphQuotient_finrank
    [Nontrivial Γ(base K C d z V T q, ⊤)] :
    Module.finrank Γ(base K C d z V T q, ⊤)
      (evaluatedGraphQuotientAlgebra K C d z V T q r E hE w) = d := by
  rw [(evaluatedGraphQuotientEquivProductRoot
    K C d z V T q r E hE w).toLinearEquiv.finrank_eq]
  exact finrank_pi_eq_degree Γ(base K C d z V T q, ⊤) d
    (sheetCount K C d z r)
    (selectedComponent K C d z V T q r E hE
      (productPoint K C d z V T q w))
    (fun j ↦ AdjoinRoot
      (baseChangedSheetPolynomial Γ(Spec (.of K), ⊤) d
        (sheetCount K C d z r)
        (selectedComponent K C d z V T q r E hE
          (productPoint K C d z V T q w))
        Γ(base K C d z V T q, ⊤)
        (rootCoordinateHom K C d z V T q r E hE w) j).1)
    (fun j ↦ SplitMonicRootFamily.rootAlgebra_finrank
      Γ(base K C d z V T q, ⊤) (sheetCount K C d z r)
      (sheetMultiplicity d (sheetCount K C d z r)
        (selectedComponent K C d z V T q r E hE
          (productPoint K C d z V T q w)))
      (baseChangedSheetPolynomial Γ(Spec (.of K), ⊤) d
        (sheetCount K C d z r)
        (selectedComponent K C d z V T q r E hE
          (productPoint K C d z V T q w))
        Γ(base K C d z V T q, ⊤)
      (rootCoordinateHom K C d z V T q r E hE w)) j)

/-- The affine graph quotient over the spectrum of the coherent base's
section ring. -/
noncomputable def evaluatedGraphSpecProjection
    [Nontrivial Γ(base K C d z V T q, ⊤)] :
    Spec (.of (evaluatedGraphQuotientAlgebra
      K C d z V T q r E hE w)) ⟶
      Spec (.of Γ(base K C d z V T q, ⊤)) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap Γ(base K C d z V T q, ⊤)
      (evaluatedGraphQuotientAlgebra K C d z V T q r E hE w)))

instance evaluatedGraphSpecProjection_isFinite
    [Nontrivial Γ(base K C d z V T q, ⊤)] :
    IsFinite (evaluatedGraphSpecProjection K C d z V T q r E hE w) := by
  rw [evaluatedGraphSpecProjection, IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr inferInstance

instance evaluatedGraphSpecProjection_flat
    [Nontrivial Γ(base K C d z V T q, ⊤)] :
    Flat (evaluatedGraphSpecProjection K C d z V T q r E hE w) := by
  rw [evaluatedGraphSpecProjection, Flat.SpecMap_iff]
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- The affine evaluated graph family has constant scheme-theoretic degree
`d` over the coherent base ring. -/
theorem evaluatedGraphSpecProjection_finrank
    [Nontrivial Γ(base K C d z V T q, ⊤)] :
    (evaluatedGraphSpecProjection K C d z V T q r E hE w).finrank =
      fun _ ↦ d := by
  rw [evaluatedGraphSpecProjection,
    Scheme.Hom.finrank_SpecMap_eq_finrank]
  · ext x
    change (algebraMap Γ(base K C d z V T q, ⊤)
      (evaluatedGraphQuotientAlgebra K C d z V T q r E hE w)).finrank x = d
    rw [RingHom.finrank_algebraMap]
    change Module.rankAtStalk
      (evaluatedGraphQuotientAlgebra K C d z V T q r E hE w) x = d
    rw [Module.rankAtStalk_eq_finrank_of_free]
    exact evaluatedGraphQuotient_finrank K C d z V T q r E hE w
  · exact RingHom.finite_algebraMap.mpr inferInstance
  · exact RingHom.flat_algebraMap_iff.mpr inferInstance

end MazurTorsion.AlgebraicGeometry.Jacobian.GeometricAssignedGraphQuotient

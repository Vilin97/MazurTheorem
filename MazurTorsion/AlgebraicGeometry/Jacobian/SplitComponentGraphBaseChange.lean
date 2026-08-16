/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.SplitComponentGraphIdeal

/-!
# Base change of split-component graph ideals

The ordered graph-product calculation is stable under an arbitrary change
of its root-coordinate coefficient ring.  For a ring map from the universal
ordered-root polynomial ring to a new coefficient ring, map each sheetwise
affine-line polynomial componentwise.  One universal graph ideal then maps
to the corresponding graph ideal with the transported root value, and the
entire finite product maps to the entire transported graph product.

No flatness is needed for this ideal equality.  The named downstream
consumer is `GeometricAssignedRootCoordinates`, where the ring map is first
the actual coherent-support specialization and later the coordinate map on
the dimension-preserving fpqc occurrence chart.
-/

noncomputable section

universe u v

namespace MazurTorsion.AlgebraicGeometry.Jacobian.SplitComponentGraphBaseChange

open _root_.AlgebraicGeometry
open AffineLineMonicCoordinates
open MonicRootFamily
open SplitComponentGraphIdeal
open SplitComponentMonicCoordinates
open SplitComponentUniversalRoot
open SplitFiniteSymmetricQuotient
open SplitMonicRootFamily

variable (R : Type u) [CommRing R] [Nontrivial R]
variable (d m : ℕ) (c : splitComponentIndex d m)
variable (B : Type v) [CommRing B]
variable (φ : coefficientRing R d m c →+* B)

/-- The product of the sheetwise affine-line polynomial rings after a
change of ordered-root coefficients. -/
abbrev baseChangedOrderedAmbientAlgebra :=
  ∀ _ : Fin m, Polynomial B

/-- Map every sheetwise affine-line polynomial componentwise along the
chosen root-coordinate homomorphism. -/
noncomputable def orderedAmbientBaseChangeHom :
    orderedAmbientAlgebra R d m c →+*
      baseChangedOrderedAmbientAlgebra m B :=
  RingHom.pi fun j ↦
    (Polynomial.mapRingHom φ).comp
      (Pi.evalRingHom
        (fun _ : Fin m ↦ Polynomial (coefficientRing R d m c)) j)

/-- The transported linear equation for one ordered root. -/
noncomputable def baseChangedRootLinearFactor
    (x : componentRootIndex d m c) : Polynomial B :=
  (rootLinearFactor R d m c x).map φ

/-- On one distinguished sheet, the base-changed graph ideal is generated
by the transported linear factor when the root belongs to that sheet and is
the unit ideal otherwise. -/
noncomputable def baseChangedRootGraphIdealOnSheet
    (x : componentRootIndex d m c) (j : Fin m) : Ideal (Polynomial B) :=
  if x.1 = j then Ideal.span {baseChangedRootLinearFactor R d m c B φ x}
  else ⊤

/-- One base-changed owner-sheet graph ideal in the product ambient ring. -/
noncomputable def baseChangedRootGraphIdeal
    (x : componentRootIndex d m c) :
    Ideal (baseChangedOrderedAmbientAlgebra m B) :=
  Ideal.pi (baseChangedRootGraphIdealOnSheet R d m c B φ x)

/-- The product of all base-changed ordered graph ideals. -/
noncomputable def baseChangedOrderedGraphIdeal :
    Ideal (baseChangedOrderedAmbientAlgebra m B) :=
  ∏ x : componentRootIndex d m c,
    baseChangedRootGraphIdeal R d m c B φ x

omit [Nontrivial R] in
/-- Componentwise coefficient change sends one universal owner-sheet graph
ideal to its transported graph ideal. -/
theorem orderedAmbientBaseChangeHom_map_rootGraphIdeal
    (x : componentRootIndex d m c) :
    Ideal.map (orderedAmbientBaseChangeHom R d m c B φ)
        (rootGraphIdeal R d m c x) =
      baseChangedRootGraphIdeal R d m c B φ x := by
  apply (Ideal.piOrderIso
    (R := fun _ : Fin m ↦ Polynomial B)).injective
  funext j
  change Ideal.map (Pi.evalRingHom _ j)
      (Ideal.map (orderedAmbientBaseChangeHom R d m c B φ)
        (rootGraphIdeal R d m c x)) =
    Ideal.map (Pi.evalRingHom _ j)
      (baseChangedRootGraphIdeal R d m c B φ x)
  rw [Ideal.map_map]
  change Ideal.map
      ((Polynomial.mapRingHom φ).comp
        (Pi.evalRingHom
          (fun _ : Fin m ↦ Polynomial (coefficientRing R d m c)) j))
      (rootGraphIdeal R d m c x) = _
  unfold rootGraphIdeal baseChangedRootGraphIdeal
  rw [Ideal.map_evalRingHom_pi]
  rw [← Ideal.map_map, Ideal.map_evalRingHom_pi]
  unfold rootGraphIdealOnSheet baseChangedRootGraphIdealOnSheet
  split_ifs
  · rw [Ideal.map_span]
    simp only [Set.image_singleton]
    rfl
  · exact Ideal.map_top _

private theorem ideal_map_fintype_prod {A D ι : Type*}
    [CommRing A] [CommRing D] [Fintype ι]
    (f : A →+* D) (I : ι → Ideal A) :
    Ideal.map f (∏ i, I i) = ∏ i, Ideal.map f (I i) := by
  let Φ : Ideal A →* Ideal D :=
    { toFun := Ideal.map f
      map_one' := by
        simpa only [Ideal.one_eq_top] using Ideal.map_top f
      map_mul' := fun J L ↦ Ideal.map_mul f J L }
  change Φ (∏ i, I i) = ∏ i, Φ (I i)
  exact map_prod Φ I Finset.univ

omit [Nontrivial R] in
/-- Arbitrary coefficient change preserves the full finite product of
ordered graph ideals, including repeated graph factors. -/
theorem orderedAmbientBaseChangeHom_map_orderedGraphIdeal :
    Ideal.map (orderedAmbientBaseChangeHom R d m c B φ)
        (orderedGraphIdeal R d m c) =
      baseChangedOrderedGraphIdeal R d m c B φ := by
  rw [orderedGraphIdeal, ideal_map_fintype_prod,
    baseChangedOrderedGraphIdeal]
  apply Fintype.prod_congr
  intro x
  exact orderedAmbientBaseChangeHom_map_rootGraphIdeal R d m c B φ x

/-- The ordered-root polynomial on one sheet, transported to the new
coefficient ring and packaged with its unchanged monic degree. -/
noncomputable def baseChangedSheetPolynomial [Nontrivial B] (j : Fin m) :
    Polynomial.MonicDegreeEq B (sheetMultiplicity d m c j) :=
  Polynomial.MonicDegreeEq.mk
    ((sheetOrderedRootPolynomial R d m c j).map φ)
    (by
      unfold sheetOrderedRootPolynomial
      exact (((orderedRootPolynomial_monic R
        (sheetMultiplicity d m c j)).map
          (sheetCoefficientHom R d m c j).toRingHom).map φ))
    (by
      unfold sheetOrderedRootPolynomial
      rw [((orderedRootPolynomial_monic R
          (sheetMultiplicity d m c j)).map
            (sheetCoefficientHom R d m c j).toRingHom).natDegree_map,
        (orderedRootPolynomial_monic R
          (sheetMultiplicity d m c j)).natDegree_map,
        orderedRootPolynomial_natDegree])

/-- The product of the base-changed sheetwise root algebras. -/
abbrev baseChangedProductRootAlgebra [Nontrivial B] :=
  productRootAlgebra B m (sheetMultiplicity d m c)
    (baseChangedSheetPolynomial R d m c B φ)

/-- The same transported graph product written sheetwise as the principal
ideal generated by each transported ordered-root polynomial. -/
noncomputable def baseChangedOrderedRootLocusIdeal [Nontrivial B] :
    Ideal (baseChangedOrderedAmbientAlgebra m B) :=
  Ideal.pi fun j ↦ Ideal.span
    {(baseChangedSheetPolynomial R d m c B φ j).1}

/-- The graph-product ideal after coefficient change is exactly the
sheetwise transported ordered-root ideal. -/
theorem baseChangedOrderedGraphIdeal_eq_orderedRootLocusIdeal
    [Nontrivial B] :
    baseChangedOrderedGraphIdeal R d m c B φ =
      baseChangedOrderedRootLocusIdeal R d m c B φ := by
  calc
    baseChangedOrderedGraphIdeal R d m c B φ =
        Ideal.map (orderedAmbientBaseChangeHom R d m c B φ)
          (orderedGraphIdeal R d m c) :=
      (orderedAmbientBaseChangeHom_map_orderedGraphIdeal
        R d m c B φ).symm
    _ = Ideal.map (orderedAmbientBaseChangeHom R d m c B φ)
        (orderedRootLocusIdeal R d m c) := by
      rw [orderedGraphIdeal_eq_orderedRootLocusIdeal]
    _ = baseChangedOrderedRootLocusIdeal R d m c B φ := by
      apply (Ideal.piOrderIso
        (R := fun _ : Fin m ↦ Polynomial B)).injective
      funext j
      change Ideal.map (Pi.evalRingHom _ j)
          (Ideal.map (orderedAmbientBaseChangeHom R d m c B φ)
            (Ideal.pi fun j ↦
              Ideal.span {sheetOrderedRootPolynomial R d m c j})) =
        Ideal.map (Pi.evalRingHom _ j)
          (Ideal.pi fun j ↦ Ideal.span
            {(baseChangedSheetPolynomial R d m c B φ j).1})
      rw [Ideal.map_evalRingHom_pi, Ideal.map_map]
      change Ideal.map
          ((Polynomial.mapRingHom φ).comp
            (Pi.evalRingHom
              (fun _ : Fin m ↦ Polynomial (coefficientRing R d m c)) j))
          (Ideal.pi fun j ↦
            Ideal.span {sheetOrderedRootPolynomial R d m c j}) = _
      rw [← Ideal.map_map, Ideal.map_evalRingHom_pi, Ideal.map_span]
      simp only [Set.image_singleton]
      rfl

/-- Evaluate the distinguished affine-line coordinate in every transported
sheetwise root algebra. -/
noncomputable def ambientToBaseChangedOrderedRoot [Nontrivial B] :
    baseChangedOrderedAmbientAlgebra m B →+*
      baseChangedProductRootAlgebra R d m c B φ :=
  RingHom.pi fun j ↦
    (ambientToRoot B
      (baseChangedSheetPolynomial R d m c B φ j).1).comp
      (Pi.evalRingHom (fun _ : Fin m ↦ Polynomial B) j)

/-- The kernel of simultaneous transported root evaluation is the
sheetwise transported root-locus ideal. -/
theorem ambientToBaseChangedOrderedRoot_ker [Nontrivial B] :
    RingHom.ker (ambientToBaseChangedOrderedRoot R d m c B φ) =
      baseChangedOrderedRootLocusIdeal R d m c B φ := by
  ext f
  change ambientToBaseChangedOrderedRoot R d m c B φ f = 0 ↔
    ∀ j, f j ∈ Ideal.span
      {(baseChangedSheetPolynomial R d m c B φ j).1}
  constructor
  · intro h j
    have hj := congrFun h j
    change ambientToRoot B
      (baseChangedSheetPolynomial R d m c B φ j).1 (f j) = 0 at hj
    rw [← ambientToRoot_ker]
    exact hj
  · intro h
    funext j
    change ambientToRoot B
      (baseChangedSheetPolynomial R d m c B φ j).1 (f j) = 0
    have hj : f j ∈ RingHom.ker
        (ambientToRoot B
          (baseChangedSheetPolynomial R d m c B φ j).1) := by
      rw [ambientToRoot_ker]
      exact h j
    exact hj

/-- Simultaneous transported sheetwise root evaluation is surjective. -/
theorem ambientToBaseChangedOrderedRoot_surjective [Nontrivial B] :
    Function.Surjective
      (ambientToBaseChangedOrderedRoot R d m c B φ) := by
  intro y
  let x : baseChangedOrderedAmbientAlgebra m B := fun j ↦
    Classical.choose (ambientToRoot_surjective B
      (baseChangedSheetPolynomial R d m c B φ j).1 (y j))
  refine ⟨x, ?_⟩
  funext j
  exact Classical.choose_spec (ambientToRoot_surjective B
    (baseChangedSheetPolynomial R d m c B φ j).1 (y j))

/-- The base-changed graph product is the exact kernel of simultaneous
transported sheetwise root evaluation. -/
theorem baseChangedOrderedGraphIdeal_eq_ker [Nontrivial B] :
    baseChangedOrderedGraphIdeal R d m c B φ =
      RingHom.ker (ambientToBaseChangedOrderedRoot R d m c B φ) :=
  (baseChangedOrderedGraphIdeal_eq_orderedRootLocusIdeal
    R d m c B φ).trans
      (ambientToBaseChangedOrderedRoot_ker R d m c B φ).symm

/-- The quotient algebra of the transported graph-product ideal. -/
abbrev baseChangedGraphQuotientAlgebra : Type v :=
  (baseChangedOrderedAmbientAlgebra m B) ⧸
    baseChangedOrderedGraphIdeal R d m c B φ

noncomputable local instance baseChangedProductRootAlgebraBaseAlgebra
    [Nontrivial B] :
    Algebra B (baseChangedProductRootAlgebra R d m c B φ) :=
  inferInstance

/-- Simultaneous transported root evaluation as a `B`-algebra map. -/
noncomputable def ambientToBaseChangedOrderedRootAlgHom [Nontrivial B] :
    baseChangedOrderedAmbientAlgebra m B →ₐ[B]
      baseChangedProductRootAlgebra R d m c B φ where
  toRingHom := ambientToBaseChangedOrderedRoot R d m c B φ
  commutes' b := by
    funext j
    change AdjoinRoot.mk
        (baseChangedSheetPolynomial R d m c B φ j).1
        (Polynomial.C b) =
      algebraMap B
        (AdjoinRoot (baseChangedSheetPolynomial R d m c B φ j).1) b
    rw [AdjoinRoot.mk_C]
    rfl

/-- The quotient by the transported graph product is the product of the
transported sheetwise monic root algebras. -/
noncomputable def baseChangedGraphQuotientEquivOrderedRoot [Nontrivial B] :
    baseChangedGraphQuotientAlgebra R d m c B φ ≃ₐ[B]
      baseChangedProductRootAlgebra R d m c B φ :=
  (Ideal.quotientEquivAlgOfEq B
      (baseChangedOrderedGraphIdeal_eq_ker R d m c B φ)).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := ambientToBaseChangedOrderedRootAlgHom R d m c B φ)
      (ambientToBaseChangedOrderedRoot_surjective R d m c B φ))

/-- The transported graph-product quotient is finite free over the new
coefficient ring, with total rank equal to the original symmetric degree. -/
theorem baseChangedGraphQuotient_finrank [Nontrivial B] :
    Module.finrank B (baseChangedGraphQuotientAlgebra R d m c B φ) = d := by
  rw [(baseChangedGraphQuotientEquivOrderedRoot
    R d m c B φ).toLinearEquiv.finrank_eq]
  exact finrank_pi_eq_degree B d m c
    (fun j ↦ AdjoinRoot
      (baseChangedSheetPolynomial R d m c B φ j).1)
    (fun j ↦ rootAlgebra_finrank B m (sheetMultiplicity d m c)
      (baseChangedSheetPolynomial R d m c B φ) j)

end MazurTorsion.AlgebraicGeometry.Jacobian.SplitComponentGraphBaseChange

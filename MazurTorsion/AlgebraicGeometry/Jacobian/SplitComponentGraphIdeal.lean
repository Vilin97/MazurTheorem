/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.SplitComponentOrderedIncidence
import MazurTorsion.AlgebraicGeometry.Jacobian.MonicRootFamily

/-!
# Graph ideals on a split symmetric-power component

On a fixed sheet-label component, the original ordered positions are
canonically reindexed by a dependent sum of the sheet fibers.  For one
distinguished split sheet, a coordinate graph contributes its linear root
factor when that coordinate belongs to the sheet and the unit ideal
otherwise.  This file proves that the product of all such graph ideals is
exactly the product-ring ideal cut out sheetwise by the ordered-root
polynomials.

This retains the scheme-theoretic multiplicities of repeated coordinates.
The named downstream consumer is the assigned split-chart comparison in
`PointedIncidenceDescent`.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.SplitComponentGraphIdeal

open AffineLineMonicCoordinates
open SplitComponentMonicCoordinates
open SplitComponentOrderedIncidence
open SplitComponentUniversalRoot
open SplitFiniteSymmetricQuotient
open MonicRootFamily

variable (R : Type u) [CommRing R] [Nontrivial R]
variable (d m : ℕ) (c : splitComponentIndex d m)

local instance : MulAction (Equiv.Perm (Fin d)) (Fin d → Fin m) :=
  tuplePermutationAction d (Fin m)

/-- Reindex the original ordered positions by their sheet and their canonical
finite-ordinal position inside that sheet fiber. -/
noncomputable def positionEquivRootIndex :
    Fin d ≃ componentRootIndex d m c :=
  (Equiv.sigmaFiberEquiv c.out).symm.trans
    (Equiv.sigmaCongrRight fun j ↦
      Fintype.equivFin { i : Fin d // c.out i = j })

/-- Reindexing an ordered position does not change its sheet label. -/
@[simp]
theorem positionEquivRootIndex_fst (i : Fin d) :
    (positionEquivRootIndex d m c i).1 = c.out i := by
  rfl

/-- A permutation witnessing that an arbitrary tuple belongs to the orbit
represented by `c`. -/
noncomputable def orbitRepresentativePermutation
    (a : Fin d → Fin m)
    (h : MulAction.orbitRel (Equiv.Perm (Fin d)) (Fin d → Fin m)
      c.out a) :
    Equiv.Perm (Fin d) :=
  Classical.choose (MulAction.mem_orbit_iff.mp h)

/-- The chosen orbit permutation sends the supplied tuple to the component's
stored representative. -/
theorem orbitRepresentativePermutation_smul
    (a : Fin d → Fin m)
    (h : MulAction.orbitRel (Equiv.Perm (Fin d)) (Fin d → Fin m)
      c.out a) :
    orbitRepresentativePermutation d m c a h • a = c.out :=
  Classical.choose_spec (MulAction.mem_orbit_iff.mp h)

/-- Reindex actual ordered positions by component roots using the
permutation that relates the actual sheet tuple to the component's chosen
orbit representative. -/
noncomputable def orbitAdaptedPositionEquivRootIndex
    (a : Fin d → Fin m)
    (h : MulAction.orbitRel (Equiv.Perm (Fin d)) (Fin d → Fin m)
      c.out a) :
    Fin d ≃ componentRootIndex d m c :=
  (orbitRepresentativePermutation d m c a h).trans
    (positionEquivRootIndex d m c)

/-- The sheet of an orbit-adapted root index is the actual sheet assigned to
the original ordered position, independently of the representative stored
in the quotient component. -/
@[simp]
theorem orbitAdaptedPositionEquivRootIndex_fst
    (a : Fin d → Fin m)
    (h : MulAction.orbitRel (Equiv.Perm (Fin d)) (Fin d → Fin m)
      c.out a) (i : Fin d) :
    (orbitAdaptedPositionEquivRootIndex d m c a h i).1 = a i := by
  rw [orbitAdaptedPositionEquivRootIndex, Equiv.trans_apply,
    positionEquivRootIndex_fst]
  have hpoint := congrFun
    (orbitRepresentativePermutation_smul d m c a h)
    (orbitRepresentativePermutation d m c a h i)
  change a ((orbitRepresentativePermutation d m c a h)⁻¹
      (orbitRepresentativePermutation d m c a h i)) =
    c.out (orbitRepresentativePermutation d m c a h i) at hpoint
  simpa using hpoint.symm

/-- The linear equation saying that the distinguished affine-line coordinate
equals one specified ordered root. -/
noncomputable def rootLinearFactor
    (x : componentRootIndex d m c) :
    Polynomial (coefficientRing R d m c) :=
  Polynomial.X - Polynomial.C (MvPolynomial.X x)

/-- On distinguished sheet `j`, one ordered root contributes its linear graph
ideal precisely when that root belongs to `j`; on every other sheet its graph
is absent and contributes the unit ideal. -/
noncomputable def rootGraphIdealOnSheet
    (x : componentRootIndex d m c) (j : Fin m) :
    Ideal (Polynomial (coefficientRing R d m c)) :=
  if x.1 = j then Ideal.span {rootLinearFactor R d m c x} else ⊤

/-- One ordered coordinate graph as an ideal in the product of the affine-line
coordinate rings of all distinguished split sheets. -/
noncomputable def rootGraphIdeal
    (x : componentRootIndex d m c) :
    Ideal (∀ _ : Fin m, Polynomial (coefficientRing R d m c)) :=
  Ideal.pi (rootGraphIdealOnSheet R d m c x)

/-- Select the sheet containing one ordered root and evaluate its affine-line
coordinate at that root.  Contravariantly, this is the graph of the root in
the coproduct of the distinguished-sheet affine lines. -/
noncomputable def rootGraphEvaluation
    (x : componentRootIndex d m c) :
    (∀ _ : Fin m, Polynomial (coefficientRing R d m c)) →+*
      coefficientRing R d m c :=
  (Polynomial.evalRingHom (MvPolynomial.X x)).comp
    (Pi.evalRingHom
      (fun _ : Fin m ↦ Polynomial (coefficientRing R d m c)) x.1)

omit [Nontrivial R] in
/-- The exact kernel of one owner-sheet root graph is its product-ring graph
ideal: the linear factor on the owner sheet and the unit ideal on every
other sheet. -/
theorem rootGraphEvaluation_ker
    (x : componentRootIndex d m c) :
    RingHom.ker (rootGraphEvaluation R d m c x) =
      rootGraphIdeal R d m c x := by
  ext f
  change Polynomial.evalRingHom (MvPolynomial.X x) (f x.1) = 0 ↔
    ∀ j, f j ∈ rootGraphIdealOnSheet R d m c x j
  constructor
  · intro h j
    by_cases hj : x.1 = j
    · subst j
      simpa only [rootGraphIdealOnSheet, if_pos,
        rootLinearFactor, ← Polynomial.ker_evalRingHom,
        RingHom.mem_ker] using h
    · simp [rootGraphIdealOnSheet, hj]
  · intro h
    have hx := h x.1
    simpa only [rootGraphIdealOnSheet, if_pos,
      rootLinearFactor, ← Polynomial.ker_evalRingHom,
      RingHom.mem_ker] using hx

omit [Nontrivial R] in
/-- Evaluation on one root graph is surjective because constant
polynomials lift every coefficient. -/
theorem rootGraphEvaluation_surjective
    (x : componentRootIndex d m c) :
    Function.Surjective (rootGraphEvaluation R d m c x) := by
  intro a
  refine ⟨fun _ ↦ Polynomial.C a, ?_⟩
  simp [rootGraphEvaluation]

/-- One ordered root graph as a closed subscheme of the coproduct of
distinguished-sheet affine lines. -/
noncomputable def rootGraphι
    (x : componentRootIndex d m c) :
    Spec (.of (coefficientRing R d m c)) ⟶
      Spec (.of (∀ _ : Fin m,
        Polynomial (coefficientRing R d m c))) :=
  Spec.map (CommRingCat.ofHom (rootGraphEvaluation R d m c x))

instance rootGraphι_isClosedImmersion
    (x : componentRootIndex d m c) :
    IsClosedImmersion (rootGraphι R d m c x) :=
  IsClosedImmersion.spec_of_surjective _
    (rootGraphEvaluation_surjective R d m c x)

/-- Embed coefficients as constant polynomials on every distinguished
sheet. -/
noncomputable def coefficientToOrderedAmbient :
    coefficientRing R d m c →+*
      (∀ _ : Fin m, Polynomial (coefficientRing R d m c)) :=
  RingHom.pi fun _ ↦ Polynomial.C

omit [Nontrivial R] in
/-- A root graph lies over the coefficient base. -/
theorem coefficientToOrderedAmbient_comp_rootGraphEvaluation
    (x : componentRootIndex d m c) :
    (rootGraphEvaluation R d m c x).comp
        (coefficientToOrderedAmbient R d m c) =
      RingHom.id (coefficientRing R d m c) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [rootGraphEvaluation, coefficientToOrderedAmbient]
  · intro a
    simp [rootGraphEvaluation, coefficientToOrderedAmbient]

/-- The structure morphism from the sheetwise affine-line coproduct to its
coefficient base. -/
noncomputable def orderedAmbientProjection :
    Spec (.of (∀ _ : Fin m,
      Polynomial (coefficientRing R d m c))) ⟶
        Spec (.of (coefficientRing R d m c)) :=
  Spec.map (CommRingCat.ofHom (coefficientToOrderedAmbient R d m c))

omit [Nontrivial R] in
/-- Scheme-theoretically, every owner-sheet root graph is a section of the
sheetwise ambient projection. -/
@[reassoc]
theorem rootGraphι_comp_orderedAmbientProjection
    (x : componentRootIndex d m c) :
    (rootGraphι R d m c x) ≫ (orderedAmbientProjection R d m c) =
      𝟙 (Spec (.of (coefficientRing R d m c))) := by
  rw [rootGraphι, orderedAmbientProjection, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp,
    coefficientToOrderedAmbient_comp_rootGraphEvaluation,
    CommRingCat.ofHom_id, Spec.map_id]

/-- The scheme-theoretic union of all ordered coordinate graphs on one split
component. -/
noncomputable def orderedGraphIdeal :
    Ideal (∀ _ : Fin m, Polynomial (coefficientRing R d m c)) :=
  ∏ x : componentRootIndex d m c, rootGraphIdeal R d m c x

/-- The same incidence ideal expressed directly by the sheetwise products of
ordered linear root factors. -/
noncomputable def orderedRootLocusIdeal :
    Ideal (∀ _ : Fin m, Polynomial (coefficientRing R d m c)) :=
  Ideal.pi (fun j ↦ Ideal.span {sheetOrderedRootPolynomial R d m c j})

/-- The product of the affine-line coordinate rings for the possible
distinguished split sheets. -/
abbrev orderedAmbientAlgebra :=
  ∀ _ : Fin m, Polynomial (coefficientRing R d m c)

/-- Evaluate the distinguished affine-line coordinate in every sheetwise
ordered-root algebra. -/
noncomputable def ambientToOrderedRoot :
    orderedAmbientAlgebra R d m c →+*
      orderedProductRootAlgebra R d m c :=
  RingHom.pi fun j ↦
    (ambientToRoot (coefficientRing R d m c)
      (sheetOrderedRootPolynomial R d m c j)).comp
        (Pi.evalRingHom
          (fun _ : Fin m ↦ Polynomial (coefficientRing R d m c)) j)

omit [Nontrivial R] in
/-- The kernel of simultaneous sheetwise root evaluation is exactly the
product-ring ideal generated by the ordered-root polynomial on each sheet. -/
theorem ambientToOrderedRoot_ker :
    RingHom.ker (ambientToOrderedRoot R d m c) =
      orderedRootLocusIdeal R d m c := by
  ext f
  change ambientToOrderedRoot R d m c f = 0 ↔
    ∀ j, f j ∈ Ideal.span {sheetOrderedRootPolynomial R d m c j}
  constructor
  · intro h j
    have hj := congrFun h j
    change ambientToRoot (coefficientRing R d m c)
      (sheetOrderedRootPolynomial R d m c j) (f j) = 0 at hj
    rw [← ambientToRoot_ker]
    exact hj
  · intro h
    funext j
    change ambientToRoot (coefficientRing R d m c)
      (sheetOrderedRootPolynomial R d m c j) (f j) = 0
    have hj : f j ∈ RingHom.ker
        (ambientToRoot (coefficientRing R d m c)
          (sheetOrderedRootPolynomial R d m c j)) := by
      rw [ambientToRoot_ker]
      exact h j
    exact hj

omit [Nontrivial R] in
/-- Simultaneous sheetwise root evaluation is surjective. -/
theorem ambientToOrderedRoot_surjective :
    Function.Surjective (ambientToOrderedRoot R d m c) := by
  intro y
  let x : orderedAmbientAlgebra R d m c := fun j ↦
    Classical.choose (ambientToRoot_surjective
      (coefficientRing R d m c)
      (sheetOrderedRootPolynomial R d m c j) (y j))
  refine ⟨x, ?_⟩
  funext j
  exact Classical.choose_spec (ambientToRoot_surjective
    (coefficientRing R d m c)
    (sheetOrderedRootPolynomial R d m c j) (y j))

/-- The affine ordered-root family embedded in the product of the
distinguished-sheet affine lines. -/
noncomputable def orderedRootLocusι :
    Spec (.of (orderedProductRootAlgebra R d m c)) ⟶
      Spec (.of (orderedAmbientAlgebra R d m c)) :=
  Spec.map (CommRingCat.ofHom (ambientToOrderedRoot R d m c))

instance orderedRootLocusι_isClosedImmersion :
    IsClosedImmersion (orderedRootLocusι R d m c) :=
  IsClosedImmersion.spec_of_surjective _
    (ambientToOrderedRoot_surjective R d m c)

omit [Nontrivial R] in
private theorem product_rootLinearFactor (j : Fin m) :
    ∏ i : Fin (sheetMultiplicity d m c j),
        rootLinearFactor R d m c ⟨j, i⟩ =
      sheetOrderedRootPolynomial R d m c j := by
  unfold rootLinearFactor sheetOrderedRootPolynomial
  unfold orderedRootPolynomial orderedRoots sheetCoefficientHom
  simp only [Polynomial.map_multiset_prod, Multiset.map_map,
    Function.comp_apply, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C]
  have hrename (i : Fin (sheetMultiplicity d m c j)) :
      (MvPolynomial.rename (R := R) (fun i ↦ (⟨j, i⟩ :
        componentRootIndex d m c))).toRingHom (MvPolynomial.X i) =
        MvPolynomial.X (⟨j, i⟩ : componentRootIndex d m c) := by
    exact MvPolynomial.rename_X _ _
  simp_rw [hrename]
  rfl

omit [Nontrivial R] in
/-- The product of the coordinate-graph ideals is exactly the sheetwise
ordered-root ideal.  In particular, repeated coordinates contribute repeated
linear factors rather than being reduced to one support component. -/
theorem orderedGraphIdeal_eq_orderedRootLocusIdeal :
    orderedGraphIdeal R d m c = orderedRootLocusIdeal R d m c := by
  classical
  apply (Ideal.piOrderIso
    (R := fun _ : Fin m ↦
      Polynomial (coefficientRing R d m c))).injective
  funext j
  let e := Pi.evalRingHom
    (fun _ : Fin m ↦ Polynomial (coefficientRing R d m c)) j
  let φ : Ideal (∀ _ : Fin m,
      Polynomial (coefficientRing R d m c)) →*
      Ideal (Polynomial (coefficientRing R d m c)) :=
    { toFun := Ideal.map e
      map_one' := by
        simpa only [Ideal.one_eq_top] using Ideal.map_top e
      map_mul' := fun I J ↦ Ideal.map_mul e I J }
  change φ (orderedGraphIdeal R d m c) =
    φ (orderedRootLocusIdeal R d m c)
  rw [orderedGraphIdeal, orderedRootLocusIdeal, map_prod]
  dsimp only [φ, e, rootGraphIdeal]
  change (∏ x : componentRootIndex d m c,
      Ideal.map (Pi.evalRingHom
        (fun _ : Fin m ↦ Polynomial (coefficientRing R d m c)) j)
        (Ideal.pi (rootGraphIdealOnSheet R d m c x))) =
    Ideal.map (Pi.evalRingHom
      (fun _ : Fin m ↦ Polynomial (coefficientRing R d m c)) j)
      (Ideal.pi fun j ↦
        Ideal.span {sheetOrderedRootPolynomial R d m c j})
  simp_rw [Ideal.map_evalRingHom_pi j]
  rw [Fintype.prod_sigma]
  rw [Fintype.prod_eq_single j]
  · simp only [rootGraphIdealOnSheet, if_pos]
    rw [Ideal.prod_span_singleton]
    exact congrArg (fun p ↦ Ideal.span {p})
      (product_rootLinearFactor R d m c j)
  · intro j' hj'
    simp [rootGraphIdealOnSheet, hj']

omit [Nontrivial R] in
/-- The graph-product incidence ideal is the exact kernel of the map to the
product of sheetwise ordered-root algebras. -/
theorem orderedGraphIdeal_eq_ker :
    orderedGraphIdeal R d m c =
      RingHom.ker (ambientToOrderedRoot R d m c) :=
  (orderedGraphIdeal_eq_orderedRootLocusIdeal R d m c).trans
    (ambientToOrderedRoot_ker R d m c).symm

end MazurTorsion.AlgebraicGeometry.Jacobian.SplitComponentGraphIdeal

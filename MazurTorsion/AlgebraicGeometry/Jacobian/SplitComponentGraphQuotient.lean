/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.SplitComponentGraphIdeal

/-!
# The graph-ideal quotient is the split ordered-root family

On a split symmetric-power component, the product of the coordinate-graph
ideals is the kernel of the simultaneous sheetwise root-evaluation map.
The first isomorphism theorem therefore identifies the quotient by the
actual graph-product ideal with the product of the sheetwise ordered-root
algebras.

The scheme-level isomorphism retains its compatibility with the two closed
immersions into the common sheetwise affine-line ambient space.  The named
downstream consumer is `SplitComponentInvariantRootComparison`, which then
transports this graph-defined incidence family to the finite-flat universal
block-monic root family.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.SplitComponentGraphQuotient

open SplitComponentGraphIdeal
open SplitComponentMonicCoordinates
open SplitComponentOrderedIncidence
open SplitComponentUniversalRoot
open SplitFiniteSymmetricQuotient

variable (R : Type u) [CommRing R] [Nontrivial R]
variable (d m : ℕ) (c : splitComponentIndex d m)

local instance : MulAction (Equiv.Perm (Fin d)) (Fin d → Fin m) :=
  tuplePermutationAction d (Fin m)

/-- The coordinate algebra of the incidence family defined by the actual
product of coordinate-graph ideals. -/
abbrev orderedGraphQuotientAlgebra : Type u :=
  (orderedAmbientAlgebra R d m c) ⧸ orderedGraphIdeal R d m c

noncomputable local instance orderedProductRootAlgebraBaseAlgebra :
    Algebra R (orderedProductRootAlgebra R d m c) :=
  Algebra.compHom _
    (algebraMap R (SplitComponentUniversalRoot.coefficientRing R d m c))

/-- Simultaneous sheetwise root evaluation as an `R`-algebra map. -/
noncomputable def ambientToOrderedRootAlgHom :
    orderedAmbientAlgebra R d m c →ₐ[R]
      orderedProductRootAlgebra R d m c where
  toRingHom := ambientToOrderedRoot R d m c
  commutes' r := by
    funext j
    change AdjoinRoot.mk
        (sheetOrderedRootPolynomial R d m c j)
        (Polynomial.C (MvPolynomial.C r)) =
      algebraMap (coefficientRing R d m c)
        (AdjoinRoot (sheetOrderedRootPolynomial R d m c j))
        (MvPolynomial.C r)
    rw [AdjoinRoot.mk_C]
    rfl

/-- The graph-ideal quotient is the product of the sheetwise ordered-root
algebras. -/
noncomputable def orderedGraphQuotientEquivOrderedRoot :
    orderedGraphQuotientAlgebra R d m c ≃ₐ[R]
      orderedProductRootAlgebra R d m c :=
  (Ideal.quotientEquivAlgOfEq R
      (orderedGraphIdeal_eq_ker R d m c)).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := ambientToOrderedRootAlgHom R d m c)
      (ambientToOrderedRoot_surjective R d m c))

/-- The graph-product incidence family as a closed subscheme of the
sheetwise affine-line ambient space. -/
noncomputable def orderedGraphLocusι :
    Spec (.of (orderedGraphQuotientAlgebra R d m c)) ⟶
      Spec (.of (orderedAmbientAlgebra R d m c)) :=
  Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (orderedGraphIdeal R d m c)))

instance orderedGraphLocusι_isClosedImmersion :
    IsClosedImmersion (orderedGraphLocusι R d m c) := by
  apply IsClosedImmersion.spec_of_surjective
  exact Ideal.Quotient.mk_surjective

/-- The graph-defined incidence family is canonically the ordered-root
family.  The orientation is chosen so that the isomorphism followed by the
graph closed immersion equals the ordered-root closed immersion. -/
noncomputable def orderedRootLocusIsoGraphLocus :
    Spec (.of (orderedProductRootAlgebra R d m c)) ≅
      Spec (.of (orderedGraphQuotientAlgebra R d m c)) where
  hom := Spec.map (CommRingCat.ofHom
    (orderedGraphQuotientEquivOrderedRoot R d m c).toRingHom)
  inv := Spec.map (CommRingCat.ofHom
    (orderedGraphQuotientEquivOrderedRoot R d m c).symm.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← Spec.map_id, Spec.map_inj]
    apply CommRingCat.hom_ext
    apply DFunLike.ext _ _
    intro x
    exact (orderedGraphQuotientEquivOrderedRoot R d m c).apply_symm_apply x
  inv_hom_id := by
    rw [← Spec.map_comp, ← Spec.map_id, Spec.map_inj]
    apply CommRingCat.hom_ext
    apply DFunLike.ext _ _
    intro x
    exact (orderedGraphQuotientEquivOrderedRoot R d m c).symm_apply_apply x

omit [Nontrivial R] in
/-- The first-isomorphism-theorem identification is compatible with the
closed immersions into the common ambient affine scheme. -/
@[reassoc]
theorem orderedRootLocusIsoGraphLocus_hom_comp_ι :
    (orderedRootLocusIsoGraphLocus R d m c).hom ≫
        orderedGraphLocusι R d m c =
      orderedRootLocusι R d m c := by
  rw [orderedRootLocusIsoGraphLocus, orderedGraphLocusι,
    orderedRootLocusι, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact Ideal.quotientKerAlgEquivOfSurjective_mk
    (f := ambientToOrderedRootAlgHom R d m c)
    (ambientToOrderedRoot_surjective R d m c) x

end MazurTorsion.AlgebraicGeometry.Jacobian.SplitComponentGraphQuotient

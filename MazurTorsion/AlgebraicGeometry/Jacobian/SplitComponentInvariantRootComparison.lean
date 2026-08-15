/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.SplitComponentOrderedIncidence

/-!
# Comparing invariant and free-monic split root families

The residual-stabilizer fixed coefficient ring is canonically equivalent to
the free-monic coefficient ring used by `SplitComponentUniversalRoot`.  Map
each sheetwise root algebra through that coefficient equivalence, take their
finite product, and record the resulting commutative square on spectra.

This identifies the finite-flat rank-`d` root family obtained from incidence
invariants with the previously constructed split-component universal root
family.  The named downstream consumer is the fpqc local comparison in
`PointedIncidenceDescent`.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.SplitComponentInvariantRootComparison

open SplitComponentOrderedIncidence
open SplitComponentUniversalRoot
open SplitFiniteSymmetricQuotient
open SplitMonicRootFamily
open SplitSymmetricQuotientChart

variable (R : Type u) [CommRing R] [Nontrivial R]
variable (d m : ℕ) (c : splitComponentIndex d m)

local instance : MulAction (Equiv.Perm (Fin d)) (Fin d → Fin m) :=
  tuplePermutationAction d (Fin m)

local instance : MulSemiringAction (componentStabilizer d m c)
    (coefficientRing R d m c) :=
  componentStabilizerRootAction R d m c

local instance : SMulCommClass (componentStabilizer d m c) R
    (coefficientRing R d m c) :=
  componentStabilizerRootSMulCommClass R d m c

/-- One sheetwise root algebra transported from free-monic coefficients to
the actual stabilizer fixed coefficient ring. -/
noncomputable def sheetRootAlgEquiv (j : Fin m) :
    AdjoinRoot (sheetPolynomial R d m c j).1 ≃ₐ[R]
      AdjoinRoot (invariantSheetPolynomial R d m c j).1 := by
  exact AdjoinRoot.mapAlgEquiv
    (componentStabilizerInvariantAlgEquiv R d m c)
    (sheetPolynomial R d m c j).1
    (invariantSheetPolynomial R d m c j).1
    (Associated.of_eq rfl)

/-- Product of the free-monic root algebras on a split component. -/
noncomputable abbrev coefficientProductRootAlgebra :=
  productRootAlgebra (coefficientRing R d m c) m
    (sheetMultiplicity d m c) (sheetPolynomial R d m c)

/-- Simultaneous coefficient change on every sheetwise root algebra. -/
noncomputable def componentProductRootAlgEquiv :
    coefficientProductRootAlgebra R d m c ≃ₐ[R]
      invariantProductRootAlgebra R d m c :=
  AlgEquiv.piCongrRight fun j ↦ sheetRootAlgEquiv R d m c j

omit [Nontrivial R] in
/-- The product root equivalence maps base coefficients through the
stabilizer-invariant coefficient equivalence. -/
theorem componentProductRootAlgEquiv_algebraMap
    (b : coefficientRing R d m c) :
    componentProductRootAlgEquiv R d m c
        (algebraMap (coefficientRing R d m c)
          (coefficientProductRootAlgebra R d m c) b) =
      algebraMap (invariantCoefficientRing R d m c)
        (invariantProductRootAlgebra R d m c)
        (componentStabilizerInvariantAlgEquiv R d m c b) := by
  ext j
  change sheetRootAlgEquiv R d m c j
      (algebraMap (coefficientRing R d m c)
        (AdjoinRoot (sheetPolynomial R d m c j).1) b) =
    algebraMap (invariantCoefficientRing R d m c)
      (AdjoinRoot (invariantSheetPolynomial R d m c j).1)
      (componentStabilizerInvariantAlgEquiv R d m c b)
  simp [sheetRootAlgEquiv]

/-- The invariant and free-monic product root schemes are canonically
isomorphic. -/
noncomputable def componentProductRootSchemeIso :
    Spec (.of (invariantProductRootAlgebra R d m c)) ≅
      Spec (.of (coefficientProductRootAlgebra R d m c)) where
  hom := Spec.map (CommRingCat.ofHom
    (componentProductRootAlgEquiv R d m c).toRingHom)
  inv := Spec.map (CommRingCat.ofHom
    (componentProductRootAlgEquiv R d m c).symm.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← Spec.map_id, Spec.map_inj]
    exact (componentProductRootAlgEquiv R d m c).toRingEquiv.toCommRingCatIso.inv_hom_id
  inv_hom_id := by
    rw [← Spec.map_comp, ← Spec.map_id, Spec.map_inj]
    exact (componentProductRootAlgEquiv R d m c).toRingEquiv.toCommRingCatIso.hom_inv_id

/-- The fixed and free-monic coefficient schemes are canonically
isomorphic. -/
noncomputable def componentCoefficientSchemeIso :
    Spec (.of (invariantCoefficientRing R d m c)) ≅
      Spec (.of (coefficientRing R d m c)) where
  hom := Spec.map (CommRingCat.ofHom
    (componentStabilizerInvariantAlgEquiv R d m c).toRingHom)
  inv := Spec.map (CommRingCat.ofHom
    (componentStabilizerInvariantAlgEquiv R d m c).symm.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← Spec.map_id, Spec.map_inj]
    exact (componentStabilizerInvariantAlgEquiv R d m c).toRingEquiv.toCommRingCatIso.inv_hom_id
  inv_hom_id := by
    rw [← Spec.map_comp, ← Spec.map_id, Spec.map_inj]
    exact (componentStabilizerInvariantAlgEquiv R d m c).toRingEquiv.toCommRingCatIso.hom_inv_id

omit [Nontrivial R] in
/-- The product root scheme equivalence lies over the corresponding
coefficient scheme equivalence. -/
theorem componentProductRootSchemeIso_hom_comp_projection :
    (componentProductRootSchemeIso R d m c).hom ≫
        SplitComponentUniversalRoot.projection R d m c =
      invariantRootProjection R d m c ≫
        (componentCoefficientSchemeIso R d m c).hom := by
  simp only [componentProductRootSchemeIso, componentCoefficientSchemeIso,
    SplitComponentUniversalRoot.projection, invariantRootProjection,
    SplitMonicRootFamily.projection]
  rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj]
  apply CommRingCat.hom_ext
  apply RingHom.ext fun b ↦ ?_
  ext j
  exact congrFun (componentProductRootAlgEquiv_algebraMap R d m c b) j

end MazurTorsion.AlgebraicGeometry.Jacobian.SplitComponentInvariantRootComparison

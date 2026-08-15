/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.RingTheory.AdjoinRoot
import MazurTorsion.AlgebraicGeometry.Jacobian.SplitFiniteSymmetricQuotient

/-!
# Root families on a split symmetric-power component

Over a common affine base, take one monic polynomial for every sheet of a
split finite étale chart.  The disjoint union of their root schemes has
coordinate ring the finite product of the corresponding `AdjoinRoot`
algebras.  This product is finite free, and its rank is the sum of the
degrees of the sheet polynomials.

When those degrees are the sheet multiplicities of a component from
`SplitFiniteSymmetricQuotient`, the total rank is the symmetric-power
degree.  The named downstream consumer is the fpqc local calculation for
the pointed universal effective divisor in `PointedIncidenceDescent`.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.SplitMonicRootFamily

variable (B : Type u) [CommRing B] [Nontrivial B]
variable (m : ℕ) (k : Fin m → ℕ)
variable (p : ∀ j, Polynomial.MonicDegreeEq B (k j))

/-- The root algebra of the monic polynomial on one sheet. -/
abbrev rootAlgebra (j : Fin m) := AdjoinRoot (p j).1

/-- The coordinate ring of the disjoint union of all sheetwise root
families. -/
abbrev productRootAlgebra := ∀ j, rootAlgebra B m k p j

noncomputable instance rootAlgebra_free (j : Fin m) :
    Module.Free B (rootAlgebra B m k p j) :=
  (p j).monic.free_adjoinRoot

noncomputable instance rootAlgebra_finite (j : Fin m) :
    Module.Finite B (rootAlgebra B m k p j) :=
  (p j).monic.finite_adjoinRoot

noncomputable instance productRootAlgebra_free :
    Module.Free B (productRootAlgebra B m k p) :=
  Module.Free.pi B _

noncomputable instance productRootAlgebra_finite :
    Module.Finite B (productRootAlgebra B m k p) := by
  infer_instance

noncomputable instance productRootAlgebra_flat :
    Module.Flat B (productRootAlgebra B m k p) := by
  infer_instance

/-- One sheetwise root algebra has rank equal to the degree of its monic
polynomial, including degree zero. -/
theorem rootAlgebra_finrank (j : Fin m) :
    Module.finrank B (rootAlgebra B m k p j) = k j := by
  simpa [rootAlgebra, (p j).natDegree] using
    (AdjoinRoot.powerBasis' (p j).monic).finrank

/-- The product root algebra has rank the sum of the sheet degrees. -/
theorem productRootAlgebra_finrank :
    Module.finrank B (productRootAlgebra B m k p) = ∑ j, k j := by
  rw [Module.finrank_pi_fintype]
  exact Finset.sum_congr rfl (fun j _ ↦ rootAlgebra_finrank B m k p j)

/-- The affine projection of the union of the sheetwise root families. -/
noncomputable def projection :
    Spec (.of (productRootAlgebra B m k p)) ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap B (productRootAlgebra B m k p)))

instance projection_isFinite : IsFinite (projection B m k p) := by
  rw [projection, IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr inferInstance

instance projection_flat : Flat (projection B m k p) := by
  rw [projection, Flat.SpecMap_iff]
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- The affine union of root families has constant rank equal to the sum
of the sheet degrees. -/
theorem projection_finrank :
    (projection B m k p).finrank = fun _ ↦ ∑ j, k j := by
  rw [projection, Scheme.Hom.finrank_SpecMap_eq_finrank]
  · ext x
    change (algebraMap B (productRootAlgebra B m k p)).finrank x = ∑ j, k j
    rw [RingHom.finrank_algebraMap]
    change Module.rankAtStalk (productRootAlgebra B m k p) x = ∑ j, k j
    rw [Module.rankAtStalk_eq_finrank_of_free]
    exact productRootAlgebra_finrank B m k p
  · exact RingHom.finite_algebraMap.mpr inferInstance
  · exact RingHom.flat_algebraMap_iff.mpr inferInstance

open SplitFiniteSymmetricQuotient in
/-- On a component of a split degree-`d` symmetric power, the product of
monic root families with the component's sheet degrees has rank `d`. -/
theorem projection_finrank_of_sheetMultiplicity
    (d : ℕ) (c : splitComponentIndex d m)
    (p : ∀ j, Polynomial.MonicDegreeEq B
      (sheetMultiplicity d m c j)) :
    (projection B m (sheetMultiplicity d m c) p).finrank = fun _ ↦ d := by
  rw [projection_finrank]
  exact congrArg (fun n ↦ fun _ ↦ n) (sum_sheetMultiplicity d m c)

end MazurTorsion.AlgebraicGeometry.Jacobian.SplitMonicRootFamily

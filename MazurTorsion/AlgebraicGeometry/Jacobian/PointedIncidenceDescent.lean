/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.PointedIncidence
import MazurTorsion.AlgebraicGeometry.Jacobian.UniversalEffectiveDivisorDescent

/-!
# The pointed symmetric power maps to the incidence quotient

For a challenge curve, insertion of the distinguished point is equivariant
for permutations of the remaining ordered coordinates.  It therefore
descends from `C × C^(n+1)` to `C × Sym^(n+1)(C)` and lands in the quotient
of the degree-`n + 2` ordered incidence family.

This produces the canonical comparison whose expected isomorphism identifies
the universal effective divisor with `C × Sym^(n+1)(C)`.  The named
downstream consumer is `PicardRepresentability`; after the local monic-chart
comparison proves this morphism is an isomorphism, finite flatness, rank, and
the Cartier equation follow from the pointed symmetric-power presentation.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.PointedIncidenceDescent

open FiniteGroupQuotient
open UniversalEffectiveDivisor

variable (K : Type u) [Field K]
variable (C : Over (Spec (.of K)))
variable [GeometricallyIrreducible C.hom] [IsProper C.hom]
variable [SmoothOfRelativeDimension 1 C.hom]

/-- Ordered insertion followed by the quotient of the larger incidence
family. -/
noncomputable def orderedPointedToIncidenceQuotient (n : ℕ) :
    (orderedAmbient (Spec (.of K)) (n + 1) C).left ⟶
      curveOrderedIncidenceQuotientSucc K C (n + 1) :=
  PointedIncidence.orderedPointedIncidenceMap
      (Spec (.of K)) (n + 1) C ≫
    curveOrderedIncidenceQuotientProjectionSucc K C (n + 1)

/-- Ordered pointed addition is invariant under permutations of the
remaining coordinates after passing to the incidence quotient. -/
theorem orderedPointedToIncidenceQuotient_invariant
    (n : ℕ) (g : Equiv.Perm (Fin (n + 1))) :
    (orderedAmbientAction (Spec (.of K)) (n + 1) C).hom g ≫
        orderedPointedToIncidenceQuotient K C n =
      orderedPointedToIncidenceQuotient K C n := by
  rw [orderedPointedToIncidenceQuotient, ← Category.assoc,
    PointedIncidence.orderedAmbientAction_comp_orderedPointedIncidenceMap,
    Category.assoc]
  exact congrArg
    (fun q ↦ PointedIncidence.orderedPointedIncidenceMap
      (Spec (.of K)) (n + 1) C ≫ q)
    (FiniteGroupQuotient.hom_quotientπ
      (orderedIncidenceAction (Spec (.of K)) (n + 2) C)
      (curveOrderedIncidence_hasAffineOrbit_succ K C (n + 1))
      (PointedIncidence.fixZeroPermutation (n + 1) g))

/-- Descent of pointed addition from the ambient quotient to the larger
incidence quotient. -/
noncomputable def ambientQuotientToIncidenceQuotientPointed (n : ℕ) :
    curveOrderedAmbientQuotientSucc K C n ⟶
      curveOrderedIncidenceQuotientSucc K C (n + 1) :=
  FiniteGroupQuotient.descendedMap
    (orderedAmbientAction (Spec (.of K)) (n + 1) C)
    (curveOrderedAmbient_hasAffineOrbit_succ K C n)
    (orderedPointedToIncidenceQuotient K C n)
    (orderedPointedToIncidenceQuotient_invariant K C n)

@[reassoc]
theorem curveOrderedAmbientQuotientProjection_comp_pointedDescent
    (n : ℕ) :
    curveOrderedAmbientQuotientProjectionSucc K C n ≫
        ambientQuotientToIncidenceQuotientPointed K C n =
      orderedPointedToIncidenceQuotient K C n :=
  FiniteGroupQuotient.quotientπ_comp_descendedMap
    (orderedAmbientAction (Spec (.of K)) (n + 1) C)
    (curveOrderedAmbient_hasAffineOrbit_succ K C n)
    (orderedPointedToIncidenceQuotient K C n)
    (orderedPointedToIncidenceQuotient_invariant K C n)

/-- The pointed symmetric-power comparison
`C × Sym^(n+1)(C) ⟶ D_(n+2)`. -/
noncomputable def productSymmetricPowerToIncidenceQuotient (n : ℕ) :
    (C ⨯ SymmetricPower.curveSchemeSucc K C n).left ⟶
      curveOrderedIncidenceQuotientSucc K C (n + 1) :=
  (curveAmbientQuotientSymmetricProductIso K C n).inv ≫
    ambientQuotientToIncidenceQuotientPointed K C n

/-- Pulling the pointed comparison back to ordered coordinates is exactly
scheme-theoretic insertion followed by the incidence quotient projection. -/
@[reassoc]
theorem curveOrderedAmbientToSymmetricProduct_comp_pointedComparison
    (n : ℕ) :
    curveOrderedAmbientToSymmetricProductSucc K C n ≫
        productSymmetricPowerToIncidenceQuotient K C n =
      orderedPointedToIncidenceQuotient K C n := by
  rw [productSymmetricPowerToIncidenceQuotient, ← Category.assoc]
  change curveOrderedAmbientToSymmetricProductSucc K C n ≫
      curveSymmetricProductToAmbientQuotientSucc K C n ≫
        ambientQuotientToIncidenceQuotientPointed K C n = _
  rw [← Category.assoc,
    curveOrderedAmbientToSymmetricProductSucc_comp_inverse,
    curveOrderedAmbientQuotientProjection_comp_pointedDescent]

/-- Ordered pointed addition respects the structure maps to the field. -/
@[reassoc]
theorem orderedPointedToIncidenceQuotient_comp_structureMap (n : ℕ) :
    orderedPointedToIncidenceQuotient K C n ≫
        curveOrderedIncidenceQuotientStructureMapSucc K C (n + 1) =
      (orderedAmbient (Spec (.of K)) (n + 1) C).hom := by
  rw [orderedPointedToIncidenceQuotient, Category.assoc,
    curveOrderedIncidenceQuotientProjection_comp_structureMap,
    curveOrderedIncidenceStructureMapSucc, ← Category.assoc,
    PointedIncidence.orderedPointedIncidenceMap_comp_ι]
  exact (PointedIncidence.orderedAmbientInsertion
    (Spec (.of K)) (n + 1) C).w

/-- The pointed symmetric-power comparison is a morphism over the ground
field. -/
@[reassoc]
theorem productSymmetricPowerToIncidenceQuotient_comp_structureMap
    (n : ℕ) :
    productSymmetricPowerToIncidenceQuotient K C n ≫
        curveOrderedIncidenceQuotientStructureMapSucc K C (n + 1) =
      (C ⨯ SymmetricPower.curveSchemeSucc K C n).hom := by
  let q := curveOrderedAmbientQuotientProjectionSucc K C n
  let e := curveAmbientQuotientToSymmetricProductSucc K C n
  haveI : Epi q := FiniteGroupQuotient.epi_quotientπ
    (orderedAmbientAction (Spec (.of K)) (n + 1) C)
    (curveOrderedAmbient_hasAffineOrbit_succ K C n)
  haveI : IsIso e := curveAmbientQuotientToSymmetricProductSucc_isIso K C n
  haveI : Epi (q ≫ e) := inferInstance
  have hqe : q ≫ e = curveOrderedAmbientToSymmetricProductSucc K C n :=
    curveOrderedAmbientQuotientProjection_comp_toSymmetricProduct K C n
  haveI : Epi (curveOrderedAmbientToSymmetricProductSucc K C n) := hqe ▸ inferInstance
  apply (cancel_epi (curveOrderedAmbientToSymmetricProductSucc K C n)).mp
  rw [← Category.assoc,
    curveOrderedAmbientToSymmetricProduct_comp_pointedComparison,
    orderedPointedToIncidenceQuotient_comp_structureMap,
    curveOrderedAmbientToSymmetricProductSucc_comp_structureMap]

/-- The pointed symmetric-power comparison is proper. -/
instance productSymmetricPowerToIncidenceQuotient_isProper (n : ℕ) :
    IsProper (productSymmetricPowerToIncidenceQuotient K C n) := by
  let f := productSymmetricPowerToIncidenceQuotient K C n
  let t := curveOrderedIncidenceQuotientStructureMapSucc K C (n + 1)
  letI : IsProper t :=
    curveOrderedIncidenceQuotientStructureMapSucc_isProper K C (n + 1)
  letI : IsSeparated t := IsProper.toIsSeparated
  letI : IsProper (f ≫ t) := by
    rw [productSymmetricPowerToIncidenceQuotient_comp_structureMap K C n]
    exact curveProductSymmetricPower_isProper K C n
  exact IsProper.of_comp f t

end MazurTorsion.AlgebraicGeometry.Jacobian.PointedIncidenceDescent

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.PointedIncidence
import MazurTorsion.AlgebraicGeometry.Jacobian.UniversalEffectiveDivisorDescent
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

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

/-- The incidence quotient, packaged as a scheme over the ground field. -/
noncomputable def curveOrderedIncidenceQuotientOverSucc (n : ℕ) :
    Over (Spec (.of K)) :=
  Over.mk (curveOrderedIncidenceQuotientStructureMapSucc K C n)

/-- The pointed comparison as a morphism over the ground field. -/
noncomputable def productSymmetricPowerToIncidenceQuotientOver (n : ℕ) :
    C ⨯ SymmetricPower.curveSchemeSucc K C n ⟶
      curveOrderedIncidenceQuotientOverSucc K C (n + 1) :=
  Over.homMk (productSymmetricPowerToIncidenceQuotient K C n)
    (productSymmetricPowerToIncidenceQuotient_comp_structureMap K C n)

/-- The descended incidence morphism, packaged over the ground field. -/
noncomputable def curveDescendedIncidenceOverSucc (n : ℕ) :
    curveOrderedIncidenceQuotientOverSucc K C n ⟶
      C ⨯ SymmetricPower.curveSchemeSucc K C n :=
  Over.homMk (curveDescendedIncidenceιSucc K C n)
    (curveDescendedIncidenceιSucc_comp_structureMap K C n)

/-- Add the distinguished point to an effective divisor:
`C × Sym^(n+1)(C) ⟶ Sym^(n+2)(C)`.  This definition is obtained from
the checked incidence quotient and is the map used by the local root-chart
comparison. -/
noncomputable def pointedSymmetricPowerAddition (n : ℕ) :
    C ⨯ SymmetricPower.curveSchemeSucc K C n ⟶
      SymmetricPower.curveSchemeSucc K C (n + 1) :=
  productSymmetricPowerToIncidenceQuotientOver K C n ≫
    curveDescendedIncidenceOverSucc K C (n + 1) ≫
      (Limits.prod.snd :
        C ⨯ SymmetricPower.curveSchemeSucc K C (n + 1) ⟶
          SymmetricPower.curveSchemeSucc K C (n + 1))

theorem pointedSymmetricPowerAddition_left (n : ℕ) :
    (pointedSymmetricPowerAddition K C n).left =
      productSymmetricPowerToIncidenceQuotient K C n ≫
        curveDescendedIncidenceιSucc K C (n + 1) ≫
          (Limits.prod.snd :
            C ⨯ SymmetricPower.curveSchemeSucc K C (n + 1) ⟶
              SymmetricPower.curveSchemeSucc K C (n + 1)).left :=
  rfl

/-- The incidence comparison retains the distinguished curve coordinate. -/
@[reassoc]
theorem productSymmetricPowerToIncidenceQuotient_comp_descendedIncidence_fst
    (n : ℕ) :
    productSymmetricPowerToIncidenceQuotient K C n ≫
        curveDescendedIncidenceιSucc K C (n + 1) ≫
          (Limits.prod.fst :
            C ⨯ SymmetricPower.curveSchemeSucc K C (n + 1) ⟶ C).left =
      (Limits.prod.fst :
        C ⨯ SymmetricPower.curveSchemeSucc K C n ⟶ C).left := by
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
    orderedPointedToIncidenceQuotient]
  simp only [Category.assoc]
  rw [curveOrderedIncidenceQuotientProjection_comp_descendedIncidenceι_assoc,
    PointedIncidence.orderedPointedIncidenceMap_comp_ι_assoc]
  change
    (PointedIncidence.orderedAmbientInsertion
        (Spec (.of K)) (n + 1) C ≫
      Limits.prod.map (𝟙 C)
        (SymmetricPower.curveProjectionSucc K C (n + 1)) ≫
      (Limits.prod.fst :
        C ⨯ SymmetricPower.curveSchemeSucc K C (n + 1) ⟶ C)).left =
    (Limits.prod.map (𝟙 C)
        (SymmetricPower.curveProjectionSucc K C n) ≫
      (Limits.prod.fst :
        C ⨯ SymmetricPower.curveSchemeSucc K C n ⟶ C)).left
  rw [Limits.prod.map_fst, Limits.prod.map_fst, Category.comp_id,
    PointedIncidence.orderedAmbientInsertion_comp_pointProjection]
  rfl

/-- The composite into `C × Sym^(n+2)(C)` is the graph of pointed
addition.  Thus proving the incidence comparison is an isomorphism is
exactly the construction of the universal effective divisor as this graph. -/
theorem productSymmetricPowerToIncidenceQuotientOver_comp_descendedIncidenceOver
    (n : ℕ) :
    productSymmetricPowerToIncidenceQuotientOver K C n ≫
        curveDescendedIncidenceOverSucc K C (n + 1) =
      Limits.prod.lift
        (Limits.prod.fst :
          C ⨯ SymmetricPower.curveSchemeSucc K C n ⟶ C)
        (pointedSymmetricPowerAddition K C n) := by
  apply Limits.prod.hom_ext
  · rw [Limits.prod.lift_fst, Category.assoc]
    apply CostructuredArrow.hom_ext
    exact
      productSymmetricPowerToIncidenceQuotient_comp_descendedIncidence_fst
        K C n
  · rw [Limits.prod.lift_snd, Category.assoc]
    rfl

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

/-- The pointed comparison is an isomorphism once it becomes one after an
fpqc cover of the incidence quotient.  The downstream consumer is the local
monic-root chart comparison: its explicit affine isomorphisms provide the
pullback instance, while this theorem performs the global descent step. -/
theorem productSymmetricPowerToIncidenceQuotient_isIso_of_fpqc
    (n : ℕ) (T : Scheme.{u})
    (q : T ⟶ curveOrderedIncidenceQuotientSucc K C (n + 1))
    [Surjective q] [Flat q] [QuasiCompact q]
    [IsIso (pullback.fst q
      (productSymmetricPowerToIncidenceQuotient K C n))] :
    IsIso (productSymmetricPowerToIncidenceQuotient K C n) := by
  exact MorphismProperty.of_pullback_fst_of_descendsAlong
    (P := MorphismProperty.isomorphisms Scheme.{u})
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := q) (g := productSymmetricPowerToIncidenceQuotient K C n)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance

end MazurTorsion.AlgebraicGeometry.Jacobian.PointedIncidenceDescent

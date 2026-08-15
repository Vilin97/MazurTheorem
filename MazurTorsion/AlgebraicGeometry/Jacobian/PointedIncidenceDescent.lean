/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.PointedIncidence
import MazurTorsion.AlgebraicGeometry.Jacobian.UniversalEffectiveDivisorDescent
import MazurTorsion.AlgebraicGeometry.Jacobian.FpqcDescent
import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteSupportCoordinateMaps
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

/-- The ordered divisor coordinates underlying a point of the incidence
ambient product. -/
noncomputable def orderedSupportPoint (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left) :
    (PermutationPower.power (Spec (.of K)) (Fin d) C).left :=
  (Limits.prod.snd : orderedAmbient (Spec (.of K)) d C ⟶
    PermutationPower.power (Spec (.of K)) (Fin d) C).left z

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- Every ordered incidence-ambient point therefore carries a finite family
of actual affine étale curve-coordinate charts, one for each occurrence in
its ordered support. -/
theorem orderedSupportPoint_nonempty_charts (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left) :
    Nonempty (FiniteSupportEtaleCoordinates.Charts K C d
      (orderedSupportPoint K C d z)) :=
  FiniteSupportEtaleCoordinates.nonempty_charts K C d
    (orderedSupportPoint K C d z)

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- Chosen coordinate charts on the ordered support of an incidence point. -/
noncomputable def orderedSupportCharts (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left) :
    FiniteSupportEtaleCoordinates.Charts K C d
      (orderedSupportPoint K C d z) :=
  FiniteSupportEtaleCoordinates.charts K C d (orderedSupportPoint K C d z)

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- Chosen finite étale Zariski-main neighborhoods on the ordered support. -/
noncomputable def orderedSupportNeighborhoods (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left) :=
  FiniteSupportEtaleCoordinates.neighborhoods K C d
    (orderedSupportPoint K C d z) (orderedSupportCharts K C d z)

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- The common étale base of all selected support neighborhoods. -/
noncomputable abbrev orderedSupportCommonBase (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left) :=
  FiniteSupportEtaleCoordinates.commonBase K C d
    (orderedSupportPoint K C d z) (orderedSupportCharts K C d z)
      (orderedSupportNeighborhoods K C d z)

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- The finite family of support components over their common étale base. -/
noncomputable abbrev orderedSupportComponentFamily (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left) :=
  FiniteSupportEtaleCoordinates.commonComponentFamily K C d
    (orderedSupportPoint K C d z) (orderedSupportCharts K C d z)
      (orderedSupportNeighborhoods K C d z)

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
instance orderedSupportComponentFamily_isFinite (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left) :
    IsFinite (orderedSupportComponentFamily K C d z).hom := inferInstance

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
instance orderedSupportComponentFamily_etale (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left) :
    Etale (orderedSupportComponentFamily K C d z).hom := inferInstance

/-- The pointwise split-chart assertion specialized to the actual ordered
support of an incidence-ambient point. -/
noncomputable abbrev OrderedSupportSplitChart (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left) : Prop :=
  FiniteSupportEtaleCoordinates.HasCommonSplitChartAtSupport K C d
    (orderedSupportPoint K C d z) (orderedSupportCharts K C d z)
      (orderedSupportNeighborhoods K C d z)

omit [GeometricallyIrreducible C.hom] [IsProper C.hom] in
/-- Every ordered incidence-ambient point has a common finite étale fpqc
split chart carrying a point above its exact ordered support. -/
theorem orderedSupport_exists_splitChart (d : ℕ)
    (z : (orderedAmbient (Spec (.of K)) d C).left) :
    OrderedSupportSplitChart K C d z :=
  FiniteSupportEtaleCoordinates.exists_commonSplitChartAtSupport K C d
    (orderedSupportPoint K C d z) (orderedSupportCharts K C d z)
      (orderedSupportNeighborhoods K C d z)

/-- A chosen ordered-incidence lift of a point of the incidence quotient. -/
noncomputable def orderedIncidenceLift (n : ℕ)
    (y : curveOrderedIncidenceQuotientSucc K C n) :
    orderedIncidence (Spec (.of K)) (n + 1) C :=
  Classical.choose
    ((curveOrderedIncidenceQuotientProjectionSucc K C n).surjective y)

@[simp]
theorem orderedIncidenceQuotientProjection_lift (n : ℕ)
    (y : curveOrderedIncidenceQuotientSucc K C n) :
    curveOrderedIncidenceQuotientProjectionSucc K C n
        (orderedIncidenceLift K C n y) = y :=
  Classical.choose_spec
    ((curveOrderedIncidenceQuotientProjectionSucc K C n).surjective y)

/-- The chosen quotient lift, embedded in the ordered incidence ambient
product so that its divisor support can be charted. -/
noncomputable def orderedIncidenceAmbientLift (n : ℕ)
    (y : curveOrderedIncidenceQuotientSucc K C n) :
    (orderedAmbient (Spec (.of K)) (n + 1) C).left :=
  orderedIncidenceι (Spec (.of K)) (n + 1) C
    (orderedIncidenceLift K C n y)

/-- Every point of the actual incidence quotient therefore has an ordered
lift whose exact support is carried by one common finite étale fpqc split
chart. -/
theorem incidenceQuotientPoint_exists_orderedSupportSplitChart (n : ℕ)
    (y : curveOrderedIncidenceQuotientSucc K C n) :
    OrderedSupportSplitChart K C (n + 1)
      (orderedIncidenceAmbientLift K C n y) :=
  orderedSupport_exists_splitChart K C (n + 1)
    (orderedIncidenceAmbientLift K C n y)

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

/-- On ordered coordinates, pointed addition prepends the distinguished
point and then takes the symmetric quotient. -/
@[reassoc]
theorem curveOrderedAmbientToSymmetricProduct_comp_pointedAddition
    (n : ℕ) :
    curveOrderedAmbientToSymmetricProductSucc K C n ≫
        (pointedSymmetricPowerAddition K C n).left =
      (PointedIncidence.prependPower
          (Spec (.of K)) (n + 1) C).left ≫
        (SymmetricPower.curveProjectionSucc K C (n + 1)).left := by
  rw [pointedSymmetricPowerAddition_left, ← Category.assoc,
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
      (Limits.prod.snd :
        C ⨯ SymmetricPower.curveSchemeSucc K C (n + 1) ⟶
          SymmetricPower.curveSchemeSucc K C (n + 1))).left =
    (PointedIncidence.prependPower (Spec (.of K)) (n + 1) C ≫
      SymmetricPower.curveProjectionSucc K C (n + 1)).left
  apply congrArg Over.Hom.left
  rw [Limits.prod.map_snd, ← Category.assoc,
    PointedIncidence.orderedAmbientInsertion, Limits.prod.lift_snd]

/-- The pointed comparison covers every point of the incidence quotient.
Lift an incidence point to the ordered incidence family, choose a coordinate
graph containing that lift, delete the chosen coordinate, and reinsert it as
coordinate zero.  The explicit reindexing identity shows that the resulting
point differs from the original lift by a permutation, hence has the same
image in the quotient. -/
theorem productSymmetricPowerToIncidenceQuotient_surjective (n : ℕ) :
    Function.Surjective
      (productSymmetricPowerToIncidenceQuotient K C n) := by
  classical
  intro y
  let q := curveOrderedIncidenceQuotientProjectionSucc K C (n + 1)
  obtain ⟨a, ha⟩ := q.surjective y
  obtain ⟨i, z, hz⟩ :=
    orderedIncidence_exists_coordinateGraph_preimage
      (Spec (.of K)) (n + 2) C a
  let b : (orderedAmbient (Spec (.of K)) (n + 1) C).left :=
    (PointedIncidence.removeCoordinate
      (Spec (.of K)) (n + 1) C i).left
        ((coordinateGraphι (Spec (.of K)) (n + 2) C i).left z)
  let g : Equiv.Perm (Fin (n + 2)) :=
    (PointedIncidence.moveZeroTo (n + 1) i).symm
  have hrecover :
      (orderedAmbientAction (Spec (.of K)) (n + 2) C).hom g
          ((PointedIncidence.orderedAmbientInsertion
            (Spec (.of K)) (n + 1) C).left b) =
        orderedIncidenceι (Spec (.of K)) (n + 2) C a := by
    change
      (orderedAmbientPermutationHom (Spec (.of K)) (n + 2) C g).left
          ((PointedIncidence.orderedAmbientInsertion
            (Spec (.of K)) (n + 1) C).left b) =
        orderedIncidenceι (Spec (.of K)) (n + 2) C a
    have h := congrArg Over.Hom.left
      (PointedIncidence.coordinateGraphι_comp_removeCoordinate_comp_insertion_comp_permutation
        (Spec (.of K)) (n + 1) C i)
    have hz' := congrArg
      (fun m : (coordinateGraph (Spec (.of K)) (n + 2) C i).left ⟶
          (orderedAmbient (Spec (.of K)) (n + 2) C).left ↦ m z) h
    simpa only [Over.comp_left, Scheme.Hom.comp_apply, b, g] using hz'.trans hz
  have horbit :
      (orderedIncidenceAction (Spec (.of K)) (n + 2) C).hom g
          (PointedIncidence.orderedPointedIncidenceMap
            (Spec (.of K)) (n + 1) C b) = a := by
    apply (orderedIncidenceι (Spec (.of K)) (n + 2) C).isEmbedding.injective
    let v := PointedIncidence.orderedPointedIncidenceMap
      (Spec (.of K)) (n + 1) C b
    have hequivariant := congrArg
      (fun m : orderedIncidence (Spec (.of K)) (n + 2) C ⟶
          (orderedAmbient (Spec (.of K)) (n + 2) C).left ↦ m v)
      (orderedIncidenceAction_comp_ι
        (Spec (.of K)) (n + 2) C g)
    have hinsertion := congrArg
      (fun m : (orderedAmbient (Spec (.of K)) (n + 1) C).left ⟶
          (orderedAmbient (Spec (.of K)) (n + 2) C).left ↦ m b)
      (PointedIncidence.orderedPointedIncidenceMap_comp_ι
        (Spec (.of K)) (n + 1) C)
    calc
      orderedIncidenceι (Spec (.of K)) (n + 2) C
          ((orderedIncidenceAction (Spec (.of K)) (n + 2) C).hom g v) =
          (orderedAmbientAction (Spec (.of K)) (n + 2) C).hom g
            (orderedIncidenceι (Spec (.of K)) (n + 2) C v) := by
        simpa only [Scheme.Hom.comp_apply] using hequivariant
      _ = (orderedAmbientAction (Spec (.of K)) (n + 2) C).hom g
            ((PointedIncidence.orderedAmbientInsertion
              (Spec (.of K)) (n + 1) C).left b) := by
        exact congrArg
          ((orderedAmbientAction (Spec (.of K)) (n + 2) C).hom g)
          (by simpa only [v, Scheme.Hom.comp_apply] using hinsertion)
      _ = orderedIncidenceι (Spec (.of K)) (n + 2) C a := hrecover
  refine ⟨curveOrderedAmbientToSymmetricProductSucc K C n b, ?_⟩
  calc
    productSymmetricPowerToIncidenceQuotient K C n
        (curveOrderedAmbientToSymmetricProductSucc K C n b) =
        orderedPointedToIncidenceQuotient K C n b := by
      have h := congrArg
        (fun m : (orderedAmbient (Spec (.of K)) (n + 1) C).left ⟶
            curveOrderedIncidenceQuotientSucc K C (n + 1) ↦ m b)
        (curveOrderedAmbientToSymmetricProduct_comp_pointedComparison K C n)
      simpa only [Scheme.Hom.comp_apply] using h
    _ = q a := by
      change q
          (PointedIncidence.orderedPointedIncidenceMap
            (Spec (.of K)) (n + 1) C b) = q a
      apply (FiniteGroupQuotient.quotientπ_apply_eq_iff
        (orderedIncidenceAction (Spec (.of K)) (n + 2) C)
        (curveOrderedIncidence_hasAffineOrbit_succ K C (n + 1)) _ _).mpr
      exact ⟨g, horbit⟩
    _ = y := ha

instance productSymmetricPowerToIncidenceQuotient_surjectiveProperty
    (n : ℕ) :
    Surjective (productSymmetricPowerToIncidenceQuotient K C n) :=
  ⟨productSymmetricPowerToIncidenceQuotient_surjective K C n⟩

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

/-- Pointed addition is proper.  The remaining local task for finiteness is
therefore only quasi-finiteness of its divisor fibers. -/
instance pointedSymmetricPowerAddition_isProper (n : ℕ) :
    IsProper (pointedSymmetricPowerAddition K C n).left := by
  rw [pointedSymmetricPowerAddition_left]
  infer_instance

/-- Every point fiber of pointed addition is finite.  After choosing an
ordered lift of the target divisor and an ordered lift of each source
divisor, a point of the fiber determines a permutation carrying the
prepended source tuple to the fixed target tuple.  Choosing one such
permutation gives an injection of the fiber into the finite symmetric
group: equality of permutations forces equality of the prepended tuples,
and `unprependPower` then recovers the source lift. -/
theorem pointedSymmetricPowerAddition_finite_preimage_singleton
    (n : ℕ)
    (y : (SymmetricPower.curveSchemeSucc K C (n + 1)).left) :
    ((pointedSymmetricPowerAddition K C n).left ⁻¹' {y}).Finite := by
  classical
  let f := (pointedSymmetricPowerAddition K C n).left
  let p := curveOrderedAmbientToSymmetricProductSucc K C n
  let r := (SymmetricPower.curveProjectionSucc K C (n + 1)).left
  let σ := SymmetricPower.Action (Spec (.of K)) (n + 2) C
  let hσ := SymmetricPower.curve_hasAffineOrbits_succ K C (n + 1)
  obtain ⟨b, hb⟩ := r.surjective y
  let a (z : f ⁻¹' {y}) :
      (orderedAmbient (Spec (.of K)) (n + 1) C).left :=
    Classical.choose (p.surjective z.1)
  have ha (z : f ⁻¹' {y}) : p (a z) = z.1 :=
    Classical.choose_spec (p.surjective z.1)
  have hz (z : f ⁻¹' {y}) : f z.1 = y := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using z.2
  have horbit (z : f ⁻¹' {y}) :
      ∃ g : Equiv.Perm (Fin (n + 2)),
        σ.hom g
            ((PointedIncidence.prependPower
              (Spec (.of K)) (n + 1) C).left (a z)) = b := by
    apply (FiniteGroupQuotient.quotientπ_apply_eq_iff σ hσ
      ((PointedIncidence.prependPower
        (Spec (.of K)) (n + 1) C).left (a z)) b).mp
    change r
        ((PointedIncidence.prependPower
          (Spec (.of K)) (n + 1) C).left (a z)) = r b
    rw [hb]
    calc
      r ((PointedIncidence.prependPower
          (Spec (.of K)) (n + 1) C).left (a z)) =
          f (p (a z)) := by
        have h := congrArg
          (fun q : (orderedAmbient (Spec (.of K)) (n + 1) C).left ⟶
              (SymmetricPower.curveSchemeSucc K C (n + 1)).left ↦ q (a z))
          (curveOrderedAmbientToSymmetricProduct_comp_pointedAddition
            K C n)
        simpa only [Scheme.Hom.comp_apply] using h.symm
      _ = f z.1 := congrArg f (ha z)
      _ = y := hz z
  let permutation (z : f ⁻¹' {y}) : Equiv.Perm (Fin (n + 2)) :=
    Classical.choose (horbit z)
  have hpermutation (z : f ⁻¹' {y}) :
      σ.hom (permutation z)
          ((PointedIncidence.prependPower
            (Spec (.of K)) (n + 1) C).left (a z)) = b :=
    Classical.choose_spec (horbit z)
  have hinjective : Function.Injective permutation := by
    intro z w hzw
    apply Subtype.ext
    have haction :
        σ.hom (permutation z)
            ((PointedIncidence.prependPower
              (Spec (.of K)) (n + 1) C).left (a z)) =
          σ.hom (permutation z)
            ((PointedIncidence.prependPower
              (Spec (.of K)) (n + 1) C).left (a w)) := by
      simpa only [hzw] using
        (hpermutation z).trans (hpermutation w).symm
    have hprepend :
        (PointedIncidence.prependPower
            (Spec (.of K)) (n + 1) C).left (a z) =
          (PointedIncidence.prependPower
            (Spec (.of K)) (n + 1) C).left (a w) :=
      (σ.hom (permutation z)).isEmbedding.injective haction
    have haw : a z = a w :=
      PointedIncidence.prependPower_injective
        (Spec (.of K)) (n + 1) C hprepend
    exact (ha z).symm.trans ((congrArg p haw).trans (ha w))
  letI : Finite (f ⁻¹' {y}) :=
    Finite.of_injective permutation hinjective
  exact Set.toFinite (f ⁻¹' {y})

/-- Pointed addition is locally quasi-finite because all of its point
fibers inject into a finite symmetric group. -/
instance pointedSymmetricPowerAddition_locallyQuasiFinite (n : ℕ) :
    LocallyQuasiFinite (pointedSymmetricPowerAddition K C n).left := by
  apply LocallyQuasiFinite.of_finite_preimage_singleton
  exact pointedSymmetricPowerAddition_finite_preimage_singleton K C n

/-- Pointed addition is finite: it is proper and locally quasi-finite. -/
instance pointedSymmetricPowerAddition_isFinite (n : ℕ) :
    IsFinite (pointedSymmetricPowerAddition K C n).left :=
  IsFinite.of_isProper_of_locallyQuasiFinite
    (pointedSymmetricPowerAddition K C n).left

/-- A point fiber of the comparison with the incidence quotient is contained
in a point fiber of pointed addition, obtained by applying the descended
incidence morphism and then projecting to the symmetric-power coordinate. -/
theorem productSymmetricPowerToIncidenceQuotient_finite_preimage_singleton
    (n : ℕ) (y : curveOrderedIncidenceQuotientSucc K C (n + 1)) :
    ((productSymmetricPowerToIncidenceQuotient K C n) ⁻¹' {y}).Finite := by
  let t :=
    (Limits.prod.snd :
      C ⨯ SymmetricPower.curveSchemeSucc K C (n + 1) ⟶
        SymmetricPower.curveSchemeSucc K C (n + 1)).left
      (curveDescendedIncidenceιSucc K C (n + 1) y)
  refine
    (pointedSymmetricPowerAddition_finite_preimage_singleton K C n t).subset ?_
  intro z hz
  have hzy : productSymmetricPowerToIncidenceQuotient K C n z = y := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hz
  change (pointedSymmetricPowerAddition K C n).left z = t
  rw [pointedSymmetricPowerAddition_left]
  simp only [Scheme.Hom.comp_apply, hzy, t]

/-- The comparison with the incidence quotient is locally quasi-finite. -/
instance productSymmetricPowerToIncidenceQuotient_locallyQuasiFinite
    (n : ℕ) :
    LocallyQuasiFinite
      (productSymmetricPowerToIncidenceQuotient K C n) := by
  apply LocallyQuasiFinite.of_finite_preimage_singleton
  exact
    productSymmetricPowerToIncidenceQuotient_finite_preimage_singleton K C n

/-- The comparison with the incidence quotient is finite.  The subsequent
local monic-root calculation can therefore identify a finite algebra rather
than first establishing quasi-compactness separately. -/
instance productSymmetricPowerToIncidenceQuotient_isFinite (n : ℕ) :
    IsFinite (productSymmetricPowerToIncidenceQuotient K C n) :=
  IsFinite.of_isProper_of_locallyQuasiFinite
    (productSymmetricPowerToIncidenceQuotient K C n)

/-- The candidate degree-`n + 2` universal effective divisor, written in
its explicit pointed symmetric-power presentation
`(x, D) ↦ (x, x + D)`.  The named downstream consumer is the Abel map in
`PicardRepresentability`; flatness, rank, and Cartier-ness are deliberately
left to the local monic-root comparison. -/
noncomputable def pointedUniversalEffectiveDivisor (n : ℕ) :
    (C ⨯ SymmetricPower.curveSchemeSucc K C n).left ⟶
      (C ⨯ SymmetricPower.curveSchemeSucc K C (n + 1)).left :=
  (Limits.prod.lift
    (Limits.prod.fst :
      C ⨯ SymmetricPower.curveSchemeSucc K C n ⟶ C)
    (pointedSymmetricPowerAddition K C n)).left

/-- The explicit pointed divisor factors through the finite incidence
quotient and its descended finite morphism. -/
theorem pointedUniversalEffectiveDivisor_eq_incidenceComposite (n : ℕ) :
    pointedUniversalEffectiveDivisor K C n =
      productSymmetricPowerToIncidenceQuotient K C n ≫
        curveDescendedIncidenceιSucc K C (n + 1) := by
  exact congrArg Over.Hom.left
    (productSymmetricPowerToIncidenceQuotientOver_comp_descendedIncidenceOver
      K C n).symm

/-- The pointed universal-divisor candidate is finite over
`C × Sym^(n+2)(C)`. -/
instance pointedUniversalEffectiveDivisor_isFinite (n : ℕ) :
    IsFinite (pointedUniversalEffectiveDivisor K C n) := by
  rw [pointedUniversalEffectiveDivisor_eq_incidenceComposite]
  infer_instance

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

/-- The pointed comparison may be checked on an independently chosen fpqc
chart around every point of the incidence quotient. -/
theorem productSymmetricPowerToIncidenceQuotient_isIso_of_pointwise_fpqc
    (n : ℕ)
    (U : curveOrderedIncidenceQuotientSucc K C (n + 1) →
      (curveOrderedIncidenceQuotientSucc K C (n + 1)).Opens)
    (mem : ∀ y, y ∈ U y)
    (T : curveOrderedIncidenceQuotientSucc K C (n + 1) → Scheme.{u})
    (q : ∀ y, T y ⟶ (U y).toScheme)
    [∀ y, Surjective (q y)] [∀ y, Flat (q y)] [∀ y, QuasiCompact (q y)]
    [∀ y, IsIso (pullback.fst (q y)
      (productSymmetricPowerToIncidenceQuotient K C n ∣_ U y))] :
    IsIso (productSymmetricPowerToIncidenceQuotient K C n) :=
  FpqcDescent.isIso_of_pointwise_fpqc_pullback
    (productSymmetricPowerToIncidenceQuotient K C n) U mem T q

/-- The universal-divisor candidate is flat once the local monic-root model
identifies its pullback along an fpqc chart as flat. -/
theorem pointedUniversalEffectiveDivisor_flat_of_fpqc
    (n : ℕ) (T : Scheme.{u})
    (q : T ⟶ (C ⨯ SymmetricPower.curveSchemeSucc K C (n + 1)).left)
    [Surjective q] [Flat q] [QuasiCompact q]
    [Flat (pullback.fst q (pointedUniversalEffectiveDivisor K C n))] :
    Flat (pointedUniversalEffectiveDivisor K C n) :=
  FpqcDescent.flat_of_fpqc_pullback
    (pointedUniversalEffectiveDivisor K C n) q

/-- Flatness of the universal-divisor candidate may be checked on one fpqc
chart chosen around each point of `C × Sym^(n+2)(C)`. -/
theorem pointedUniversalEffectiveDivisor_flat_of_pointwise_fpqc
    (n : ℕ)
    (U : (C ⨯ SymmetricPower.curveSchemeSucc K C (n + 1)).left →
      (C ⨯ SymmetricPower.curveSchemeSucc K C (n + 1)).left.Opens)
    (mem : ∀ y, y ∈ U y)
    (T : (C ⨯ SymmetricPower.curveSchemeSucc K C (n + 1)).left → Scheme.{u})
    (q : ∀ y, T y ⟶ (U y).toScheme)
    [∀ y, Surjective (q y)] [∀ y, Flat (q y)] [∀ y, QuasiCompact (q y)]
    [∀ y, Flat (pullback.fst (q y)
      (pointedUniversalEffectiveDivisor K C n ∣_ U y))] :
    Flat (pointedUniversalEffectiveDivisor K C n) :=
  FpqcDescent.flat_of_pointwise_fpqc_pullback
    (pointedUniversalEffectiveDivisor K C n) U mem T q

/-- If the local monic-root model has constant rank `n + 2`, then the
global universal-divisor candidate is finite flat of that same rank. -/
theorem pointedUniversalEffectiveDivisor_finrank_eq_of_fpqc
    (n : ℕ) (T : Scheme.{u})
    (q : T ⟶ (C ⨯ SymmetricPower.curveSchemeSucc K C (n + 1)).left)
    [Surjective q] [Flat q] [QuasiCompact q]
    [Flat (pullback.fst q (pointedUniversalEffectiveDivisor K C n))]
    (h : (pullback.fst q (pointedUniversalEffectiveDivisor K C n)).finrank =
      fun _ ↦ n + 2) :
    (pointedUniversalEffectiveDivisor K C n).finrank = fun _ ↦ n + 2 := by
  letI : Flat (pointedUniversalEffectiveDivisor K C n) :=
    pointedUniversalEffectiveDivisor_flat_of_fpqc K C n T q
  exact FpqcDescent.finrank_eq_of_surjective_baseChange
    (pointedUniversalEffectiveDivisor K C n) q (n + 2) h

/-- The constant degree of the universal-divisor candidate may likewise be
checked on independently chosen pointwise fpqc charts. -/
theorem pointedUniversalEffectiveDivisor_finrank_eq_of_pointwise_fpqc
    (n : ℕ)
    (U : (C ⨯ SymmetricPower.curveSchemeSucc K C (n + 1)).left →
      (C ⨯ SymmetricPower.curveSchemeSucc K C (n + 1)).left.Opens)
    (mem : ∀ y, y ∈ U y)
    (T : (C ⨯ SymmetricPower.curveSchemeSucc K C (n + 1)).left → Scheme.{u})
    (q : ∀ y, T y ⟶ (U y).toScheme)
    [∀ y, Surjective (q y)] [∀ y, Flat (q y)] [∀ y, QuasiCompact (q y)]
    [∀ y, Flat (pullback.fst (q y)
      (pointedUniversalEffectiveDivisor K C n ∣_ U y))]
    (h : ∀ y, (pullback.fst (q y)
      (pointedUniversalEffectiveDivisor K C n ∣_ U y)).finrank =
        fun _ ↦ n + 2) :
    (pointedUniversalEffectiveDivisor K C n).finrank = fun _ ↦ n + 2 :=
  FpqcDescent.finrank_eq_of_pointwise_fpqc_baseChange
    (pointedUniversalEffectiveDivisor K C n) U mem T q (n + 2) h

end MazurTorsion.AlgebraicGeometry.Jacobian.PointedIncidenceDescent

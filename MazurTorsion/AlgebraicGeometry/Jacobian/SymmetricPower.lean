/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteGroupQuotient
import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteMapToProjectiveLine
import MazurTorsion.AlgebraicGeometry.Jacobian.GeometricallyIrreducibleDescent
import MazurTorsion.AlgebraicGeometry.Jacobian.PermutationPower
import MazurTorsion.AlgebraicGeometry.Jacobian.ProjectiveFiniteOrbit

/-!
# Relative symmetric powers from finite permutation quotients

This module constructs the relative symmetric power once the permutation
orbits in the relative power have affine neighbourhoods.  The hypothesis is
exactly the geometric premise required by the checked AINTLIB finite-group
quotient construction; it is not a representability assumption.
-/

universe u

open CategoryTheory Limits

namespace MazurTorsion.AlgebraicGeometry.Jacobian.SymmetricPower

open _root_.AlgebraicGeometry
open FiniteGroupQuotient
open PermutationPower

variable (S : Scheme.{u}) (d : ℕ) (X : Over S)

noncomputable abbrev Action : SchemeAction (Equiv.Perm (Fin d)) (power S (Fin d) X).left :=
  action S (Fin d) X

/-- The affine-orbit premise needed to construct `Sym^d_S(X)`. -/
noncomputable abbrev HasAffineOrbits : Prop :=
  HasAffineOrbit (Action S d X)

/-- Affine permutation-orbit neighbourhoods transfer along an affine
componentwise map of relative powers. -/
theorem hasAffineOrbits_of_map {X Y : Over S} (f : X ⟶ Y)
    [IsAffineHom (PermutationPower.map S (Fin d) f).left]
    (hY : HasAffineOrbits S d Y) : HasAffineOrbits S d X :=
  FiniteGroupQuotient.hasAffineOrbit_of_equivariant_affine
    (Action S d X) (Action S d Y) (PermutationPower.map S (Fin d) f).left hY
    (PermutationPower.action_equivariant S (Fin d) f)

/-- Finite componentwise maps transfer affine permutation-orbit
neighbourhoods. -/
theorem hasAffineOrbits_of_finite_map {X Y : Over S} (f : X ⟶ Y)
    [IsFinite f.left] (hY : HasAffineOrbits S d Y) : HasAffineOrbits S d X := by
  letI : IsFinite (PermutationPower.map S (Fin d) f).left :=
    PermutationPower.map_isFinite S (Fin d) f
  exact hasAffineOrbits_of_map S d f hY

/-- The checked finite map from a smooth proper geometrically irreducible
curve to `P¹` supplies affine permutation-orbit neighbourhoods in every
nonempty relative power. -/
theorem curve_hasAffineOrbits_succ
    (K : Type u) [Field K]
    (C : Over (Spec (.of K)))
    [GeometricallyIrreducible C.hom] [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom]
    (n : ℕ) : HasAffineOrbits (Spec (.of K)) (n + 1) C := by
  letI : IsFinite (FiniteMapToProjectiveLine.overHom K C).left :=
    FiniteMapToProjectiveLine.hom_isFinite K C
  exact hasAffineOrbits_of_finite_map (Spec (.of K)) (n + 1)
    (FiniteMapToProjectiveLine.overHom K C)
    (ProjectiveFiniteOrbit.projectiveLinePower_hasAffineOrbit K n)

section

variable [IsAffineHom
  (pullback.diagonal (terminal.from (power S (Fin d) X).left))]
variable (hX : HasAffineOrbits S d X)

/-- The underlying scheme quotient of the relative power by permutations. -/
noncomputable def underlying : Scheme.{u} :=
  FiniteGroupQuotient.quotient (Action S d X) hX

/-- The quotient projection on underlying schemes. -/
noncomputable def underlyingProjection :
    (power S (Fin d) X).left ⟶ underlying S d X hX :=
  FiniteGroupQuotient.quotientπ (Action S d X) hX

/-- The symmetric-power quotient projection is affine. -/
instance underlyingProjection_isAffineHom :
    IsAffineHom (underlyingProjection S d X hX) := by
  exact FiniteGroupQuotient.quotientπ_isAffineHom (Action S d X) hX

/-- Over an affine base, a locally finite-type relative power has finite
symmetric-quotient projection.  On every stable affine chart this is the
finite extension from the chart ring's invariants to the chart ring. -/
instance underlyingProjection_isFinite [IsAffine S]
    [LocallyOfFiniteType (power S (Fin d) X).hom] :
    IsFinite (underlyingProjection S d X hX) := by
  apply FiniteGroupQuotient.quotientπ_isFinite_of_chart_moduleFinite
  intro x
  exact FiniteGroupQuotient.chart_moduleFinite_of_locallyOfFiniteType
    (Action S d X) (power S (Fin d) X).hom
    (action_hom_comp_structureMap S (Fin d) X)
    (isAffineOpen_top S)
    (FiniteGroupQuotient.stableAffineOpen_isStable (Action S d X) hX x)
    (FiniteGroupQuotient.stableAffineOpen_isAffine (Action S d X) hX x)
    (by simp)

/-- The symmetric-power quotient projection is surjective on points. -/
theorem underlyingProjection_surjective :
    Function.Surjective ⇑(underlyingProjection S d X hX) :=
  FiniteGroupQuotient.quotientπ_surjective (Action S d X) hX

/-- The quotient projection packaged as a surjective scheme morphism. -/
instance underlyingProjection_surjectiveProperty :
    Surjective (underlyingProjection S d X hX) :=
  ⟨underlyingProjection_surjective S d X hX⟩

/-- The structure map descended from the relative power. -/
noncomputable def structureMap : underlying S d X hX ⟶ S :=
  Classical.choose <|
    FiniteGroupQuotient.existsUnique_quotientπ_lift (Action S d X) hX
      (power S (Fin d) X).hom (action_hom_comp_structureMap S (Fin d) X)

/-- The quotient projection followed by the descended structure map is the
original structure map. -/
theorem underlyingProjection_comp_structureMap :
    underlyingProjection S d X hX ≫ structureMap S d X hX =
      (power S (Fin d) X).hom :=
  (Classical.choose_spec <|
    FiniteGroupQuotient.existsUnique_quotientπ_lift (Action S d X) hX
      (power S (Fin d) X).hom (action_hom_comp_structureMap S (Fin d) X)).1

/-- The relative symmetric power as a scheme over the base. -/
noncomputable def scheme : Over S :=
  Over.mk (structureMap S d X hX)

/-- The canonical projection `X^d_S ⟶ Sym^d_S(X)`. -/
noncomputable def projection : power S (Fin d) X ⟶ scheme S d X hX :=
  Over.homMk (underlyingProjection S d X hX)
    (underlyingProjection_comp_structureMap S d X hX)

/-- The symmetric-power projection is invariant under every permutation. -/
theorem action_comp_projection (g : Equiv.Perm (Fin d)) :
    (Action S d X).hom g ≫ (projection S d X hX).left =
      (projection S d X hX).left :=
  FiniteGroupQuotient.hom_quotientπ (Action S d X) hX g

end

section Curve

variable (K : Type u) [Field K]

/-- Properness over `Spec K` as an object property in its slice category. -/
abbrev properOver : ObjectProperty (Over (Spec (.of K))) :=
  fun X ↦ IsProper X.hom

/-- The pair of geometric properties needed to iterate geometric
irreducibility through relative products. -/
abbrev geometricallyIrreducibleUniversallyOpenOver :
    ObjectProperty (Over (Spec (.of K))) :=
  fun X ↦ GeometricallyIrreducible X.hom ∧ UniversallyOpen X.hom

/-- Binary products of proper objects over a field remain proper. -/
theorem binaryProduct_isProper
    (X Y : Over (Spec (.of K))) (hX : IsProper X.hom)
    (hY : IsProper Y.hom) : IsProper (X ⨯ Y).hom := by
  have hpull : IsProper (pullback.fst X.hom Y.hom ≫ X.hom) := by
    letI : IsProper (pullback.fst X.hom Y.hom) :=
      MorphismProperty.pullback_fst (P := @IsProper) X.hom Y.hom hY
    letI : IsProper X.hom := hX
    infer_instance
  have hcomp :
      (Over.prodLeftIsoPullback X Y).hom ≫
          (pullback.fst X.hom Y.hom ≫ X.hom) =
        (X ⨯ Y).hom := by
    rw [← Category.assoc, Over.prodLeftIsoPullback_hom_fst]
    exact (Limits.prod.fst : X ⨯ Y ⟶ X).w
  have hprod : IsProper ((Over.prodLeftIsoPullback X Y).hom ≫
      (pullback.fst X.hom Y.hom ≫ X.hom)) := by
    infer_instance
  rw [hcomp] at hprod
  exact hprod

instance properOver_isClosedUnderIsomorphisms :
    (properOver K).IsClosedUnderIsomorphisms := by
  constructor
  intro X Y e hX
  let eleft : Y.left ≅ X.left := (Over.forget _).mapIso e.symm
  have hY : IsProper (eleft.hom ≫ X.hom) := by
    infer_instance
  have heq : eleft.hom ≫ X.hom = Y.hom := by
    change e.inv.left ≫ X.hom = Y.hom
    exact e.inv.w
  rw [heq] at hY
  exact hY

instance properOver_isClosedUnderBinaryProducts :
    (properOver K).IsClosedUnderBinaryProducts := by
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
  rintro _ ⟨F, hF⟩
  let X := F.obj ⟨WalkingPair.left⟩
  let Y := F.obj ⟨WalkingPair.right⟩
  let e : limit F ≅ X ⨯ Y := HasLimit.isoOfNatIso (diagramIsoPair F)
  apply (properOver K).prop_of_iso e.symm
  exact binaryProduct_isProper K X Y
    (hF ⟨WalkingPair.left⟩) (hF ⟨WalkingPair.right⟩)

instance geometricallyIrreducibleUniversallyOpenOver_isClosedUnderIsomorphisms :
    (geometricallyIrreducibleUniversallyOpenOver K).IsClosedUnderIsomorphisms := by
  constructor
  intro X Y e hX
  let eleft : Y.left ≅ X.left := (Over.forget _).mapIso e.symm
  letI : GeometricallyIrreducible eleft.hom :=
    geometricallyIrreducible_of_isIso eleft.hom
  letI : GeometricallyIrreducible X.hom := hX.1
  letI : UniversallyOpen X.hom := hX.2
  have hgi : GeometricallyIrreducible (eleft.hom ≫ X.hom) :=
    GeometricallyIrreducible.comp eleft.hom X.hom
  have huo : UniversallyOpen (eleft.hom ≫ X.hom) := by
    infer_instance
  have heq : eleft.hom ≫ X.hom = Y.hom := by
    change e.inv.left ≫ X.hom = Y.hom
    exact e.inv.w
  rw [heq] at hgi huo
  exact ⟨hgi, huo⟩

/-- The product of two geometrically irreducible, universally open schemes
over a field has the same pair of properties. -/
theorem binaryProduct_geometricallyIrreducibleUniversallyOpen
    (X Y : Over (Spec (.of K)))
    (hX : geometricallyIrreducibleUniversallyOpenOver K X)
    (hY : geometricallyIrreducibleUniversallyOpenOver K Y) :
    geometricallyIrreducibleUniversallyOpenOver K (X ⨯ Y) := by
  letI : GeometricallyIrreducible X.hom := hX.1
  letI : UniversallyOpen X.hom := hX.2
  letI : GeometricallyIrreducible Y.hom := hY.1
  letI : UniversallyOpen Y.hom := hY.2
  have hgi : GeometricallyIrreducible
      (pullback.fst X.hom Y.hom ≫ X.hom) :=
    GeometricallyIrreducible.comp (pullback.fst X.hom Y.hom) X.hom
  have huo : UniversallyOpen (pullback.fst X.hom Y.hom ≫ X.hom) := by
    infer_instance
  have hcomp :
      (Over.prodLeftIsoPullback X Y).hom ≫
          (pullback.fst X.hom Y.hom ≫ X.hom) =
        (X ⨯ Y).hom := by
    rw [← Category.assoc, Over.prodLeftIsoPullback_hom_fst]
    exact (Limits.prod.fst : X ⨯ Y ⟶ X).w
  have hprodGI : GeometricallyIrreducible
      ((Over.prodLeftIsoPullback X Y).hom ≫
        (pullback.fst X.hom Y.hom ≫ X.hom)) := by
    letI : GeometricallyIrreducible (Over.prodLeftIsoPullback X Y).hom :=
      geometricallyIrreducible_of_isIso (Over.prodLeftIsoPullback X Y).hom
    exact GeometricallyIrreducible.comp _ _
  have hprodUO : UniversallyOpen
      ((Over.prodLeftIsoPullback X Y).hom ≫
        (pullback.fst X.hom Y.hom ≫ X.hom)) := by
    infer_instance
  rw [hcomp] at hprodGI hprodUO
  exact ⟨hprodGI, hprodUO⟩

instance geometricallyIrreducibleUniversallyOpenOver_isClosedUnderBinaryProducts :
    (geometricallyIrreducibleUniversallyOpenOver K).IsClosedUnderBinaryProducts := by
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
  rintro _ ⟨F, hF⟩
  let X := F.obj ⟨WalkingPair.left⟩
  let Y := F.obj ⟨WalkingPair.right⟩
  let e : limit F ≅ X ⨯ Y := HasLimit.isoOfNatIso (diagramIsoPair F)
  apply (geometricallyIrreducibleUniversallyOpenOver K).prop_of_iso e.symm
  exact binaryProduct_geometricallyIrreducibleUniversallyOpen K X Y
    (hF ⟨WalkingPair.left⟩) (hF ⟨WalkingPair.right⟩)

variable (C : Over (Spec (.of K)))
variable [GeometricallyIrreducible C.hom] [IsProper C.hom]
variable [SmoothOfRelativeDimension 1 C.hom]

/-- Every nonempty relative power of a proper curve is proper over the
ground field. -/
instance curvePowerSucc_isProper (n : ℕ) :
    IsProper (power (Spec (.of K)) (Fin (n + 1)) C).hom :=
  ProjectiveFiniteOrbit.ObjectProperty.prop_product_fin_succ
    (properOver K) n (fun _ ↦ C) (fun _ ↦ inferInstance)

omit [GeometricallyIrreducible C.hom] [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] in
/-- A nonempty relative power of a scheme which is geometrically irreducible
and universally open over the ground field has the same properties. -/
theorem curvePowerSucc_geometricallyIrreducibleUniversallyOpen (n : ℕ)
    (hC : geometricallyIrreducibleUniversallyOpenOver K C) :
    geometricallyIrreducibleUniversallyOpenOver K
      (power (Spec (.of K)) (Fin (n + 1)) C) :=
  ProjectiveFiniteOrbit.ObjectProperty.prop_product_fin_succ
    (geometricallyIrreducibleUniversallyOpenOver K) n (fun _ ↦ C)
      (fun _ ↦ hC)

instance curvePowerSucc_geometricallyIrreducible (n : ℕ) :
    GeometricallyIrreducible
      (power (Spec (.of K)) (Fin (n + 1)) C).hom :=
  (curvePowerSucc_geometricallyIrreducibleUniversallyOpen K C n
    ⟨inferInstance, inferInstance⟩).1

instance curvePowerSucc_universallyOpen (n : ℕ) :
    UniversallyOpen (power (Spec (.of K)) (Fin (n + 1)) C).hom :=
  (curvePowerSucc_geometricallyIrreducibleUniversallyOpen K C n
    ⟨inferInstance, inferInstance⟩).2

/-- The underlying scheme of a nonempty relative power of a proper curve is
separated. -/
instance curvePowerSucc_isSeparated (n : ℕ) :
    (power (Spec (.of K)) (Fin (n + 1)) C).left.IsSeparated := by
  constructor
  rw [← terminal.comp_from (power (Spec (.of K)) (Fin (n + 1)) C).hom]
  infer_instance

/-- The positive-degree symmetric power of a challenge curve. -/
noncomputable def curveSchemeSucc (n : ℕ) : Over (Spec (.of K)) :=
  scheme (Spec (.of K)) (n + 1) C (curve_hasAffineOrbits_succ K C n)

/-- The canonical projection from the ordered power of a curve to its
positive-degree symmetric power. -/
noncomputable def curveProjectionSucc (n : ℕ) :
    power (Spec (.of K)) (Fin (n + 1)) C ⟶ curveSchemeSucc K C n :=
  projection (Spec (.of K)) (n + 1) C (curve_hasAffineOrbits_succ K C n)

@[reassoc]
theorem curveProjectionSucc_comp_structureMap (n : ℕ) :
    (curveProjectionSucc K C n).left ≫ (curveSchemeSucc K C n).hom =
      (power (Spec (.of K)) (Fin (n + 1)) C).hom :=
  underlyingProjection_comp_structureMap (Spec (.of K)) (n + 1) C
    (curve_hasAffineOrbits_succ K C n)

/-- The curve symmetric-power projection is affine. -/
instance curveProjectionSucc_isAffineHom (n : ℕ) :
    IsAffineHom (curveProjectionSucc K C n).left := by
  change IsAffineHom (underlyingProjection (Spec (.of K)) (n + 1) C
    (curve_hasAffineOrbits_succ K C n))
  exact underlyingProjection_isAffineHom (Spec (.of K)) (n + 1) C _

/-- The quotient from an ordered curve power to its symmetric power is
finite. -/
instance curveProjectionSucc_isFinite (n : ℕ) :
    IsFinite (curveProjectionSucc K C n).left := by
  change IsFinite (underlyingProjection (Spec (.of K)) (n + 1) C
    (curve_hasAffineOrbits_succ K C n))
  infer_instance

/-- The curve symmetric-power projection is surjective on points. -/
instance curveProjectionSucc_surjective (n : ℕ) :
    Surjective (curveProjectionSucc K C n).left := by
  change Surjective (underlyingProjection (Spec (.of K)) (n + 1) C
    (curve_hasAffineOrbits_succ K C n))
  exact underlyingProjection_surjectiveProperty (Spec (.of K)) (n + 1) C _

/-- Every positive-degree symmetric power of a challenge curve is
geometrically irreducible over the ground field. -/
instance curveSchemeSucc_geometricallyIrreducible (n : ℕ) :
    GeometricallyIrreducible (curveSchemeSucc K C n).hom := by
  letI : GeometricallyIrreducible
      ((curveProjectionSucc K C n).left ≫
        (curveSchemeSucc K C n).hom) := by
    rw [curveProjectionSucc_comp_structureMap K C n]
    infer_instance
  exact geometricallyIrreducible_of_comp_surjective
    (curveProjectionSucc K C n).left (curveSchemeSucc K C n).hom

/-- Every positive-degree symmetric power of a proper curve is universally
closed over the ground field. -/
instance curveSchemeSucc_universallyClosed (n : ℕ) :
    UniversallyClosed (curveSchemeSucc K C n).hom := by
  letI : UniversallyClosed
      ((curveProjectionSucc K C n).left ≫
        (curveSchemeSucc K C n).hom) := by
    rw [curveProjectionSucc_comp_structureMap K C n]
    infer_instance
  exact UniversallyClosed.of_comp_surjective
    (curveProjectionSucc K C n).left (curveSchemeSucc K C n).hom

end Curve

end MazurTorsion.AlgebraicGeometry.Jacobian.SymmetricPower

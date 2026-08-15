/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.SymmetricPower
import MazurTorsion.AlgebraicGeometry.Jacobian.UniversalEffectiveDivisor

/-!
# Finite quotients of the ordered universal incidence family

This file constructs the finite-group quotient of the ordered incidence
family on a challenge curve.  The key geometric input is an affine orbit
neighbourhood theorem for both the ordered ambient product and its invariant
closed subscheme.  It is obtained by mapping the curve finitely to `P¹`,
taking the product of that map with its componentwise power, and pulling back
affine orbit neighbourhoods from a projective target.

The quotient of the incidence family maps canonically to the quotient of the
ambient product.  The next representability step identifies that ambient
quotient with `C × Sym^d(C)` and proves that the descended closed family is a
relative effective Cartier divisor.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.UniversalEffectiveDivisor

open FiniteGroupQuotient
open PermutationPower
open ProjectiveFiniteOrbit

variable (S : Scheme.{u}) (d : ℕ) {X Y : Over S}

/-- A morphism `X ⟶ Y` induces a morphism on the ordered ambient products,
acting on the distinguished point and componentwise on the ordered power. -/
noncomputable def orderedAmbientMap (f : X ⟶ Y) :
    orderedAmbient S d X ⟶ orderedAmbient S d Y :=
  Limits.prod.map f (PermutationPower.map S (Fin d) f)

/-- The induced map on ordered ambient products is finite when the original
morphism is finite. -/
theorem orderedAmbientMap_isFinite (f : X ⟶ Y) [IsFinite f.left] :
    IsFinite (orderedAmbientMap S d f).left := by
  letI : IsFinite (PermutationPower.map S (Fin d) f).left :=
    PermutationPower.map_isFinite S (Fin d) f
  exact PermutationPower.binaryMap_isFinite S f
    (PermutationPower.map S (Fin d) f)

/-- The induced map on ordered ambient products commutes with coordinate
permutations. -/
theorem orderedAmbientMap_equivariant (f : X ⟶ Y)
    (g : Equiv.Perm (Fin d)) :
    (orderedAmbientAction S d X).hom g ≫ (orderedAmbientMap S d f).left =
      (orderedAmbientMap S d f).left ≫
        (orderedAmbientAction S d Y).hom g := by
  change
    (orderedAmbientPermutationHom S d X g ≫ orderedAmbientMap S d f).left =
      (orderedAmbientMap S d f ≫
        orderedAmbientPermutationHom S d Y g).left
  congr 1
  apply Limits.prod.hom_ext
  · simp [orderedAmbientMap, orderedAmbientPermutationHom]
  · simp only [orderedAmbientMap, orderedAmbientPermutationHom,
      Limits.prod.map_snd, Category.assoc]
    have h : PermutationPower.permutationHom S (Fin d) X g ≫
        PermutationPower.map S (Fin d) f =
      PermutationPower.map S (Fin d) f ≫
        PermutationPower.permutationHom S (Fin d) Y g := by
      apply Limits.Pi.hom_ext
      intro i
      simp only [Category.assoc, PermutationPower.map_comp_π,
        PermutationPower.permutationHom_comp_π]
      rw [← Category.assoc, PermutationPower.permutationHom_comp_π]
    simp only [← Category.assoc, Limits.prod.map_snd]
    rw [Category.assoc, h]
    simp

section Curve

variable (K : Type u) [Field K]

/-- The projective line as an object over `Spec K`. -/
noncomputable abbrev projectiveLine : Over (Spec (.of K)) :=
  Over.mk (TauCeti.AlgebraicGeometry.ProjectiveLine.structureMap K)

/-- The ordered ambient product for a positive power of `P¹` is projective. -/
theorem projectiveLineOrderedAmbient_isProjectiveFactorization (n : ℕ) :
    CoherentCohomology.ProjectiveSpace.IsProjectiveFactorization
      (orderedAmbient (Spec (.of K)) (n + 1) (projectiveLine K)).hom := by
  exact binaryProduct_isProjectiveFactorization K (projectiveLine K)
    (PermutationPower.power (Spec (.of K)) (Fin (n + 1))
      (projectiveLine K))
    (by
      change CoherentCohomology.ProjectiveSpace.IsProjectiveFactorization
        (TauCeti.AlgebraicGeometry.ProjectiveLine.structureMap K)
      rw [projectiveLine_structureMap_eq_toSpec K]
      exact CoherentCohomology.ProjectiveSpace.isProjectiveFactorization_toSpec K 1)
    (projectiveLinePower_isProjectiveFactorization K n)

/-- Every orbit of the action fixing the distinguished `P¹` coordinate and
permuting the remaining positive number of coordinates has an affine
neighbourhood. -/
theorem projectiveLineOrderedAmbient_hasAffineOrbit (n : ℕ) :
    HasAffineOrbit
      (orderedAmbientAction (Spec (.of K)) (n + 1) (projectiveLine K)) :=
  hasAffineOrbit_of_isProjectiveFactorization K _
    (projectiveLineOrderedAmbient_isProjectiveFactorization K n)

variable (C : Over (Spec (.of K)))
variable [GeometricallyIrreducible C.hom] [IsProper C.hom]
variable [SmoothOfRelativeDimension 1 C.hom]

/-- Every orbit in `C × C^(n+1)` for the action fixing the first coordinate
and permuting the remaining coordinates has an affine neighbourhood. -/
theorem curveOrderedAmbient_hasAffineOrbit_succ (n : ℕ) :
    HasAffineOrbit (orderedAmbientAction (Spec (.of K)) (n + 1) C) := by
  let f := FiniteMapToProjectiveLine.overHom K C
  letI : IsFinite f.left := FiniteMapToProjectiveLine.hom_isFinite K C
  letI : IsFinite (orderedAmbientMap (Spec (.of K)) (n + 1) f).left :=
    orderedAmbientMap_isFinite (Spec (.of K)) (n + 1) f
  exact hasAffineOrbit_of_equivariant_affine
    (orderedAmbientAction (Spec (.of K)) (n + 1) C)
    (orderedAmbientAction (Spec (.of K)) (n + 1) (projectiveLine K))
    (orderedAmbientMap (Spec (.of K)) (n + 1) f).left
    (projectiveLineOrderedAmbient_hasAffineOrbit K n)
    (orderedAmbientMap_equivariant (Spec (.of K)) (n + 1) f)

/-- The underlying ordered ambient product is separated as an absolute
scheme.  This supplies the affine-diagonal hypothesis of the quotient
construction. -/
instance curveOrderedAmbient_isSeparated (n : ℕ) :
    (orderedAmbient (Spec (.of K)) (n + 1) C).left.IsSeparated := by
  letI : IsAffineHom (terminal.from (Spec (.of K))) := by infer_instance
  letI : IsProper (orderedAmbient (Spec (.of K)) (n + 1) C).hom :=
    SymmetricPower.binaryProduct_isProper K C
      (PermutationPower.power (Spec (.of K)) (Fin (n + 1)) C)
      inferInstance inferInstance
  constructor
  rw [← terminal.comp_from
    (orderedAmbient (Spec (.of K)) (n + 1) C).hom]
  infer_instance

/-- Affine orbit neighbourhoods restrict from the ordered ambient product to
the invariant ordered incidence closed subscheme. -/
theorem curveOrderedIncidence_hasAffineOrbit_succ (n : ℕ) :
    HasAffineOrbit
      (orderedIncidenceAction (Spec (.of K)) (n + 1) C) := by
  exact hasAffineOrbit_of_equivariant_affine
    (orderedIncidenceAction (Spec (.of K)) (n + 1) C)
    (orderedAmbientAction (Spec (.of K)) (n + 1) C)
    (orderedIncidenceι (Spec (.of K)) (n + 1) C)
    (curveOrderedAmbient_hasAffineOrbit_succ K C n)
    (orderedIncidenceAction_comp_ι (Spec (.of K)) (n + 1) C)

/-- The ordered incidence closed subscheme is separated as an absolute
scheme. -/
instance curveOrderedIncidence_isSeparated (n : ℕ) :
    (orderedIncidence (Spec (.of K)) (n + 1) C).IsSeparated := by
  constructor
  rw [← terminal.comp_from
    (orderedIncidenceι (Spec (.of K)) (n + 1) C)]
  infer_instance

/-- The finite-group quotient of the ordered ambient product. -/
noncomputable def curveOrderedAmbientQuotientSucc (n : ℕ) : Scheme.{u} :=
  quotient (orderedAmbientAction (Spec (.of K)) (n + 1) C)
    (curveOrderedAmbient_hasAffineOrbit_succ K C n)

/-- The quotient projection from the ordered ambient product. -/
noncomputable def curveOrderedAmbientQuotientProjectionSucc (n : ℕ) :
    (orderedAmbient (Spec (.of K)) (n + 1) C).left ⟶
      curveOrderedAmbientQuotientSucc K C n :=
  quotientπ (orderedAmbientAction (Spec (.of K)) (n + 1) C)
    (curveOrderedAmbient_hasAffineOrbit_succ K C n)

instance curveOrderedAmbientQuotientProjectionSucc_isAffineHom (n : ℕ) :
    IsAffineHom (curveOrderedAmbientQuotientProjectionSucc K C n) := by
  exact quotientπ_isAffineHom
    (orderedAmbientAction (Spec (.of K)) (n + 1) C)
    (curveOrderedAmbient_hasAffineOrbit_succ K C n)

instance curveOrderedAmbientQuotientProjectionSucc_surjective (n : ℕ) :
    Surjective (curveOrderedAmbientQuotientProjectionSucc K C n) := by
  exact quotientπ_surjectiveProperty
    (orderedAmbientAction (Spec (.of K)) (n + 1) C)
    (curveOrderedAmbient_hasAffineOrbit_succ K C n)

/-- The finite-group quotient of the ordered incidence family. -/
noncomputable def curveOrderedIncidenceQuotientSucc (n : ℕ) : Scheme.{u} :=
  quotient (orderedIncidenceAction (Spec (.of K)) (n + 1) C)
    (curveOrderedIncidence_hasAffineOrbit_succ K C n)

/-- The quotient projection from the ordered incidence family. -/
noncomputable def curveOrderedIncidenceQuotientProjectionSucc (n : ℕ) :
    orderedIncidence (Spec (.of K)) (n + 1) C ⟶
      curveOrderedIncidenceQuotientSucc K C n :=
  quotientπ (orderedIncidenceAction (Spec (.of K)) (n + 1) C)
    (curveOrderedIncidence_hasAffineOrbit_succ K C n)

instance curveOrderedIncidenceQuotientProjectionSucc_isAffineHom (n : ℕ) :
    IsAffineHom (curveOrderedIncidenceQuotientProjectionSucc K C n) := by
  exact quotientπ_isAffineHom
    (orderedIncidenceAction (Spec (.of K)) (n + 1) C)
    (curveOrderedIncidence_hasAffineOrbit_succ K C n)

instance curveOrderedIncidenceQuotientProjectionSucc_surjective (n : ℕ) :
    Surjective (curveOrderedIncidenceQuotientProjectionSucc K C n) := by
  exact quotientπ_surjectiveProperty
    (orderedIncidenceAction (Spec (.of K)) (n + 1) C)
    (curveOrderedIncidence_hasAffineOrbit_succ K C n)

/-- The ordered incidence inclusion followed by the ambient quotient
projection is invariant under coordinate permutations. -/
theorem orderedIncidenceι_comp_ambientQuotientProjection_invariant
    (n : ℕ) (g : Equiv.Perm (Fin (n + 1))) :
    (orderedIncidenceAction (Spec (.of K)) (n + 1) C).hom g ≫
        orderedIncidenceι (Spec (.of K)) (n + 1) C ≫
          curveOrderedAmbientQuotientProjectionSucc K C n =
      orderedIncidenceι (Spec (.of K)) (n + 1) C ≫
        curveOrderedAmbientQuotientProjectionSucc K C n := by
  rw [← Category.assoc, orderedIncidenceAction_comp_ι,
    Category.assoc]
  exact congrArg
    (fun q ↦ orderedIncidenceι (Spec (.of K)) (n + 1) C ≫ q)
    (FiniteGroupQuotient.hom_quotientπ
      (orderedAmbientAction (Spec (.of K)) (n + 1) C)
      (curveOrderedAmbient_hasAffineOrbit_succ K C n) g)

/-- The quotient of the ordered incidence family maps canonically into the
quotient of the ordered ambient product. -/
noncomputable def curveIncidenceQuotientToAmbientQuotientSucc (n : ℕ) :
    curveOrderedIncidenceQuotientSucc K C n ⟶
      curveOrderedAmbientQuotientSucc K C n :=
  Classical.choose <| FiniteGroupQuotient.existsUnique_quotientπ_lift
    (orderedIncidenceAction (Spec (.of K)) (n + 1) C)
    (curveOrderedIncidence_hasAffineOrbit_succ K C n)
    (orderedIncidenceι (Spec (.of K)) (n + 1) C ≫
      curveOrderedAmbientQuotientProjectionSucc K C n)
    (orderedIncidenceι_comp_ambientQuotientProjection_invariant K C n)

/-- Pulling the descended incidence morphism back along the quotient
projection recovers the ordered incidence inclusion followed by the ambient
quotient projection. -/
@[reassoc]
theorem curveOrderedIncidenceQuotientProjection_comp_descendedι (n : ℕ) :
    curveOrderedIncidenceQuotientProjectionSucc K C n ≫
        curveIncidenceQuotientToAmbientQuotientSucc K C n =
      orderedIncidenceι (Spec (.of K)) (n + 1) C ≫
        curveOrderedAmbientQuotientProjectionSucc K C n :=
  (Classical.choose_spec <| FiniteGroupQuotient.existsUnique_quotientπ_lift
    (orderedIncidenceAction (Spec (.of K)) (n + 1) C)
    (curveOrderedIncidence_hasAffineOrbit_succ K C n)
    (orderedIncidenceι (Spec (.of K)) (n + 1) C ≫
      curveOrderedAmbientQuotientProjectionSucc K C n)
    (orderedIncidenceι_comp_ambientQuotientProjection_invariant K C n)).1

/-- Before quotienting the ambient product, take the symmetric quotient in
the ordered-power coordinate and leave the distinguished curve coordinate
unchanged. -/
noncomputable def curveOrderedAmbientToSymmetricProductSucc (n : ℕ) :
    (orderedAmbient (Spec (.of K)) (n + 1) C).left ⟶
      (C ⨯ SymmetricPower.curveSchemeSucc K C n).left :=
  (Limits.prod.map (𝟙 C) (SymmetricPower.curveProjectionSucc K C n)).left

/-- The map from the ordered ambient product to
`C × Sym^(n+1)(C)` is invariant under coordinate permutations. -/
theorem curveOrderedAmbientToSymmetricProductSucc_invariant
    (n : ℕ) (g : Equiv.Perm (Fin (n + 1))) :
    (orderedAmbientAction (Spec (.of K)) (n + 1) C).hom g ≫
        curveOrderedAmbientToSymmetricProductSucc K C n =
      curveOrderedAmbientToSymmetricProductSucc K C n := by
  change
    (orderedAmbientPermutationHom (Spec (.of K)) (n + 1) C g ≫
      Limits.prod.map (𝟙 C)
        (SymmetricPower.curveProjectionSucc K C n)).left =
    (Limits.prod.map (𝟙 C)
      (SymmetricPower.curveProjectionSucc K C n)).left
  congr 1
  apply Limits.prod.hom_ext
  · simp [orderedAmbientPermutationHom]
  · simp only [orderedAmbientPermutationHom, Category.assoc,
      Limits.prod.map_snd]
    rw [← Category.assoc, Limits.prod.map_snd, Category.assoc]
    have hq :
        PermutationPower.permutationHom (Spec (.of K)) (Fin (n + 1)) C g ≫
            SymmetricPower.curveProjectionSucc K C n =
          SymmetricPower.curveProjectionSucc K C n := by
      apply Over.OverMorphism.ext
      exact SymmetricPower.action_comp_projection
        (Spec (.of K)) (n + 1) C
        (SymmetricPower.curve_hasAffineOrbits_succ K C n) g
    rw [hq]

/-- The invariant ambient map descends to the finite-group quotient. -/
noncomputable def curveAmbientQuotientToSymmetricProductSucc (n : ℕ) :
    curveOrderedAmbientQuotientSucc K C n ⟶
      (C ⨯ SymmetricPower.curveSchemeSucc K C n).left :=
  Classical.choose <| FiniteGroupQuotient.existsUnique_quotientπ_lift
    (orderedAmbientAction (Spec (.of K)) (n + 1) C)
    (curveOrderedAmbient_hasAffineOrbit_succ K C n)
    (curveOrderedAmbientToSymmetricProductSucc K C n)
    (curveOrderedAmbientToSymmetricProductSucc_invariant K C n)

@[reassoc]
theorem curveOrderedAmbientQuotientProjection_comp_toSymmetricProduct
    (n : ℕ) :
    curveOrderedAmbientQuotientProjectionSucc K C n ≫
        curveAmbientQuotientToSymmetricProductSucc K C n =
      curveOrderedAmbientToSymmetricProductSucc K C n :=
  (Classical.choose_spec <| FiniteGroupQuotient.existsUnique_quotientπ_lift
    (orderedAmbientAction (Spec (.of K)) (n + 1) C)
    (curveOrderedAmbient_hasAffineOrbit_succ K C n)
    (curveOrderedAmbientToSymmetricProductSucc K C n)
    (curveOrderedAmbientToSymmetricProductSucc_invariant K C n)).1

/-- The descended incidence family as a morphism into
`C × Sym^(n+1)(C)`. -/
noncomputable def curveDescendedIncidenceιSucc (n : ℕ) :
    curveOrderedIncidenceQuotientSucc K C n ⟶
      (C ⨯ SymmetricPower.curveSchemeSucc K C n).left :=
  curveIncidenceQuotientToAmbientQuotientSucc K C n ≫
    curveAmbientQuotientToSymmetricProductSucc K C n

/-- Pullback of the descended incidence morphism to the ordered incidence
family is the original inclusion followed by quotienting the divisor
coordinate. -/
@[reassoc]
theorem curveOrderedIncidenceQuotientProjection_comp_descendedIncidenceι
    (n : ℕ) :
    curveOrderedIncidenceQuotientProjectionSucc K C n ≫
        curveDescendedIncidenceιSucc K C n =
      orderedIncidenceι (Spec (.of K)) (n + 1) C ≫
        curveOrderedAmbientToSymmetricProductSucc K C n := by
  rw [curveDescendedIncidenceιSucc, ← Category.assoc,
    curveOrderedIncidenceQuotientProjection_comp_descendedι,
    Category.assoc,
    curveOrderedAmbientQuotientProjection_comp_toSymmetricProduct]

end Curve

end MazurTorsion.AlgebraicGeometry.Jacobian.UniversalEffectiveDivisor

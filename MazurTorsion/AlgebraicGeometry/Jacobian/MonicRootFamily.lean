/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.PicardGroup
import MazurTorsion.AlgebraicGeometry.Jacobian.AdjoinRootBaseChange

/-!
# A monic equation as a finite flat Cartier family

For a monic polynomial `p : A[X]`, its root scheme is the closed subscheme of
the affine line over `A` cut out by `p`.  It is finite free over `Spec A`, of
constant rank `natDegree p`, and its defining equation is regular.  This file
packages those standard algebraic facts at scheme level.

The named downstream consumer is `UniversalEffectiveDivisorDescent`: after a
smooth curve is put in an étale coordinate, the universal incidence family is
locally a monic root family.  Keeping the result for an arbitrary monic
polynomial makes the subsequent base changes explicit and avoids tying the
Cartier calculation to universal coefficients.
-/

noncomputable section

universe u

open CategoryTheory Limits
open Polynomial
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.MonicRootFamily

section PrincipalIdeal

variable (B : Type u) [CommRing B] (q : B)

/-- Multiplication by a regular element identifies the ring with the
principal ideal it generates. -/
noncomputable def spanSingletonLinearEquiv (hq : IsRegular q) :
    B ≃ₗ[B] (Ideal.span {q} : Ideal B) :=
  (LinearEquiv.ofInjective (LinearMap.toSpanSingleton B B q)
      (LinearMap.ker_eq_bot.mp
        ((LinearMap.ker_toSpanSingleton_eq_bot_iff (R := B) (x := q)).mpr
          hq.2.mem_nonZeroDivisorsRight))).trans
    (LinearEquiv.ofEq
      (LinearMap.range (LinearMap.toSpanSingleton B B q))
      (Ideal.span {q})
      (LinearMap.range_toSpanSingleton q))

/-- A regular principal ideal is an invertible module. -/
theorem spanSingleton_invertible (hq : IsRegular q) :
    Module.Invertible B (Ideal.span {q} : Ideal B) :=
  Module.Invertible.congr (spanSingletonLinearEquiv B q hq)

end PrincipalIdeal

variable (A : Type u) [CommRing A] [Nontrivial A] (p : A[X])
  [hp : Fact p.Monic]

/-- The coordinate ring of the root scheme of `p`. -/
abbrev rootAlgebra := AdjoinRoot p

/-- The base-ring map into the root algebra. -/
noncomputable abbrev coefficientToRoot : A →+* rootAlgebra A p :=
  algebraMap A (rootAlgebra A p)

noncomputable instance rootAlgebra_free : Module.Free A (rootAlgebra A p) :=
  hp.out.free_adjoinRoot

noncomputable instance rootAlgebra_finite : Module.Finite A (rootAlgebra A p) :=
  hp.out.finite_adjoinRoot

noncomputable instance rootAlgebra_flat : Module.Flat A (rootAlgebra A p) := by
  infer_instance

/-- A monic root algebra has rank equal to the degree of its defining
polynomial. -/
theorem rootAlgebra_finrank :
    Module.finrank A (rootAlgebra A p) = p.natDegree := by
  simpa [rootAlgebra] using (AdjoinRoot.powerBasis' hp.out).finrank

/-- The quotient map from the ambient polynomial ring. -/
noncomputable abbrev ambientToRoot : A[X] →+* rootAlgebra A p :=
  AdjoinRoot.mk p

omit [Nontrivial A] hp in
theorem ambientToRoot_surjective :
    Function.Surjective (ambientToRoot A p) :=
  AdjoinRoot.mk_surjective

omit [Nontrivial A] hp in
/-- The root locus is cut out scheme-theoretically by exactly `p`. -/
theorem ambientToRoot_ker :
    RingHom.ker (ambientToRoot A p) = Ideal.span {p} :=
  Ideal.mk_ker

omit [Nontrivial A] in
/-- A monic equation is a non-zero-divisor, over an arbitrary commutative
base ring. -/
theorem polynomial_isRegular : IsRegular p := hp.out.isRegular

/-- The defining ideal of a monic root locus is invertible. -/
noncomputable instance definingIdeal_invertible :
    Module.Invertible A[X] (Ideal.span {p} : Ideal A[X]) :=
  spanSingleton_invertible A[X] p (polynomial_isRegular A p)

/-- Equivalently, the kernel ideal of the closed immersion is invertible. -/
noncomputable instance ambientToRoot_ker_invertible :
    Module.Invertible A[X] (RingHom.ker (ambientToRoot A p)) := by
  rw [ambientToRoot_ker A p]
  infer_instance

omit [Nontrivial A] in
theorem coefficientToRoot_finite : (coefficientToRoot A p).Finite := by
  rw [RingHom.finite_algebraMap]
  infer_instance

omit [Nontrivial A] in
theorem coefficientToRoot_flat : (coefficientToRoot A p).Flat := by
  rw [RingHom.flat_algebraMap_iff]
  infer_instance

/-- The affine root scheme over its coefficient base. -/
noncomputable def projection :
    Spec (.of (rootAlgebra A p)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (coefficientToRoot A p))

/-- The root scheme as a closed subscheme of the affine line over `A`. -/
noncomputable def locusι :
    Spec (.of (rootAlgebra A p)) ⟶ Spec (.of A[X]) :=
  Spec.map (CommRingCat.ofHom (ambientToRoot A p))

/-- The structure map of the ambient affine line. -/
noncomputable def ambientProjection : Spec (.of A[X]) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* A[X]))

omit [Nontrivial A] hp in
theorem locusι_comp_ambientProjection :
    locusι A p ≫ ambientProjection A = projection A p := by
  rw [locusι, ambientProjection, projection, ← Spec.map_comp]
  congr 1

instance locusι_isClosedImmersion : IsClosedImmersion (locusι A p) := by
  apply IsClosedImmersion.spec_of_surjective
  exact ambientToRoot_surjective A p

instance projection_isFinite : IsFinite (projection A p) := by
  change IsFinite (Spec.map (CommRingCat.ofHom (coefficientToRoot A p)))
  rw [IsFinite.SpecMap_iff]
  exact coefficientToRoot_finite A p

instance projection_flat : Flat (projection A p) := by
  change Flat (Spec.map (CommRingCat.ofHom (coefficientToRoot A p)))
  rw [Flat.SpecMap_iff]
  exact coefficientToRoot_flat A p

/-- The affine monic root morphism has constant rank equal to the degree of
its equation. -/
theorem projection_finrank :
    (projection A p).finrank = fun _ ↦ p.natDegree := by
  ext x
  rw [projection]
  change (Spec.map (CommRingCat.ofHom
    (algebraMap A (rootAlgebra A p)))).finrank x = p.natDegree
  calc
    _ = Module.rankAtStalk (rootAlgebra A p) x :=
      Scheme.Hom.finrank_SpecMap_algebraMap A (rootAlgebra A p) x
    _ = Module.finrank A (rootAlgebra A p) := by
      exact congrFun (Module.rankAtStalk_eq_finrank_of_free
        (R := A) (M := rootAlgebra A p)) x
    _ = p.natDegree := rootAlgebra_finrank A p

variable {Y : Scheme.{u}}

/-- An arbitrary scheme base change of the monic root family. -/
noncomputable abbrev baseChangeProjection
    (g : Y ⟶ Spec (.of A)) :
    pullback (projection A p) g ⟶ Y :=
  pullback.snd (projection A p) g

private noncomputable def baseChangeIsoMappedRootExplicit
    (B : Type u) [CommRing B] [Algebra A B] :
    pullback
        (Spec.map (CommRingCat.ofHom
          (algebraMap A (AdjoinRoot p))))
        (Spec.map (CommRingCat.ofHom (algebraMap A B))) ≅
      Spec (.of (AdjoinRoot (p.map (algebraMap A B)))) :=
  pullbackSymmetry
      (Spec.map (CommRingCat.ofHom
        (algebraMap A (AdjoinRoot p))))
      (Spec.map (CommRingCat.ofHom (algebraMap A B))) ≪≫
    pullbackSpecIso A B (AdjoinRoot p) ≪≫
    (Scheme.Spec.mapIso
      (AdjoinRootBaseChange.equiv A B p).toRingEquiv.toCommRingCatIso.op).symm

/-- The affine base change of a monic root scheme is the root scheme of the
coefficient-wise mapped polynomial. -/
noncomputable def baseChangeIsoMappedRoot
    (B : Type u) [CommRing B] [Algebra A B] :
    pullback (projection A p)
        (Spec.map (CommRingCat.ofHom (algebraMap A B))) ≅
      Spec (.of (AdjoinRoot (p.map (algebraMap A B)))) :=
  baseChangeIsoMappedRootExplicit A p B

omit [Nontrivial A] hp in
/-- The explicit base-change isomorphism carries the mapped-root projection
to the second projection of the scheme pullback. -/
@[reassoc]
theorem baseChangeIsoMappedRoot_inv_comp_snd
    (B : Type u) [CommRing B] [Algebra A B] :
    (baseChangeIsoMappedRoot A p B).inv ≫
        pullback.snd (projection A p)
          (Spec.map (CommRingCat.ofHom (algebraMap A B))) =
      projection B (p.map (algebraMap A B)) := by
  change (baseChangeIsoMappedRootExplicit A p B).inv ≫
      pullback.snd
        (Spec.map (CommRingCat.ofHom
          (algebraMap A (AdjoinRoot p))))
        (Spec.map (CommRingCat.ofHom (algebraMap A B))) =
    Spec.map (CommRingCat.ofHom
      (algebraMap B (AdjoinRoot (p.map (algebraMap A B)))))
  rw [baseChangeIsoMappedRootExplicit]
  simp only [Iso.trans_inv, Category.assoc,
    pullbackSymmetry_inv_comp_snd]
  change (Scheme.Spec.mapIso
      (AdjoinRootBaseChange.equiv A B p).toRingEquiv.toCommRingCatIso.op).hom ≫
    (pullbackSpecIso A B (AdjoinRoot p)).inv ≫
      pullback.fst
        (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        (Spec.map (CommRingCat.ofHom
          (algebraMap A (AdjoinRoot p)))) = _
  erw [pullbackSpecIso_inv_fst]
  simp only [Functor.mapIso_hom, Iso.op_hom]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, Spec.map_inj]
  ext b
  exact (AdjoinRootBaseChange.equiv A B p).commutes b

instance baseChangeProjection_isFinite (g : Y ⟶ Spec (.of A)) :
    IsFinite (baseChangeProjection A p g) := by
  infer_instance

instance baseChangeProjection_flat (g : Y ⟶ Spec (.of A)) :
    Flat (baseChangeProjection A p g) := by
  infer_instance

/-- Constant degree is preserved by arbitrary base change. -/
theorem baseChangeProjection_finrank (g : Y ⟶ Spec (.of A)) :
    (baseChangeProjection A p g).finrank = fun _ ↦ p.natDegree := by
  ext y
  rw [baseChangeProjection, Scheme.Hom.finrank_pullback_snd]
  exact congrFun (projection_finrank A p) (g y)

end MazurTorsion.AlgebraicGeometry.Jacobian.MonicRootFamily

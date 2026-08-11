/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Algebra.Category.Ring.Under.Limits
import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.ConstantPrimeFiniteEtaleCoverFppfHOne

/-!
# Effective torsors for represented constant-prime fppf cocycles over `Spec ℤ`

This leaf module is reserved for the effective-descent step from an arbitrary represented
constant-prime fppf cocycle to its finite-etale torsor algebra and the resulting contraction.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.PresheafOfGroups

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme.ConstantPrimeEtale

universe u

namespace FaithfullyFlatAlgebraDescent

variable (R S : CommRingCat.{u}) [Algebra R S]

/-- Bijectivity descends across a categorical pushout whose left edge is faithfully flat.

This is the categorical form of `RingHom.FaithfullyFlat.codescendsAlong_bijective`; it avoids
identifying a categorical pushout object definitionally with a tensor product. -/
lemma bijective_of_isPushout_of_faithfullyFlat
    {R S R' S' : CommRingCat.{u}}
    {f : R ⟶ S} {g : R ⟶ R'} {inl : S ⟶ S'} {inr : R' ⟶ S'}
    (hsq : IsPushout f g inl inr) (hg : g.hom.FaithfullyFlat)
    (hinr : Function.Bijective inr.hom) : Function.Bijective f.hom := by
  algebraize [f.hom, g.hom, inl.hom, inr.hom, inl.hom.comp f.hom]
  have : IsScalarTower R R' S' :=
    .of_algebraMap_eq' <| congr($(hsq.1.1).hom)
  have : Algebra.IsPushout R S R' S' :=
    CommRingCat.isPushout_iff_isPushout.mp hsq
  exact RingHom.FaithfullyFlat.codescendsAlong_bijective hg hinr

/-- The naturality square for scalar extension in `Under R` is itself a pushout square. -/
lemma isPushout_pushout_map {R S : CommRingCat.{u}} (f : R ⟶ S)
    {A B : Under R} (g : A ⟶ B) :
    IsPushout g.right (pushout.inl A.hom f) (pushout.inl B.hom f)
      ((Under.pushout f).map g).right := by
  have hinl :
      pushout.inl A.hom f ≫ ((Under.pushout f).map g).right =
        g.right ≫ pushout.inl B.hom f := by
    change pushout.inl A.hom f ≫
      pushout.desc (g.right ≫ pushout.inl B.hom f) (pushout.inr B.hom f) _ = _
    exact pushout.inl_desc _ _ _
  have hinr :
      pushout.inr A.hom f ≫ ((Under.pushout f).map g).right =
        pushout.inr B.hom f := by
    change pushout.inr A.hom f ≫
      pushout.desc (g.right ≫ pushout.inl B.hom f) (pushout.inr B.hom f) _ = _
    exact pushout.inr_desc _ _ _
  refine (IsPushout.of_top ?_ hinl
    (IsPushout.of_hasPushout A.hom f).flip).flip
  rw [g.w, hinr]
  exact (IsPushout.of_hasPushout B.hom f).flip

/-- Faithfully-flat scalar extension reflects isomorphisms of commutative algebras. -/
lemma pushoutReflectsIsomorphisms
    (hf : (algebraMap R S).FaithfullyFlat) :
    (Under.pushout (CommRingCat.ofHom (algebraMap R S))).ReflectsIsomorphisms := by
  let f : R ⟶ S := CommRingCat.ofHom (algebraMap R S)
  refine ⟨fun {A B} g hg ↦ ?_⟩
  haveI : IsIso ((Under.pushout f).map g) := hg
  have hmap : Function.Bijective ((Under.pushout f).map g).right := by
    change Function.Bijective
      ((CategoryTheory.Under.forget S).map ((Under.pushout f).map g))
    rw [← ConcreteCategory.isIso_iff_bijective]
    infer_instance
  have hff : (pushout.inl A.hom f).hom.FaithfullyFlat :=
    RingHom.FaithfullyFlat.isStableUnderBaseChange.pushout_inl
      RingHom.FaithfullyFlat.respectsIso A.hom f hf
  have hg' : Function.Bijective g.right :=
    bijective_of_isPushout_of_faithfullyFlat
      (isPushout_pushout_map f g) hff hmap
  rw [← isIso_iff_of_reflects_iso g (CategoryTheory.Under.forget R),
    ConcreteCategory.isIso_iff_bijective]
  exact hg'

end FaithfullyFlatAlgebraDescent

end AlgebraicGeometry.FiniteFlatCommGroupScheme.ConstantPrimeEtale

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Rational sections of smooth relative curves

This file packages a rational section of an integral smooth relative curve
and proves that its image is not the generic point. The proof needs no
properness: the section is a closed immersion, and a generic closed image
would make the curve isomorphic to the base point. Standard-smooth Kähler
differentials then contradict relative dimension one.

The result is shared by the divisor/Picard and degree-one formal-immersion
lanes. No Picard or modular-curve construction is imported here.
-/

namespace MazurTorsion.AlgebraicGeometry

universe u

open _root_.AlgebraicGeometry
open CategoryTheory

/-- A rational section of an integral smooth relative curve. -/
structure SmoothCurveRationalSection
    (K : Type u) [Field K]
    (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 pi] where
  /-- The represented rational point. -/
  hom : Spec (.of K) ⟶ X
  /-- The rational point is a section of the structure morphism. -/
  hom_comp : hom ≫ pi = 𝟙 _

namespace SmoothCurveRationalSection

variable {K : Type u} [Field K]
variable {X : Scheme.{u}} [IsIntegral X]
variable {pi : X ⟶ Spec (.of K)} [SmoothOfRelativeDimension 1 pi]

/-- A section of an integral smooth relative curve cannot land at its generic
point. The section is a closed immersion. If its image were generic, that
closed image would be all of the integral curve, making both the section and
the structure map isomorphisms. A relative-dimension-one standard-smooth
chart would then have Kähler differentials of ranks one and zero. -/
theorem ne_generic (x : SmoothCurveRationalSection K X pi) :
    x.hom (IsLocalRing.closedPoint K) ≠ genericPoint X := by
  letI : IsClosedImmersion x.hom :=
    isClosedImmersion_of_comp_eq_id pi x.hom x.hom_comp
  intro hgeneric
  have hrange : Set.range x.hom = Set.univ := by
    have hclosed : IsClosed (Set.range x.hom) :=
      x.hom.isClosedEmbedding.isClosed_range
    have hrangeSingleton : Set.range x.hom = {genericPoint X} := by
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        rw [Set.mem_singleton_iff]
        exact (congrArg x.hom (Subsingleton.elim z
          (IsLocalRing.closedPoint K))).trans hgeneric
      · intro hy
        rw [Set.mem_singleton_iff] at hy
        exact ⟨IsLocalRing.closedPoint K, hgeneric.trans hy.symm⟩
    calc
      Set.range x.hom = closure (Set.range x.hom) :=
        hclosed.closure_eq.symm
      _ = closure ({genericPoint X} : Set X) :=
        congrArg closure hrangeSingleton
      _ = Set.univ := genericPoint_closure X
  letI : Surjective x.hom := ⟨Set.range_eq_univ.mp hrange⟩
  letI : Subsingleton X :=
    Function.Surjective.subsingleton x.hom.surjective
  letI : IsIso x.hom :=
    isIso_of_isClosedImmersion_of_surjective x.hom
  haveI : IsIso (x.hom ≫ pi) := by
    rw [x.hom_comp]
    infer_instance
  letI : IsIso pi := IsIso.of_isIso_comp_left x.hom pi
  obtain ⟨U, -, V, -, hx, e, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := 1) (f := pi) (x.hom (IsLocalRing.closedPoint K))
  have hUtop : U = ⊤ := by
    have hfx : pi (x.hom (IsLocalRing.closedPoint K)) ∈ U := e hx
    apply top_unique
    intro y _
    exact Subsingleton.elim y
      (pi (x.hom (IsLocalRing.closedPoint K))) ▸ hfx
  have hVtop : V = ⊤ := by
    apply top_unique
    intro y _
    simpa only [Subsingleton.elim y
      (x.hom (IsLocalRing.closedPoint K))] using hx
  subst U
  subst V
  have hstdTop :
      RingHom.IsStandardSmoothOfRelativeDimension 1 pi.appTop.hom := by
    rw [Scheme.Hom.appTop, ← Scheme.Hom.appLE_eq_app]
    exact (pi.appLE_congr e rfl (by simp)
      (fun f ↦ RingHom.IsStandardSmoothOfRelativeDimension 1 f.hom)).mp hstd
  letI : IsIso pi.appTop := by
    apply Scheme.Hom.isIso_app pi ⊤
    rw [Scheme.Hom.opensRange_of_isIso]
  letI : Algebra Γ(Spec (.of K), ⊤) Γ(X, ⊤) :=
    pi.appTop.hom.toAlgebra
  letI : Algebra.IsStandardSmoothOfRelativeDimension 1
      Γ(Spec (.of K), ⊤) Γ(X, ⊤) := hstdTop.toAlgebra
  have hbij : Function.Bijective pi.appTop.hom :=
    (ConcreteCategory.isIso_iff_bijective pi.appTop).mp inferInstance
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0
      Γ(Spec (.of K), ⊤) Γ(X, ⊤) :=
    Algebra.IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective hbij
  have hzero :=
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
      (R := Γ(Spec (.of K), ⊤)) (S := Γ(X, ⊤)) 0
  have hone :=
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
      (R := Γ(Spec (.of K), ⊤)) (S := Γ(X, ⊤)) 1
  rw [hzero] at hone
  norm_num at hone

end SmoothCurveRationalSection

end MazurTorsion.AlgebraicGeometry

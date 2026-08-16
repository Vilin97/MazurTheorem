/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.MonicRootFamily

/-!
# Products of affine-line section ideals

A finite family of sections of an affine line over a ring `B` has equations
`X - xᵢ`.  Their scheme-theoretic union is cut out by the product of those
linear equations, including repeated factors.  The quotient is therefore a
monic root algebra, finite free of rank the number of sections.

The named downstream consumer is
`GeometricAssignedAffineSupportCoproduct`, where independently varying
occurrence coordinates become sections on a common affine line.
-/

noncomputable section

universe u v

open Polynomial

namespace MazurTorsion.AlgebraicGeometry.Jacobian.SectionProductRootAlgebra

variable (B : Type u) [CommRing B] [Nontrivial B]
variable (ι : Type v) [Fintype ι]

/-- Extension of ideals preserves finite products.  This packages the ideal
map as a monoid homomorphism for the section-product consumers below. -/
theorem ideal_map_fintype_prod
    {A D κ : Type*} [CommRing A] [CommRing D] [Fintype κ]
    (f : A →+* D) (I : κ → Ideal A) :
    Ideal.map f (∏ i, I i) = ∏ i, Ideal.map f (I i) := by
  let Φ : Ideal A →* Ideal D :=
    { toFun := Ideal.map f
      map_one' := by
        simpa only [Ideal.one_eq_top] using Ideal.map_top f
      map_mul' := fun J L ↦ Ideal.map_mul f J L }
  change Φ (∏ i, I i) = ∏ i, Φ (I i)
  exact map_prod Φ I Finset.univ

/-- Multiplying ideals supported in one component of a finite product can
be performed componentwise.  The `dite` transports the owner ideal across
the equality of component indices; all non-owner components contribute the
unit ideal. -/
theorem pi_fintype_prod_single
    {k : Type*} [Fintype k] [DecidableEq k]
    {R : k → Type*} [∀ a, CommRing (R a)]
    {t : k → Type*} [∀ a, Fintype (t a)]
    (I : ∀ a, t a → Ideal (R a)) :
    (∏ a, ∏ i, Ideal.pi (fun b ↦
      if h : b = a then h ▸ I a i else ⊤)) =
      Ideal.pi (fun a ↦ ∏ i, I a i) := by
  classical
  apply (Ideal.piOrderIso (R := R)).injective
  funext b
  let e := Pi.evalRingHom R b
  let φ : Ideal (∀ a, R a) →* Ideal (R b) :=
    { toFun := Ideal.map e
      map_one' := by
        simpa only [Ideal.one_eq_top] using Ideal.map_top e
      map_mul' := fun J L ↦ Ideal.map_mul e J L }
  change φ (∏ a, ∏ i, Ideal.pi (fun b ↦
      if h : b = a then h ▸ I a i else ⊤)) =
    φ (Ideal.pi (fun a ↦ ∏ i, I a i))
  rw [map_prod]
  simp_rw [map_prod]
  change (∏ a, ∏ i, Ideal.map e (Ideal.pi (fun b ↦
      if h : b = a then h ▸ I a i else ⊤))) =
    Ideal.map e (Ideal.pi (fun a ↦ ∏ i, I a i))
  rw [Ideal.map_evalRingHom_pi]
  rw [Fintype.prod_eq_single b]
  · dsimp only [φ, e]
    simp only [Ideal.map_evalRingHom_pi, dif_pos]
  · intro a ha
    dsimp only [φ, e]
    simp only [Ideal.map_evalRingHom_pi]
    simp [ha.symm]

/-- Quotienting a finite product ring by the product of component ideals is
the product of the component quotients. -/
noncomputable def piIdealQuotientAlgEquiv
    {R₀ κ : Type*} {A : κ → Type*}
    [CommRing R₀] [Finite κ] [∀ i, CommRing (A i)]
    [∀ i, Algebra R₀ (A i)] (I : ∀ i, Ideal (A i)) :
    ((∀ i, A i) ⧸ Ideal.pi I) ≃ₐ[R₀] ∀ i, A i ⧸ I i := by
  let q : (∀ i, A i) →ₐ[R₀] ∀ i, A i ⧸ I i :=
    AlgHom.pi (fun i ↦
      (Ideal.Quotient.mkₐ R₀ (I i)).comp (Pi.evalAlgHom R₀ A i))
  have hq : ∀ x, x ∈ Ideal.pi I → q x = 0 := by
    intro x hx
    ext i
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hx i)
  let f := Ideal.Quotient.liftₐ (Ideal.pi I) q hq
  apply AlgEquiv.ofBijective f
  constructor
  · change Function.Injective
      (Ideal.Quotient.lift (Ideal.pi I) q.toRingHom hq)
    rw [Ideal.injective_lift_iff]
    ext x
    simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, Ideal.mem_pi]
    constructor
    · intro hx i
      have hi := congrFun hx i
      exact Ideal.Quotient.eq_zero_iff_mem.mp hi
    · intro hx
      ext i
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hx i)
  · intro y
    choose x hx using fun i ↦ Ideal.Quotient.mk_surjective (y i)
    refine ⟨Ideal.Quotient.mk (Ideal.pi I) x, ?_⟩
    ext i
    exact hx i

/-- The product of the linear equations of a finite family of points of the
affine line. -/
noncomputable def sectionPolynomial (x : ι → B) : B[X] :=
  ∏ i, (X - C (x i))

omit [Nontrivial B] in
/-- The product of linear section equations is monic. -/
theorem sectionPolynomial_monic (x : ι → B) :
    (sectionPolynomial B ι x).Monic := by
  classical
  exact monic_prod_of_monic Finset.univ _
    (fun i _ ↦ monic_X_sub_C (x i))

/-- The degree of the section product counts occurrences, so coincident
sections still contribute their full multiplicity. -/
theorem sectionPolynomial_natDegree (x : ι → B) :
    (sectionPolynomial B ι x).natDegree = Fintype.card ι := by
  classical
  rw [sectionPolynomial,
    natDegree_prod_of_monic Finset.univ
      (fun i ↦ X - C (x i))
      (fun i _ ↦ monic_X_sub_C (x i))]
  simp

/-- The section product packaged together with its degree. -/
noncomputable def sectionPolynomialMonicDegreeEq (x : ι → B) :
    Polynomial.MonicDegreeEq B (Fintype.card ι) :=
  Polynomial.MonicDegreeEq.mk (sectionPolynomial B ι x)
    (sectionPolynomial_monic B ι x)
    (sectionPolynomial_natDegree B ι x)

/-- The product of the individual graph ideals. -/
noncomputable def graphProductIdeal (x : ι → B) : Ideal B[X] :=
  ∏ i, Ideal.span {X - C (x i)}

omit [Nontrivial B] in
/-- A product of principal graph ideals is generated by the product of the
corresponding linear equations. -/
theorem graphProductIdeal_eq_span (x : ι → B) :
    graphProductIdeal B ι x = Ideal.span {sectionPolynomial B ι x} := by
  classical
  rw [graphProductIdeal, Ideal.prod_span_singleton]
  rfl

/-- The quotient by the complete graph product. -/
abbrev graphProductQuotient (x : ι → B) :=
  B[X] ⧸ graphProductIdeal B ι x

/-- The graph-product quotient is the monic root algebra of the product
polynomial. -/
noncomputable def graphProductQuotientEquivRoot (x : ι → B) :
    graphProductQuotient B ι x ≃ₐ[B]
      AdjoinRoot (sectionPolynomial B ι x) :=
  Ideal.quotientEquivAlgOfEq B (graphProductIdeal_eq_span B ι x)

noncomputable instance graphProductQuotient_free (x : ι → B) :
    Module.Free B (graphProductQuotient B ι x) := by
  letI : Fact (sectionPolynomial B ι x).Monic :=
    ⟨sectionPolynomial_monic B ι x⟩
  exact Module.Free.of_equiv
    (graphProductQuotientEquivRoot B ι x).symm.toLinearEquiv

noncomputable instance graphProductQuotient_finite (x : ι → B) :
    Module.Finite B (graphProductQuotient B ι x) := by
  letI : Fact (sectionPolynomial B ι x).Monic :=
    ⟨sectionPolynomial_monic B ι x⟩
  exact Module.Finite.equiv
    (graphProductQuotientEquivRoot B ι x).symm.toLinearEquiv

noncomputable instance graphProductQuotient_flat (x : ι → B) :
    Module.Flat B (graphProductQuotient B ι x) := by
  infer_instance

/-- The graph-product quotient has rank equal to the number of indexed
sections. -/
theorem graphProductQuotient_finrank (x : ι → B) :
    Module.finrank B (graphProductQuotient B ι x) = Fintype.card ι := by
  letI : Fact (sectionPolynomial B ι x).Monic :=
    ⟨sectionPolynomial_monic B ι x⟩
  rw [(graphProductQuotientEquivRoot B ι x).toLinearEquiv.finrank_eq]
  rw [MonicRootFamily.rootAlgebra_finrank]
  exact sectionPolynomial_natDegree B ι x

end MazurTorsion.AlgebraicGeometry.Jacobian.SectionProductRootAlgebra

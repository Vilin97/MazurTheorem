/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.AlgebraicGeometry.AffineSpace
import MazurTorsion.AlgebraicGeometry.Jacobian.SectionProductRootAlgebra

/-!
# Finite products of sections on a relative affine line

Over an affine scheme `S`, the global sections of relative affine space are
the expected multivariable polynomial ring.  In one variable, the kernel of
the section with value `x` is therefore `(X - x)`.  A finite product of such
kernels has quotient a monic root algebra, finite free with rank equal to
the number of indexed sections.

The named downstream consumer is
`GeometricAssignedAffineSupportCoproduct`, which transports its common
base-changed coordinate line and occurrence graphs to this standard model.
-/

noncomputable section

universe u v

open CategoryTheory
open Polynomial
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.AffineLineSectionProduct

/-- The algebra structure on affine-space sections induced by its structural
morphism to the base. -/
noncomputable instance affineSpaceSectionsAlgebra
    (n : Type u) (S : Scheme.{u}) :
    Algebra Γ(S, ⊤) Γ(𝔸(n; S), ⊤) :=
  (𝔸(n; S) ↘ S).appTop.hom.toAlgebra

/-- Polynomial coordinates identify the global sections of affine space
over an affine scheme. -/
noncomputable def coordinateAlgEquiv
    (n : Type u) (S : Scheme.{u}) [IsAffine S] :
    MvPolynomial n Γ(S, ⊤) ≃ₐ[Γ(S, ⊤)] Γ(𝔸(n; S), ⊤) := by
  let f : MvPolynomial n Γ(S, ⊤) →ₐ[Γ(S, ⊤)] Γ(𝔸(n; S), ⊤) :=
    MvPolynomial.aeval (AffineSpace.coord S)
  apply AlgEquiv.ofBijective f
  let e := AffineSpace.isoOfIsAffine n S
  have he : Function.Bijective e.hom.appTop.hom := by
    exact ConcreteCategory.bijective_of_isIso
      (e.hom.app (⊤ : (Spec
        (CommRingCat.of (MvPolynomial n Γ(S, ⊤)))).Opens))
  have hg : Function.Bijective
      (Scheme.ΓSpecIso
        (CommRingCat.of (MvPolynomial n Γ(S, ⊤)))).hom.hom :=
    ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso
        (CommRingCat.of (MvPolynomial n Γ(S, ⊤)))).hom
  apply (Function.Bijective.of_comp_iff f hg).mp
  change Function.Bijective
    (f.toRingHom.comp
      (Scheme.ΓSpecIso
        (CommRingCat.of (MvPolynomial n Γ(S, ⊤)))).hom.hom)
  have hcomp : f.toRingHom.comp
      (Scheme.ΓSpecIso
        (CommRingCat.of (MvPolynomial n Γ(S, ⊤)))).hom.hom =
      e.hom.appTop.hom := by
    rw [AffineSpace.isoOfIsAffine_hom_appTop]
    rfl
  rw [hcomp]
  exact he

theorem coordinateAlgEquiv_X
    (n : Type u) (S : Scheme.{u}) [IsAffine S] (i : n) :
    coordinateAlgEquiv n S (MvPolynomial.X i) =
      AffineSpace.coord S i := by
  rw [coordinateAlgEquiv, AlgEquiv.ofBijective_apply]
  exact MvPolynomial.aeval_X (AffineSpace.coord S) i

theorem coordinateAlgEquiv_C
    (n : Type u) (S : Scheme.{u}) [IsAffine S] (b : Γ(S, ⊤)) :
    coordinateAlgEquiv n S (MvPolynomial.C b) =
      (𝔸(n; S) ↘ S).appTop b := by
  rw [coordinateAlgEquiv, AlgEquiv.ofBijective_apply]
  exact MvPolynomial.aeval_C (AffineSpace.coord S) b

variable (n : Type u) [Unique n]
variable (S : Scheme.{u}) [IsAffine S]

/-- In one variable, the global coordinate equivalence followed by the
canonical unique-variable equivalence gives an ordinary polynomial ring. -/
noncomputable def polynomialCoordinateAlgEquiv :
    Γ(𝔸(n; S), ⊤) ≃ₐ[Γ(S, ⊤)] Polynomial Γ(S, ⊤) := by
  exact (coordinateAlgEquiv n S).symm.trans
    (MvPolynomial.uniqueAlgEquiv Γ(S, ⊤) n)

theorem polynomialCoordinateAlgEquiv_symm_C (b : Γ(S, ⊤)) :
    (polynomialCoordinateAlgEquiv n S).symm (Polynomial.C b) =
      (𝔸(n; S) ↘ S).appTop b := by
  change (coordinateAlgEquiv n S)
    ((MvPolynomial.uniqueAlgEquiv Γ(S, ⊤) n).symm
      (Polynomial.C b)) = _
  rw [show (MvPolynomial.uniqueAlgEquiv Γ(S, ⊤) n).symm
      (Polynomial.C b) = MvPolynomial.C b by
    change Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X default)
      (Polynomial.C b) = _
    rw [Polynomial.eval₂_C]]
  exact coordinateAlgEquiv_C n S b

theorem polynomialCoordinateAlgEquiv_symm_X :
    (polynomialCoordinateAlgEquiv n S).symm Polynomial.X =
      AffineSpace.coord S default := by
  change (coordinateAlgEquiv n S)
    ((MvPolynomial.uniqueAlgEquiv Γ(S, ⊤) n).symm Polynomial.X) = _
  rw [show (MvPolynomial.uniqueAlgEquiv Γ(S, ⊤) n).symm
      Polynomial.X = MvPolynomial.X default by
    change Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X default)
      Polynomial.X = _
    rw [Polynomial.eval₂_X]]
  exact coordinateAlgEquiv_X n S default

/-- The section of the relative affine line with prescribed global value. -/
noncomputable def lineSection (x : Γ(S, ⊤)) :
    S ⟶ 𝔸(n; S) :=
  AffineSpace.homOfVector (𝟙 S) (fun _ ↦ x)

omit [Unique n] [IsAffine S] in
@[reassoc]
theorem section_comp_projection (x : Γ(S, ⊤)) :
    lineSection n S x ≫ (𝔸(n; S) ↘ S) = 𝟙 S :=
  AffineSpace.homOfVector_over (𝟙 S) (fun _ ↦ x)

omit [Unique n] [IsAffine S] in
theorem section_appTop_coordinate (x : Γ(S, ⊤)) (i : n) :
    (lineSection n S x).appTop (AffineSpace.coord S i) = x :=
  AffineSpace.homOfVector_appTop_coord (𝟙 S) (fun _ ↦ x) i

/-- After the polynomial coordinate equivalence, the ring map of a section
is ordinary polynomial evaluation. -/
theorem section_appTop_comp_polynomialCoordinateAlgEquiv_symm
    (x : Γ(S, ⊤)) :
    (lineSection n S x).appTop.hom.comp
        (polynomialCoordinateAlgEquiv n S).symm.toRingEquiv.toRingHom =
      Polynomial.evalRingHom x := by
  apply Polynomial.ringHom_ext
  · intro b
    simp only [RingHom.comp_apply]
    rw [show
      (polynomialCoordinateAlgEquiv n S).symm.toRingEquiv.toRingHom
          (Polynomial.C b) = (𝔸(n; S) ↘ S).appTop b by
        exact polynomialCoordinateAlgEquiv_symm_C n S b]
    rw [show Polynomial.evalRingHom x (Polynomial.C b) = b by simp]
    have hcomp := congrArg CommRingCat.Hom.hom
      (Scheme.Hom.comp_appTop (lineSection n S x) (𝔸(n; S) ↘ S))
    rw [section_comp_projection, Scheme.Hom.id_appTop] at hcomp
    have hb := congrArg
      (fun f : Γ(S, ⊤) →+* Γ(S, ⊤) ↦ f b) hcomp
    simpa only [CommRingCat.comp_apply,
      ConcreteCategory.id_apply] using hb.symm
  · simp only [RingHom.comp_apply]
    rw [show Polynomial.evalRingHom x Polynomial.X = x by simp]
    rw [show
      (polynomialCoordinateAlgEquiv n S).symm.toRingEquiv.toRingHom
          Polynomial.X = AffineSpace.coord S default by
        exact polynomialCoordinateAlgEquiv_symm_X n S]
    change (lineSection n S x).appTop (AffineSpace.coord S default) = x
    exact section_appTop_coordinate n S x default

/-- Under polynomial coordinates, the kernel ideal of a section is generated
by its linear equation. -/
theorem map_section_ker (x : Γ(S, ⊤)) :
    Ideal.map (polynomialCoordinateAlgEquiv n S).toRingEquiv.toRingHom
        (RingHom.ker (lineSection n S x).appTop.hom) =
      Ideal.span {Polynomial.X - Polynomial.C x} := by
  let e := polynomialCoordinateAlgEquiv n S
  calc
    Ideal.map e.toRingEquiv.toRingHom
        (RingHom.ker (lineSection n S x).appTop.hom) =
        Ideal.comap e.symm.toRingEquiv.toRingHom
          (RingHom.ker (lineSection n S x).appTop.hom) :=
      Ideal.map_comap_of_equiv e.toRingEquiv
    _ = RingHom.ker ((lineSection n S x).appTop.hom.comp
        e.symm.toRingEquiv.toRingHom) := rfl
    _ = Ideal.span {Polynomial.X - Polynomial.C x} := by
      rw [section_appTop_comp_polynomialCoordinateAlgEquiv_symm,
        Polynomial.ker_evalRingHom]

variable (ι : Type v) [Fintype ι]

/-- The product of the kernel ideals of a finite family of standard
affine-line sections. -/
noncomputable def sectionGraphProductIdeal (x : ι → Γ(S, ⊤)) :
    Ideal Γ(𝔸(n; S), ⊤) :=
  ∏ i, RingHom.ker (lineSection n S (x i)).appTop.hom

/-- Polynomial coordinates carry the complete section-kernel product to the
product of its linear graph ideals. -/
theorem map_sectionGraphProductIdeal (x : ι → Γ(S, ⊤)) :
    Ideal.map (polynomialCoordinateAlgEquiv n S).toRingEquiv.toRingHom
        (sectionGraphProductIdeal n S ι x) =
      SectionProductRootAlgebra.graphProductIdeal Γ(S, ⊤) ι x := by
  rw [sectionGraphProductIdeal,
    SectionProductRootAlgebra.ideal_map_fintype_prod,
    SectionProductRootAlgebra.graphProductIdeal]
  apply Fintype.prod_congr
  intro i
  exact map_section_ker n S (x i)

/-- The quotient of a standard relative affine line by the full product of
section kernels is the corresponding monic root algebra. -/
noncomputable def sectionGraphProductQuotientEquivRoot
    [Nontrivial Γ(S, ⊤)] (x : ι → Γ(S, ⊤)) :
    letI : Algebra Γ(S, ⊤) Γ(𝔸(n; S), ⊤) :=
      (𝔸(n; S) ↘ S).appTop.hom.toAlgebra
    (Γ(𝔸(n; S), ⊤) ⧸ sectionGraphProductIdeal n S ι x) ≃ₐ[Γ(S, ⊤)]
      AdjoinRoot
        (SectionProductRootAlgebra.sectionPolynomial Γ(S, ⊤) ι x) := by
  letI : Algebra Γ(S, ⊤) Γ(𝔸(n; S), ⊤) :=
    (𝔸(n; S) ↘ S).appTop.hom.toAlgebra
  exact (Ideal.quotientEquivAlg
      (sectionGraphProductIdeal n S ι x)
      (SectionProductRootAlgebra.graphProductIdeal Γ(S, ⊤) ι x)
      (polynomialCoordinateAlgEquiv n S)
      (map_sectionGraphProductIdeal n S ι x).symm).trans
    (SectionProductRootAlgebra.graphProductQuotientEquivRoot
      Γ(S, ⊤) ι x)

/-- The standard section-product quotient has rank equal to the number of
indexed sections. -/
theorem sectionGraphProductQuotient_finrank
    [Nontrivial Γ(S, ⊤)] (x : ι → Γ(S, ⊤)) :
    letI : Algebra Γ(S, ⊤) Γ(𝔸(n; S), ⊤) :=
      (𝔸(n; S) ↘ S).appTop.hom.toAlgebra
    Module.finrank Γ(S, ⊤)
        (Γ(𝔸(n; S), ⊤) ⧸ sectionGraphProductIdeal n S ι x) =
      Fintype.card ι := by
  letI : Algebra Γ(S, ⊤) Γ(𝔸(n; S), ⊤) :=
    (𝔸(n; S) ↘ S).appTop.hom.toAlgebra
  letI : Fact
      (SectionProductRootAlgebra.sectionPolynomial Γ(S, ⊤) ι x).Monic :=
    ⟨SectionProductRootAlgebra.sectionPolynomial_monic Γ(S, ⊤) ι x⟩
  rw [(sectionGraphProductQuotientEquivRoot n S ι x).toLinearEquiv.finrank_eq]
  rw [MonicRootFamily.rootAlgebra_finrank]
  exact SectionProductRootAlgebra.sectionPolynomial_natDegree Γ(S, ⊤) ι x

end MazurTorsion.AlgebraicGeometry.Jacobian.AffineLineSectionProduct

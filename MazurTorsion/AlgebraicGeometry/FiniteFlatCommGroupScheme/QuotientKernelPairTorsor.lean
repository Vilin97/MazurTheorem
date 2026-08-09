/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Quotient

/-!
# The kernel-pair torsor law for finite-flat fppf quotients

For an actual finite-flat quotient presentation `K → G → Q`, the action map identifies
`K ×_S G` with the kernel pair `G ×_Q G`.  The forward map sends `(k, g)` to
`(i(k) * g, g)`.  Its inverse sends `(g₁, g₂)` to `(g₁ / g₂, g₂)`, using the
scheme-theoretic kernel presentation to lift the difference uniquely to `K`.

The construction is made in `Over S`.  Products there are fibre products over `S`, and
pullbacks of the underlying quotient homomorphism are fibre products over `Q`, so the resulting
isomorphism is exactly the represented torsor law.  No quotient representability or pointwise
surjectivity theorem is inferred: the supplied quotient object and its fppf properties remain
part of `FppfQuotientPresentation`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

universe u

namespace FppfQuotientPresentation

variable {S : Scheme.{u}} {G : FiniteFlatCommGroupScheme S}

/-- The underlying morphism in `Over S` of the chosen finite-flat kernel inclusion. -/
abbrev kernelInclusionOverHom (D : FppfQuotientPresentation G) :
    D.kernelPresentation.kernel.obj.X ⟶ G.obj.X :=
  D.kernelPresentation.inclusion.hom.hom.hom.hom

/-- The underlying morphism in `Over S` of the quotient projection. -/
abbrev projectOverHom (D : FppfQuotientPresentation G) :
    G.obj.X ⟶ D.quotient.obj.X :=
  D.project.hom.hom.hom.hom

/-- The product `K ×_S G`, represented as a product in `Over S`. -/
abbrev KernelProduct (D : FppfQuotientPresentation G) : Over S :=
  D.kernelPresentation.kernel.obj.X ⨯ G.obj.X

/-- The kernel pair `G ×_Q G` of the actual quotient projection, represented in `Over S`. -/
abbrev ProjectKernelPair (D : FppfQuotientPresentation G) : Over S :=
  pullback D.projectOverHom D.projectOverHom

/-- The chosen kernel inclusion followed by the quotient projection is the identity-valued
morphism in the represented group of maps over `S`. -/
theorem kernelInclusionOverHom_comp_projectOverHom_eq_one
    (D : FppfQuotientPresentation G) :
    D.kernelInclusionOverHom ≫ D.projectOverHom = 1 := by
  apply Over.OverMorphism.ext
  exact D.kernelPresentation.inclusion_condition

/-- The action map from `K ×_S G` to the quotient kernel pair `G ×_Q G`. -/
def kernelProductToKernelPair (D : FppfQuotientPresentation G) :
    D.KernelProduct ⟶ D.ProjectKernelPair :=
  pullback.lift
    (prod.fst ≫ D.kernelInclusionOverHom * prod.snd)
    prod.snd
    (by
      rw [MonObj.mul_comp, Category.assoc,
        D.kernelInclusionOverHom_comp_projectOverHom_eq_one,
        MonObj.comp_one, one_mul])

@[reassoc]
theorem kernelProductToKernelPair_fst (D : FppfQuotientPresentation G) :
    D.kernelProductToKernelPair ≫
        pullback.fst D.projectOverHom D.projectOverHom =
      prod.fst ≫ D.kernelInclusionOverHom * prod.snd :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem kernelProductToKernelPair_snd (D : FppfQuotientPresentation G) :
    D.kernelProductToKernelPair ≫
        pullback.snd D.projectOverHom D.projectOverHom = prod.snd :=
  pullback.lift_snd _ _ _

/-- Difference of the two projections from the quotient kernel pair. -/
private def kernelPairDifference (D : FppfQuotientPresentation G) :
    D.ProjectKernelPair ⟶ G.obj.X :=
  pullback.fst D.projectOverHom D.projectOverHom /
    pullback.snd D.projectOverHom D.projectOverHom

private theorem kernelPairDifference_comp_projectOverHom_eq_one
    (D : FppfQuotientPresentation G) :
    D.kernelPairDifference ≫ D.projectOverHom = 1 := by
  change (pullback.fst D.projectOverHom D.projectOverHom /
      pullback.snd D.projectOverHom D.projectOverHom) ≫ D.projectOverHom = 1
  rw [GrpObj.div_comp, pullback.condition]
  simp

/-- The unique lift of the quotient-kernel-pair difference to the chosen geometric kernel. -/
private noncomputable def kernelPairDifferenceLift
    (D : FppfQuotientPresentation G) :
    D.ProjectKernelPair ⟶ D.kernelPresentation.kernel.obj.X :=
  (D.kernelPresentation.existsUnique_point_lift
    D.ProjectKernelPair D.kernelPairDifference
    D.kernelPairDifference_comp_projectOverHom_eq_one).choose

private theorem kernelPairDifferenceLift_comp_kernelInclusionOverHom
    (D : FppfQuotientPresentation G) :
    D.kernelPairDifferenceLift ≫ D.kernelInclusionOverHom =
      D.kernelPairDifference :=
  (D.kernelPresentation.existsUnique_point_lift
    D.ProjectKernelPair D.kernelPairDifference
    D.kernelPairDifference_comp_projectOverHom_eq_one).choose_spec.1

/-- The inverse coordinate map from the quotient kernel pair to `K ×_S G`. -/
private noncomputable def kernelPairToKernelProduct
    (D : FppfQuotientPresentation G) :
    D.ProjectKernelPair ⟶ D.KernelProduct :=
  prod.lift D.kernelPairDifferenceLift
    (pullback.snd D.projectOverHom D.projectOverHom)

private theorem kernelPairToKernelProduct_comp_kernelProductToKernelPair
    (D : FppfQuotientPresentation G) :
    D.kernelPairToKernelProduct ≫ D.kernelProductToKernelPair = 𝟙 _ := by
  apply pullback.hom_ext
  · dsimp only [kernelPairToKernelProduct, kernelProductToKernelPair]
    rw [Category.assoc, pullback.lift_fst, Category.id_comp, MonObj.comp_mul]
    rw [← Category.assoc, prod.lift_fst, prod.lift_snd,
      D.kernelPairDifferenceLift_comp_kernelInclusionOverHom]
    simp [kernelPairDifference]
  · dsimp only [kernelPairToKernelProduct, kernelProductToKernelPair]
    rw [Category.assoc, pullback.lift_snd, Category.id_comp, prod.lift_snd]

private theorem kernelProductToKernelPair_comp_kernelPairToKernelProduct
    (D : FppfQuotientPresentation G) :
    D.kernelProductToKernelPair ≫ D.kernelPairToKernelProduct = 𝟙 _ := by
  apply prod.hom_ext
  · dsimp only [kernelPairToKernelProduct]
    rw [Category.assoc, prod.lift_fst, Category.id_comp]
    apply (D.kernelPresentation.pointMulEquiv D.KernelProduct).injective
    apply Subtype.ext
    change (D.kernelProductToKernelPair ≫ D.kernelPairDifferenceLift) ≫
        D.kernelInclusionOverHom = prod.fst ≫ D.kernelInclusionOverHom
    rw [Category.assoc, D.kernelPairDifferenceLift_comp_kernelInclusionOverHom]
    dsimp only [kernelProductToKernelPair, kernelPairDifference]
    rw [GrpObj.comp_div, pullback.lift_fst, pullback.lift_snd]
    simp
  · dsimp only [kernelPairToKernelProduct, kernelProductToKernelPair]
    rw [Category.assoc, prod.lift_snd, Category.id_comp, pullback.lift_snd]

/-- The represented torsor law: kernel translation identifies `K ×_S G` with the kernel
pair `G ×_Q G` of the actual finite-flat quotient projection. -/
noncomputable def kernelProductIsoKernelPair (D : FppfQuotientPresentation G) :
    D.KernelProduct ≅ D.ProjectKernelPair where
  hom := D.kernelProductToKernelPair
  inv := D.kernelPairToKernelProduct
  hom_inv_id := D.kernelProductToKernelPair_comp_kernelPairToKernelProduct
  inv_hom_id := D.kernelPairToKernelProduct_comp_kernelProductToKernelPair

@[reassoc]
theorem kernelProductIsoKernelPair_hom_fst (D : FppfQuotientPresentation G) :
    D.kernelProductIsoKernelPair.hom ≫
        pullback.fst D.projectOverHom D.projectOverHom =
      prod.fst ≫ D.kernelInclusionOverHom * prod.snd :=
  D.kernelProductToKernelPair_fst

@[reassoc]
theorem kernelProductIsoKernelPair_hom_snd (D : FppfQuotientPresentation G) :
    D.kernelProductIsoKernelPair.hom ≫
        pullback.snd D.projectOverHom D.projectOverHom = prod.snd :=
  D.kernelProductToKernelPair_snd

/-- The first inverse coordinate is the unique kernel point whose inclusion is the difference
of the two kernel-pair projections. -/
@[reassoc]
theorem kernelProductIsoKernelPair_inv_fst_comp_kernelInclusionOverHom
    (D : FppfQuotientPresentation G) :
    (D.kernelProductIsoKernelPair.inv ≫ prod.fst) ≫
        D.kernelInclusionOverHom =
      pullback.fst D.projectOverHom D.projectOverHom /
        pullback.snd D.projectOverHom D.projectOverHom := by
  change (D.kernelPairToKernelProduct ≫ prod.fst) ≫
      D.kernelInclusionOverHom = D.kernelPairDifference
  dsimp only [kernelPairToKernelProduct]
  rw [prod.lift_fst]
  exact D.kernelPairDifferenceLift_comp_kernelInclusionOverHom

@[reassoc]
theorem kernelProductIsoKernelPair_inv_snd (D : FppfQuotientPresentation G) :
    D.kernelProductIsoKernelPair.inv ≫ prod.snd =
      pullback.snd D.projectOverHom D.projectOverHom :=
  prod.lift_snd _ _

end FppfQuotientPresentation

end AlgebraicGeometry.FiniteFlatCommGroupScheme

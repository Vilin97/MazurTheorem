/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FiniteTranslationQuotientGeometry
import TauCeti.AlgebraicGeometry.AbelianVariety.Basic

/-!
# Geometry of a finite translation quotient of an abelian variety

This file is the field-level abelian-variety consumer of the generic finite translation quotient
geometry.  The actual quotient, its projection, and its commutative group law are constructed in
the algebraic-geometry layer.  Properness, geometric integrality, and smoothness are obtained from
that quotient rather than supplied as data.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace AlgebraicGeometry
namespace FiniteTranslationQuotient

variable {K : Type u} [Field K]
variable {G : Type u} [Group G] [hGfinite : Finite G]
variable
  (E : CommGroupScheme (Spec (.of K)))
  (sections : G →* (𝟙_ (Over (Spec (.of K))) ⟶ E.X))
  [hDiagonalAffine : IsAffineHom (pullback.diagonal (terminal.from E.X.left))]
  (V : E.X.left → E.X.left.Opens)
  (hVs : ∀ x, (translationAction E sections).IsStableOpen (V x))
  (hVa : ∀ x, IsAffineOpen (V x))
  (hVmem : ∀ x, x ∈ V x)
  (hfree : ∀ g : G, g ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ E.X.left),
    t ≫ (translationAction E sections).hom g = t → IsEmpty T)

include hGfinite hDiagonalAffine

include hfree in
/-- The field-level signature retained for existing abelian-variety consumers.  It is an
application of the generic noetherian-affine quotient smoothness theorem. -/
theorem structureMap_smooth [IsProper E.X.hom] [GeometricallyIntegral E.X.hom] :
    Smooth (structureMap E sections V hVs hVa hVmem) := by
  exact structureMap_smooth_of_flat E sections V hVs hVa hVmem hfree

include hfree in
/-- The actual finite translation quotient, bundled as an abelian variety. -/
noncomputable def abelianVariety [IsProper E.X.hom] [GeometricallyIntegral E.X.hom] :
    TauCeti.AlgebraicGeometry.AbelianVariety K := by
  let Q := commGroupScheme E sections V hVs hVa hVmem hfree
  letI : GrpObj Q.X := Q.grp
  letI : IsProper Q.X.hom := by
    change IsProper (structureMap E sections V hVs hVa hVmem)
    exact structureMap_isProper E sections V hVs hVa hVmem hfree
  letI : GeometricallyIntegral Q.X.hom := by
    change GeometricallyIntegral (structureMap E sections V hVs hVa hVmem)
    exact structureMap_geometricallyIntegral E sections V hVs hVa hVmem hfree
  exact TauCeti.AlgebraicGeometry.AbelianVariety.ofGeometricallyIntegral
    Q.X

@[simp]
theorem abelianVariety_toOver [IsProper E.X.hom] [GeometricallyIntegral E.X.hom] :
    (abelianVariety E sections V hVs hVa hVmem hfree).toOver =
      (commGroupScheme E sections V hVs hVa hVmem hfree).X :=
  rfl

/-- The genuine quotient projection, now regarded as a homomorphism to the abelian quotient. -/
noncomputable def projectionToAbelianVariety
    [IsProper E.X.hom] [GeometricallyIntegral E.X.hom] :
    E ⟶ CommGrp.mk (abelianVariety E sections V hVs hVa hVmem hfree).toOver :=
  projectionHom E sections V hVs hVa hVmem hfree

/-! ## Consumer for an existing abelian variety -/

variable
  (A : TauCeti.AlgebraicGeometry.AbelianVariety K)
  (abelianSections :
    G →* (𝟙_ (Over (Spec (.of K))) ⟶ (CommGrp.mk A.toOver).X))
  [IsAffineHom
    (pullback.diagonal (terminal.from (CommGrp.mk A.toOver).X.left))]
  (abelianV : (CommGrp.mk A.toOver).X.left →
    (CommGrp.mk A.toOver).X.left.Opens)
  (abelianVs : ∀ x,
    (translationAction (CommGrp.mk A.toOver) abelianSections).IsStableOpen (abelianV x))
  (abelianVa : ∀ x, IsAffineOpen (abelianV x))
  (abelianVmem : ∀ x, x ∈ abelianV x)
  (abelianFree : ∀ g : G, g ≠ 1 →
    ∀ (T : Scheme.{u}) (t : T ⟶ (CommGrp.mk A.toOver).X.left),
      t ≫ (translationAction (CommGrp.mk A.toOver) abelianSections).hom g = t →
        IsEmpty T)

/-- A finite free translation quotient of an actual abelian variety is an actual abelian
variety, constructed from the quotient rather than supplied as quotient data. -/
noncomputable def abelianVarietyOfAbelianVariety :
    TauCeti.AlgebraicGeometry.AbelianVariety K :=
  abelianVariety (CommGrp.mk A.toOver) abelianSections abelianV
    abelianVs abelianVa abelianVmem abelianFree

/-- The quotient projection for `abelianVarietyOfAbelianVariety`. -/
noncomputable def projectionOfAbelianVariety :
    CommGrp.mk A.toOver ⟶
      CommGrp.mk (abelianVarietyOfAbelianVariety A abelianSections abelianV
        abelianVs abelianVa abelianVmem abelianFree).toOver :=
  projectionToAbelianVariety (CommGrp.mk A.toOver) abelianSections abelianV
    abelianVs abelianVa abelianVmem abelianFree

end FiniteTranslationQuotient
end AlgebraicGeometry

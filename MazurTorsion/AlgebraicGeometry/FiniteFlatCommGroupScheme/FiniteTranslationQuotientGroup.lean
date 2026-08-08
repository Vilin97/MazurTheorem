/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Chris Birkbeck, Claude Opus 4.8, OpenAI Codex
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Basic
import MazurTorsion.Upstream.AINTLIB.ForMathlib.QuotientTorsor

/-!
# The group object carried by a finite translation quotient

Let `E` be a commutative group scheme over `S`, and let a finite abstract group `G` act on `E`
through translations by a homomorphism `G → E(S)`.  Given a stable affine atlas and freeness of
the action, AINTLIB's finite-action quotient constructs an actual scheme `E/G` and a finite étale
surjection `q : E ⟶ E/G`.

This file upgrades that scheme quotient to a commutative group scheme.  The structure morphism,
inverse, and multiplication are descended through the quotient torsor.  Multiplication is
descended one variable at a time: both covers used in the construction are literal base changes
of `q`, so no product-torsor assumption is introduced.  The group laws are then checked after
pullback along the corresponding fpqc covers.

The proof skeletons for `constSection`, `translateBy`, and their elementary
composition laws are adapted from the exact AINTLIB blob
`6223d2904bc6f2162d4ee4e77ed684a40396ef18`, at
`projects/ModularCurves/ModularCurves/GroupScheme/TranslationBySection.lean`.
That blob was authored by Chris Birkbeck with Claude Opus 4.8 and occurs
unchanged at AINTLIB commit `1c1c74664e40071c2c2165bc55ca2616a67ccd6b`,
whose root license is Apache-2.0. The equivariance, action, descent, and
group-object proofs below are new local work.
The representability design agrees with SGA 3, Exposé V, §7 and the modern
finite-locally-free free-action formulation in the Stacks Project, Tag 07S7;
no proof text is ported from those references.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj
open scoped CategoryTheory.MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

namespace AlgebraicGeometry
namespace FiniteTranslationQuotient

universe u

variable {S : Scheme.{u}}

/-! ## Translation actions -/

/-- The constant endomorphism of a commutative group scheme at a section. -/
noncomputable def constSection (E : CommGroupScheme S)
    (x : 𝟙_ (Over S) ⟶ E.X) : E.X ⟶ E.X :=
  toUnit E.X ≫ x

/-- Translation by a section, written in the pointwise commutative group of endomorphisms. -/
noncomputable def translateBy (E : CommGroupScheme S)
    (x : 𝟙_ (Over S) ⟶ E.X) : E.X ⟶ E.X :=
  letI : CommGroup (E.X ⟶ E.X) := Hom.commGroup
  𝟙 E.X * constSection E x

theorem translateBy_def (E : CommGroupScheme S)
    (x : 𝟙_ (Over S) ⟶ E.X) :
    letI : CommGroup (E.X ⟶ E.X) := Hom.commGroup
    translateBy E x = 𝟙 E.X * constSection E x :=
  rfl

theorem comp_constSection (E : CommGroupScheme S) {T : Over S} (f : T ⟶ E.X)
    (x : 𝟙_ (Over S) ⟶ E.X) :
    f ≫ constSection E x = toUnit T ≫ x := by
  rw [constSection, ← Category.assoc,
    CartesianMonoidalCategory.toUnit_unique (f ≫ toUnit E.X) (toUnit T)]

theorem constSection_mul (E : CommGroupScheme S)
    (x y : 𝟙_ (Over S) ⟶ E.X) :
    constSection E (x * y) = constSection E x * constSection E y := by
  rw [constSection, constSection, constSection, MonObj.comp_mul]

theorem translateBy_one (E : CommGroupScheme S) : translateBy E 1 = 𝟙 E.X := by
  letI : CommGroup (E.X ⟶ E.X) := Hom.commGroup
  rw [translateBy, constSection, MonObj.comp_one]
  exact mul_one _

/-- Evaluating translation by `x` at the identity section gives `x`. -/
@[simp]
theorem one_comp_translateBy (E : CommGroupScheme S)
    (x : 𝟙_ (Over S) ⟶ E.X) :
    η[E.X] ≫ translateBy E x = x := by
  letI : CommGroup (E.X ⟶ E.X) := Hom.commGroup
  letI : CommGroup (𝟙_ (Over S) ⟶ E.X) := Hom.commGroup
  rw [translateBy_def, MonObj.comp_mul, Category.comp_id,
    comp_constSection, toUnit_unit, Category.id_comp, MonObj.one_eq_one E.X]
  exact _root_.one_mul x

theorem translateBy_comp (E : CommGroupScheme S)
    (x y : 𝟙_ (Over S) ⟶ E.X) :
    translateBy E x ≫ translateBy E y = translateBy E (x * y) := by
  letI : CommGroup (E.X ⟶ E.X) := Hom.commGroup
  rw [translateBy_def E y, MonObj.comp_mul, Category.comp_id,
    comp_constSection E, translateBy_def E x, translateBy_def E (x * y),
    constSection_mul E]
  exact mul_assoc _ _ _

/-- Translating the first input translates the product. -/
theorem translateBy_tensor_id_comp_mul (E : CommGroupScheme S)
    (x : 𝟙_ (Over S) ⟶ E.X) :
    (translateBy E x ⊗ₘ 𝟙 E.X) ≫ μ[E.X] = μ[E.X] ≫ translateBy E x := by
  letI : CommGroup (E.X ⊗ E.X ⟶ E.X) := Hom.commGroup
  rw [MonObj.mul_eq_mul E.X, MonObj.comp_mul, translateBy_def,
    MonObj.comp_mul]
  simp only [tensorHom_fst, tensorHom_snd, Category.comp_id,
    MonObj.comp_mul, comp_constSection E]
  ac_rfl

/-- Translating the second input translates the product. -/
theorem id_tensor_translateBy_comp_mul (E : CommGroupScheme S)
    (x : 𝟙_ (Over S) ⟶ E.X) :
    (𝟙 E.X ⊗ₘ translateBy E x) ≫ μ[E.X] = μ[E.X] ≫ translateBy E x := by
  letI : CommGroup (E.X ⊗ E.X ⟶ E.X) := Hom.commGroup
  rw [MonObj.mul_eq_mul E.X, MonObj.comp_mul, translateBy_def,
    MonObj.comp_mul]
  simp only [tensorHom_fst, tensorHom_snd, Category.comp_id,
    MonObj.comp_mul, comp_constSection E]
  ac_rfl

/-- Inversion conjugates translation by `x` to translation by `x⁻¹`. -/
theorem translateBy_comp_inv (E : CommGroupScheme S)
    (x : 𝟙_ (Over S) ⟶ E.X) :
    translateBy E x ≫ ι[E.X] = ι[E.X] ≫ translateBy E x⁻¹ := by
  letI : CommGroup (E.X ⟶ E.X) := Hom.commGroup
  change (translateBy E x)⁻¹ = _
  simp only [translateBy_def, mul_inv_rev, Hom.inv_def, constSection,
    MonObj.comp_mul, Category.comp_id,
    CartesianMonoidalCategory.comp_toUnit_assoc]
  ac_rfl

/-- The scheme action associated to a finite group of translating sections. -/
noncomputable def translationAction {G : Type u} [Group G] (E : CommGroupScheme S)
    (sections : G →* (𝟙_ (Over S) ⟶ E.X)) : SchemeAction G E.X.left where
  hom g := (translateBy E (sections g)).left
  hom_one := by
    rw [map_one, translateBy_one]
    rfl
  hom_mul g h := by
    rw [map_mul, ← translateBy_comp]
    rfl

theorem translationAction_over {G : Type u} [Group G] (E : CommGroupScheme S)
    (sections : G →* (𝟙_ (Over S) ⟶ E.X)) (g : G) :
    (translationAction E sections).hom g ≫ E.X.hom = E.X.hom :=
  (translateBy E (sections g)).w

/-! ## The underlying scheme quotient -/

section Quotient

variable {G : Type u} [Group G] [Finite G]
  (E : CommGroupScheme S)
  (sections : G →* (𝟙_ (Over S) ⟶ E.X))
  [IsAffineHom (pullback.diagonal (terminal.from E.X.left))]
  (V : E.X.left → E.X.left.Opens)
  (hVs : ∀ x, (translationAction E sections).IsStableOpen (V x))
  (hVa : ∀ x, IsAffineOpen (V x))
  (hVmem : ∀ x, x ∈ V x)
  (hfree : ∀ g : G, g ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ E.X.left),
    t ≫ (translationAction E sections).hom g = t → IsEmpty T)

/-- The actual AINTLIB finite-action quotient scheme. -/
noncomputable abbrev scheme : Scheme.{u} :=
  (translationAction E sections).quotient V hVs hVa

/-- The actual finite-action quotient projection. -/
noncomputable abbrev projection : E.X.left ⟶ scheme E sections V hVs hVa :=
  (translationAction E sections).quotientπ V hVs hVa hVmem

/-- The descended structure map of the quotient. -/
noncomputable def structureMap : scheme E sections V hVs hVa ⟶ S :=
  ((translationAction E sections).existsUnique_quotientπ_lift V hVs hVa hVmem
    E.X.hom (translationAction_over E sections)).choose

@[reassoc]
theorem projection_comp_structureMap :
    projection E sections V hVs hVa hVmem ≫
        structureMap E sections V hVs hVa hVmem = E.X.hom :=
  ((translationAction E sections).existsUnique_quotientπ_lift V hVs hVa hVmem
    E.X.hom (translationAction_over E sections)).choose_spec.1

/-- The quotient scheme as an object over `S`. -/
noncomputable def asOver : Over S :=
  Over.mk (structureMap E sections V hVs hVa hVmem)

/-- The quotient projection as a morphism over `S`. -/
noncomputable def projectionOver : E.X ⟶ asOver E sections V hVs hVa hVmem :=
  Over.homMk (projection E sections V hVs hVa hVmem)
    (projection_comp_structureMap E sections V hVs hVa hVmem)

@[simp]
theorem projectionOver_left :
    (projectionOver E sections V hVs hVa hVmem).left =
      projection E sections V hVs hVa hVmem :=
  rfl

/-- The quotient projection identifies every translate. -/
theorem translateBy_comp_projectionOver (g : G) :
    translateBy E (sections g) ≫ projectionOver E sections V hVs hVa hVmem =
      projectionOver E sections V hVs hVa hVmem := by
  apply Over.OverMorphism.ext
  exact (translationAction E sections).hom_quotientπ V hVs hVa hVmem g

/-- The inverse followed by the quotient projection is translation-invariant. -/
theorem translateBy_comp_inv_comp_projectionOver (g : G) :
    translateBy E (sections g) ≫ ι[E.X] ≫
        projectionOver E sections V hVs hVa hVmem =
      ι[E.X] ≫ projectionOver E sections V hVs hVa hVmem := by
  rw [← Category.assoc, translateBy_comp_inv E, Category.assoc, ← map_inv,
    translateBy_comp_projectionOver E sections V hVs hVa hVmem]

/-- Multiplication followed by the quotient projection is invariant in its first input. -/
theorem translateBy_tensor_id_comp_mul_comp_projectionOver (g : G) :
    (translateBy E (sections g) ⊗ₘ 𝟙 E.X) ≫ μ[E.X] ≫
        projectionOver E sections V hVs hVa hVmem =
      μ[E.X] ≫ projectionOver E sections V hVs hVa hVmem := by
  rw [← Category.assoc, translateBy_tensor_id_comp_mul E, Category.assoc,
    translateBy_comp_projectionOver E sections V hVs hVa hVmem]

/-- Multiplication followed by the quotient projection is invariant in its second input. -/
theorem id_tensor_translateBy_comp_mul_comp_projectionOver (g : G) :
    (𝟙 E.X ⊗ₘ translateBy E (sections g)) ≫ μ[E.X] ≫
        projectionOver E sections V hVs hVa hVmem =
      μ[E.X] ≫ projectionOver E sections V hVs hVa hVmem := by
  rw [← Category.assoc, id_tensor_translateBy_comp_mul E, Category.assoc,
    translateBy_comp_projectionOver E sections V hVs hVa hVmem]

include hfree in
/-- The quotient projection is a finite morphism. -/
theorem projection_isFinite :
    IsFinite (projection E sections V hVs hVa hVmem) :=
  (translationAction E sections).isFinite_quotientπ V hVs hVa hVmem hfree

include hfree in
/-- The quotient projection is étale. -/
theorem projection_etale :
    Etale (projection E sections V hVs hVa hVmem) :=
  (translationAction E sections).etale_quotientπ V hVs hVa hVmem hfree

/-- The quotient projection is surjective. -/
theorem projection_surjective :
    Surjective (projection E sections V hVs hVa hVmem) :=
  ⟨(translationAction E sections).quotientπ_surjective V hVs hVa hVmem⟩

include hfree in
/-- Effective descent through an arbitrary base change of the actual quotient projection.

This is the engine used below to descend multiplication one variable at a time.  Its torsor
hypothesis is not extra data: it is the torsor theorem for AINTLIB's quotient projection, pulled
back along `j`. -/
theorem existsUnique_descent_baseChange {W Y : Scheme.{u}}
    (j : W ⟶ scheme E sections V hVs hVa)
    (F : pullback (projection E sections V hVs hVa hVmem) j ⟶ Y)
    (hF : ∀ g : G,
      (ModularCurves.pullbackTorsorAction (translationAction E sections)
        (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g) j).hom g ≫
          F = F) :
    ∃! u : W ⟶ Y,
      pullback.snd (projection E sections V hVs hVa hVmem) j ≫ u = F := by
  letI : IsFinite (projection E sections V hVs hVa hVmem) :=
    projection_isFinite E sections V hVs hVa hVmem hfree
  letI : Etale (projection E sections V hVs hVa hVmem) :=
    projection_etale E sections V hVs hVa hVmem hfree
  letI : Surjective (projection E sections V hVs hVa hVmem) :=
    projection_surjective E sections V hVs hVa hVmem
  letI : Surjective
      (pullback.snd (projection E sections V hVs hVa hVmem) j) :=
    MorphismProperty.pullback_snd _ _
      (inferInstanceAs (Surjective (projection E sections V hVs hVa hVmem)))
  letI : Flat (pullback.snd (projection E sections V hVs hVa hVmem) j) :=
    MorphismProperty.pullback_snd _ _
      (inferInstanceAs (Flat (projection E sections V hVs hVa hVmem)))
  letI : QuasiCompact
      (pullback.snd (projection E sections V hVs hVa hVmem) j) :=
    MorphismProperty.pullback_snd _ _
      (inferInstanceAs (QuasiCompact (projection E sections V hVs hVa hVmem)))
  have hqtors : IsIso (ModularCurves.torsorCompare
      (projection E sections V hVs hVa hVmem) (translationAction E sections)
      (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g)) :=
    (translationAction E sections).isIso_torsorCompare_quotientπ
      V hVs hVa hVmem hfree
  exact ModularCurves.existsUnique_descent_of_torsor
    (ModularCurves.pullbackTorsorAction (translationAction E sections)
      (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g) j)
    (ModularCurves.pullbackTorsorAction_over (translationAction E sections)
      (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g) j)
    (ModularCurves.isIso_torsorCompare_pullback (translationAction E sections)
      (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g)
      hqtors j)
    F hF

include hfree in
/-- The quotient projection is an epimorphism in schemes. -/
theorem projection_epi : Epi (projection E sections V hVs hVa hVmem) := by
  haveI : Etale (projection E sections V hVs hVa hVmem) :=
    projection_etale E sections V hVs hVa hVmem hfree
  haveI : Surjective (projection E sections V hVs hVa hVmem) :=
    projection_surjective E sections V hVs hVa hVmem
  exact Flat.epi_of_flat_of_surjective _

include hfree in
/-- The quotient projection is also epi in the slice over `S`. -/
theorem projectionOver_epi : Epi (projectionOver E sections V hVs hVa hVmem) := by
  letI : Epi (projection E sections V hVs hVa hVmem) :=
    projection_epi E sections V hVs hVa hVmem hfree
  haveI : Epi (projectionOver E sections V hVs hVa hVmem).left := by
    change Epi (projection E sections V hVs hVa hVmem)
    infer_instance
  exact Over.epi_of_epi_left _

/-! ## Unit and inverse -/

/-- The unit of the quotient is the image of the unit of `E`. -/
noncomputable def oneOver :
    𝟙_ (Over S) ⟶ asOver E sections V hVs hVa hVmem :=
  η[E.X] ≫ projectionOver E sections V hVs hVa hVmem

/-- The descended inverse on the underlying quotient scheme. -/
noncomputable def inv :
    scheme E sections V hVs hVa ⟶ scheme E sections V hVs hVa :=
  ((translationAction E sections).existsUnique_quotientπ_lift V hVs hVa hVmem
    (ι[E.X].left ≫ projection E sections V hVs hVa hVmem)
    (fun g ↦ congrArg CommaMorphism.left
      (translateBy_comp_inv_comp_projectionOver E sections V hVs hVa hVmem g))).choose

@[reassoc]
theorem projection_comp_inv :
    projection E sections V hVs hVa hVmem ≫ inv E sections V hVs hVa hVmem =
      ι[E.X].left ≫ projection E sections V hVs hVa hVmem :=
  ((translationAction E sections).existsUnique_quotientπ_lift V hVs hVa hVmem
    (ι[E.X].left ≫ projection E sections V hVs hVa hVmem)
    (fun g ↦ congrArg CommaMorphism.left
      (translateBy_comp_inv_comp_projectionOver E sections V hVs hVa hVmem g))).choose_spec.1

include hfree in
/-- The descended inverse is a morphism over `S`. -/
theorem inv_comp_structureMap :
    inv E sections V hVs hVa hVmem ≫ structureMap E sections V hVs hVa hVmem =
      structureMap E sections V hVs hVa hVmem := by
  letI : Epi (projection E sections V hVs hVa hVmem) :=
    projection_epi E sections V hVs hVa hVmem hfree
  rw [← cancel_epi (projection E sections V hVs hVa hVmem)]
  rw [← Category.assoc, projection_comp_inv, Category.assoc,
    projection_comp_structureMap]
  exact (ι[E.X]).w

include hfree in
/-- Inversion on the quotient as a morphism in the slice over `S`. -/
noncomputable def invOver :
    asOver E sections V hVs hVa hVmem ⟶ asOver E sections V hVs hVa hVmem :=
  Over.homMk (inv E sections V hVs hVa hVmem)
    (inv_comp_structureMap E sections V hVs hVa hVmem hfree)

@[simp]
theorem invOver_left :
    (invOver E sections V hVs hVa hVmem hfree).left =
      inv E sections V hVs hVa hVmem :=
  rfl

@[reassoc (attr := simp)]
theorem projectionOver_comp_invOver :
    projectionOver E sections V hVs hVa hVmem ≫
        invOver E sections V hVs hVa hVmem hfree =
      ι[E.X] ≫ projectionOver E sections V hVs hVa hVmem := by
  apply Over.OverMorphism.ext
  exact projection_comp_inv E sections V hVs hVa hVmem

/-! ## Multiplication: descent in the second variable -/

/-- The first descent base, `E ×_S (E/G)`. -/
noncomputable abbrev rightDescentBase : Scheme.{u} :=
  (E.X ⊗ asOver E sections V hVs hVa hVmem).left

/-- Its projection to the quotient factor. -/
noncomputable abbrev rightDescentBaseToQuotient :
    rightDescentBase E sections V hVs hVa hVmem ⟶
      scheme E sections V hVs hVa :=
  (snd E.X (asOver E sections V hVs hVa hVmem)).left

/-- The base change of `q` used to descend the second input of multiplication. -/
noncomputable abbrev rightDescentTotal : Scheme.{u} :=
  pullback (projection E sections V hVs hVa hVmem)
    (rightDescentBaseToQuotient E sections V hVs hVa hVmem)

/-- The first `E`-coordinate on the total space of the right-variable descent. -/
noncomputable def rightDescentFirst :
    rightDescentTotal E sections V hVs hVa hVmem ⟶ E.X.left :=
  pullback.snd (projection E sections V hVs hVa hVmem)
      (rightDescentBaseToQuotient E sections V hVs hVa hVmem) ≫
    (fst E.X (asOver E sections V hVs hVa hVmem)).left

/-- The second `E`-coordinate on the total space of the right-variable descent. -/
noncomputable def rightDescentSecond :
    rightDescentTotal E sections V hVs hVa hVmem ⟶ E.X.left :=
  pullback.fst (projection E sections V hVs hVa hVmem)
    (rightDescentBaseToQuotient E sections V hVs hVa hVmem)

theorem rightDescentFirst_comp_structureMap :
    rightDescentFirst E sections V hVs hVa hVmem ≫ E.X.hom =
      rightDescentSecond E sections V hVs hVa hVmem ≫ E.X.hom := by
  change (pullback.snd (projection E sections V hVs hVa hVmem)
      (pullback.snd E.X.hom (structureMap E sections V hVs hVa hVmem)) ≫
        pullback.fst E.X.hom (structureMap E sections V hVs hVa hVmem)) ≫
      E.X.hom =
    pullback.fst (projection E sections V hVs hVa hVmem)
        (pullback.snd E.X.hom (structureMap E sections V hVs hVa hVmem)) ≫
      E.X.hom
  rw [Category.assoc,
    pullback.condition (f := E.X.hom)
      (g := structureMap E sections V hVs hVa hVmem),
    ← Category.assoc,
    ← pullback.condition
      (f := projection E sections V hVs hVa hVmem)
      (g := pullback.snd E.X.hom
        (structureMap E sections V hVs hVa hVmem)),
    Category.assoc, projection_comp_structureMap]

/-- The canonical comparison from the first base-changed torsor to `E ×_S E`. -/
noncomputable def rightDescentPair :
    rightDescentTotal E sections V hVs hVa hVmem ⟶ (E.X ⊗ E.X).left :=
  pullback.lift
    (rightDescentFirst E sections V hVs hVa hVmem)
    (rightDescentSecond E sections V hVs hVa hVmem)
    (rightDescentFirst_comp_structureMap E sections V hVs hVa hVmem)

@[reassoc (attr := simp)]
theorem rightDescentPair_fst :
    rightDescentPair E sections V hVs hVa hVmem ≫ pullback.fst E.X.hom E.X.hom =
      rightDescentFirst E sections V hVs hVa hVmem :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem rightDescentPair_snd :
    rightDescentPair E sections V hVs hVa hVmem ≫ pullback.snd E.X.hom E.X.hom =
      rightDescentSecond E sections V hVs hVa hVmem :=
  pullback.lift_snd _ _ _

/-- The product on `E`, followed by `q`, on the first base-changed torsor. -/
noncomputable def rightDescentRaw :
    rightDescentTotal E sections V hVs hVa hVmem ⟶
      scheme E sections V hVs hVa :=
  rightDescentPair E sections V hVs hVa hVmem ≫ μ[E.X].left ≫
    projection E sections V hVs hVa hVmem

@[reassoc (attr := simp)]
theorem pullbackTorsorAction_fst {W : Scheme.{u}}
    (j : W ⟶ scheme E sections V hVs hVa) (g : G) :
    (ModularCurves.pullbackTorsorAction (translationAction E sections)
      (fun g ↦ (translationAction E sections).hom_quotientπ
        V hVs hVa hVmem g) j).hom g ≫
        pullback.fst (projection E sections V hVs hVa hVmem) j =
      pullback.fst (projection E sections V hVs hVa hVmem) j ≫
        (translateBy E (sections g)).left := by
  change pullback.lift
      (pullback.fst (projection E sections V hVs hVa hVmem) j ≫
        (translateBy E (sections g)).left)
      (pullback.snd (projection E sections V hVs hVa hVmem) j) _ ≫
        pullback.fst (projection E sections V hVs hVa hVmem) j =
    pullback.fst (projection E sections V hVs hVa hVmem) j ≫
      (translateBy E (sections g)).left
  exact pullback.lift_fst _ _ _

/-- The pulled-back translation action changes exactly the second `E`-coordinate. -/
theorem pullbackAction_comp_rightDescentPair (g : G) :
    (ModularCurves.pullbackTorsorAction (translationAction E sections)
      (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g)
      (rightDescentBaseToQuotient E sections V hVs hVa hVmem)).hom g ≫
        rightDescentPair E sections V hVs hVa hVmem =
      rightDescentPair E sections V hVs hVa hVmem ≫
        (𝟙 E.X ⊗ₘ translateBy E (sections g)).left := by
  apply pullback.hom_ext
  · have hcover := ModularCurves.pullbackTorsorAction_over
      (translationAction E sections)
      (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g)
      (rightDescentBaseToQuotient E sections V hVs hVa hVmem) g
    have hfirst := congrArg
      (fun f ↦ f ≫ (fst E.X (asOver E sections V hVs hVa hVmem)).left) hcover
    have hinv :
        (ModularCurves.pullbackTorsorAction (translationAction E sections)
          (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g)
          (rightDescentBaseToQuotient E sections V hVs hVa hVmem)).hom g ≫
            rightDescentFirst E sections V hVs hVa hVmem =
          rightDescentFirst E sections V hVs hVa hVmem := by
      simpa only [rightDescentFirst, Category.assoc] using hfirst
    have htensor := Over.tensorHom_left_fst E.X.hom E.X.hom
      (𝟙 E.X) (translateBy E (sections g))
    change (𝟙 E.X ⊗ₘ translateBy E (sections g)).left ≫
        pullback.fst E.X.hom E.X.hom =
      pullback.fst E.X.hom E.X.hom ≫
        (𝟙 E.X : E.X ⟶ E.X).left at htensor
    rw [Over.id_left, Category.comp_id] at htensor
    have hpre := congrArg
      (fun f ↦ (ModularCurves.pullbackTorsorAction (translationAction E sections)
        (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g)
        (rightDescentBaseToQuotient E sections V hVs hVa hVmem)).hom g ≫ f)
      (rightDescentPair_fst E sections V hVs hVa hVmem)
    have hstep := (Category.assoc
      ((ModularCurves.pullbackTorsorAction (translationAction E sections)
        (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g)
        (rightDescentBaseToQuotient E sections V hVs hVa hVmem)).hom g)
      (rightDescentPair E sections V hVs hVa hVmem)
      (pullback.fst E.X.hom E.X.hom)).trans hpre
    have hpost := congrArg
      (fun f ↦ rightDescentPair E sections V hVs hVa hVmem ≫ f) htensor
    have hpoststep := (Category.assoc
      (rightDescentPair E sections V hVs hVa hVmem)
      (𝟙 E.X ⊗ₘ translateBy E (sections g)).left
      (pullback.fst E.X.hom E.X.hom)).trans hpost
    exact hstep.trans (hinv.trans
      ((rightDescentPair_fst E sections V hVs hVa hVmem).symm.trans
        hpoststep.symm))
  · have hmid := pullbackTorsorAction_fst E sections V hVs hVa hVmem
      (rightDescentBaseToQuotient E sections V hVs hVa hVmem) g
    change (ModularCurves.pullbackTorsorAction (translationAction E sections)
        (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g)
        (rightDescentBaseToQuotient E sections V hVs hVa hVmem)).hom g ≫
          rightDescentSecond E sections V hVs hVa hVmem =
      rightDescentSecond E sections V hVs hVa hVmem ≫
        (translateBy E (sections g)).left at hmid
    have htensor := Over.tensorHom_left_snd E.X.hom E.X.hom
      (𝟙 E.X) (translateBy E (sections g))
    change (𝟙 E.X ⊗ₘ translateBy E (sections g)).left ≫
        pullback.snd E.X.hom E.X.hom =
      pullback.snd E.X.hom E.X.hom ≫
        (translateBy E (sections g)).left at htensor
    have hpre := congrArg
      (fun f ↦ (ModularCurves.pullbackTorsorAction (translationAction E sections)
        (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g)
        (rightDescentBaseToQuotient E sections V hVs hVa hVmem)).hom g ≫ f)
      (rightDescentPair_snd E sections V hVs hVa hVmem)
    have hstep := (Category.assoc
      ((ModularCurves.pullbackTorsorAction (translationAction E sections)
        (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g)
        (rightDescentBaseToQuotient E sections V hVs hVa hVmem)).hom g)
      (rightDescentPair E sections V hVs hVa hVmem)
      (pullback.snd E.X.hom E.X.hom)).trans hpre
    have hpair := congrArg
      (fun f ↦ f ≫ (translateBy E (sections g)).left)
      (rightDescentPair_snd E sections V hVs hVa hVmem).symm
    have hpost := congrArg
      (fun f ↦ rightDescentPair E sections V hVs hVa hVmem ≫ f) htensor
    have hfinal := (Category.assoc
      (rightDescentPair E sections V hVs hVa hVmem)
      (𝟙 E.X ⊗ₘ translateBy E (sections g)).left
      (pullback.snd E.X.hom E.X.hom)).trans (hpost.trans
        (Category.assoc (rightDescentPair E sections V hVs hVa hVmem)
          (pullback.snd E.X.hom E.X.hom)
          (translateBy E (sections g)).left).symm)
    exact hstep.trans (hmid.trans (hpair.trans hfinal.symm))

/-- The raw product is invariant under the pulled-back action. -/
theorem pullbackAction_comp_rightDescentRaw (g : G) :
    (ModularCurves.pullbackTorsorAction (translationAction E sections)
      (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g)
      (rightDescentBaseToQuotient E sections V hVs hVa hVmem)).hom g ≫
        rightDescentRaw E sections V hVs hVa hVmem =
      rightDescentRaw E sections V hVs hVa hVmem := by
  rw [rightDescentRaw, ← Category.assoc, ← Category.assoc,
    pullbackAction_comp_rightDescentPair E sections V hVs hVa hVmem g,
    Category.assoc, Category.assoc]
  have h := congrArg CommaMorphism.left
    (id_tensor_translateBy_comp_mul_comp_projectionOver
      E sections V hVs hVa hVmem g)
  change ( 𝟙 E.X ⊗ₘ translateBy E (sections g)).left ≫
      μ[E.X].left ≫ projection E sections V hVs hVa hVmem =
    μ[E.X].left ≫ projection E sections V hVs hVa hVmem at h
  simpa only [Category.assoc] using
    congrArg (fun f ↦ rightDescentPair E sections V hVs hVa hVmem ≫ f) h

include hfree in
/-- The product after descending its second variable, `E ×_S (E/G) ⟶ E/G`. -/
noncomputable def rightDescentMul :
    rightDescentBase E sections V hVs hVa hVmem ⟶
      scheme E sections V hVs hVa :=
  (existsUnique_descent_baseChange E sections V hVs hVa hVmem hfree
    (rightDescentBaseToQuotient E sections V hVs hVa hVmem)
    (rightDescentRaw E sections V hVs hVa hVmem)
    (pullbackAction_comp_rightDescentRaw E sections V hVs hVa hVmem)).choose

@[reassoc]
theorem rightDescentCover_comp_mul :
    pullback.snd (projection E sections V hVs hVa hVmem)
        (rightDescentBaseToQuotient E sections V hVs hVa hVmem) ≫
      rightDescentMul E sections V hVs hVa hVmem hfree =
    rightDescentRaw E sections V hVs hVa hVmem :=
  (existsUnique_descent_baseChange E sections V hVs hVa hVmem hfree
    (rightDescentBaseToQuotient E sections V hVs hVa hVmem)
    (rightDescentRaw E sections V hVs hVa hVmem)
    (pullbackAction_comp_rightDescentRaw E sections V hVs hVa hVmem)).choose_spec.1

/-- The half-descended product is a morphism over `S`. -/
theorem rightDescentMul_comp_structureMap :
    rightDescentMul E sections V hVs hVa hVmem hfree ≫
        structureMap E sections V hVs hVa hVmem =
      (E.X ⊗ asOver E sections V hVs hVa hVmem).hom := by
  letI := (translationAction E sections).epi_pullback_snd_quotientπ
    V hVs hVa hVmem
    (fun {T} t g hg hfix ↦ hfree g hg T t hfix)
    (rightDescentBaseToQuotient E sections V hVs hVa hVmem)
  rw [← cancel_epi (pullback.snd (projection E sections V hVs hVa hVmem)
    (rightDescentBaseToQuotient E sections V hVs hVa hVmem))]
  rw [← Category.assoc, rightDescentCover_comp_mul]
  change (rightDescentPair E sections V hVs hVa hVmem ≫
      μ[E.X].left ≫ projection E sections V hVs hVa hVmem) ≫
        structureMap E sections V hVs hVa hVmem = _
  simp only [Category.assoc, projection_comp_structureMap, μ[E.X].w,
    Over.tensorObj_hom]
  calc
    rightDescentPair E sections V hVs hVa hVmem ≫
          pullback.fst E.X.hom E.X.hom ≫ E.X.hom =
        rightDescentFirst E sections V hVs hVa hVmem ≫ E.X.hom := by
      exact rightDescentPair_fst_assoc E sections V hVs hVa hVmem E.X.hom
    _ = pullback.snd (projection E sections V hVs hVa hVmem)
          (rightDescentBaseToQuotient E sections V hVs hVa hVmem) ≫
        pullback.fst E.X.hom (structureMap E sections V hVs hVa hVmem) ≫
          E.X.hom := rfl

include hfree in
/-- The half-descended product in the slice category. -/
noncomputable def rightDescentMulOver :
    E.X ⊗ asOver E sections V hVs hVa hVmem ⟶
      asOver E sections V hVs hVa hVmem :=
  Over.homMk (rightDescentMul E sections V hVs hVa hVmem hfree)
    (rightDescentMul_comp_structureMap E sections V hVs hVa hVmem hfree)

/-- Translation of the remaining `E`-variable on `E ×_S (E/G)`. -/
noncomputable def rightDescentTranslateBase (g : G) :
    rightDescentBase E sections V hVs hVa hVmem ⟶
      rightDescentBase E sections V hVs hVa hVmem :=
  (translateBy E (sections g) ⊗ₘ
    𝟙 (asOver E sections V hVs hVa hVmem)).left

@[reassoc (attr := simp)]
theorem rightDescentTranslateBase_fst (g : G) :
    rightDescentTranslateBase E sections V hVs hVa hVmem g ≫
        pullback.fst E.X.hom (structureMap E sections V hVs hVa hVmem) =
      pullback.fst E.X.hom (structureMap E sections V hVs hVa hVmem) ≫
        (translateBy E (sections g)).left :=
  Over.tensorHom_left_fst _ _ _ _

@[reassoc (attr := simp)]
theorem rightDescentTranslateBase_snd (g : G) :
    rightDescentTranslateBase E sections V hVs hVa hVmem g ≫
        pullback.snd E.X.hom (structureMap E sections V hVs hVa hVmem) =
      pullback.snd E.X.hom (structureMap E sections V hVs hVa hVmem) := by
  have hsnd := Over.tensorHom_left_snd E.X.hom
    (structureMap E sections V hVs hVa hVmem)
    (translateBy E (sections g))
    (𝟙 (asOver E sections V hVs hVa hVmem))
  simpa only [rightDescentTranslateBase, rightDescentBase, asOver, Over.mk_hom,
    Over.id_left, Category.comp_id] using hsnd

/-- Translation of the remaining variable lifted to the first descent torsor. -/
noncomputable def rightDescentTranslateTotal (g : G) :
    rightDescentTotal E sections V hVs hVa hVmem ⟶
      rightDescentTotal E sections V hVs hVa hVmem :=
  pullback.map
    (projection E sections V hVs hVa hVmem)
    (rightDescentBaseToQuotient E sections V hVs hVa hVmem)
    (projection E sections V hVs hVa hVmem)
    (rightDescentBaseToQuotient E sections V hVs hVa hVmem)
    (𝟙 E.X.left)
    (rightDescentTranslateBase E sections V hVs hVa hVmem g)
    (𝟙 (scheme E sections V hVs hVa))
    (by simp)
    (by
      change pullback.snd E.X.hom
          (structureMap E sections V hVs hVa hVmem) ≫ 𝟙 _ =
        rightDescentTranslateBase E sections V hVs hVa hVmem g ≫
          pullback.snd E.X.hom (structureMap E sections V hVs hVa hVmem)
      rw [Category.comp_id, rightDescentTranslateBase_snd])

@[reassoc (attr := simp)]
theorem rightDescentTranslateTotal_cover (g : G) :
    rightDescentTranslateTotal E sections V hVs hVa hVmem g ≫
        pullback.snd (projection E sections V hVs hVa hVmem)
          (rightDescentBaseToQuotient E sections V hVs hVa hVmem) =
      pullback.snd (projection E sections V hVs hVa hVmem)
          (rightDescentBaseToQuotient E sections V hVs hVa hVmem) ≫
        rightDescentTranslateBase E sections V hVs hVa hVmem g :=
  pullback.lift_snd _ _ _

/-- On `E ×_S E`, the lifted map translates exactly the first input. -/
theorem rightDescentTranslateTotal_pair (g : G) :
    rightDescentTranslateTotal E sections V hVs hVa hVmem g ≫
        rightDescentPair E sections V hVs hVa hVmem =
      rightDescentPair E sections V hVs hVa hVmem ≫
        (translateBy E (sections g) ⊗ₘ 𝟙 E.X).left := by
  apply pullback.hom_ext
  · have hcover := congrArg
      (fun f ↦ f ≫ pullback.fst E.X.hom
        (structureMap E sections V hVs hVa hVmem))
      (rightDescentTranslateTotal_cover E sections V hVs hVa hVmem g)
    have hbase := congrArg
      (fun f ↦ pullback.snd (projection E sections V hVs hVa hVmem)
        (rightDescentBaseToQuotient E sections V hVs hVa hVmem) ≫ f)
      (rightDescentTranslateBase_fst E sections V hVs hVa hVmem g)
    have hmid := (Category.assoc
      (rightDescentTranslateTotal E sections V hVs hVa hVmem g)
      (pullback.snd (projection E sections V hVs hVa hVmem)
        (rightDescentBaseToQuotient E sections V hVs hVa hVmem))
      (pullback.fst E.X.hom
        (structureMap E sections V hVs hVa hVmem))).symm.trans
      (hcover.trans ((Category.assoc
        (pullback.snd (projection E sections V hVs hVa hVmem)
          (rightDescentBaseToQuotient E sections V hVs hVa hVmem))
        (rightDescentTranslateBase E sections V hVs hVa hVmem g)
        (pullback.fst E.X.hom
          (structureMap E sections V hVs hVa hVmem))).trans
        (hbase.trans (Category.assoc
          (pullback.snd (projection E sections V hVs hVa hVmem)
            (rightDescentBaseToQuotient E sections V hVs hVa hVmem))
          (pullback.fst E.X.hom
            (structureMap E sections V hVs hVa hVmem))
          (translateBy E (sections g)).left).symm)))
    change rightDescentTranslateTotal E sections V hVs hVa hVmem g ≫
        rightDescentFirst E sections V hVs hVa hVmem =
      rightDescentFirst E sections V hVs hVa hVmem ≫
        (translateBy E (sections g)).left at hmid
    have htensor := Over.tensorHom_left_fst E.X.hom E.X.hom
      (translateBy E (sections g)) (𝟙 E.X)
    change (translateBy E (sections g) ⊗ₘ 𝟙 E.X).left ≫
        pullback.fst E.X.hom E.X.hom =
      pullback.fst E.X.hom E.X.hom ≫
        (translateBy E (sections g)).left at htensor
    have hpre := congrArg
      (fun f ↦ rightDescentTranslateTotal E sections V hVs hVa hVmem g ≫ f)
      (rightDescentPair_fst E sections V hVs hVa hVmem)
    have hstep := (Category.assoc
      (rightDescentTranslateTotal E sections V hVs hVa hVmem g)
      (rightDescentPair E sections V hVs hVa hVmem)
      (pullback.fst E.X.hom E.X.hom)).trans hpre
    have hpair := congrArg
      (fun f ↦ f ≫ (translateBy E (sections g)).left)
      (rightDescentPair_fst E sections V hVs hVa hVmem).symm
    have hpost := congrArg
      (fun f ↦ rightDescentPair E sections V hVs hVa hVmem ≫ f) htensor
    have hfinal := (Category.assoc
      (rightDescentPair E sections V hVs hVa hVmem)
      (translateBy E (sections g) ⊗ₘ 𝟙 E.X).left
      (pullback.fst E.X.hom E.X.hom)).trans (hpost.trans
        (Category.assoc (rightDescentPair E sections V hVs hVa hVmem)
          (pullback.fst E.X.hom E.X.hom)
          (translateBy E (sections g)).left).symm)
    exact hstep.trans (hmid.trans (hpair.trans hfinal.symm))
  · have hmid :
        rightDescentTranslateTotal E sections V hVs hVa hVmem g ≫
          rightDescentSecond E sections V hVs hVa hVmem =
        rightDescentSecond E sections V hVs hVa hVmem := by
      change pullback.lift
          (pullback.fst (projection E sections V hVs hVa hVmem)
              (rightDescentBaseToQuotient E sections V hVs hVa hVmem) ≫
            𝟙 E.X.left)
          (pullback.snd (projection E sections V hVs hVa hVmem)
              (rightDescentBaseToQuotient E sections V hVs hVa hVmem) ≫
            rightDescentTranslateBase E sections V hVs hVa hVmem g) _ ≫
            pullback.fst (projection E sections V hVs hVa hVmem)
              (rightDescentBaseToQuotient E sections V hVs hVa hVmem) =
        pullback.fst (projection E sections V hVs hVa hVmem)
          (rightDescentBaseToQuotient E sections V hVs hVa hVmem)
      rw [pullback.lift_fst, Category.comp_id]
    have htensor := Over.tensorHom_left_snd E.X.hom E.X.hom
      (translateBy E (sections g)) (𝟙 E.X)
    change (translateBy E (sections g) ⊗ₘ 𝟙 E.X).left ≫
        pullback.snd E.X.hom E.X.hom =
      pullback.snd E.X.hom E.X.hom ≫
        (𝟙 E.X : E.X ⟶ E.X).left at htensor
    rw [Over.id_left, Category.comp_id] at htensor
    have hpre := congrArg
      (fun f ↦ rightDescentTranslateTotal E sections V hVs hVa hVmem g ≫ f)
      (rightDescentPair_snd E sections V hVs hVa hVmem)
    have hstep := (Category.assoc
      (rightDescentTranslateTotal E sections V hVs hVa hVmem g)
      (rightDescentPair E sections V hVs hVa hVmem)
      (pullback.snd E.X.hom E.X.hom)).trans hpre
    have hpost := congrArg
      (fun f ↦ rightDescentPair E sections V hVs hVa hVmem ≫ f) htensor
    have hpoststep := (Category.assoc
      (rightDescentPair E sections V hVs hVa hVmem)
      (translateBy E (sections g) ⊗ₘ 𝟙 E.X).left
      (pullback.snd E.X.hom E.X.hom)).trans hpost
    exact hstep.trans (hmid.trans
      ((rightDescentPair_snd E sections V hVs hVa hVmem).symm.trans
        hpoststep.symm))

/-- The half-descended product remains invariant under translation in its `E`-variable. -/
theorem rightDescentTranslateBase_comp_mul (g : G) :
    rightDescentTranslateBase E sections V hVs hVa hVmem g ≫
        rightDescentMul E sections V hVs hVa hVmem hfree =
      rightDescentMul E sections V hVs hVa hVmem hfree := by
  letI := (translationAction E sections).epi_pullback_snd_quotientπ
    V hVs hVa hVmem
    (fun {T} t g hg hfix ↦ hfree g hg T t hfix)
    (rightDescentBaseToQuotient E sections V hVs hVa hVmem)
  rw [← cancel_epi (pullback.snd (projection E sections V hVs hVa hVmem)
    (rightDescentBaseToQuotient E sections V hVs hVa hVmem))]
  rw [← Category.assoc, ← rightDescentTranslateTotal_cover,
    Category.assoc, rightDescentCover_comp_mul, rightDescentRaw,
    ← Category.assoc, ← Category.assoc, rightDescentTranslateTotal_pair,
    Category.assoc, Category.assoc]
  have h := congrArg CommaMorphism.left
    (translateBy_tensor_id_comp_mul_comp_projectionOver
      E sections V hVs hVa hVmem g)
  change (translateBy E (sections g) ⊗ₘ 𝟙 E.X).left ≫
      μ[E.X].left ≫ projection E sections V hVs hVa hVmem =
    μ[E.X].left ≫ projection E sections V hVs hVa hVmem at h
  simpa only [Category.assoc] using
    congrArg (fun f ↦ rightDescentPair E sections V hVs hVa hVmem ≫ f) h

/-! ## Multiplication: descent in the first variable -/

@[reassoc]
theorem quotientTensor_fst_comp_structureMap :
    (fst (asOver E sections V hVs hVa hVmem)
          (asOver E sections V hVs hVa hVmem)).left ≫
        structureMap E sections V hVs hVa hVmem =
      (asOver E sections V hVs hVa hVmem ⊗
        asOver E sections V hVs hVa hVmem).hom :=
  (fst (asOver E sections V hVs hVa hVmem)
    (asOver E sections V hVs hVa hVmem)).w

@[reassoc]
theorem quotientTensor_snd_comp_structureMap :
    (snd (asOver E sections V hVs hVa hVmem)
          (asOver E sections V hVs hVa hVmem)).left ≫
        structureMap E sections V hVs hVa hVmem =
      (asOver E sections V hVs hVa hVmem ⊗
        asOver E sections V hVs hVa hVmem).hom :=
  (snd (asOver E sections V hVs hVa hVmem)
    (asOver E sections V hVs hVa hVmem)).w

/-- The second descent base, `(E/G) ×_S (E/G)`. -/
noncomputable abbrev mulDescentBase : Scheme.{u} :=
  (asOver E sections V hVs hVa hVmem ⊗
    asOver E sections V hVs hVa hVmem).left

/-- Its projection to the first quotient factor. -/
noncomputable abbrev mulDescentBaseToQuotient :
    mulDescentBase E sections V hVs hVa hVmem ⟶
      scheme E sections V hVs hVa :=
  (fst (asOver E sections V hVs hVa hVmem)
    (asOver E sections V hVs hVa hVmem)).left

/-- The base change of `q` used for the second descent. -/
noncomputable abbrev mulDescentTotal : Scheme.{u} :=
  pullback (projection E sections V hVs hVa hVmem)
    (mulDescentBaseToQuotient E sections V hVs hVa hVmem)

/-- The `E`-coordinate on the second descent total space. -/
noncomputable def mulDescentFirst :
    mulDescentTotal E sections V hVs hVa hVmem ⟶ E.X.left :=
  pullback.fst (projection E sections V hVs hVa hVmem)
    (mulDescentBaseToQuotient E sections V hVs hVa hVmem)

/-- The remaining quotient coordinate on the second descent total space. -/
noncomputable def mulDescentSecond :
    mulDescentTotal E sections V hVs hVa hVmem ⟶
      scheme E sections V hVs hVa :=
  pullback.snd (projection E sections V hVs hVa hVmem)
      (mulDescentBaseToQuotient E sections V hVs hVa hVmem) ≫
    (snd (asOver E sections V hVs hVa hVmem)
      (asOver E sections V hVs hVa hVmem)).left

theorem mulDescentFirst_comp_structureMap :
    mulDescentFirst E sections V hVs hVa hVmem ≫ E.X.hom =
      mulDescentSecond E sections V hVs hVa hVmem ≫
        structureMap E sections V hVs hVa hVmem := by
  calc
    mulDescentFirst E sections V hVs hVa hVmem ≫ E.X.hom =
        pullback.fst (projection E sections V hVs hVa hVmem)
            (mulDescentBaseToQuotient E sections V hVs hVa hVmem) ≫
          projection E sections V hVs hVa hVmem ≫
            structureMap E sections V hVs hVa hVmem := by
      simpa only [mulDescentFirst, Category.assoc] using
        congrArg (fun f ↦ pullback.fst
          (projection E sections V hVs hVa hVmem)
          (mulDescentBaseToQuotient E sections V hVs hVa hVmem) ≫ f)
          (projection_comp_structureMap (G := G)
            E sections V hVs hVa hVmem).symm
    _ = pullback.snd (projection E sections V hVs hVa hVmem)
          (mulDescentBaseToQuotient E sections V hVs hVa hVmem) ≫
        mulDescentBaseToQuotient E sections V hVs hVa hVmem ≫
          structureMap E sections V hVs hVa hVmem := by
      rw [← Category.assoc,
        pullback.condition
          (f := projection E sections V hVs hVa hVmem)
          (g := mulDescentBaseToQuotient E sections V hVs hVa hVmem),
        Category.assoc]
    _ = pullback.snd (projection E sections V hVs hVa hVmem)
          (mulDescentBaseToQuotient E sections V hVs hVa hVmem) ≫
        (snd (asOver E sections V hVs hVa hVmem)
          (asOver E sections V hVs hVa hVmem)).left ≫
            structureMap E sections V hVs hVa hVmem := by
      have h := (quotientTensor_fst_comp_structureMap
        E sections V hVs hVa hVmem).trans
          (quotientTensor_snd_comp_structureMap
            E sections V hVs hVa hVmem).symm
      change pullback.snd (projection E sections V hVs hVa hVmem)
            (mulDescentBaseToQuotient E sections V hVs hVa hVmem) ≫
          ((fst (asOver E sections V hVs hVa hVmem)
            (asOver E sections V hVs hVa hVmem)).left ≫
              structureMap E sections V hVs hVa hVmem) =
        pullback.snd (projection E sections V hVs hVa hVmem)
            (mulDescentBaseToQuotient E sections V hVs hVa hVmem) ≫
          ((snd (asOver E sections V hVs hVa hVmem)
            (asOver E sections V hVs hVa hVmem)).left ≫
              structureMap E sections V hVs hVa hVmem)
      exact congrArg
        (fun f ↦ pullback.snd (projection E sections V hVs hVa hVmem)
          (mulDescentBaseToQuotient E sections V hVs hVa hVmem) ≫ f) h
    _ = mulDescentSecond E sections V hVs hVa hVmem ≫
          structureMap E sections V hVs hVa hVmem := rfl

/-- The canonical comparison from the second base-changed torsor to `E ×_S (E/G)`. -/
noncomputable def mulDescentPair :
    mulDescentTotal E sections V hVs hVa hVmem ⟶
      rightDescentBase E sections V hVs hVa hVmem :=
  pullback.lift
    (mulDescentFirst E sections V hVs hVa hVmem)
    (mulDescentSecond E sections V hVs hVa hVmem)
    (mulDescentFirst_comp_structureMap E sections V hVs hVa hVmem)

@[reassoc (attr := simp)]
theorem mulDescentPair_fst :
    mulDescentPair E sections V hVs hVa hVmem ≫
        pullback.fst E.X.hom (structureMap E sections V hVs hVa hVmem) =
      mulDescentFirst E sections V hVs hVa hVmem :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem mulDescentPair_snd :
    mulDescentPair E sections V hVs hVa hVmem ≫
        pullback.snd E.X.hom (structureMap E sections V hVs hVa hVmem) =
      mulDescentSecond E sections V hVs hVa hVmem :=
  pullback.lift_snd _ _ _

include hfree in
/-- The half-descended product on the second base-changed torsor. -/
noncomputable def mulDescentRaw :
    mulDescentTotal E sections V hVs hVa hVmem ⟶
      scheme E sections V hVs hVa :=
  mulDescentPair E sections V hVs hVa hVmem ≫
    rightDescentMul E sections V hVs hVa hVmem hfree

/-- The pulled-back action changes exactly the `E`-coordinate of the half-product. -/
theorem pullbackAction_comp_mulDescentPair (g : G) :
    (ModularCurves.pullbackTorsorAction (translationAction E sections)
      (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g)
      (mulDescentBaseToQuotient E sections V hVs hVa hVmem)).hom g ≫
        mulDescentPair E sections V hVs hVa hVmem =
      mulDescentPair E sections V hVs hVa hVmem ≫
        rightDescentTranslateBase E sections V hVs hVa hVmem g := by
  apply pullback.hom_ext
  · have hmid := pullbackTorsorAction_fst E sections V hVs hVa hVmem
      (mulDescentBaseToQuotient E sections V hVs hVa hVmem) g
    change (ModularCurves.pullbackTorsorAction (translationAction E sections)
        (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g)
        (mulDescentBaseToQuotient E sections V hVs hVa hVmem)).hom g ≫
          mulDescentFirst E sections V hVs hVa hVmem =
      mulDescentFirst E sections V hVs hVa hVmem ≫
        (translateBy E (sections g)).left at hmid
    have hbase := rightDescentTranslateBase_fst E sections V hVs hVa hVmem g
    have hpre := congrArg
      (fun f ↦ (ModularCurves.pullbackTorsorAction (translationAction E sections)
        (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g)
        (mulDescentBaseToQuotient E sections V hVs hVa hVmem)).hom g ≫ f)
      (mulDescentPair_fst E sections V hVs hVa hVmem)
    have hstep := (Category.assoc
      ((ModularCurves.pullbackTorsorAction (translationAction E sections)
        (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g)
        (mulDescentBaseToQuotient E sections V hVs hVa hVmem)).hom g)
      (mulDescentPair E sections V hVs hVa hVmem)
      (pullback.fst E.X.hom
        (structureMap E sections V hVs hVa hVmem))).trans hpre
    have hpair := congrArg
      (fun f ↦ f ≫ (translateBy E (sections g)).left)
      (mulDescentPair_fst E sections V hVs hVa hVmem).symm
    have hpost := congrArg
      (fun f ↦ mulDescentPair E sections V hVs hVa hVmem ≫ f) hbase
    have hfinal := (Category.assoc
      (mulDescentPair E sections V hVs hVa hVmem)
      (rightDescentTranslateBase E sections V hVs hVa hVmem g)
      (pullback.fst E.X.hom
        (structureMap E sections V hVs hVa hVmem))).trans (hpost.trans
        (Category.assoc (mulDescentPair E sections V hVs hVa hVmem)
          (pullback.fst E.X.hom
            (structureMap E sections V hVs hVa hVmem))
          (translateBy E (sections g)).left).symm)
    exact hstep.trans (hmid.trans (hpair.trans hfinal.symm))
  · have hcover := ModularCurves.pullbackTorsorAction_over
      (translationAction E sections)
      (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g)
      (mulDescentBaseToQuotient E sections V hVs hVa hVmem) g
    change (ModularCurves.pullbackTorsorAction (translationAction E sections)
        (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g)
        (mulDescentBaseToQuotient E sections V hVs hVa hVmem)).hom g ≫
          pullback.snd (projection E sections V hVs hVa hVmem)
            (mulDescentBaseToQuotient E sections V hVs hVa hVmem) =
      pullback.snd (projection E sections V hVs hVa hVmem)
        (mulDescentBaseToQuotient E sections V hVs hVa hVmem) at hcover
    have hsecond := congrArg
      (fun f ↦ f ≫ (snd (asOver E sections V hVs hVa hVmem)
        (asOver E sections V hVs hVa hVmem)).left) hcover
    have hinv :
        (ModularCurves.pullbackTorsorAction (translationAction E sections)
          (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g)
          (mulDescentBaseToQuotient E sections V hVs hVa hVmem)).hom g ≫
            mulDescentSecond E sections V hVs hVa hVmem =
          mulDescentSecond E sections V hVs hVa hVmem := by
      change (ModularCurves.pullbackTorsorAction (translationAction E sections)
          (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g)
          (mulDescentBaseToQuotient E sections V hVs hVa hVmem)).hom g ≫
            pullback.snd (projection E sections V hVs hVa hVmem)
              (mulDescentBaseToQuotient E sections V hVs hVa hVmem) ≫
                (snd (asOver E sections V hVs hVa hVmem)
                  (asOver E sections V hVs hVa hVmem)).left =
        pullback.snd (projection E sections V hVs hVa hVmem)
            (mulDescentBaseToQuotient E sections V hVs hVa hVmem) ≫
          (snd (asOver E sections V hVs hVa hVmem)
            (asOver E sections V hVs hVa hVmem)).left
      exact (Category.assoc
        ((ModularCurves.pullbackTorsorAction (translationAction E sections)
          (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g)
          (mulDescentBaseToQuotient E sections V hVs hVa hVmem)).hom g)
        (pullback.snd (projection E sections V hVs hVa hVmem)
          (mulDescentBaseToQuotient E sections V hVs hVa hVmem))
        (snd (asOver E sections V hVs hVa hVmem)
          (asOver E sections V hVs hVa hVmem)).left).symm.trans hsecond
    have hbase := rightDescentTranslateBase_snd E sections V hVs hVa hVmem g
    have hpre := congrArg
      (fun f ↦ (ModularCurves.pullbackTorsorAction (translationAction E sections)
        (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g)
        (mulDescentBaseToQuotient E sections V hVs hVa hVmem)).hom g ≫ f)
      (mulDescentPair_snd E sections V hVs hVa hVmem)
    have hstep := (Category.assoc
      ((ModularCurves.pullbackTorsorAction (translationAction E sections)
        (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g)
        (mulDescentBaseToQuotient E sections V hVs hVa hVmem)).hom g)
      (mulDescentPair E sections V hVs hVa hVmem)
      (pullback.snd E.X.hom
        (structureMap E sections V hVs hVa hVmem))).trans hpre
    have hpost := congrArg
      (fun f ↦ mulDescentPair E sections V hVs hVa hVmem ≫ f) hbase
    have hpoststep := (Category.assoc
      (mulDescentPair E sections V hVs hVa hVmem)
      (rightDescentTranslateBase E sections V hVs hVa hVmem g)
      (pullback.snd E.X.hom
        (structureMap E sections V hVs hVa hVmem))).trans hpost
    exact hstep.trans (hinv.trans
      ((mulDescentPair_snd E sections V hVs hVa hVmem).symm.trans
        hpoststep.symm))

/-- The half-product is invariant on the second descent torsor. -/
theorem pullbackAction_comp_mulDescentRaw (g : G) :
    (ModularCurves.pullbackTorsorAction (translationAction E sections)
      (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g)
      (mulDescentBaseToQuotient E sections V hVs hVa hVmem)).hom g ≫
        mulDescentRaw E sections V hVs hVa hVmem hfree =
      mulDescentRaw E sections V hVs hVa hVmem hfree := by
  rw [mulDescentRaw, ← Category.assoc,
    pullbackAction_comp_mulDescentPair E sections V hVs hVa hVmem g,
    Category.assoc,
    rightDescentTranslateBase_comp_mul E sections V hVs hVa hVmem hfree g]

include hfree in
/-- Multiplication on the underlying quotient scheme, obtained by two torsor descents. -/
noncomputable def mul :
    mulDescentBase E sections V hVs hVa hVmem ⟶
      scheme E sections V hVs hVa :=
  (existsUnique_descent_baseChange E sections V hVs hVa hVmem hfree
    (mulDescentBaseToQuotient E sections V hVs hVa hVmem)
    (mulDescentRaw E sections V hVs hVa hVmem hfree)
    (pullbackAction_comp_mulDescentRaw E sections V hVs hVa hVmem hfree)).choose

@[reassoc]
theorem mulDescentCover_comp_mul :
    pullback.snd (projection E sections V hVs hVa hVmem)
        (mulDescentBaseToQuotient E sections V hVs hVa hVmem) ≫
      mul E sections V hVs hVa hVmem hfree =
    mulDescentRaw E sections V hVs hVa hVmem hfree :=
  (existsUnique_descent_baseChange E sections V hVs hVa hVmem hfree
    (mulDescentBaseToQuotient E sections V hVs hVa hVmem)
    (mulDescentRaw E sections V hVs hVa hVmem hfree)
    (pullbackAction_comp_mulDescentRaw E sections V hVs hVa hVmem hfree)).choose_spec.1

/-- The descended multiplication is a morphism over `S`. -/
theorem mul_comp_structureMap :
    mul E sections V hVs hVa hVmem hfree ≫
        structureMap E sections V hVs hVa hVmem =
      (asOver E sections V hVs hVa hVmem ⊗
        asOver E sections V hVs hVa hVmem).hom := by
  letI := (translationAction E sections).epi_pullback_snd_quotientπ
    V hVs hVa hVmem
    (fun {T} t g hg hfix ↦ hfree g hg T t hfix)
    (mulDescentBaseToQuotient E sections V hVs hVa hVmem)
  rw [← cancel_epi (pullback.snd (projection E sections V hVs hVa hVmem)
    (mulDescentBaseToQuotient E sections V hVs hVa hVmem))]
  rw [← Category.assoc,
    mulDescentCover_comp_mul (G := G) E sections V hVs hVa hVmem hfree]
  change (mulDescentPair E sections V hVs hVa hVmem ≫
      rightDescentMul E sections V hVs hVa hVmem hfree) ≫
        structureMap E sections V hVs hVa hVmem = _
  rw [Category.assoc,
    rightDescentMul_comp_structureMap (G := G)
      E sections V hVs hVa hVmem hfree]
  change mulDescentPair E sections V hVs hVa hVmem ≫
      (pullback.fst E.X.hom (structureMap E sections V hVs hVa hVmem) ≫
        E.X.hom) =
    pullback.snd (projection E sections V hVs hVa hVmem)
      (mulDescentBaseToQuotient E sections V hVs hVa hVmem) ≫
      (pullback.fst (structureMap E sections V hVs hVa hVmem)
        (structureMap E sections V hVs hVa hVmem) ≫
          structureMap E sections V hVs hVa hVmem)
  calc
    mulDescentPair E sections V hVs hVa hVmem ≫
          pullback.fst E.X.hom
            (structureMap E sections V hVs hVa hVmem) ≫ E.X.hom =
        mulDescentFirst E sections V hVs hVa hVmem ≫ E.X.hom :=
      mulDescentPair_fst_assoc E sections V hVs hVa hVmem E.X.hom
    _ = mulDescentSecond E sections V hVs hVa hVmem ≫
          structureMap E sections V hVs hVa hVmem :=
      mulDescentFirst_comp_structureMap E sections V hVs hVa hVmem
    _ = (pullback.snd (projection E sections V hVs hVa hVmem)
          (mulDescentBaseToQuotient E sections V hVs hVa hVmem) ≫
        (snd (asOver E sections V hVs hVa hVmem)
          (asOver E sections V hVs hVa hVmem)).left) ≫
            structureMap E sections V hVs hVa hVmem := rfl
    _ = pullback.snd (projection E sections V hVs hVa hVmem)
          (mulDescentBaseToQuotient E sections V hVs hVa hVmem) ≫
        pullback.fst (structureMap E sections V hVs hVa hVmem)
          (structureMap E sections V hVs hVa hVmem) ≫
            structureMap E sections V hVs hVa hVmem := by
      have h := (quotientTensor_snd_comp_structureMap
        E sections V hVs hVa hVmem).trans
          (quotientTensor_fst_comp_structureMap
            E sections V hVs hVa hVmem).symm
      change pullback.snd (projection E sections V hVs hVa hVmem)
            (mulDescentBaseToQuotient E sections V hVs hVa hVmem) ≫
          ((snd (asOver E sections V hVs hVa hVmem)
            (asOver E sections V hVs hVa hVmem)).left ≫
              structureMap E sections V hVs hVa hVmem) =
        pullback.snd (projection E sections V hVs hVa hVmem)
            (mulDescentBaseToQuotient E sections V hVs hVa hVmem) ≫
          ((fst (asOver E sections V hVs hVa hVmem)
            (asOver E sections V hVs hVa hVmem)).left ≫
              structureMap E sections V hVs hVa hVmem)
      exact congrArg
        (fun f ↦ pullback.snd (projection E sections V hVs hVa hVmem)
          (mulDescentBaseToQuotient E sections V hVs hVa hVmem) ≫ f) h

include hfree in
/-- Multiplication on the quotient in the slice category. -/
noncomputable def mulOver :
    asOver E sections V hVs hVa hVmem ⊗ asOver E sections V hVs hVa hVmem ⟶
      asOver E sections V hVs hVa hVmem :=
  Over.homMk (mul E sections V hVs hVa hVmem hfree)
    (mul_comp_structureMap E sections V hVs hVa hVmem hfree)

/-! ## Defining equation for multiplication -/

/-- The comparison from `E ×_S E` to the first canonical base-changed torsor. -/
noncomputable def rightDescentLift :
    (E.X ⊗ E.X).left ⟶ rightDescentTotal E sections V hVs hVa hVmem :=
  pullback.lift
    (pullback.snd E.X.hom E.X.hom)
    ((𝟙 E.X ⊗ₘ projectionOver E sections V hVs hVa hVmem).left)
    (by
      exact (Over.tensorHom_left_snd E.X.hom
        (structureMap E sections V hVs hVa hVmem)
        (𝟙 E.X) (projectionOver E sections V hVs hVa hVmem)).symm)

@[reassoc (attr := simp)]
theorem rightDescentLift_cover :
    rightDescentLift E sections V hVs hVa hVmem ≫
        pullback.snd (projection E sections V hVs hVa hVmem)
          (rightDescentBaseToQuotient E sections V hVs hVa hVmem) =
      (𝟙 E.X ⊗ₘ projectionOver E sections V hVs hVa hVmem).left :=
  pullback.lift_snd _ _ _

/-- The first comparison recovers the two original `E`-coordinates. -/
theorem rightDescentLift_pair :
    rightDescentLift E sections V hVs hVa hVmem ≫
        rightDescentPair E sections V hVs hVa hVmem = 𝟙 (E.X ⊗ E.X).left := by
  apply Over.tensorObj_ext
  · change (rightDescentLift E sections V hVs hVa hVmem ≫
        rightDescentPair E sections V hVs hVa hVmem) ≫
          (fst E.X E.X).left =
      𝟙 (E.X ⊗ E.X).left ≫ (fst E.X E.X).left
    have hpair := rightDescentPair_fst E sections V hVs hVa hVmem
    change rightDescentPair E sections V hVs hVa hVmem ≫
        (fst E.X E.X).left =
      rightDescentFirst E sections V hVs hVa hVmem at hpair
    have hpre := congrArg
      (fun f ↦ rightDescentLift E sections V hVs hVa hVmem ≫ f) hpair
    have hstep := (Category.assoc
      (rightDescentLift E sections V hVs hVa hVmem)
      (rightDescentPair E sections V hVs hVa hVmem)
      (fst E.X E.X).left).trans hpre
    have hcover := rightDescentLift_cover E sections V hVs hVa hVmem
    have hcoverPost := congrArg
      (fun f ↦ f ≫ (fst E.X
        (asOver E sections V hVs hVa hVmem)).left) hcover
    have hfirst :
        rightDescentLift E sections V hVs hVa hVmem ≫
            rightDescentFirst E sections V hVs hVa hVmem =
          (𝟙 E.X ⊗ₘ projectionOver E sections V hVs hVa hVmem).left ≫
            (fst E.X (asOver E sections V hVs hVa hVmem)).left := by
      change rightDescentLift E sections V hVs hVa hVmem ≫
          (pullback.snd (projection E sections V hVs hVa hVmem)
              (rightDescentBaseToQuotient E sections V hVs hVa hVmem) ≫
            (fst E.X (asOver E sections V hVs hVa hVmem)).left) =
        (𝟙 E.X ⊗ₘ projectionOver E sections V hVs hVa hVmem).left ≫
          (fst E.X (asOver E sections V hVs hVa hVmem)).left
      exact (Category.assoc
        (rightDescentLift E sections V hVs hVa hVmem)
        (pullback.snd (projection E sections V hVs hVa hVmem)
          (rightDescentBaseToQuotient E sections V hVs hVa hVmem))
        (fst E.X (asOver E sections V hVs hVa hVmem)).left).symm.trans
          hcoverPost
    have htensor := Over.tensorHom_left_fst E.X.hom
      (structureMap E sections V hVs hVa hVmem)
      (𝟙 E.X) (projectionOver E sections V hVs hVa hVmem)
    change (𝟙 E.X ⊗ₘ projectionOver E sections V hVs hVa hVmem).left ≫
        (fst E.X (asOver E sections V hVs hVa hVmem)).left =
      (fst E.X E.X).left ≫ (𝟙 E.X : E.X ⟶ E.X).left at htensor
    rw [Over.id_left, Category.comp_id] at htensor
    exact hstep.trans (hfirst.trans
      (htensor.trans (Category.id_comp (fst E.X E.X).left).symm))
  · change (rightDescentLift E sections V hVs hVa hVmem ≫
        rightDescentPair E sections V hVs hVa hVmem) ≫
          (snd E.X E.X).left =
      𝟙 (E.X ⊗ E.X).left ≫ (snd E.X E.X).left
    have hpair := rightDescentPair_snd E sections V hVs hVa hVmem
    change rightDescentPair E sections V hVs hVa hVmem ≫
        (snd E.X E.X).left =
      rightDescentSecond E sections V hVs hVa hVmem at hpair
    have hpre := congrArg
      (fun f ↦ rightDescentLift E sections V hVs hVa hVmem ≫ f) hpair
    have hstep := (Category.assoc
      (rightDescentLift E sections V hVs hVa hVmem)
      (rightDescentPair E sections V hVs hVa hVmem)
      (snd E.X E.X).left).trans hpre
    have hlift :
        rightDescentLift E sections V hVs hVa hVmem ≫
            rightDescentSecond E sections V hVs hVa hVmem =
          (snd E.X E.X).left := by
      change pullback.lift
          (pullback.snd E.X.hom E.X.hom)
          ((𝟙 E.X ⊗ₘ projectionOver E sections V hVs hVa hVmem).left) _ ≫
            pullback.fst (projection E sections V hVs hVa hVmem)
              (rightDescentBaseToQuotient E sections V hVs hVa hVmem) =
        (snd E.X E.X).left
      exact pullback.lift_fst _ _ _
    exact hstep.trans
      (hlift.trans (Category.id_comp (snd E.X E.X).left).symm)

/-- Defining equation of the half-descended product. -/
theorem id_tensor_projectionOver_comp_rightDescentMul :
    (𝟙 E.X ⊗ₘ projectionOver E sections V hVs hVa hVmem).left ≫
        rightDescentMul E sections V hVs hVa hVmem hfree =
      μ[E.X].left ≫ projection E sections V hVs hVa hVmem := by
  rw [← rightDescentLift_cover E sections V hVs hVa hVmem,
    Category.assoc, rightDescentCover_comp_mul, rightDescentRaw,
    ← Category.assoc, ← Category.assoc, rightDescentLift_pair,
    Category.id_comp]

/-- The comparison from `E ×_S (E/G)` to the second canonical base-changed torsor. -/
noncomputable def mulDescentLift :
    rightDescentBase E sections V hVs hVa hVmem ⟶
      mulDescentTotal E sections V hVs hVa hVmem :=
  pullback.lift
    (pullback.fst E.X.hom (structureMap E sections V hVs hVa hVmem))
    ((projectionOver E sections V hVs hVa hVmem ⊗ₘ
      𝟙 (asOver E sections V hVs hVa hVmem)).left)
    (by
      exact (Over.tensorHom_left_fst
        (structureMap E sections V hVs hVa hVmem)
        (structureMap E sections V hVs hVa hVmem)
        (projectionOver E sections V hVs hVa hVmem)
        (𝟙 (asOver E sections V hVs hVa hVmem))).symm)

@[reassoc (attr := simp)]
theorem mulDescentLift_cover :
    mulDescentLift E sections V hVs hVa hVmem ≫
        pullback.snd (projection E sections V hVs hVa hVmem)
          (mulDescentBaseToQuotient E sections V hVs hVa hVmem) =
      (projectionOver E sections V hVs hVa hVmem ⊗ₘ
        𝟙 (asOver E sections V hVs hVa hVmem)).left :=
  pullback.lift_snd _ _ _

/-- The second comparison recovers `E ×_S (E/G)`. -/
theorem mulDescentLift_pair :
    mulDescentLift E sections V hVs hVa hVmem ≫
        mulDescentPair E sections V hVs hVa hVmem =
      𝟙 (rightDescentBase E sections V hVs hVa hVmem) := by
  apply Over.tensorObj_ext
  · change (mulDescentLift E sections V hVs hVa hVmem ≫
        mulDescentPair E sections V hVs hVa hVmem) ≫
          (fst E.X (asOver E sections V hVs hVa hVmem)).left =
      𝟙 (rightDescentBase E sections V hVs hVa hVmem) ≫
        (fst E.X (asOver E sections V hVs hVa hVmem)).left
    have hpair := mulDescentPair_fst E sections V hVs hVa hVmem
    change mulDescentPair E sections V hVs hVa hVmem ≫
        (fst E.X (asOver E sections V hVs hVa hVmem)).left =
      mulDescentFirst E sections V hVs hVa hVmem at hpair
    have hpre := congrArg
      (fun f ↦ mulDescentLift E sections V hVs hVa hVmem ≫ f) hpair
    have hstep := (Category.assoc
      (mulDescentLift E sections V hVs hVa hVmem)
      (mulDescentPair E sections V hVs hVa hVmem)
      (fst E.X (asOver E sections V hVs hVa hVmem)).left).trans hpre
    have hlift :
        mulDescentLift E sections V hVs hVa hVmem ≫
            mulDescentFirst E sections V hVs hVa hVmem =
          (fst E.X (asOver E sections V hVs hVa hVmem)).left := by
      change pullback.lift
          (pullback.fst E.X.hom
            (structureMap E sections V hVs hVa hVmem))
          ((projectionOver E sections V hVs hVa hVmem ⊗ₘ
            𝟙 (asOver E sections V hVs hVa hVmem)).left) _ ≫
            pullback.fst (projection E sections V hVs hVa hVmem)
              (mulDescentBaseToQuotient E sections V hVs hVa hVmem) =
        (fst E.X (asOver E sections V hVs hVa hVmem)).left
      exact pullback.lift_fst _ _ _
    exact hstep.trans
      (hlift.trans (Category.id_comp
        (fst E.X (asOver E sections V hVs hVa hVmem)).left).symm)
  · change (mulDescentLift E sections V hVs hVa hVmem ≫
        mulDescentPair E sections V hVs hVa hVmem) ≫
          (snd E.X (asOver E sections V hVs hVa hVmem)).left =
      𝟙 (rightDescentBase E sections V hVs hVa hVmem) ≫
        (snd E.X (asOver E sections V hVs hVa hVmem)).left
    have hpair := mulDescentPair_snd E sections V hVs hVa hVmem
    change mulDescentPair E sections V hVs hVa hVmem ≫
        (snd E.X (asOver E sections V hVs hVa hVmem)).left =
      mulDescentSecond E sections V hVs hVa hVmem at hpair
    have hpre := congrArg
      (fun f ↦ mulDescentLift E sections V hVs hVa hVmem ≫ f) hpair
    have hstep := (Category.assoc
      (mulDescentLift E sections V hVs hVa hVmem)
      (mulDescentPair E sections V hVs hVa hVmem)
      (snd E.X (asOver E sections V hVs hVa hVmem)).left).trans hpre
    have hcover := mulDescentLift_cover E sections V hVs hVa hVmem
    have hcoverPost := congrArg
      (fun f ↦ f ≫ (snd (asOver E sections V hVs hVa hVmem)
        (asOver E sections V hVs hVa hVmem)).left) hcover
    have hsecond :
        mulDescentLift E sections V hVs hVa hVmem ≫
            mulDescentSecond E sections V hVs hVa hVmem =
          (projectionOver E sections V hVs hVa hVmem ⊗ₘ
              𝟙 (asOver E sections V hVs hVa hVmem)).left ≫
            (snd (asOver E sections V hVs hVa hVmem)
              (asOver E sections V hVs hVa hVmem)).left := by
      change mulDescentLift E sections V hVs hVa hVmem ≫
          (pullback.snd (projection E sections V hVs hVa hVmem)
              (mulDescentBaseToQuotient E sections V hVs hVa hVmem) ≫
            (snd (asOver E sections V hVs hVa hVmem)
              (asOver E sections V hVs hVa hVmem)).left) =
        (projectionOver E sections V hVs hVa hVmem ⊗ₘ
            𝟙 (asOver E sections V hVs hVa hVmem)).left ≫
          (snd (asOver E sections V hVs hVa hVmem)
            (asOver E sections V hVs hVa hVmem)).left
      exact (Category.assoc
        (mulDescentLift E sections V hVs hVa hVmem)
        (pullback.snd (projection E sections V hVs hVa hVmem)
          (mulDescentBaseToQuotient E sections V hVs hVa hVmem))
        (snd (asOver E sections V hVs hVa hVmem)
          (asOver E sections V hVs hVa hVmem)).left).symm.trans hcoverPost
    have htensor := Over.tensorHom_left_snd
      (structureMap E sections V hVs hVa hVmem)
      (structureMap E sections V hVs hVa hVmem)
      (projectionOver E sections V hVs hVa hVmem)
      (𝟙 (asOver E sections V hVs hVa hVmem))
    change (projectionOver E sections V hVs hVa hVmem ⊗ₘ
        𝟙 (asOver E sections V hVs hVa hVmem)).left ≫
          (snd (asOver E sections V hVs hVa hVmem)
            (asOver E sections V hVs hVa hVmem)).left =
      (snd E.X (asOver E sections V hVs hVa hVmem)).left ≫
        (𝟙 (asOver E sections V hVs hVa hVmem) :
          asOver E sections V hVs hVa hVmem ⟶
            asOver E sections V hVs hVa hVmem).left at htensor
    rw [Over.id_left, Category.comp_id] at htensor
    exact hstep.trans (hsecond.trans
      (htensor.trans (Category.id_comp
        (snd E.X (asOver E sections V hVs hVa hVmem)).left).symm))

/-- Defining equation after the second descent. -/
theorem projectionOver_tensor_id_comp_mul :
    (projectionOver E sections V hVs hVa hVmem ⊗ₘ
        𝟙 (asOver E sections V hVs hVa hVmem)).left ≫
      mul E sections V hVs hVa hVmem hfree =
    rightDescentMul E sections V hVs hVa hVmem hfree := by
  rw [← mulDescentLift_cover E sections V hVs hVa hVmem,
    Category.assoc, mulDescentCover_comp_mul, mulDescentRaw,
    ← Category.assoc, mulDescentLift_pair, Category.id_comp]

/-- The quotient projection preserves multiplication. -/
@[reassoc (attr := simp)]
theorem projectionOver_mul :
    μ[E.X] ≫ projectionOver E sections V hVs hVa hVmem =
      (projectionOver E sections V hVs hVa hVmem ⊗ₘ
        projectionOver E sections V hVs hVa hVmem) ≫
          mulOver E sections V hVs hVa hVmem hfree := by
  apply Over.OverMorphism.ext
  change μ[E.X].left ≫ projection E sections V hVs hVa hVmem = _
  rw [← id_tensor_projectionOver_comp_rightDescentMul
      E sections V hVs hVa hVmem hfree,
    ← projectionOver_tensor_id_comp_mul E sections V hVs hVa hVmem hfree,
    ← Category.assoc]
  congr 1
  simpa only [Over.comp_left, MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_id] using
    congrArg CommaMorphism.left
      (MonoidalCategory.tensorHom_def'
        (projectionOver E sections V hVs hVa hVmem)
        (projectionOver E sections V hVs hVa hVmem)).symm

/-! ## Epimorphic product covers -/

/-- The canonical pullback used to recognize `q ⊗ id_R` as a base change of `q`. -/
noncomputable abbrev whiskerRightTotal (R : Over S) : Scheme.{u} :=
  pullback (projection E sections V hVs hVa hVmem)
    (pullback.fst (structureMap E sections V hVs hVa hVmem) R.hom)

/-- Comparison from `E ×_S R` to the canonical pullback presenting `q × id_R`. -/
noncomputable def whiskerRightLift (R : Over S) :
    (E.X ⊗ R).left ⟶ whiskerRightTotal E sections V hVs hVa hVmem R :=
  pullback.lift (pullback.fst E.X.hom R.hom)
    ((projectionOver E sections V hVs hVa hVmem ▷ R).left)
    (by
      change pullback.fst E.X.hom R.hom ≫
          (projectionOver E sections V hVs hVa hVmem).left =
        (projectionOver E sections V hVs hVa hVmem ▷ R).left ≫
          pullback.fst (asOver E sections V hVs hVa hVmem).hom R.hom
      exact (Over.whiskerRight_left_fst (R := R)
        (projectionOver E sections V hVs hVa hVmem)).symm)

/-- The inverse comparison, obtained from the two evident coordinates. -/
noncomputable def whiskerRightPair (R : Over S) :
    whiskerRightTotal E sections V hVs hVa hVmem R ⟶ (E.X ⊗ R).left :=
  pullback.lift
    (pullback.fst (projection E sections V hVs hVa hVmem)
      (pullback.fst (structureMap E sections V hVs hVa hVmem) R.hom))
    (pullback.snd (projection E sections V hVs hVa hVmem)
        (pullback.fst (structureMap E sections V hVs hVa hVmem) R.hom) ≫
      pullback.snd (structureMap E sections V hVs hVa hVmem) R.hom)
    (by
      rw [← projection_comp_structureMap (G := G)
        E sections V hVs hVa hVmem,
        ← Category.assoc,
        pullback.condition
          (f := projection E sections V hVs hVa hVmem)
          (g := pullback.fst (structureMap E sections V hVs hVa hVmem) R.hom),
        Category.assoc,
        pullback.condition
          (f := structureMap E sections V hVs hVa hVmem) (g := R.hom)]
      exact (Category.assoc _ _ _).symm)

@[reassoc (attr := simp)]
theorem whiskerRightLift_cover (R : Over S) :
    whiskerRightLift E sections V hVs hVa hVmem R ≫
        pullback.snd (projection E sections V hVs hVa hVmem)
          (pullback.fst (structureMap E sections V hVs hVa hVmem) R.hom) =
      (projectionOver E sections V hVs hVa hVmem ▷ R).left :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem whiskerRightLift_fst (R : Over S) :
    whiskerRightLift E sections V hVs hVa hVmem R ≫
        pullback.fst (projection E sections V hVs hVa hVmem)
          (pullback.fst (structureMap E sections V hVs hVa hVmem) R.hom) =
      pullback.fst E.X.hom R.hom :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem whiskerRightPair_fst (R : Over S) :
    whiskerRightPair E sections V hVs hVa hVmem R ≫
        pullback.fst E.X.hom R.hom =
      pullback.fst (projection E sections V hVs hVa hVmem)
        (pullback.fst (structureMap E sections V hVs hVa hVmem) R.hom) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem whiskerRightPair_snd (R : Over S) :
    whiskerRightPair E sections V hVs hVa hVmem R ≫
        pullback.snd E.X.hom R.hom =
      pullback.snd (projection E sections V hVs hVa hVmem)
          (pullback.fst (structureMap E sections V hVs hVa hVmem) R.hom) ≫
        pullback.snd (structureMap E sections V hVs hVa hVmem) R.hom :=
  pullback.lift_snd _ _ _

theorem whiskerRightLift_pair (R : Over S) :
    whiskerRightLift E sections V hVs hVa hVmem R ≫
      whiskerRightPair E sections V hVs hVa hVmem R = 𝟙 (E.X ⊗ R).left := by
  exact Over.tensorObj_ext _ _
    ((Category.assoc
        (whiskerRightLift E sections V hVs hVa hVmem R)
        (whiskerRightPair E sections V hVs hVa hVmem R)
        (pullback.fst E.X.hom R.hom)).trans
      ((congrArg
        (fun f ↦ whiskerRightLift E sections V hVs hVa hVmem R ≫ f)
        (whiskerRightPair_fst (G := G)
          E sections V hVs hVa hVmem R)).trans
        ((whiskerRightLift_fst (G := G)
          E sections V hVs hVa hVmem R).trans
          (Category.id_comp _).symm)))
    ((Category.assoc
        (whiskerRightLift E sections V hVs hVa hVmem R)
        (whiskerRightPair E sections V hVs hVa hVmem R)
        (pullback.snd E.X.hom R.hom)).trans
      ((congrArg
        (fun f ↦ whiskerRightLift E sections V hVs hVa hVmem R ≫ f)
        (whiskerRightPair_snd (G := G)
          E sections V hVs hVa hVmem R)).trans
        ((Category.assoc
          (whiskerRightLift E sections V hVs hVa hVmem R)
          (pullback.snd (projection E sections V hVs hVa hVmem)
            (pullback.fst (structureMap E sections V hVs hVa hVmem) R.hom))
          (pullback.snd (structureMap E sections V hVs hVa hVmem) R.hom)).symm.trans
          ((congrArg
            (fun f ↦ f ≫
              pullback.snd (structureMap E sections V hVs hVa hVmem) R.hom)
            (whiskerRightLift_cover (G := G)
              E sections V hVs hVa hVmem R)).trans
            ((Over.whiskerRight_left_snd
              (projectionOver E sections V hVs hVa hVmem)).trans
              (Category.id_comp _).symm)))))

theorem whiskerRightPair_lift (R : Over S) :
    whiskerRightPair E sections V hVs hVa hVmem R ≫
      whiskerRightLift E sections V hVs hVa hVmem R =
        𝟙 (whiskerRightTotal E sections V hVs hVa hVmem R) := by
  have hpair : whiskerRightPair E sections V hVs hVa hVmem R ≫
        (projectionOver E sections V hVs hVa hVmem ▷ R).left =
      pullback.snd (projection E sections V hVs hVa hVmem)
        (pullback.fst (structureMap E sections V hVs hVa hVmem) R.hom) :=
    Over.tensorObj_ext _ _
      ((Category.assoc
          (whiskerRightPair E sections V hVs hVa hVmem R)
          (projectionOver E sections V hVs hVa hVmem ▷ R).left
          (pullback.fst (structureMap E sections V hVs hVa hVmem) R.hom)).trans
        ((congrArg
          (fun f ↦ whiskerRightPair E sections V hVs hVa hVmem R ≫ f)
          (Over.whiskerRight_left_fst
            (projectionOver E sections V hVs hVa hVmem))).trans
          ((Category.assoc
            (whiskerRightPair E sections V hVs hVa hVmem R)
            (pullback.fst E.X.hom R.hom)
            (projection E sections V hVs hVa hVmem)).symm.trans
            ((congrArg
              (fun f ↦ f ≫ projection E sections V hVs hVa hVmem)
              (whiskerRightPair_fst (G := G)
                E sections V hVs hVa hVmem R)).trans
              (pullback.condition
                (f := projection E sections V hVs hVa hVmem)
                (g := pullback.fst
                  (structureMap E sections V hVs hVa hVmem) R.hom))))))
      ((Category.assoc
          (whiskerRightPair E sections V hVs hVa hVmem R)
          (projectionOver E sections V hVs hVa hVmem ▷ R).left
          (pullback.snd (structureMap E sections V hVs hVa hVmem) R.hom)).trans
        ((congrArg
          (fun f ↦ whiskerRightPair E sections V hVs hVa hVmem R ≫ f)
          (Over.whiskerRight_left_snd
            (projectionOver E sections V hVs hVa hVmem))).trans
          (whiskerRightPair_snd (G := G)
            E sections V hVs hVa hVmem R)))
  apply pullback.hom_ext
  · exact (Category.assoc
      (whiskerRightPair E sections V hVs hVa hVmem R)
      (whiskerRightLift E sections V hVs hVa hVmem R)
      (pullback.fst (projection E sections V hVs hVa hVmem)
        (pullback.fst (structureMap E sections V hVs hVa hVmem) R.hom))).trans
        ((congrArg
          (fun f ↦ whiskerRightPair E sections V hVs hVa hVmem R ≫ f)
          (whiskerRightLift_fst (G := G)
            E sections V hVs hVa hVmem R)).trans
          ((whiskerRightPair_fst (G := G)
            E sections V hVs hVa hVmem R).trans
            (Category.id_comp _).symm))
  · exact (Category.assoc
      (whiskerRightPair E sections V hVs hVa hVmem R)
      (whiskerRightLift E sections V hVs hVa hVmem R)
      (pullback.snd (projection E sections V hVs hVa hVmem)
        (pullback.fst (structureMap E sections V hVs hVa hVmem) R.hom))).trans
        ((congrArg
          (fun f ↦ whiskerRightPair E sections V hVs hVa hVmem R ≫ f)
          (whiskerRightLift_cover (G := G)
            E sections V hVs hVa hVmem R)).trans
          (hpair.trans (Category.id_comp _).symm))

/-- The comparison recognizing `q × id_R` as a base change is an isomorphism. -/
instance whiskerRightLift_isIso (R : Over S) :
    IsIso (whiskerRightLift E sections V hVs hVa hVmem R) :=
  ⟨whiskerRightPair (G := G) E sections V hVs hVa hVmem R,
    whiskerRightLift_pair (G := G) E sections V hVs hVa hVmem R,
    whiskerRightPair_lift (G := G) E sections V hVs hVa hVmem R⟩

include hfree in
/-- Products of the quotient projection with an identity are epimorphisms. -/
theorem projectionOver_whiskerRight_epi (R : Over S) :
    Epi (projectionOver E sections V hVs hVa hVmem ▷ R) := by
  letI hbase : Epi (pullback.snd
      (projection E sections V hVs hVa hVmem)
      (pullback.fst (structureMap E sections V hVs hVa hVmem) R.hom)) :=
    (translationAction E sections).epi_pullback_snd_quotientπ
      V hVs hVa hVmem
      (fun {T} t g hg hfix ↦ hfree g hg T t hfix)
      (pullback.fst (structureMap E sections V hVs hVa hVmem) R.hom)
  letI hliftIso : IsIso (whiskerRightLift (G := G)
      E sections V hVs hVa hVmem R) :=
    whiskerRightLift_isIso (G := G) E sections V hVs hVa hVmem R
  letI hliftEpi : Epi (whiskerRightLift (G := G)
      E sections V hVs hVa hVmem R) := inferInstance
  haveI : Epi ((projectionOver E sections V hVs hVa hVmem ▷ R).left) := by
    rw [← whiskerRightLift_cover (G := G) E sections V hVs hVa hVmem R]
    exact epi_comp' hliftEpi hbase
  exact Over.epi_of_epi_left _

include hfree in
/-- Identities tensored with the quotient projection are epimorphisms as well. -/
theorem whiskerLeft_projectionOver_epi (R : Over S) :
    Epi (R ◁ projectionOver E sections V hVs hVa hVmem) := by
  letI : Epi (projectionOver E sections V hVs hVa hVmem ▷ R) :=
    projectionOver_whiskerRight_epi E sections V hVs hVa hVmem hfree R
  have hfactor :
      (β_ R E.X).hom ≫
          (projectionOver E sections V hVs hVa hVmem ▷ R) ≫
          (β_ R (asOver E sections V hVs hVa hVmem)).inv =
        R ◁ projectionOver E sections V hVs hVa hVmem := by
    simpa only [MonoidalCategory.tensorHom_id,
      MonoidalCategory.id_tensorHom, Category.assoc,
      Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun f ↦ f ≫
        (β_ R (asOver E sections V hVs hVa hVmem)).inv)
        (BraidedCategory.braiding_naturality (𝟙 R)
          (projectionOver E sections V hVs hVa hVmem)).symm
  rw [← hfactor]
  infer_instance

include hfree in
/-- The product of two quotient projections is epi. -/
theorem projectionOver_tensor_projectionOver_epi :
    Epi (projectionOver E sections V hVs hVa hVmem ⊗ₘ
      projectionOver E sections V hVs hVa hVmem) := by
  letI : Epi (E.X ◁ projectionOver E sections V hVs hVa hVmem) :=
    whiskerLeft_projectionOver_epi E sections V hVs hVa hVmem hfree E.X
  letI : Epi (projectionOver E sections V hVs hVa hVmem ▷
      asOver E sections V hVs hVa hVmem) :=
    projectionOver_whiskerRight_epi E sections V hVs hVa hVmem hfree
      (asOver E sections V hVs hVa hVmem)
  have hfactor :
      (E.X ◁ projectionOver E sections V hVs hVa hVmem) ≫
        (projectionOver E sections V hVs hVa hVmem ▷
          asOver E sections V hVs hVa hVmem) =
      projectionOver E sections V hVs hVa hVmem ⊗ₘ
        projectionOver E sections V hVs hVa hVmem :=
    (MonoidalCategory.tensorHom_def'
      (projectionOver E sections V hVs hVa hVmem)
      (projectionOver E sections V hVs hVa hVmem)).symm
  rw [← hfactor]
  infer_instance

/-- A coherence isomorphism bringing the middle tensor factor to the front. -/
noncomputable def middleToFront (L X R : Over S) :
    (L ⊗ X) ⊗ R ≅ X ⊗ (L ⊗ R) :=
  ((β_ L X) ▷ᵢ R) ≪≫ (α_ X L R)

include hfree in
/-- A copy of the quotient projection in an arbitrary middle tensor factor is epi. -/
theorem middle_projectionOver_epi (L R : Over S) :
    Epi ((L ◁ projectionOver E sections V hVs hVa hVmem) ▷ R) := by
  letI : Epi (projectionOver E sections V hVs hVa hVmem ▷ (L ⊗ R)) :=
    projectionOver_whiskerRight_epi E sections V hVs hVa hVmem hfree (L ⊗ R)
  have hnat :
      (middleToFront L E.X R).hom ≫
          (projectionOver E sections V hVs hVa hVmem ▷ (L ⊗ R)) =
        ((L ◁ projectionOver E sections V hVs hVa hVmem) ▷ R) ≫
          (middleToFront L (asOver E sections V hVs hVa hVmem) R).hom := by
    dsimp only [middleToFront, Iso.trans_hom,
      MonoidalCategory.whiskerRightIso_hom]
    simp only [Iso.trans_hom, MonoidalCategory.whiskerRightIso_hom]
    rw [Category.assoc, ← MonoidalCategory.associator_naturality_left
      (projectionOver E sections V hVs hVa hVmem) L R]
    have hbraid := BraidedCategory.braiding_naturality_right L
      (projectionOver E sections V hVs hVa hVmem)
    have hwhisker := congrArg (fun f ↦ f ▷ R) hbraid
    simp only [MonoidalCategory.comp_whiskerRight] at hwhisker
    simpa only [Category.assoc] using congrArg
      (fun f ↦ f ≫
        (α_ (asOver E sections V hVs hVa hVmem) L R).hom) hwhisker.symm
  have hfactor :
      (middleToFront L E.X R).hom ≫
          (projectionOver E sections V hVs hVa hVmem ▷ (L ⊗ R)) ≫
          (middleToFront L (asOver E sections V hVs hVa hVmem) R).inv =
        (L ◁ projectionOver E sections V hVs hVa hVmem) ▷ R := by
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun f ↦ f ≫
        (middleToFront L (asOver E sections V hVs hVa hVmem) R).inv) hnat
  rw [← hfactor]
  infer_instance

include hfree in
/-- A quotient projection with two fixed tensor factors on its right is epi. -/
theorem projectionOver_doubleWhiskerRight_epi (R T : Over S) :
    Epi ((projectionOver E sections V hVs hVa hVmem ▷ R) ▷ T) := by
  letI : Epi (projectionOver E sections V hVs hVa hVmem ▷ (R ⊗ T)) :=
    projectionOver_whiskerRight_epi E sections V hVs hVa hVmem hfree (R ⊗ T)
  have hfactor :
      (α_ E.X R T).hom ≫
          (projectionOver E sections V hVs hVa hVmem ▷ (R ⊗ T)) ≫
      (α_ (asOver E sections V hVs hVa hVmem) R T).inv =
        (projectionOver E sections V hVs hVa hVmem ▷ R) ▷ T := by
    rw [MonoidalCategory.whiskerRight_tensor]
    simp
  rw [← hfactor]
  infer_instance

include hfree in
/-- The threefold product of quotient projections is epi. -/
theorem projectionOver_tensor_three_epi :
    Epi ((projectionOver E sections V hVs hVa hVmem ⊗ₘ
      projectionOver E sections V hVs hVa hVmem) ⊗ₘ
        projectionOver E sections V hVs hVa hVmem) := by
  let q := projectionOver E sections V hVs hVa hVmem
  let Q := asOver E sections V hVs hVa hVmem
  letI : Epi ((E.X ⊗ E.X) ◁ q) :=
    whiskerLeft_projectionOver_epi E sections V hVs hVa hVmem hfree (E.X ⊗ E.X)
  letI : Epi ((E.X ◁ q) ▷ Q) :=
    middle_projectionOver_epi E sections V hVs hVa hVmem hfree E.X Q
  letI : Epi ((q ▷ Q) ▷ Q) :=
    projectionOver_doubleWhiskerRight_epi E sections V hVs hVa hVmem hfree Q Q
  have hfactor :
      ((E.X ⊗ E.X) ◁ q) ≫
        ((E.X ◁ q) ▷ Q) ≫
        ((q ▷ Q) ▷ Q) = (q ⊗ₘ q) ⊗ₘ q := by
    rw [MonoidalCategory.tensorHom_def' (q ⊗ₘ q) q,
      MonoidalCategory.tensorHom_def' q q,
      MonoidalCategory.comp_whiskerRight]
  rw [← hfactor]
  infer_instance

/-! ## The commutative group laws -/

/-- Left unit law for the descended multiplication. -/
theorem oneOver_mulOver :
    (oneOver E sections V hVs hVa hVmem ▷
        asOver E sections V hVs hVa hVmem) ≫
      mulOver E sections V hVs hVa hVmem hfree =
    (λ_ (asOver E sections V hVs hVa hVmem)).hom := by
  let q := projectionOver E sections V hVs hVa hVmem
  let Q := asOver E sections V hVs hVa hVmem
  letI : Epi (𝟙_ (Over S) ◁ q) :=
    whiskerLeft_projectionOver_epi E sections V hVs hVa hVmem hfree (𝟙_ (Over S))
  rw [← cancel_epi (𝟙_ (Over S) ◁ q)]
  rw [MonoidalCategory.leftUnitor_naturality q]
  simpa only [q, Q, oneOver, Category.assoc, tensorHom_comp_tensorHom,
    tensorHom_comp_tensorHom_assoc,
    projectionOver_mul (G := G) E sections V hVs hVa hVmem hfree,
    ← MonoidalCategory.id_tensorHom, ← MonoidalCategory.tensorHom_id,
    Category.id_comp, Category.comp_id] using
    congrArg (fun f ↦ f ≫ projectionOver E sections V hVs hVa hVmem)
      (MonObj.one_mul E.X)

/-- Right unit law for the descended multiplication. -/
theorem mulOver_one :
    (asOver E sections V hVs hVa hVmem ◁
        oneOver E sections V hVs hVa hVmem) ≫
      mulOver E sections V hVs hVa hVmem hfree =
    (ρ_ (asOver E sections V hVs hVa hVmem)).hom := by
  let q := projectionOver E sections V hVs hVa hVmem
  let Q := asOver E sections V hVs hVa hVmem
  letI : Epi (q ▷ 𝟙_ (Over S)) :=
    projectionOver_whiskerRight_epi E sections V hVs hVa hVmem hfree (𝟙_ (Over S))
  rw [← cancel_epi (q ▷ 𝟙_ (Over S))]
  rw [MonoidalCategory.rightUnitor_naturality q]
  simpa only [q, Q, oneOver, Category.assoc, tensorHom_comp_tensorHom,
    tensorHom_comp_tensorHom_assoc,
    projectionOver_mul (G := G) E sections V hVs hVa hVmem hfree,
    ← MonoidalCategory.id_tensorHom, ← MonoidalCategory.tensorHom_id,
    Category.id_comp, Category.comp_id] using
    congrArg (fun f ↦ f ≫ projectionOver E sections V hVs hVa hVmem)
      (MonObj.mul_one E.X)

/-- Associativity of the descended multiplication. -/
theorem mulOver_assoc :
    (mulOver E sections V hVs hVa hVmem hfree ▷
        asOver E sections V hVs hVa hVmem) ≫
      mulOver E sections V hVs hVa hVmem hfree =
    (α_ (asOver E sections V hVs hVa hVmem)
        (asOver E sections V hVs hVa hVmem)
        (asOver E sections V hVs hVa hVmem)).hom ≫
      (asOver E sections V hVs hVa hVmem ◁
        mulOver E sections V hVs hVa hVmem hfree) ≫
      mulOver E sections V hVs hVa hVmem hfree := by
  let q := projectionOver E sections V hVs hVa hVmem
  let Q := asOver E sections V hVs hVa hVmem
  letI : Epi ((q ⊗ₘ q) ⊗ₘ q) :=
    projectionOver_tensor_three_epi E sections V hVs hVa hVmem hfree
  rw [← cancel_epi ((q ⊗ₘ q) ⊗ₘ q)]
  simpa only [q, Q, Category.assoc, tensorHom_comp_tensorHom,
    tensorHom_comp_tensorHom_assoc,
    projectionOver_mul (G := G) E sections V hVs hVa hVmem hfree,
    ← MonoidalCategory.id_tensorHom, ← MonoidalCategory.tensorHom_id,
    Category.id_comp, Category.comp_id, associator_naturality,
    associator_naturality_assoc] using
    congrArg (fun f ↦ f ≫ projectionOver E sections V hVs hVa hVmem)
      (MonObj.mul_assoc E.X)

/-- Commutativity of the descended multiplication. -/
theorem mulOver_comm :
    (β_ (asOver E sections V hVs hVa hVmem)
      (asOver E sections V hVs hVa hVmem)).hom ≫
        mulOver E sections V hVs hVa hVmem hfree =
      mulOver E sections V hVs hVa hVmem hfree := by
  let q := projectionOver E sections V hVs hVa hVmem
  letI : Epi (q ⊗ₘ q) :=
    projectionOver_tensor_projectionOver_epi E sections V hVs hVa hVmem hfree
  rw [← cancel_epi (q ⊗ₘ q)]
  simpa only [q, Category.assoc,
    projectionOver_mul (G := G) E sections V hVs hVa hVmem hfree,
    BraidedCategory.braiding_naturality,
    BraidedCategory.braiding_naturality_assoc] using
    congrArg (fun f ↦ f ≫ projectionOver E sections V hVs hVa hVmem)
      (IsCommMonObj.mul_comm E.X)

/-- Left inverse law for the descended inverse. -/
theorem invOver_mulOver_left :
    lift (invOver E sections V hVs hVa hVmem hfree)
        (𝟙 (asOver E sections V hVs hVa hVmem)) ≫
      mulOver E sections V hVs hVa hVmem hfree =
    toUnit (asOver E sections V hVs hVa hVmem) ≫
      oneOver E sections V hVs hVa hVmem := by
  let q := projectionOver E sections V hVs hVa hVmem
  letI : Epi q := projectionOver_epi E sections V hVs hVa hVmem hfree
  rw [← cancel_epi q]
  simpa only [q, oneOver, Category.assoc, comp_lift_assoc, Category.comp_id,
    Category.id_comp,
    projectionOver_comp_invOver,
    projectionOver_mul (G := G) E sections V hVs hVa hVmem hfree,
    lift_map_assoc, comp_toUnit_assoc] using
    congrArg (fun f ↦ f ≫ projectionOver E sections V hVs hVa hVmem)
      (GrpObj.left_inv E.X)

/-- Right inverse law for the descended inverse. -/
theorem invOver_mulOver_right :
    lift (𝟙 (asOver E sections V hVs hVa hVmem))
        (invOver E sections V hVs hVa hVmem hfree) ≫
      mulOver E sections V hVs hVa hVmem hfree =
    toUnit (asOver E sections V hVs hVa hVmem) ≫
      oneOver E sections V hVs hVa hVmem := by
  let q := projectionOver E sections V hVs hVa hVmem
  letI : Epi q := projectionOver_epi E sections V hVs hVa hVmem hfree
  rw [← cancel_epi q]
  simpa only [q, oneOver, Category.assoc, comp_lift_assoc, Category.comp_id,
    Category.id_comp,
    projectionOver_comp_invOver,
    projectionOver_mul (G := G) E sections V hVs hVa hVmem hfree,
    lift_map_assoc, comp_toUnit_assoc] using
    congrArg (fun f ↦ f ≫ projectionOver E sections V hVs hVa hVmem)
      (GrpObj.right_inv E.X)

/-! ## Packaging and the quotient torsor -/

include hfree in
/-- The group-object structure obtained by descending the operations of `E`.

This is deliberately a definition rather than a global instance: the descended multiplication
depends on the proof that the translation action is free, while the underlying quotient object
does not record that proof in its type. -/
@[instance_reducible]
noncomputable def quotientGrpObj :
    GrpObj (asOver E sections V hVs hVa hVmem) where
  one := oneOver E sections V hVs hVa hVmem
  mul := mulOver E sections V hVs hVa hVmem hfree
  one_mul := oneOver_mulOver E sections V hVs hVa hVmem hfree
  mul_one := mulOver_one E sections V hVs hVa hVmem hfree
  mul_assoc := mulOver_assoc E sections V hVs hVa hVmem hfree
  inv := invOver E sections V hVs hVa hVmem hfree
  left_inv := invOver_mulOver_left E sections V hVs hVa hVmem hfree
  right_inv := invOver_mulOver_right E sections V hVs hVa hVmem hfree

include hfree in
/-- The actual quotient scheme equipped with its descended commutative group structure. -/
noncomputable def commGroupScheme : CommGroupScheme S := by
  letI : GrpObj (asOver E sections V hVs hVa hVmem) :=
    quotientGrpObj E sections V hVs hVa hVmem hfree
  letI : IsCommMonObj (asOver E sections V hVs hVa hVmem) :=
    { mul_comm := mulOver_comm E sections V hVs hVa hVmem hfree }
  exact { X := asOver E sections V hVs hVa hVmem }

@[simp]
theorem commGroupScheme_X :
    (commGroupScheme E sections V hVs hVa hVmem hfree).X =
      asOver E sections V hVs hVa hVmem :=
  rfl

/-- The quotient projection, bundled as a homomorphism of commutative group schemes. -/
noncomputable def projectionHom :
    E ⟶ commGroupScheme E sections V hVs hVa hVmem hfree := by
  apply InducedCategory.homMk
  refine Grp.homMk'' (projectionOver E sections V hVs hVa hVmem)
    (one_f := ?_) (mul_f := ?_)
  · rfl
  · exact projectionOver_mul E sections V hVs hVa hVmem hfree

@[simp]
theorem projectionHom_over :
    (projectionHom E sections V hVs hVa hVmem hfree).hom.hom.hom =
      projectionOver E sections V hVs hVa hVmem :=
  rfl

@[simp]
theorem projectionHom_underlying :
    (projectionHom E sections V hVs hVa hVmem hfree).hom.hom.hom.left =
      projection E sections V hVs hVa hVmem :=
  rfl

include hfree in
/-- The actual quotient projection is the torsor attached to the translation action. -/
theorem projection_torsorCompare_isIso :
    IsIso (ModularCurves.torsorCompare
      (projection E sections V hVs hVa hVmem)
      (translationAction E sections)
      (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g)) :=
  (translationAction E sections).isIso_torsorCompare_quotientπ
    V hVs hVa hVmem hfree

include hfree in
/-- Every base change of the actual quotient projection is the torsor for the pulled-back
translation action. -/
theorem projection_baseChange_torsorCompare_isIso {W : Scheme.{u}}
    (j : W ⟶ scheme E sections V hVs hVa) :
    IsIso (ModularCurves.torsorCompare
      (pullback.snd (projection E sections V hVs hVa hVmem) j)
      (ModularCurves.pullbackTorsorAction (translationAction E sections)
        (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g) j)
      (ModularCurves.pullbackTorsorAction_over (translationAction E sections)
        (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g) j)) :=
  ModularCurves.isIso_torsorCompare_pullback
    (translationAction E sections)
    (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g)
    (projection_torsorCompare_isIso E sections V hVs hVa hVmem hfree) j

end Quotient

end FiniteTranslationQuotient
end AlgebraicGeometry

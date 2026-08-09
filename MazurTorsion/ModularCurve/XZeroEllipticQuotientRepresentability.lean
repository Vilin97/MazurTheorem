/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/

import MazurTorsion.AlgebraicGeometry.FiniteEtaleRelativeDimensionDescent
import MazurTorsion.ModularCurve.XZeroEllipticQuotientGeometry
import MazurTorsion.ModularCurve.XZeroEllipticQuotientAtlas
import MazurTorsion.ModularCurve.XZeroEllipticQuotientTranslation
import MazurTorsion.ModularCurve.XZeroGeometricCyclicQuotient
import MazurTorsion.ModularCurve.XZeroWeierstrassRelativeDimension

/-!
# Representability of split rational cyclic quotients

For a concrete projective Weierstrass cubic over `ℚ`, a chosen comparison from coordinate
points to represented rational points transports the finite subgroup underlying a
`RationalDatum` to sections that act by translation.  The stable affine atlas constructed in
`XZeroEllipticQuotientAtlas` therefore feeds AINTLIB's finite-action quotient construction.  The
result is an actual quotient scheme, and the descent in
`FiniteTranslationQuotientGroup` equips it with a commutative group law for which the projection
is a finite étale homomorphism.

The main point of this file is the exact geometric kernel.  Pulling the quotient torsor back
along its unit section gives the zero fibre.  The pulled-back torsor has the source unit as a
section, so AINTLIB's `isIso_sigmaDesc_section` trivializes that fibre as a coproduct of copies of
the base.  The checked coproduct presentation of the constant finite group scheme identifies
this trivialization with the original closed subgroup inclusion, component by component.  Thus
the constant subgroup is isomorphic to the canonical group-scheme kernel, rather than merely
having the same rational points.

The resulting `FppfQuotientPresentation` is constructed here, not taken as an input.  Its
existing `baseChange` operation consequently gives compatibility with every morphism of base
schemes.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj
open AlgebraicGeometry
open scoped CategoryTheory.MonObj

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

namespace AlgebraicGeometry.FiniteTranslationQuotient

universe u

section ExactKernel

variable {K : Type u} [Field K]
  {G : Type u} [CommGroup G] [Fintype G]
  (E : CommGroupScheme (Spec (.of K)))
  (sections : G →* (𝟙_ (Over (Spec (.of K))) ⟶ E.X))
  [IsAffineHom (pullback.diagonal (terminal.from E.X.left))]
  (V : E.X.left → E.X.left.Opens)
  (hVs : ∀ x, (translationAction E sections).IsStableOpen (V x))
  (hVa : ∀ x, IsAffineOpen (V x))
  (hVmem : ∀ x, x ∈ V x)
  (hfree : ∀ g : G, g ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ E.X.left),
    t ≫ (translationAction E sections).hom g = t → IsEmpty T)
  (inclusion : (FiniteFlatCommGroupScheme.constantScheme K G).obj ⟶ E)
  (hsections : ∀ g : G,
    FiniteFlatCommGroupScheme.constantGeometricPointMap K G g ≫
        CommGroupScheme.underlyingHom inclusion =
      (sections g).left)

private abbrev Q : CommGroupScheme (Spec (.of K)) :=
  commGroupScheme E sections V hVs hVa hVmem hfree

private abbrev q : E ⟶ Q E sections V hVs hVa hVmem hfree :=
  projectionHom E sections V hVs hVa hVmem hfree

private theorem selfTestObject_hom_eq_id :
    (AffineCommGroupScheme.testObject (R := K) K).hom =
      𝟙 (Spec (.of K)) := by
  change Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 _
  rw [Spec.map_eq_id]
  ext x
  rfl

/-- The concrete spectrum used in the constant-scheme coproduct is the underlying scheme of
the monoidal unit in the slice.  Naming this definitional comparison keeps type-class search
from depending on reducibility. -/
private noncomputable def baseSchemeIso :
    Spec (.of K) ≅ (𝟙_ (Over (Spec (.of K)))).left := by
  change Spec (.of K) ≅ Spec (.of K)
  exact Iso.refl _

@[simp]
private theorem baseSchemeIso_hom :
    (baseSchemeIso (K := K)).hom = 𝟙 (Spec (.of K)) :=
  rfl

/-- The quotient unit with its codomain exposed as the literal finite-action quotient scheme. -/
private noncomputable def quotientUnit :
    (𝟙_ (Over (Spec (.of K)))).left ⟶ scheme E sections V hVs hVa :=
  (oneOver E sections V hVs hVa hVmem).left

/- The equation used to lift the chosen subgroup into the canonical internal-group kernel. -/
include hsections in
private theorem inclusion_zero_grp :
    inclusion.hom ≫ (q E sections V hVs hVa hVmem hfree).hom =
      (default :
          (FiniteFlatCommGroupScheme.constantScheme K G).obj.toGrp ⟶
            Grp.trivial (Over (Spec (.of K)))) ≫
        CommGroupScheme.kernelZero (Q E sections V hVs hVa hVmem hfree) := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply FiniteFlatCommGroupScheme.constantScheme_hom_ext K G
  intro g
  change FiniteFlatCommGroupScheme.constantGeometricPointMap K G g ≫
      CommGroupScheme.underlyingHom inclusion ≫
        projection E sections V hVs hVa hVmem =
    FiniteFlatCommGroupScheme.constantGeometricPointMap K G g ≫
      (FiniteFlatCommGroupScheme.constantScheme K G).obj.X.hom ≫
        (oneOver E sections V hVs hVa hVmem).left
  rw [← Category.assoc, hsections]
  have hx := congrArg Over.Hom.left (one_comp_translateBy E (sections g))
  change η[E.X].left ≫ (translateBy E (sections g)).left = (sections g).left at hx
  have hinvariant := congrArg Over.Hom.left
    (translateBy_comp_projectionOver E sections V hVs hVa hVmem g)
  change (translateBy E (sections g)).left ≫
      projection E sections V hVs hVa hVmem =
    projection E sections V hVs hVa hVmem at hinvariant
  have hone := congrArg Over.Hom.left
    (IsMonHom.one_hom (q E sections V hVs hVa hVmem hfree).hom.hom.hom)
  change η[E.X].left ≫ projection E sections V hVs hVa hVmem =
    (oneOver E sections V hVs hVa hVmem).left at hone
  rw [← hx, Category.assoc, hinvariant, hone]
  have hw := (FiniteFlatCommGroupScheme.constantGeometricPoint K G g).w
  change FiniteFlatCommGroupScheme.constantGeometricPointMap K G g ≫
      (FiniteFlatCommGroupScheme.constantScheme K G).obj.X.hom =
    (AffineCommGroupScheme.testObject (R := K) K).hom at hw
  rw [← Category.assoc, hw, selfTestObject_hom_eq_id, Category.id_comp]

include hsections in
/-- The original constant subgroup maps to the canonical kernel of the constructed quotient
projection. -/
noncomputable def toKernel :
    (FiniteFlatCommGroupScheme.constantScheme K G).obj ⟶
      CommGroupScheme.kernel (q E sections V hVs hVa hVmem hfree) := by
  apply InducedCategory.homMk
  exact pullback.lift inclusion.hom default
    (inclusion_zero_grp E sections V hVs hVa hVmem hfree inclusion hsections)

@[reassoc]
theorem toKernel_comp_kernelInclusion :
    toKernel E sections V hVs hVa hVmem hfree inclusion hsections ≫
        CommGroupScheme.kernelInclusion (q E sections V hVs hVa hVmem hfree) =
      inclusion := by
  apply CommGrp.hom_ext
  have hlift := pullback.lift_fst inclusion.hom default
    (inclusion_zero_grp E sections V hVs hVa hVmem hfree inclusion hsections)
  exact congrArg (fun f ↦ f.hom.hom) hlift

/-- The source unit gives a section of the fibre of the quotient projection over the quotient
unit. -/
noncomputable def kernelFiberSection :
    (𝟙_ (Over (Spec (.of K)))).left ⟶
      CommGroupScheme.kernelScheme (q E sections V hVs hVa hVmem hfree) :=
  pullback.lift η[E.X].left (𝟙 _) (by
    change η[E.X].left ≫ projection E sections V hVs hVa hVmem =
      𝟙 _ ≫ (oneOver E sections V hVs hVa hVmem).left
    have hone := IsMonHom.one_hom
      (q E sections V hVs hVa hVmem hfree).hom.hom.hom
    have hone_left := congrArg Over.Hom.left hone
    change η[E.X].left ≫ projection E sections V hVs hVa hVmem =
      (oneOver E sections V hVs hVa hVmem).left at hone_left
    simpa only [Category.id_comp] using hone_left)

@[reassoc (attr := simp)]
theorem kernelFiberSection_isSection :
    kernelFiberSection E sections V hVs hVa hVmem hfree ≫
        CommGroupScheme.kernelStructureMap
          (q E sections V hVs hVa hVmem hfree) =
      𝟙 ((𝟙_ (Over (Spec (.of K)))).left) :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
private theorem kernelFiberSection_comp_kernelι :
    kernelFiberSection E sections V hVs hVa hVmem hfree ≫
        CommGroupScheme.kernelι (q E sections V hVs hVa hVmem hfree) =
      η[E.X].left :=
  pullback.lift_fst _ _ _

/-- The pulled-back translation action, with its carrier exposed as the canonical group-scheme
kernel. -/
private noncomputable def kernelFiberAction :
    SchemeAction G
      (CommGroupScheme.kernelScheme (q E sections V hVs hVa hVmem hfree)) := by
  change SchemeAction G
    (pullback (projection E sections V hVs hVa hVmem)
      (quotientUnit E sections V hVs hVa hVmem))
  exact ModularCurves.pullbackTorsorAction
    (translationAction E sections)
    (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g)
    (quotientUnit E sections V hVs hVa hVmem)

@[reassoc]
private theorem kernelFiberAction_hom_fst (g : G) :
    (kernelFiberAction E sections V hVs hVa hVmem hfree).hom g ≫
        CommGroupScheme.kernelι (q E sections V hVs hVa hVmem hfree) =
      CommGroupScheme.kernelι (q E sections V hVs hVa hVmem hfree) ≫
        (translationAction E sections).hom g := by
  change (ModularCurves.pullbackTorsorAction
      (translationAction E sections)
      (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g)
      (quotientUnit E sections V hVs hVa hVmem)).hom g ≫
        pullback.fst (projection E sections V hVs hVa hVmem)
          (quotientUnit E sections V hVs hVa hVmem) =
    pullback.fst (projection E sections V hVs hVa hVmem)
        (quotientUnit E sections V hVs hVa hVmem) ≫
      (translationAction E sections).hom g
  simp only [ModularCurves.pullbackTorsorAction_hom, pullback.map,
    pullback.lift_fst]

@[reassoc]
private theorem kernelFiberAction_hom_snd (g : G) :
    (kernelFiberAction E sections V hVs hVa hVmem hfree).hom g ≫
        CommGroupScheme.kernelStructureMap
          (q E sections V hVs hVa hVmem hfree) =
      CommGroupScheme.kernelStructureMap
        (q E sections V hVs hVa hVmem hfree) := by
  change (ModularCurves.pullbackTorsorAction
      (translationAction E sections)
      (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g)
      (quotientUnit E sections V hVs hVa hVmem)).hom g ≫
        pullback.snd (projection E sections V hVs hVa hVmem)
          (quotientUnit E sections V hVs hVa hVmem) =
    pullback.snd (projection E sections V hVs hVa hVmem)
      (quotientUnit E sections V hVs hVa hVmem)
  exact ModularCurves.pullbackTorsorAction_over
    (translationAction E sections)
    (fun g ↦ (translationAction E sections).hom_quotientπ V hVs hVa hVmem g)
    (quotientUnit E sections V hVs hVa hVmem) g

/-- The zero fibre is trivialized by translating the source unit by every member of `G`. -/
noncomputable def kernelFiberTrivialization :
    (FiniteFlatCommGroupScheme.constantScheme K G).scheme ⟶
      CommGroupScheme.kernelScheme (q E sections V hVs hVa hVmem hfree) :=
  (FiniteFlatCommGroupScheme.constantSchemeSigmaIso K G).hom ≫
    (Sigma.mapIso (fun _ : G ↦ baseSchemeIso (K := K))).hom ≫
      Sigma.desc (fun g : G ↦
        kernelFiberSection E sections V hVs hVa hVmem hfree ≫
          (kernelFiberAction E sections V hVs hVa hVmem hfree).hom g)

@[reassoc]
private theorem constantGeometricPoint_comp_kernelFiberTrivialization (g : G) :
    FiniteFlatCommGroupScheme.constantGeometricPointMap K G g ≫
        kernelFiberTrivialization E sections V hVs hVa hVmem hfree =
      (baseSchemeIso (K := K)).hom ≫
        kernelFiberSection E sections V hVs hVa hVmem hfree ≫
          (kernelFiberAction E sections V hVs hVa hVmem hfree).hom g := by
  rw [kernelFiberTrivialization, ← Category.assoc,
    FiniteFlatCommGroupScheme.constantGeometricPoint_sigma,
    ← Category.assoc, Sigma.ι_mapIso_hom, Category.assoc, Sigma.ι_desc]

/-- A torsor with the source unit as section has zero fibre equal to the constant group scheme.
This is a scheme isomorphism statement, not a point-counting argument. -/
instance kernelFiberTrivialization_isIso :
    IsIso (kernelFiberTrivialization E sections V hVs hVa hVmem hfree) := by
  let σP := kernelFiberAction E sections V hVs hVa hVmem hfree
  let hPover := kernelFiberAction_hom_snd E sections V hVs hVa hVmem hfree
  have hPtors : IsIso (ModularCurves.torsorCompare
      (CommGroupScheme.kernelStructureMap
        (q E sections V hVs hVa hVmem hfree)) σP hPover) := by
    exact projection_baseChange_torsorCompare_isIso
      E sections V hVs hVa hVmem hfree
      (quotientUnit E sections V hVs hVa hVmem)
  haveI : IsIso (Sigma.desc (fun g : G ↦
      kernelFiberSection E sections V hVs hVa hVmem hfree ≫ σP.hom g)) :=
    ModularCurves.isIso_sigmaDesc_section σP hPover hPtors
      (kernelFiberSection E sections V hVs hVa hVmem hfree)
      (kernelFiberSection_isSection E sections V hVs hVa hVmem hfree)
  unfold kernelFiberTrivialization
  change IsIso
    ((FiniteFlatCommGroupScheme.constantSchemeSigmaIso K G).hom ≫
      (Sigma.mapIso (fun _ : G ↦ baseSchemeIso (K := K))).hom ≫
        Sigma.desc (fun g : G ↦
          kernelFiberSection E sections V hVs hVa hVmem hfree ≫ σP.hom g))
  infer_instance

/-- The internal-group kernel lift is the torsor trivialization after passing through the
canonical comparison between the internal and scheme pullbacks. -/
@[reassoc]
theorem toKernel_underlying_comp_kernelSchemeIso :
    CommGroupScheme.underlyingHom
        (toKernel E sections V hVs hVa hVmem hfree inclusion hsections) ≫
      (CommGroupScheme.kernelSchemeIso
        (q E sections V hVs hVa hVmem hfree)).hom =
      kernelFiberTrivialization E sections V hVs hVa hVmem hfree := by
  apply FiniteFlatCommGroupScheme.constantScheme_hom_ext K G
  intro g
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc,
      CommGroupScheme.kernelSchemeIso_hom_kernelι]
    have hinc := congrArg (fun f ↦ CommGroupScheme.underlyingHom f)
      (toKernel_comp_kernelInclusion E sections V hVs hVa hVmem hfree
        inclusion hsections)
    change CommGroupScheme.underlyingHom
        (toKernel E sections V hVs hVa hVmem hfree inclusion hsections) ≫
      CommGroupScheme.underlyingHom
        (CommGroupScheme.kernelInclusion (q E sections V hVs hVa hVmem hfree)) =
      CommGroupScheme.underlyingHom inclusion at hinc
    rw [Category.assoc, hinc, hsections]
    rw [constantGeometricPoint_comp_kernelFiberTrivialization_assoc,
      baseSchemeIso_hom, Category.id_comp, kernelFiberAction_hom_fst,
      kernelFiberSection_comp_kernelι_assoc]
    exact (congrArg Over.Hom.left (one_comp_translateBy E (sections g))).symm
  · rw [Category.assoc, Category.assoc,
      CommGroupScheme.kernelSchemeIso_hom_structureMap]
    rw [Category.assoc,
      (toKernel E sections V hVs hVa hVmem hfree inclusion hsections).hom.hom.hom.w]
    rw [constantGeometricPoint_comp_kernelFiberTrivialization_assoc,
      baseSchemeIso_hom, Category.id_comp, kernelFiberAction_hom_snd,
      kernelFiberSection_isSection]
    exact (FiniteFlatCommGroupScheme.constantGeometricPoint K G g).w.trans
      (selfTestObject_hom_eq_id (K := K))

/-- The geometric comparison from the supplied constant subgroup to the canonical quotient
kernel is an isomorphism. -/
instance toKernel_isIso :
    IsIso (toKernel E sections V hVs hVa hVmem hfree inclusion hsections) := by
  have hunderlying :
      CommGroupScheme.underlyingHom
          (toKernel E sections V hVs hVa hVmem hfree inclusion hsections) =
        kernelFiberTrivialization E sections V hVs hVa hVmem hfree ≫
          (CommGroupScheme.kernelSchemeIso
            (q E sections V hVs hVa hVmem hfree)).inv := by
    apply (cancel_mono (CommGroupScheme.kernelSchemeIso
      (q E sections V hVs hVa hVmem hfree)).hom).1
    rw [Category.assoc, (CommGroupScheme.kernelSchemeIso
      (q E sections V hVs hVa hVmem hfree)).inv_hom_id,
      Category.comp_id,
      toKernel_underlying_comp_kernelSchemeIso]
  haveI : IsIso (CommGroupScheme.underlyingHom
      (toKernel E sections V hVs hVa hVmem hfree inclusion hsections)) := by
    rw [hunderlying]
    infer_instance
  haveI : IsIso ((Over.forget (Spec (.of K))).map
      (toKernel E sections V hVs hVa hVmem hfree inclusion hsections).hom.hom.hom) := by
    change IsIso (CommGroupScheme.underlyingHom
      (toKernel E sections V hVs hVa hVmem hfree inclusion hsections))
    infer_instance
  haveI : IsIso
      (toKernel E sections V hVs hVa hVmem hfree inclusion hsections).hom.hom.hom :=
    isIso_of_reflects_iso _ (Over.forget (Spec (.of K)))
  haveI : IsIso ((Mon.forget (Over (Spec (.of K)))).map
      (toKernel E sections V hVs hVa hVmem hfree inclusion hsections).hom.hom) := by
    change IsIso
      (toKernel E sections V hVs hVa hVmem hfree inclusion hsections).hom.hom.hom
    infer_instance
  haveI : IsIso
      (toKernel E sections V hVs hVa hVmem hfree inclusion hsections).hom.hom :=
    isIso_of_reflects_iso _ (Mon.forget (Over (Spec (.of K))))
  haveI : IsIso ((Grp.forget₂Mon (Over (Spec (.of K)))).map
      (toKernel E sections V hVs hVa hVmem hfree inclusion hsections).hom) := by
    change IsIso
      (toKernel E sections V hVs hVa hVmem hfree inclusion hsections).hom.hom
    infer_instance
  haveI : IsIso
      (toKernel E sections V hVs hVa hVmem hfree inclusion hsections).hom :=
    isIso_of_reflects_iso _ (Grp.forget₂Mon (Over (Spec (.of K))))
  haveI : IsIso ((CommGrp.forget₂Grp (Over (Spec (.of K)))).map
      (toKernel E sections V hVs hVa hVmem hfree inclusion hsections)) := by
    change IsIso
      (toKernel E sections V hVs hVa hVmem hfree inclusion hsections).hom
    infer_instance
  exact isIso_of_reflects_iso _ (CommGrp.forget₂Grp (Over (Spec (.of K))))

include inclusion hsections in
/-- Exact identification of the original subgroup with the geometric kernel of the actual
finite-action quotient projection. -/
noncomputable def kernelIso :
    (FiniteFlatCommGroupScheme.constantScheme K G).obj ≅
      CommGroupScheme.kernel (q E sections V hVs hVa hVmem hfree) :=
  asIso (toKernel E sections V hVs hVa hVmem hfree inclusion hsections)

@[reassoc]
theorem kernelIso_hom_kernelInclusion :
    (kernelIso E sections V hVs hVa hVmem hfree inclusion hsections).hom ≫
        CommGroupScheme.kernelInclusion (q E sections V hVs hVa hVmem hfree) =
      inclusion :=
  toKernel_comp_kernelInclusion E sections V hVs hVa hVmem hfree inclusion hsections

include hsections in
/-- The quotient constructed from the finite translation action, with its exact geometric
kernel. -/
noncomputable def fppfQuotientPresentation :
    CommGroupScheme.FppfQuotientPresentation inclusion where
  quotient := Q E sections V hVs hVa hVmem hfree
  project := q E sections V hVs hVa hVmem hfree
  project_flat := by
    change Flat (projection E sections V hVs hVa hVmem)
    letI : Etale (projection E sections V hVs hVa hVmem) :=
      projection_etale E sections V hVs hVa hVmem hfree
    infer_instance
  project_surjective := by
    change Surjective (projection E sections V hVs hVa hVmem)
    exact projection_surjective E sections V hVs hVa hVmem
  project_lfp := by
    change LocallyOfFinitePresentation (projection E sections V hVs hVa hVmem)
    letI : Etale (projection E sections V hVs hVa hVmem) :=
      projection_etale E sections V hVs hVa hVmem hfree
    infer_instance
  kernelIso := kernelIso E sections V hVs hVa hVmem hfree inclusion hsections
  kernelIso_hom_kernelInclusion :=
    kernelIso_hom_kernelInclusion E sections V hVs hVa hVmem hfree inclusion hsections

/-- Arbitrary base change of the constructed quotient presentation.  In particular, the
base-changed projection has the literal pullback of `inclusion` as its chosen exact kernel. -/
noncomputable def fppfQuotientPresentationBaseChange {T : Scheme.{u}}
    (t : T ⟶ Spec (.of K)) :=
  (fppfQuotientPresentation E sections V hVs hVa hVmem hfree
    inclusion hsections).baseChange t

@[simp]
theorem fppfQuotientPresentationBaseChange_quotient {T : Scheme.{u}}
    (t : T ⟶ Spec (.of K)) :
    (fppfQuotientPresentationBaseChange E sections V hVs hVa hVmem hfree
      inclusion hsections t).quotient =
      (Over.pullback t).mapCommGrp.obj
        (commGroupScheme E sections V hVs hVa hVmem hfree) :=
  rfl

@[simp]
theorem fppfQuotientPresentationBaseChange_project {T : Scheme.{u}}
    (t : T ⟶ Spec (.of K)) :
    (fppfQuotientPresentationBaseChange E sections V hVs hVa hVmem hfree
      inclusion hsections t).project =
      (Over.pullback t).mapCommGrp.map
        (projectionHom E sections V hVs hVa hVmem hfree) :=
  rfl

/-- Finiteness of the constructed quotient projection survives every base change. -/
theorem fppfQuotientPresentationBaseChange_project_isFinite {T : Scheme.{u}}
    (t : T ⟶ Spec (.of K)) :
    IsFinite (CommGroupScheme.underlyingHom
      (fppfQuotientPresentationBaseChange E sections V hVs hVa hVmem hfree
        inclusion hsections t).project) := by
  exact MorphismProperty.overPullbackMap t
    (projectionHom E sections V hVs hVa hVmem hfree).hom.hom.hom
    (projection_isFinite E sections V hVs hVa hVmem hfree)

/-- Étaleness of the constructed quotient projection survives every base change. -/
theorem fppfQuotientPresentationBaseChange_project_etale {T : Scheme.{u}}
    (t : T ⟶ Spec (.of K)) :
    Etale (CommGroupScheme.underlyingHom
      (fppfQuotientPresentationBaseChange E sections V hVs hVa hVmem hfree
        inclusion hsections t).project) := by
  exact MorphismProperty.overPullbackMap t
    (projectionHom E sections V hVs hVa hVmem hfree).hom.hom.hom
    (projection_etale E sections V hVs hVa hVmem hfree)

/-- After arbitrary base change, the pulled-back subgroup is still exactly the geometric kernel
of the pulled-back projection. -/
theorem fppfQuotientPresentationBaseChange_kernel_exact {T : Scheme.{u}}
    (t : T ⟶ Spec (.of K)) :
    (fppfQuotientPresentationBaseChange E sections V hVs hVa hVmem hfree
        inclusion hsections t).kernelIso.hom ≫
      CommGroupScheme.kernelInclusion
        (fppfQuotientPresentationBaseChange E sections V hVs hVa hVmem hfree
          inclusion hsections t).project =
      (Over.pullback t).mapCommGrp.map inclusion :=
  (fppfQuotientPresentationBaseChange E sections V hVs hVa hVmem hfree
    inclusion hsections t).kernelIso_hom_kernelInclusion

end ExactKernel

end AlgebraicGeometry.FiniteTranslationQuotient

namespace MazurTorsion.ModularCurve.XZeroFiniteFlatModuli
namespace WeierstrassGroupSchemeInterface
namespace EllipticQuotientRepresentability

open XZeroModuli
open WeierstrassProjectiveCubic

variable {N : ℕ} [NeZero N]

noncomputable local instance rationalDatumSubgroupFintype
    (x : RationalDatum ℚ N) : Fintype x.subgroup.carrier :=
  Fintype.ofFinite x.subgroup.carrier

noncomputable local instance rationalDatumGeometricallyIntegral
    (x : RationalDatum ℚ N) : GeometricallyIntegral (toOver x.curve).hom := by
  change GeometricallyIntegral (WeierstrassProjectiveCubic.structureMap x.curve)
  exact WeierstrassProjectiveCubic.structureMap_geometricallyIntegral x.curve

/-- The checked concrete-cubic group-scheme interface used in the quotient construction. -/
noncomputable def concreteGroupSchemeInterface
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve)) :
    WeierstrassGroupSchemeInterface x.curve :=
  (toAbelianVarietyComparison x.curve e).toGroupSchemeInterface

private abbrev E
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)] :=
  CommGrp.mk (toAbelianVariety x.curve).toOver

/-- The distinguished rational cyclic sections on the concrete cubic, transported through the
chosen coordinate-to-represented-point comparison. -/
noncomputable def subgroupSections
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve)) :
    Multiplicative x.subgroup.carrier →*
      (𝟙_ (Over (Spec (.of ℚ))) ⟶ (E x).X) :=
  EllipticQuotient.rationalCyclicSubgroupSectionHom
    (concreteGroupSchemeInterface x e) x.subgroup

/-- The translation action whose quotient is constructed below. -/
noncomputable abbrev subgroupAction
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve)) :=
  FiniteTranslationQuotient.translationAction (E x) (subgroupSections x e)

noncomputable instance concreteScheme_isSeparated
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)] :
    (E x).X.left.IsSeparated :=
  WeierstrassProjectiveCubic.scheme_isSeparated x.curve

noncomputable instance concreteScheme_diagonal_isAffine
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)] :
    IsAffineHom (pullback.diagonal (terminal.from (E x).X.left)) := by
  infer_instance

/-- The concrete point-indexed stable affine atlas for the translation action. -/
noncomputable def quotientAtlas
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve)) :
    (E x).X.left → (E x).X.left.Opens :=
  WeierstrassProjectiveCubic.stableAffineAtlas x.curve (subgroupAction x e)

theorem quotientAtlas_isStable
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve))
    (p : (E x).X.left) :
    (subgroupAction x e).IsStableOpen (quotientAtlas x e p) :=
  WeierstrassProjectiveCubic.stableAffineAtlas_isStable
    x.curve (subgroupAction x e) p

theorem quotientAtlas_isAffine
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve))
    (p : (E x).X.left) :
    IsAffineOpen (quotientAtlas x e p) :=
  WeierstrassProjectiveCubic.stableAffineAtlas_isAffine
    x.curve (subgroupAction x e) p

theorem mem_quotientAtlas
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve))
    (p : (E x).X.left) :
    p ∈ quotientAtlas x e p :=
  WeierstrassProjectiveCubic.mem_stableAffineAtlas
    x.curve (subgroupAction x e) p

/-- The transported rational cyclic translation action is free after every scheme-valued
extension. -/
theorem subgroupAction_free
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve)) :
    ∀ g : Multiplicative x.subgroup.carrier, g ≠ 1 →
      ∀ (T : Scheme) (t : T ⟶ (E x).X.left),
        t ≫ (subgroupAction x e).hom g = t → IsEmpty T := by
  change ∀ g : Multiplicative x.subgroup.carrier, g ≠ 1 →
    ∀ (T : Scheme)
      (t : T ⟶ (concreteGroupSchemeInterface x e).groupScheme.X.left),
      t ≫ (EllipticQuotient.rationalCyclicSubgroupAction
        (concreteGroupSchemeInterface x e) x.subgroup).hom g = t → IsEmpty T
  exact EllipticQuotient.rationalCyclicSubgroupAction_free
    (concreteGroupSchemeInterface x e) x.subgroup

/-- Each distinguished constant point followed by the actual finite-flat subgroup immersion is
the section used in the translation action. -/
theorem constantPoint_comp_subgroupInclusion
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve))
    (g : Multiplicative x.subgroup.carrier) :
    FiniteFlatCommGroupScheme.constantGeometricPointMap ℚ
        (Multiplicative x.subgroup.carrier) g ≫
      CommGroupScheme.underlyingHom
        (splitGammaZeroDatumOfRationalDatum x
          (concreteGroupSchemeInterface x e)).subgroup.inclusion =
      (subgroupSections x e g).left := by
  have h := EllipticQuotient.rationalCyclicSubgroupSectionHom_eq_map_constantPoint
    (concreteGroupSchemeInterface x e) x.subgroup g
  have hleft := congrArg Over.Hom.left h
  exact hleft.symm

/-- The actual quotient commutative group scheme of the concrete cubic by the cyclic subgroup
transported through `e`. Its underlying scheme is AINTLIB's finite-action quotient, not supplied
quotient data. -/
noncomputable def quotient
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve)) :
    CommGroupScheme (Spec (.of ℚ)) :=
  FiniteTranslationQuotient.commGroupScheme
    (E x) (subgroupSections x e) (quotientAtlas x e)
    (quotientAtlas_isStable x e) (quotientAtlas_isAffine x e)
    (mem_quotientAtlas x e) (subgroupAction_free x e)

/-- The actual finite étale quotient projection. -/
noncomputable def projection
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve)) :
    (E x) ⟶ quotient x e :=
  FiniteTranslationQuotient.projectionHom
    (E x) (subgroupSections x e) (quotientAtlas x e)
    (quotientAtlas_isStable x e) (quotientAtlas_isAffine x e)
    (mem_quotientAtlas x e) (subgroupAction_free x e)

/-- The represented quotient, bundled as an actual abelian variety.  Properness and geometric
integrality are proved from the finite étale quotient projection; this object is not supplied as
quotient data. -/
noncomputable def quotientAbelianVariety
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve)) :
    TauCeti.AlgebraicGeometry.AbelianVariety ℚ :=
  FiniteTranslationQuotient.abelianVariety
    (E x) (subgroupSections x e) (quotientAtlas x e)
    (quotientAtlas_isStable x e) (quotientAtlas_isAffine x e)
    (mem_quotientAtlas x e) (subgroupAction_free x e)

@[simp]
theorem quotientAbelianVariety_toOver
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve)) :
    (quotientAbelianVariety x e).toOver = (quotient x e).X :=
  rfl

/-- The finite étale quotient projection with its represented abelian-variety target exposed. -/
noncomputable def projectionToQuotientAbelianVariety
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve)) :
    (E x) ⟶ CommGrp.mk (quotientAbelianVariety x e).toOver :=
  FiniteTranslationQuotient.projectionToAbelianVariety
    (E x) (subgroupSections x e) (quotientAtlas x e)
    (quotientAtlas_isStable x e) (quotientAtlas_isAffine x e)
    (mem_quotientAtlas x e) (subgroupAction_free x e)

@[simp]
theorem projectionToQuotientAbelianVariety_eq_projection
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve)) :
    projectionToQuotientAbelianVariety x e = projection x e :=
  rfl

/-- The named projection to the represented abelian quotient is finite. -/
theorem projectionToQuotientAbelianVariety_isFinite
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve)) :
    IsFinite (CommGroupScheme.underlyingHom
      (projectionToQuotientAbelianVariety x e)) :=
  FiniteTranslationQuotient.projection_isFinite
    (E x) (subgroupSections x e) (quotientAtlas x e)
    (quotientAtlas_isStable x e) (quotientAtlas_isAffine x e)
    (mem_quotientAtlas x e) (subgroupAction_free x e)

/-- The named projection to the represented abelian quotient is étale. -/
theorem projectionToQuotientAbelianVariety_etale
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve)) :
    Etale (CommGroupScheme.underlyingHom
      (projectionToQuotientAbelianVariety x e)) :=
  FiniteTranslationQuotient.projection_etale
    (E x) (subgroupSections x e) (quotientAtlas x e)
    (quotientAtlas_isStable x e) (quotientAtlas_isAffine x e)
    (mem_quotientAtlas x e) (subgroupAction_free x e)

/-- The named projection is an fppf cover of the represented abelian quotient. -/
theorem projectionToQuotientAbelianVariety_is_fppf
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve)) :
    Flat (CommGroupScheme.underlyingHom
        (projectionToQuotientAbelianVariety x e)) ∧
      Surjective (CommGroupScheme.underlyingHom
        (projectionToQuotientAbelianVariety x e)) ∧
      LocallyOfFinitePresentation (CommGroupScheme.underlyingHom
        (projectionToQuotientAbelianVariety x e)) := by
  letI : Etale (CommGroupScheme.underlyingHom
      (projectionToQuotientAbelianVariety x e)) :=
    projectionToQuotientAbelianVariety_etale x e
  refine ⟨inferInstance, ?_, inferInstance⟩
  exact FiniteTranslationQuotient.projection_surjective
    (E x) (subgroupSections x e) (quotientAtlas x e)
    (quotientAtlas_isStable x e) (quotientAtlas_isAffine x e)
    (mem_quotientAtlas x e)

/-- Together with the bundled proper, geometrically integral commutative-group structure,
relative dimension one identifies the represented finite-translation quotient as an elliptic
curve. -/
theorem quotient_structureMap_smoothOfRelativeDimension_one
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve)) :
    SmoothOfRelativeDimension 1 (quotient x e).X.hom := by
  let f := CommGroupScheme.underlyingHom (projection x e)
  let g := (quotient x e).X.hom
  letI : IsFinite f := by
    dsimp only [f]
    exact FiniteTranslationQuotient.projection_isFinite
      (E x) (subgroupSections x e) (quotientAtlas x e)
      (quotientAtlas_isStable x e) (quotientAtlas_isAffine x e)
      (mem_quotientAtlas x e) (subgroupAction_free x e)
  letI : IsAffineHom f := by infer_instance
  letI : Etale f := by
    dsimp only [f]
    exact FiniteTranslationQuotient.projection_etale
      (E x) (subgroupSections x e) (quotientAtlas x e)
      (quotientAtlas_isStable x e) (quotientAtlas_isAffine x e)
      (mem_quotientAtlas x e) (subgroupAction_free x e)
  letI : Surjective f := by
    dsimp only [f]
    exact FiniteTranslationQuotient.projection_surjective
      (E x) (subgroupSections x e) (quotientAtlas x e)
      (quotientAtlas_isStable x e) (quotientAtlas_isAffine x e)
      (mem_quotientAtlas x e)
  letI : Smooth g := by
    change Smooth (quotientAbelianVariety x e).toOver.hom
    infer_instance
  have hfg : f ≫ g = (toOver x.curve).hom := by
    exact (projection x e).hom.hom.hom.w
  letI : SmoothOfRelativeDimension 1 (f ≫ g) := by
    rw [hfg]
    change SmoothOfRelativeDimension 1
      (WeierstrassProjectiveCubic.structureMap x.curve)
    infer_instance
  exact MazurTorsion.AlgebraicGeometry.smoothOfRelativeDimension_of_etale_surjective_comp
    1 f g

/-- The transported rational cyclic subgroup is exactly the geometric kernel of the actual
projection. -/
noncomputable def projectionKernelIso
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve)) :
    (splitGammaZeroDatumOfRationalDatum x
        (concreteGroupSchemeInterface x e)).subgroup.carrier.obj ≅
      CommGroupScheme.kernel (projection x e) :=
  FiniteTranslationQuotient.kernelIso
    (E x) (subgroupSections x e) (quotientAtlas x e)
    (quotientAtlas_isStable x e) (quotientAtlas_isAffine x e)
    (mem_quotientAtlas x e) (subgroupAction_free x e)
    (splitGammaZeroDatumOfRationalDatum x
      (concreteGroupSchemeInterface x e)).subgroup.inclusion
    (constantPoint_comp_subgroupInclusion x e)

@[reassoc]
theorem projectionKernelIso_hom_kernelInclusion
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve)) :
    (projectionKernelIso x e).hom ≫
        CommGroupScheme.kernelInclusion (projection x e) =
      (splitGammaZeroDatumOfRationalDatum x
        (concreteGroupSchemeInterface x e)).subgroup.inclusion :=
  FiniteTranslationQuotient.kernelIso_hom_kernelInclusion
    (E x) (subgroupSections x e) (quotientAtlas x e)
    (quotientAtlas_isStable x e) (quotientAtlas_isAffine x e)
    (mem_quotientAtlas x e) (subgroupAction_free x e)
    (splitGammaZeroDatumOfRationalDatum x
      (concreteGroupSchemeInterface x e)).subgroup.inclusion
    (constantPoint_comp_subgroupInclusion x e)

/-- The transported rational cyclic subgroup is the canonical kernel of the named projection to
the represented abelian quotient. -/
noncomputable def projectionToQuotientAbelianVarietyKernelIso
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve)) :
    (splitGammaZeroDatumOfRationalDatum x
        (concreteGroupSchemeInterface x e)).subgroup.carrier.obj ≅
      CommGroupScheme.kernel (projectionToQuotientAbelianVariety x e) :=
  projectionKernelIso x e

@[reassoc]
theorem projectionToQuotientAbelianVarietyKernelIso_hom_kernelInclusion
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve)) :
    (projectionToQuotientAbelianVarietyKernelIso x e).hom ≫
        CommGroupScheme.kernelInclusion
          (projectionToQuotientAbelianVariety x e) =
      (splitGammaZeroDatumOfRationalDatum x
        (concreteGroupSchemeInterface x e)).subgroup.inclusion :=
  projectionKernelIso_hom_kernelInclusion x e

/-- Honest construction of the formerly supplied geometric quotient boundary. -/
noncomputable def geometricQuotientPresentation
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve)) :
    RationalDatumGeometricQuotientPresentation x
      (concreteGroupSchemeInterface x e) :=
  FiniteTranslationQuotient.fppfQuotientPresentation
    (E x) (subgroupSections x e) (quotientAtlas x e)
    (quotientAtlas_isStable x e) (quotientAtlas_isAffine x e)
    (mem_quotientAtlas x e) (subgroupAction_free x e)
    (splitGammaZeroDatumOfRationalDatum x
      (concreteGroupSchemeInterface x e)).subgroup.inclusion
    (constantPoint_comp_subgroupInclusion x e)

@[simp]
theorem geometricQuotientPresentation_quotient
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve)) :
    (geometricQuotientPresentation x e).quotient = quotient x e :=
  rfl

@[simp]
theorem geometricQuotientPresentation_project
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve)) :
    (geometricQuotientPresentation x e).project = projection x e :=
  rfl

/-- The constructed presentation after an arbitrary base change. -/
noncomputable def geometricQuotientPresentationBaseChange
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve))
    {T : Scheme} (t : T ⟶ Spec (.of ℚ)) :=
  (geometricQuotientPresentation x e).baseChange t

@[simp]
theorem geometricQuotientPresentationBaseChange_quotient
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve))
    {T : Scheme} (t : T ⟶ Spec (.of ℚ)) :
    (geometricQuotientPresentationBaseChange x e t).quotient =
      (Over.pullback t).mapCommGrp.obj (quotient x e) :=
  rfl

@[simp]
theorem geometricQuotientPresentationBaseChange_project
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve))
    {T : Scheme} (t : T ⟶ Spec (.of ℚ)) :
    (geometricQuotientPresentationBaseChange x e t).project =
      (Over.pullback t).mapCommGrp.map (projection x e) :=
  rfl

/-- The pulled-back geometric quotient projection is finite over every base scheme. -/
theorem geometricQuotientPresentationBaseChange_project_isFinite
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve))
    {T : Scheme} (t : T ⟶ Spec (.of ℚ)) :
    IsFinite (CommGroupScheme.underlyingHom
      (geometricQuotientPresentationBaseChange x e t).project) := by
  exact MorphismProperty.overPullbackMap t (projection x e).hom.hom.hom
    (projectionToQuotientAbelianVariety_isFinite x e)

/-- The pulled-back geometric quotient projection is étale over every base scheme. -/
theorem geometricQuotientPresentationBaseChange_project_etale
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve))
    {T : Scheme} (t : T ⟶ Spec (.of ℚ)) :
    Etale (CommGroupScheme.underlyingHom
      (geometricQuotientPresentationBaseChange x e t).project) := by
  exact MorphismProperty.overPullbackMap t (projection x e).hom.hom.hom
    (projectionToQuotientAbelianVariety_etale x e)

/-- The quotient remains smooth of relative dimension one after every morphism of base schemes. -/
theorem
    geometricQuotientPresentationBaseChange_quotient_structureMap_smoothOfRelativeDimension_one
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve))
    {T : Scheme} (t : T ⟶ Spec (.of ℚ)) :
    SmoothOfRelativeDimension 1
      (geometricQuotientPresentationBaseChange x e t).quotient.X.hom := by
  change SmoothOfRelativeDimension 1
    (((Over.pullback t).mapCommGrp.obj (quotient x e)).X.hom)
  change SmoothOfRelativeDimension 1
    (((Over.pullback t).obj (quotient x e).X).hom)
  letI : MorphismProperty.IsStableUnderBaseChange
      (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  exact MorphismProperty.baseChange_obj t (quotient x e).X
    (quotient_structureMap_smoothOfRelativeDimension_one x e)

@[simp]
theorem geometricQuotientPresentationBaseChange_kernel_inclusion
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve))
    {T : Scheme} (t : T ⟶ Spec (.of ℚ)) :
    (geometricQuotientPresentationBaseChange x e t).kernelPresentation.inclusion =
      (Over.pullback t).mapCommGrp.map
        (splitGammaZeroDatumOfRationalDatum x
          (concreteGroupSchemeInterface x e)).subgroup.inclusion :=
  rfl

/-- Exactness of the constructed quotient kernel after an arbitrary morphism of base schemes. -/
theorem geometricQuotientPresentationBaseChange_kernel_exact
    (x : RationalDatum ℚ N)
    [GrpObj (toOver x.curve)]
    (e : Multiplicative x.curve.toProjective.Point ≃*
      AbelianVarietyRationalPoint (toAbelianVariety x.curve))
    {T : Scheme} (t : T ⟶ Spec (.of ℚ)) :
    (geometricQuotientPresentationBaseChange x e t).kernelIso.hom ≫
        CommGroupScheme.kernelInclusion
          (geometricQuotientPresentationBaseChange x e t).project =
      (Over.pullback t).mapCommGrp.map
        (splitGammaZeroDatumOfRationalDatum x
          (concreteGroupSchemeInterface x e)).subgroup.inclusion :=
  (geometricQuotientPresentationBaseChange x e t).kernelIso_hom_kernelInclusion

end EllipticQuotientRepresentability
end WeierstrassGroupSchemeInterface
end MazurTorsion.ModularCurve.XZeroFiniteFlatModuli

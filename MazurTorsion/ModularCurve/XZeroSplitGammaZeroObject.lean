/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/

import MazurTorsion.ModularCurve.XZeroWeierstrassCanonicalFiniteFlatSubgroup
import MazurTorsion.ModularCurve.XZeroWeierstrassRelativeDimension

/-!
# Intrinsic split `Gamma_0(N)` objects over fields

This module replaces the presentation-level source of the future open modular
curve classifier by an intrinsic geometric object.  A `SplitGeometricDatum`
contains a proper geometrically integral commutative group scheme, its checked
relative dimension one, and an actual split finite-flat cyclic subgroup.  It
therefore records an elliptic curve with split `Gamma_0(N)` structure without
remembering a Weierstrass equation, a coordinate-point equivalence, or a
chosen generator.

`SplitGeometricDatum.Iso` is an isomorphism of the ambient group schemes
together with an isomorphism of the finite-flat carriers which commutes with
their inclusions.  Its quotient `IsomorphismClass` is the honest field-valued
split moduli set.  Scalar extension descends to this quotient.

This remains strictly below representability: no scheme is asserted to
represent these classes, and no class is called a point of `X_0(N)`.  The next
geometric layer must construct a natural moduli functor for arbitrary bases
and prove its coarse representability.  The named downstream consumer is
`MazurTorsion.XZeroFortyNine.splitGeometricModuliClassOfOrderFortyNineTorsion`.
-/

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry
open TauCeti.AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroModuli

open XZeroFiniteFlatModuli
open XZeroFiniteFlatModuli.WeierstrassProjectiveCubic

universe u

/-- An intrinsic split `Gamma_0(N)` object over a field.

The ambient commutative group scheme is proper, geometrically integral, and
smooth of relative dimension one.  The subgroup is an actual finite-flat
closed subgroup which is isomorphic to the constant cyclic group of order
`N`; no generator or Weierstrass presentation is retained. -/
structure SplitGeometricDatum (K : Type u) [Field K]
    (N : ℕ) [NeZero N] where
  /-- The ambient commutative group scheme. -/
  curve : CommGroupScheme (Spec (.of K))
  /-- Properness of the elliptic curve over the ground field. -/
  isProper : IsProper curve.X.hom
  /-- Geometric integrality of the elliptic curve over the ground field. -/
  geometricallyIntegral : GeometricallyIntegral curve.X.hom
  /-- The relative dimension is exactly one. -/
  smoothOfRelativeDimensionOne : SmoothOfRelativeDimension 1 curve.X.hom
  /-- The finite-flat split cyclic subgroup of level `N`. -/
  subgroup : SplitCyclicSubgroup curve (N := N)

namespace SplitGeometricDatum

variable {K : Type u} [Field K] {N : ℕ} [NeZero N]

attribute [instance] SplitGeometricDatum.isProper
  SplitGeometricDatum.geometricallyIntegral
  SplitGeometricDatum.smoothOfRelativeDimensionOne

/-- Forget the level structure and bundle the ambient curve as an abelian
variety. -/
noncomputable def toAbelianVariety (D : SplitGeometricDatum K N) :
    AbelianVariety K where
  toOver := D.curve.X
  grpObj := inferInstance
  isProper := inferInstance
  geometricallyIntegral := inferInstance

@[simp]
theorem toAbelianVariety_toOver (D : SplitGeometricDatum K N) :
    D.toAbelianVariety.toOver = D.curve.X :=
  rfl

/-- Scalar extension of an intrinsic split `Gamma_0(N)` object.  Properness,
geometric integrality, relative dimension one, and the split cyclic subgroup
all persist under base change. -/
noncomputable def baseChange (D : SplitGeometricDatum K N)
    (L : Type u) [Field L] [Algebra K L] : SplitGeometricDatum L N where
  curve := (Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapCommGrp.obj D.curve
  isProper := by
    change IsProper (Limits.pullback.snd D.curve.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    infer_instance
  geometricallyIntegral := by
    change GeometricallyIntegral (Limits.pullback.snd D.curve.X.hom
      (Spec.map (CommRingCat.ofHom (algebraMap K L))))
    infer_instance
  smoothOfRelativeDimensionOne := by
    let t := Spec.map (CommRingCat.ofHom (algebraMap K L))
    change SmoothOfRelativeDimension 1 ((Over.pullback t).obj D.curve.X).hom
    letI : MorphismProperty.IsStableUnderBaseChangeAlong
        (@SmoothOfRelativeDimension 1) t :=
      ⟨fun pb h ↦
        (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback pb h⟩
    exact MorphismProperty.baseChange_obj t D.curve.X
      D.smoothOfRelativeDimensionOne
  subgroup := D.subgroup.baseChange

@[simp]
theorem baseChange_curve (D : SplitGeometricDatum K N)
    (L : Type u) [Field L] [Algebra K L] :
    (D.baseChange L).curve =
      (Over.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapCommGrp.obj D.curve :=
  rfl

@[simp]
theorem baseChange_subgroup (D : SplitGeometricDatum K N)
    (L : Type u) [Field L] [Algebra K L] :
    (D.baseChange L).subgroup = D.subgroup.baseChange :=
  rfl

/-- A subgroup-preserving isomorphism of intrinsic split `Gamma_0(N)`
objects. -/
structure Iso (X Y : SplitGeometricDatum K N) where
  /-- Isomorphism of the ambient commutative group schemes. -/
  curveIso : X.curve ≅ Y.curve
  /-- Isomorphism of the finite-flat subgroup carriers. -/
  subgroupIso : X.subgroup.carrier ≅ Y.subgroup.carrier
  /-- The carrier isomorphism respects both closed subgroup inclusions. -/
  inclusion_compatibility :
    subgroupIso.hom.hom ≫ Y.subgroup.inclusion =
      X.subgroup.inclusion ≫ curveIso.hom

namespace Iso

/-- Identity isomorphism of a split geometric datum. -/
def refl (X : SplitGeometricDatum K N) : Iso X X where
  curveIso := CategoryTheory.Iso.refl _
  subgroupIso := CategoryTheory.Iso.refl _
  inclusion_compatibility := by simp

/-- Inverse of a subgroup-preserving isomorphism. -/
def symm {X Y : SplitGeometricDatum K N} (e : Iso X Y) : Iso Y X where
  curveIso := e.curveIso.symm
  subgroupIso := e.subgroupIso.symm
  inclusion_compatibility := by
    rw [← cancel_epi e.subgroupIso.hom.hom]
    have hcarrier :
        e.subgroupIso.hom.hom ≫ e.subgroupIso.inv.hom = 𝟙 _ :=
      congrArg (fun f ↦ f.hom) e.subgroupIso.hom_inv_id
    calc
      e.subgroupIso.hom.hom ≫ e.subgroupIso.inv.hom ≫
          X.subgroup.inclusion = X.subgroup.inclusion := by
            rw [← Category.assoc, hcarrier, Category.id_comp]
      _ = X.subgroup.inclusion ≫ e.curveIso.hom ≫
          e.curveIso.inv := by simp
      _ = e.subgroupIso.hom.hom ≫ Y.subgroup.inclusion ≫
          e.curveIso.inv := by
            simpa only [Category.assoc] using
              congrArg (fun q ↦ q ≫ e.curveIso.inv)
                e.inclusion_compatibility.symm

/-- Composite of subgroup-preserving isomorphisms. -/
def trans {X Y Z : SplitGeometricDatum K N}
    (e : Iso X Y) (f : Iso Y Z) : Iso X Z where
  curveIso := e.curveIso.trans f.curveIso
  subgroupIso := e.subgroupIso.trans f.subgroupIso
  inclusion_compatibility := by
    change (e.subgroupIso.hom.hom ≫ f.subgroupIso.hom.hom) ≫
        Z.subgroup.inclusion =
      X.subgroup.inclusion ≫ (e.curveIso.hom ≫ f.curveIso.hom)
    simp only [Category.assoc]
    rw [f.inclusion_compatibility, ← Category.assoc,
      e.inclusion_compatibility]
    exact Category.assoc _ _ _

/-- Scalar extension preserves subgroup-compatible isomorphisms. -/
noncomputable def baseChange {X Y : SplitGeometricDatum K N}
    (e : Iso X Y) (L : Type u) [Field L] [Algebra K L] :
    Iso (X.baseChange L) (Y.baseChange L) where
  curveIso := (Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapCommGrp.mapIso e.curveIso
  subgroupIso := (FiniteFlatCommGroupScheme.baseChange
    (Spec.map (CommRingCat.ofHom (algebraMap K L)))).mapIso e.subgroupIso
  inclusion_compatibility := by
    let t := Spec.map (CommRingCat.ofHom (algebraMap K L))
    let F := (Over.pullback t).mapCommGrp
    change F.map e.subgroupIso.hom.hom ≫ F.map Y.subgroup.inclusion =
      F.map X.subgroup.inclusion ≫ F.map e.curveIso.hom
    rw [← F.map_comp, e.inclusion_compatibility, F.map_comp]

end Iso

/-- Two split geometric data define the same field-valued moduli object when
they are isomorphic through their ambient curves and subgroup inclusions. -/
def Isomorphic (X Y : SplitGeometricDatum K N) : Prop :=
  Nonempty (Iso X Y)

theorem isomorphic_refl (X : SplitGeometricDatum K N) : Isomorphic X X :=
  ⟨Iso.refl X⟩

theorem isomorphic_symm {X Y : SplitGeometricDatum K N} :
    Isomorphic X Y → Isomorphic Y X :=
  fun ⟨e⟩ ↦ ⟨e.symm⟩

theorem isomorphic_trans {X Y Z : SplitGeometricDatum K N} :
    Isomorphic X Y → Isomorphic Y Z → Isomorphic X Z :=
  fun ⟨e⟩ ⟨f⟩ ↦ ⟨e.trans f⟩

/-- The equivalence relation generated by genuine subgroup-preserving
isomorphisms; unlike the earlier coordinate quotient, no Weierstrass
presentation occurs here. -/
def isomorphicSetoid : Setoid (SplitGeometricDatum K N) where
  r := Isomorphic
  iseqv := ⟨isomorphic_refl, isomorphic_symm, isomorphic_trans⟩

/-- The field-valued split `Gamma_0(N)` moduli set.  This quotient is not
claimed to be represented by a scheme. -/
def IsomorphismClass (K : Type u) [Field K] (N : ℕ) [NeZero N] :=
  Quotient (isomorphicSetoid (K := K) (N := N))

/-- Forget a representative of an intrinsic split datum. -/
def classOf (D : SplitGeometricDatum K N) : IsomorphismClass K N :=
  Quotient.mk (isomorphicSetoid (K := K) (N := N)) D

namespace IsomorphismClass

/-- Scalar extension on field-valued split moduli classes. -/
noncomputable def baseChange (L : Type u) [Field L] [Algebra K L] :
    IsomorphismClass K N → IsomorphismClass L N :=
  Quotient.lift (fun D ↦ classOf (D.baseChange L)) (fun X Y hXY ↦ by
    apply Quotient.sound
    obtain ⟨e⟩ := hXY
    exact ⟨e.baseChange L⟩)

@[simp]
theorem baseChange_classOf (L : Type u) [Field L] [Algebra K L]
    (D : SplitGeometricDatum K N) :
    baseChange L (classOf D) = classOf (D.baseChange L) :=
  rfl

end IsomorphismClass

/-- The intrinsic geometric datum generated by a point of exact order `N` on
a Weierstrass elliptic curve.  All group-scheme and point-comparison data are
the canonical checked constructions on the concrete projective cubic. -/
noncomputable def ofExactTorsion [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (P : W.toAffine.Point) (hP : addOrderOf P = N) :
    SplitGeometricDatum K N where
  curve := (canonicalWeierstrassGroupSchemeInterface W).groupScheme
  isProper := by
    change IsProper (structureMap W)
    infer_instance
  geometricallyIntegral := by
    change GeometricallyIntegral (structureMap W)
    infer_instance
  smoothOfRelativeDimensionOne := by
    change SmoothOfRelativeDimension 1 (structureMap W)
    infer_instance
  subgroup := (canonicalSplitGammaZeroDatumOfTorsion W P hP).subgroup

@[simp]
theorem ofExactTorsion_curve [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (P : W.toAffine.Point) (hP : addOrderOf P = N) :
    (ofExactTorsion W P hP).curve =
      (canonicalWeierstrassGroupSchemeInterface W).groupScheme :=
  rfl

@[simp]
theorem ofExactTorsion_subgroup [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (P : W.toAffine.Point) (hP : addOrderOf P = N) :
    (ofExactTorsion W P hP).subgroup =
      (canonicalSplitGammaZeroDatumOfTorsion W P hP).subgroup :=
  rfl

/-- The intrinsic subgroup generated by exact torsion has constant geometric
order `N`. -/
theorem ofExactTorsion_subgroup_hasConstantOrder [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (P : W.toAffine.Point) (hP : addOrderOf P = N) :
    (ofExactTorsion W P hP).subgroup.carrier.HasConstantOrder N :=
  canonicalSplitGammaZeroDatumOfTorsion_hasConstantOrder W P hP

/-- A point of exact order `N` determines an intrinsic field-valued split
moduli class, with no chosen generator or Weierstrass presentation in the
codomain. -/
noncomputable def classOfExactTorsion [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (P : W.toAffine.Point) (hP : addOrderOf P = N) :
    IsomorphismClass K N :=
  classOf (ofExactTorsion W P hP)

end SplitGeometricDatum

end MazurTorsion.ModularCurve.XZeroModuli

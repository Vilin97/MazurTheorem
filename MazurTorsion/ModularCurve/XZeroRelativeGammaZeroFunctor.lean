/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/

import MazurTorsion.ModularCurve.XZeroRelativeGammaZeroFamily

/-!
# The locally constant `Gamma_0(N)` moduli functor

This module quotients relative locally constant `Gamma_0(N)` families by
isomorphisms of their ambient group schemes and finite-flat subgroup carriers
which commute with the inclusions.  Choices of fppf cover and local
trivialization are therefore property witnesses, not part of the resulting
moduli class.

The pullback operation from `XZeroRelativeGammaZeroFamily` descends to these
classes.  Canonical identity and composition isomorphisms for pullback prove
the functor laws, producing an actual contravariant functor from schemes to
types.  The earlier field-valued split quotient maps into this functor without
choosing a representative.

This is only the locally constant (finite-etale) open moduli problem.  No
representing scheme, universal family, generalized cyclic subgroup at bad
characteristic, compactification, cusp, or point of `X_0(N)` is constructed.
The named downstream consumer is
`MazurTorsion.XZeroFortyNine.locallyConstantGammaZeroModuliClassOfOrderFortyNineTorsion`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroModuli

open XZeroFiniteFlatModuli

universe u

variable {S T : Scheme.{u}} {N : ℕ} [NeZero N]

/-- Pullback along the identity, as a natural isomorphism on commutative
group schemes. -/
noncomputable def commGroupBaseChangeIdNatIso (S : Scheme.{u}) :
    (Over.pullback (𝟙 S)).mapCommGrp ≅ 𝟭 (CommGroupScheme S) :=
  Functor.mapCommGrpNatIso Over.pullbackId ≪≫ Functor.mapCommGrpIdIso

/-- Pullback along a composite, as a natural isomorphism on commutative
group schemes. -/
noncomputable def commGroupBaseChangeCompNatIso
    {R S T : Scheme.{u}} (f : T ⟶ S) (g : S ⟶ R) :
    (Over.pullback (f ≫ g)).mapCommGrp ≅
      (Over.pullback g).mapCommGrp ⋙ (Over.pullback f).mapCommGrp :=
  Functor.mapCommGrpNatIso (Over.pullbackComp f g) ≪≫
    Functor.mapCommGrpCompIso

namespace LocallyConstantGammaZeroFamily

/-- A subgroup-preserving isomorphism of relative locally constant
`Gamma_0(N)` families.

The fppf covers and their trivializations do not appear: they witness a local
property of the carrier. -/
structure Iso (X Y : LocallyConstantGammaZeroFamily S N) where
  /-- Isomorphism of the ambient relative group schemes. -/
  curveIso : X.curve ≅ Y.curve
  /-- Isomorphism of the finite-flat subgroup carriers. -/
  subgroupIso : X.subgroup.carrier ≅ Y.subgroup.carrier
  /-- The carrier isomorphism respects both subgroup inclusions. -/
  inclusion_compatibility :
    subgroupIso.hom.hom ≫ Y.subgroup.inclusion =
      X.subgroup.inclusion ≫ curveIso.hom

namespace Iso

/-- Identity isomorphism of a relative family. -/
def refl (X : LocallyConstantGammaZeroFamily S N) : Iso X X where
  curveIso := CategoryTheory.Iso.refl _
  subgroupIso := CategoryTheory.Iso.refl _
  inclusion_compatibility := by simp

/-- Inverse of a subgroup-preserving relative-family isomorphism. -/
def symm {X Y : LocallyConstantGammaZeroFamily S N}
    (e : Iso X Y) : Iso Y X where
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

/-- Composite of subgroup-preserving relative-family isomorphisms. -/
def trans {X Y Z : LocallyConstantGammaZeroFamily S N}
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

/-- Pullback preserves subgroup-compatible isomorphisms. -/
noncomputable def baseChange
    {X Y : LocallyConstantGammaZeroFamily S N}
    (e : Iso X Y) (f : T ⟶ S) :
    Iso (X.baseChange f) (Y.baseChange f) where
  curveIso := (Over.pullback f).mapCommGrp.mapIso e.curveIso
  subgroupIso :=
    (FiniteFlatCommGroupScheme.baseChange f).mapIso e.subgroupIso
  inclusion_compatibility := by
    let F := (Over.pullback f).mapCommGrp
    change F.map e.subgroupIso.hom.hom ≫ F.map Y.subgroup.inclusion =
      F.map X.subgroup.inclusion ≫ F.map e.curveIso.hom
    rw [← F.map_comp, e.inclusion_compatibility, F.map_comp]

/-- Pullback along the identity is isomorphic to the original family. -/
noncomputable def baseChangeIdIso
    (X : LocallyConstantGammaZeroFamily S N) :
    Iso (X.baseChange (𝟙 S)) X where
  curveIso := (commGroupBaseChangeIdNatIso S).app X.curve
  subgroupIso := finiteFlatBaseChangeIdIso S X.subgroup.carrier
  inclusion_compatibility := by
    change
      (commGroupBaseChangeIdNatIso S).hom.app X.subgroup.carrier.obj ≫
          X.subgroup.inclusion =
        (Over.pullback (𝟙 S)).mapCommGrp.map X.subgroup.inclusion ≫
          (commGroupBaseChangeIdNatIso S).hom.app X.curve
    exact ((commGroupBaseChangeIdNatIso S).hom.naturality
      X.subgroup.inclusion).symm

/-- Pullback along a composite is isomorphic to iterated pullback. -/
noncomputable def baseChangeCompIso
    {R S T : Scheme.{u}} (X : LocallyConstantGammaZeroFamily R N)
    (f : T ⟶ S) (g : S ⟶ R) :
    Iso (X.baseChange (f ≫ g)) ((X.baseChange g).baseChange f) where
  curveIso := (commGroupBaseChangeCompNatIso f g).app X.curve
  subgroupIso := finiteFlatBaseChangeCompIso S f g X.subgroup.carrier
  inclusion_compatibility := by
    change
      (commGroupBaseChangeCompNatIso f g).hom.app
          X.subgroup.carrier.obj ≫
          ((Over.pullback g).mapCommGrp ⋙
            (Over.pullback f).mapCommGrp).map X.subgroup.inclusion =
        (Over.pullback (f ≫ g)).mapCommGrp.map X.subgroup.inclusion ≫
          (commGroupBaseChangeCompNatIso f g).hom.app X.curve
    exact ((commGroupBaseChangeCompNatIso f g).hom.naturality
      X.subgroup.inclusion).symm

/-- A split field-family isomorphism induces an isomorphism of the associated
relative locally constant families. -/
def ofSplitGeometricIso
    {K : Type u} [Field K]
    {X Y : SplitGeometricDatum K N}
    (e : SplitGeometricDatum.Iso X Y) :
    Iso (ofSplitGeometricDatum K X) (ofSplitGeometricDatum K Y) where
  curveIso := e.curveIso
  subgroupIso := e.subgroupIso
  inclusion_compatibility := e.inclusion_compatibility

end Iso

/-- Two relative families give the same moduli object when their curves and
subgroup inclusions are compatibly isomorphic. -/
def Isomorphic (X Y : LocallyConstantGammaZeroFamily S N) : Prop :=
  Nonempty (Iso X Y)

theorem isomorphic_refl (X : LocallyConstantGammaZeroFamily S N) :
    Isomorphic X X :=
  ⟨Iso.refl X⟩

theorem isomorphic_symm {X Y : LocallyConstantGammaZeroFamily S N} :
    Isomorphic X Y → Isomorphic Y X :=
  fun ⟨e⟩ ↦ ⟨e.symm⟩

theorem isomorphic_trans {X Y Z : LocallyConstantGammaZeroFamily S N} :
    Isomorphic X Y → Isomorphic Y Z → Isomorphic X Z :=
  fun ⟨e⟩ ⟨f⟩ ↦ ⟨e.trans f⟩

/-- The equivalence relation of subgroup-preserving family isomorphism. -/
def isomorphicSetoid : Setoid (LocallyConstantGammaZeroFamily S N) where
  r := Isomorphic
  iseqv := ⟨isomorphic_refl, isomorphic_symm, isomorphic_trans⟩

/-- Isomorphism classes of locally constant relative `Gamma_0(N)` families
over a fixed scheme. -/
def IsomorphismClass (S : Scheme.{u}) (N : ℕ) [NeZero N] :=
  Quotient (isomorphicSetoid (S := S) (N := N))

/-- Forget a representative relative family. -/
def classOf (D : LocallyConstantGammaZeroFamily S N) :
    IsomorphismClass S N :=
  Quotient.mk (isomorphicSetoid (S := S) (N := N)) D

namespace IsomorphismClass

/-- Pullback descends to isomorphism classes of relative families. -/
noncomputable def baseChange (f : T ⟶ S) :
    IsomorphismClass S N → IsomorphismClass T N :=
  Quotient.lift (fun D ↦ classOf (D.baseChange f)) (fun X Y hXY ↦ by
    apply Quotient.sound
    obtain ⟨e⟩ := hXY
    exact ⟨e.baseChange f⟩)

@[simp]
theorem baseChange_classOf (f : T ⟶ S)
    (D : LocallyConstantGammaZeroFamily S N) :
    baseChange f (classOf D) = classOf (D.baseChange f) :=
  rfl

@[simp]
theorem baseChange_id (x : IsomorphismClass S N) :
    baseChange (𝟙 S) x = x := by
  induction x using Quotient.inductionOn with
  | _ D =>
      apply Quotient.sound
      exact ⟨Iso.baseChangeIdIso D⟩

/-- Pullback along a composite equals iterated pullback on isomorphism
classes. -/
theorem baseChange_comp {R : Scheme.{u}}
    (f : T ⟶ S) (g : S ⟶ R) (x : IsomorphismClass R N) :
    baseChange (f ≫ g) x = baseChange f (baseChange g x) := by
  induction x using Quotient.inductionOn with
  | _ D =>
      apply Quotient.sound
      exact ⟨Iso.baseChangeCompIso D f g⟩

/-- Pass from the intrinsic field-valued split quotient to the relative
locally constant moduli class without choosing a representative. -/
noncomputable def ofSplitGeometricClass
    (K : Type u) [Field K] :
    SplitGeometricDatum.IsomorphismClass K N →
      IsomorphismClass (Spec (.of K)) N :=
  Quotient.lift
    (fun D ↦ classOf (ofSplitGeometricDatum K D))
    (fun X Y hXY ↦ by
      apply Quotient.sound
      obtain ⟨e⟩ := hXY
      exact ⟨Iso.ofSplitGeometricIso e⟩)

@[simp]
theorem ofSplitGeometricClass_classOf
    (K : Type u) [Field K] (D : SplitGeometricDatum K N) :
    ofSplitGeometricClass K (SplitGeometricDatum.classOf D) =
      classOf (ofSplitGeometricDatum K D) :=
  rfl

end IsomorphismClass

/-- The contravariant type-valued moduli functor of locally constant
`Gamma_0(N)` families. -/
noncomputable def locallyConstantGammaZeroModuliFunctor
    (N : ℕ) [NeZero N] : Scheme.{u}ᵒᵖ ⥤ Type (u + 1) where
  obj S := IsomorphismClass S.unop N
  map f := ↾fun x ↦ IsomorphismClass.baseChange (N := N) f.unop x
  map_id S := by
    ext x
    exact IsomorphismClass.baseChange_id x
  map_comp f g := by
    ext x
    exact IsomorphismClass.baseChange_comp g.unop f.unop x

end LocallyConstantGammaZeroFamily

end MazurTorsion.ModularCurve.XZeroModuli

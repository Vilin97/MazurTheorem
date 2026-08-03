/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.SupportedFppfHOneBridge

/-!
# Invariance of represented fppf `H¹` under an isomorphism of bases

This file transports the concrete common-refinement model of fppf `H¹` along an isomorphism
of base schemes.  The transport is constructed on actual Cech cochains and covering families;
no abstract base-change assertion for sheaf cohomology is assumed.
-/

noncomputable section

open CategoryTheory

namespace CategoryTheory.PresheafOfCommGroups.BaseEquivalence

universe wI w v u

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v} D]
variable (e : C ≌ D) (A : Functor Cᵒᵖ CommGrpCat.{w})
variable {I : Type wI} (U : I → C)

private abbrev transported : Functor Dᵒᵖ CommGrpCat.{w} :=
  e.inverse.op ⋙ A

private abbrev mappedFamily : I → D :=
  fun i ↦ e.functor.obj (U i)

open PresheafOfGroups

private def zeroUp (a : ZeroCochain (toGroups A) U) :
    ZeroCochain (toGroups (transported e A)) (mappedFamily e U) :=
  fun i ↦ A.map (e.unitIso.inv.app (U i)).op (a i)

private def cochainUp (c : OneCochain (toGroups A) U) :
    OneCochain (toGroups (transported e A)) (mappedFamily e U) where
  ev i j T a b :=
    c.ev i j
      (e.inverse.map a ≫ e.unitIso.inv.app (U i))
      (e.inverse.map b ≫ e.unitIso.inv.app (U j))
  ev_precomp i j T T' φ a b := by
    change (toGroups A).map (e.inverse.map φ).op
        (c.ev i j
          (e.inverse.map a ≫ e.unitIso.inv.app (U i))
          (e.inverse.map b ≫ e.unitIso.inv.app (U j))) = _
    rw [c.ev_precomp]
    simp only [e.inverse.map_comp, Category.assoc]

private def cocycleUp (c : OneCocycle (toGroups A) U) :
    OneCocycle (toGroups (transported e A)) (mappedFamily e U) where
  toOneCochain := cochainUp e A U c.toOneCochain
  ev_trans i j k _T a b d :=
    c.ev_trans i j k
      (e.inverse.map a ≫ e.unitIso.inv.app (U i))
      (e.inverse.map b ≫ e.unitIso.inv.app (U j))
      (e.inverse.map d ≫ e.unitIso.inv.app (U k))

private lemma relation_up {c d : OneCocycle (toGroups A) U}
    (h : c.IsCohomologous d) :
    (cocycleUp e A U c).IsCohomologous (cocycleUp e A U d) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨zeroUp e A U a, ?_⟩
  intro i j T f g
  change (toGroups A).map (e.inverse.map f).op
        ((toGroups A).map (e.unitIso.inv.app (U i)).op (a i)) *
      c.ev i j
        (e.inverse.map f ≫ e.unitIso.inv.app (U i))
        (e.inverse.map g ≫ e.unitIso.inv.app (U j)) =
      d.ev i j
        (e.inverse.map f ≫ e.unitIso.inv.app (U i))
        (e.inverse.map g ≫ e.unitIso.inv.app (U j)) *
      (toGroups A).map (e.inverse.map g).op
        ((toGroups A).map (e.unitIso.inv.app (U j)).op (a j))
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
  simpa only [← op_comp] using
    ha i j
      (e.inverse.map f ≫ e.unitIso.inv.app (U i))
      (e.inverse.map g ≫ e.unitIso.inv.app (U j))

private def hOneUp : H1 A U → H1 (transported e A) (mappedFamily e U) :=
  Quot.lift
    (fun c ↦ (cocycleUp e A U c).class)
    (fun _ _ h ↦ (relation_up e A U h).class_eq)

private def cochainDown
    (c : OneCochain (toGroups (transported e A)) (mappedFamily e U)) :
    OneCochain (toGroups A) U where
  ev i j T a b :=
    A.map (e.unitIso.hom.app T).op
      (c.ev i j (e.functor.map a) (e.functor.map b))
  ev_precomp i j T T' φ a b := by
    change A.map φ.op
        (A.map (e.unitIso.hom.app T').op
          (c.ev i j (e.functor.map a) (e.functor.map b))) = _
    rw [← Functor.map_comp_apply]
    rw [← op_comp]
    have hunit :
        φ ≫ e.unitIso.hom.app T' =
          e.unitIso.hom.app T ≫ e.inverse.map (e.functor.map φ) := by
      simpa only [Functor.id_map, Functor.comp_map] using e.unit.naturality φ
    rw [hunit, op_comp]
    rw [Functor.map_comp_apply]
    change A.map (e.unitIso.hom.app T).op
        ((transported e A).map (e.functor.map φ).op
          (c.ev i j (e.functor.map a) (e.functor.map b))) = _
    apply congrArg (fun x ↦ A.map (e.unitIso.hom.app T).op x)
    change (toGroups (transported e A)).map (e.functor.map φ).op
        (c.ev i j (e.functor.map a) (e.functor.map b)) = _
    rw [c.ev_precomp]
    simp only [← e.functor.map_comp]

private def zeroDown
    (a : ZeroCochain (toGroups (transported e A)) (mappedFamily e U)) :
    ZeroCochain (toGroups A) U :=
  fun i ↦ A.map (e.unitIso.hom.app (U i)).op (a i)

private def cocycleDown
    (c : OneCocycle (toGroups (transported e A)) (mappedFamily e U)) :
    OneCocycle (toGroups A) U where
  toOneCochain := cochainDown e A U c.toOneCochain
  ev_trans i j k T a b d := by
    change A.map (e.unitIso.hom.app T).op
          (c.ev i j (e.functor.map a) (e.functor.map b)) *
        A.map (e.unitIso.hom.app T).op
          (c.ev j k (e.functor.map b) (e.functor.map d)) = _
    rw [← map_mul, c.ev_trans]
    rfl

private lemma relation_down
    {c d : OneCocycle (toGroups (transported e A)) (mappedFamily e U)}
    (h : c.IsCohomologous d) :
    (cocycleDown e A U c).IsCohomologous (cocycleDown e A U d) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨zeroDown e A U a, ?_⟩
  intro i j T f g
  have hmapped := congrArg
    (fun x ↦ A.map (e.unitIso.hom.app T).op x)
    (ha i j (e.functor.map f) (e.functor.map g))
  have hleft :
      A.map (e.unitIso.hom.app T).op
          ((toGroups (transported e A)).map (e.functor.map f).op (a i)) =
        (toGroups A).map f.op
          (A.map (e.unitIso.hom.app (U i)).op (a i)) := by
    change A.map (e.unitIso.hom.app T).op
        (A.map (e.inverse.map (e.functor.map f)).op (a i)) = _
    rw [← Functor.map_comp_apply, ← op_comp]
    have hunit :
        e.unitIso.hom.app T ≫ e.inverse.map (e.functor.map f) =
          f ≫ e.unitIso.hom.app (U i) := by
      simpa only [Functor.id_obj] using e.unit_naturality f
    rw [hunit, op_comp, Functor.map_comp_apply]
    rfl
  have hright :
      A.map (e.unitIso.hom.app T).op
          ((toGroups (transported e A)).map (e.functor.map g).op (a j)) =
        (toGroups A).map g.op
          (A.map (e.unitIso.hom.app (U j)).op (a j)) := by
    change A.map (e.unitIso.hom.app T).op
        (A.map (e.inverse.map (e.functor.map g)).op (a j)) = _
    rw [← Functor.map_comp_apply, ← op_comp]
    have hunit :
        e.unitIso.hom.app T ≫ e.inverse.map (e.functor.map g) =
          g ≫ e.unitIso.hom.app (U j) := by
      simpa only [Functor.id_obj] using e.unit_naturality g
    rw [hunit, op_comp, Functor.map_comp_apply]
    rfl
  simp only [Functor.id_obj] at hmapped ⊢
  simp only [map_mul] at hmapped
  rw [hleft, hright] at hmapped
  simpa only [zeroDown, cocycleDown, cochainDown] using hmapped

private def hOneDown : H1 (transported e A) (mappedFamily e U) → H1 A U :=
  Quot.lift
    (fun c ↦ (cocycleDown e A U c).class)
    (fun _ _ h ↦ (relation_down e A U h).class_eq)

private lemma cochain_down_up (c : OneCochain (toGroups A) U) :
    cochainDown e A U (cochainUp e A U c) = c := by
  apply OneCochain.ext
  funext i j T f g
  change (toGroups A).map (e.unitIso.hom.app T).op
      (c.ev i j
        (e.inverse.map (e.functor.map f) ≫ e.unitIso.inv.app (U i))
        (e.inverse.map (e.functor.map g) ≫ e.unitIso.inv.app (U j))) =
    c.ev i j f g
  rw [c.ev_precomp]
  have hf :
      e.unitIso.hom.app T ≫
          (e.inverse.map (e.functor.map f) ≫ e.unitIso.inv.app (U i)) = f := by
    rw [← Category.assoc]
    have hunit :
        f ≫ e.unitIso.hom.app (U i) =
          e.unitIso.hom.app T ≫ e.inverse.map (e.functor.map f) := by
      simpa only [Functor.id_map, Functor.comp_map] using e.unit.naturality f
    rw [← hunit, Category.assoc, e.unitIso.hom_inv_id_app]
    simpa only [Functor.id_obj] using Category.comp_id f
  have hg :
      e.unitIso.hom.app T ≫
          (e.inverse.map (e.functor.map g) ≫ e.unitIso.inv.app (U j)) = g := by
    rw [← Category.assoc]
    have hunit :
        g ≫ e.unitIso.hom.app (U j) =
          e.unitIso.hom.app T ≫ e.inverse.map (e.functor.map g) := by
      simpa only [Functor.id_map, Functor.comp_map] using e.unit.naturality g
    rw [← hunit, Category.assoc, e.unitIso.hom_inv_id_app]
    simpa only [Functor.id_obj] using Category.comp_id g
  rw [hf, hg]

private lemma cocycle_down_up (c : OneCocycle (toGroups A) U) :
    cocycleDown e A U (cocycleUp e A U c) = c := by
  apply PresheafOfGroups.FamilyRefinement.oneCocycle_ext
  exact cochain_down_up e A U c.toOneCochain

private lemma hOne_down_up (x : H1 A U) :
    hOneDown e A U (hOneUp e A U x) = x := by
  induction x using Quot.inductionOn with
  | _ c => exact congrArg OneCocycle.class (cocycle_down_up e A U c)

private lemma cochain_up_down
    (c : OneCochain (toGroups (transported e A)) (mappedFamily e U)) :
    cochainUp e A U (cochainDown e A U c) = c := by
  apply OneCochain.ext
  funext i j T f g
  change A.map (e.unitIso.hom.app (e.inverse.obj T)).op
      (c.ev i j
        (e.functor.map
          (e.inverse.map f ≫ e.unitIso.inv.app (U i)))
        (e.functor.map
          (e.inverse.map g ≫ e.unitIso.inv.app (U j)))) =
    c.ev i j f g
  have hf :
      e.functor.map
          (e.inverse.map f ≫ e.unitIso.inv.app (U i)) =
        e.counitIso.hom.app T ≫ f := by
    rw [e.functor.map_comp, ← e.counit_app_functor]
    simpa only [Functor.id_obj] using e.counit_naturality f
  have hg :
      e.functor.map
          (e.inverse.map g ≫ e.unitIso.inv.app (U j)) =
        e.counitIso.hom.app T ≫ g := by
    rw [e.functor.map_comp, ← e.counit_app_functor]
    simpa only [Functor.id_obj] using e.counit_naturality g
  rw [hf, hg]
  have hpre := c.ev_precomp i j (e.counitIso.hom.app T) f g
  change A.map (e.inverse.map (e.counitIso.hom.app T)).op
      (c.ev i j f g) =
        c.ev i j (e.counitIso.hom.app T ≫ f)
          (e.counitIso.hom.app T ≫ g) at hpre
  rw [← hpre, ← Functor.map_comp_apply, ← op_comp,
    e.unit_inverse_comp]
  change A.map (CategoryStruct.id (Opposite.op (e.inverse.obj T)))
      (c.ev i j f g) = c.ev i j f g
  exact A.map_id_apply _ _

private lemma cocycle_up_down
    (c : OneCocycle (toGroups (transported e A)) (mappedFamily e U)) :
    cocycleUp e A U (cocycleDown e A U c) = c := by
  apply PresheafOfGroups.FamilyRefinement.oneCocycle_ext
  exact cochain_up_down e A U c.toOneCochain

private lemma hOne_up_down (x : H1 (transported e A) (mappedFamily e U)) :
    hOneUp e A U (hOneDown e A U x) = x := by
  induction x using Quot.inductionOn with
  | _ c => exact congrArg OneCocycle.class (cocycle_up_down e A U c)

private lemma cocycle_up_mul
    (c d : OneCocycle (toGroups A) U) :
    cocycleUp e A U (PresheafOfCommGroups.OneCocycle.mul A c d) =
      PresheafOfCommGroups.OneCocycle.mul (transported e A)
        (cocycleUp e A U c) (cocycleUp e A U d) := by
  apply PresheafOfGroups.FamilyRefinement.oneCocycle_ext
  apply OneCochain.ext
  funext i j T f g
  rfl

private lemma hOne_up_mul (x y : H1 A U) :
    hOneUp e A U (x * y) = hOneUp e A U x * hOneUp e A U y := by
  induction x using Quot.inductionOn with
  | _ c =>
      induction y using Quot.inductionOn with
      | _ d => exact congrArg OneCocycle.class (cocycle_up_mul e A U c d)

/-- Cover-level commutative `H¹` is invariant under an equivalence of the indexing category.
Both directions act explicitly on Cech cocycles. -/
noncomputable def hOneMulEquiv :
    H1 A U ≃* H1 (transported e A) (mappedFamily e U) where
  toFun := hOneUp e A U
  invFun := hOneDown e A U
  left_inv := hOne_down_up e A U
  right_inv := hOne_up_down e A U
  map_mul' := hOne_up_mul e A U

/-- Apply an equivalence of categories to a refinement of indexed families. -/
def mapFamilyRefinement {J : Type*} {V : J → C}
    (r : PresheafOfGroups.FamilyRefinement V U) :
    PresheafOfGroups.FamilyRefinement
      (fun j ↦ e.functor.obj (V j)) (mappedFamily e U) where
  index := r.index
  map j := e.functor.map (r.map j)

private lemma cocycle_up_pullback {J : Type*} {V : J → C}
    (r : PresheafOfGroups.FamilyRefinement V U)
    (c : OneCocycle (toGroups A) U) :
    cocycleUp e A V (r.pullbackOneCocycle c) =
      (mapFamilyRefinement e U r).pullbackOneCocycle
        (cocycleUp e A U c) := by
  apply PresheafOfGroups.FamilyRefinement.oneCocycle_ext
  apply OneCochain.ext
  funext i j T f g
  simp only [cocycleUp, cochainUp,
    PresheafOfGroups.FamilyRefinement.pullbackOneCocycle,
    PresheafOfGroups.FamilyRefinement.pullbackOneCochain,
    mapFamilyRefinement, e.inverse.map_comp, Category.assoc]
  congr 1 <;> simp only [← Category.assoc, e.unitInv_naturality]

/-- Equivalence transport of cover-level `H¹` commutes with refinement pullback. -/
theorem hOneMulEquiv_pullback {J : Type*} {V : J → C}
    (r : PresheafOfGroups.FamilyRefinement V U) (x : H1 A U) :
    hOneMulEquiv e A V
        (PresheafOfCommGroups.pullbackHOneHom A r x) =
      PresheafOfCommGroups.pullbackHOneHom (transported e A)
        (mapFamilyRefinement e U r) (hOneMulEquiv e A U x) := by
  induction x using Quot.inductionOn with
  | _ c => exact congrArg OneCocycle.class (cocycle_up_pullback e A U r c)

end CategoryTheory.PresheafOfCommGroups.BaseEquivalence

namespace AlgebraicGeometry.Scheme.Cover

universe v u

local instance flat_respectsIso :
    MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
  MorphismProperty.RespectsIso.mk @Flat
    (fun _ _ hf ↦ by letI := hf; infer_instance)
    (fun _ _ hf ↦ by letI := hf; infer_instance)

local instance locallyOfFinitePresentation_respectsIso :
    MorphismProperty.RespectsIso
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
  MorphismProperty.RespectsIso.mk @LocallyOfFinitePresentation
    (fun _ _ hf ↦ by letI := hf; infer_instance)
    (fun _ _ hf ↦ by letI := hf; infer_instance)

local instance flat_containsIdentities :
    MorphismProperty.ContainsIdentities
      (@Flat : MorphismProperty Scheme.{u}) :=
  ⟨fun _ ↦ by infer_instance⟩

local instance locallyOfFinitePresentation_containsIdentities :
  MorphismProperty.ContainsIdentities
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
  ⟨fun _ ↦ by infer_instance⟩

local instance fppfMorphismProperty_respectsIso :
    MorphismProperty.RespectsIso
      ((@Flat : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFinitePresentation) :=
  MorphismProperty.RespectsIso.inf _ _

local instance fppfMorphismProperty_containsIdentities :
    MorphismProperty.ContainsIdentities
      ((@Flat : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFinitePresentation) :=
  MorphismProperty.ContainsIdentities.inf

local instance fppfMorphismProperty_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition
      ((@Flat : MorphismProperty Scheme.{u}) ⊓ @LocallyOfFinitePresentation) :=
  MorphismProperty.IsStableUnderComposition.inf

variable {S T : Scheme.{u}}

/-- Push an fppf cover forward along an isomorphism of bases. -/
@[implicit_reducible]
noncomputable def baseIsoPushforward (e : S ≅ T)
    (U : Cover.{v} fppfPrecoverage S) : Cover.{v} fppfPrecoverage T :=
  U.pushforwardIso e.hom

namespace Hom

variable (e : S ≅ T) {U V : Cover.{v} fppfPrecoverage S}

/-- Push a refinement of fppf covers forward along an isomorphism of bases. -/
def pushforwardIso (r : V.Hom U) :
    (baseIsoPushforward e V).Hom (baseIsoPushforward e U) := by
  change (V.pushforwardIso e.hom).Hom (U.pushforwardIso e.hom)
  exact
    { s₀ := r.s₀
      h₀ := r.h₀
      w₀ := fun i ↦ by
        change V.I₀ at i
        change r.h₀ i ≫ (U.f (r.s₀ i) ≫ e.hom) = V.f i ≫ e.hom
        rw [← Category.assoc, r.w₀] }

/-- Pushing a cover across a base isomorphism and back refines the original cover by identity
maps on all components. -/
def pushforwardIsoInvTo (U : Cover.{v} fppfPrecoverage S) :
    (baseIsoPushforward e.symm (baseIsoPushforward e U)).Hom U := by
  change ((U.pushforwardIso e.hom).pushforwardIso e.inv).Hom U
  exact
    { s₀ := fun i ↦ i
      h₀ := fun _ ↦ 𝟙 _
      w₀ := fun i ↦ by
        change U.I₀ at i
        change 𝟙 _ ≫ U.f i = (U.f i ≫ e.hom) ≫ e.inv
        simp }

/-- The same double-pushforward refinement, starting from the target of the isomorphism. -/
def pushforwardIsoSymmTo (U : Cover.{v} fppfPrecoverage T) :
    (baseIsoPushforward e (baseIsoPushforward e.symm U)).Hom U := by
  change ((U.pushforwardIso e.inv).pushforwardIso e.hom).Hom U
  exact
    { s₀ := fun i ↦ i
      h₀ := fun _ ↦ 𝟙 _
      w₀ := fun i ↦ by
        change U.I₀ at i
        change 𝟙 _ ≫ U.f i = (U.f i ≫ e.inv) ≫ e.hom
        simp }

end Hom

end AlgebraicGeometry.Scheme.Cover

namespace AlgebraicGeometry.Scheme.FppfHOne

universe w v u

open CategoryTheory.PresheafOfCommGroups
open CategoryTheory.PresheafOfCommGroups.BaseEquivalence

variable {S T : Scheme.{u}} (e : S ≅ T)
variable (A : (Over S)ᵒᵖ ⥤ CommGrpCat.{w})

private abbrev transported : (Over T)ᵒᵖ ⥤ CommGrpCat.{w} :=
  (Over.map e.inv).op ⋙ A

/-- On one actual fppf cover, transport along a base isomorphism is the explicit equivalence
of Cech `H¹` classes induced by `Over.mapIso`. -/
noncomputable def pushforwardCoverMulEquiv
    (U : Cover.{v} fppfPrecoverage S) :
    H1 A U.overFamily ≃*
      H1 (transported e A) (Cover.baseIsoPushforward e U).overFamily :=
  by
    change H1 A U.overFamily ≃*
      H1 ((Over.map e.inv).op ⋙ A)
        (fun i ↦ (Over.map e.hom).obj (U.overFamily i))
    exact hOneMulEquiv (Over.mapIso e) A U.overFamily

private lemma pushforwardCoverMulEquiv_pullback
    {U V : Cover.{v} fppfPrecoverage S} (r : V.Hom U)
    (x : H1 A U.overFamily) :
    pushforwardCoverMulEquiv e A V
        (Cover.Hom.pullbackCommHOneHom A r x) =
      Cover.Hom.pullbackCommHOneHom (transported e A)
        (Cover.Hom.pushforwardIso e r)
        (pushforwardCoverMulEquiv e A U x) := by
  exact hOneMulEquiv_pullback (Over.mapIso e) A U.overFamily
    (Cover.Hom.toOverFamilyRefinement r) x

/-- Transport a global fppf `H¹` class along an isomorphism of base schemes.  A representative
on an fppf cover is sent to the explicitly transported cocycle on the pushed-forward cover. -/
noncomputable def baseIsoMap :
    Scheme.FppfHOne.{w, v, u} S (toGroups A) →
      Scheme.FppfHOne.{w, v, u} T (toGroups (transported e A)) :=
  FppfHOne.lift
    (fun U x ↦ FppfHOne.mk (Cover.baseIsoPushforward e U)
      (pushforwardCoverMulEquiv e A U x))
    (by
      intro U V r x
      change FppfHOne.mk (Cover.baseIsoPushforward e V)
          (pushforwardCoverMulEquiv e A V
            (Cover.Hom.pullbackCommHOneHom A r x)) =
        FppfHOne.mk (Cover.baseIsoPushforward e U)
          (pushforwardCoverMulEquiv e A U x)
      rw [pushforwardCoverMulEquiv_pullback]
      exact FppfHOne.class_pullback
        (Cover.baseIsoPushforward e U) (Cover.baseIsoPushforward e V)
        (Cover.Hom.pushforwardIso e r)
        (pushforwardCoverMulEquiv e A U x))

@[simp]
theorem baseIsoMap_mk (U : Cover.{v} fppfPrecoverage S)
    (x : H1 A U.overFamily) :
    baseIsoMap e A (FppfHOne.mk U x) =
      FppfHOne.mk (Cover.baseIsoPushforward e U)
        (pushforwardCoverMulEquiv e A U x) :=
  rfl

private lemma baseIsoMap_mul
    (x y : Scheme.FppfHOne.{w, v, u} S (toGroups A)) :
    baseIsoMap e A (x * y) = baseIsoMap e A x * baseIsoMap e A y := by
  induction x using Quot.inductionOn with
  | _ a =>
      rcases a with ⟨U, x⟩
      induction y using Quot.inductionOn with
      | _ b =>
          rcases b with ⟨V, y⟩
          let Q : Cover.{v} fppfPrecoverage S := U.inter V
          let pU : Q.Hom U := Cover.interFst U V
          let pV : Q.Hom V := Cover.interSnd U V
          change baseIsoMap e A (FppfHOne.mk U x * FppfHOne.mk V y) =
            baseIsoMap e A (FppfHOne.mk U x) *
              baseIsoMap e A (FppfHOne.mk V y)
          rw [mk_mul_mk_eq_mk_of_commonRefinement A U V Q pU pV,
            baseIsoMap_mk, baseIsoMap_mk, baseIsoMap_mk,
            mk_mul_mk_eq_mk_of_commonRefinement (transported e A)
              (Cover.baseIsoPushforward e U) (Cover.baseIsoPushforward e V)
              (Cover.baseIsoPushforward e Q)
              (Cover.Hom.pushforwardIso e pU)
              (Cover.Hom.pushforwardIso e pV)]
          apply congrArg (FppfHOne.mk (Cover.baseIsoPushforward e Q))
          rw [_root_.map_mul, pushforwardCoverMulEquiv_pullback,
            pushforwardCoverMulEquiv_pullback]

/-- The global base-isomorphism transport is a homomorphism for the common-refinement group law. -/
noncomputable def baseIsoMapHom :
    Scheme.FppfHOne.{w, v, u} S (toGroups A) →*
      Scheme.FppfHOne.{w, v, u} T (toGroups (transported e A)) where
  toFun := baseIsoMap e A
  map_one' := by
    change baseIsoMap e A (FppfHOne.mk (FppfHOne.identityCover S) 1) = 1
    rw [baseIsoMap_mk, map_one, FppfHOne.mk_one]
  map_mul' := baseIsoMap_mul e A

private noncomputable def inverseCoverClass
    (U : Cover.{v} fppfPrecoverage T)
    (x : H1 (transported e A) U.overFamily) :
    H1 A (Cover.baseIsoPushforward e.symm U).overFamily :=
  (pushforwardCoverMulEquiv e A (Cover.baseIsoPushforward e.symm U)).symm
    (Cover.Hom.pullbackCommHOneHom (transported e A)
      (Cover.Hom.pushforwardIsoSymmTo e U) x)

private lemma inverseCoverClass_pullback
    {U V : Cover.{v} fppfPrecoverage T} (r : V.Hom U)
    (x : H1 (transported e A) U.overFamily) :
    inverseCoverClass e A V
        (Cover.Hom.pullbackCommHOneHom (transported e A) r x) =
      Cover.Hom.pullbackCommHOneHom A (Cover.Hom.pushforwardIso e.symm r)
        (inverseCoverClass e A U x) := by
  apply (pushforwardCoverMulEquiv e A
    (Cover.baseIsoPushforward e.symm V)).injective
  unfold inverseCoverClass
  rw [MulEquiv.apply_symm_apply, pushforwardCoverMulEquiv_pullback,
    MulEquiv.apply_symm_apply]
  change Cover.Hom.pullbackHOne (toGroups (transported e A))
        (Cover.Hom.pushforwardIsoSymmTo e V)
        (Cover.Hom.pullbackHOne (toGroups (transported e A)) r x) =
      Cover.Hom.pullbackHOne (toGroups (transported e A))
        (Cover.Hom.pushforwardIso e
          (Cover.Hom.pushforwardIso e.symm r))
        (Cover.Hom.pullbackHOne (toGroups (transported e A))
          (Cover.Hom.pushforwardIsoSymmTo e U) x)
  rw [← Cover.Hom.pullbackHOne_comp, ← Cover.Hom.pullbackHOne_comp]
  exact Cover.Hom.pullbackHOne_eq (toGroups (transported e A)) _ _ x

/-- Explicit inverse candidate for global base-isomorphism transport.  It pushes a cover back,
pulls its class to the double-pushed cover, and uses the inverse cover-level cocycle transport. -/
noncomputable def baseIsoInverse :
    Scheme.FppfHOne.{w, v, u} T (toGroups (transported e A)) →
      Scheme.FppfHOne.{w, v, u} S (toGroups A) :=
  FppfHOne.lift
    (fun U x ↦ FppfHOne.mk (Cover.baseIsoPushforward e.symm U)
      (inverseCoverClass e A U x))
    (by
      intro U V r x
      change FppfHOne.mk (Cover.baseIsoPushforward e.symm V)
          (inverseCoverClass e A V
            (Cover.Hom.pullbackCommHOneHom (transported e A) r x)) =
        FppfHOne.mk (Cover.baseIsoPushforward e.symm U)
          (inverseCoverClass e A U x)
      rw [inverseCoverClass_pullback]
      exact FppfHOne.class_pullback
        (Cover.baseIsoPushforward e.symm U) (Cover.baseIsoPushforward e.symm V)
        (Cover.Hom.pushforwardIso e.symm r) (inverseCoverClass e A U x))

@[simp]
private theorem baseIsoInverse_mk (U : Cover.{v} fppfPrecoverage T)
    (x : H1 (transported e A) U.overFamily) :
    baseIsoInverse e A (FppfHOne.mk U x) =
      FppfHOne.mk (Cover.baseIsoPushforward e.symm U)
        (inverseCoverClass e A U x) :=
  rfl

private lemma inverseCoverClass_pushforward
    (U : Cover.{v} fppfPrecoverage S) (x : H1 A U.overFamily) :
    inverseCoverClass e A (Cover.baseIsoPushforward e U)
        (pushforwardCoverMulEquiv e A U x) =
      Cover.Hom.pullbackCommHOneHom A
        (Cover.Hom.pushforwardIsoInvTo e U) x := by
  apply (pushforwardCoverMulEquiv e A
    (Cover.baseIsoPushforward e.symm (Cover.baseIsoPushforward e U))).injective
  unfold inverseCoverClass
  rw [MulEquiv.apply_symm_apply, pushforwardCoverMulEquiv_pullback]
  change Cover.Hom.pullbackHOne (toGroups (transported e A))
        (Cover.Hom.pushforwardIsoSymmTo e (Cover.baseIsoPushforward e U))
        (pushforwardCoverMulEquiv e A U x) =
      Cover.Hom.pullbackHOne (toGroups (transported e A))
        (Cover.Hom.pushforwardIso e (Cover.Hom.pushforwardIsoInvTo e U))
        (pushforwardCoverMulEquiv e A U x)
  exact Cover.Hom.pullbackHOne_eq (toGroups (transported e A)) _ _ _

private lemma baseIsoInverse_baseIsoMap
    (x : Scheme.FppfHOne.{w, v, u} S (toGroups A)) :
    baseIsoInverse e A (baseIsoMap e A x) = x := by
  induction x using Quot.inductionOn with
  | _ a =>
      rcases a with ⟨U, x⟩
      change baseIsoInverse e A
          (FppfHOne.mk (Cover.baseIsoPushforward e U)
            (pushforwardCoverMulEquiv e A U x)) = FppfHOne.mk U x
      rw [baseIsoInverse_mk, inverseCoverClass_pushforward]
      exact FppfHOne.class_pullback U
        (Cover.baseIsoPushforward e.symm (Cover.baseIsoPushforward e U))
        (Cover.Hom.pushforwardIsoInvTo e U) x

private lemma baseIsoMap_baseIsoInverse
    (x : Scheme.FppfHOne.{w, v, u} T (toGroups (transported e A))) :
    baseIsoMap e A (baseIsoInverse e A x) = x := by
  induction x using Quot.inductionOn with
  | _ a =>
      rcases a with ⟨U, x⟩
      change baseIsoMap e A (baseIsoInverse e A (FppfHOne.mk U x)) =
        FppfHOne.mk U x
      rw [baseIsoInverse_mk, baseIsoMap_mk]
      unfold inverseCoverClass
      rw [MulEquiv.apply_symm_apply]
      exact FppfHOne.class_pullback U
        (Cover.baseIsoPushforward e (Cover.baseIsoPushforward e.symm U))
        (Cover.Hom.pushforwardIsoSymmTo e U) x

/-- Global fppf `H¹` with commutative coefficients is invariant under an isomorphism of base
schemes.  The equivalence is checked on Cech cocycles, fppf covers, refinements, and common
refinements. -/
noncomputable def baseIsoMulEquiv :
    Scheme.FppfHOne.{w, v, u} S (toGroups A) ≃*
      Scheme.FppfHOne.{w, v, u} T (toGroups (transported e A)) where
  toFun := baseIsoMap e A
  invFun := baseIsoInverse e A
  left_inv := baseIsoInverse_baseIsoMap e A
  right_inv := baseIsoMap_baseIsoInverse e A
  map_mul' := baseIsoMap_mul e A

end AlgebraicGeometry.Scheme.FppfHOne

namespace AlgebraicGeometry.CommGroupScheme

universe v u

variable {S T : Scheme.{u}}

/-- Isomorphic commutative group schemes have equivalent represented global fppf `H¹`. -/
noncomputable def fppfHOneMulEquivOfIso {G H : CommGroupScheme S} (i : G ≅ H) :
    G.FppfHOne.{v} ≃* H.FppfHOne.{v} where
  toFun := fppfHOneMap i.hom
  invFun := fppfHOneMap i.inv
  left_inv x := by
    rw [← MonoidHom.comp_apply, ← fppfHOneMap_comp, i.hom_inv_id,
      fppfHOneMap_id, MonoidHom.id_apply]
  right_inv x := by
    rw [← MonoidHom.comp_apply, ← fppfHOneMap_comp, i.inv_hom_id,
      fppfHOneMap_id, MonoidHom.id_apply]
  map_mul' := map_mul (fppfHOneMap i.hom)

/-- Represented fppf `H¹` of a commutative group scheme is unchanged after transporting the
base across an isomorphism.  The target is the canonical pullback group scheme. -/
noncomputable def fppfHOneMulEquivBaseIso (e : S ≅ T) (G : CommGroupScheme S) :
    G.FppfHOne.{v} ≃*
      CommGroupScheme.FppfHOne.{v}
        ((Over.pullback e.inv).mapCommGrp.obj G) :=
  (Scheme.FppfHOne.baseIsoMulEquiv e G.commPointPresheaf).trans
    (Scheme.FppfHOne.mulEquivOfIso (baseChangeCommPointPresheafIso e.inv G)).symm

end AlgebraicGeometry.CommGroupScheme

namespace AlgebraicGeometry.CommGroupScheme

universe v u

open CategoryTheory.Limits

variable {R : Type u} [CommRing R]

/-- Pulling a group scheme first to the basic open and then across
`basicOpenIsoSpecAway` gives the same commutative group scheme as pulling it directly along the
localization morphism. -/
noncomputable def basicOpenBaseChangeIso (f : R)
    (G : CommGroupScheme (_root_.AlgebraicGeometry.Spec (.of R))) :
    (Over.pullback (basicOpenIsoSpecAway (R := .of R) f).inv).mapCommGrp.obj
        ((Over.pullback (Scheme.Opens.ι (X := _root_.AlgebraicGeometry.Spec (.of R))
          (PrimeSpectrum.basicOpen f))).mapCommGrp.obj G) ≅
      (Over.pullback (_root_.AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap R (Localization.Away f))))).mapCommGrp.obj G := by
  let U : (_root_.AlgebraicGeometry.Spec (.of R)).Opens := PrimeSpectrum.basicOpen f
  let e : U.toScheme ≅ _root_.AlgebraicGeometry.Spec (.of (Localization.Away f)) :=
    basicOpenIsoSpecAway (R := .of R) f
  let j : _root_.AlgebraicGeometry.Spec (.of (Localization.Away f)) ⟶
      _root_.AlgebraicGeometry.Spec (.of R) :=
    _root_.AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap R (Localization.Away f)))
  have hcomp : e.inv ≫ U.ι = j := by
    rw [← basicOpenIsoSpecAway_hom_SpecMap (R := .of R) f]
    simp [e, j]
  let compIso :
      (Over.pullback (e.inv ≫ U.ι)).mapCommGrp.obj G ≅
        (Over.pullback e.inv).mapCommGrp.obj
          ((Over.pullback U.ι).mapCommGrp.obj G) :=
    (Functor.mapCommGrpNatIso (Over.pullbackComp e.inv U.ι)).app G ≪≫
      Functor.mapCommGrpCompIso.app G
  exact compIso.symm ≪≫
    eqToIso (congrArg (fun q ↦ (Over.pullback q).mapCommGrp.obj G) hcomp)

/-- Named `basicOpenIsoSpecAway` consumer: represented fppf `H¹` on a basic-open base change
is equivalent to represented fppf `H¹` of the direct localization base change. -/
noncomputable def basicOpenFppfHOneMulEquivSpecAway (f : R)
    (G : CommGroupScheme (_root_.AlgebraicGeometry.Spec (.of R))) :
    CommGroupScheme.FppfHOne.{v}
        ((Over.pullback (Scheme.Opens.ι (X := _root_.AlgebraicGeometry.Spec (.of R))
          (PrimeSpectrum.basicOpen f))).mapCommGrp.obj G) ≃*
      CommGroupScheme.FppfHOne.{v}
        ((Over.pullback (_root_.AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap R (Localization.Away f))))).mapCommGrp.obj G) :=
  (fppfHOneMulEquivBaseIso (basicOpenIsoSpecAway (R := .of R) f)
      ((Over.pullback (Scheme.Opens.ι (X := _root_.AlgebraicGeometry.Spec (.of R))
        (PrimeSpectrum.basicOpen f))).mapCommGrp.obj G)).trans
    (fppfHOneMulEquivOfIso (basicOpenBaseChangeIso f G))

end AlgebraicGeometry.CommGroupScheme

namespace AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme

universe v u

open CommGroupScheme

section ConstantFlat

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]

/-- After identifying the basic open with the localization spectrum, the checked supported-`H¹`
comparison for the constant-flat bad-level model becomes a comparison of the two direct
localization base changes. -/
noncomputable def constantFlatFppfHOneSpecAwayMulEquiv (level : R) :
    CommGroupScheme.FppfHOne.{v}
        ((Over.pullback (_root_.AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap R (Localization.Away level))))).mapCommGrp.obj
            (constantFlat R G level).obj) ≃*
      CommGroupScheme.FppfHOne.{v}
        ((Over.pullback (_root_.AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap R (Localization.Away level))))).mapCommGrp.obj
            (FiniteFlatCommGroupScheme.constantScheme R G).obj) :=
  (basicOpenFppfHOneMulEquivSpecAway level (constantFlat R G level).obj).symm.trans
    ((constantFlatFppfHOneAwayMulEquiv level).trans
      (basicOpenFppfHOneMulEquivSpecAway level
        (FiniteFlatCommGroupScheme.constantScheme R G).obj))

end ConstantFlat

section MultiplicativeFlat

variable {coeffPrime level : ℕ} [NeZero coeffPrime]

/-- The multiplicative-flat supported-`H¹` comparison, transported from the basic open to the
direct localization spectrum. -/
noncomputable def muFlatFppfHOneSpecAwayMulEquiv
    (datum : MuFlatDatum coeffPrime level) :
    CommGroupScheme.FppfHOne.{v}
        ((Over.pullback (_root_.AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap ℤ
            (Localization.Away (level : ℤ)))))).mapCommGrp.obj
              (muFlat coeffPrime level datum).obj) ≃*
      CommGroupScheme.FppfHOne.{v}
        ((Over.pullback (_root_.AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap ℤ
            (Localization.Away (level : ℤ)))))).mapCommGrp.obj
              (FiniteFlatCommGroupScheme.muScheme ℤ coeffPrime).obj) :=
  (basicOpenFppfHOneMulEquivSpecAway (level : ℤ)
      (muFlat coeffPrime level datum).obj).symm.trans
    ((muFlatFppfHOneAwayMulEquiv datum).trans
      (basicOpenFppfHOneMulEquivSpecAway (level : ℤ)
        (FiniteFlatCommGroupScheme.muScheme ℤ coeffPrime).obj))

end MultiplicativeFlat

end AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits

/-!
# Finite flat commutative group schemes

This file packages commutative group objects over a scheme whose structure morphism is finite
and flat.  The ambient group-scheme category is mathlib's category of internal commutative group
objects in `Over S`; the finite-flat category is its full subcategory.  Consequently morphisms
carry all compatibility with multiplication, identity, and inverse without repeating those laws.

The rank is deliberately a function on the base.  A finite flat morphism need not have a single
global rank on a disconnected base.  `HasConstantOrder G n` records the additional assertion
needed to speak of one order `n`.

The scheme-theoretic kernel is the pullback of a homomorphism along the identity section.  It is
constructed first as a pullback of internal groups, and commutativity follows from its monic map
to the commutative source.  Packaging it back into the finite-flat category still takes explicit
finiteness and flatness hypotheses on its structure map.  In particular, flatness of kernels is
an arithmetic-base theorem rather than a formal consequence of the source and target being
finite flat.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj

namespace AlgebraicGeometry

universe u

/-- A commutative group scheme over `S`, expressed as an internal commutative group object in
the slice category of schemes over `S`. -/
abbrev CommGroupScheme (S : Scheme.{u}) := CommGrp (Over S)

/-- The object property saying that the structure morphism of a commutative group scheme is
finite and flat. -/
def finiteFlatCommGroupSchemeProperty (S : Scheme.{u}) :
    ObjectProperty (CommGroupScheme S) :=
  fun G => IsFinite G.X.hom ∧ Flat G.X.hom

/-- Finite flat commutative group schemes over `S` form the full subcategory of commutative
group schemes whose structure morphism is finite and flat. -/
abbrev FiniteFlatCommGroupScheme (S : Scheme.{u}) :=
  (finiteFlatCommGroupSchemeProperty S).FullSubcategory

namespace FiniteFlatCommGroupScheme

variable {S T U : Scheme.{u}}

/-- The underlying commutative group scheme. -/
abbrev toCommGroupScheme (G : FiniteFlatCommGroupScheme S) : CommGroupScheme S := G.obj

/-- The underlying scheme. -/
abbrev scheme (G : FiniteFlatCommGroupScheme S) : Scheme.{u} := G.obj.X.left

/-- The finite flat structure morphism. -/
abbrev structureMap (G : FiniteFlatCommGroupScheme S) : G.scheme ⟶ S := G.obj.X.hom

instance (G : FiniteFlatCommGroupScheme S) : IsFinite G.structureMap := G.property.1

instance (G : FiniteFlatCommGroupScheme S) : Flat G.structureMap := G.property.2

/-- The underlying morphism of schemes of a morphism of finite flat commutative group schemes. -/
abbrev hom {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H) : G.scheme ⟶ H.scheme :=
  f.hom.hom.hom.hom.left

@[simp]
theorem hom_id (G : FiniteFlatCommGroupScheme S) : hom (𝟙 G) = 𝟙 G.scheme := rfl

@[simp]
theorem hom_comp {G H K : FiniteFlatCommGroupScheme S} (f : G ⟶ H) (g : H ⟶ K) :
    hom (f ≫ g) = hom f ≫ hom g := rfl

@[reassoc (attr := simp)]
theorem hom_comp_structureMap {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H) :
    hom f ≫ H.structureMap = G.structureMap :=
  f.hom.hom.hom.hom.w

/-- The group of `X`-valued points of `G`, where `X` is any scheme over the same base.

Because `G` is an internal commutative group object, this hom-set carries its canonical
commutative group structure. -/
abbrev Point (G : FiniteFlatCommGroupScheme S) (X : Over S) := X ⟶ G.obj.X

/-- A homomorphism of finite-flat commutative group schemes acts on points by postcomposition. -/
def mapPoint {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H) (X : Over S) :
    G.Point X →* H.Point X :=
  IsMonHom.monoidHom f.hom.hom.hom.hom X

@[simp]
theorem mapPoint_apply {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H)
    (X : Over S) (x : G.Point X) :
    mapPoint f X x = x ≫ f.hom.hom.hom.hom :=
  rfl

@[simp]
theorem mapPoint_id (G : FiniteFlatCommGroupScheme S) (X : Over S) :
    mapPoint (CategoryStruct.id G) X = MonoidHom.id (G.Point X) := by
  ext x
  simp

@[simp]
theorem mapPoint_comp {G H K : FiniteFlatCommGroupScheme S} (f : G ⟶ H) (g : H ⟶ K)
    (X : Over S) :
    mapPoint (f ≫ g) X = (mapPoint g X).comp (mapPoint f X) := by
  ext x
  simp

/-- An isomorphism of finite-flat commutative group schemes induces a multiplicative equivalence
on points of every test scheme. -/
def pointMulEquivOfIso {G H : FiniteFlatCommGroupScheme S} (e : G ≅ H) (X : Over S) :
    G.Point X ≃* H.Point X where
  toFun := mapPoint e.hom X
  invFun := mapPoint e.inv X
  left_inv x := by
    rw [← MonoidHom.comp_apply, ← mapPoint_comp, e.hom_inv_id, mapPoint_id]
    rfl
  right_inv x := by
    rw [← MonoidHom.comp_apply, ← mapPoint_comp, e.inv_hom_id, mapPoint_id]
    rfl
  map_mul' x y := map_mul (mapPoint e.hom X) x y

/-- Base change of finite flat commutative group schemes.  This is a functor because pullback is a
finite-product-preserving functor on slice categories, hence maps internal commutative groups. -/
def baseChange (f : T ⟶ S) :
    FiniteFlatCommGroupScheme S ⥤ FiniteFlatCommGroupScheme T where
  obj G :=
    { obj := (Over.pullback f).mapCommGrp.obj G.obj
      property := by
        change IsFinite (pullback.snd G.structureMap f) ∧ Flat (pullback.snd G.structureMap f)
        exact ⟨inferInstance, inferInstance⟩ }
  map g := ObjectProperty.homMk ((Over.pullback f).mapCommGrp.map g.hom)

@[simp]
theorem baseChange_scheme (f : T ⟶ S) (G : FiniteFlatCommGroupScheme S) :
    ((baseChange f).obj G).scheme = pullback G.structureMap f := rfl

@[simp]
theorem baseChange_structureMap (f : T ⟶ S) (G : FiniteFlatCommGroupScheme S) :
    ((baseChange f).obj G).structureMap = pullback.snd G.structureMap f := rfl

/-- Projection from a base-changed finite-flat group scheme to its original scheme. -/
def baseChangeProjection (f : T ⟶ S) (G : FiniteFlatCommGroupScheme S) :
    ((baseChange f).obj G).scheme ⟶ G.scheme :=
  pullback.fst G.structureMap f

@[reassoc]
theorem baseChangeProjection_condition (f : T ⟶ S)
    (G : FiniteFlatCommGroupScheme S) :
    baseChangeProjection f G ≫ G.structureMap =
      ((baseChange f).obj G).structureMap ≫ f := by
  exact pullback.condition

/-- Two maps into a base-changed scheme agree when they agree after both projections. -/
theorem baseChangeScheme_hom_ext (f : T ⟶ S) (G : FiniteFlatCommGroupScheme S)
    {X : Scheme.{u}} {a b : X ⟶ ((baseChange f).obj G).scheme}
    (hprojection : a ≫ baseChangeProjection f G = b ≫ baseChangeProjection f G)
    (hbase : a ≫ ((baseChange f).obj G).structureMap =
      b ≫ ((baseChange f).obj G).structureMap) : a = b := by
  apply pullback.hom_ext
  · exact hprojection
  · exact hbase

/-- The universal lift into a base-changed scheme, with its source type kept opaque. -/
def baseChangeLift (f : T ⟶ S) (G : FiniteFlatCommGroupScheme S)
    {X : Scheme.{u}} (a : X ⟶ G.scheme) (b : X ⟶ T)
    (h : a ≫ G.structureMap = b ≫ f) : X ⟶ ((baseChange f).obj G).scheme :=
  pullback.lift a b h

@[reassoc]
theorem baseChangeLift_projection (f : T ⟶ S)
    (G : FiniteFlatCommGroupScheme S) {X : Scheme.{u}}
    (a : X ⟶ G.scheme) (b : X ⟶ T) (h : a ≫ G.structureMap = b ≫ f) :
    baseChangeLift f G a b h ≫ baseChangeProjection f G = a := by
  unfold baseChangeLift baseChangeProjection
  exact pullback.lift_fst _ _ _

@[reassoc]
theorem baseChangeLift_structureMap (f : T ⟶ S)
    (G : FiniteFlatCommGroupScheme S) {X : Scheme.{u}}
    (a : X ⟶ G.scheme) (b : X ⟶ T) (h : a ≫ G.structureMap = b ≫ f) :
    baseChangeLift f G a b h ≫ ((baseChange f).obj G).structureMap = b := by
  unfold baseChangeLift
  exact pullback.lift_snd _ _ _

/-- Base change of a group-scheme homomorphism commutes with the projection to the original
source and target. -/
@[reassoc]
theorem baseChange_hom_projection (t : T ⟶ S)
    {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H) :
    hom ((baseChange t).map f) ≫ baseChangeProjection t H =
      baseChangeProjection t G ≫ hom f := by
  unfold baseChangeProjection
  change ((Over.pullback t).map f.hom.hom.hom.hom).left ≫
      pullback.fst H.structureMap t = _
  have hmap := Over.pullback_map_left t G.obj.X (k := f.hom.hom.hom.hom)
  have hmcomp := congrArg (fun q ↦ q ≫ pullback.fst H.structureMap t) hmap
  rw [pullback.lift_fst] at hmcomp
  exact hmcomp

/-- Base change of a group-scheme homomorphism remains a morphism over the new base. -/
@[reassoc]
theorem baseChange_hom_structureMap (t : T ⟶ S)
    {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H) :
    hom ((baseChange t).map f) ≫ ((baseChange t).obj H).structureMap =
      ((baseChange t).obj G).structureMap := by
  exact hom_comp_structureMap ((baseChange t).map f)

/-- The identity section of a base-changed group scheme projects to the original identity
section. -/
@[reassoc]
theorem baseChange_one_projection (t : T ⟶ S) (H : FiniteFlatCommGroupScheme S) :
    η[((baseChange t).obj H).obj.X].left ≫ baseChangeProjection t H =
      t ≫ η[H.obj.X].left := by
  unfold baseChangeProjection
  change Over.Hom.left (η[((Over.pullback t).mapCommGrp.obj H.obj).X]) ≫
      pullback.fst H.structureMap t = t ≫ η[H.obj.X].left
  change Over.Hom.left (Functor.LaxMonoidal.ε (Over.pullback t) ≫
      (Over.pullback t).map η[H.obj.X]) ≫ pullback.fst H.structureMap t = _
  rw [Functor.Monoidal.ε_of_cartesianMonoidalCategory]
  simp only [Over.tensorUnit_left, Over.pullback_obj_left,
    Over.preservesTerminalIso_pullback, Over.tensorUnit_hom, Over.comp_left,
    Over.isoMk_inv_left, asIso_inv, Over.pullback_map_left, Category.assoc,
    IsIso.inv_comp_eq]
  rw [pullback.lift_fst]
  have hbase : pullback.fst (𝟙 S) t = pullback.snd (𝟙 S) t ≫ t := by
    simpa only [Category.comp_id] using (pullback.condition :
      pullback.fst (𝟙 S) t ≫ 𝟙 S = pullback.snd (𝟙 S) t ≫ t)
  rw [hbase, Category.assoc]

/-- The identity section of a base-changed group scheme is a section over the new base. -/
@[reassoc]
theorem baseChange_one_structureMap (t : T ⟶ S) (H : FiniteFlatCommGroupScheme S) :
    η[((baseChange t).obj H).obj.X].left ≫ ((baseChange t).obj H).structureMap = 𝟙 T := by
  exact (η[((baseChange t).obj H).obj.X]).w

/-- The square underlying a base-changed group-scheme homomorphism is cartesian. -/
theorem baseChange_hom_isPullback (t : T ⟶ S)
    {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H) :
    IsPullback (baseChangeProjection t G) (hom ((baseChange t).map f))
      (hom f) (baseChangeProjection t H) := by
  refine ⟨⟨(baseChange_hom_projection t f).symm⟩, ⟨?_⟩⟩
  let lift (s : PullbackCone (hom f) (baseChangeProjection t H)) :
      s.pt ⟶ ((baseChange t).obj G).scheme :=
    baseChangeLift t G s.fst (s.snd ≫ ((baseChange t).obj H).structureMap) (by
      calc
        s.fst ≫ G.structureMap = s.fst ≫ hom f ≫ H.structureMap := by
          rw [hom_comp_structureMap]
        _ = s.snd ≫ baseChangeProjection t H ≫ H.structureMap :=
          s.condition_assoc H.structureMap
        _ = s.snd ≫ ((baseChange t).obj H).structureMap ≫ t := by
          rw [baseChangeProjection_condition])
  refine PullbackCone.IsLimit.mk _ lift ?_ ?_ ?_
  · intro s
    simpa only [lift] using
      (baseChangeLift_projection t G s.fst
        (s.snd ≫ ((baseChange t).obj H).structureMap) _)
  · intro s
    apply baseChangeScheme_hom_ext t H
    · calc
        (lift s ≫ hom ((baseChange t).map f)) ≫ baseChangeProjection t H =
            lift s ≫ (baseChangeProjection t G ≫ hom f) := by
          rw [Category.assoc, baseChange_hom_projection]
        _ = s.fst ≫ hom f := by
          rw [← Category.assoc]
          have hlift : lift s ≫ baseChangeProjection t G = s.fst := by
            simpa only [lift] using
              (baseChangeLift_projection t G s.fst
                (s.snd ≫ ((baseChange t).obj H).structureMap) _)
          rw [hlift]
        _ = s.snd ≫ baseChangeProjection t H := s.condition
    · calc
        (lift s ≫ hom ((baseChange t).map f)) ≫
            ((baseChange t).obj H).structureMap =
            lift s ≫ ((baseChange t).obj G).structureMap := by
          rw [Category.assoc, baseChange_hom_structureMap]
        _ = s.snd ≫ ((baseChange t).obj H).structureMap := by
          simpa only [lift] using
            (baseChangeLift_structureMap t G s.fst
              (s.snd ≫ ((baseChange t).obj H).structureMap) _)
  · intro s m hfst hsnd
    apply baseChangeScheme_hom_ext t G
    · have hlift : lift s ≫ baseChangeProjection t G = s.fst := by
        simpa only [lift] using
          (baseChangeLift_projection t G s.fst
            (s.snd ≫ ((baseChange t).obj H).structureMap) _)
      exact hfst.trans hlift.symm
    · calc
        m ≫ ((baseChange t).obj G).structureMap =
            m ≫ hom ((baseChange t).map f) ≫
              ((baseChange t).obj H).structureMap := by
          rw [baseChange_hom_structureMap]
        _ = s.snd ≫ ((baseChange t).obj H).structureMap := by
          rw [← Category.assoc, hsnd]
        _ = lift s ≫ ((baseChange t).obj G).structureMap := by
          symm
          simpa only [lift] using
            (baseChangeLift_structureMap t G s.fst
              (s.snd ≫ ((baseChange t).obj H).structureMap) _)

/-- The direct pullback kernel over a new base maps canonically to the base-changed source. -/
noncomputable def directKernelToBaseChangeSource (t : T ⟶ S)
    {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H) :
    pullback (hom f) (t ≫ η[H.obj.X].left) ⟶ ((baseChange t).obj G).scheme :=
  (baseChange_hom_isPullback t f).lift
    (pullback.fst (hom f) (t ≫ η[H.obj.X].left))
    (pullback.snd (hom f) (t ≫ η[H.obj.X].left) ≫
      η[((baseChange t).obj H).obj.X].left)
    (by
      calc
        pullback.fst (hom f) (t ≫ η[H.obj.X].left) ≫ hom f =
            pullback.snd (hom f) (t ≫ η[H.obj.X].left) ≫
              (t ≫ η[H.obj.X].left) := pullback.condition
        _ = pullback.snd (hom f) (t ≫ η[H.obj.X].left) ≫
              (η[((baseChange t).obj H).obj.X].left ≫
                baseChangeProjection t H) := by rw [baseChange_one_projection]
        _ = (pullback.snd (hom f) (t ≫ η[H.obj.X].left) ≫
              η[((baseChange t).obj H).obj.X].left) ≫
                baseChangeProjection t H := (Category.assoc _ _ _).symm)

/-- The direct kernel square remains a pullback after changing the base. -/
theorem directKernel_isPullback (t : T ⟶ S)
    {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H) :
    IsPullback (directKernelToBaseChangeSource t f)
      (pullback.snd (hom f) (t ≫ η[H.obj.X].left))
      (hom ((baseChange t).map f)) η[((baseChange t).obj H).obj.X].left := by
  let right := baseChange_hom_isPullback t f
  have outer : IsPullback
      (pullback.fst (hom f) (t ≫ η[H.obj.X].left))
      (pullback.snd (hom f) (t ≫ η[H.obj.X].left)) (hom f)
      (η[((baseChange t).obj H).obj.X].left ≫ baseChangeProjection t H) := by
    rw [baseChange_one_projection]
    exact IsPullback.of_hasPullback (hom f) (t ≫ η[H.obj.X].left)
  exact outer.of_right' right

@[reassoc]
theorem directKernelToBaseChangeSource_projection (t : T ⟶ S)
    {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H) :
    directKernelToBaseChangeSource t f ≫ baseChangeProjection t G =
      pullback.fst (hom f) (t ≫ η[H.obj.X].left) := by
  unfold directKernelToBaseChangeSource
  exact (baseChange_hom_isPullback t f).lift_fst _ _ _

@[reassoc]
theorem directKernelToBaseChangeSource_project (t : T ⟶ S)
    {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H) :
    directKernelToBaseChangeSource t f ≫ hom ((baseChange t).map f) =
      pullback.snd (hom f) (t ≫ η[H.obj.X].left) ≫
        η[((baseChange t).obj H).obj.X].left := by
  unfold directKernelToBaseChangeSource
  exact (baseChange_hom_isPullback t f).lift_snd _ _ _

@[reassoc]
theorem directKernelToBaseChangeSource_structureMap (t : T ⟶ S)
    {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H) :
    directKernelToBaseChangeSource t f ≫ ((baseChange t).obj G).structureMap =
      pullback.snd (hom f) (t ≫ η[H.obj.X].left) := by
  calc
    directKernelToBaseChangeSource t f ≫ ((baseChange t).obj G).structureMap =
        (directKernelToBaseChangeSource t f ≫ hom ((baseChange t).map f)) ≫
          ((baseChange t).obj H).structureMap := by
      rw [Category.assoc, baseChange_hom_structureMap]
    _ = (pullback.snd (hom f) (t ≫ η[H.obj.X].left) ≫
          η[((baseChange t).obj H).obj.X].left) ≫
            ((baseChange t).obj H).structureMap := by
      rw [directKernelToBaseChangeSource_project]
    _ = pullback.snd (hom f) (t ≫ η[H.obj.X].left) := by
      rw [Category.assoc, baseChange_one_structureMap, Category.comp_id]

/-- The rank of a finite flat commutative group scheme at a point of its base. -/
def orderAt (G : FiniteFlatCommGroupScheme S) : S → ℕ := G.structureMap.finrank

/-- The assertion that a finite flat commutative group scheme has one constant order on its
possibly disconnected base. -/
def HasConstantOrder (G : FiniteFlatCommGroupScheme S) (n : ℕ) : Prop :=
  G.orderAt = Function.const S n

/-- Isomorphic finite-flat commutative group schemes have the same geometric rank function. -/
theorem orderAt_eq_of_iso {G H : FiniteFlatCommGroupScheme S} (e : G ≅ H) :
    G.orderAt = H.orderAt := by
  funext s
  let es : G.scheme ≅ H.scheme :=
    { hom := hom e.hom
      inv := hom e.inv
      hom_inv_id := by rw [← hom_comp, e.hom_inv_id, hom_id]
      inv_hom_id := by rw [← hom_comp, e.inv_hom_id, hom_id] }
  letI : IsIso es.hom := es.isIso_hom
  change G.structureMap.finrank s = H.structureMap.finrank s
  rw [← Scheme.Hom.finrank_comp_left_of_isIso es.hom H.structureMap]
  change G.structureMap.finrank s = (hom e.hom ≫ H.structureMap).finrank s
  rw [hom_comp_structureMap]

theorem orderAt_baseChange (f : T ⟶ S) (G : FiniteFlatCommGroupScheme S) (t : T) :
    ((baseChange f).obj G).orderAt t = G.orderAt (f t) :=
  Scheme.Hom.finrank_pullback_snd G.structureMap f t

theorem hasConstantOrder_baseChange {G : FiniteFlatCommGroupScheme S} {n : ℕ}
    (hG : G.HasConstantOrder n) (f : T ⟶ S) :
    ((baseChange f).obj G).HasConstantOrder n := by
  funext t
  rw [orderAt_baseChange, hG]
  rfl

/-- The underlying scheme of the scheme-theoretic kernel of `f`, obtained by pulling `G` back
along the identity section of `H`. -/
abbrev kernelScheme {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H) : Scheme.{u} :=
  pullback (hom f) (η[H.obj.X].left)

/-- The canonical map from the scheme-theoretic kernel to the source group scheme. -/
abbrev kernelι {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H) :
    kernelScheme f ⟶ G.scheme :=
  pullback.fst (hom f) (η[H.obj.X].left)

/-- The structure morphism of the underlying scheme-theoretic kernel. -/
abbrev kernelStructureMap {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H) :
    kernelScheme f ⟶ S :=
  pullback.snd (hom f) (η[H.obj.X].left)

@[reassoc (attr := simp)]
theorem kernel_condition {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H) :
    kernelι f ≫ hom f = kernelStructureMap f ≫ η[H.obj.X].left :=
  pullback.condition

/-- The zero morphism from the trivial internal group to the target.  Its underlying map of
schemes is the identity section of the target group scheme. -/
noncomputable abbrev kernelZero (H : FiniteFlatCommGroupScheme S) :
    Grp.trivial (Over S) ⟶ H.obj.toGrp :=
  default

/-- The kernel constructed first in internal (not necessarily commutative) groups.  Limits of
internal groups are created by the forgetful functor, so this pullback inherits its group law
without choosing formulas for multiplication and inverse on the underlying scheme. -/
noncomputable abbrev kernelGrp {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H) :
    Grp (Over S) :=
  pullback f.hom.hom (kernelZero H)

/-- The internal group kernel is commutative.  The identity section is split mono, hence the
first pullback projection is mono.  Its underlying map remains mono because the forgetful
functor from internal groups preserves pullbacks, and commutativity can therefore be checked
after mapping to the commutative source. -/
theorem kernelGrp_isComm {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H) :
    IsCommMonObj (kernelGrp f).X := by
  let se : SplitMono (kernelZero H) := SplitMono.mk default (Subsingleton.elim _ _)
  letI : Mono (kernelZero H) := se.mono
  haveI : Mono (pullback.fst f.hom.hom (kernelZero H)) := inferInstance
  haveI : Mono (pullback.fst f.hom.hom (kernelZero H)).hom.hom := inferInstanceAs
    (Mono ((Grp.forget (Over S)).map (pullback.fst f.hom.hom (kernelZero H))))
  constructor
  apply (cancel_mono (pullback.fst f.hom.hom (kernelZero H)).hom.hom).1
  rw [Category.assoc, IsMonHom.mul_hom]
  rw [← Category.assoc, ← BraidedCategory.braiding_naturality, Category.assoc,
    IsCommMonObj.mul_comm]

/-- The commutative group scheme underlying the scheme-theoretic kernel. -/
noncomputable def kernelCommGroupScheme {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H) :
    CommGroupScheme S :=
  letI : IsCommMonObj (kernelGrp f).X := kernelGrp_isComm f
  { X := (kernelGrp f).X }

/-- The kernel inclusion before imposing the finite-flat object property. -/
noncomputable def kernelCommGroupSchemeInclusion
    {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H) :
    kernelCommGroupScheme f ⟶ G.obj := by
  apply InducedCategory.homMk
  exact pullback.fst f.hom.hom (kernelZero H)

/-- After forgetting first the group structure and then the map to the base, the internal-group
kernel square is the scheme-theoretic pullback square. -/
theorem kernelGrp_isPullback {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H) :
    IsPullback
      (pullback.fst f.hom.hom (kernelZero H)).hom.hom.left
      (pullback.snd f.hom.hom (kernelZero H)).hom.hom.left
      (hom f) (η[H.obj.X].left) := by
  change IsPullback
    ((Over.forget S).map
      ((Grp.forget (Over S)).map (pullback.fst f.hom.hom (kernelZero H))))
    ((Over.forget S).map
      ((Grp.forget (Over S)).map (pullback.snd f.hom.hom (kernelZero H))))
    ((Over.forget S).map ((Grp.forget (Over S)).map f.hom.hom))
    ((Over.forget S).map ((Grp.forget (Over S)).map (kernelZero H)))
  exact (((IsPullback.of_hasPullback f.hom.hom (kernelZero H)).map
    (Grp.forget (Over S))).map (Over.forget S))

/-- The canonical identification of the inherited internal-group kernel with the explicit
scheme-theoretic pullback used by `kernelScheme`. -/
noncomputable def kernelGrpSchemeIso {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H) :
    (kernelGrp f).X.left ≅ kernelScheme f :=
  (kernelGrp_isPullback f).isoPullback

@[reassoc]
theorem kernelGrpSchemeIso_hom_structureMap
    {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H) :
    (kernelGrpSchemeIso f).hom ≫ kernelStructureMap f = (kernelGrp f).X.hom := by
  have hs : (kernelGrpSchemeIso f).hom ≫ kernelStructureMap f =
      (pullback.snd f.hom.hom (kernelZero H)).hom.hom.left := by
    change (kernelGrp_isPullback f).isoPullback.hom ≫
      pullback.snd (hom f) (η[H.obj.X].left) =
        (pullback.snd f.hom.hom (kernelZero H)).hom.hom.left
    exact IsPullback.isoPullback_hom_snd (kernelGrp_isPullback f)
  rw [hs]
  exact Over.w (pullback.snd f.hom.hom (kernelZero H)).hom.hom

@[reassoc]
theorem kernelGrpSchemeIso_hom_kernelι
    {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H) :
    (kernelGrpSchemeIso f).hom ≫ kernelι f =
      (kernelCommGroupSchemeInclusion f).hom.hom.hom.left := by
  change (kernelGrp_isPullback f).isoPullback.hom ≫
    pullback.fst (hom f) (η[H.obj.X].left) =
      (pullback.fst f.hom.hom (kernelZero H)).hom.hom.left
  exact IsPullback.isoPullback_hom_fst (kernelGrp_isPullback f)

/-- Data certifying that the scheme-theoretic kernel carries the expected finite-flat
commutative group-scheme structure.  The isomorphism fixes its underlying scheme and structure
map, while the universal pullback above fixes its geometric meaning. -/
structure KernelPresentation {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H) where
  /-- The kernel as a finite flat commutative group scheme. -/
  kernel : FiniteFlatCommGroupScheme S
  /-- The kernel inclusion as a homomorphism of group schemes. -/
  inclusion : kernel ⟶ G
  /-- Identification with the scheme-theoretic pullback kernel. -/
  schemeIso : kernel.scheme ≅ kernelScheme f
  /-- Compatibility of the identification with the maps to the base. -/
  schemeIso_hom_structureMap : schemeIso.hom ≫ kernelStructureMap f = kernel.structureMap
  /-- Compatibility of the group-scheme inclusion with the pullback projection. -/
  schemeIso_hom_kernelι : schemeIso.hom ≫ kernelι f = hom inclusion

/-- The inherited kernel group scheme, packaged as finite flat when its structure morphism is
known to be finite and flat.  These hypotheses are intentionally attached to the explicit
scheme-theoretic structure map rather than inferred from `G` and `H`. -/
noncomputable def kernelFiniteFlat {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H)
    [IsFinite (kernelStructureMap f)] [Flat (kernelStructureMap f)] :
    FiniteFlatCommGroupScheme S where
  obj := kernelCommGroupScheme f
  property := by
    change IsFinite (kernelGrp f).X.hom ∧ Flat (kernelGrp f).X.hom
    rw [← kernelGrpSchemeIso_hom_structureMap f]
    exact ⟨inferInstance, inferInstance⟩

/-- The finite-flat kernel of `f`, under the exact geometric hypotheses needed over the base.

Flatness of kernels is not automatic over an arbitrary scheme, so the hypotheses deliberately
remain visible at this public entry point. -/
noncomputable abbrev kernel {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H)
    [IsFinite (kernelStructureMap f)] [Flat (kernelStructureMap f)] :
    FiniteFlatCommGroupScheme S :=
  kernelFiniteFlat f

/-- The inclusion of the finite-flat kernel into its source. -/
noncomputable def kernelFiniteFlatInclusion
    {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H)
    [IsFinite (kernelStructureMap f)] [Flat (kernelStructureMap f)] :
    kernelFiniteFlat f ⟶ G :=
  ObjectProperty.homMk (kernelCommGroupSchemeInclusion f)

/-- The canonical inclusion of the finite-flat kernel. -/
noncomputable abbrev kernelInclusion
    {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H)
    [IsFinite (kernelStructureMap f)] [Flat (kernelStructureMap f)] :
    kernel f ⟶ G :=
  kernelFiniteFlatInclusion f

/-- The canonical finite-flat kernel presentation under the precise hypotheses needed to put
the inherited group scheme in `FiniteFlatCommGroupScheme S`. -/
noncomputable def kernelPresentationOfFiniteFlat
    {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H)
    [IsFinite (kernelStructureMap f)] [Flat (kernelStructureMap f)] :
    KernelPresentation f where
  kernel := kernel f
  inclusion := kernelInclusion f
  schemeIso := kernelGrpSchemeIso f
  schemeIso_hom_structureMap := kernelGrpSchemeIso_hom_structureMap f
  schemeIso_hom_kernelι := kernelGrpSchemeIso_hom_kernelι f

/-- A scheme-theoretic kernel known finite and flat has the canonical certified presentation.
This permanent theorem is the destination of the checked Challenge bridge. -/
theorem kernelPresentation_exists_of_finite_flat
    {G H : FiniteFlatCommGroupScheme S} (f : G ⟶ H)
    [IsFinite (kernelStructureMap f)] [Flat (kernelStructureMap f)] :
    Nonempty (KernelPresentation f) :=
  ⟨kernelPresentationOfFiniteFlat f⟩

namespace KernelPresentation

variable {G H : FiniteFlatCommGroupScheme S} {f : G ⟶ H}

/-- The first comparison map in the geometric pullback of a certified kernel. -/
def baseChangeKernelMap (P : KernelPresentation f) (t : T ⟶ S) :
    pullback P.kernel.structureMap t ⟶ pullback (kernelStructureMap f) t :=
  pullback.map P.kernel.structureMap t (kernelStructureMap f) t
    P.schemeIso.hom (𝟙 T) (𝟙 S)
    (by simpa using P.schemeIso_hom_structureMap.symm) (by simp)

/-- Pulling back the chosen kernel scheme or its canonical scheme-theoretic model gives
isomorphic schemes over the new base. -/
noncomputable def baseChangeKernelIso (P : KernelPresentation f) (t : T ⟶ S) :
    pullback P.kernel.structureMap t ≅ pullback (kernelStructureMap f) t := by
  haveI : IsIso (P.baseChangeKernelMap t) := by
    unfold baseChangeKernelMap
    exact pullback.map_isIso P.kernel.structureMap t (kernelStructureMap f) t
      P.schemeIso.hom (𝟙 T) (𝟙 S)
      (by simpa using P.schemeIso_hom_structureMap.symm) (by simp)
  exact asIso (P.baseChangeKernelMap t)

@[reassoc]
theorem baseChangeKernelIso_hom_fst (P : KernelPresentation f) (t : T ⟶ S) :
    (P.baseChangeKernelIso t).hom ≫ pullback.fst (kernelStructureMap f) t =
      baseChangeProjection t P.kernel ≫ P.schemeIso.hom := by
  change P.baseChangeKernelMap t ≫ pullback.fst (kernelStructureMap f) t = _
  unfold baseChangeKernelMap baseChangeProjection
  exact pullback.lift_fst _ _ _

@[reassoc]
theorem baseChangeKernelIso_hom_snd (P : KernelPresentation f) (t : T ⟶ S) :
    (P.baseChangeKernelIso t).hom ≫ pullback.snd (kernelStructureMap f) t =
      ((baseChange t).obj P.kernel).structureMap := by
  change P.baseChangeKernelMap t ≫ pullback.snd (kernelStructureMap f) t = _
  unfold baseChangeKernelMap
  exact pullback.lift_snd _ _ _

/-- The pullback of a certified kernel is the direct kernel of the original morphism against
the base-changed identity section. -/
noncomputable def baseChangeDirectIso (P : KernelPresentation f) (t : T ⟶ S) :
    ((baseChange t).obj P.kernel).scheme ≅ pullback (hom f) (t ≫ η[H.obj.X].left) :=
  P.baseChangeKernelIso t ≪≫
    pullbackLeftPullbackSndIso (hom f) η[H.obj.X].left t

@[reassoc]
theorem baseChangeDirectIso_hom_fst (P : KernelPresentation f) (t : T ⟶ S) :
    (P.baseChangeDirectIso t).hom ≫
        pullback.fst (hom f) (t ≫ η[H.obj.X].left) =
      baseChangeProjection t P.kernel ≫ hom P.inclusion := by
  unfold baseChangeDirectIso
  change ((P.baseChangeKernelIso t).hom ≫
      (pullbackLeftPullbackSndIso (hom f) η[H.obj.X].left t).hom) ≫
        pullback.fst (hom f) (t ≫ η[H.obj.X].left) = _
  rw [Category.assoc, pullbackLeftPullbackSndIso_hom_fst]
  rw [← Category.assoc, baseChangeKernelIso_hom_fst]
  change (baseChangeProjection t P.kernel ≫ P.schemeIso.hom) ≫ kernelι f =
    baseChangeProjection t P.kernel ≫ hom P.inclusion
  calc
    (baseChangeProjection t P.kernel ≫ P.schemeIso.hom) ≫ kernelι f =
        baseChangeProjection t P.kernel ≫ (P.schemeIso.hom ≫ kernelι f) :=
      Category.assoc _ _ _
    _ = baseChangeProjection t P.kernel ≫ hom P.inclusion :=
      congrArg (fun q ↦ baseChangeProjection t P.kernel ≫ q) P.schemeIso_hom_kernelι

@[reassoc]
theorem baseChangeDirectIso_hom_snd (P : KernelPresentation f) (t : T ⟶ S) :
    (P.baseChangeDirectIso t).hom ≫
        pullback.snd (hom f) (t ≫ η[H.obj.X].left) =
      ((baseChange t).obj P.kernel).structureMap := by
  unfold baseChangeDirectIso
  change ((P.baseChangeKernelIso t).hom ≫
      (pullbackLeftPullbackSndIso (hom f) η[H.obj.X].left t).hom) ≫
        pullback.snd (hom f) (t ≫ η[H.obj.X].left) = _
  rw [Category.assoc, pullbackLeftPullbackSndIso_hom_snd]
  exact baseChangeKernelIso_hom_snd P t

@[reassoc]
theorem baseChangeDirectIso_hom_toSource (P : KernelPresentation f) (t : T ⟶ S) :
    (P.baseChangeDirectIso t).hom ≫ directKernelToBaseChangeSource t f =
      hom ((baseChange t).map P.inclusion) := by
  apply baseChangeScheme_hom_ext t G
  · calc
      ((P.baseChangeDirectIso t).hom ≫ directKernelToBaseChangeSource t f) ≫
          baseChangeProjection t G =
        (P.baseChangeDirectIso t).hom ≫
          (directKernelToBaseChangeSource t f ≫ baseChangeProjection t G) :=
        Category.assoc _ _ _
      _ = (P.baseChangeDirectIso t).hom ≫
          pullback.fst (hom f) (t ≫ η[H.obj.X].left) := by
        rw [directKernelToBaseChangeSource_projection]
      _ = baseChangeProjection t P.kernel ≫ hom P.inclusion :=
        P.baseChangeDirectIso_hom_fst t
      _ = hom ((baseChange t).map P.inclusion) ≫ baseChangeProjection t G :=
        (baseChange_hom_projection t P.inclusion).symm
  · calc
      ((P.baseChangeDirectIso t).hom ≫ directKernelToBaseChangeSource t f) ≫
          ((baseChange t).obj G).structureMap =
        (P.baseChangeDirectIso t).hom ≫
          (directKernelToBaseChangeSource t f ≫
            ((baseChange t).obj G).structureMap) := Category.assoc _ _ _
      _ = (P.baseChangeDirectIso t).hom ≫
          pullback.snd (hom f) (t ≫ η[H.obj.X].left) := by
        rw [directKernelToBaseChangeSource_structureMap]
      _ = ((baseChange t).obj P.kernel).structureMap :=
        P.baseChangeDirectIso_hom_snd t
      _ = hom ((baseChange t).map P.inclusion) ≫
          ((baseChange t).obj G).structureMap :=
        (hom_comp_structureMap ((baseChange t).map P.inclusion)).symm

/-- The canonical identification of a pulled-back certified kernel with the scheme-theoretic
kernel of the pulled-back homomorphism. -/
noncomputable def baseChangeSchemeIso (P : KernelPresentation f) (t : T ⟶ S) :
    ((baseChange t).obj P.kernel).scheme ≅ kernelScheme ((baseChange t).map f) :=
  P.baseChangeDirectIso t ≪≫ (directKernel_isPullback t f).isoPullback

@[reassoc]
theorem baseChangeSchemeIso_hom_structureMap (P : KernelPresentation f) (t : T ⟶ S) :
    (P.baseChangeSchemeIso t).hom ≫ kernelStructureMap ((baseChange t).map f) =
      ((baseChange t).obj P.kernel).structureMap := by
  unfold baseChangeSchemeIso
  change ((P.baseChangeDirectIso t).hom ≫
      (directKernel_isPullback t f).isoPullback.hom) ≫
        kernelStructureMap ((baseChange t).map f) = _
  rw [Category.assoc, IsPullback.isoPullback_hom_snd]
  exact P.baseChangeDirectIso_hom_snd t

@[reassoc]
theorem baseChangeSchemeIso_hom_kernelι (P : KernelPresentation f) (t : T ⟶ S) :
    (P.baseChangeSchemeIso t).hom ≫ kernelι ((baseChange t).map f) =
      hom ((baseChange t).map P.inclusion) := by
  unfold baseChangeSchemeIso
  change ((P.baseChangeDirectIso t).hom ≫
      (directKernel_isPullback t f).isoPullback.hom) ≫
        kernelι ((baseChange t).map f) = _
  rw [Category.assoc, IsPullback.isoPullback_hom_fst]
  exact P.baseChangeDirectIso_hom_toSource t

/-- Certified scheme-theoretic kernels commute with arbitrary base change. -/
noncomputable def baseChange (P : KernelPresentation f) (t : T ⟶ S) :
    KernelPresentation ((FiniteFlatCommGroupScheme.baseChange t).map f) where
  kernel := (FiniteFlatCommGroupScheme.baseChange t).obj P.kernel
  inclusion := (FiniteFlatCommGroupScheme.baseChange t).map P.inclusion
  schemeIso := P.baseChangeSchemeIso t
  schemeIso_hom_structureMap := P.baseChangeSchemeIso_hom_structureMap t
  schemeIso_hom_kernelι := P.baseChangeSchemeIso_hom_kernelι t

@[simp]
theorem baseChange_kernel (P : KernelPresentation f) (t : T ⟶ S) :
    (P.baseChange t).kernel = (FiniteFlatCommGroupScheme.baseChange t).obj P.kernel := rfl

@[simp]
theorem baseChange_inclusion (P : KernelPresentation f) (t : T ⟶ S) :
    (P.baseChange t).inclusion =
      (FiniteFlatCommGroupScheme.baseChange t).map P.inclusion := rfl

/-- The certified kernel inclusion maps trivially to the target group scheme. -/
@[reassoc]
theorem inclusion_condition (P : KernelPresentation f) :
    hom P.inclusion ≫ hom f = P.kernel.structureMap ≫ η[H.obj.X].left := by
  rw [← P.schemeIso_hom_kernelι, Category.assoc, kernel_condition, ← Category.assoc,
    P.schemeIso_hom_structureMap]

/-- A point of a certified scheme-theoretic kernel maps to the identity in the target. -/
theorem mapPoint_inclusion_eq_one (P : KernelPresentation f) (X : Over S)
    (y : P.kernel.Point X) :
    mapPoint f X (mapPoint P.inclusion X y) = 1 := by
  apply Over.OverMorphism.ext
  change (y.left ≫ hom P.inclusion) ≫ hom f = X.hom ≫ η[H.obj.X].left
  rw [Category.assoc, P.inclusion_condition, ← Category.assoc, Over.w y]

/-- Pointwise kernel membership is the scheme-theoretic pullback condition. -/
theorem point_condition_scheme (X : Over S) (x : G.Point X)
    (hx : mapPoint f X x = 1) :
    x.left ≫ hom f = X.hom ≫ η[H.obj.X].left := by
  have hxleft := congrArg Over.Hom.left hx
  change x.left ≫ hom f = X.hom ≫ η[H.obj.X].left at hxleft
  exact hxleft

/-- Every point killed by `f` lifts uniquely to the certified scheme-theoretic kernel. -/
theorem existsUnique_point_lift (P : KernelPresentation f) (X : Over S) (x : G.Point X)
    (hx : mapPoint f X x = 1) :
    ∃! y : P.kernel.Point X, mapPoint P.inclusion X y = x := by
  let l : X.left ⟶ kernelScheme f :=
    pullback.lift x.left X.hom (point_condition_scheme X x hx)
  have hstruct : P.schemeIso.inv ≫ P.kernel.structureMap = kernelStructureMap f := by
    apply (cancel_epi P.schemeIso.hom).1
    simpa using P.schemeIso_hom_structureMap.symm
  have hincl : P.schemeIso.inv ≫ hom P.inclusion = kernelι f := by
    apply (cancel_epi P.schemeIso.hom).1
    simpa using P.schemeIso_hom_kernelι.symm
  let y : P.kernel.Point X := Over.homMk (l ≫ P.schemeIso.inv) (by
    rw [Category.assoc, hstruct]
    exact pullback.lift_snd _ _ _)
  refine ⟨y, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    change (l ≫ P.schemeIso.inv) ≫ hom P.inclusion = x.left
    rw [Category.assoc, hincl]
    exact pullback.lift_fst _ _ _
  · intro z hz
    apply Over.OverMorphism.ext
    apply (cancel_mono P.schemeIso.hom).1
    change z.left ≫ P.schemeIso.hom = (l ≫ P.schemeIso.inv) ≫ P.schemeIso.hom
    rw [Category.assoc, P.schemeIso.inv_hom_id, Category.comp_id]
    apply pullback.hom_ext
    · rw [Category.assoc, P.schemeIso_hom_kernelι]
      rw [show l ≫ kernelι f = x.left by exact pullback.lift_fst _ _ _]
      exact congrArg Over.Hom.left hz
    · rw [Category.assoc, P.schemeIso_hom_structureMap]
      rw [show l ≫ kernelStructureMap f = X.hom by exact pullback.lift_snd _ _ _]
      exact Over.w z

/-- The inclusion identifies geometric kernel points with the actual kernel of the induced
homomorphism on points. -/
def pointKernelHom (P : KernelPresentation f) (X : Over S) :
    P.kernel.Point X →* (mapPoint f X).ker :=
  (mapPoint P.inclusion X).codRestrict (mapPoint f X).ker (P.mapPoint_inclusion_eq_one X)

/-- Scheme-theoretic kernels represent the pointwise kernel functor, multiplicatively and on
every test scheme over the base. -/
noncomputable def pointMulEquiv (P : KernelPresentation f) (X : Over S) :
    P.kernel.Point X ≃* (mapPoint f X).ker :=
  MulEquiv.ofBijective (P.pointKernelHom X) ⟨by
    intro a b hab
    have hv : mapPoint P.inclusion X a = mapPoint P.inclusion X b :=
      congrArg Subtype.val hab
    exact (P.existsUnique_point_lift X (mapPoint P.inclusion X a)
      (P.mapPoint_inclusion_eq_one X a)).unique rfl hv.symm, by
    intro x
    let h := P.existsUnique_point_lift X x.1 x.2
    refine ⟨h.choose, ?_⟩
    apply Subtype.ext
    exact h.choose_spec.1⟩

end KernelPresentation

end FiniteFlatCommGroupScheme

end AlgebraicGeometry

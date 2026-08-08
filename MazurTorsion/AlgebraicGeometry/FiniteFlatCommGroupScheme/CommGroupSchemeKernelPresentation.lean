/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.CommGroupSchemeKernel

/-!
# Geometric kernel presentations for ambient commutative group schemes

The canonical kernel of an arbitrary morphism of commutative group schemes exists, but it need
not inherit a finiteness or flatness property from the source and target.  A
`KernelPresentation` records an actual supplied group scheme, its chosen inclusion, and its
geometric identification with that canonical kernel.  Compatibility with the inclusion rules
out unrelated pointwise models.

This interface is deliberately independent of finite-flat and quasi-finite wrappers.  Its
point-kernel equivalence, unique lift, and represented-point exactness API therefore applies to
both settings without duplicating the later fppf connecting construction.  No claim is made
that an arbitrary canonical kernel is flat, quasi-finite, finite, or finitely presented.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.CommGroupScheme

universe u

variable {S : Scheme.{u}} {G H K : CommGroupScheme S}

/-- Ambient group-scheme point maps preserve identity morphisms. -/
@[simp]
theorem mapPoint_id (G : CommGroupScheme S) (T : Over S) :
    mapPoint (CategoryStruct.id G) T = MonoidHom.id (G.Point T) := by
  ext x
  simp [mapPoint]

/-- Ambient group-scheme point maps turn composition into composition of homomorphisms. -/
@[simp]
theorem mapPoint_comp (f : G ⟶ H) (g : H ⟶ K) (T : Over S) :
    mapPoint (f ≫ g) T = (mapPoint g T).comp (mapPoint f T) := by
  ext x
  simp only [mapPoint_apply, MonoidHom.comp_apply]
  exact (Category.assoc _ _ _).symm

/-- An isomorphism of ambient commutative group schemes induces a multiplicative equivalence on
points of every test scheme. -/
def pointMulEquivOfIso (e : G ≅ H) (T : Over S) : G.Point T ≃* H.Point T where
  toFun := mapPoint e.hom T
  invFun := mapPoint e.inv T
  left_inv x := by
    rw [← MonoidHom.comp_apply, ← mapPoint_comp, e.hom_inv_id, mapPoint_id]
    rfl
  right_inv x := by
    rw [← MonoidHom.comp_apply, ← mapPoint_comp, e.inv_hom_id, mapPoint_id]
    rfl
  map_mul' x y := map_mul (mapPoint e.hom T) x y

/-- A supplied commutative group scheme identified geometrically with the canonical kernel of
`f`.  The explicit inclusion preserves a caller's chosen exact-sequence morphism, while the
compatibility field certifies that it is the inclusion induced by the geometric kernel. -/
structure KernelPresentation (f : G ⟶ H) where
  /-- The supplied geometric kernel object. -/
  kernel : CommGroupScheme S
  /-- The chosen inclusion into the source. -/
  inclusion : kernel ⟶ G
  /-- Identification with the canonical ambient group-scheme kernel. -/
  kernelIso : kernel ≅ CommGroupScheme.kernel f
  /-- The chosen inclusion is the canonical one under the geometric identification. -/
  kernelIso_hom_kernelInclusion :
    kernelIso.hom ≫ CommGroupScheme.kernelInclusion f = inclusion

namespace KernelPresentation

variable {f : G ⟶ H} (P : KernelPresentation f)

/-- Points of a supplied geometric kernel are the pointwise kernel of the original morphism. -/
noncomputable def pointKernelMulEquiv (T : Over S) :
    P.kernel.Point T ≃* (mapPoint f T).ker :=
  (pointMulEquivOfIso P.kernelIso T).trans (CommGroupScheme.pointKernelMulEquiv f T)

@[simp]
theorem pointKernelMulEquiv_apply (T : Over S) (x : P.kernel.Point T) :
    (P.pointKernelMulEquiv T x).1 = mapPoint P.inclusion T x := by
  change (x ≫ P.kernelIso.hom.hom.hom.hom) ≫
      (CommGroupScheme.kernelInclusion f).hom.hom.hom =
    x ≫ P.inclusion.hom.hom.hom
  rw [Category.assoc]
  exact congrArg (fun q ↦ x ≫ q.hom.hom.hom) P.kernelIso_hom_kernelInclusion

/-- Every supplied-kernel point maps to the identity in the target. -/
@[simp]
theorem mapPoint_inclusion_eq_one (T : Over S) (x : P.kernel.Point T) :
    mapPoint f T (mapPoint P.inclusion T x) = 1 := by
  rw [← P.pointKernelMulEquiv_apply T x]
  exact (P.pointKernelMulEquiv T x).2

/-- The canonical chosen lift of a point killed by the original morphism. -/
noncomputable def liftPoint {T : Over S} (x : G.Point T) (hx : mapPoint f T x = 1) :
    P.kernel.Point T :=
  (P.pointKernelMulEquiv T).symm ⟨x, hx⟩

@[simp]
theorem mapPoint_liftPoint {T : Over S} (x : G.Point T)
    (hx : mapPoint f T x = 1) :
    mapPoint P.inclusion T (P.liftPoint x hx) = x := by
  have h := P.pointKernelMulEquiv_apply T (P.liftPoint x hx)
  rw [show P.pointKernelMulEquiv T (P.liftPoint x hx) = ⟨x, hx⟩ by
    exact MulEquiv.apply_symm_apply (P.pointKernelMulEquiv T) ⟨x, hx⟩] at h
  exact h.symm

/-- A supplied geometric kernel inclusion is injective on every test scheme. -/
theorem inclusion_point_injective (T : Over S) :
    Function.Injective (mapPoint P.inclusion T) := by
  intro x y hxy
  apply (P.pointKernelMulEquiv T).injective
  apply Subtype.ext
  simpa only [P.pointKernelMulEquiv_apply] using hxy

/-- Every killed point lifts uniquely through the supplied geometric kernel. -/
theorem existsUnique_point_lift (T : Over S) (x : G.Point T)
    (hx : mapPoint f T x = 1) :
    ∃! y : P.kernel.Point T, mapPoint P.inclusion T y = x := by
  refine ⟨P.liftPoint x hx, P.mapPoint_liftPoint x hx, ?_⟩
  intro y hy
  apply P.inclusion_point_injective T
  exact hy.trans (P.mapPoint_liftPoint x hx).symm

/-- A geometric kernel presentation is exact on represented points of every test scheme. -/
theorem point_mulExact (T : Over S) :
    Function.MulExact (mapPoint P.inclusion T) (mapPoint f T) := by
  intro x
  constructor
  · intro hx
    exact ⟨P.liftPoint x hx, P.mapPoint_liftPoint x hx⟩
  · rintro ⟨y, rfl⟩
    exact P.mapPoint_inclusion_eq_one T y

/-- Concrete represented-point consumer of the ambient presentation: a source point is killed
exactly when it comes from the supplied geometric kernel. -/
theorem mapPoint_eq_one_iff_exists_kernelPoint (T : Over S) (x : G.Point T) :
    mapPoint f T x = 1 ↔
      ∃ y : P.kernel.Point T, mapPoint P.inclusion T y = x :=
  P.point_mulExact T x

/-! ### Arbitrary base change -/

variable {T : Scheme.{u}}

/-- The scheme isomorphism underlying an isomorphism of commutative group schemes. -/
private noncomputable def underlyingSchemeIso {A B : CommGroupScheme S}
    (e : A ≅ B) : A.X.left ≅ B.X.left where
  hom := underlyingHom e.hom
  inv := underlyingHom e.inv
  hom_inv_id := by
    change underlyingHom (e.hom ≫ e.inv) = underlyingHom (𝟙 A)
    rw [e.hom_inv_id]
  inv_hom_id := by
    change underlyingHom (e.inv ≫ e.hom) = underlyingHom (𝟙 B)
    rw [e.inv_hom_id]

/-- A geometric kernel presentation also identifies the underlying supplied scheme with the
ordinary scheme-theoretic pullback kernel. -/
private noncomputable def schemeIso : P.kernel.X.left ≅ kernelScheme f :=
  (underlyingSchemeIso P.kernelIso).trans (kernelSchemeIso f)

@[reassoc]
private theorem schemeIso_hom_structureMap :
    P.schemeIso.hom ≫ kernelStructureMap f = P.kernel.X.hom := by
  unfold schemeIso
  change (underlyingHom P.kernelIso.hom ≫ (kernelSchemeIso f).hom) ≫
      kernelStructureMap f = P.kernel.X.hom
  rw [Category.assoc, kernelSchemeIso_hom_structureMap]
  exact P.kernelIso.hom.hom.hom.hom.w

@[reassoc]
private theorem schemeIso_hom_kernelι :
    P.schemeIso.hom ≫ kernelι f = underlyingHom P.inclusion := by
  unfold schemeIso
  change (underlyingHom P.kernelIso.hom ≫ (kernelSchemeIso f).hom) ≫
      kernelι f = underlyingHom P.inclusion
  rw [Category.assoc, kernelSchemeIso_hom_kernelι]
  exact congrArg (fun q : P.kernel ⟶ G ↦ underlyingHom q)
    P.kernelIso_hom_kernelInclusion

/-- Projection from the canonical base change of an ambient group scheme to its original
underlying scheme. -/
private def baseChangeProjection (t : T ⟶ S) (A : CommGroupScheme S) :
    ((Over.pullback t).mapCommGrp.obj A).X.left ⟶ A.X.left :=
  pullback.fst A.X.hom t

@[reassoc]
private theorem baseChangeProjection_condition (t : T ⟶ S)
    (A : CommGroupScheme S) :
    baseChangeProjection t A ≫ A.X.hom =
      ((Over.pullback t).mapCommGrp.obj A).X.hom ≫ t :=
  pullback.condition

/-- Two scheme maps into an ambient base change agree after both pullback projections. -/
private theorem baseChangeScheme_hom_ext (t : T ⟶ S) (A : CommGroupScheme S)
    {X : Scheme.{u}}
    {a b : X ⟶ ((Over.pullback t).mapCommGrp.obj A).X.left}
    (hprojection : a ≫ baseChangeProjection t A = b ≫ baseChangeProjection t A)
    (hbase : a ≫ ((Over.pullback t).mapCommGrp.obj A).X.hom =
      b ≫ ((Over.pullback t).mapCommGrp.obj A).X.hom) : a = b := by
  apply pullback.hom_ext
  · exact hprojection
  · exact hbase

/-- Universal lift into the underlying scheme of an ambient base change. -/
private def baseChangeLift (t : T ⟶ S) (A : CommGroupScheme S)
    {X : Scheme.{u}} (a : X ⟶ A.X.left) (b : X ⟶ T)
    (h : a ≫ A.X.hom = b ≫ t) :
    X ⟶ ((Over.pullback t).mapCommGrp.obj A).X.left :=
  pullback.lift a b h

@[reassoc]
private theorem baseChangeLift_projection (t : T ⟶ S)
    (A : CommGroupScheme S) {X : Scheme.{u}}
    (a : X ⟶ A.X.left) (b : X ⟶ T) (h : a ≫ A.X.hom = b ≫ t) :
    baseChangeLift t A a b h ≫ baseChangeProjection t A = a :=
  pullback.lift_fst _ _ _

@[reassoc]
private theorem baseChangeLift_structureMap (t : T ⟶ S)
    (A : CommGroupScheme S) {X : Scheme.{u}}
    (a : X ⟶ A.X.left) (b : X ⟶ T) (h : a ≫ A.X.hom = b ≫ t) :
    baseChangeLift t A a b h ≫
      ((Over.pullback t).mapCommGrp.obj A).X.hom = b :=
  pullback.lift_snd _ _ _

@[reassoc]
private theorem baseChange_hom_projection (t : T ⟶ S)
    {A B : CommGroupScheme S} (g : A ⟶ B) :
    underlyingHom ((Over.pullback t).mapCommGrp.map g) ≫
        baseChangeProjection t B =
      baseChangeProjection t A ≫ underlyingHom g := by
  unfold baseChangeProjection
  change ((Over.pullback t).map g.hom.hom.hom).left ≫
      pullback.fst B.X.hom t = _
  have hmap := Over.pullback_map_left t A.X (k := g.hom.hom.hom)
  have hmcomp := congrArg (fun q ↦ q ≫ pullback.fst B.X.hom t) hmap
  rw [pullback.lift_fst] at hmcomp
  exact hmcomp

@[reassoc]
private theorem baseChange_hom_structureMap (t : T ⟶ S)
    {A B : CommGroupScheme S} (g : A ⟶ B) :
    underlyingHom ((Over.pullback t).mapCommGrp.map g) ≫
        ((Over.pullback t).mapCommGrp.obj B).X.hom =
      ((Over.pullback t).mapCommGrp.obj A).X.hom :=
  ((Over.pullback t).mapCommGrp.map g).hom.hom.hom.w

@[reassoc]
private theorem baseChange_one_projection (t : T ⟶ S)
    (A : CommGroupScheme S) :
    η[((Over.pullback t).mapCommGrp.obj A).X].left ≫
        baseChangeProjection t A =
      t ≫ η[A.X].left := by
  unfold baseChangeProjection
  change Over.Hom.left (η[((Over.pullback t).mapCommGrp.obj A).X]) ≫
      pullback.fst A.X.hom t = t ≫ η[A.X].left
  change Over.Hom.left (Functor.LaxMonoidal.ε (Over.pullback t) ≫
      (Over.pullback t).map η[A.X]) ≫ pullback.fst A.X.hom t = _
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

@[reassoc]
private theorem baseChange_one_structureMap (t : T ⟶ S)
    (A : CommGroupScheme S) :
    η[((Over.pullback t).mapCommGrp.obj A).X].left ≫
        ((Over.pullback t).mapCommGrp.obj A).X.hom = 𝟙 T :=
  (η[((Over.pullback t).mapCommGrp.obj A).X]).w

/-- The square underlying the pullback of an ambient group-scheme homomorphism is cartesian. -/
private theorem baseChange_hom_isPullback (t : T ⟶ S)
    {A B : CommGroupScheme S} (g : A ⟶ B) :
    IsPullback (baseChangeProjection t A)
      (underlyingHom ((Over.pullback t).mapCommGrp.map g))
      (underlyingHom g) (baseChangeProjection t B) := by
  refine ⟨⟨(baseChange_hom_projection t g).symm⟩, ⟨?_⟩⟩
  let lift (s : PullbackCone (underlyingHom g) (baseChangeProjection t B)) :
      s.pt ⟶ ((Over.pullback t).mapCommGrp.obj A).X.left :=
    baseChangeLift t A s.fst
      (s.snd ≫ ((Over.pullback t).mapCommGrp.obj B).X.hom) (by
        calc
          s.fst ≫ A.X.hom = s.fst ≫ underlyingHom g ≫ B.X.hom := by
            rw [g.hom.hom.hom.w]
          _ = s.snd ≫ baseChangeProjection t B ≫ B.X.hom :=
            s.condition_assoc B.X.hom
          _ = s.snd ≫ ((Over.pullback t).mapCommGrp.obj B).X.hom ≫ t := by
            rw [baseChangeProjection_condition])
  refine PullbackCone.IsLimit.mk _ lift ?_ ?_ ?_
  · intro s
    simpa only [lift] using
      (baseChangeLift_projection t A s.fst
        (s.snd ≫ ((Over.pullback t).mapCommGrp.obj B).X.hom) _)
  · intro s
    apply baseChangeScheme_hom_ext t B
    · calc
        (lift s ≫ underlyingHom ((Over.pullback t).mapCommGrp.map g)) ≫
            baseChangeProjection t B =
          lift s ≫ (baseChangeProjection t A ≫ underlyingHom g) := by
            rw [Category.assoc, baseChange_hom_projection]
        _ = s.fst ≫ underlyingHom g := by
          rw [← Category.assoc]
          have hlift : lift s ≫ baseChangeProjection t A = s.fst := by
            simpa only [lift] using
              (baseChangeLift_projection t A s.fst
                (s.snd ≫ ((Over.pullback t).mapCommGrp.obj B).X.hom) _)
          rw [hlift]
        _ = s.snd ≫ baseChangeProjection t B := s.condition
    · calc
        (lift s ≫ underlyingHom ((Over.pullback t).mapCommGrp.map g)) ≫
            ((Over.pullback t).mapCommGrp.obj B).X.hom =
          lift s ≫ ((Over.pullback t).mapCommGrp.obj A).X.hom := by
            rw [Category.assoc, baseChange_hom_structureMap]
        _ = s.snd ≫ ((Over.pullback t).mapCommGrp.obj B).X.hom := by
          simpa only [lift] using
            (baseChangeLift_structureMap t A s.fst
              (s.snd ≫ ((Over.pullback t).mapCommGrp.obj B).X.hom) _)
  · intro s m hfst hsnd
    apply baseChangeScheme_hom_ext t A
    · have hlift : lift s ≫ baseChangeProjection t A = s.fst := by
        simpa only [lift] using
          (baseChangeLift_projection t A s.fst
            (s.snd ≫ ((Over.pullback t).mapCommGrp.obj B).X.hom) _)
      exact hfst.trans hlift.symm
    · calc
        m ≫ ((Over.pullback t).mapCommGrp.obj A).X.hom =
          m ≫ underlyingHom ((Over.pullback t).mapCommGrp.map g) ≫
            ((Over.pullback t).mapCommGrp.obj B).X.hom := by
              rw [baseChange_hom_structureMap]
        _ = s.snd ≫ ((Over.pullback t).mapCommGrp.obj B).X.hom := by
          rw [← Category.assoc, hsnd]
        _ = lift s ≫ ((Over.pullback t).mapCommGrp.obj A).X.hom := by
          symm
          simpa only [lift] using
            (baseChangeLift_structureMap t A s.fst
              (s.snd ≫ ((Over.pullback t).mapCommGrp.obj B).X.hom) _)

/-- The direct pullback kernel over the new base maps to the pulled-back source. -/
private noncomputable def directKernelToBaseChangeSource (t : T ⟶ S) :
    pullback (underlyingHom f) (t ≫ η[H.X].left) ⟶
      ((Over.pullback t).mapCommGrp.obj G).X.left :=
  (baseChange_hom_isPullback t f).lift
    (pullback.fst (underlyingHom f) (t ≫ η[H.X].left))
    (pullback.snd (underlyingHom f) (t ≫ η[H.X].left) ≫
      η[((Over.pullback t).mapCommGrp.obj H).X].left)
    (by
      calc
        pullback.fst (underlyingHom f) (t ≫ η[H.X].left) ≫ underlyingHom f =
          pullback.snd (underlyingHom f) (t ≫ η[H.X].left) ≫
            (t ≫ η[H.X].left) := pullback.condition
        _ = pullback.snd (underlyingHom f) (t ≫ η[H.X].left) ≫
            (η[((Over.pullback t).mapCommGrp.obj H).X].left ≫
              baseChangeProjection t H) := by rw [baseChange_one_projection]
        _ = (pullback.snd (underlyingHom f) (t ≫ η[H.X].left) ≫
            η[((Over.pullback t).mapCommGrp.obj H).X].left) ≫
              baseChangeProjection t H := (Category.assoc _ _ _).symm)

private theorem directKernel_isPullback (t : T ⟶ S) :
    IsPullback (directKernelToBaseChangeSource t)
      (pullback.snd (underlyingHom f) (t ≫ η[H.X].left))
      (underlyingHom ((Over.pullback t).mapCommGrp.map f))
      η[((Over.pullback t).mapCommGrp.obj H).X].left := by
  let right := baseChange_hom_isPullback t f
  have outer : IsPullback
      (pullback.fst (underlyingHom f) (t ≫ η[H.X].left))
      (pullback.snd (underlyingHom f) (t ≫ η[H.X].left))
      (underlyingHom f)
      (η[((Over.pullback t).mapCommGrp.obj H).X].left ≫
        baseChangeProjection t H) := by
    rw [baseChange_one_projection]
    exact IsPullback.of_hasPullback (underlyingHom f) (t ≫ η[H.X].left)
  exact outer.of_right' right

@[reassoc]
private theorem directKernelToBaseChangeSource_projection (t : T ⟶ S) :
    directKernelToBaseChangeSource t ≫ baseChangeProjection t G =
      pullback.fst (underlyingHom f) (t ≫ η[H.X].left) :=
  (baseChange_hom_isPullback t f).lift_fst _ _ _

@[reassoc]
private theorem directKernelToBaseChangeSource_project (t : T ⟶ S) :
    directKernelToBaseChangeSource t ≫
        underlyingHom ((Over.pullback t).mapCommGrp.map f) =
      pullback.snd (underlyingHom f) (t ≫ η[H.X].left) ≫
        η[((Over.pullback t).mapCommGrp.obj H).X].left :=
  (baseChange_hom_isPullback t f).lift_snd _ _ _

@[reassoc]
private theorem directKernelToBaseChangeSource_structureMap (t : T ⟶ S) :
    directKernelToBaseChangeSource t ≫
        ((Over.pullback t).mapCommGrp.obj G).X.hom =
      pullback.snd (underlyingHom f) (t ≫ η[H.X].left) := by
  calc
    directKernelToBaseChangeSource t ≫
        ((Over.pullback t).mapCommGrp.obj G).X.hom =
      (directKernelToBaseChangeSource t ≫
          underlyingHom ((Over.pullback t).mapCommGrp.map f)) ≫
        ((Over.pullback t).mapCommGrp.obj H).X.hom := by
          rw [Category.assoc, baseChange_hom_structureMap]
    _ = (pullback.snd (underlyingHom f) (t ≫ η[H.X].left) ≫
          η[((Over.pullback t).mapCommGrp.obj H).X].left) ≫
        ((Over.pullback t).mapCommGrp.obj H).X.hom := by
          rw [directKernelToBaseChangeSource_project]
    _ = pullback.snd (underlyingHom f) (t ≫ η[H.X].left) := by
      rw [Category.assoc, baseChange_one_structureMap, Category.comp_id]

/-- First comparison map obtained by pulling back the supplied scheme-kernel isomorphism. -/
private def baseChangeKernelMap (t : T ⟶ S) :
    pullback P.kernel.X.hom t ⟶ pullback (kernelStructureMap f) t :=
  pullback.map P.kernel.X.hom t (kernelStructureMap f) t
    P.schemeIso.hom (𝟙 T) (𝟙 S)
    (by simpa using P.schemeIso_hom_structureMap.symm) (by simp)

private noncomputable def baseChangeKernelIso (t : T ⟶ S) :
    pullback P.kernel.X.hom t ≅ pullback (kernelStructureMap f) t := by
  haveI : IsIso (P.baseChangeKernelMap t) := by
    unfold baseChangeKernelMap
    exact pullback.map_isIso P.kernel.X.hom t (kernelStructureMap f) t
      P.schemeIso.hom (𝟙 T) (𝟙 S)
      (by simpa using P.schemeIso_hom_structureMap.symm) (by simp)
  exact asIso (P.baseChangeKernelMap t)

@[reassoc]
private theorem baseChangeKernelIso_hom_fst (t : T ⟶ S) :
    (P.baseChangeKernelIso t).hom ≫ pullback.fst (kernelStructureMap f) t =
      baseChangeProjection t P.kernel ≫ P.schemeIso.hom := by
  change P.baseChangeKernelMap t ≫ pullback.fst (kernelStructureMap f) t = _
  exact pullback.lift_fst _ _ _

@[reassoc]
private theorem baseChangeKernelIso_hom_snd (t : T ⟶ S) :
    (P.baseChangeKernelIso t).hom ≫ pullback.snd (kernelStructureMap f) t =
      ((Over.pullback t).mapCommGrp.obj P.kernel).X.hom := by
  change P.baseChangeKernelMap t ≫ pullback.snd (kernelStructureMap f) t = _
  exact pullback.lift_snd _ _ _

/-- Pulling back a supplied kernel scheme gives the direct kernel pullback over the new base. -/
private noncomputable def baseChangeDirectIso (t : T ⟶ S) :
    ((Over.pullback t).mapCommGrp.obj P.kernel).X.left ≅
      pullback (underlyingHom f) (t ≫ η[H.X].left) :=
  (P.baseChangeKernelIso t).trans
    (pullbackLeftPullbackSndIso (underlyingHom f) η[H.X].left t)

@[reassoc]
private theorem baseChangeDirectIso_hom_fst (t : T ⟶ S) :
    (P.baseChangeDirectIso t).hom ≫
        pullback.fst (underlyingHom f) (t ≫ η[H.X].left) =
      baseChangeProjection t P.kernel ≫ underlyingHom P.inclusion := by
  unfold baseChangeDirectIso
  change ((P.baseChangeKernelIso t).hom ≫
      (pullbackLeftPullbackSndIso (underlyingHom f) η[H.X].left t).hom) ≫
        pullback.fst (underlyingHom f) (t ≫ η[H.X].left) = _
  rw [Category.assoc, pullbackLeftPullbackSndIso_hom_fst]
  rw [← Category.assoc, baseChangeKernelIso_hom_fst]
  calc
    (baseChangeProjection t P.kernel ≫ P.schemeIso.hom) ≫ kernelι f =
        baseChangeProjection t P.kernel ≫ (P.schemeIso.hom ≫ kernelι f) :=
      Category.assoc _ _ _
    _ = baseChangeProjection t P.kernel ≫ underlyingHom P.inclusion := by
      rw [P.schemeIso_hom_kernelι]

@[reassoc]
private theorem baseChangeDirectIso_hom_snd (t : T ⟶ S) :
    (P.baseChangeDirectIso t).hom ≫
        pullback.snd (underlyingHom f) (t ≫ η[H.X].left) =
      ((Over.pullback t).mapCommGrp.obj P.kernel).X.hom := by
  unfold baseChangeDirectIso
  change ((P.baseChangeKernelIso t).hom ≫
      (pullbackLeftPullbackSndIso (underlyingHom f) η[H.X].left t).hom) ≫
        pullback.snd (underlyingHom f) (t ≫ η[H.X].left) = _
  rw [Category.assoc, pullbackLeftPullbackSndIso_hom_snd]
  exact P.baseChangeKernelIso_hom_snd t

@[reassoc]
private theorem baseChangeDirectIso_hom_toSource (t : T ⟶ S) :
    (P.baseChangeDirectIso t).hom ≫
        directKernelToBaseChangeSource t =
      underlyingHom ((Over.pullback t).mapCommGrp.map P.inclusion) := by
  apply baseChangeScheme_hom_ext t G
  · calc
      ((P.baseChangeDirectIso t).hom ≫
          directKernelToBaseChangeSource t) ≫
          baseChangeProjection t G =
        (P.baseChangeDirectIso t).hom ≫
          (directKernelToBaseChangeSource t ≫
            baseChangeProjection t G) := Category.assoc _ _ _
      _ = (P.baseChangeDirectIso t).hom ≫
          pullback.fst (underlyingHom f) (t ≫ η[H.X].left) := by
        rw [directKernelToBaseChangeSource_projection]
      _ = baseChangeProjection t P.kernel ≫ underlyingHom P.inclusion :=
        P.baseChangeDirectIso_hom_fst t
      _ = underlyingHom ((Over.pullback t).mapCommGrp.map P.inclusion) ≫
          baseChangeProjection t G :=
        (baseChange_hom_projection t P.inclusion).symm
  · calc
      ((P.baseChangeDirectIso t).hom ≫
          directKernelToBaseChangeSource t) ≫
          ((Over.pullback t).mapCommGrp.obj G).X.hom =
        (P.baseChangeDirectIso t).hom ≫
          (directKernelToBaseChangeSource t ≫
            ((Over.pullback t).mapCommGrp.obj G).X.hom) := Category.assoc _ _ _
      _ = (P.baseChangeDirectIso t).hom ≫
          pullback.snd (underlyingHom f) (t ≫ η[H.X].left) := by
        rw [directKernelToBaseChangeSource_structureMap]
      _ = ((Over.pullback t).mapCommGrp.obj P.kernel).X.hom :=
        P.baseChangeDirectIso_hom_snd t
      _ = underlyingHom ((Over.pullback t).mapCommGrp.map P.inclusion) ≫
          ((Over.pullback t).mapCommGrp.obj G).X.hom :=
        (baseChange_hom_structureMap t P.inclusion).symm

/-- The underlying scheme of a pulled-back supplied kernel is canonically the kernel scheme of
the pulled-back homomorphism. -/
private noncomputable def baseChangeSchemeIso (t : T ⟶ S) :
    ((Over.pullback t).mapCommGrp.obj P.kernel).X.left ≅
      kernelScheme ((Over.pullback t).mapCommGrp.map f) :=
  (P.baseChangeDirectIso t).trans (directKernel_isPullback t).isoPullback

@[reassoc]
private theorem baseChangeSchemeIso_hom_structureMap (t : T ⟶ S) :
    (P.baseChangeSchemeIso t).hom ≫
        kernelStructureMap ((Over.pullback t).mapCommGrp.map f) =
      ((Over.pullback t).mapCommGrp.obj P.kernel).X.hom := by
  unfold baseChangeSchemeIso
  change ((P.baseChangeDirectIso t).hom ≫
      (directKernel_isPullback t).isoPullback.hom) ≫
        kernelStructureMap ((Over.pullback t).mapCommGrp.map f) = _
  rw [Category.assoc, IsPullback.isoPullback_hom_snd]
  exact P.baseChangeDirectIso_hom_snd t

@[reassoc]
private theorem baseChangeSchemeIso_hom_kernelι (t : T ⟶ S) :
    (P.baseChangeSchemeIso t).hom ≫
        kernelι ((Over.pullback t).mapCommGrp.map f) =
      underlyingHom ((Over.pullback t).mapCommGrp.map P.inclusion) := by
  unfold baseChangeSchemeIso
  change ((P.baseChangeDirectIso t).hom ≫
      (directKernel_isPullback t).isoPullback.hom) ≫
        kernelι ((Over.pullback t).mapCommGrp.map f) = _
  rw [Category.assoc, IsPullback.isoPullback_hom_fst]
  exact P.baseChangeDirectIso_hom_toSource t

private theorem baseChange_inclusion_zero_grp (t : T ⟶ S) :
    ((Over.pullback t).mapCommGrp.map P.inclusion).hom ≫
        ((Over.pullback t).mapCommGrp.map f).hom =
      (default : ((Over.pullback t).mapCommGrp.obj P.kernel).toGrp ⟶
        Grp.trivial (Over T)) ≫
        kernelZero ((Over.pullback t).mapCommGrp.obj H) := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  change underlyingHom ((Over.pullback t).mapCommGrp.map P.inclusion) ≫
      underlyingHom ((Over.pullback t).mapCommGrp.map f) =
    ((Over.pullback t).mapCommGrp.obj P.kernel).X.hom ≫
      η[((Over.pullback t).mapCommGrp.obj H).X].left
  rw [← P.baseChangeSchemeIso_hom_kernelι t, Category.assoc,
    kernel_condition, ← Category.assoc,
    P.baseChangeSchemeIso_hom_structureMap t]

/-- Comparison from the pulled-back supplied kernel to the canonical kernel of the pulled-back
homomorphism. -/
private noncomputable def baseChangeToKernel (t : T ⟶ S) :
    (Over.pullback t).mapCommGrp.obj P.kernel ⟶
      CommGroupScheme.kernel ((Over.pullback t).mapCommGrp.map f) := by
  apply InducedCategory.homMk
  exact pullback.lift ((Over.pullback t).mapCommGrp.map P.inclusion).hom
    default (P.baseChange_inclusion_zero_grp t)

@[reassoc]
private theorem baseChangeToKernel_comp_kernelInclusion (t : T ⟶ S) :
    P.baseChangeToKernel t ≫
        kernelInclusion ((Over.pullback t).mapCommGrp.map f) =
      (Over.pullback t).mapCommGrp.map P.inclusion := by
  apply CommGrp.hom_ext
  have hlift := pullback.lift_fst
    ((Over.pullback t).mapCommGrp.map P.inclusion).hom
    (default : ((Over.pullback t).mapCommGrp.obj P.kernel).toGrp ⟶
      Grp.trivial (Over T))
    (P.baseChange_inclusion_zero_grp t)
  exact congrArg (fun q ↦ q.hom.hom) hlift

@[reassoc]
private theorem baseChangeToKernel_hom_comp_kernelSchemeIso (t : T ⟶ S) :
    underlyingHom (P.baseChangeToKernel t) ≫
        (kernelSchemeIso ((Over.pullback t).mapCommGrp.map f)).hom =
      (P.baseChangeSchemeIso t).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, kernelSchemeIso_hom_kernelι]
    have h := congrArg
      (fun q : (Over.pullback t).mapCommGrp.obj P.kernel ⟶
          (Over.pullback t).mapCommGrp.obj G ↦ underlyingHom q)
      (P.baseChangeToKernel_comp_kernelInclusion t)
    exact h.trans (P.baseChangeSchemeIso_hom_kernelι t).symm
  · rw [Category.assoc, kernelSchemeIso_hom_structureMap]
    exact (P.baseChangeToKernel t).hom.hom.hom.w.trans
      (P.baseChangeSchemeIso_hom_structureMap t).symm

private theorem baseChangeToKernel_underlyingHom (t : T ⟶ S) :
    underlyingHom (P.baseChangeToKernel t) =
      (P.baseChangeSchemeIso t).hom ≫
        (kernelSchemeIso ((Over.pullback t).mapCommGrp.map f)).inv := by
  apply (cancel_mono
    (kernelSchemeIso ((Over.pullback t).mapCommGrp.map f)).hom).1
  rw [Category.assoc,
    (kernelSchemeIso ((Over.pullback t).mapCommGrp.map f)).inv_hom_id,
    Category.comp_id, P.baseChangeToKernel_hom_comp_kernelSchemeIso]

private noncomputable instance baseChangeToKernel_isIso (t : T ⟶ S) :
    IsIso (P.baseChangeToKernel t) := by
  haveI : IsIso (underlyingHom (P.baseChangeToKernel t)) := by
    rw [P.baseChangeToKernel_underlyingHom t]
    infer_instance
  haveI : IsIso
      ((Over.forget T).map (P.baseChangeToKernel t).hom.hom.hom) := by
    change IsIso (underlyingHom (P.baseChangeToKernel t))
    infer_instance
  haveI : IsIso (P.baseChangeToKernel t).hom.hom.hom :=
    isIso_of_reflects_iso _ (Over.forget T)
  haveI : IsIso
      ((Mon.forget (Over T)).map (P.baseChangeToKernel t).hom.hom) := by
    change IsIso (P.baseChangeToKernel t).hom.hom.hom
    infer_instance
  haveI : IsIso (P.baseChangeToKernel t).hom.hom :=
    isIso_of_reflects_iso _ (Mon.forget (Over T))
  haveI : IsIso
      ((Grp.forget₂Mon (Over T)).map (P.baseChangeToKernel t).hom) := by
    change IsIso (P.baseChangeToKernel t).hom.hom
    infer_instance
  haveI : IsIso (P.baseChangeToKernel t).hom :=
    isIso_of_reflects_iso _ (Grp.forget₂Mon (Over T))
  haveI : IsIso
      ((CommGrp.forget₂Grp (Over T)).map (P.baseChangeToKernel t)) := by
    change IsIso (P.baseChangeToKernel t).hom
    infer_instance
  exact isIso_of_reflects_iso _ (CommGrp.forget₂Grp (Over T))

/-- Certified geometric kernels of ambient commutative group-scheme homomorphisms commute with
arbitrary base change. -/
noncomputable def baseChange (t : T ⟶ S) :
    KernelPresentation ((Over.pullback t).mapCommGrp.map f) where
  kernel := (Over.pullback t).mapCommGrp.obj P.kernel
  inclusion := (Over.pullback t).mapCommGrp.map P.inclusion
  kernelIso := asIso (P.baseChangeToKernel t)
  kernelIso_hom_kernelInclusion := P.baseChangeToKernel_comp_kernelInclusion t

@[simp]
theorem baseChange_kernel (t : T ⟶ S) :
    (P.baseChange t).kernel = (Over.pullback t).mapCommGrp.obj P.kernel :=
  rfl

@[simp]
theorem baseChange_inclusion (t : T ⟶ S) :
    (P.baseChange t).inclusion =
      (Over.pullback t).mapCommGrp.map P.inclusion :=
  rfl

end KernelPresentation

end AlgebraicGeometry.CommGroupScheme

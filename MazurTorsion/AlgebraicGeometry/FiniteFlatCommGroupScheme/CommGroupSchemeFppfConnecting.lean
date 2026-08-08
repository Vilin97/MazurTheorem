/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.CommGroupSchemeKernelPresentation
import Mathlib.CategoryTheory.Sites.Hypercover.Subcanonical

/-!
# Čech connecting classes for geometric group-scheme kernels

Let `P` be a geometric presentation of the kernel of a morphism `G ⟶ H` of ambient
commutative group schemes.  A section of `H` with actual lifts to `G` on an fppf cover produces
overlap differences in `G`.  The kernel universal property lifts each difference uniquely to
`P.kernel`; uniqueness proves naturality and the cocycle law.  Thus the construction below is an
actual Čech connecting class in global fppf `H¹`, not an abstract map supplied as an assumption.

This low-level file constructs the class associated to supplied local lifts and proves that it is
independent of every choice.  A family of local lifts therefore determines a genuine connecting
homomorphism.  Its values on globally lifted sections are trivial, and extending a boundary class
along the certified kernel inclusion is also trivial.  No finiteness or flatness property of the
three coefficient schemes is used here; those properties enter only through later quotient and
cardinality consumers.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace AlgebraicGeometry.CommGroupScheme

open CategoryTheory.PresheafOfCommGroups
open CategoryTheory.PresheafOfGroups
open scoped CategoryTheory.MonObj

universe v u

variable {S : Scheme.{u}} {G H : CommGroupScheme S} {f : G ⟶ H}

/-- The identity object of the slice, used for global sections over the base. -/
def baseObject (S : Scheme.{u}) : Over S := Over.mk (𝟙 S)

/-- Global sections of an ambient commutative group scheme over its base. -/
abbrev BasePoint (G : CommGroupScheme S) := G.Point (baseObject S)

/-- Send an ambient group-scheme cover-level class to global fppf `H¹`. -/
def fppfHOneClass (G : CommGroupScheme S)
    (𝒰 : Scheme.Cover.{v} Scheme.fppfPrecoverage S)
    (x : H1 G.commPointPresheaf 𝒰.overFamily) :
    G.FppfHOne.{v} :=
  Scheme.FppfHOne.mk 𝒰 x

/-- Pulling an ambient group-scheme cocycle to a genuine refinement does not change its global
fppf class. -/
theorem fppfHOneClass_pullback (G : CommGroupScheme S)
    (𝒰 𝒱 : Scheme.Cover.{v} Scheme.fppfPrecoverage S) (r : 𝒱.Hom 𝒰)
    (x : H1 G.commPointPresheaf 𝒰.overFamily) :
    fppfHOneClass G 𝒱 (Scheme.Cover.Hom.pullbackCommHOneHom G.commPointPresheaf r x) =
      fppfHOneClass G 𝒰 x :=
  Scheme.FppfHOne.class_pullback 𝒰 𝒱 r x

/-- Multiplication of ambient group-scheme fppf classes is computed on any supplied common
refinement of their representing covers. -/
theorem fppfHOneClass_mul_of_commonRefinement (G : CommGroupScheme S)
    (𝒰 𝒱 𝒲 : Scheme.Cover.{v} Scheme.fppfPrecoverage S)
    (r : 𝒲.Hom 𝒰) (s : 𝒲.Hom 𝒱)
    (x : H1 G.commPointPresheaf 𝒰.overFamily)
    (y : H1 G.commPointPresheaf 𝒱.overFamily) :
    fppfHOneClass G 𝒰 x * fppfHOneClass G 𝒱 y =
      fppfHOneClass G 𝒲
        (Scheme.Cover.Hom.pullbackCommHOneHom G.commPointPresheaf r x *
          Scheme.Cover.Hom.pullbackCommHOneHom G.commPointPresheaf s y) :=
  Scheme.FppfHOne.mk_mul_mk_eq_mk_of_commonRefinement
    G.commPointPresheaf 𝒰 𝒱 𝒲 r s x y

/-- Pull a represented point back along a morphism of test schemes over the base. -/
def pullPoint (G : CommGroupScheme S) {T U : Over S} (g : T ⟶ U) :
    G.Point U →* G.Point T :=
  ((commPointPresheaf G).map g.op).hom

@[simp]
theorem pullPoint_apply (G : CommGroupScheme S) {T U : Over S}
    (g : T ⟶ U) (x : G.Point U) :
    pullPoint G g x = g ≫ x :=
  rfl

@[simp]
theorem pullPoint_id (G : CommGroupScheme S) {T : Over S}
    (x : G.Point T) : pullPoint G (𝟙 T) x = x := by
  change (𝟙 T) ≫ x = x
  rw [Category.id_comp]

theorem pullPoint_comp (G : CommGroupScheme S) {T U V : Over S}
    (g : T ⟶ U) (h : U ⟶ V) (x : G.Point V) :
    pullPoint G (g ≫ h) x = pullPoint G g (pullPoint G h x) := by
  change (g ≫ h) ≫ x = g ≫ h ≫ x
  exact Category.assoc _ _ _

/-- Pullback along an isomorphism of test objects is an equivalence on the represented
commutative groups. -/
def pointMulEquivOfOverIso (G : CommGroupScheme S) {T U : Over S} (e : T ≅ U) :
    G.Point T ≃* G.Point U where
  toFun := pullPoint G e.inv
  invFun := pullPoint G e.hom
  left_inv x := by
    change e.hom ≫ e.inv ≫ x = x
    simp
  right_inv x := by
    change e.inv ≫ e.hom ≫ x = x
    simp
  map_mul' := (pullPoint G e.inv).map_mul

/-- Postcomposition by a group-scheme morphism commutes with restriction of points. -/
theorem mapPoint_pullPoint (f : G ⟶ H) {T U : Over S} (g : T ⟶ U)
    (x : G.Point U) :
    mapPoint f T (pullPoint G g x) = pullPoint H g (mapPoint f U x) := by
  exact (PresheafOfCommGroups.NatTrans.naturality_apply
    (commPointPresheafMap f) g.op x).symm

/-- The canonical map from a member of an fppf cover to the identity object of the slice. -/
def coverToBase (𝒰 : Scheme.Cover.{v} Scheme.fppfPrecoverage S) (i : 𝒰.I₀) :
    𝒰.overFamily i ⟶ baseObject S :=
  (Scheme.Cover.Hom.toOverFamilyRefinement (Scheme.FppfHOne.toIdentityCover 𝒰)).map i

/-- Restriction of a global point to one member of an fppf cover. -/
def restrictBasePoint (G : CommGroupScheme S)
    (𝒰 : Scheme.Cover.{v} Scheme.fppfPrecoverage S) (i : 𝒰.I₀)
    (x : BasePoint G) : G.Point (𝒰.overFamily i) :=
  pullPoint G (coverToBase 𝒰 i) x

/-- Actual local lifts of a global target section through an ambient group-scheme morphism. -/
structure KernelPresentation.LocalLift (P : KernelPresentation f) (q : BasePoint H) where
  /-- The genuine fppf cover on which the section lifts. -/
  cover : Scheme.Cover.{v} Scheme.fppfPrecoverage S
  /-- One source-group point on each cover member. -/
  lift (i : cover.I₀) : G.Point (cover.overFamily i)
  /-- Each local source point maps to the restriction of the original global target section. -/
  maps_to (i : cover.I₀) :
    mapPoint f (cover.overFamily i) (lift i) = restrictBasePoint H cover i q

namespace KernelPresentation

variable (P : KernelPresentation f)

/-- Pullback of the chosen kernel lift is the chosen lift of the pulled-back point; uniqueness
removes all dependence on the `Classical.choose` witnesses. -/
theorem pullPoint_liftPoint {T U : Over S} (g : T ⟶ U)
    (x : G.Point U) (hx : mapPoint f U x = 1) :
    pullPoint P.kernel g (P.liftPoint x hx) =
      P.liftPoint (pullPoint G g x) (by
        rw [mapPoint_pullPoint, hx, map_one]) := by
  apply P.inclusion_point_injective T
  rw [mapPoint_pullPoint, P.mapPoint_liftPoint, P.mapPoint_liftPoint]

namespace LocalLift

variable {P} {q : BasePoint H} (L : P.LocalLift.{v} q)

/-- The two restrictions of local lifts have the same image in the target group. -/
theorem mapPoint_pull_lift_eq (i j : L.cover.I₀) {T : Over S}
    (a : T ⟶ L.cover.overFamily i) (b : T ⟶ L.cover.overFamily j) :
    mapPoint f T (pullPoint G a (L.lift i)) =
      mapPoint f T (pullPoint G b (L.lift j)) := by
  rw [mapPoint_pullPoint, mapPoint_pullPoint, L.maps_to, L.maps_to]
  unfold restrictBasePoint
  rw [← pullPoint_comp, ← pullPoint_comp]
  apply congrArg (fun k : T ⟶ baseObject S ↦ pullPoint H k q)
  unfold baseObject
  exact Over.mkIdTerminal.hom_ext _ _

/-- The overlap difference between two local lifts. -/
def difference (i j : L.cover.I₀) {T : Over S}
    (a : T ⟶ L.cover.overFamily i) (b : T ⟶ L.cover.overFamily j) :
    G.Point T :=
  (pullPoint G a (L.lift i))⁻¹ * pullPoint G b (L.lift j)

/-- Every overlap difference is killed by the original group-scheme morphism. -/
theorem mapPoint_difference_eq_one (i j : L.cover.I₀) {T : Over S}
    (a : T ⟶ L.cover.overFamily i) (b : T ⟶ L.cover.overFamily j) :
    mapPoint f T (L.difference i j a b) = 1 := by
  rw [difference, map_mul, map_inv, L.mapPoint_pull_lift_eq i j a b,
    inv_mul_cancel]

/-- Overlap differences commute with further pullback of the test scheme. -/
theorem pullPoint_difference (i j : L.cover.I₀) {T U : Over S}
    (φ : T ⟶ U) (a : U ⟶ L.cover.overFamily i)
    (b : U ⟶ L.cover.overFamily j) :
    pullPoint G φ (L.difference i j a b) =
      L.difference i j (φ ≫ a) (φ ≫ b) := by
  rw [difference, map_mul, map_inv, ← pullPoint_comp, ← pullPoint_comp]
  rfl

/-- The actual kernel-valued Čech cocycle attached to local lifts of one target section. -/
def cocycle : OneCocycle (toGroups (commPointPresheaf P.kernel)) L.cover.overFamily where
  toOneCochain :=
    { ev := fun i j T a b ↦
        P.liftPoint (L.difference i j a b)
          (L.mapPoint_difference_eq_one i j a b)
      ev_precomp := by
        intro i j T U φ a b
        change pullPoint P.kernel φ
            (P.liftPoint (L.difference i j a b)
              (L.mapPoint_difference_eq_one i j a b)) =
          P.liftPoint (L.difference i j (φ ≫ a) (φ ≫ b))
            (L.mapPoint_difference_eq_one i j (φ ≫ a) (φ ≫ b))
        apply P.inclusion_point_injective T
        rw [mapPoint_pullPoint, P.mapPoint_liftPoint, P.mapPoint_liftPoint]
        exact L.pullPoint_difference i j φ a b }
  ev_trans i j k T a b d := by
    apply P.inclusion_point_injective T
    change mapPoint P.inclusion T
        (P.liftPoint (L.difference i j a b)
            (L.mapPoint_difference_eq_one i j a b) *
          P.liftPoint (L.difference j k b d)
            (L.mapPoint_difference_eq_one j k b d)) =
      mapPoint P.inclusion T
        (P.liftPoint (L.difference i k a d)
          (L.mapPoint_difference_eq_one i k a d))
    rw [map_mul, P.mapPoint_liftPoint, P.mapPoint_liftPoint, P.mapPoint_liftPoint]
    simp only [difference, mul_assoc, mul_inv_cancel_left]

/-- The global fppf connecting class produced by genuine local lifts and the certified kernel
universal property. -/
def boundaryClass : P.kernel.FppfHOne.{v} :=
  fppfHOneClass P.kernel L.cover L.cocycle.class

/-- Replace the chosen local lifts while keeping the same genuine cover. -/
def withLift
    (b : ∀ i : L.cover.I₀, G.Point (L.cover.overFamily i))
    (hb : ∀ i, mapPoint f (L.cover.overFamily i) (b i) =
      restrictBasePoint H L.cover i q) :
    P.LocalLift q where
  cover := L.cover
  lift := b
  maps_to := hb

/-- The pointwise gauge between two systems of local lifts on the same cover, lifted uniquely
to the certified kernel. -/
def comparisonZeroCochain
    (b : ∀ i : L.cover.I₀, G.Point (L.cover.overFamily i))
    (hb : ∀ i, mapPoint f (L.cover.overFamily i) (b i) =
      restrictBasePoint H L.cover i q) :
    (i : L.cover.I₀) → P.kernel.Point (L.cover.overFamily i) :=
  fun i ↦ P.liftPoint ((b i)⁻¹ * L.lift i) (by
    rw [map_mul, map_inv, hb, L.maps_to, inv_mul_cancel])

/-- Two choices of local lifts on one cover give cohomologous kernel cocycles. -/
theorem cocycle_isCohomologous
    (b' : ∀ i : L.cover.I₀, G.Point (L.cover.overFamily i))
    (hb' : ∀ i, mapPoint f (L.cover.overFamily i) (b' i) =
      restrictBasePoint H L.cover i q) :
    L.cocycle.IsCohomologous (L.withLift b' hb').cocycle := by
  let M : P.LocalLift q := L.withLift b' hb'
  refine ⟨L.comparisonZeroCochain b' hb', ?_⟩
  intro i j T a b
  apply P.inclusion_point_injective T
  change mapPoint P.inclusion T
      (pullPoint P.kernel a (L.comparisonZeroCochain b' hb' i) *
        P.liftPoint (L.difference i j a b)
          (L.mapPoint_difference_eq_one i j a b)) =
    mapPoint P.inclusion T
      (P.liftPoint (M.difference i j a b)
          (M.mapPoint_difference_eq_one i j a b) *
        pullPoint P.kernel b (L.comparisonZeroCochain b' hb' j))
  rw [map_mul, map_mul, mapPoint_pullPoint, mapPoint_pullPoint,
    P.mapPoint_liftPoint, P.mapPoint_liftPoint]
  dsimp only [comparisonZeroCochain, M, withLift]
  rw [P.mapPoint_liftPoint, P.mapPoint_liftPoint, map_mul, map_mul, map_inv, map_inv]
  simp only [difference, mul_assoc, mul_inv_cancel_left]

/-- Consequently the global connecting class is independent of local lifts made on a fixed
cover. -/
theorem boundaryClass_eq_withLift
    (b : ∀ i : L.cover.I₀, G.Point (L.cover.overFamily i))
    (hb : ∀ i, mapPoint f (L.cover.overFamily i) (b i) =
      restrictBasePoint H L.cover i q) :
    L.boundaryClass = (L.withLift b hb).boundaryClass := by
  exact congrArg (fppfHOneClass P.kernel L.cover)
    (L.cocycle_isCohomologous b hb).class_eq

/-- Pull a chosen system of local lifts to a genuine refinement of its fppf cover. -/
def pullback {𝒱 : Scheme.Cover.{v} Scheme.fppfPrecoverage S}
    (r : 𝒱.Hom L.cover) : P.LocalLift q where
  cover := 𝒱
  lift i :=
    let rr := Scheme.Cover.Hom.toOverFamilyRefinement r
    pullPoint G (rr.map i) (L.lift (rr.index i))
  maps_to i := by
    rw [mapPoint_pullPoint, L.maps_to]
    unfold restrictBasePoint
    rw [← pullPoint_comp]
    apply congrArg (fun k : 𝒱.overFamily i ⟶ baseObject S ↦ pullPoint H k q)
    unfold baseObject
    exact Over.mkIdTerminal.hom_ext _ _

/-- The cocycle built after refining local lifts is the actual pullback of the original
cocycle. -/
theorem cocycle_pullback {𝒱 : Scheme.Cover.{v} Scheme.fppfPrecoverage S}
    (r : 𝒱.Hom L.cover) :
    (L.pullback r).cocycle =
      (Scheme.Cover.Hom.toOverFamilyRefinement r).pullbackOneCocycle L.cocycle := by
  apply PresheafOfCommGroups.OneCocycle.ext
  apply PresheafOfGroups.OneCochain.ext
  funext i j T a b
  apply P.inclusion_point_injective T
  change mapPoint P.inclusion T
      (P.liftPoint ((L.pullback r).difference i j a b)
        ((L.pullback r).mapPoint_difference_eq_one i j a b)) =
    mapPoint P.inclusion T
      (P.liftPoint
        (L.difference
          ((Scheme.Cover.Hom.toOverFamilyRefinement r).index i)
          ((Scheme.Cover.Hom.toOverFamilyRefinement r).index j)
          (a ≫ (Scheme.Cover.Hom.toOverFamilyRefinement r).map i)
          (b ≫ (Scheme.Cover.Hom.toOverFamilyRefinement r).map j))
        (L.mapPoint_difference_eq_one
          ((Scheme.Cover.Hom.toOverFamilyRefinement r).index i)
          ((Scheme.Cover.Hom.toOverFamilyRefinement r).index j)
          (a ≫ (Scheme.Cover.Hom.toOverFamilyRefinement r).map i)
          (b ≫ (Scheme.Cover.Hom.toOverFamilyRefinement r).map j)))
  rw [P.mapPoint_liftPoint, P.mapPoint_liftPoint]
  dsimp only [difference, pullback]
  rfl

/-- Refining the cover and the chosen local lifts does not change the global connecting class. -/
theorem boundaryClass_pullback
    {𝒱 : Scheme.Cover.{v} Scheme.fppfPrecoverage S} (r : 𝒱.Hom L.cover) :
    (L.pullback r).boundaryClass = L.boundaryClass := by
  rw [boundaryClass, boundaryClass, L.cocycle_pullback r]
  exact fppfHOneClass_pullback P.kernel L.cover 𝒱 r L.cocycle.class

/-- The global connecting class is independent of both the fppf cover and all chosen local
lifts. -/
theorem boundaryClass_eq (M : P.LocalLift.{v} q) :
    L.boundaryClass = M.boundaryClass := by
  let 𝒬 : Scheme.Cover.{v} Scheme.fppfPrecoverage S := L.cover.inter M.cover
  let r : 𝒬.Hom L.cover := Scheme.Cover.interFst L.cover M.cover
  let s : 𝒬.Hom M.cover := Scheme.Cover.interSnd L.cover M.cover
  let L' : P.LocalLift q := L.pullback r
  let M' : P.LocalLift q := M.pullback s
  calc
    L.boundaryClass = L'.boundaryClass := (L.boundaryClass_pullback r).symm
    _ = M'.boundaryClass := L'.boundaryClass_eq_withLift M'.lift M'.maps_to
    _ = M.boundaryClass := M.boundaryClass_pullback s

/-- The trivial target section has its tautological lift on the identity fppf cover. -/
def one (P : KernelPresentation f) : P.LocalLift.{v} (1 : BasePoint H) where
  cover := Scheme.FppfHOne.identityCover S
  lift _ := 1
  maps_to i := by
    rw [map_one]
    unfold restrictBasePoint
    exact map_one (pullPoint H (coverToBase (Scheme.FppfHOne.identityCover S) i))

@[simp]
theorem one_cocycle (P : KernelPresentation f) :
    (LocalLift.one.{v} P).cocycle = 1 := by
  apply PresheafOfCommGroups.OneCocycle.ext
  apply PresheafOfGroups.OneCochain.ext
  funext i j T a b
  apply P.inclusion_point_injective T
  change mapPoint P.inclusion T
      (P.liftPoint ((LocalLift.one.{v} P).difference i j a b)
        ((LocalLift.one.{v} P).mapPoint_difference_eq_one i j a b)) =
    mapPoint P.inclusion T 1
  rw [P.mapPoint_liftPoint, map_one]
  change
    (pullPoint G a ((LocalLift.one.{v} P).lift i) ⁻¹ *
        pullPoint G b ((LocalLift.one.{v} P).lift j)) = 1
  have hi : (LocalLift.one.{v} P).lift i = 1 := rfl
  have hj : (LocalLift.one.{v} P).lift j = 1 := rfl
  simp only [hi, hj, map_one, inv_one, one_mul]

@[simp]
theorem one_boundaryClass (P : KernelPresentation f) :
    (LocalLift.one.{v} P).boundaryClass = 1 := by
  unfold boundaryClass
  rw [one_cocycle]
  exact Scheme.FppfHOne.mk_one _

/-- Multiply two locally lifted sections after passing to the intersection of their covers. -/
def mul {q r : BasePoint H} (L : P.LocalLift.{v} q) (M : P.LocalLift.{v} r) :
    P.LocalLift.{v} (q * r) := by
  let 𝒬 : Scheme.Cover.{v} Scheme.fppfPrecoverage S := L.cover.inter M.cover
  let pL : 𝒬.Hom L.cover := Scheme.Cover.interFst L.cover M.cover
  let pM : 𝒬.Hom M.cover := Scheme.Cover.interSnd L.cover M.cover
  let rrL := Scheme.Cover.Hom.toOverFamilyRefinement pL
  let rrM := Scheme.Cover.Hom.toOverFamilyRefinement pM
  let bL : (i : 𝒬.I₀) → G.Point (𝒬.overFamily i) :=
    fun i ↦ pullPoint G (rrL.map i) (L.lift (rrL.index i))
  let bM : (i : 𝒬.I₀) → G.Point (𝒬.overFamily i) :=
    fun i ↦ pullPoint G (rrM.map i) (M.lift (rrM.index i))
  have hbL : ∀ i, mapPoint f (𝒬.overFamily i) (bL i) =
      restrictBasePoint H 𝒬 i q := by
    intro i
    rw [mapPoint_pullPoint, L.maps_to]
    unfold restrictBasePoint
    rw [← pullPoint_comp]
    apply congrArg (fun k : 𝒬.overFamily i ⟶ baseObject S ↦ pullPoint H k q)
    unfold baseObject
    exact Over.mkIdTerminal.hom_ext _ _
  have hbM : ∀ i, mapPoint f (𝒬.overFamily i) (bM i) =
      restrictBasePoint H 𝒬 i r := by
    intro i
    rw [mapPoint_pullPoint, M.maps_to]
    unfold restrictBasePoint
    rw [← pullPoint_comp]
    apply congrArg (fun k : 𝒬.overFamily i ⟶ baseObject S ↦ pullPoint H k r)
    unfold baseObject
    exact Over.mkIdTerminal.hom_ext _ _
  exact
    { cover := 𝒬
      lift := fun i ↦ bL i * bM i
      maps_to := fun i ↦ by
        rw [map_mul, hbL, hbM]
        unfold restrictBasePoint
        rw [map_mul] }

/-- The overlap cocycle of a product of local lifts is the pointwise product of the two
pulled-back overlap cocycles on the common refinement. -/
theorem mul_cocycle {q r : BasePoint H} (L : P.LocalLift.{v} q)
    (M : P.LocalLift.{v} r) :
    (L.mul M).cocycle =
      OneCocycle.mul (commPointPresheaf P.kernel)
        (L.pullback (Scheme.Cover.interFst L.cover M.cover)).cocycle
        (M.pullback (Scheme.Cover.interSnd L.cover M.cover)).cocycle := by
  apply PresheafOfCommGroups.OneCocycle.ext
  apply PresheafOfGroups.OneCochain.ext
  funext i j T a b
  apply P.inclusion_point_injective T
  change mapPoint P.inclusion T
      (P.liftPoint ((L.mul M).difference i j a b)
        ((L.mul M).mapPoint_difference_eq_one i j a b)) =
    mapPoint P.inclusion T
      (P.liftPoint
          ((L.pullback (Scheme.Cover.interFst L.cover M.cover)).difference i j a b)
          ((L.pullback (Scheme.Cover.interFst L.cover M.cover)).mapPoint_difference_eq_one
            i j a b) *
        P.liftPoint
          ((M.pullback (Scheme.Cover.interSnd L.cover M.cover)).difference i j a b)
          ((M.pullback (Scheme.Cover.interSnd L.cover M.cover)).mapPoint_difference_eq_one
            i j a b))
  rw [P.mapPoint_liftPoint, map_mul, P.mapPoint_liftPoint, P.mapPoint_liftPoint]
  dsimp only [difference, mul, pullback]
  simp only [map_mul, mul_inv_rev]
  ac_rfl

/-- The connecting class respects multiplication.  Both sides are computed on the actual
intersection cover used to multiply the local lifts. -/
theorem mul_boundaryClass {q r : BasePoint H} (L : P.LocalLift.{v} q)
    (M : P.LocalLift.{v} r) :
    (L.mul M).boundaryClass = L.boundaryClass * M.boundaryClass := by
  let 𝒬 : Scheme.Cover.{v} Scheme.fppfPrecoverage S := L.cover.inter M.cover
  let pL : 𝒬.Hom L.cover := Scheme.Cover.interFst L.cover M.cover
  let pM : 𝒬.Hom M.cover := Scheme.Cover.interSnd L.cover M.cover
  rw [boundaryClass, L.mul_cocycle M]
  change fppfHOneClass P.kernel 𝒬
      ((OneCocycle.mul (commPointPresheaf P.kernel)
        (L.pullback pL).cocycle (M.pullback pM).cocycle).class) = _
  rw [L.cocycle_pullback pL, M.cocycle_pullback pM]
  exact (fppfHOneClass_mul_of_commonRefinement P.kernel
    L.cover M.cover 𝒬 pL pM L.cocycle.class M.cocycle.class).symm

/-- A global source section gives a local lift of its image on the identity cover. -/
def ofBasePoint (P : KernelPresentation f) (x : BasePoint G) :
    P.LocalLift.{v} (mapPoint f (baseObject S) x) where
  cover := Scheme.FppfHOne.identityCover S
  lift i := restrictBasePoint G (Scheme.FppfHOne.identityCover S) i x
  maps_to i := mapPoint_pullPoint f
    (coverToBase (Scheme.FppfHOne.identityCover S) i) x

/-- The overlap cocycle of a genuinely global lift is trivial. -/
@[simp]
theorem ofBasePoint_cocycle (P : KernelPresentation f) (x : BasePoint G) :
    (LocalLift.ofBasePoint.{v} P x).cocycle = 1 := by
  apply PresheafOfCommGroups.OneCocycle.ext
  apply PresheafOfGroups.OneCochain.ext
  funext i j T a b
  apply P.inclusion_point_injective T
  change mapPoint P.inclusion T
      (P.liftPoint ((LocalLift.ofBasePoint.{v} P x).difference i j a b)
        ((LocalLift.ofBasePoint.{v} P x).mapPoint_difference_eq_one i j a b)) =
    mapPoint P.inclusion T 1
  rw [P.mapPoint_liftPoint, map_one]
  change
    ((pullPoint G a ((LocalLift.ofBasePoint.{v} P x).lift i)) ⁻¹ *
        pullPoint G b ((LocalLift.ofBasePoint.{v} P x).lift j)) = 1
  have hij :
      pullPoint G a ((LocalLift.ofBasePoint.{v} P x).lift i) =
        pullPoint G b ((LocalLift.ofBasePoint.{v} P x).lift j) := by
    change pullPoint G a
        (pullPoint G
          (coverToBase (LocalLift.ofBasePoint.{v} P x).cover i) x) =
      pullPoint G b
        (pullPoint G
          (coverToBase (LocalLift.ofBasePoint.{v} P x).cover j) x)
    rw [← pullPoint_comp, ← pullPoint_comp]
    apply congrArg (fun k : T ⟶ baseObject S ↦ pullPoint G k x)
    unfold baseObject
    exact Over.mkIdTerminal.hom_ext _ _
  rw [hij, inv_mul_cancel]

/-- A global lift therefore has the trivial global connecting class. -/
@[simp]
theorem ofBasePoint_boundaryClass (P : KernelPresentation f) (x : BasePoint G) :
    (LocalLift.ofBasePoint.{v} P x).boundaryClass = 1 := by
  unfold boundaryClass
  rw [ofBasePoint_cocycle]
  exact Scheme.FppfHOne.mk_one _

/-- After applying the kernel inclusion to coefficients, a boundary cocycle is cohomologous to
the trivial cocycle; the original local source points are the explicit gauge. -/
theorem map_cocycle_isCohomologous_one :
    (NatTrans.mapOneCocycle
      (commPointPresheafMap P.inclusion) L.cocycle).IsCohomologous
        (1 : OneCocycle (toGroups (commPointPresheaf G)) L.cover.overFamily) := by
  refine ⟨L.lift, ?_⟩
  intro i j T a b
  change pullPoint G a (L.lift i) *
      mapPoint P.inclusion T
        (P.liftPoint (L.difference i j a b)
          (L.mapPoint_difference_eq_one i j a b)) =
    1 * pullPoint G b (L.lift j)
  rw [P.mapPoint_liftPoint]
  simp only [difference, one_mul, mul_inv_cancel_left]

/-- The induced `H¹` map along the kernel inclusion kills every constructed boundary class. -/
@[simp]
theorem fppfHOneMap_boundaryClass :
    fppfHOneMap P.inclusion L.boundaryClass = 1 := by
  unfold boundaryClass fppfHOneClass
  rw [fppfHOneMap_class]
  change fppfHOneClass G L.cover
      (NatTrans.mapOneCocycle (commPointPresheafMap P.inclusion) L.cocycle).class = 1
  rw [L.map_cocycle_isCohomologous_one.class_eq]
  exact Scheme.FppfHOne.mk_one _

end LocalLift

/-- Local surjectivity on represented points, with the actual fppf cover and local lifts retained
for every global target section. -/
structure LocallyLiftable where
  /-- A genuine local lift of each global target section. -/
  localLift (q : BasePoint H) : P.LocalLift.{v} q

namespace LocallyLiftable

variable {P : KernelPresentation f}
variable (E : P.LocallyLiftable.{v})

/-- The connecting homomorphism obtained from actual local lifts and their kernel-valued Čech
cocycles.  Independence of all choices, rather than an assumed map, supplies its group laws. -/
def boundaryHom : BasePoint H →* P.kernel.FppfHOne.{v} where
  toFun q := (E.localLift q).boundaryClass
  map_one' := by
    calc
      (E.localLift 1).boundaryClass =
          (LocalLift.one.{v} P).boundaryClass :=
        (E.localLift 1).boundaryClass_eq (LocalLift.one P)
      _ = 1 := LocalLift.one_boundaryClass P
  map_mul' q r := by
    calc
      (E.localLift (q * r)).boundaryClass =
          ((E.localLift q).mul (E.localLift r)).boundaryClass :=
        (E.localLift (q * r)).boundaryClass_eq
          ((E.localLift q).mul (E.localLift r))
      _ = (E.localLift q).boundaryClass * (E.localLift r).boundaryClass :=
        (E.localLift q).mul_boundaryClass (E.localLift r)

@[simp]
theorem boundaryHom_apply (q : BasePoint H) :
    E.boundaryHom q = (E.localLift q).boundaryClass :=
  rfl

/-- A section already lifted globally has zero boundary.  This is the checked
`image(H⁰(G)) ⊆ kernel(δ)` half of exactness at `H⁰(H)`. -/
@[simp]
theorem boundaryHom_mapPoint (x : BasePoint G) :
    E.boundaryHom (mapPoint f (baseObject S) x) = 1 := by
  calc
    E.boundaryHom (mapPoint f (baseObject S) x) =
        (LocalLift.ofBasePoint.{v} P x).boundaryClass :=
      (E.localLift (mapPoint f (baseObject S) x)).boundaryClass_eq
        (LocalLift.ofBasePoint P x)
    _ = 1 := LocalLift.ofBasePoint_boundaryClass P x

/-- Every constructed connecting class maps to zero in `H¹(G)`.  This is the checked
`image(δ) ⊆ kernel(H¹(P.kernel) → H¹(G))` half of the next exactness assertion. -/
@[simp]
theorem fppfHOneMap_boundaryHom (q : BasePoint H) :
    fppfHOneMap P.inclusion (E.boundaryHom q) = 1 :=
  (E.localLift q).fppfHOneMap_boundaryClass

/-- If a locally liftable section has trivial connecting class, an fppf refinement and a
zero-cochain gauge make its local lifts agree.  Subcanonical descent then glues those lifts to a
global source section. -/
theorem exists_source_of_boundaryHom_eq_one (q : BasePoint H)
    (hq : E.boundaryHom q = 1) :
    ∃ x : BasePoint G, mapPoint f (baseObject S) x = q := by
  let L := E.localLift q
  have hq' : L.boundaryClass = 1 := hq
  change Scheme.FppfHOne.mk L.cover L.cocycle.class = 1 at hq'
  have hq'' : Scheme.FppfHOne.mk L.cover L.cocycle.class =
      Scheme.FppfHOne.mk (Scheme.FppfHOne.identityCover S) 1 := by
    rw [Scheme.FppfHOne.mk_one]
    exact hq'
  obtain ⟨𝒲, r, _s, hrs⟩ :=
    (Scheme.FppfHOne.class_eq_iff L.cover
      (Scheme.FppfHOne.identityCover S) L.cocycle.class 1).mp hq''
  have hrs' :
      ((Scheme.Cover.Hom.toOverFamilyRefinement r).pullbackOneCocycle
        L.cocycle).class = 1 := by
    simpa only [Scheme.Cover.Hom.pullbackHOne,
      PresheafOfGroups.FamilyRefinement.pullbackHOne_class,
      PresheafOfGroups.FamilyRefinement.pullbackHOne_one] using hrs
  let M := L.pullback r
  have hM : M.cocycle.class = 1 := by
    rw [L.cocycle_pullback r]
    exact hrs'
  obtain ⟨α, hα⟩ :=
    (PresheafOfGroups.OneCocycle.class_eq_iff M.cocycle 1).mp hM
  let gauge (i : M.cover.I₀) : P.kernel.Point (M.cover.overFamily i) := α i
  let adjusted (i : M.cover.I₀) : G.Point (M.cover.overFamily i) :=
    M.lift i *
      (mapPoint P.inclusion (M.cover.overFamily i) (gauge i))⁻¹
  have hadjusted (i j : M.cover.I₀) :
      pullback.fst (M.cover.f i) (M.cover.f j) ≫ (adjusted i).left =
        pullback.snd (M.cover.f i) (M.cover.f j) ≫ (adjusted j).left := by
    let T : Over S :=
      Over.mk (pullback.fst (M.cover.f i) (M.cover.f j) ≫ M.cover.f i)
    let a : T ⟶ M.cover.overFamily i :=
      Over.homMk (pullback.fst (M.cover.f i) (M.cover.f j)) rfl
    let b : T ⟶ M.cover.overFamily j :=
      Over.homMk (pullback.snd (M.cover.f i) (M.cover.f j)) pullback.condition.symm
    have hrel := congrArg (mapPoint P.inclusion T) (hα i j a b)
    change mapPoint P.inclusion T
        (pullPoint P.kernel a (gauge i) *
          P.liftPoint (M.difference i j a b)
            (M.mapPoint_difference_eq_one i j a b)) =
      mapPoint P.inclusion T (1 * pullPoint P.kernel b (gauge j)) at hrel
    rw [map_mul, map_mul, mapPoint_pullPoint, P.mapPoint_liftPoint,
      map_one, one_mul, mapPoint_pullPoint] at hrel
    have hp : pullPoint G a (adjusted i) = pullPoint G b (adjusted j) := by
      dsimp only [adjusted]
      rw [map_mul, map_mul, map_inv, map_inv]
      rw [← hrel]
      dsimp only [LocalLift.difference]
      group
    change (a ≫ adjusted i).left = (b ≫ adjusted j).left
    exact congrArg Over.Hom.left hp
  let xleft : S ⟶ G.X.left :=
    Precoverage.ZeroHypercover.glueMorphisms M.cover
      (fun i ↦ (adjusted i).left) hadjusted
  have hxleft : xleft ≫ G.X.hom = 𝟙 S := by
    apply Precoverage.ZeroHypercover.hom_ext M.cover
    intro i
    have hglue : M.cover.f i ≫ xleft = (adjusted i).left := by
      simpa only [xleft] using
        Precoverage.ZeroHypercover.f_glueMorphisms M.cover
          (fun i ↦ (adjusted i).left) hadjusted i
    rw [← Category.assoc, hglue, Category.comp_id]
    exact (adjusted i).w
  let x : BasePoint G := Over.homMk xleft hxleft
  have hxrestrict (i : M.cover.I₀) :
      pullPoint G (coverToBase M.cover i) x = adjusted i := by
    apply Over.OverMorphism.ext
    change M.cover.f i ≫ xleft = (adjusted i).left
    simpa only [xleft] using
      Precoverage.ZeroHypercover.f_glueMorphisms M.cover
        (fun i ↦ (adjusted i).left) hadjusted i
  have hadjusted_map (i : M.cover.I₀) :
      mapPoint f (M.cover.overFamily i) (adjusted i) =
        restrictBasePoint H M.cover i q := by
    dsimp only [adjusted]
    rw [map_mul, map_inv, P.mapPoint_inclusion_eq_one, inv_one, mul_one,
      LocalLift.maps_to]
  refine ⟨x, ?_⟩
  apply Over.OverMorphism.ext
  apply Precoverage.ZeroHypercover.hom_ext M.cover
  intro i
  have hlocal :
      pullPoint H (coverToBase M.cover i)
          (mapPoint f (baseObject S) x) =
        pullPoint H (coverToBase M.cover i) q := by
    rw [← mapPoint_pullPoint, hxrestrict, hadjusted_map]
    rfl
  exact congrArg Over.Hom.left hlocal

/-- Exactness at global target sections for every locally liftable group-scheme morphism. -/
theorem boundaryHom_eq_one_iff_exists_source (q : BasePoint H) :
    E.boundaryHom q = 1 ↔
      ∃ x : BasePoint G, mapPoint f (baseObject S) x = q := by
  constructor
  · exact E.exists_source_of_boundaryHom_eq_one q
  · rintro ⟨x, rfl⟩
    exact E.boundaryHom_mapPoint x

/-- The represented-point map followed by its checked connecting homomorphism is exact. -/
theorem exact_mapPoint_boundaryHom :
    Function.MulExact (mapPoint f (baseObject S)) E.boundaryHom :=
  fun q ↦ E.boundaryHom_eq_one_iff_exists_source q

/-- A kernel-valued cocycle whose extension to the source group is trivial is the boundary of a
global target section.  A zero-cochain on a common refinement supplies source-group points;
their target images agree and glue by subcanonical fppf descent. -/
private theorem exists_boundary_of_class
    (𝒰 : Scheme.Cover.{v} Scheme.fppfPrecoverage S)
    (c : OneCocycle
      (toGroups (commPointPresheaf P.kernel)) 𝒰.overFamily)
    (hc : fppfHOneMap P.inclusion
      (fppfHOneClass P.kernel 𝒰 c.class) = 1) :
    ∃ q : BasePoint H,
      E.boundaryHom q = fppfHOneClass P.kernel 𝒰 c.class := by
  let coeffMap := commPointPresheafMap P.inclusion
  change Scheme.FppfHOne.mk 𝒰
      (NatTrans.mapOneCocycle coeffMap c).class = 1 at hc
  have hc' : Scheme.FppfHOne.mk 𝒰
      (NatTrans.mapOneCocycle coeffMap c).class =
      Scheme.FppfHOne.mk (Scheme.FppfHOne.identityCover S) 1 := by
    rw [Scheme.FppfHOne.mk_one]
    exact hc
  obtain ⟨𝒲, r, _s, hrs⟩ :=
    (Scheme.FppfHOne.class_eq_iff 𝒰
      (Scheme.FppfHOne.identityCover S)
      (NatTrans.mapOneCocycle coeffMap c).class 1).mp hc'
  let ρ := Scheme.Cover.Hom.toOverFamilyRefinement r
  let c𝒲 := ρ.pullbackOneCocycle c
  have hrs' :
      (ρ.pullbackOneCocycle (NatTrans.mapOneCocycle coeffMap c)).class = 1 := by
    simpa only [Scheme.Cover.Hom.pullbackHOne,
      FamilyRefinement.pullbackHOne_class,
      FamilyRefinement.pullbackHOne_one] using hrs
  have hmapped : (NatTrans.mapOneCocycle coeffMap c𝒲).class = 1 := by
    change
      (NatTrans.mapOneCocycle coeffMap (ρ.pullbackOneCocycle c)).class = 1
    rw [NatTrans.mapOneCocycle_pullback]
    exact hrs'
  obtain ⟨b, hb⟩ :=
    (OneCocycle.class_eq_iff (NatTrans.mapOneCocycle coeffMap c𝒲) 1).mp hmapped
  let liftLocal (i : 𝒲.I₀) : G.Point (𝒲.overFamily i) := b i
  let qLocal (i : 𝒲.I₀) : H.Point (𝒲.overFamily i) :=
    mapPoint f (𝒲.overFamily i) (liftLocal i)
  have hqLocal (i j : 𝒲.I₀) :
      pullback.fst (𝒲.f i) (𝒲.f j) ≫ (qLocal i).left =
        pullback.snd (𝒲.f i) (𝒲.f j) ≫ (qLocal j).left := by
    let T : Over S := Over.mk (pullback.fst (𝒲.f i) (𝒲.f j) ≫ 𝒲.f i)
    let a : T ⟶ 𝒲.overFamily i :=
      Over.homMk (pullback.fst (𝒲.f i) (𝒲.f j)) rfl
    let d : T ⟶ 𝒲.overFamily j :=
      Over.homMk (pullback.snd (𝒲.f i) (𝒲.f j)) pullback.condition.symm
    let kOverlap : P.kernel.Point T := c𝒲.ev i j a d
    have hrel := hb i j a d
    change pullPoint G a (liftLocal i) *
        mapPoint P.inclusion T kOverlap =
      1 * pullPoint G d (liftLocal j) at hrel
    have hp := congrArg (mapPoint f T) hrel
    rw [map_mul, map_mul, map_one, one_mul,
      mapPoint_pullPoint, mapPoint_pullPoint,
      P.mapPoint_inclusion_eq_one T kOverlap, mul_one] at hp
    change (a ≫ qLocal i).left = (d ≫ qLocal j).left
    exact congrArg Over.Hom.left hp
  let qleft : S ⟶ H.X.left :=
    Precoverage.ZeroHypercover.glueMorphisms 𝒲
      (fun i ↦ (qLocal i).left) hqLocal
  have hqleft : qleft ≫ H.X.hom = 𝟙 S := by
    apply Precoverage.ZeroHypercover.hom_ext 𝒲
    intro i
    have hglue : 𝒲.f i ≫ qleft = (qLocal i).left := by
      simpa only [qleft] using
        Precoverage.ZeroHypercover.f_glueMorphisms 𝒲
          (fun i ↦ (qLocal i).left) hqLocal i
    rw [← Category.assoc, hglue, Category.comp_id]
    exact (qLocal i).w
  let q : BasePoint H := Over.homMk qleft hqleft
  have hqrestrict (i : 𝒲.I₀) :
      pullPoint H (coverToBase 𝒲 i) q = qLocal i := by
    apply Over.OverMorphism.ext
    change 𝒲.f i ≫ qleft = (qLocal i).left
    simpa only [qleft] using
      Precoverage.ZeroHypercover.f_glueMorphisms 𝒲
        (fun i ↦ (qLocal i).left) hqLocal i
  let L : P.LocalLift.{v} q :=
    { cover := 𝒲
      lift := liftLocal
      maps_to := fun i ↦ by
        change qLocal i = restrictBasePoint H 𝒲 i q
        exact (hqrestrict i).symm }
  have hLc : L.cocycle = c𝒲 := by
    apply PresheafOfCommGroups.OneCocycle.ext
    apply PresheafOfGroups.OneCochain.ext
    funext i j T a d
    apply P.inclusion_point_injective T
    change mapPoint P.inclusion T
        (P.liftPoint (L.difference i j a d)
          (L.mapPoint_difference_eq_one i j a d)) =
      mapPoint P.inclusion T (c𝒲.ev i j a d)
    rw [P.mapPoint_liftPoint]
    have hrel := hb i j a d
    change pullPoint G a (liftLocal i) *
        mapPoint P.inclusion T (c𝒲.ev i j a d) =
      1 * pullPoint G d (liftLocal j) at hrel
    dsimp only [LocalLift.difference]
    change (pullPoint G a (liftLocal i))⁻¹ *
        pullPoint G d (liftLocal j) =
      mapPoint P.inclusion T (c𝒲.ev i j a d)
    rw [one_mul] at hrel
    rw [← hrel]
    group
  refine ⟨q, ?_⟩
  calc
    E.boundaryHom q = (E.localLift q).boundaryClass := rfl
    _ = L.boundaryClass := (E.localLift q).boundaryClass_eq L
    _ = fppfHOneClass P.kernel 𝒲 c𝒲.class := by
      rw [LocalLift.boundaryClass, hLc]
    _ = fppfHOneClass P.kernel 𝒰 c.class := by
      change Scheme.FppfHOne.mk 𝒲 c𝒲.class =
        Scheme.FppfHOne.mk 𝒰 c.class
      dsimp only [c𝒲]
      simpa only [Scheme.Cover.Hom.pullbackHOne,
        FamilyRefinement.pullbackHOne_class] using
        Scheme.FppfHOne.class_pullback 𝒰 𝒲 r c.class

/-- Every global kernel `H¹` class killed by extension to the source group is represented by a
boundary of a global target section. -/
theorem exists_boundary_of_fppfHOneMap_eq_one
    (z : P.kernel.FppfHOne.{v})
    (hz : fppfHOneMap P.inclusion z = 1) :
    ∃ q : BasePoint H, E.boundaryHom q = z := by
  induction z using Quot.inductionOn with
  | _ a =>
    rcases a with ⟨𝒰, x⟩
    induction x using Quot.inductionOn with
    | _ c => exact E.exists_boundary_of_class 𝒰 c hz

/-- A kernel `H¹` class dies in source-group `H¹` exactly when it is a connecting class. -/
theorem fppfHOneMap_eq_one_iff_exists_boundaryHom
    (z : P.kernel.FppfHOne.{v}) :
    fppfHOneMap P.inclusion z = 1 ↔
      ∃ q : BasePoint H, E.boundaryHom q = z := by
  constructor
  · exact E.exists_boundary_of_fppfHOneMap_eq_one z
  · rintro ⟨q, rfl⟩
    exact E.fppfHOneMap_boundaryHom q

/-- Exactness at kernel-valued `H¹` for every locally liftable ambient group-scheme morphism. -/
theorem exact_boundaryHom_fppfHOneMap :
    Function.MulExact E.boundaryHom (fppfHOneMap P.inclusion) :=
  fun z ↦ E.fppfHOneMap_eq_one_iff_exists_boundaryHom z

end LocallyLiftable

end KernelPresentation

end AlgebraicGeometry.CommGroupScheme

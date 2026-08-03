/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.AdmissibleCohomology
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfHOneFunctoriality

/-!
# Čech connecting classes for certified finite-flat kernels

Let `P` be the checked scheme-theoretic kernel of a morphism `G ⟶ H` of finite-flat
commutative group schemes.  A section of `H` with actual lifts to `G` on an fppf cover produces
overlap differences in `G`.  The kernel universal property lifts each difference uniquely to
`P.kernel`; uniqueness proves naturality and the cocycle law.  Thus the construction below is an
actual Čech connecting class in global fppf `H¹`, not an abstract map supplied as an assumption.

The final section records how the already-proved exactness on points fills the middle degree-zero
field of `FppfLowDegreeExactSequence`; the other low-degree terms remain explicit obligations.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

open CategoryTheory.PresheafOfCommGroups
open CategoryTheory.PresheafOfGroups
open scoped CategoryTheory.MonObj

universe v u

variable {S : Scheme.{u}} {G H : FiniteFlatCommGroupScheme S} {f : G ⟶ H}

/-- The identity object of the slice, used for global sections over the base. -/
def baseObject (S : Scheme.{u}) : Over S := Over.mk (𝟙 S)

/-- Global sections of a finite-flat group scheme over its base. -/
abbrev BasePoint (G : FiniteFlatCommGroupScheme S) := G.Point (baseObject S)

/-- Pull a represented point back along a morphism of test schemes over the base. -/
def pullPoint (G : FiniteFlatCommGroupScheme S) {T U : Over S} (g : T ⟶ U) :
    G.Point U →* G.Point T :=
  ((commPointPresheaf G).map g.op).hom

@[simp]
theorem pullPoint_apply (G : FiniteFlatCommGroupScheme S) {T U : Over S}
    (g : T ⟶ U) (x : G.Point U) :
    pullPoint G g x = g ≫ x :=
  rfl

@[simp]
theorem pullPoint_id (G : FiniteFlatCommGroupScheme S) {T : Over S}
    (x : G.Point T) : pullPoint G (𝟙 T) x = x := by
  change (𝟙 T) ≫ x = x
  rw [Category.id_comp]

theorem pullPoint_comp (G : FiniteFlatCommGroupScheme S) {T U V : Over S}
    (g : T ⟶ U) (h : U ⟶ V) (x : G.Point V) :
    pullPoint G (g ≫ h) x = pullPoint G g (pullPoint G h x) := by
  change (g ≫ h) ≫ x = g ≫ h ≫ x
  exact Category.assoc _ _ _

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
def restrictBasePoint (G : FiniteFlatCommGroupScheme S)
    (𝒰 : Scheme.Cover.{v} Scheme.fppfPrecoverage S) (i : 𝒰.I₀)
    (x : BasePoint G) : G.Point (𝒰.overFamily i) :=
  pullPoint G (coverToBase 𝒰 i) x

/-- Actual local lifts of a global target section through a finite-flat group-scheme morphism. -/
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

/-- The unique point of the certified scheme-theoretic kernel above a killed source point. -/
def liftPoint {T : Over S} (x : G.Point T) (hx : mapPoint f T x = 1) :
    P.kernel.Point T :=
  (P.existsUnique_point_lift T x hx).choose

@[simp]
theorem mapPoint_liftPoint {T : Over S} (x : G.Point T)
    (hx : mapPoint f T x = 1) :
    mapPoint P.inclusion T (P.liftPoint x hx) = x :=
  (P.existsUnique_point_lift T x hx).choose_spec.1

/-- The certified kernel inclusion is injective on every test scheme. -/
theorem inclusion_point_injective (T : Over S) :
    Function.Injective (mapPoint P.inclusion T) := by
  intro x y hxy
  apply (P.pointMulEquiv T).injective
  apply Subtype.ext
  exact hxy

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
  rw [boundaryClass, fppfHOneMap_class]
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

end LocallyLiftable

end KernelPresentation

namespace FppfQuotientPresentation

variable {G : FiniteFlatCommGroupScheme S}

/-- The quotient projection itself, regarded as a singleton fppf cover of the quotient scheme. -/
abbrev projectCover (D : FppfQuotientPresentation G) :
    Scheme.Cover.{u} Scheme.fppfPrecoverage D.quotient.scheme := by
  letI : Flat (hom D.project) := D.project_flat
  letI : Surjective (hom D.project) := D.project_surjective
  letI : LocallyOfFinitePresentation (hom D.project) := D.project_lfp
  exact (hom D.project).cover ⟨D.project_flat, D.project_lfp⟩

/-- A checked fppf quotient projection is locally surjective on represented points.  The lift is
the second projection from the actual pullback of the quotient cover along the target section. -/
def locallyLiftable (D : FppfQuotientPresentation G) :
    D.kernelPresentation.LocallyLiftable.{u} where
  localLift q := by
    letI : Precoverage.IsStableUnderBaseChange Scheme.fppfPrecoverage :=
      Scheme.instIsStableUnderBaseChangeFppfPrecoverage
    let 𝒱 := D.projectCover
    let 𝒬 := 𝒱.pullback₁ q.left
    have hq : q.left ≫ D.quotient.structureMap = (baseObject S).hom :=
      Over.w q
    exact
      { cover := 𝒬
        lift := fun _ ↦
          Over.homMk (pullback.snd q.left (hom D.project)) (by
          change pullback.snd q.left (hom D.project) ≫ G.structureMap =
            pullback.fst q.left (hom D.project)
          rw [← hom_comp_structureMap D.project, ← Category.assoc,
            ← pullback.condition, Category.assoc, hq]
          change pullback.fst q.left (hom D.project) ≫ 𝟙 S =
            pullback.fst q.left (hom D.project)
          exact Category.comp_id _)
        maps_to := fun i ↦ by
          ext
          change pullback.snd q.left (hom D.project) ≫ hom D.project =
            (coverToBase 𝒬 i).left ≫ q.left
          exact (pullback.condition :
            pullback.fst q.left (hom D.project) ≫ q.left =
              pullback.snd q.left (hom D.project) ≫ hom D.project).symm
      }

/-- The canonical connecting homomorphism of an actual checked fppf quotient presentation.  Its
value is the kernel torsor of the tautological local lifts on the pulled-back quotient cover. -/
def boundaryHom (D : FppfQuotientPresentation G) :
    BasePoint D.quotient →* D.kernelPresentation.kernel.FppfHOne.{u} :=
  D.locallyLiftable.boundaryHom

@[simp]
theorem boundaryHom_apply (D : FppfQuotientPresentation G) (q : BasePoint D.quotient) :
    D.boundaryHom q = (D.locallyLiftable.localLift q).boundaryClass :=
  rfl

/-- A globally lifted quotient section has trivial connecting class. -/
@[simp]
theorem boundaryHom_project (D : FppfQuotientPresentation G) (x : BasePoint G) :
    D.boundaryHom (mapPoint D.project (baseObject S) x) = 1 :=
  D.locallyLiftable.boundaryHom_mapPoint x

/-- The constructed quotient boundary maps to zero after extending its kernel torsor to the
middle finite-flat group scheme. -/
@[simp]
theorem fppfHOneMap_boundaryHom (D : FppfQuotientPresentation G)
    (q : BasePoint D.quotient) :
    fppfHOneMap D.kernelPresentation.inclusion (D.boundaryHom q) = 1 :=
  D.locallyLiftable.fppfHOneMap_boundaryHom q

end FppfQuotientPresentation

namespace FinitePGroup

/-- Finiteness and a certified base-`p` logarithm for an already specified commutative group.
Unlike `FinitePGroup`, this structure does not replace the carrier by an abstract type, so it is
suited to packaging the actual represented-point and fppf-cohomology groups in a consumer. -/
structure CertifiedData (p : ℕ) (A : Type u) [CommGroup A] where
  finite : Finite A
  length : ℕ
  card_eq : Nat.card A = p ^ length

/-- Package certified data while preserving the specified carrier definitionally. -/
def CertifiedData.toFinitePGroup {p : ℕ} {A : Type u} [CommGroup A]
    (D : CertifiedData p A) : FinitePGroup p where
  carrier := A
  commGroup := inferInstance
  finite := D.finite
  length := D.length
  card_eq := D.card_eq

/-- Raise a certified carrier by one universe while preserving its cardinal certificate.  This
is needed because the global Čech quotient defining fppf `H¹` lives one universe above the
represented-point groups. -/
def CertifiedData.toULiftFinitePGroup {p : ℕ} {A : Type u} [CommGroup A]
    (D : CertifiedData p A) : FinitePGroup.{u + 1} p := by
  letI : Finite A := D.finite
  exact
    { carrier := ULift.{u + 1} A
      commGroup := inferInstance
      finite := inferInstance
      length := D.length
      card_eq := by
        rw [Nat.card_congr Equiv.ulift]
        exact D.card_eq }

/-- Raise both source and target of a homomorphism by one universe. -/
def uliftMonoidHom {A B : Type u} [CommGroup A] [CommGroup B] (g : A →* B) :
    ULift.{u + 1} A →* ULift.{u + 1} B :=
  MulEquiv.ulift.symm.toMonoidHom.comp
    (g.comp MulEquiv.ulift.toMonoidHom)

/-- Use a homomorphism on the underlying value of a universe-raised source. -/
def downMonoidHom {A : Type u} {B : Type (u + 1)} [CommGroup A] [CommGroup B]
    (g : A →* B) : ULift.{u + 1} A →* B :=
  g.comp MulEquiv.ulift.toMonoidHom

/-- Multiplicative exactness is unchanged when all three terms are universe-raised. -/
theorem mulExact_ulift {A B C : Type u} [CommGroup A] [CommGroup B] [CommGroup C]
    {g : A →* B} {h : B →* C} (e : Function.MulExact g h) :
    Function.MulExact (uliftMonoidHom g) (uliftMonoidHom h) := by
  rintro ⟨y⟩
  constructor
  · intro hy
    have hy' : h y = 1 := congrArg ULift.down hy
    obtain ⟨x, hx⟩ := (e y).mp hy'
    exact ⟨ULift.up x, by
      change ULift.up (g x) = ULift.up y
      rw [hx]⟩
  · rintro ⟨⟨x⟩, hx⟩
    have hx' : g x = y := congrArg ULift.down hx
    have hy : h y = 1 := (e y).mpr ⟨x, hx'⟩
    apply ULift.ext
    exact hy

/-- Raising only the source of the first map leaves exactness at its target unchanged. -/
theorem mulExact_downMonoidHom {A : Type u} {B C : Type (u + 1)}
    [CommGroup A] [CommGroup B] [CommGroup C]
    {g : A →* B} {h : B →* C} (e : Function.MulExact g h) :
    Function.MulExact (downMonoidHom g) h := by
  intro y
  rw [e y]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨ULift.up x, rfl⟩
  · rintro ⟨⟨x⟩, hx⟩
    exact ⟨x, hx⟩

/-- Injectivity is unchanged when a homomorphism is universe-raised. -/
theorem uliftMonoidHom_injective {A B : Type u} [CommGroup A] [CommGroup B]
    {g : A →* B} (hg : Function.Injective g) :
    Function.Injective (uliftMonoidHom g) := by
  rintro ⟨x⟩ ⟨y⟩ hxy
  apply ULift.ext
  exact hg (congrArg ULift.down hxy)

end FinitePGroup

namespace FppfLowDegreeExactSequence

/-- Build the concrete five-term group sequence attached to a certified finite-flat kernel and
its constructed connecting homomorphism.  The middle `H⁰` exactness and left injectivity are
discharged by the scheme-theoretic kernel universal property.  The three descent-sensitive
remaining exactness assertions stay explicit inputs; this constructor does not disguise them as
formal consequences of the group packages. -/
def ofKernelPresentation {p : ℕ} (P : KernelPresentation f)
    (E : P.LocallyLiftable.{u})
    (kernelHZeroData : FinitePGroup.CertifiedData p (BasePoint P.kernel))
    (middleHZeroData : FinitePGroup.CertifiedData p (BasePoint G))
    (quotientHZeroData : FinitePGroup.CertifiedData p (BasePoint H))
    (kernelHOneData : FinitePGroup.CertifiedData p P.kernel.FppfHOne.{u})
    (middleHOneData : FinitePGroup.CertifiedData p G.FppfHOne.{u})
    (quotientHOneData : FinitePGroup.CertifiedData p H.FppfHOne.{u})
    (exact_quotientHZero : Function.MulExact
      (FinitePGroup.uliftMonoidHom (mapPoint f (baseObject S)))
      (FinitePGroup.downMonoidHom E.boundaryHom))
    (exact_kernelHOne : Function.MulExact
      E.boundaryHom (fppfHOneMap P.inclusion))
    (exact_middleHOne : Function.MulExact
      (fppfHOneMap P.inclusion) (fppfHOneMap f)) :
    FppfLowDegreeExactSequence.{u + 1} p where
  kernelHZero := kernelHZeroData.toULiftFinitePGroup
  middleHZero := middleHZeroData.toULiftFinitePGroup
  quotientHZero := quotientHZeroData.toULiftFinitePGroup
  kernelHOne := kernelHOneData.toFinitePGroup
  middleHOne := middleHOneData.toFinitePGroup
  quotientHOne := quotientHOneData.toFinitePGroup
  includeHZero := FinitePGroup.uliftMonoidHom
    (mapPoint P.inclusion (baseObject S))
  projectHZero := FinitePGroup.uliftMonoidHom (mapPoint f (baseObject S))
  boundary := FinitePGroup.downMonoidHom E.boundaryHom
  includeHOne := fppfHOneMap P.inclusion
  projectHOne := fppfHOneMap f
  includeHZero_injective := FinitePGroup.uliftMonoidHom_injective
    (P.inclusion_point_injective (baseObject S))
  exact_middleHZero := FinitePGroup.mulExact_ulift
    (P.point_mulExact (baseObject S))
  exact_quotientHZero := exact_quotientHZero
  exact_kernelHOne := FinitePGroup.mulExact_downMonoidHom exact_kernelHOne
  exact_middleHOne := exact_middleHOne

/-- The concrete low-degree sequence constructor for an actual fppf quotient presentation.  It
uses the quotient's pulled-back singleton cover and the resulting checked boundary homomorphism;
only the three genuinely descent-sensitive full exactness statements remain arguments. -/
def ofFppfQuotientPresentation {p : ℕ} {G : FiniteFlatCommGroupScheme S}
    (D : FppfQuotientPresentation G)
    (kernelHZeroData : FinitePGroup.CertifiedData p
      (BasePoint D.kernelPresentation.kernel))
    (middleHZeroData : FinitePGroup.CertifiedData p (BasePoint G))
    (quotientHZeroData : FinitePGroup.CertifiedData p (BasePoint D.quotient))
    (kernelHOneData : FinitePGroup.CertifiedData p
      D.kernelPresentation.kernel.FppfHOne.{u})
    (middleHOneData : FinitePGroup.CertifiedData p G.FppfHOne.{u})
    (quotientHOneData : FinitePGroup.CertifiedData p D.quotient.FppfHOne.{u})
    (exact_quotientHZero : Function.MulExact
      (FinitePGroup.uliftMonoidHom (mapPoint D.project (baseObject S)))
      (FinitePGroup.downMonoidHom D.boundaryHom))
    (exact_kernelHOne : Function.MulExact D.boundaryHom
      (fppfHOneMap D.kernelPresentation.inclusion))
    (exact_middleHOne : Function.MulExact
      (fppfHOneMap D.kernelPresentation.inclusion) (fppfHOneMap D.project)) :
    FppfLowDegreeExactSequence.{u + 1} p :=
  ofKernelPresentation D.kernelPresentation D.locallyLiftable
    kernelHZeroData middleHZeroData quotientHZeroData
    kernelHOneData middleHOneData quotientHOneData
    exact_quotientHZero exact_kernelHOne exact_middleHOne

end FppfLowDegreeExactSequence

end AlgebraicGeometry.FiniteFlatCommGroupScheme

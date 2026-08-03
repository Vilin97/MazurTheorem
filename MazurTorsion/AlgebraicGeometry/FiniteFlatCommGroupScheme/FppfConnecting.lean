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

end LocalLift

end KernelPresentation

end AlgebraicGeometry.FiniteFlatCommGroupScheme

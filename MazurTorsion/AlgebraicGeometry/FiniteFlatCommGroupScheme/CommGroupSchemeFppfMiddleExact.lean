/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.CommGroupSchemeFppfConnecting

/-!
# Middle fppf `H¹` exactness for ambient commutative group schemes

Exactness at the middle `H¹` term of a short exact sequence requires more than local lifting
of global sections over the base.  In a Čech representative, a trivialization of the projected
cocycle is a zero-cochain whose entries are sections over the members of an arbitrary fppf
cover.  Those entries must themselves lift after a common refinement.

`KernelPresentation.CoverwiseLocallyLiftable` records exactly that sheaf-local input.  It is
strictly stronger than `KernelPresentation.LocallyLiftable`, and a named adapter below produces
the latter by applying the coverwise property to the identity cover.  No representability,
flatness, or surjectivity assertion is inferred from a bare kernel presentation.

With this input, the standard Čech gauge argument proves exactness

`H¹(P.kernel) ⟶ H¹(G) ⟶ H¹(H)`.

The quasi-finite quotient module supplies the primary geometric consumer: an actual fppf
projection constructs the required coverwise lifts by pullback.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.CommGroupScheme

open CategoryTheory.PresheafOfCommGroups
open CategoryTheory.PresheafOfGroups

universe v u

variable {S : Scheme.{u}} {G H : CommGroupScheme S} {f : G ⟶ H}

/-- Gauge a represented-point one-cocycle by a represented-point zero-cochain. -/
def pointGaugeOneCocycle (G : CommGroupScheme S)
    {I : Type v} {U : I → Over S}
    (c : OneCocycle (toGroups (commPointPresheaf G)) U)
    (gauge : ∀ i : I, G.Point (U i)) :
    OneCocycle (toGroups (commPointPresheaf G)) U where
  toOneCochain :=
    { ev := fun i j T x y ↦
        pullPoint G x (gauge i) * (show G.Point T from c.ev i j x y) *
          (pullPoint G y (gauge j))⁻¹
      ev_precomp := by
        intro i j T V g x y
        change pullPoint G g
            (pullPoint G x (gauge i) * (show G.Point V from c.ev i j x y) *
              (pullPoint G y (gauge j))⁻¹) =
          pullPoint G (g ≫ x) (gauge i) *
            (show G.Point T from c.ev i j (g ≫ x) (g ≫ y)) *
              (pullPoint G (g ≫ y) (gauge j))⁻¹
        have hcev : pullPoint G g (show G.Point V from c.ev i j x y) =
            (show G.Point T from c.ev i j (g ≫ x) (g ≫ y)) := by
          exact c.ev_precomp i j g x y
        rw [map_mul, map_mul, map_inv, ← pullPoint_comp, ← pullPoint_comp, hcev] }
  ev_trans i j k T x y z := by
    let cij : G.Point T := c.ev i j x y
    let cjk : G.Point T := c.ev j k y z
    let cik : G.Point T := c.ev i k x z
    change
      (pullPoint G x (gauge i) * cij * (pullPoint G y (gauge j))⁻¹) *
          (pullPoint G y (gauge j) * cjk * (pullPoint G z (gauge k))⁻¹) =
        pullPoint G x (gauge i) * cik * (pullPoint G z (gauge k))⁻¹
    have hc : cij * cjk = cik := c.ev_trans i j k x y z
    rw [← hc]
    group

/-- A cocycle and its represented-point gauge transform define the same `H¹` class. -/
theorem pointGaugeOneCocycle_isCohomologous (G : CommGroupScheme S)
    {I : Type v} {U : I → Over S}
    (c : OneCocycle (toGroups (commPointPresheaf G)) U)
    (gauge : ∀ i : I, G.Point (U i)) :
    c.IsCohomologous (pointGaugeOneCocycle G c gauge) := by
  refine ⟨gauge, ?_⟩
  intro i j T x y
  change pullPoint G x (gauge i) * (show G.Point T from c.ev i j x y) =
    (pullPoint G x (gauge i) * (show G.Point T from c.ev i j x y) *
      (pullPoint G y (gauge j))⁻¹) * pullPoint G y (gauge j)
  group

namespace KernelPresentation

variable {G H : CommGroupScheme S} {f : G ⟶ H}

/-- Lift a source-valued cocycle killed pointwise by `f` to the supplied geometric kernel. -/
def liftOneCocycle (P : KernelPresentation f)
    {I : Type v} {U : I → Over S}
    (c : OneCocycle (toGroups (commPointPresheaf G)) U)
    (hc : ∀ (i j : I) (T : Over S) (a : T ⟶ U i) (b : T ⟶ U j),
      mapPoint f T (c.ev i j a b) = 1) :
    OneCocycle (toGroups (commPointPresheaf P.kernel)) U where
  toOneCochain :=
    { ev := fun i j T a b ↦
        P.liftPoint (show G.Point T from c.ev i j a b) (hc i j T a b)
      ev_precomp := by
        intro i j T V g a b
        change pullPoint P.kernel g
            (P.liftPoint (show G.Point V from c.ev i j a b) (hc i j V a b)) =
          P.liftPoint (show G.Point T from c.ev i j (g ≫ a) (g ≫ b))
            (hc i j T (g ≫ a) (g ≫ b))
        apply P.inclusion_point_injective T
        rw [mapPoint_pullPoint, P.mapPoint_liftPoint, P.mapPoint_liftPoint]
        exact c.ev_precomp i j g a b }
  ev_trans i j k T a b d := by
    change P.liftPoint (show G.Point T from c.ev i j a b) (hc i j T a b) *
        P.liftPoint (show G.Point T from c.ev j k b d) (hc j k T b d) =
      P.liftPoint (show G.Point T from c.ev i k a d) (hc i k T a d)
    apply P.inclusion_point_injective T
    rw [map_mul, P.mapPoint_liftPoint, P.mapPoint_liftPoint, P.mapPoint_liftPoint]
    exact c.ev_trans i j k a b d

/-- Mapping a uniquely lifted cocycle back along the kernel inclusion recovers it strictly. -/
theorem mapOneCocycle_liftOneCocycle (P : KernelPresentation f)
    {I : Type v} {U : I → Over S}
    (c : OneCocycle (toGroups (commPointPresheaf G)) U)
    (hc : ∀ (i j : I) (T : Over S) (a : T ⟶ U i) (b : T ⟶ U j),
      mapPoint f T (c.ev i j a b) = 1) :
    NatTrans.mapOneCocycle (commPointPresheafMap P.inclusion)
        (P.liftOneCocycle c hc) = c := by
  apply PresheafOfCommGroups.OneCocycle.ext
  apply PresheafOfGroups.OneCochain.ext
  funext i j T a b
  change mapPoint P.inclusion T
      (P.liftPoint (show G.Point T from c.ev i j a b) (hc i j T a b)) = c.ev i j a b
  exact P.mapPoint_liftPoint (c.ev i j a b) (hc i j T a b)

/-- A common fppf refinement on which every entry of one target-valued zero-cochain has an
actual source-valued lift. -/
structure CoverLiftData (P : KernelPresentation f)
    (U : Scheme.Cover.{v} Scheme.fppfPrecoverage S)
    (b : ∀ i : U.I₀, H.Point (U.overFamily i)) where
  /-- The common fppf refinement on which all entries lift. -/
  cover : Scheme.Cover.{v} Scheme.fppfPrecoverage S
  /-- The actual refinement map to the original cover. -/
  refinement : cover.Hom U
  /-- A source-valued lift on every member of the refinement. -/
  lift (i : cover.I₀) : G.Point (cover.overFamily i)
  /-- Each source point lifts the corresponding pullback of the zero-cochain entry. -/
  maps_to (i : cover.I₀) :
    mapPoint f (cover.overFamily i) (lift i) =
      pullPoint H
        ((Scheme.Cover.Hom.toOverFamilyRefinement refinement).map i)
        (b ((Scheme.Cover.Hom.toOverFamilyRefinement refinement).index i))

/-- Sheaf-local surjectivity in the precise form required by the middle-`H¹` gauge argument.

This is deliberately stronger than `LocallyLiftable`: the latter only treats target sections
over `S`, whereas this structure lifts every zero-cochain on every fppf cover after a common
refinement. -/
structure CoverwiseLocallyLiftable (P : KernelPresentation f) where
  /-- Produce simultaneous local lifts of an arbitrary target-valued zero-cochain. -/
  liftData (U : Scheme.Cover.{v} Scheme.fppfPrecoverage S)
      (b : ∀ i : U.I₀, H.Point (U.overFamily i)) : P.CoverLiftData U b

namespace CoverwiseLocallyLiftable

variable {P : KernelPresentation f} (E : P.CoverwiseLocallyLiftable.{v})

include E

/-- Coverwise local lifting implies local lifting of global target sections. -/
def toLocallyLiftable : P.LocallyLiftable.{v} where
  localLift q := by
    let U := Scheme.FppfHOne.identityCover S
    let b (i : U.I₀) : H.Point (U.overFamily i) := restrictBasePoint H U i q
    let D := E.liftData U b
    exact
      { cover := D.cover
        lift := D.lift
        maps_to := fun i ↦ by
          rw [D.maps_to]
          dsimp only [b]
          unfold restrictBasePoint
          rw [← pullPoint_comp]
          apply congrArg (fun k : D.cover.overFamily i ⟶ baseObject S ↦ pullPoint H k q)
          unfold baseObject
          exact Over.mkIdTerminal.hom_ext _ _ }

/-- Cover-level reverse exactness at the middle `H¹` term. -/
theorem exists_kernelClass_of_mapOneCocycle_isCohomologous_one
    (U : Scheme.Cover.{v} Scheme.fppfPrecoverage S)
    (c : OneCocycle (toGroups (commPointPresheaf G)) U.overFamily)
    (hc : (NatTrans.mapOneCocycle
      (commPointPresheafMap f) c).IsCohomologous 1) :
    ∃ z : P.kernel.FppfHOne.{v},
      fppfHOneMap P.inclusion z = fppfHOneClass G U c.class := by
  obtain ⟨b, hb⟩ := hc
  let qGauge (i : U.I₀) : H.Point (U.overFamily i) := b i
  have hb' : ∀ (i j : U.I₀) (T : Over S)
      (a : T ⟶ U.overFamily i) (d : T ⟶ U.overFamily j),
      pullPoint H a (qGauge i) *
          mapPoint f T (show G.Point T from c.ev i j a d) =
        1 * pullPoint H d (qGauge j) := by
    intro i j T a d
    exact hb i j a d
  let D := E.liftData U qGauge
  let V := D.cover
  let r : V.Hom U := D.refinement
  let rr := Scheme.Cover.Hom.toOverFamilyRefinement r
  let cV := rr.pullbackOneCocycle c
  let gauge (i : V.I₀) : G.Point (V.overFamily i) := D.lift i
  let d := pointGaugeOneCocycle G cV gauge
  have hd : ∀ (i j : V.I₀) (T : Over S)
      (a : T ⟶ V.overFamily i) (e : T ⟶ V.overFamily j),
      mapPoint f T (show G.Point T from d.ev i j a e) = 1 := by
    intro i j T a e
    have hrel := hb' (rr.index i) (rr.index j) T
      (a ≫ rr.map i) (e ≫ rr.map j)
    change mapPoint f T
        (pullPoint G a (gauge i) *
          (show G.Point T from cV.ev i j a e) *
            (pullPoint G e (gauge j))⁻¹) = 1
    rw [map_mul, map_mul, map_inv, mapPoint_pullPoint, mapPoint_pullPoint]
    rw [D.maps_to, D.maps_to, ← pullPoint_comp, ← pullPoint_comp]
    change
      pullPoint H (a ≫ rr.map i) (qGauge (rr.index i)) *
          mapPoint f T
            (show G.Point T from c.ev (rr.index i) (rr.index j)
              (a ≫ rr.map i) (e ≫ rr.map j)) *
            (pullPoint H (e ≫ rr.map j) (qGauge (rr.index j)))⁻¹ = 1
    rw [hrel]
    group
  let k := P.liftOneCocycle d hd
  refine ⟨fppfHOneClass P.kernel V k.class, ?_⟩
  unfold fppfHOneClass
  rw [fppfHOneMap_class]
  change fppfHOneClass G V
      (NatTrans.mapOneCocycle (commPointPresheafMap P.inclusion) k).class =
    fppfHOneClass G U c.class
  rw [P.mapOneCocycle_liftOneCocycle d hd]
  calc
    fppfHOneClass G V d.class = fppfHOneClass G V cV.class :=
      congrArg (fppfHOneClass G V)
        (pointGaugeOneCocycle_isCohomologous G cV gauge).class_eq.symm
    _ = fppfHOneClass G U c.class := by
      have h := fppfHOneClass_pullback G U V r c.class
      change fppfHOneClass G V
        ((Scheme.Cover.Hom.toOverFamilyRefinement r).pullbackOneCocycle c).class =
          fppfHOneClass G U c.class at h
      exact h

/-- A represented middle `H¹` class killed by `f` comes from the supplied geometric kernel. -/
theorem exists_kernelClass_of_fppfHOneMap_class_eq_one
    (U : Scheme.Cover.{v} Scheme.fppfPrecoverage S)
    (c : OneCocycle (toGroups (commPointPresheaf G)) U.overFamily)
    (hc : fppfHOneMap f (fppfHOneClass G U c.class) = 1) :
    ∃ z : P.kernel.FppfHOne.{v},
      fppfHOneMap P.inclusion z = fppfHOneClass G U c.class := by
  change fppfHOneClass H U
      (NatTrans.mapOneCocycle (commPointPresheafMap f) c).class = 1 at hc
  have hc' : Scheme.FppfHOne.mk U
      (NatTrans.mapOneCocycle (commPointPresheafMap f) c).class =
      Scheme.FppfHOne.mk (Scheme.FppfHOne.identityCover S) 1 := by
    rw [Scheme.FppfHOne.mk_one]
    exact hc
  obtain ⟨W, r, _s, hrs⟩ :=
    (Scheme.FppfHOne.class_eq_iff U (Scheme.FppfHOne.identityCover S)
      (NatTrans.mapOneCocycle (commPointPresheafMap f) c).class 1).mp hc'
  let rr := Scheme.Cover.Hom.toOverFamilyRefinement r
  let cW := rr.pullbackOneCocycle c
  have hrs' :
      (rr.pullbackOneCocycle
        (NatTrans.mapOneCocycle (commPointPresheafMap f) c)).class = 1 := by
    simpa only [Scheme.Cover.Hom.pullbackHOne,
      FamilyRefinement.pullbackHOne_class,
      FamilyRefinement.pullbackHOne_one] using hrs
  have hmap :
      (NatTrans.mapOneCocycle (commPointPresheafMap f) cW).class = 1 := by
    dsimp only [cW]
    rw [NatTrans.mapOneCocycle_pullback]
    exact hrs'
  have hcoh :
      (NatTrans.mapOneCocycle (commPointPresheafMap f) cW).IsCohomologous 1 :=
    (OneCocycle.class_eq_iff _ 1).mp hmap
  obtain ⟨z, hz⟩ :=
    E.exists_kernelClass_of_mapOneCocycle_isCohomologous_one W cW hcoh
  refine ⟨z, hz.trans ?_⟩
  have h := fppfHOneClass_pullback G U W r c.class
  change fppfHOneClass G W
      ((Scheme.Cover.Hom.toOverFamilyRefinement r).pullbackOneCocycle c).class =
    fppfHOneClass G U c.class at h
  exact h

/-- Reverse exactness at the middle global `H¹` term for an arbitrary represented class. -/
theorem exists_kernelClass_of_fppfHOneMap_eq_one
    (z : G.FppfHOne.{v}) (hz : fppfHOneMap f z = 1) :
    ∃ y : P.kernel.FppfHOne.{v}, fppfHOneMap P.inclusion y = z := by
  induction z using Quot.inductionOn with
  | _ a =>
      rcases a with ⟨U, x⟩
      induction x using Quot.inductionOn with
      | _ c => exact E.exists_kernelClass_of_fppfHOneMap_class_eq_one U c hz

omit E

/-- Extending a kernel torsor to `G` and then along `f` gives the trivial torsor. -/
@[simp]
theorem fppfHOneMap_f_fppfHOneMap_inclusion
    (z : P.kernel.FppfHOne.{v}) :
    fppfHOneMap f (fppfHOneMap P.inclusion z) = 1 := by
  induction z using Quot.inductionOn with
  | _ a =>
      rcases a with ⟨U, x⟩
      induction x using Quot.inductionOn with
      | _ c =>
          change fppfHOneClass H U
            (NatTrans.mapOneCocycle (commPointPresheafMap f)
              (NatTrans.mapOneCocycle
                (commPointPresheafMap P.inclusion) c)).class = 1
          have hmap :
              NatTrans.mapOneCocycle (commPointPresheafMap f)
                (NatTrans.mapOneCocycle
                  (commPointPresheafMap P.inclusion) c) = 1 := by
            apply PresheafOfCommGroups.OneCocycle.ext
            apply PresheafOfGroups.OneCochain.ext
            funext i j T a b
            change mapPoint f T
              (mapPoint P.inclusion T
                (show P.kernel.Point T from c.ev i j a b)) = 1
            exact P.mapPoint_inclusion_eq_one T _
          rw [hmap]
          exact Scheme.FppfHOne.mk_one U

include E

/-- Middle `H¹` kernel membership is equivalent to coming from the geometric kernel. -/
theorem fppfHOneMap_eq_one_iff_exists_kernelClass (z : G.FppfHOne.{v}) :
    fppfHOneMap f z = 1 ↔
      ∃ y : P.kernel.FppfHOne.{v}, fppfHOneMap P.inclusion y = z := by
  constructor
  · exact E.exists_kernelClass_of_fppfHOneMap_eq_one z
  · rintro ⟨y, rfl⟩
    exact fppfHOneMap_f_fppfHOneMap_inclusion y

/-- Exactness at the middle global `H¹` term from honest coverwise local lifting. -/
theorem exact_fppfHOneMap_inclusion_f :
    Function.MulExact
      (fppfHOneMap P.inclusion : P.kernel.FppfHOne.{v} →* G.FppfHOne.{v})
      (fppfHOneMap f : G.FppfHOne.{v} →* H.FppfHOne.{v}) :=
  fun z ↦ E.fppfHOneMap_eq_one_iff_exists_kernelClass z

end CoverwiseLocallyLiftable

end KernelPresentation

end AlgebraicGeometry.CommGroupScheme

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.AdmissibleCohomology
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.CommGroupSchemeFppfMiddleExact
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfConnecting
import Mathlib.CategoryTheory.Sites.Hypercover.Subcanonical

/-!
# Quotient connecting homomorphisms and the low-degree sequence

An actual fppf quotient projection is itself a singleton fppf cover.  Pulling that cover back
along a global quotient section supplies canonical local lifts, so the choice-independent
construction in `FppfConnecting` gives the genuine connecting homomorphism.  This bridge also
packages the represented-point groups and global fppf `H¹` groups into the existing finite
`p`-group low-degree sequence.

The certified kernel property proves left injectivity and exactness at the middle degree-zero
term.  Fppf descent proves exactness at the quotient degree-zero term by gluing a gauged system
of local lifts.  A second descent argument proves exactness at the kernel `H¹` term by gluing the
quotient images of a trivializing zero-cochain.  A third descent argument lifts a trivializing
quotient-valued gauge and proves exactness at the middle `H¹` term.  Thus the concrete quotient
presentation supplies every exactness assertion in the low-degree sequence.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

universe u

variable {S : Scheme.{u}} {G H : FiniteFlatCommGroupScheme S} {f : G ⟶ H}

/-- Gauge a represented-point one-cocycle by a represented-point zero-cochain. -/
def pointGaugeOneCocycle (G : FiniteFlatCommGroupScheme S)
    {I : Type u} {U : I → Over S}
    (c : PresheafOfGroups.OneCocycle
      (PresheafOfCommGroups.toGroups (commPointPresheaf G)) U)
    (gauge : ∀ i : I, G.Point (U i)) :
    PresheafOfGroups.OneCocycle
      (PresheafOfCommGroups.toGroups (commPointPresheaf G)) U where
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
      (pullPoint G x (gauge i) *
          cij *
            (pullPoint G y (gauge j))⁻¹) *
        (pullPoint G y (gauge j) *
          cjk *
            (pullPoint G z (gauge k))⁻¹) =
      pullPoint G x (gauge i) *
        cik *
          (pullPoint G z (gauge k))⁻¹
    have hc : cij * cjk = cik := c.ev_trans i j k x y z
    rw [← hc]
    group

/-- A cocycle and any of its represented-point gauge transforms are cohomologous via the
displayed zero-cochain. -/
theorem pointGaugeOneCocycle_isCohomologous (G : FiniteFlatCommGroupScheme S)
    {I : Type u} {U : I → Over S}
    (c : PresheafOfGroups.OneCocycle
      (PresheafOfCommGroups.toGroups (commPointPresheaf G)) U)
    (gauge : ∀ i : I, G.Point (U i)) :
    c.IsCohomologous (pointGaugeOneCocycle G c gauge) := by
  refine ⟨gauge, ?_⟩
  intro i j T x y
  change pullPoint G x (gauge i) * (show G.Point T from c.ev i j x y) =
    (pullPoint G x (gauge i) * (show G.Point T from c.ev i j x y) *
      (pullPoint G y (gauge j))⁻¹) * pullPoint G y (gauge j)
  group

namespace KernelPresentation

variable {G H : FiniteFlatCommGroupScheme S} {f : G ⟶ H}

/-- A `G`-valued one-cocycle whose values are pointwise killed by `f` lifts uniquely to a
one-cocycle valued in a certified scheme-theoretic kernel of `f`.  Naturality and the cocycle
law follow from uniqueness of kernel lifts on every test scheme. -/
def liftOneCocycle (P : KernelPresentation f)
    {I : Type u} {U : I → Over S}
    (c : PresheafOfGroups.OneCocycle
      (PresheafOfCommGroups.toGroups (commPointPresheaf G)) U)
    (hc : ∀ (i j : I) (T : Over S) (a : T ⟶ U i) (b : T ⟶ U j),
      mapPoint f T (c.ev i j a b) = 1) :
    PresheafOfGroups.OneCocycle
      (PresheafOfCommGroups.toGroups (commPointPresheaf P.kernel)) U where
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

/-- Mapping the uniquely lifted cocycle back along the kernel inclusion recovers the original
cocycle strictly. -/
theorem mapOneCocycle_liftOneCocycle (P : KernelPresentation f)
    {I : Type u} {U : I → Over S}
    (c : PresheafOfGroups.OneCocycle
      (PresheafOfCommGroups.toGroups (commPointPresheaf G)) U)
    (hc : ∀ (i j : I) (T : Over S) (a : T ⟶ U i) (b : T ⟶ U j),
      mapPoint f T (c.ev i j a b) = 1) :
    PresheafOfCommGroups.NatTrans.mapOneCocycle
        (commPointPresheafMap P.inclusion) (P.liftOneCocycle c hc) = c := by
  apply PresheafOfCommGroups.OneCocycle.ext
  apply PresheafOfGroups.OneCochain.ext
  funext i j T a b
  change mapPoint P.inclusion T
      (P.liftPoint (show G.Point T from c.ev i j a b) (hc i j T a b)) = c.ev i j a b
  exact P.mapPoint_liftPoint (c.ev i j a b) (hc i j T a b)

end KernelPresentation

section FiniteConnectingCompatibility

/- These private downstream consumers guard the constructor and eliminator names generated by
the original finite-flat structures.  The finite compatibility facade must keep these exact call
patterns compiling even though the implementation now delegates to the ambient group-scheme
connecting construction. -/

variable {P : KernelPresentation f} {q : BasePoint H}

private def rebuildLocalLiftRec (L : P.LocalLift.{u} q) : P.LocalLift.{u} q :=
  KernelPresentation.LocalLift.rec
    (fun cover lift maps_to => KernelPresentation.LocalLift.mk cover lift maps_to) L

private def rebuildLocalLiftRecOn (L : P.LocalLift.{u} q) : P.LocalLift.{u} q :=
  KernelPresentation.LocalLift.recOn L
    (fun cover lift maps_to => KernelPresentation.LocalLift.mk cover lift maps_to)

private def rebuildLocalLiftCasesOn (L : P.LocalLift.{u} q) : P.LocalLift.{u} q :=
  KernelPresentation.LocalLift.casesOn L
    (fun cover lift maps_to => KernelPresentation.LocalLift.mk cover lift maps_to)

private def rebuildLocallyLiftableRec
    (E : P.LocallyLiftable.{u}) : P.LocallyLiftable.{u} :=
  KernelPresentation.LocallyLiftable.rec
    (fun localLift => KernelPresentation.LocallyLiftable.mk localLift) E

private def rebuildLocallyLiftableRecOn
    (E : P.LocallyLiftable.{u}) : P.LocallyLiftable.{u} :=
  KernelPresentation.LocallyLiftable.recOn E
    (fun localLift => KernelPresentation.LocallyLiftable.mk localLift)

private def rebuildLocallyLiftableCasesOn
    (E : P.LocallyLiftable.{u}) : P.LocallyLiftable.{u} :=
  KernelPresentation.LocallyLiftable.casesOn E
    (fun localLift => KernelPresentation.LocallyLiftable.mk localLift)

end FiniteConnectingCompatibility

namespace FppfQuotientPresentation

variable {G : FiniteFlatCommGroupScheme S}

open CategoryTheory.PresheafOfCommGroups
open CategoryTheory.PresheafOfGroups

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

/-- Refine an fppf cover so that every member of a quotient-valued zero-cochain acquires a
lift through the quotient projection.  Each component is refined by the pullback of the actual
singleton quotient cover. -/
noncomputable def gaugeLiftCover (D : FppfQuotientPresentation G)
    (U : Scheme.Cover.{u} Scheme.fppfPrecoverage S)
    (b : ∀ i : U.I₀, D.quotient.Point (U.overFamily i)) :
    Scheme.Cover.{u} Scheme.fppfPrecoverage S :=
  U.bind fun i ↦ D.projectCover.pullback₁ (b i).left

/-- The composite gauge-lifting cover genuinely refines the original cover. -/
def gaugeLiftCoverHom (D : FppfQuotientPresentation G)
    (U : Scheme.Cover.{u} Scheme.fppfPrecoverage S)
    (b : ∀ i : U.I₀, D.quotient.Point (U.overFamily i)) :
    (D.gaugeLiftCover U b).Hom U where
  s₀ ij := ij.1
  h₀ ij := (D.projectCover.pullback₁ (b ij.1).left).f ij.2
  w₀ _ := rfl

/-- The tautological lift of a quotient-valued zero-cochain on its gauge-lifting cover. -/
def gaugeLift (D : FppfQuotientPresentation G)
    (U : Scheme.Cover.{u} Scheme.fppfPrecoverage S)
    (b : ∀ i : U.I₀, D.quotient.Point (U.overFamily i))
    (ij : (D.gaugeLiftCover U b).I₀) :
    G.Point ((D.gaugeLiftCover U b).overFamily ij) :=
  Over.homMk (pullback.snd (b ij.1).left (hom D.project)) (by
    change pullback.snd (b ij.1).left (hom D.project) ≫ G.structureMap =
      pullback.fst (b ij.1).left (hom D.project) ≫ U.f ij.1
    rw [← hom_comp_structureMap D.project, ← Category.assoc,
      ← pullback.condition, Category.assoc, Over.w (b ij.1)]
    rfl)

/-- The tautological gauge lift maps to the pullback of the original quotient-valued
zero-cochain. -/
theorem mapPoint_gaugeLift (D : FppfQuotientPresentation G)
    (U : Scheme.Cover.{u} Scheme.fppfPrecoverage S)
    (b : ∀ i : U.I₀, D.quotient.Point (U.overFamily i))
    (ij : (D.gaugeLiftCover U b).I₀) :
    mapPoint D.project ((D.gaugeLiftCover U b).overFamily ij) (D.gaugeLift U b ij) =
      pullPoint D.quotient
        ((Scheme.Cover.Hom.toOverFamilyRefinement (D.gaugeLiftCoverHom U b)).map ij)
        (b ((Scheme.Cover.Hom.toOverFamilyRefinement
          (D.gaugeLiftCoverHom U b)).index ij)) := by
  apply Over.OverMorphism.ext
  change pullback.snd (b ij.1).left (hom D.project) ≫ hom D.project =
    pullback.fst (b ij.1).left (hom D.project) ≫ (b ij.1).left
  exact pullback.condition.symm

/-- A checked finite-flat fppf quotient supplies the ambient coverwise lifting input.  This
adapter is a downstream API check: it retains the actual quotient projection and its pullback
cover, rather than replacing the quotient by an abstract representable cokernel. -/
def coverwiseLocallyLiftable (D : FppfQuotientPresentation G) :
    D.kernelPresentation.toCommGroupScheme.CoverwiseLocallyLiftable.{u} where
  liftData U b :=
    { cover := D.gaugeLiftCover U b
      refinement := D.gaugeLiftCoverHom U b
      lift := D.gaugeLift U b
      maps_to := D.mapPoint_gaugeLift U b }

/-- Cover-level reverse exactness at the middle `H¹` term.  If the projected cocycle is
cohomologous to one on its current cover, refine by the pulled-back quotient cover, lift the
trivializing gauge, and take the uniquely kernel-valued gauge transform. -/
theorem exists_kernelClass_of_mapOneCocycle_isCohomologous_one
    (D : FppfQuotientPresentation G)
    (U : Scheme.Cover.{u} Scheme.fppfPrecoverage S)
    (c : PresheafOfGroups.OneCocycle
      (PresheafOfCommGroups.toGroups (commPointPresheaf G)) U.overFamily)
    (hc : (PresheafOfCommGroups.NatTrans.mapOneCocycle
      (commPointPresheafMap D.project) c).IsCohomologous 1) :
    ∃ z : D.kernelPresentation.kernel.FppfHOne.{u},
      fppfHOneMap D.kernelPresentation.inclusion z =
        fppfHOneClass G U c.class := by
  obtain ⟨b, hb⟩ := hc
  let qGauge (i : U.I₀) : D.quotient.Point (U.overFamily i) := b i
  have hb' : ∀ (i j : U.I₀) (T : Over S)
      (a : T ⟶ U.overFamily i) (d : T ⟶ U.overFamily j),
      pullPoint D.quotient a (qGauge i) *
          mapPoint D.project T (show G.Point T from c.ev i j a d) =
        1 * pullPoint D.quotient d (qGauge j) := by
    intro i j T a d
    exact hb i j a d
  let V := D.gaugeLiftCover U qGauge
  let r : V.Hom U := D.gaugeLiftCoverHom U qGauge
  let rr := Scheme.Cover.Hom.toOverFamilyRefinement r
  let cV := rr.pullbackOneCocycle c
  let gauge (i : V.I₀) : G.Point (V.overFamily i) := D.gaugeLift U qGauge i
  let d := pointGaugeOneCocycle G cV gauge
  have hd : ∀ (i j : V.I₀) (T : Over S)
      (a : T ⟶ V.overFamily i) (e : T ⟶ V.overFamily j),
      mapPoint D.project T (show G.Point T from d.ev i j a e) = 1 := by
    intro i j T a e
    have hrel := hb' (rr.index i) (rr.index j) T
      (a ≫ rr.map i) (e ≫ rr.map j)
    change mapPoint D.project T
        (pullPoint G a (gauge i) *
          (show G.Point T from cV.ev i j a e) *
            (pullPoint G e (gauge j))⁻¹) = 1
    rw [map_mul, map_mul, map_inv, mapPoint_pullPoint, mapPoint_pullPoint]
    rw [D.mapPoint_gaugeLift U qGauge, D.mapPoint_gaugeLift U qGauge]
    rw [← pullPoint_comp, ← pullPoint_comp]
    change
      pullPoint D.quotient (a ≫ rr.map i) (qGauge (rr.index i)) *
          mapPoint D.project T
            (show G.Point T from c.ev (rr.index i) (rr.index j)
              (a ≫ rr.map i) (e ≫ rr.map j)) *
            (pullPoint D.quotient (e ≫ rr.map j) (qGauge (rr.index j)))⁻¹ = 1
    rw [hrel]
    group
  let k := D.kernelPresentation.liftOneCocycle d hd
  refine ⟨fppfHOneClass D.kernelPresentation.kernel V k.class, ?_⟩
  rw [fppfHOneMap_class]
  change fppfHOneClass G V
      (PresheafOfCommGroups.NatTrans.mapOneCocycle
        (commPointPresheafMap D.kernelPresentation.inclusion) k).class =
    fppfHOneClass G U c.class
  rw [D.kernelPresentation.mapOneCocycle_liftOneCocycle d hd]
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

/-- A represented global `H¹(G)` class killed by the quotient map comes from the kernel after
passing to the common refinement which witnesses global triviality. -/
theorem exists_kernelClass_of_fppfHOneMap_class_eq_one
    (D : FppfQuotientPresentation G)
    (U : Scheme.Cover.{u} Scheme.fppfPrecoverage S)
    (c : PresheafOfGroups.OneCocycle
      (PresheafOfCommGroups.toGroups (commPointPresheaf G)) U.overFamily)
    (hc : fppfHOneMap D.project (fppfHOneClass G U c.class) = 1) :
    ∃ z : D.kernelPresentation.kernel.FppfHOne.{u},
      fppfHOneMap D.kernelPresentation.inclusion z =
        fppfHOneClass G U c.class := by
  change fppfHOneClass D.quotient U
      (PresheafOfCommGroups.NatTrans.mapOneCocycle
        (commPointPresheafMap D.project) c).class = 1 at hc
  have hc' : Scheme.FppfHOne.mk U
      (PresheafOfCommGroups.NatTrans.mapOneCocycle
        (commPointPresheafMap D.project) c).class =
      Scheme.FppfHOne.mk (Scheme.FppfHOne.identityCover S) 1 := by
    rw [Scheme.FppfHOne.mk_one]
    exact hc
  obtain ⟨W, r, s, hrs⟩ :=
    (Scheme.FppfHOne.class_eq_iff U (Scheme.FppfHOne.identityCover S)
      (PresheafOfCommGroups.NatTrans.mapOneCocycle
        (commPointPresheafMap D.project) c).class 1).mp hc'
  let rr := Scheme.Cover.Hom.toOverFamilyRefinement r
  let cW := rr.pullbackOneCocycle c
  have hrs' :
      (rr.pullbackOneCocycle
        (PresheafOfCommGroups.NatTrans.mapOneCocycle
          (commPointPresheafMap D.project) c)).class = 1 := by
    simpa only [Scheme.Cover.Hom.pullbackHOne,
      PresheafOfGroups.FamilyRefinement.pullbackHOne_class,
      PresheafOfGroups.FamilyRefinement.pullbackHOne_one] using hrs
  have hmap :
      (PresheafOfCommGroups.NatTrans.mapOneCocycle
        (commPointPresheafMap D.project) cW).class = 1 := by
    dsimp only [cW]
    rw [PresheafOfCommGroups.NatTrans.mapOneCocycle_pullback]
    exact hrs'
  have hcoh :
      (PresheafOfCommGroups.NatTrans.mapOneCocycle
        (commPointPresheafMap D.project) cW).IsCohomologous 1 :=
    (PresheafOfGroups.OneCocycle.class_eq_iff _ 1).mp hmap
  obtain ⟨z, hz⟩ := D.exists_kernelClass_of_mapOneCocycle_isCohomologous_one W cW hcoh
  refine ⟨z, hz.trans ?_⟩
  have h := fppfHOneClass_pullback G U W r c.class
  change fppfHOneClass G W
      ((Scheme.Cover.Hom.toOverFamilyRefinement r).pullbackOneCocycle c).class =
    fppfHOneClass G U c.class at h
  exact h

/-- Reverse exactness at the middle global `H¹` term, for an arbitrary class represented in
the common-refinement quotient. -/
theorem exists_kernelClass_of_fppfHOneMap_eq_one
    (D : FppfQuotientPresentation G) (z : G.FppfHOne.{u})
    (hz : fppfHOneMap D.project z = 1) :
    ∃ y : D.kernelPresentation.kernel.FppfHOne.{u},
      fppfHOneMap D.kernelPresentation.inclusion y = z := by
  induction z using Quot.inductionOn with
  | _ a =>
      rcases a with ⟨U, x⟩
      induction x using Quot.inductionOn with
      | _ c => exact D.exists_kernelClass_of_fppfHOneMap_class_eq_one U c hz

/-- Extending a kernel torsor to the middle group scheme and then to the quotient gives the
trivial torsor.  This is the direct image-in-kernel half of middle-`H¹` exactness. -/
@[simp]
theorem fppfHOneMap_project_fppfHOneMap_inclusion
    (D : FppfQuotientPresentation G)
    (z : D.kernelPresentation.kernel.FppfHOne.{u}) :
    fppfHOneMap D.project
      (fppfHOneMap D.kernelPresentation.inclusion z) = 1 := by
  induction z using Quot.inductionOn with
  | _ a =>
      rcases a with ⟨U, x⟩
      induction x using Quot.inductionOn with
      | _ c =>
          change fppfHOneClass D.quotient U
            (PresheafOfCommGroups.NatTrans.mapOneCocycle
              (commPointPresheafMap D.project)
              (PresheafOfCommGroups.NatTrans.mapOneCocycle
                (commPointPresheafMap D.kernelPresentation.inclusion) c)).class = 1
          have hmap :
              PresheafOfCommGroups.NatTrans.mapOneCocycle
                (commPointPresheafMap D.project)
                (PresheafOfCommGroups.NatTrans.mapOneCocycle
                  (commPointPresheafMap D.kernelPresentation.inclusion) c) = 1 := by
            apply PresheafOfCommGroups.OneCocycle.ext
            apply PresheafOfGroups.OneCochain.ext
            funext i j T a b
            change mapPoint D.project T
              (mapPoint D.kernelPresentation.inclusion T
                (show D.kernelPresentation.kernel.Point T from c.ev i j a b)) = 1
            exact D.kernelPresentation.mapPoint_inclusion_eq_one T _
          rw [hmap]
          exact Scheme.FppfHOne.mk_one U

/-- A middle `H¹` class maps trivially to the quotient if and only if it is induced from a
kernel `H¹` class. -/
theorem fppfHOneMap_project_eq_one_iff_exists_kernelClass
    (D : FppfQuotientPresentation G) (z : G.FppfHOne.{u}) :
    fppfHOneMap D.project z = 1 ↔
      ∃ y : D.kernelPresentation.kernel.FppfHOne.{u},
        fppfHOneMap D.kernelPresentation.inclusion y = z := by
  constructor
  · exact D.exists_kernelClass_of_fppfHOneMap_eq_one z
  · rintro ⟨y, rfl⟩
    exact D.fppfHOneMap_project_fppfHOneMap_inclusion y

/-- Exactness of the global fppf `H¹` sequence at the middle group scheme for every checked
fppf quotient presentation. -/
theorem exact_fppfHOneMap_inclusion_project (D : FppfQuotientPresentation G) :
    Function.MulExact
      (fppfHOneMap D.kernelPresentation.inclusion :
        D.kernelPresentation.kernel.FppfHOne.{u} →* G.FppfHOne.{u})
      (fppfHOneMap D.project : G.FppfHOne.{u} →* D.quotient.FppfHOne.{u}) :=
  fun z ↦ D.fppfHOneMap_project_eq_one_iff_exists_kernelClass z

/-- The ambient coverwise theorem recovers the established finite-flat middle-`H¹` exactness
with the original projection and kernel inclusion definitionally unchanged. -/
theorem exact_fppfHOneMap_inclusion_project_via_ambient
    (D : FppfQuotientPresentation G) :
    Function.MulExact
      (fppfHOneMap D.kernelPresentation.inclusion :
        D.kernelPresentation.kernel.FppfHOne.{u} →* G.FppfHOne.{u})
      (fppfHOneMap D.project : G.FppfHOne.{u} →* D.quotient.FppfHOne.{u}) :=
  D.coverwiseLocallyLiftable.exact_fppfHOneMap_inclusion_f

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

/-- If the connecting class of a quotient section is trivial, a Čech gauge makes its local
lifts agree after an fppf refinement, and subcanonical descent glues them to a global lift. -/
theorem exists_project_of_boundaryHom_eq_one
    (D : FppfQuotientPresentation G) (q : BasePoint D.quotient)
    (hq : D.boundaryHom q = 1) :
    ∃ x : BasePoint G, mapPoint D.project (baseObject S) x = q := by
  let L := D.locallyLiftable.localLift q
  have hq' : L.boundaryClass = 1 := hq
  change Scheme.FppfHOne.mk L.cover L.cocycle.class = 1 at hq'
  have hq'' : Scheme.FppfHOne.mk L.cover L.cocycle.class =
      Scheme.FppfHOne.mk (Scheme.FppfHOne.identityCover S) 1 := by
    rw [Scheme.FppfHOne.mk_one]
    exact hq'
  obtain ⟨𝒲, r, s, hrs⟩ :=
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
  let gauge (i : M.cover.I₀) :
      D.kernelPresentation.kernel.Point (M.cover.overFamily i) := α i
  let adjusted (i : M.cover.I₀) : G.Point (M.cover.overFamily i) :=
    M.lift i *
      (mapPoint D.kernelPresentation.inclusion (M.cover.overFamily i) (gauge i))⁻¹
  have hadjusted (i j : M.cover.I₀) :
      pullback.fst (M.cover.f i) (M.cover.f j) ≫ (adjusted i).left =
        pullback.snd (M.cover.f i) (M.cover.f j) ≫ (adjusted j).left := by
    let T : Over S :=
      Over.mk (pullback.fst (M.cover.f i) (M.cover.f j) ≫ M.cover.f i)
    let a : T ⟶ M.cover.overFamily i :=
      Over.homMk (pullback.fst (M.cover.f i) (M.cover.f j)) rfl
    let b : T ⟶ M.cover.overFamily j :=
      Over.homMk (pullback.snd (M.cover.f i) (M.cover.f j)) pullback.condition.symm
    have hrel := congrArg
      (CommGroupScheme.mapPoint D.kernelPresentation.toCommGroupScheme.inclusion T)
      (hα i j a b)
    change CommGroupScheme.mapPoint D.kernelPresentation.toCommGroupScheme.inclusion T
        (CommGroupScheme.pullPoint D.kernelPresentation.kernel.obj a (gauge i) *
          D.kernelPresentation.toCommGroupScheme.liftPoint (M.difference i j a b)
            (CommGroupScheme.KernelPresentation.LocalLift.mapPoint_difference_eq_one
              M i j a b)) =
      CommGroupScheme.mapPoint D.kernelPresentation.toCommGroupScheme.inclusion T
        (1 * CommGroupScheme.pullPoint D.kernelPresentation.kernel.obj b (gauge j)) at hrel
    rw [map_mul, map_mul, CommGroupScheme.mapPoint_pullPoint,
      D.kernelPresentation.toCommGroupScheme.mapPoint_liftPoint, map_one, one_mul,
      CommGroupScheme.mapPoint_pullPoint] at hrel
    have hp : CommGroupScheme.pullPoint G.obj a (adjusted i) =
        CommGroupScheme.pullPoint G.obj b (adjusted j) := by
      dsimp only [adjusted]
      change CommGroupScheme.pullPoint G.obj a
          (M.lift i *
            (CommGroupScheme.mapPoint D.kernelPresentation.toCommGroupScheme.inclusion
              (M.cover.overFamily i) (gauge i))⁻¹) =
        CommGroupScheme.pullPoint G.obj b
          (M.lift j *
            (CommGroupScheme.mapPoint D.kernelPresentation.toCommGroupScheme.inclusion
              (M.cover.overFamily j) (gauge j))⁻¹)
      rw [map_mul, map_mul, map_inv, map_inv]
      rw [← hrel]
      dsimp only [KernelPresentation.LocalLift.difference,
        CommGroupScheme.KernelPresentation.LocalLift.difference]
      group
    change (a ≫ adjusted i).left = (b ≫ adjusted j).left
    exact congrArg Over.Hom.left hp
  let xleft : S ⟶ G.scheme :=
    Precoverage.ZeroHypercover.glueMorphisms M.cover
      (fun i ↦ (adjusted i).left) hadjusted
  have hxleft : xleft ≫ G.structureMap = 𝟙 S := by
    apply Precoverage.ZeroHypercover.hom_ext M.cover
    intro i
    have hglue : M.cover.f i ≫ xleft = (adjusted i).left := by
      simpa only [xleft] using
        Precoverage.ZeroHypercover.f_glueMorphisms M.cover
          (fun i ↦ (adjusted i).left) hadjusted i
    rw [← Category.assoc, hglue]
    rw [Category.comp_id]
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
      mapPoint D.project (M.cover.overFamily i) (adjusted i) =
        restrictBasePoint D.quotient M.cover i q := by
    dsimp only [adjusted]
    change CommGroupScheme.mapPoint D.project.hom (M.cover.overFamily i)
        (M.lift i *
          (CommGroupScheme.mapPoint D.kernelPresentation.toCommGroupScheme.inclusion
            (M.cover.overFamily i) (gauge i))⁻¹) =
      CommGroupScheme.restrictBasePoint D.quotient.obj M.cover i q
    rw [map_mul, map_inv,
      D.kernelPresentation.toCommGroupScheme.mapPoint_inclusion_eq_one, inv_one, mul_one,
      CommGroupScheme.KernelPresentation.LocalLift.maps_to]
  refine ⟨x, ?_⟩
  apply Over.OverMorphism.ext
  apply Precoverage.ZeroHypercover.hom_ext M.cover
  intro i
  have hlocal :
      pullPoint D.quotient (coverToBase M.cover i)
          (mapPoint D.project (baseObject S) x) =
        pullPoint D.quotient (coverToBase M.cover i) q := by
    rw [← mapPoint_pullPoint, hxrestrict, hadjusted_map]
    rfl
  exact congrArg Over.Hom.left hlocal

/-- Exactness at quotient-valued global sections: a quotient section has zero boundary exactly
when it comes from a global section of the middle group scheme. -/
theorem boundaryHom_eq_one_iff_exists_project
    (D : FppfQuotientPresentation G) (q : BasePoint D.quotient) :
    D.boundaryHom q = 1 ↔
      ∃ x : BasePoint G, mapPoint D.project (baseObject S) x = q := by
  constructor
  · exact D.exists_project_of_boundaryHom_eq_one q
  · rintro ⟨x, rfl⟩
    exact D.boundaryHom_project x

/-- The quotient projection followed by the constructed boundary homomorphism is exact. -/
theorem exact_project_boundaryHom (D : FppfQuotientPresentation G) :
    Function.MulExact (mapPoint D.project (baseObject S)) D.boundaryHom :=
  fun q ↦ D.boundaryHom_eq_one_iff_exists_project q

/-- A kernel-valued cocycle whose extension to the middle group is trivial is the boundary of a
global quotient section.  On a common refinement, the trivialization supplies middle-group
zero-cochain values.  Their quotient images agree on overlaps and hence glue by fppf descent;
the original values are local lifts of the glued section, whose boundary is the refined input
cocycle by injectivity of the certified kernel inclusion. -/
private theorem exists_boundary_of_class
    (D : FppfQuotientPresentation G)
    (U : Scheme.Cover.{u} Scheme.fppfPrecoverage S)
    (c : OneCocycle
      (toGroups (commPointPresheaf D.kernelPresentation.kernel)) U.overFamily)
    (hc : fppfHOneMap D.kernelPresentation.inclusion
      (fppfHOneClass D.kernelPresentation.kernel U c.class) = 1) :
    ∃ q : BasePoint D.quotient,
      D.boundaryHom q =
        fppfHOneClass D.kernelPresentation.kernel U c.class := by
  let coeffMap := commPointPresheafMap D.kernelPresentation.inclusion
  change Scheme.FppfHOne.mk U
      (NatTrans.mapOneCocycle coeffMap c).class = 1 at hc
  have hc' : Scheme.FppfHOne.mk U
      (NatTrans.mapOneCocycle coeffMap c).class =
      Scheme.FppfHOne.mk (Scheme.FppfHOne.identityCover S) 1 := by
    rw [Scheme.FppfHOne.mk_one]
    exact hc
  obtain ⟨W, r, s, hrs⟩ :=
    (Scheme.FppfHOne.class_eq_iff U
      (Scheme.FppfHOne.identityCover S)
      (NatTrans.mapOneCocycle coeffMap c).class 1).mp hc'
  let ρ := Scheme.Cover.Hom.toOverFamilyRefinement r
  let cW := ρ.pullbackOneCocycle c
  have hrs' :
      (ρ.pullbackOneCocycle (NatTrans.mapOneCocycle coeffMap c)).class = 1 := by
    simpa only [Scheme.Cover.Hom.pullbackHOne,
      FamilyRefinement.pullbackHOne_class,
      FamilyRefinement.pullbackHOne_one] using hrs
  have hmapped : (NatTrans.mapOneCocycle coeffMap cW).class = 1 := by
    change
      (NatTrans.mapOneCocycle coeffMap (ρ.pullbackOneCocycle c)).class = 1
    rw [NatTrans.mapOneCocycle_pullback]
    exact hrs'
  obtain ⟨b, hb⟩ :=
    (OneCocycle.class_eq_iff (NatTrans.mapOneCocycle coeffMap cW) 1).mp hmapped
  let liftLocal (i : W.I₀) : G.Point (W.overFamily i) := b i
  let qLocal (i : W.I₀) : D.quotient.Point (W.overFamily i) :=
    mapPoint D.project (W.overFamily i) (liftLocal i)
  have hqLocal (i j : W.I₀) :
      pullback.fst (W.f i) (W.f j) ≫ (qLocal i).left =
        pullback.snd (W.f i) (W.f j) ≫ (qLocal j).left := by
    let T : Over S := Over.mk (pullback.fst (W.f i) (W.f j) ≫ W.f i)
    let a : T ⟶ W.overFamily i :=
      Over.homMk (pullback.fst (W.f i) (W.f j)) rfl
    let d : T ⟶ W.overFamily j :=
      Over.homMk (pullback.snd (W.f i) (W.f j)) pullback.condition.symm
    let kOverlap : D.kernelPresentation.kernel.Point T := cW.ev i j a d
    have hrel := hb i j a d
    change pullPoint G a (liftLocal i) *
        mapPoint D.kernelPresentation.inclusion T kOverlap =
      1 * pullPoint G d (liftLocal j) at hrel
    have hp := congrArg (mapPoint D.project T) hrel
    rw [map_mul, map_mul, map_one, one_mul,
      mapPoint_pullPoint, mapPoint_pullPoint,
      D.kernelPresentation.mapPoint_inclusion_eq_one T kOverlap, mul_one] at hp
    change (a ≫ qLocal i).left = (d ≫ qLocal j).left
    exact congrArg Over.Hom.left hp
  let qleft : S ⟶ D.quotient.scheme :=
    Precoverage.ZeroHypercover.glueMorphisms W
      (fun i ↦ (qLocal i).left) hqLocal
  have hqleft : qleft ≫ D.quotient.structureMap = 𝟙 S := by
    apply Precoverage.ZeroHypercover.hom_ext W
    intro i
    have hglue : W.f i ≫ qleft = (qLocal i).left := by
      simpa only [qleft] using
        Precoverage.ZeroHypercover.f_glueMorphisms W
          (fun i ↦ (qLocal i).left) hqLocal i
    rw [← Category.assoc, hglue, Category.comp_id]
    exact (qLocal i).w
  let q : BasePoint D.quotient := Over.homMk qleft hqleft
  have hqrestrict (i : W.I₀) :
      pullPoint D.quotient (coverToBase W i) q = qLocal i := by
    apply Over.OverMorphism.ext
    change W.f i ≫ qleft = (qLocal i).left
    simpa only [qleft] using
      Precoverage.ZeroHypercover.f_glueMorphisms W
        (fun i ↦ (qLocal i).left) hqLocal i
  let L : D.kernelPresentation.LocalLift.{u} q :=
    { cover := W
      lift := liftLocal
      maps_to := fun i ↦ by
        change qLocal i = restrictBasePoint D.quotient W i q
        exact (hqrestrict i).symm }
  have hLc : L.cocycle = cW := by
    apply PresheafOfCommGroups.OneCocycle.ext
    apply PresheafOfGroups.OneCochain.ext
    funext i j T a d
    apply D.kernelPresentation.inclusion_point_injective T
    change mapPoint D.kernelPresentation.inclusion T
        (D.kernelPresentation.liftPoint (L.difference i j a d)
          (L.mapPoint_difference_eq_one i j a d)) =
      mapPoint D.kernelPresentation.inclusion T (cW.ev i j a d)
    rw [D.kernelPresentation.mapPoint_liftPoint]
    have hrel := hb i j a d
    change pullPoint G a (liftLocal i) *
        mapPoint D.kernelPresentation.inclusion T (cW.ev i j a d) =
      1 * pullPoint G d (liftLocal j) at hrel
    dsimp only [KernelPresentation.LocalLift.difference]
    change (pullPoint G a (liftLocal i))⁻¹ *
        pullPoint G d (liftLocal j) =
      mapPoint D.kernelPresentation.inclusion T (cW.ev i j a d)
    rw [one_mul] at hrel
    rw [← hrel]
    group
  let cAmbient : OneCocycle
      (toGroups (CommGroupScheme.commPointPresheaf
        D.kernelPresentation.kernel.obj)) U.overFamily := by
    change OneCocycle
      (toGroups (commPointPresheaf D.kernelPresentation.kernel)) U.overFamily
    exact c
  let cWClass : H1
      (CommGroupScheme.commPointPresheaf D.kernelPresentation.kernel.obj)
      W.overFamily :=
    (Scheme.Cover.Hom.toOverFamilyRefinement r).pullbackOneCocycle cAmbient |>.class
  have hLcClass :
      (CommGroupScheme.KernelPresentation.LocalLift.cocycle L).class = cWClass := by
    dsimp only [cWClass, cAmbient, cW, ρ]
    exact congrArg (fun z ↦ z.class) hLc
  refine ⟨q, ?_⟩
  change CommGroupScheme.KernelPresentation.LocallyLiftable.boundaryHom
      D.locallyLiftable q =
    CommGroupScheme.fppfHOneClass
      D.kernelPresentation.kernel.obj U cAmbient.class
  calc
    CommGroupScheme.KernelPresentation.LocallyLiftable.boundaryHom
        D.locallyLiftable q =
        CommGroupScheme.KernelPresentation.LocalLift.boundaryClass
          (D.locallyLiftable.localLift q) := rfl
    _ = CommGroupScheme.KernelPresentation.LocalLift.boundaryClass L :=
      CommGroupScheme.KernelPresentation.LocalLift.boundaryClass_eq
        (D.locallyLiftable.localLift q) L
    _ = CommGroupScheme.fppfHOneClass
        D.kernelPresentation.kernel.obj W cWClass := by
      rw [CommGroupScheme.KernelPresentation.LocalLift.boundaryClass, hLcClass]
    _ = CommGroupScheme.fppfHOneClass
        D.kernelPresentation.kernel.obj U cAmbient.class := by
      change Scheme.FppfHOne.mk W
        cWClass =
        Scheme.FppfHOne.mk U cAmbient.class
      dsimp only [cWClass]
      simpa only [Scheme.Cover.Hom.pullbackHOne,
        PresheafOfGroups.FamilyRefinement.pullbackHOne_class] using
        Scheme.FppfHOne.class_pullback U W r cAmbient.class

/-- Every global kernel `H¹` class killed by extension to the middle group is represented by a
boundary of a global quotient section. -/
theorem exists_boundary_of_fppfHOneMap_eq_one
    (D : FppfQuotientPresentation G)
    (z : D.kernelPresentation.kernel.FppfHOne.{u})
    (hz : fppfHOneMap D.kernelPresentation.inclusion z = 1) :
    ∃ q : BasePoint D.quotient, D.boundaryHom q = z := by
  induction z using Quot.inductionOn with
  | _ a =>
    rcases a with ⟨U, x⟩
    induction x using Quot.inductionOn with
    | _ c => exact D.exists_boundary_of_class U c hz

/-- Membership in the kernel of the map from kernel `H¹` to middle `H¹` is equivalent to
coming from the quotient connecting homomorphism. -/
theorem fppfHOneMap_eq_one_iff_exists_boundaryHom
    (D : FppfQuotientPresentation G)
    (z : D.kernelPresentation.kernel.FppfHOne.{u}) :
    fppfHOneMap D.kernelPresentation.inclusion z = 1 ↔
      ∃ q : BasePoint D.quotient, D.boundaryHom q = z := by
  constructor
  · exact D.exists_boundary_of_fppfHOneMap_eq_one z
  · rintro ⟨q, rfl⟩
    exact D.fppfHOneMap_boundaryHom q

/-- Exactness at the kernel `H¹` term of the quotient low-degree sequence. -/
theorem exact_boundaryHom_fppfHOneMap
    (D : FppfQuotientPresentation G) :
    Function.MulExact D.boundaryHom
      (fppfHOneMap D.kernelPresentation.inclusion) :=
  fun z ↦ D.fppfHOneMap_eq_one_iff_exists_boundaryHom z

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

/-- Raising the first map's source and evaluating the second map on the lowered middle term
preserves multiplicative exactness. -/
theorem mulExact_ulift_downMonoidHom
    {A B : Type u} {C : Type (u + 1)}
    [CommGroup A] [CommGroup B] [CommGroup C]
    {g : A →* B} {h : B →* C} (e : Function.MulExact g h) :
    Function.MulExact (uliftMonoidHom g) (downMonoidHom h) := by
  rintro ⟨y⟩
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := (e y).mp hy
    exact ⟨ULift.up x, by
      apply ULift.ext
      exact hx⟩
  · rintro ⟨⟨x⟩, hx⟩
    apply (e y).mpr
    exact ⟨x, congrArg ULift.down hx⟩

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
uses the quotient's pulled-back singleton cover, the resulting checked boundary homomorphism,
and fppf descent for exactness at quotient-valued global sections and both `H¹` terms.  No
exactness assertion remains as an argument. -/
def ofFppfQuotientPresentation {p : ℕ} {G : FiniteFlatCommGroupScheme S}
    (D : FppfQuotientPresentation G)
    (kernelHZeroData : FinitePGroup.CertifiedData p
      (BasePoint D.kernelPresentation.kernel))
    (middleHZeroData : FinitePGroup.CertifiedData p (BasePoint G))
    (quotientHZeroData : FinitePGroup.CertifiedData p (BasePoint D.quotient))
    (kernelHOneData : FinitePGroup.CertifiedData p
      D.kernelPresentation.kernel.FppfHOne.{u})
    (middleHOneData : FinitePGroup.CertifiedData p G.FppfHOne.{u})
    (quotientHOneData : FinitePGroup.CertifiedData p D.quotient.FppfHOne.{u}) :
    FppfLowDegreeExactSequence.{u + 1} p :=
  ofKernelPresentation D.kernelPresentation D.locallyLiftable
    kernelHZeroData middleHZeroData quotientHZeroData
    kernelHOneData middleHOneData quotientHOneData
    (FinitePGroup.mulExact_ulift_downMonoidHom D.exact_project_boundaryHom)
    D.exact_boundaryHom_fppfHOneMap D.exact_fppfHOneMap_inclusion_project

end FppfLowDegreeExactSequence

end AlgebraicGeometry.FiniteFlatCommGroupScheme

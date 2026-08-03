/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.CommGroupSchemeFppfConnecting
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.QuasiFiniteKernelPresentation

/-!
# Finite-flat compatibility for fppf connecting classes

The connecting-class construction is finiteness-free and now lives in
`CommGroupSchemeFppfConnecting`.  This file preserves the existing finite-flat public API by
transporting a certified finite-flat kernel presentation through its checked ambient geometric
kernel adapter.  No connecting proof is duplicated here.
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

/-- The identity object of the slice, retained under its original finite-flat name. -/
abbrev baseObject (S : Scheme.{u}) : Over S := CommGroupScheme.baseObject S

/-- Global sections of a finite-flat group scheme over its base. -/
abbrev BasePoint (G : FiniteFlatCommGroupScheme S) := CommGroupScheme.BasePoint G.obj

/-- Pull a represented finite-flat point back along a morphism of test schemes. -/
abbrev pullPoint (G : FiniteFlatCommGroupScheme S) {T U : Over S} (g : T ⟶ U) :
    G.Point U →* G.Point T :=
  CommGroupScheme.pullPoint G.obj g

@[simp]
theorem pullPoint_apply (G : FiniteFlatCommGroupScheme S) {T U : Over S}
    (g : T ⟶ U) (x : G.Point U) :
    pullPoint G g x = g ≫ x :=
  CommGroupScheme.pullPoint_apply G.obj g x

@[simp]
theorem pullPoint_id (G : FiniteFlatCommGroupScheme S) {T : Over S}
    (x : G.Point T) : pullPoint G (𝟙 T) x = x :=
  CommGroupScheme.pullPoint_id G.obj x

theorem pullPoint_comp (G : FiniteFlatCommGroupScheme S) {T U V : Over S}
    (g : T ⟶ U) (h : U ⟶ V) (x : G.Point V) :
    pullPoint G (g ≫ h) x = pullPoint G g (pullPoint G h x) :=
  CommGroupScheme.pullPoint_comp G.obj g h x

/-- Postcomposition commutes with restriction of finite-flat points. -/
theorem mapPoint_pullPoint (f : G ⟶ H) {T U : Over S} (g : T ⟶ U)
    (x : G.Point U) :
    mapPoint f T (pullPoint G g x) = pullPoint H g (mapPoint f U x) :=
  CommGroupScheme.mapPoint_pullPoint f.hom g x

/-- The canonical map from a cover member to the identity slice object. -/
abbrev coverToBase (𝒰 : Scheme.Cover.{v} Scheme.fppfPrecoverage S) (i : 𝒰.I₀) :
    𝒰.overFamily i ⟶ baseObject S :=
  CommGroupScheme.coverToBase 𝒰 i

/-- Restriction of a finite-flat global point to a cover member. -/
abbrev restrictBasePoint (G : FiniteFlatCommGroupScheme S)
    (𝒰 : Scheme.Cover.{v} Scheme.fppfPrecoverage S) (i : 𝒰.I₀)
    (x : BasePoint G) : G.Point (𝒰.overFamily i) :=
  CommGroupScheme.restrictBasePoint G.obj 𝒰 i x

/-- Existing finite-flat local-lift data, definitionally identified with the ambient
construction through the geometric kernel adapter. -/
abbrev KernelPresentation.LocalLift (P : KernelPresentation f) (q : BasePoint H) :=
  CommGroupScheme.KernelPresentation.LocalLift.{v} P.toCommGroupScheme q

namespace KernelPresentation

variable (P : KernelPresentation f)

/-- The chosen lift of a killed finite-flat source point. -/
noncomputable abbrev liftPoint {T : Over S} (x : G.Point T) (hx : mapPoint f T x = 1) :
    P.kernel.Point T :=
  P.toCommGroupScheme.liftPoint x hx

@[simp]
theorem mapPoint_liftPoint {T : Over S} (x : G.Point T)
    (hx : mapPoint f T x = 1) :
    mapPoint P.inclusion T (P.liftPoint x hx) = x :=
  P.toCommGroupScheme.mapPoint_liftPoint x hx

/-- The certified finite-flat kernel inclusion is injective on every test scheme. -/
theorem inclusion_point_injective (T : Over S) :
    Function.Injective (mapPoint P.inclusion T) :=
  P.toCommGroupScheme.inclusion_point_injective T

/-- Pullback commutes with the chosen kernel lift. -/
theorem pullPoint_liftPoint {T U : Over S} (g : T ⟶ U)
    (x : G.Point U) (hx : mapPoint f U x = 1) :
    pullPoint P.kernel g (P.liftPoint x hx) =
      P.liftPoint (pullPoint G g x) (by
        rw [mapPoint_pullPoint, hx, map_one]) :=
  P.toCommGroupScheme.pullPoint_liftPoint g x hx

namespace LocalLift

/-- Compatibility projection for the genuine cover carried by finite-flat local lifts. -/
abbrev cover {P : KernelPresentation f} {q : BasePoint H}
    (self : P.LocalLift.{v} q) :
    Scheme.Cover.{v} Scheme.fppfPrecoverage S :=
  CommGroupScheme.KernelPresentation.LocalLift.cover self

/-- Compatibility projection for the source point on each cover member. -/
abbrev lift {P : KernelPresentation f} {q : BasePoint H}
    (self : P.LocalLift.{v} q) (i : self.cover.I₀) :
    G.Point (self.cover.overFamily i) :=
  CommGroupScheme.KernelPresentation.LocalLift.lift self i

/-- Compatibility projection certifying that every local point maps to the target section. -/
theorem maps_to {P : KernelPresentation f} {q : BasePoint H}
    (self : P.LocalLift.{v} q) (i : self.cover.I₀) :
    mapPoint f (self.cover.overFamily i) (self.lift i) =
      restrictBasePoint H self.cover i q := by
  change CommGroupScheme.mapPoint f.hom (self.cover.overFamily i) (self.lift i) =
    CommGroupScheme.restrictBasePoint H.obj self.cover i q
  exact CommGroupScheme.KernelPresentation.LocalLift.maps_to self i

variable {P} {q : BasePoint H} (L : P.LocalLift.{v} q)

theorem mapPoint_pull_lift_eq (i j : L.cover.I₀) {T : Over S}
    (a : T ⟶ L.cover.overFamily i) (b : T ⟶ L.cover.overFamily j) :
    mapPoint f T (pullPoint G a (L.lift i)) =
      mapPoint f T (pullPoint G b (L.lift j)) :=
  CommGroupScheme.KernelPresentation.LocalLift.mapPoint_pull_lift_eq L i j a b

abbrev difference (i j : L.cover.I₀) {T : Over S}
    (a : T ⟶ L.cover.overFamily i) (b : T ⟶ L.cover.overFamily j) :
    G.Point T :=
  CommGroupScheme.KernelPresentation.LocalLift.difference L i j a b

theorem mapPoint_difference_eq_one (i j : L.cover.I₀) {T : Over S}
    (a : T ⟶ L.cover.overFamily i) (b : T ⟶ L.cover.overFamily j) :
    mapPoint f T (L.difference i j a b) = 1 :=
  CommGroupScheme.KernelPresentation.LocalLift.mapPoint_difference_eq_one L i j a b

theorem pullPoint_difference (i j : L.cover.I₀) {T U : Over S}
    (φ : T ⟶ U) (a : U ⟶ L.cover.overFamily i)
    (b : U ⟶ L.cover.overFamily j) :
    pullPoint G φ (L.difference i j a b) =
      L.difference i j (φ ≫ a) (φ ≫ b) :=
  CommGroupScheme.KernelPresentation.LocalLift.pullPoint_difference L i j φ a b

abbrev cocycle : OneCocycle (toGroups (commPointPresheaf P.kernel)) L.cover.overFamily :=
  CommGroupScheme.KernelPresentation.LocalLift.cocycle L

abbrev boundaryClass : P.kernel.FppfHOne.{v} :=
  CommGroupScheme.KernelPresentation.LocalLift.boundaryClass L

abbrev withLift
    (b : ∀ i : L.cover.I₀, G.Point (L.cover.overFamily i))
    (hb : ∀ i, mapPoint f (L.cover.overFamily i) (b i) =
      restrictBasePoint H L.cover i q) :
    P.LocalLift q :=
  CommGroupScheme.KernelPresentation.LocalLift.withLift L b hb

abbrev comparisonZeroCochain
    (b : ∀ i : L.cover.I₀, G.Point (L.cover.overFamily i))
    (hb : ∀ i, mapPoint f (L.cover.overFamily i) (b i) =
      restrictBasePoint H L.cover i q) :
    (i : L.cover.I₀) → P.kernel.Point (L.cover.overFamily i) :=
  CommGroupScheme.KernelPresentation.LocalLift.comparisonZeroCochain L b hb

theorem cocycle_isCohomologous
    (b' : ∀ i : L.cover.I₀, G.Point (L.cover.overFamily i))
    (hb' : ∀ i, mapPoint f (L.cover.overFamily i) (b' i) =
      restrictBasePoint H L.cover i q) :
    L.cocycle.IsCohomologous (L.withLift b' hb').cocycle :=
  CommGroupScheme.KernelPresentation.LocalLift.cocycle_isCohomologous L b' hb'

theorem boundaryClass_eq_withLift
    (b : ∀ i : L.cover.I₀, G.Point (L.cover.overFamily i))
    (hb : ∀ i, mapPoint f (L.cover.overFamily i) (b i) =
      restrictBasePoint H L.cover i q) :
    L.boundaryClass = (L.withLift b hb).boundaryClass :=
  CommGroupScheme.KernelPresentation.LocalLift.boundaryClass_eq_withLift L b hb

abbrev pullback {𝒱 : Scheme.Cover.{v} Scheme.fppfPrecoverage S}
    (r : 𝒱.Hom L.cover) : P.LocalLift q :=
  CommGroupScheme.KernelPresentation.LocalLift.pullback L r

theorem cocycle_pullback {𝒱 : Scheme.Cover.{v} Scheme.fppfPrecoverage S}
    (r : 𝒱.Hom L.cover) :
    (L.pullback r).cocycle =
      (Scheme.Cover.Hom.toOverFamilyRefinement r).pullbackOneCocycle L.cocycle :=
  CommGroupScheme.KernelPresentation.LocalLift.cocycle_pullback L r

theorem boundaryClass_pullback
    {𝒱 : Scheme.Cover.{v} Scheme.fppfPrecoverage S} (r : 𝒱.Hom L.cover) :
    (L.pullback r).boundaryClass = L.boundaryClass :=
  CommGroupScheme.KernelPresentation.LocalLift.boundaryClass_pullback L r

theorem boundaryClass_eq (M : P.LocalLift.{v} q) :
    L.boundaryClass = M.boundaryClass :=
  CommGroupScheme.KernelPresentation.LocalLift.boundaryClass_eq L M

abbrev one (P : KernelPresentation f) : P.LocalLift.{v} (1 : BasePoint H) :=
  CommGroupScheme.KernelPresentation.LocalLift.one P.toCommGroupScheme

@[simp]
theorem one_cocycle (P : KernelPresentation f) :
    (LocalLift.one.{v} P).cocycle = 1 :=
  CommGroupScheme.KernelPresentation.LocalLift.one_cocycle P.toCommGroupScheme

@[simp]
theorem one_boundaryClass (P : KernelPresentation f) :
    (LocalLift.one.{v} P).boundaryClass = 1 :=
  CommGroupScheme.KernelPresentation.LocalLift.one_boundaryClass P.toCommGroupScheme

abbrev mul {q r : BasePoint H} (L : P.LocalLift.{v} q) (M : P.LocalLift.{v} r) :
    P.LocalLift.{v} (q * r) :=
  CommGroupScheme.KernelPresentation.LocalLift.mul L M

theorem mul_cocycle {q r : BasePoint H} (L : P.LocalLift.{v} q)
    (M : P.LocalLift.{v} r) :
    (L.mul M).cocycle =
      OneCocycle.mul (commPointPresheaf P.kernel)
        (L.pullback (Scheme.Cover.interFst L.cover M.cover)).cocycle
        (M.pullback (Scheme.Cover.interSnd L.cover M.cover)).cocycle :=
  CommGroupScheme.KernelPresentation.LocalLift.mul_cocycle L M

theorem mul_boundaryClass {q r : BasePoint H} (L : P.LocalLift.{v} q)
    (M : P.LocalLift.{v} r) :
    (L.mul M).boundaryClass = L.boundaryClass * M.boundaryClass :=
  CommGroupScheme.KernelPresentation.LocalLift.mul_boundaryClass L M

abbrev ofBasePoint (P : KernelPresentation f) (x : BasePoint G) :
    P.LocalLift.{v} (mapPoint f (baseObject S) x) :=
  CommGroupScheme.KernelPresentation.LocalLift.ofBasePoint P.toCommGroupScheme x

@[simp]
theorem ofBasePoint_cocycle (P : KernelPresentation f) (x : BasePoint G) :
    (LocalLift.ofBasePoint.{v} P x).cocycle = 1 :=
  CommGroupScheme.KernelPresentation.LocalLift.ofBasePoint_cocycle P.toCommGroupScheme x

@[simp]
theorem ofBasePoint_boundaryClass (P : KernelPresentation f) (x : BasePoint G) :
    (LocalLift.ofBasePoint.{v} P x).boundaryClass = 1 :=
  CommGroupScheme.KernelPresentation.LocalLift.ofBasePoint_boundaryClass
    P.toCommGroupScheme x

theorem map_cocycle_isCohomologous_one :
    (NatTrans.mapOneCocycle
      (commPointPresheafMap P.inclusion) L.cocycle).IsCohomologous
        (1 : OneCocycle (toGroups (commPointPresheaf G)) L.cover.overFamily) :=
  CommGroupScheme.KernelPresentation.LocalLift.map_cocycle_isCohomologous_one L

@[simp]
theorem fppfHOneMap_boundaryClass :
    fppfHOneMap P.inclusion L.boundaryClass = 1 :=
  CommGroupScheme.KernelPresentation.LocalLift.fppfHOneMap_boundaryClass L

end LocalLift

/-- Existing finite-flat local-surjectivity data as an ambient compatibility alias. -/
abbrev LocallyLiftable := P.toCommGroupScheme.LocallyLiftable.{v}

namespace LocallyLiftable

variable {P : KernelPresentation f}

/-- Compatibility projection selecting local lifts for each global target section. -/
abbrev localLift (self : P.LocallyLiftable.{v}) (q : BasePoint H) :
    P.LocalLift.{v} q :=
  CommGroupScheme.KernelPresentation.LocallyLiftable.localLift self q

variable (E : P.LocallyLiftable.{v})

abbrev boundaryHom : BasePoint H →* P.kernel.FppfHOne.{v} :=
  CommGroupScheme.KernelPresentation.LocallyLiftable.boundaryHom E

@[simp]
theorem boundaryHom_apply (q : BasePoint H) :
    E.boundaryHom q = (E.localLift q).boundaryClass :=
  CommGroupScheme.KernelPresentation.LocallyLiftable.boundaryHom_apply E q

@[simp]
theorem boundaryHom_mapPoint (x : BasePoint G) :
    E.boundaryHom (mapPoint f (baseObject S) x) = 1 :=
  CommGroupScheme.KernelPresentation.LocallyLiftable.boundaryHom_mapPoint E x

@[simp]
theorem fppfHOneMap_boundaryHom (q : BasePoint H) :
    fppfHOneMap P.inclusion (E.boundaryHom q) = 1 :=
  CommGroupScheme.KernelPresentation.LocallyLiftable.fppfHOneMap_boundaryHom E q

end LocallyLiftable

end KernelPresentation

end AlgebraicGeometry.FiniteFlatCommGroupScheme

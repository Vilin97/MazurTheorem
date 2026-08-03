/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.CommGroupSchemeFppfConnecting
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.QuasiFiniteKernelPresentation

/-!
# Fppf connecting classes for quasi-finite flat group schemes

The connecting-class construction only uses represented points, ambient fppf `H¹`, and a
geometric kernel presentation.  This file transports that construction to the quasi-finite-flat
wrapper without adding a finiteness hypothesis.  Supplied local lifts produce a genuine boundary
homomorphism; globally lifted sections have trivial boundary, and every constructed boundary
class maps trivially after extension to the middle group scheme.

Constructing local lifts canonically from an fppf quotient projection is a separate quotient
layer.  In particular, no surjectivity on points and no representability of an arbitrary quotient
is asserted here.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme

universe v u

variable {S : Scheme.{u}} {G H : QuasiFiniteFlatCommGroupScheme S} {f : G ⟶ H}

/-- The identity object of the slice used for quasi-finite global sections. -/
abbrev baseObject (S : Scheme.{u}) : Over S := CommGroupScheme.baseObject S

/-- Global sections of a quasi-finite flat commutative group scheme. -/
abbrev BasePoint (G : QuasiFiniteFlatCommGroupScheme S) :=
  CommGroupScheme.BasePoint G.obj

/-- Pull a represented quasi-finite point back along a morphism of test schemes. -/
abbrev pullPoint (G : QuasiFiniteFlatCommGroupScheme S) {T U : Over S} (g : T ⟶ U) :
    CommGroupScheme.Point G.obj U →* CommGroupScheme.Point G.obj T :=
  CommGroupScheme.pullPoint G.obj g

@[simp]
theorem pullPoint_apply (G : QuasiFiniteFlatCommGroupScheme S) {T U : Over S}
    (g : T ⟶ U) (x : CommGroupScheme.Point G.obj U) :
    pullPoint G g x = g ≫ x :=
  CommGroupScheme.pullPoint_apply G.obj g x

@[simp]
theorem pullPoint_id (G : QuasiFiniteFlatCommGroupScheme S) {T : Over S}
    (x : CommGroupScheme.Point G.obj T) : pullPoint G (𝟙 T) x = x :=
  CommGroupScheme.pullPoint_id G.obj x

theorem pullPoint_comp (G : QuasiFiniteFlatCommGroupScheme S) {T U V : Over S}
    (g : T ⟶ U) (h : U ⟶ V) (x : CommGroupScheme.Point G.obj V) :
    pullPoint G (g ≫ h) x = pullPoint G g (pullPoint G h x) :=
  CommGroupScheme.pullPoint_comp G.obj g h x

/-- Quasi-finite point maps commute with restriction to test schemes. -/
theorem mapPoint_pullPoint (f : G ⟶ H) {T U : Over S} (g : T ⟶ U)
    (x : CommGroupScheme.Point G.obj U) :
    mapPoint f T (pullPoint G g x) = pullPoint H g (mapPoint f U x) :=
  CommGroupScheme.mapPoint_pullPoint f.hom g x

/-- The canonical map from a cover member to the identity slice object. -/
abbrev coverToBase (𝒰 : Scheme.Cover.{v} Scheme.fppfPrecoverage S) (i : 𝒰.I₀) :
    𝒰.overFamily i ⟶ baseObject S :=
  CommGroupScheme.coverToBase 𝒰 i

/-- Restrict a quasi-finite global point to a member of an fppf cover. -/
abbrev restrictBasePoint (G : QuasiFiniteFlatCommGroupScheme S)
    (𝒰 : Scheme.Cover.{v} Scheme.fppfPrecoverage S) (i : 𝒰.I₀)
    (x : BasePoint G) : CommGroupScheme.Point G.obj (𝒰.overFamily i) :=
  CommGroupScheme.restrictBasePoint G.obj 𝒰 i x

/-- Actual local lifts through a quasi-finite morphism with a supplied geometric kernel. -/
abbrev KernelPresentation.LocalLift (P : KernelPresentation f) (q : BasePoint H) :=
  CommGroupScheme.KernelPresentation.LocalLift.{v} P.toCommGroupScheme q

namespace KernelPresentation

variable (P : KernelPresentation f)

/-- Pullback commutes with the canonical lift into a supplied quasi-finite geometric kernel. -/
theorem pullPoint_liftPoint {T U : Over S} (g : T ⟶ U)
    (x : CommGroupScheme.Point G.obj U) (hx : mapPoint f U x = 1) :
    pullPoint P.kernel g (P.liftPoint x hx) =
      P.liftPoint (pullPoint G g x) (by
        rw [mapPoint_pullPoint, hx, map_one]) :=
  P.toCommGroupScheme.pullPoint_liftPoint g x hx

namespace LocalLift

variable {P} {q : BasePoint H} (L : P.LocalLift.{v} q)

/-- The kernel-valued Čech cocycle attached to supplied quasi-finite local lifts. -/
abbrev cocycle :
    CategoryTheory.PresheafOfGroups.OneCocycle
      (CategoryTheory.PresheafOfCommGroups.toGroups
        (CommGroupScheme.commPointPresheaf P.kernel.obj))
      L.cover.overFamily :=
  CommGroupScheme.KernelPresentation.LocalLift.cocycle L

/-- The global fppf connecting class attached to supplied quasi-finite local lifts. -/
abbrev boundaryClass : P.kernel.FppfHOne.{v} :=
  CommGroupScheme.KernelPresentation.LocalLift.boundaryClass L

/-- The connecting class is independent of the fppf cover and all supplied local lifts. -/
theorem boundaryClass_eq (M : P.LocalLift.{v} q) :
    L.boundaryClass = M.boundaryClass :=
  CommGroupScheme.KernelPresentation.LocalLift.boundaryClass_eq L M

/-- A genuinely global quasi-finite source section supplies tautological local lifts. -/
abbrev ofBasePoint (P : KernelPresentation f) (x : BasePoint G) :
    P.LocalLift.{v} (mapPoint f (baseObject S) x) :=
  CommGroupScheme.KernelPresentation.LocalLift.ofBasePoint P.toCommGroupScheme x

/-- The connecting class of a globally lifted section is trivial. -/
@[simp]
theorem ofBasePoint_boundaryClass (P : KernelPresentation f) (x : BasePoint G) :
    (LocalLift.ofBasePoint.{v} P x).boundaryClass = 1 :=
  CommGroupScheme.KernelPresentation.LocalLift.ofBasePoint_boundaryClass
    P.toCommGroupScheme x

/-- Extending a constructed boundary class along the quasi-finite kernel inclusion gives the
trivial middle-group class. -/
@[simp]
theorem fppfHOneMap_boundaryClass :
    fppfHOneMap P.inclusion L.boundaryClass = 1 :=
  CommGroupScheme.KernelPresentation.LocalLift.fppfHOneMap_boundaryClass L

end LocalLift

/-- Local lift data for every global target section. -/
abbrev LocallyLiftable := P.toCommGroupScheme.LocallyLiftable.{v}

namespace LocallyLiftable

variable {P : KernelPresentation f}
variable (E : P.LocallyLiftable.{v})

/-- The genuine quasi-finite connecting homomorphism constructed from supplied local lifts. -/
abbrev boundaryHom : BasePoint H →* P.kernel.FppfHOne.{v} :=
  CommGroupScheme.KernelPresentation.LocallyLiftable.boundaryHom E

@[simp]
theorem boundaryHom_apply (q : BasePoint H) :
    E.boundaryHom q = (E.localLift q).boundaryClass :=
  CommGroupScheme.KernelPresentation.LocallyLiftable.boundaryHom_apply E q

/-- Named represented-point exactness consumer: every globally lifted target section has
trivial quasi-finite connecting class. -/
@[simp]
theorem boundaryHom_mapPoint (x : BasePoint G) :
    E.boundaryHom (mapPoint f (baseObject S) x) = 1 :=
  CommGroupScheme.KernelPresentation.LocallyLiftable.boundaryHom_mapPoint E x

/-- Named degree-one exactness consumer: every constructed quasi-finite boundary lies in the
kernel of extension to the middle group scheme. -/
@[simp]
theorem fppfHOneMap_boundaryHom (q : BasePoint H) :
    fppfHOneMap P.inclusion (E.boundaryHom q) = 1 :=
  CommGroupScheme.KernelPresentation.LocallyLiftable.fppfHOneMap_boundaryHom E q

end LocallyLiftable

end KernelPresentation

end AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.CommGroupSchemeFppfMiddleExact
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.QuasiFiniteQuotient

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
open CategoryTheory.Limits
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

namespace FppfQuotientPresentation

variable {G : QuasiFiniteFlatCommGroupScheme S}

/-- The quasi-finite quotient projection itself, regarded as a singleton fppf cover. -/
abbrev projectCover (D : FppfQuotientPresentation G) :
    Scheme.Cover.{u} Scheme.fppfPrecoverage D.quotient.scheme := by
  letI : Flat (hom D.project) := D.project_flat
  letI : Surjective (hom D.project) := D.project_surjective
  letI : LocallyOfFinitePresentation (hom D.project) := D.project_lfp
  exact (hom D.project).cover ⟨D.project_flat, D.project_lfp⟩

/-- Refine a cover so that every quotient-valued zero-cochain entry acquires a source lift. -/
noncomputable def gaugeLiftCover (D : FppfQuotientPresentation G)
    (U : Scheme.Cover.{u} Scheme.fppfPrecoverage S)
    (b : ∀ i : U.I₀, CommGroupScheme.Point D.quotient.obj (U.overFamily i)) :
    Scheme.Cover.{u} Scheme.fppfPrecoverage S :=
  U.bind fun i ↦ D.projectCover.pullback₁ (b i).left

/-- The gauge-lifting cover is a genuine refinement of the original cover. -/
def gaugeLiftCoverHom (D : FppfQuotientPresentation G)
    (U : Scheme.Cover.{u} Scheme.fppfPrecoverage S)
    (b : ∀ i : U.I₀, CommGroupScheme.Point D.quotient.obj (U.overFamily i)) :
    (D.gaugeLiftCover U b).Hom U where
  s₀ ij := ij.1
  h₀ ij := (D.projectCover.pullback₁ (b ij.1).left).f ij.2
  w₀ _ := rfl

/-- The tautological source point on the pullback of the quotient projection. -/
def gaugeLift (D : FppfQuotientPresentation G)
    (U : Scheme.Cover.{u} Scheme.fppfPrecoverage S)
    (b : ∀ i : U.I₀, CommGroupScheme.Point D.quotient.obj (U.overFamily i))
    (ij : (D.gaugeLiftCover U b).I₀) :
    CommGroupScheme.Point G.obj ((D.gaugeLiftCover U b).overFamily ij) :=
  Over.homMk (pullback.snd (b ij.1).left (hom D.project)) (by
    change pullback.snd (b ij.1).left (hom D.project) ≫ G.structureMap =
      pullback.fst (b ij.1).left (hom D.project) ≫ U.f ij.1
    rw [← hom_comp_structureMap D.project, ← Category.assoc,
      ← pullback.condition, Category.assoc, Over.w (b ij.1)]
    rfl)

/-- The tautological source point maps to the pulled-back zero-cochain entry. -/
theorem mapPoint_gaugeLift (D : FppfQuotientPresentation G)
    (U : Scheme.Cover.{u} Scheme.fppfPrecoverage S)
    (b : ∀ i : U.I₀, CommGroupScheme.Point D.quotient.obj (U.overFamily i))
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

/-- An actual quasi-finite fppf quotient projection is coverwise locally liftable. -/
def coverwiseLocallyLiftable (D : FppfQuotientPresentation G) :
    D.kernelPresentation.toCommGroupScheme.CoverwiseLocallyLiftable.{u} where
  liftData U b :=
    { cover := D.gaugeLiftCover U b
      refinement := D.gaugeLiftCoverHom U b
      lift := D.gaugeLift U b
      maps_to := D.mapPoint_gaugeLift U b }

/-- The quotient projection is locally liftable on global sections, obtained from its stronger
coverwise lifting property. -/
def locallyLiftable (D : FppfQuotientPresentation G) :
    D.kernelPresentation.LocallyLiftable.{u} :=
  D.coverwiseLocallyLiftable.toLocallyLiftable

/-- The connecting homomorphism of a genuine quasi-finite fppf quotient. -/
def boundaryHom (D : FppfQuotientPresentation G) :
    BasePoint D.quotient →* D.kernelPresentation.kernel.FppfHOne.{u} :=
  D.locallyLiftable.boundaryHom

@[simp]
theorem boundaryHom_apply (D : FppfQuotientPresentation G)
    (q : BasePoint D.quotient) :
    D.boundaryHom q = (D.locallyLiftable.localLift q).boundaryClass :=
  D.locallyLiftable.boundaryHom_apply q

/-- Exactness at global quotient sections for a genuine quasi-finite fppf quotient. -/
theorem exact_project_boundaryHom (D : FppfQuotientPresentation G) :
    Function.MulExact
      (mapPoint D.project (baseObject S)) D.boundaryHom :=
  D.locallyLiftable.exact_mapPoint_boundaryHom

/-- Exactness at kernel-valued `H¹` for a genuine quasi-finite fppf quotient. -/
theorem exact_boundaryHom_fppfHOneMap (D : FppfQuotientPresentation G) :
    Function.MulExact D.boundaryHom
      (fppfHOneMap D.kernelPresentation.inclusion) :=
  D.locallyLiftable.exact_boundaryHom_fppfHOneMap

/-- Exactness at the middle global fppf `H¹` term for a genuine quasi-finite quotient
presentation.  This is the geometric downstream consumer of the ambient coverwise interface. -/
theorem exact_fppfHOneMap_inclusion_project (D : FppfQuotientPresentation G) :
    Function.MulExact
      (fppfHOneMap D.kernelPresentation.inclusion :
        D.kernelPresentation.kernel.FppfHOne.{u} →* G.FppfHOne.{u})
      (fppfHOneMap D.project : G.FppfHOne.{u} →* D.quotient.FppfHOne.{u}) :=
  D.coverwiseLocallyLiftable.exact_fppfHOneMap_inclusion_f

end FppfQuotientPresentation

end AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme

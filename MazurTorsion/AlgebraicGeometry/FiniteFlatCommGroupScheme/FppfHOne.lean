/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.NonabelianCohomology.H1
import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Basic

/-!
# Refinement maps and global fppf cohomology in degree one

Mathlib defines nonabelian `H¹` on one indexed family, but at the pinned revision leaves its
globalization over covering families as a TODO.  This file supplies the missing transition maps:
a refinement of indexed families pulls zero-cochains, one-cochains, cocycles, and cohomology
classes back.  The construction is contravariantly functorial and sends the trivial class to the
trivial class.

For actual fppf covers of a scheme `X`, `FppfHOne` is the filtered-colimit quotient of all
cover-level classes by common refinement.  Crucially, a cover component `Uᵢ ⟶ X` is regarded as
an object of `Over X`, and coefficients are presheaves on `(Over X)ᵒᵖ`.  Thus the test morphisms in
a one-cochain are morphisms over `X`; the resulting overlaps are fibre products `Uᵢ ×_X Uⱼ`, not
absolute products of schemes.

We use the explicit quotient presentation of a colimit of types, rather than asking Lean for a
small category of all covers.  The latter would require a smallness instance which the large
indexed-cover category does not possess.  The relation is generated only by genuine
`Scheme.Cover.Hom` refinements.  The final section checks the intended coefficient system:
the point presheaf represented by a finite-flat commutative group scheme over `X`.
-/

noncomputable section

open CategoryTheory

namespace CategoryTheory.PresheafOfGroups

universe wK wJ wI w v u

variable {C : Type u} [Category.{v} C]
variable (G : Cᵒᵖ ⥤ GrpCat.{w})
variable {I : Type wI} {J : Type wJ} {K : Type wK}
variable {U : I → C} {V : J → C} {W : K → C}

/-- A refinement of an indexed family `U` by an indexed family `V`. -/
structure FamilyRefinement (V : J → C) (U : I → C) where
  /-- Index of the old family containing a member of the refined family. -/
  index : J → I
  /-- The refinement morphism. -/
  map (j : J) : V j ⟶ U (index j)

namespace FamilyRefinement

variable {G}

/-- Equality of one-cocycles is detected on the underlying one-cochain. -/
lemma oneCocycle_ext {U : I → C} {c d : OneCocycle G U}
    (h : c.toOneCochain = d.toOneCochain) : c = d := by
  cases c
  cases d
  cases h
  rfl

/-- The identity refinement. -/
@[simps]
def refl (U : I → C) : FamilyRefinement U U where
  index := id
  map _ := 𝟙 _

/-- Composition of refinements. -/
@[simps]
def comp (VU : FamilyRefinement V U) (WV : FamilyRefinement W V) :
    FamilyRefinement W U where
  index := VU.index ∘ WV.index
  map k := WV.map k ≫ VU.map (WV.index k)

/-- Pull a zero-cochain back along a refinement. -/
def pullbackZeroCochain (VU : FamilyRefinement V U) (a : ZeroCochain G U) :
    ZeroCochain G V :=
  fun j ↦ G.map (VU.map j).op (a (VU.index j))

@[simp]
lemma pullbackZeroCochain_apply (VU : FamilyRefinement V U) (a : ZeroCochain G U) (j : J) :
    VU.pullbackZeroCochain a j = G.map (VU.map j).op (a (VU.index j)) :=
  rfl

/-- Pull a one-cochain back along a refinement. -/
def pullbackOneCochain (VU : FamilyRefinement V U) (c : OneCochain G U) :
    OneCochain G V where
  ev i j T a b := c.ev (VU.index i) (VU.index j) (a ≫ VU.map i) (b ≫ VU.map j)
  ev_precomp i j T T' φ a b := by
    simpa only [Category.assoc] using
      c.ev_precomp (VU.index i) (VU.index j) φ (a ≫ VU.map i) (b ≫ VU.map j)

@[simp]
lemma pullbackOneCochain_ev (VU : FamilyRefinement V U) (c : OneCochain G U)
    (i j : J) {T : C} (a : T ⟶ V i) (b : T ⟶ V j) :
    (VU.pullbackOneCochain c).ev i j a b =
      c.ev (VU.index i) (VU.index j) (a ≫ VU.map i) (b ≫ VU.map j) :=
  rfl

/-- Pull a one-cocycle back along a refinement. -/
def pullbackOneCocycle (VU : FamilyRefinement V U) (c : OneCocycle G U) :
    OneCocycle G V where
  toOneCochain := VU.pullbackOneCochain c.toOneCochain
  ev_trans i j k _T a b d :=
    c.ev_trans (VU.index i) (VU.index j) (VU.index k)
      (a ≫ VU.map i) (b ≫ VU.map j) (d ≫ VU.map k)

@[simp]
lemma pullbackOneCocycle_toOneCochain (VU : FamilyRefinement V U) (c : OneCocycle G U) :
    (VU.pullbackOneCocycle c).toOneCochain = VU.pullbackOneCochain c.toOneCochain :=
  rfl

lemma pullback_oneCohomologyRelation (VU : FamilyRefinement V U)
    {c d : OneCochain G U} {a : ZeroCochain G U}
    (h : OneCohomologyRelation c d a) :
    OneCohomologyRelation (VU.pullbackOneCochain c) (VU.pullbackOneCochain d)
      (VU.pullbackZeroCochain a) := by
  intro i j T f g
  dsimp only [pullbackZeroCochain, pullbackOneCochain]
  simpa only [← Functor.map_comp_apply, ← op_comp] using
    h (VU.index i) (VU.index j) (f ≫ VU.map i) (g ≫ VU.map j)

lemma pullback_isCohomologous (VU : FamilyRefinement V U) {c d : OneCocycle G U}
    (h : c.IsCohomologous d) :
    (VU.pullbackOneCocycle c).IsCohomologous (VU.pullbackOneCocycle d) := by
  obtain ⟨a, ha⟩ := h
  exact ⟨VU.pullbackZeroCochain a, VU.pullback_oneCohomologyRelation ha⟩

/-- Pull a cover-level `H¹` class back along a refinement. -/
def pullbackHOne (VU : FamilyRefinement V U) : H1 G U → H1 G V :=
  Quot.lift
    (fun c ↦ (VU.pullbackOneCocycle c).class)
    (fun _ _ h ↦ (VU.pullback_isCohomologous h).class_eq)

@[simp]
lemma pullbackHOne_class (VU : FamilyRefinement V U) (c : OneCocycle G U) :
    VU.pullbackHOne c.class = (VU.pullbackOneCocycle c).class :=
  rfl

@[simp]
lemma pullbackOneCocycle_one (VU : FamilyRefinement V U) :
    VU.pullbackOneCocycle (1 : OneCocycle G U) = 1 := by
  apply oneCocycle_ext
  apply OneCochain.ext
  funext i j T a b
  rfl

@[simp]
lemma pullbackHOne_one (VU : FamilyRefinement V U) :
    VU.pullbackHOne (1 : H1 G U) = 1 := by
  rfl

lemma pullbackOneCocycle_refl (c : OneCocycle G U) :
    (refl U).pullbackOneCocycle c = c := by
  apply oneCocycle_ext
  apply OneCochain.ext
  funext i j T a b
  simp [refl]

lemma pullbackOneCocycle_comp (VU : FamilyRefinement V U) (WV : FamilyRefinement W V)
    (c : OneCocycle G U) :
    (VU.comp WV).pullbackOneCocycle c =
      WV.pullbackOneCocycle (VU.pullbackOneCocycle c) := by
  apply oneCocycle_ext
  apply OneCochain.ext
  funext i j T a b
  simp [comp, Category.assoc]

@[simp]
lemma pullbackHOne_refl (x : H1 G U) : (refl U).pullbackHOne x = x := by
  induction x using Quot.inductionOn with
  | _ c =>
      change ((refl U).pullbackOneCocycle c).class = c.class
      rw [pullbackOneCocycle_refl]

lemma pullbackHOne_comp (VU : FamilyRefinement V U) (WV : FamilyRefinement W V)
    (x : H1 G U) :
    (VU.comp WV).pullbackHOne x = WV.pullbackHOne (VU.pullbackHOne x) := by
  induction x using Quot.inductionOn with
  | _ c =>
      change ((VU.comp WV).pullbackOneCocycle c).class =
        (WV.pullbackOneCocycle (VU.pullbackOneCocycle c)).class
      rw [pullbackOneCocycle_comp]

/-- The zero-cochain comparing the pullbacks of a cocycle along two refinement choices. -/
def comparisonZeroCochain (VU VU' : FamilyRefinement V U) (c : OneCocycle G U) :
    ZeroCochain G V :=
  fun i ↦ c.ev (VU'.index i) (VU.index i) (VU'.map i) (VU.map i)

/-- Two choices of refinement map pull a cocycle back to cohomologous cocycles.  This is the
degree-one Čech homotopy which makes the global common-refinement relation transitive. -/
lemma pullbackOneCocycle_isCohomologous (VU VU' : FamilyRefinement V U)
    (c : OneCocycle G U) :
    (VU.pullbackOneCocycle c).IsCohomologous (VU'.pullbackOneCocycle c) := by
  refine ⟨comparisonZeroCochain VU VU' c, ?_⟩
  intro i j T a b
  dsimp only [comparisonZeroCochain, pullbackOneCocycle, pullbackOneCochain]
  rw [c.ev_precomp (VU'.index i) (VU.index i) a (VU'.map i) (VU.map i),
    c.ev_precomp (VU'.index j) (VU.index j) b (VU'.map j) (VU.map j),
    c.ev_trans (VU'.index i) (VU.index i) (VU.index j)
      (a ≫ VU'.map i) (a ≫ VU.map i) (b ≫ VU.map j),
    c.ev_trans (VU'.index i) (VU'.index j) (VU.index j)
      (a ≫ VU'.map i) (b ≫ VU'.map j) (b ≫ VU.map j)]

/-- Cover-level `H¹` pullback is independent of the chosen refinement morphism. -/
lemma pullbackHOne_eq (VU VU' : FamilyRefinement V U) (x : H1 G U) :
    VU.pullbackHOne x = VU'.pullbackHOne x := by
  induction x using Quot.inductionOn with
  | _ c => exact (pullbackOneCocycle_isCohomologous VU VU' c).class_eq

end FamilyRefinement

end CategoryTheory.PresheafOfGroups

namespace CategoryTheory.PreZeroHypercover.Hom

universe wK wJ wI w v u

open PresheafOfGroups

variable {C : Type u} [Category.{v} C] {S : C}
variable {𝒰 : PreZeroHypercover.{wI} S} {𝒱 : PreZeroHypercover.{wJ} S}
variable {𝒲 : PreZeroHypercover.{wK} S}

/-- The indexed-family refinement underlying a morphism of pre-zero-hypercovers. -/
def toFamilyRefinement (r : 𝒱.Hom 𝒰) : FamilyRefinement 𝒱.X 𝒰.X where
  index := r.s₀
  map := r.h₀

@[simp]
lemma toFamilyRefinement_index (r : 𝒱.Hom 𝒰) (i : 𝒱.I₀) :
    (toFamilyRefinement r).index i = r.s₀ i :=
  rfl

@[simp]
lemma toFamilyRefinement_map (r : 𝒱.Hom 𝒰) (i : 𝒱.I₀) :
    (toFamilyRefinement r).map i = r.h₀ i :=
  rfl

lemma toFamilyRefinement_id :
    toFamilyRefinement (PreZeroHypercover.Hom.id 𝒰) =
      FamilyRefinement.refl 𝒰.X := by
  rfl

lemma toFamilyRefinement_comp (r : 𝒱.Hom 𝒰) (s : 𝒲.Hom 𝒱) :
    toFamilyRefinement (PreZeroHypercover.Hom.comp s r) =
      (toFamilyRefinement r).comp (toFamilyRefinement s) := by
  rfl

variable (G : Cᵒᵖ ⥤ GrpCat.{w})

/-- Pull a family-level `H¹` class back along a morphism of pre-zero-hypercovers. -/
def pullbackHOne (r : 𝒱.Hom 𝒰) : H1 G 𝒰.X → H1 G 𝒱.X :=
  (toFamilyRefinement r).pullbackHOne

@[simp]
lemma pullbackHOne_id (x : H1 G 𝒰.X) :
    pullbackHOne G (PreZeroHypercover.Hom.id 𝒰) x = x := by
  simpa only [pullbackHOne, toFamilyRefinement_id] using
    FamilyRefinement.pullbackHOne_refl x

lemma pullbackHOne_comp (r : 𝒱.Hom 𝒰) (s : 𝒲.Hom 𝒱) (x : H1 G 𝒰.X) :
    pullbackHOne G (PreZeroHypercover.Hom.comp s r) x =
      pullbackHOne G s (pullbackHOne G r x) := by
  simpa only [pullbackHOne, toFamilyRefinement_comp] using
    FamilyRefinement.pullbackHOne_comp (toFamilyRefinement r) (toFamilyRefinement s) x

lemma pullbackHOne_eq (r r' : 𝒱.Hom 𝒰) (x : H1 G 𝒰.X) :
    pullbackHOne G r x = pullbackHOne G r' x :=
  FamilyRefinement.pullbackHOne_eq (toFamilyRefinement r) (toFamilyRefinement r') x

@[simp]
lemma pullbackHOne_one (r : 𝒱.Hom 𝒰) :
    pullbackHOne G r (1 : H1 G 𝒰.X) = 1 :=
  FamilyRefinement.pullbackHOne_one (toFamilyRefinement r)

end CategoryTheory.PreZeroHypercover.Hom

namespace AlgebraicGeometry.Scheme

universe w v u

open CategoryTheory.PresheafOfGroups

/-- Regard the components of an fppf cover of `X` as objects in the slice category `Over X`.
Keeping the structure maps in the objects is essential: morphisms between components must commute
with their maps to `X`. -/
def Cover.overFamily {X : Scheme.{u}} (𝒰 : Cover.{v} fppfPrecoverage X) :
    𝒰.I₀ → Over X :=
  fun i ↦ Over.mk (𝒰.f i)

namespace Cover.Hom

variable {X : Scheme.{u}} {𝒰 𝒱 𝒲 : Cover.{v} fppfPrecoverage X}

/-- A refinement of fppf covers induces a refinement of their component families in `Over X`.
The proof field `r.w₀` is precisely what makes every component map a morphism over `X`. -/
def toOverFamilyRefinement (r : 𝒱.Hom 𝒰) :
    FamilyRefinement 𝒱.overFamily 𝒰.overFamily where
  index := r.s₀
  map i := Over.homMk (r.h₀ i) (r.w₀ i)

lemma toOverFamilyRefinement_id :
    toOverFamilyRefinement (PreZeroHypercover.Hom.id 𝒰.toPreZeroHypercover) =
      FamilyRefinement.refl 𝒰.overFamily := by
  rfl

lemma toOverFamilyRefinement_comp (r : 𝒱.Hom 𝒰) (s : 𝒲.Hom 𝒱) :
    toOverFamilyRefinement (PreZeroHypercover.Hom.comp s r) =
      (toOverFamilyRefinement r).comp (toOverFamilyRefinement s) := by
  rfl

variable (G : (Over X)ᵒᵖ ⥤ GrpCat.{w})

/-- Pull a relative cover-level `H¹` class back along a refinement of fppf covers. -/
def pullbackHOne (r : 𝒱.Hom 𝒰) : H1 G 𝒰.overFamily → H1 G 𝒱.overFamily :=
  (toOverFamilyRefinement r).pullbackHOne

@[simp]
lemma pullbackHOne_id (x : H1 G 𝒰.overFamily) :
    pullbackHOne G (PreZeroHypercover.Hom.id 𝒰.toPreZeroHypercover) x = x := by
  simpa only [pullbackHOne, toOverFamilyRefinement_id] using
    FamilyRefinement.pullbackHOne_refl x

lemma pullbackHOne_comp (r : 𝒱.Hom 𝒰) (s : 𝒲.Hom 𝒱)
    (x : H1 G 𝒰.overFamily) :
    pullbackHOne G (PreZeroHypercover.Hom.comp s r) x =
      pullbackHOne G s (pullbackHOne G r x) := by
  simpa only [pullbackHOne, toOverFamilyRefinement_comp] using
    FamilyRefinement.pullbackHOne_comp
      (toOverFamilyRefinement r) (toOverFamilyRefinement s) x

lemma pullbackHOne_eq (r r' : 𝒱.Hom 𝒰) (x : H1 G 𝒰.overFamily) :
    pullbackHOne G r x = pullbackHOne G r' x :=
  FamilyRefinement.pullbackHOne_eq
    (toOverFamilyRefinement r) (toOverFamilyRefinement r') x

@[simp]
lemma pullbackHOne_one (r : 𝒱.Hom 𝒰) :
    pullbackHOne G r (1 : H1 G 𝒰.overFamily) = 1 :=
  FamilyRefinement.pullbackHOne_one (toOverFamilyRefinement r)

end Cover.Hom

/-- One cover-level representative of a prospective global fppf `H¹` class. -/
structure FppfHOneRepresentative (X : Scheme.{u}) (G : (Over X)ᵒᵖ ⥤ GrpCat.{w}) where
  /-- The fppf covering family on which the cocycle is defined. -/
  cover : Cover.{v} fppfPrecoverage X
  /-- Its relative cover-level nonabelian cohomology class. -/
  value : PresheafOfGroups.H1 G cover.overFamily

namespace FppfHOneRepresentative

variable {X : Scheme.{u}} {G : (Over X)ᵒᵖ ⥤ GrpCat.{w}}

/-- Two representatives agree if their classes agree after pullback to one genuine common
fppf refinement. -/
def IsEquivalent (a b : FppfHOneRepresentative.{w, v, u} X G) : Prop :=
  ∃ (𝒲 : Cover.{v} fppfPrecoverage X)
    (ra : 𝒲.Hom a.cover) (rb : 𝒲.Hom b.cover),
      Cover.Hom.pullbackHOne G ra a.value =
        Cover.Hom.pullbackHOne G rb b.value

lemma isEquivalent_refl (a : FppfHOneRepresentative.{w, v, u} X G) :
    a.IsEquivalent a := by
  let r : a.cover.Hom a.cover := PreZeroHypercover.Hom.id a.cover.toPreZeroHypercover
  exact ⟨a.cover, r, r, rfl⟩

lemma isEquivalent_symm {a b : FppfHOneRepresentative.{w, v, u} X G}
    (h : a.IsEquivalent b) : b.IsEquivalent a := by
  obtain ⟨𝒲, ra, rb, h⟩ := h
  exact ⟨𝒲, rb, ra, h.symm⟩

lemma isEquivalent_trans {a b c : FppfHOneRepresentative.{w, v, u} X G}
    (hab : a.IsEquivalent b) (hbc : b.IsEquivalent c) : a.IsEquivalent c := by
  obtain ⟨𝒲, ra, rb, hab⟩ := hab
  obtain ⟨𝒵, sb, sc, hbc⟩ := hbc
  let 𝒬 : Cover.{v} fppfPrecoverage X := 𝒲.inter 𝒵
  let q𝒲 : 𝒬.Hom 𝒲 :=
    PreZeroHypercover.interFst 𝒲.toPreZeroHypercover 𝒵.toPreZeroHypercover
  let q𝒵 : 𝒬.Hom 𝒵 :=
    PreZeroHypercover.interSnd 𝒲.toPreZeroHypercover 𝒵.toPreZeroHypercover
  refine ⟨𝒬, PreZeroHypercover.Hom.comp q𝒲 ra,
    PreZeroHypercover.Hom.comp q𝒵 sc, ?_⟩
  rw [Cover.Hom.pullbackHOne_comp, Cover.Hom.pullbackHOne_comp]
  calc
    Cover.Hom.pullbackHOne G q𝒲
        (Cover.Hom.pullbackHOne G ra a.value) =
        Cover.Hom.pullbackHOne G q𝒲
          (Cover.Hom.pullbackHOne G rb b.value) :=
      congrArg (Cover.Hom.pullbackHOne G q𝒲) hab
    _ = Cover.Hom.pullbackHOne G q𝒵
        (Cover.Hom.pullbackHOne G sb b.value) := by
      rw [← Cover.Hom.pullbackHOne_comp,
        ← Cover.Hom.pullbackHOne_comp]
      exact Cover.Hom.pullbackHOne_eq G _ _ b.value
    _ = Cover.Hom.pullbackHOne G q𝒵
        (Cover.Hom.pullbackHOne G sc c.value) :=
      congrArg (Cover.Hom.pullbackHOne G q𝒵) hbc

/-- The common-refinement relation is an equivalence relation, using intersections of actual
fppf covers and independence of refinement choices on cover-level `H¹`. -/
theorem equivalence_isEquivalent :
    Equivalence (IsEquivalent (X := X) (G := G) :
      FppfHOneRepresentative.{w, v, u} X G → _ → Prop) where
  refl := isEquivalent_refl
  symm := isEquivalent_symm
  trans := isEquivalent_trans

end FppfHOneRepresentative

/-- Global nonabelian fppf cohomology in degree one, presented as the filtered-colimit quotient
of relative cover-level classes by genuine common refinement.  The cover index universe is
explicit. -/
def FppfHOne (X : Scheme.{u}) (G : (Over X)ᵒᵖ ⥤ GrpCat.{w}) : Type _ :=
  Quot (FppfHOneRepresentative.IsEquivalent (X := X) (G := G) :
    FppfHOneRepresentative.{w, v, u} X G → _ → Prop)

namespace FppfHOne

variable {X : Scheme.{u}} {G : (Over X)ᵒᵖ ⥤ GrpCat.{w}}

/-- Send one cover-level class into global fppf `H¹`. -/
def mk (𝒰 : Cover.{v} fppfPrecoverage X)
    (x : PresheafOfGroups.H1 G 𝒰.overFamily) :
    FppfHOne.{w, v, u} X G :=
  Quot.mk _ ⟨𝒰, x⟩

/-- The singleton identity cover, constructed directly from the checked fppf-cover theorem for
an identity morphism. -/
def identityCover (X : Scheme.{u}) : Cover.{v} fppfPrecoverage X :=
  Precoverage.ZeroHypercover.singleton (𝟙 X) (by
    exact Scheme.Hom.singleton_mem_fppfPrecoverage (𝟙 X))

/-- Every fppf cover refines the singleton identity cover. -/
def toIdentityCover (𝒰 : Cover.{v} fppfPrecoverage X) : 𝒰.Hom (identityCover X) where
  s₀ _ := PUnit.unit
  h₀ i := 𝒰.f i
  w₀ i := by
    change 𝒰.f i ≫ 𝟙 X = 𝒰.f i
    simp

/-- The distinguished trivial global fppf class. -/
instance : One (FppfHOne.{w, v, u} X G) where
  one := mk (identityCover X) 1

/-- The trivial cover-level class maps to the distinguished global class on every fppf cover. -/
@[simp]
theorem mk_one (𝒰 : Cover.{v} fppfPrecoverage X) :
    mk 𝒰 (1 : PresheafOfGroups.H1 G 𝒰.overFamily) =
      (1 : FppfHOne.{w, v, u} X G) := by
  apply Quot.sound
  let e : 𝒰.Hom 𝒰 := PreZeroHypercover.Hom.id 𝒰.toPreZeroHypercover
  exact ⟨𝒰, e, toIdentityCover 𝒰, by
    rw [Cover.Hom.pullbackHOne_one, Cover.Hom.pullbackHOne_one]⟩

/-- A class and its pullback to a refinement define the same global fppf class. -/
theorem class_pullback (𝒰 𝒱 : Cover.{v} fppfPrecoverage X) (r : 𝒱.Hom 𝒰)
    (x : PresheafOfGroups.H1 G 𝒰.overFamily) :
    mk 𝒱 (Cover.Hom.pullbackHOne G r x) = mk 𝒰 x := by
  apply Quot.sound
  let e : 𝒱.Hom 𝒱 := PreZeroHypercover.Hom.id 𝒱.toPreZeroHypercover
  refine ⟨𝒱, e, r, ?_⟩
  dsimp only [e]
  exact Cover.Hom.pullbackHOne_id G _

/-- Two cover-level classes have the same global class exactly when they agree after one common
fppf refinement. -/
theorem class_eq_iff (𝒰 𝒱 : Cover.{v} fppfPrecoverage X)
    (x : PresheafOfGroups.H1 G 𝒰.overFamily)
    (y : PresheafOfGroups.H1 G 𝒱.overFamily) :
    mk 𝒰 x = mk 𝒱 y ↔
      ∃ (𝒲 : Cover.{v} fppfPrecoverage X)
        (r : 𝒲.Hom 𝒰) (s : 𝒲.Hom 𝒱),
          Cover.Hom.pullbackHOne G r x =
            Cover.Hom.pullbackHOne G s y :=
  (FppfHOneRepresentative.equivalence_isEquivalent (X := X) (G := G)).quot_mk_eq_iff _ _

/-- The eliminator expressing the colimit universal property at the level of types: a compatible
family of maps out of all cover-level `H¹` types descends to global fppf `H¹`. -/
def lift {Y : Sort*}
    (f : ∀ (𝒰 : Cover.{v} fppfPrecoverage X),
      PresheafOfGroups.H1 G 𝒰.overFamily → Y)
    (compatible : ∀ (𝒰 𝒱 : Cover.{v} fppfPrecoverage X) (r : 𝒱.Hom 𝒰)
      (x : PresheafOfGroups.H1 G 𝒰.overFamily),
      f 𝒱 (Cover.Hom.pullbackHOne G r x) = f 𝒰 x) :
    FppfHOne.{w, v, u} X G → Y :=
  Quot.lift
    (fun a ↦ f a.cover a.value)
    (by
      rintro ⟨𝒰, x⟩ ⟨𝒱, y⟩ ⟨𝒲, r, s, h⟩
      calc
        f 𝒰 x = f 𝒲 (Cover.Hom.pullbackHOne G r x) :=
          (compatible 𝒰 𝒲 r x).symm
        _ = f 𝒲 (Cover.Hom.pullbackHOne G s y) := congrArg (f 𝒲) h
        _ = f 𝒱 y := compatible 𝒱 𝒲 s y)

@[simp]
theorem lift_mk {Y : Sort*}
    (f : ∀ (𝒰 : Cover.{v} fppfPrecoverage X),
      PresheafOfGroups.H1 G 𝒰.overFamily → Y)
    (compatible : ∀ (𝒰 𝒱 : Cover.{v} fppfPrecoverage X) (r : 𝒱.Hom 𝒰)
      (x : PresheafOfGroups.H1 G 𝒰.overFamily),
      f 𝒱 (Cover.Hom.pullbackHOne G r x) = f 𝒰 x)
    (𝒰 : Cover.{v} fppfPrecoverage X)
    (x : PresheafOfGroups.H1 G 𝒰.overFamily) :
    lift f compatible (mk 𝒰 x) = f 𝒰 x :=
  rfl

/-- Maps out of global fppf `H¹` are determined by all cover-level classes. -/
theorem funext {Y : Sort*} {f g : FppfHOne.{w, v, u} X G → Y}
    (h : ∀ (𝒰 : Cover.{v} fppfPrecoverage X)
      (x : PresheafOfGroups.H1 G 𝒰.overFamily),
      f (mk 𝒰 x) = g (mk 𝒰 x)) :
    f = g := by
  funext z
  induction z using Quot.inductionOn with
  | _ a => exact h a.cover a.value

end FppfHOne

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

universe v u

open CategoryTheory
open scoped CategoryTheory.MonObj

variable {S : Scheme.{u}}

/-- The presheaf of groups on `Over S` represented by a finite-flat commutative group scheme.
Its value on `T ⟶ S` is the actual group of `S`-morphisms `T ⟶ G`. -/
def pointPresheaf (G : FiniteFlatCommGroupScheme S) :
    (Over S)ᵒᵖ ⥤ GrpCat.{u} :=
  yonedaGrpObj G.obj.X

@[simp]
lemma pointPresheaf_obj (G : FiniteFlatCommGroupScheme S) (T : Over S) :
    (pointPresheaf G).obj (Opposite.op T) = GrpCat.of (G.Point T) :=
  rfl

/-- The underlying type-valued point presheaf of a finite-flat group scheme is an fppf sheaf on
the slice site.  This records that the coefficient system used below is genuinely representable,
not an arbitrary family of groups. -/
theorem pointPresheaf_isFppfSheaf (G : FiniteFlatCommGroupScheme S) :
    Presieve.IsSheaf (Scheme.fppfTopology.over S) (pointPresheaf G ⋙ forget GrpCat) := by
  letI : (pointPresheaf G ⋙ forget GrpCat).IsRepresentable :=
    (yonedaGrpObjRepresentableBy G.obj.X).isRepresentable
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

/-- Global fppf `H¹` of the representable point presheaf of a finite-flat commutative group
scheme.  This is a pointed type; its canonical commutative group structure is separate work. -/
abbrev FppfHOne (G : FiniteFlatCommGroupScheme S) : Type _ :=
  Scheme.FppfHOne.{u, v, u} S (pointPresheaf G)

/-- Send an actual relative cover-level class for a finite-flat group scheme to global fppf
`H¹`.  This is the representable downstream consumer of the globalization interface. -/
def fppfHOneClass (G : FiniteFlatCommGroupScheme S)
    (𝒰 : Scheme.Cover.{v} Scheme.fppfPrecoverage S)
    (x : PresheafOfGroups.H1 (pointPresheaf G) 𝒰.overFamily) :
    G.FppfHOne.{v} :=
  Scheme.FppfHOne.mk 𝒰 x

/-- Pulling a finite-flat group-scheme cocycle to a genuine refinement does not change its
global fppf class. -/
theorem fppfHOneClass_pullback (G : FiniteFlatCommGroupScheme S)
    (𝒰 𝒱 : Scheme.Cover.{v} Scheme.fppfPrecoverage S) (r : 𝒱.Hom 𝒰)
    (x : PresheafOfGroups.H1 (pointPresheaf G) 𝒰.overFamily) :
    fppfHOneClass G 𝒱 (Scheme.Cover.Hom.pullbackHOne (pointPresheaf G) r x) =
      fppfHOneClass G 𝒰 x :=
  Scheme.FppfHOne.class_pullback 𝒰 𝒱 r x

end AlgebraicGeometry.FiniteFlatCommGroupScheme

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfHOneCommGroup

/-!
# Functoriality of global commutative fppf H¹

A natural transformation of commutative-group-valued presheaves acts pointwise on Čech
cochains.  This file proves that the action preserves cocycles and cohomology, commutes with
genuine cover refinements, and descends to the common-refinement quotient defining global
relative fppf `H¹`.  Identity and composition are proved both before and after globalization.

The final section applies the construction to an actual morphism of finite-flat commutative
group schemes.  Its action on `H¹` is therefore induced by postcomposition on represented
points, rather than by an unrelated homomorphism between abstract groups.
-/

noncomputable section

open CategoryTheory

namespace CategoryTheory.PresheafOfCommGroups

universe wI wJ w v u

variable {C : Type u} [Category.{v} C]
variable {A B D : Cᵒᵖ ⥤ CommGrpCat.{w}}
variable {I : Type wI} {J : Type wJ}
variable {U : I → C} {V : J → C}

local instance coefficientCommGroupA (X : Cᵒᵖ) : CommGroup ((toGroups A).obj X) := by
  change CommGroup (A.obj X)
  infer_instance

local instance coefficientCommGroupB (X : Cᵒᵖ) : CommGroup ((toGroups B).obj X) := by
  change CommGroup (B.obj X)
  infer_instance

local instance coefficientCommGroupD (X : Cᵒᵖ) : CommGroup ((toGroups D).obj X) := by
  change CommGroup (D.obj X)
  infer_instance

namespace NatTrans

open PresheafOfGroups

variable (η : A ⟶ B)

/-- The component homomorphism, with both coefficient presheaves forgotten to groups. -/
abbrev appHom (X : Cᵒᵖ) : (toGroups A).obj X →* (toGroups B).obj X :=
  (η.app X).hom

/-- Elementwise naturality after forgetting both coefficient presheaves to groups. -/
lemma naturality_apply {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : (toGroups A).obj X) :
    (toGroups B).map f (appHom η X x) =
      appHom η Y ((toGroups A).map f x) := by
  change B.map f (appHom η X x) = appHom η Y (A.map f x)
  simpa only [CommGrpCat.comp_apply] using
    congrArg (fun q ↦ q x) (η.naturality f).symm

/-- Apply a natural transformation to a zero-cochain, component by component. -/
def mapZeroCochain (a : ZeroCochain (toGroups A) U) :
    ZeroCochain (toGroups B) U :=
  fun i ↦ appHom η (Opposite.op (U i)) (a i)

@[simp]
lemma mapZeroCochain_apply (a : ZeroCochain (toGroups A) U) (i : I) :
    mapZeroCochain η a i = appHom η (Opposite.op (U i)) (a i) :=
  rfl

/-- Apply a natural transformation to every overlap value of a one-cochain. -/
def mapOneCochain (c : OneCochain (toGroups A) U) :
    OneCochain (toGroups B) U where
  ev i j T a b := appHom η (Opposite.op T) (c.ev i j a b)
  ev_precomp i j T T' φ a b := by
    rw [naturality_apply, c.ev_precomp]

@[simp]
lemma mapOneCochain_ev (c : OneCochain (toGroups A) U)
    (i j : I) {T : C} (a : T ⟶ U i) (b : T ⟶ U j) :
    (mapOneCochain η c).ev i j a b =
      appHom η (Opposite.op T) (c.ev i j a b) :=
  rfl

/-- A coefficient map sends one-cocycles to one-cocycles. -/
def mapOneCocycle (c : OneCocycle (toGroups A) U) :
    OneCocycle (toGroups B) U where
  toOneCochain := mapOneCochain η c.toOneCochain
  ev_trans i j k T a b d := by
    change appHom η (Opposite.op T) (c.ev i j a b) *
        appHom η (Opposite.op T) (c.ev j k b d) =
      appHom η (Opposite.op T) (c.ev i k a d)
    rw [← map_mul, c.ev_trans]

@[simp]
lemma mapOneCocycle_toOneCochain (c : OneCocycle (toGroups A) U) :
    (mapOneCocycle η c).toOneCochain = mapOneCochain η c.toOneCochain :=
  rfl

@[simp]
lemma mapOneCocycle_one :
    mapOneCocycle η (1 : OneCocycle (toGroups A) U) = 1 := by
  apply PresheafOfCommGroups.OneCocycle.ext
  apply PresheafOfGroups.OneCochain.ext
  funext i j T a b
  exact map_one (appHom η (Opposite.op T))

/-- Coefficient maps preserve the explicit degree-one cohomology relation. -/
lemma map_oneCohomologyRelation
    {c d : OneCochain (toGroups A) U}
    {a : ZeroCochain (toGroups A) U}
    (h : OneCohomologyRelation c d a) :
    OneCohomologyRelation (mapOneCochain η c) (mapOneCochain η d)
      (mapZeroCochain η a) := by
  intro i j T f g
  change (toGroups B).map f.op (appHom η (Opposite.op (U i)) (a i)) *
      appHom η (Opposite.op T) (c.ev i j f g) =
    appHom η (Opposite.op T) (d.ev i j f g) *
      (toGroups B).map g.op (appHom η (Opposite.op (U j)) (a j))
  rw [naturality_apply, naturality_apply, ← map_mul, ← map_mul]
  apply congrArg (appHom η (Opposite.op T))
  exact h i j f g

/-- Coefficient maps preserve cohomologous cocycles. -/
lemma map_isCohomologous {c d : OneCocycle (toGroups A) U}
    (h : c.IsCohomologous d) :
    (mapOneCocycle η c).IsCohomologous (mapOneCocycle η d) := by
  obtain ⟨a, ha⟩ := h
  exact ⟨mapZeroCochain η a, map_oneCohomologyRelation η ha⟩

/-- The map on cover-level `H¹` induced by a coefficient natural transformation. -/
def mapHOne : H1 A U → H1 B U :=
  Quot.lift
    (fun c ↦ (mapOneCocycle η c).class)
    (fun _ _ h ↦ (map_isCohomologous η h).class_eq)

@[simp]
lemma mapHOne_class (c : OneCocycle (toGroups A) U) :
    mapHOne η c.class = (mapOneCocycle η c).class :=
  rfl

/-- Mapping coefficients commutes with pointwise multiplication of commutative cocycles. -/
lemma mapOneCocycle_mul (c d : OneCocycle (toGroups A) U) :
    mapOneCocycle η (OneCocycle.mul A c d) =
      OneCocycle.mul B (mapOneCocycle η c) (mapOneCocycle η d) := by
  apply PresheafOfCommGroups.OneCocycle.ext
  apply PresheafOfGroups.OneCochain.ext
  funext i j T f g
  exact map_mul (appHom η (Opposite.op T)) _ _

/-- Cover-level functoriality is a homomorphism for the canonical `H¹` group laws. -/
def mapHOneHom : H1 A U →* H1 B U where
  toFun := mapHOne η
  map_one' := by
    change (mapOneCocycle η (1 : OneCocycle (toGroups A) U)).class = 1
    rw [mapOneCocycle_one]
    rfl
  map_mul' x y := by
    induction x using Quot.inductionOn with
    | _ c =>
      induction y using Quot.inductionOn with
      | _ d => exact congrArg OneCocycle.class (mapOneCocycle_mul η c d)

@[simp]
lemma mapHOneHom_apply (x : H1 A U) : mapHOneHom η x = mapHOne η x :=
  rfl

/-- Mapping a cocycle by the identity natural transformation changes nothing. -/
lemma mapOneCocycle_id (c : OneCocycle (toGroups A) U) :
    mapOneCocycle (𝟙 A) c = c := by
  apply PresheafOfCommGroups.OneCocycle.ext
  apply PresheafOfGroups.OneCochain.ext
  funext i j T f g
  rfl

/-- Mapping a cocycle by a composite is successive mapping. -/
lemma mapOneCocycle_comp (η : A ⟶ B) (θ : B ⟶ D)
    (c : OneCocycle (toGroups A) U) :
    mapOneCocycle (η ≫ θ) c = mapOneCocycle θ (mapOneCocycle η c) := by
  apply PresheafOfCommGroups.OneCocycle.ext
  apply PresheafOfGroups.OneCochain.ext
  funext i j T f g
  rfl

@[simp]
lemma mapHOneHom_id : mapHOneHom (𝟙 A) = MonoidHom.id (H1 A U) := by
  ext x
  induction x using Quot.inductionOn with
  | _ c => exact congrArg OneCocycle.class (mapOneCocycle_id c)

lemma mapHOneHom_comp (η : A ⟶ B) (θ : B ⟶ D) :
    mapHOneHom (U := U) (η ≫ θ) =
      (mapHOneHom (U := U) θ).comp (mapHOneHom (U := U) η) := by
  ext x
  induction x using Quot.inductionOn with
  | _ c => exact congrArg OneCocycle.class (mapOneCocycle_comp η θ c)

/-- Coefficient mapping commutes strictly with pullback of one-cocycles along a refinement. -/
lemma mapOneCocycle_pullback
    (r : PresheafOfGroups.FamilyRefinement V U)
    (c : OneCocycle (toGroups A) U) :
    mapOneCocycle η (r.pullbackOneCocycle c) =
      r.pullbackOneCocycle (mapOneCocycle η c) := by
  apply PresheafOfCommGroups.OneCocycle.ext
  apply PresheafOfGroups.OneCochain.ext
  funext i j T f g
  rfl

/-- Coefficient mapping and cover refinement commute on `H¹`. -/
lemma mapHOne_pullback
    (r : PresheafOfGroups.FamilyRefinement V U) (x : H1 A U) :
    mapHOneHom η (PresheafOfCommGroups.pullbackHOneHom A r x) =
      PresheafOfCommGroups.pullbackHOneHom B r (mapHOneHom η x) := by
  induction x using Quot.inductionOn with
  | _ c => exact congrArg OneCocycle.class (mapOneCocycle_pullback η r c)

end NatTrans

end CategoryTheory.PresheafOfCommGroups

namespace AlgebraicGeometry.Scheme.FppfHOne

universe w v u

open CategoryTheory.PresheafOfCommGroups

variable {X : Scheme.{u}} {A B D : (Over X)ᵒᵖ ⥤ CommGrpCat.{w}}

/-- Apply a coefficient natural transformation to a global fppf class.  On a representative
cover this is the pointwise map of its actual Čech cocycle. -/
def map (η : A ⟶ B) :
    Scheme.FppfHOne.{w, v, u} X (toGroups A) →
      Scheme.FppfHOne.{w, v, u} X (toGroups B) :=
  lift
    (fun 𝒰 x ↦ mk 𝒰 (PresheafOfCommGroups.NatTrans.mapHOneHom η x))
    (by
      intro 𝒰 𝒱 r x
      change mk 𝒱
          (PresheafOfCommGroups.NatTrans.mapHOneHom η
            (PresheafOfCommGroups.pullbackHOneHom A
              (Cover.Hom.toOverFamilyRefinement r) x)) = _
      rw [PresheafOfCommGroups.NatTrans.mapHOne_pullback]
      exact class_pullback 𝒰 𝒱 r
        (PresheafOfCommGroups.NatTrans.mapHOneHom η x))

@[simp]
lemma map_mk (η : A ⟶ B) (𝒰 : Cover.{v} fppfPrecoverage X)
    (x : H1 A 𝒰.overFamily) :
    map η (mk 𝒰 x) =
      mk 𝒰 (PresheafOfCommGroups.NatTrans.mapHOneHom η x) :=
  rfl

/-- Coefficient mapping preserves the global common-refinement product. -/
lemma map_mul (η : A ⟶ B)
    (x y : Scheme.FppfHOne.{w, v, u} X (toGroups A)) :
    map η (x * y) = map η x * map η y := by
  induction x using Quot.inductionOn with
  | _ a =>
      rcases a with ⟨𝒰, x⟩
      induction y using Quot.inductionOn with
      | _ b =>
          rcases b with ⟨𝒱, y⟩
          let 𝒬 : Cover.{v} fppfPrecoverage X := 𝒰.inter 𝒱
          let p𝒰 : Cover.Hom 𝒬 𝒰 := Cover.interFst 𝒰 𝒱
          let p𝒱 : Cover.Hom 𝒬 𝒱 := Cover.interSnd 𝒰 𝒱
          change map η (mk 𝒰 x * mk 𝒱 y) = map η (mk 𝒰 x) * map η (mk 𝒱 y)
          rw [mk_mul_mk_eq_mk_of_commonRefinement A 𝒰 𝒱 𝒬 p𝒰 p𝒱,
            map_mk, map_mk, map_mk,
            mk_mul_mk_eq_mk_of_commonRefinement B 𝒰 𝒱 𝒬 p𝒰 p𝒱]
          congr 1
          rw [_root_.map_mul]
          change
            PresheafOfCommGroups.NatTrans.mapHOneHom η
                (PresheafOfCommGroups.pullbackHOneHom A
                  (Cover.Hom.toOverFamilyRefinement p𝒰) x) *
              PresheafOfCommGroups.NatTrans.mapHOneHom η
                (PresheafOfCommGroups.pullbackHOneHom A
                  (Cover.Hom.toOverFamilyRefinement p𝒱) y) =
            PresheafOfCommGroups.pullbackHOneHom B
                (Cover.Hom.toOverFamilyRefinement p𝒰)
                (PresheafOfCommGroups.NatTrans.mapHOneHom η x) *
              PresheafOfCommGroups.pullbackHOneHom B
                (Cover.Hom.toOverFamilyRefinement p𝒱)
                (PresheafOfCommGroups.NatTrans.mapHOneHom η y)
          rw [PresheafOfCommGroups.NatTrans.mapHOne_pullback,
            PresheafOfCommGroups.NatTrans.mapHOne_pullback]

/-- Global relative fppf `H¹` is covariantly functorial in commutative coefficients. -/
def mapHom (η : A ⟶ B) :
    Scheme.FppfHOne.{w, v, u} X (toGroups A) →*
      Scheme.FppfHOne.{w, v, u} X (toGroups B) where
  toFun := map η
  map_one' := by
    change map η (mk (identityCover X) 1) = 1
    rw [map_mk, map_one, mk_one]
  map_mul' := map_mul η

@[simp]
lemma mapHom_apply (η : A ⟶ B)
    (x : Scheme.FppfHOne.{w, v, u} X (toGroups A)) :
    mapHom η x = map η x :=
  rfl

@[simp]
lemma map_id : map (𝟙 A) = id := by
  apply FppfHOne.funext
  intro 𝒰 x
  rw [map_mk]
  change mk 𝒰 (PresheafOfCommGroups.NatTrans.mapHOneHom (𝟙 A) x) = mk 𝒰 x
  rw [PresheafOfCommGroups.NatTrans.mapHOneHom_id]
  rfl

lemma map_comp (η : A ⟶ B) (θ : B ⟶ D) :
    map (η ≫ θ) = map θ ∘ map η := by
  apply FppfHOne.funext
  intro 𝒰 x
  rw [map_mk, Function.comp_apply, map_mk, map_mk]
  congr 1
  exact DFunLike.congr_fun
    (PresheafOfCommGroups.NatTrans.mapHOneHom_comp (U := 𝒰.overFamily) η θ) x

@[simp]
lemma mapHom_id : mapHom (𝟙 A) = MonoidHom.id _ := by
  ext x
  exact congrFun map_id x

lemma mapHom_comp (η : A ⟶ B) (θ : B ⟶ D) :
    mapHom (η ≫ θ) = (mapHom θ).comp (mapHom η) := by
  ext x
  exact congrFun (map_comp η θ) x

end AlgebraicGeometry.Scheme.FppfHOne

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

universe v u

open CategoryTheory.PresheafOfCommGroups
open scoped CategoryTheory.MonObj

variable {S : Scheme.{u}} {G H K : FiniteFlatCommGroupScheme S}

/-- A morphism of finite-flat commutative group schemes induces the natural transformation of
represented point presheaves given by postcomposition. -/
def commPointPresheafMap (f : G ⟶ H) : commPointPresheaf G ⟶ commPointPresheaf H where
  app T := ConcreteCategory.ofHom (C := CommGrpCat) (mapPoint f T.unop)
  naturality T U g := by
    apply CommGrpCat.ext
    intro x
    change (g.unop ≫ (show T.unop ⟶ G.obj.X from x)) ≫
        f.hom.hom.hom.hom =
      g.unop ≫ ((show T.unop ⟶ G.obj.X from x) ≫ f.hom.hom.hom.hom)
    exact Category.assoc _ _ _

@[simp]
theorem commPointPresheafMap_id (G : FiniteFlatCommGroupScheme S) :
    commPointPresheafMap (𝟙 G) = 𝟙 (commPointPresheaf G) := by
  ext T x
  change (show T.unop ⟶ G.obj.X from x) ≫ 𝟙 G.obj.X = x
  rw [Category.comp_id]

theorem commPointPresheafMap_comp (f : G ⟶ H) (g : H ⟶ K) :
    commPointPresheafMap (f ≫ g) =
      commPointPresheafMap f ≫ commPointPresheafMap g := by
  ext T x
  change (show T.unop ⟶ G.obj.X from x) ≫
      (f.hom.hom.hom.hom ≫ g.hom.hom.hom.hom) =
    ((show T.unop ⟶ G.obj.X from x) ≫ f.hom.hom.hom.hom) ≫
      g.hom.hom.hom.hom
  exact (Category.assoc _ _ _).symm

/-- The map on global fppf `H¹` induced by an actual finite-flat group-scheme morphism. -/
def fppfHOneMap (f : G ⟶ H) : G.FppfHOne.{v} →* H.FppfHOne.{v} :=
  Scheme.FppfHOne.mapHom (commPointPresheafMap f)

/-- On an actual cover-level class, the group-scheme map acts pointwise on its Čech cocycle. -/
@[simp]
theorem fppfHOneMap_class (f : G ⟶ H)
    (𝒰 : Scheme.Cover.{v} Scheme.fppfPrecoverage S)
    (x : H1 (commPointPresheaf G) 𝒰.overFamily) :
    fppfHOneMap f (fppfHOneClass G 𝒰 x) =
      fppfHOneClass H 𝒰 (NatTrans.mapHOneHom (commPointPresheafMap f) x) :=
  rfl

@[simp]
theorem fppfHOneMap_id (G : FiniteFlatCommGroupScheme S) :
    fppfHOneMap (𝟙 G) = MonoidHom.id G.FppfHOne.{v} := by
  ext x
  change Scheme.FppfHOne.mapHom (commPointPresheafMap (𝟙 G)) x = x
  rw [commPointPresheafMap_id, Scheme.FppfHOne.mapHom_id]
  rfl

theorem fppfHOneMap_comp (f : G ⟶ H) (g : H ⟶ K) :
    fppfHOneMap (f ≫ g) = (fppfHOneMap g).comp (fppfHOneMap f) := by
  ext x
  change Scheme.FppfHOne.mapHom (commPointPresheafMap (f ≫ g)) x =
    Scheme.FppfHOne.mapHom (commPointPresheafMap g)
      (Scheme.FppfHOne.mapHom (commPointPresheafMap f) x)
  rw [commPointPresheafMap_comp, Scheme.FppfHOne.mapHom_comp]
  rfl

/-- A certified scheme-theoretic kernel gives an exact pair on points of every test scheme.
This is the degree-zero exactness input later consumed by the low-degree fppf sequence. -/
theorem KernelPresentation.point_mulExact {f : G ⟶ H}
    (P : KernelPresentation f) (X : Over S) :
    Function.MulExact (mapPoint P.inclusion X) (mapPoint f X) := by
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy, _⟩ := P.existsUnique_point_lift X x hx
    exact ⟨y, hy⟩
  · rintro ⟨y, rfl⟩
    exact P.mapPoint_inclusion_eq_one X y

end AlgebraicGeometry.FiniteFlatCommGroupScheme

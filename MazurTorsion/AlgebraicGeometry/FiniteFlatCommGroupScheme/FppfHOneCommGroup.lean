/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfHOne

/-!
# The commutative group law on global fppf H¹

For a presheaf of commutative groups, pointwise multiplication and inversion preserve Čech
one-cocycles and cohomology.  This file first constructs that group law on Mathlib's cover-level
`PresheafOfGroups.H1`, then proves that genuine cover refinements act by homomorphisms.

The global law is descended through the common-refinement quotient defining `Scheme.FppfHOne`.
Products of classes represented on two covers are computed after pullback to their intersection.
No group structure is transported from an unrelated type.
-/

noncomputable section

open CategoryTheory

namespace CategoryTheory.PresheafOfCommGroups

universe wI wJ w v u

variable {C : Type u} [Category.{v} C]
variable (A : Cᵒᵖ ⥤ CommGrpCat.{w})
variable {I : Type wI} {J : Type wJ}
variable {U : I → C} {V : J → C}

/-- Forget a presheaf of commutative groups to a presheaf of groups. -/
abbrev toGroups : Cᵒᵖ ⥤ GrpCat.{w} :=
  A ⋙ forget₂ CommGrpCat GrpCat

local instance coefficientCommGroup (X : Cᵒᵖ) : CommGroup ((toGroups A).obj X) := by
  change CommGroup (A.obj X)
  infer_instance

/-- Cover-level degree-one cohomology with commutative coefficients. -/
abbrev H1 (U : I → C) :=
  PresheafOfGroups.H1 (toGroups A) U

namespace OneCocycle

open PresheafOfGroups

/-- Pointwise multiplication of one-cocycles with commutative coefficients. -/
def mul (c d : OneCocycle (toGroups A) U) : OneCocycle (toGroups A) U where
  toOneCochain := c.toOneCochain * d.toOneCochain
  ev_trans i j k T a b e := by
    change (c.ev i j a b * d.ev i j a b) * (c.ev j k b e * d.ev j k b e) =
      c.ev i k a e * d.ev i k a e
    rw [mul_mul_mul_comm, c.ev_trans, d.ev_trans]

/-- Pointwise inversion of a one-cocycle with commutative coefficients. -/
def inv (c : OneCocycle (toGroups A) U) : OneCocycle (toGroups A) U where
  toOneCochain := c.toOneCochain⁻¹
  ev_trans i j k T a b e := by
    change (c.ev i j a b)⁻¹ * (c.ev j k b e)⁻¹ = (c.ev i k a e)⁻¹
    rw [mul_comm, ← mul_inv_rev, c.ev_trans]

@[simp]
lemma mul_toOneCochain (c d : OneCocycle (toGroups A) U) :
    (mul A c d).toOneCochain = c.toOneCochain * d.toOneCochain :=
  rfl

@[simp]
lemma inv_toOneCochain (c : OneCocycle (toGroups A) U) :
    (inv A c).toOneCochain = c.toOneCochain⁻¹ :=
  rfl

lemma ext {c d : OneCocycle (toGroups A) U}
    (h : c.toOneCochain = d.toOneCochain) : c = d := by
  cases c
  cases d
  cases h
  rfl

@[simp]
lemma one_mul (c : OneCocycle (toGroups A) U) : mul A 1 c = c := by
  apply ext
  apply PresheafOfGroups.OneCochain.ext
  funext i j T f g
  exact _root_.one_mul _

@[simp]
lemma mul_one (c : OneCocycle (toGroups A) U) : mul A c 1 = c := by
  apply ext
  apply PresheafOfGroups.OneCochain.ext
  funext i j T f g
  exact _root_.mul_one _

lemma mul_assoc (a b c : OneCocycle (toGroups A) U) :
    mul A (mul A a b) c = mul A a (mul A b c) := by
  apply ext
  apply PresheafOfGroups.OneCochain.ext
  funext i j T f g
  exact _root_.mul_assoc _ _ _

lemma mul_comm (a b : OneCocycle (toGroups A) U) : mul A a b = mul A b a := by
  apply ext
  apply PresheafOfGroups.OneCochain.ext
  funext i j T f g
  exact _root_.mul_comm _ _

@[simp]
lemma inv_mul (c : OneCocycle (toGroups A) U) : mul A (inv A c) c = 1 := by
  apply ext
  apply PresheafOfGroups.OneCochain.ext
  funext i j T f g
  exact inv_mul_cancel _

end OneCocycle

open PresheafOfGroups

/-- Cohomologous cocycles may be multiplied when the coefficient groups are commutative. -/
lemma isCohomologous_mul {a b c d : OneCocycle (toGroups A) U}
    (hab : a.IsCohomologous b) (hcd : c.IsCohomologous d) :
    (OneCocycle.mul A a c).IsCohomologous (OneCocycle.mul A b d) := by
  obtain ⟨α, hα⟩ := hab
  obtain ⟨β, hβ⟩ := hcd
  refine ⟨α * β, ?_⟩
  intro i j T f g
  change (toGroups A).map f.op (α i * β i) * (a.ev i j f g * c.ev i j f g) =
    (b.ev i j f g * d.ev i j f g) * (toGroups A).map g.op (α j * β j)
  rw [map_mul, map_mul]
  calc
    ((toGroups A).map f.op (α i) * (toGroups A).map f.op (β i)) *
        (a.ev i j f g * c.ev i j f g) =
        ((toGroups A).map f.op (α i) * a.ev i j f g) *
          ((toGroups A).map f.op (β i) * c.ev i j f g) := by
            ac_rfl
    _ = (b.ev i j f g * (toGroups A).map g.op (α j)) *
        (d.ev i j f g * (toGroups A).map g.op (β j)) := by
          rw [hα i j f g, hβ i j f g]
    _ = (b.ev i j f g * d.ev i j f g) *
        ((toGroups A).map g.op (α j) * (toGroups A).map g.op (β j)) := by
          ac_rfl

/-- Cohomologous cocycles may be inverted when the coefficient groups are commutative. -/
lemma isCohomologous_inv {a b : OneCocycle (toGroups A) U}
    (hab : a.IsCohomologous b) :
    (OneCocycle.inv A a).IsCohomologous (OneCocycle.inv A b) := by
  obtain ⟨α, hα⟩ := hab
  refine ⟨α⁻¹, ?_⟩
  intro i j T f g
  change (toGroups A).map f.op ((α i)⁻¹) * (a.ev i j f g)⁻¹ =
    (b.ev i j f g)⁻¹ * (toGroups A).map g.op ((α j)⁻¹)
  simpa only [map_inv, mul_inv_rev, mul_comm] using congrArg Inv.inv (hα i j f g)

/-- Multiplication on cover-level `H¹`, descended from pointwise multiplication of cocycles. -/
def hOneMul : H1 A U → H1 A U → H1 A U :=
  Quot.lift₂
    (fun a b ↦ (OneCocycle.mul A a b).class)
    (fun a _b _b' h ↦
      (isCohomologous_mul A
        ((PresheafOfGroups.OneCocycle.equivalence_isCohomologous _ _).refl a) h).class_eq)
    (fun _a _a' b h ↦
      (isCohomologous_mul A h
        ((PresheafOfGroups.OneCocycle.equivalence_isCohomologous _ _).refl b)).class_eq)

/-- Inversion on cover-level `H¹`, descended from pointwise inversion of cocycles. -/
def hOneInv : H1 A U → H1 A U :=
  Quot.lift
    (fun a ↦ (OneCocycle.inv A a).class)
    (fun _ _ h ↦ (isCohomologous_inv A h).class_eq)

@[simp]
lemma hOneMul_class (a b : OneCocycle (toGroups A) U) :
    hOneMul A a.class b.class = (OneCocycle.mul A a b).class :=
  rfl

@[simp]
lemma hOneInv_class (a : OneCocycle (toGroups A) U) :
    hOneInv A a.class = (OneCocycle.inv A a).class :=
  rfl

/-- The canonical commutative group structure on cover-level degree-one cohomology. -/
noncomputable instance hOneCommGroup : CommGroup (H1 A U) where
  mul := hOneMul A
  one := (1 : PresheafOfGroups.H1 (toGroups A) U)
  inv := hOneInv A
  mul_assoc x y z := by
    induction x using Quot.inductionOn with
    | _ a =>
      induction y using Quot.inductionOn with
      | _ b =>
        induction z using Quot.inductionOn with
        | _ c => exact congrArg OneCocycle.class (OneCocycle.mul_assoc A a b c)
  one_mul x := by
    induction x using Quot.inductionOn with
    | _ a => exact congrArg OneCocycle.class (OneCocycle.one_mul A a)
  mul_one x := by
    induction x using Quot.inductionOn with
    | _ a => exact congrArg OneCocycle.class (OneCocycle.mul_one A a)
  inv_mul_cancel x := by
    induction x using Quot.inductionOn with
    | _ a => exact congrArg OneCocycle.class (OneCocycle.inv_mul A a)
  mul_comm x y := by
    induction x using Quot.inductionOn with
    | _ a =>
      induction y using Quot.inductionOn with
      | _ b => exact congrArg OneCocycle.class (OneCocycle.mul_comm A a b)

/-- Pullback of commutative-coefficient cocycles preserves pointwise multiplication. -/
lemma pullbackOneCocycle_mul
    (VU : PresheafOfGroups.FamilyRefinement V U)
    (a b : PresheafOfGroups.OneCocycle (toGroups A) U) :
    VU.pullbackOneCocycle (OneCocycle.mul A a b) =
      OneCocycle.mul A (VU.pullbackOneCocycle a) (VU.pullbackOneCocycle b) := by
  apply OneCocycle.ext
  apply PresheafOfGroups.OneCochain.ext
  funext i j T f g
  rfl

/-- Cover-level `H¹` pullback is a homomorphism for commutative coefficients. -/
def pullbackHOneHom (VU : PresheafOfGroups.FamilyRefinement V U) :
    H1 A U →* H1 A V where
  toFun := VU.pullbackHOne
  map_one' := VU.pullbackHOne_one
  map_mul' x y := by
    induction x using Quot.inductionOn with
    | _ a =>
      induction y using Quot.inductionOn with
      | _ b =>
        exact congrArg PresheafOfGroups.OneCocycle.class
          (pullbackOneCocycle_mul A VU a b)

@[simp]
lemma pullbackHOneHom_apply (VU : PresheafOfGroups.FamilyRefinement V U)
    (x : H1 A U) :
    pullbackHOneHom A VU x = VU.pullbackHOne x :=
  rfl

end CategoryTheory.PresheafOfCommGroups

namespace AlgebraicGeometry.Scheme

universe w v u

open CategoryTheory.PresheafOfGroups

namespace Cover

variable {X : Scheme.{u}}

/-- First projection from the intersection of two genuine fppf covers. -/
noncomputable def interFst (𝒰 𝒱 : Cover.{v} fppfPrecoverage X) :
    AlgebraicGeometry.Scheme.Cover.Hom (𝒰.inter 𝒱) 𝒰 :=
  PreZeroHypercover.interFst 𝒰.toPreZeroHypercover 𝒱.toPreZeroHypercover

/-- Second projection from the intersection of two genuine fppf covers. -/
noncomputable def interSnd (𝒰 𝒱 : Cover.{v} fppfPrecoverage X) :
    AlgebraicGeometry.Scheme.Cover.Hom (𝒰.inter 𝒱) 𝒱 :=
  PreZeroHypercover.interSnd 𝒰.toPreZeroHypercover 𝒱.toPreZeroHypercover

/-- A cover refining each of two covers refines their intersection. -/
noncomputable def interLift {𝒰 𝒱 𝒲 : Cover.{v} fppfPrecoverage X}
    (r : 𝒲.Hom 𝒰) (s : 𝒲.Hom 𝒱) :
    AlgebraicGeometry.Scheme.Cover.Hom 𝒲 (𝒰.inter 𝒱) :=
  PreZeroHypercover.interLift r s

end Cover

namespace Cover.Hom

variable {X : Scheme.{u}} {𝒰 𝒱 : Cover.{v} fppfPrecoverage X}

/-- Relative cover-level pullback as a homomorphism for commutative coefficients. -/
def pullbackCommHOneHom (A : (Over X)ᵒᵖ ⥤ CommGrpCat.{w}) (r : 𝒱.Hom 𝒰) :
    CategoryTheory.PresheafOfCommGroups.H1 A 𝒰.overFamily →*
      CategoryTheory.PresheafOfCommGroups.H1 A 𝒱.overFamily :=
  CategoryTheory.PresheafOfCommGroups.pullbackHOneHom A
    (toOverFamilyRefinement r)

@[simp]
lemma pullbackCommHOneHom_apply (A : (Over X)ᵒᵖ ⥤ CommGrpCat.{w})
    (r : 𝒱.Hom 𝒰) (x : CategoryTheory.PresheafOfCommGroups.H1 A 𝒰.overFamily) :
    pullbackCommHOneHom A r x =
      pullbackHOne (CategoryTheory.PresheafOfCommGroups.toGroups A) r x :=
  rfl

lemma pullbackHOne_inv (A : (Over X)ᵒᵖ ⥤ CommGrpCat.{w})
    (r : 𝒱.Hom 𝒰) (x : CategoryTheory.PresheafOfCommGroups.H1 A 𝒰.overFamily) :
    pullbackHOne (CategoryTheory.PresheafOfCommGroups.toGroups A) r x⁻¹ =
      (pullbackHOne (CategoryTheory.PresheafOfCommGroups.toGroups A) r x)⁻¹ :=
  map_inv (pullbackCommHOneHom A r) x

end Cover.Hom

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.FppfHOne

universe w v u

open CategoryTheory.PresheafOfCommGroups

variable {X : Scheme.{u}} (A : (Over X)ᵒᵖ ⥤ CommGrpCat.{w})

/-- Multiply two cover-level classes after pulling them to the intersection of their covers,
then send the result to global fppf `H¹`. -/
def mulClass (𝒰 𝒱 : Cover.{v} fppfPrecoverage X)
    (x : H1 A 𝒰.overFamily) (y : H1 A 𝒱.overFamily) :
    Scheme.FppfHOne.{w, v, u} X (toGroups A) :=
  mk (𝒰.inter 𝒱)
    (Cover.Hom.pullbackCommHOneHom A (Cover.interFst 𝒰 𝒱) x *
      Cover.Hom.pullbackCommHOneHom A (Cover.interSnd 𝒰 𝒱) y)

/-- The product may be computed on any genuine common refinement of the two representing
covers.  This theorem removes all dependence on the chosen intersection presentation. -/
theorem mulClass_eq_mk_of_commonRefinement
    (𝒰 𝒱 𝒲 : Cover.{v} fppfPrecoverage X)
    (r : 𝒲.Hom 𝒰) (s : 𝒲.Hom 𝒱)
    (x : H1 A 𝒰.overFamily) (y : H1 A 𝒱.overFamily) :
    mulClass A 𝒰 𝒱 x y =
      mk 𝒲 (Cover.Hom.pullbackCommHOneHom A r x *
        Cover.Hom.pullbackCommHOneHom A s y) := by
  let p𝒰 : Cover.Hom (𝒰.inter 𝒱) 𝒰 := Cover.interFst 𝒰 𝒱
  let p𝒱 : Cover.Hom (𝒰.inter 𝒱) 𝒱 := Cover.interSnd 𝒰 𝒱
  let t : Cover.Hom 𝒲 (𝒰.inter 𝒱) := Cover.interLift r s
  let z : H1 A (Cover.overFamily (𝒰.inter 𝒱)) :=
    Cover.Hom.pullbackCommHOneHom A p𝒰 x *
      Cover.Hom.pullbackCommHOneHom A p𝒱 y
  change mk (𝒰.inter 𝒱) z = _
  calc
    mk (𝒰.inter 𝒱) z =
        mk 𝒲 (Cover.Hom.pullbackCommHOneHom A t z) :=
      (class_pullback (𝒰.inter 𝒱) 𝒲 t z).symm
    _ = mk 𝒲 (Cover.Hom.pullbackCommHOneHom A r x *
        Cover.Hom.pullbackCommHOneHom A s y) := by
      congr 1
      dsimp only [z]
      rw [map_mul]
      change Cover.Hom.pullbackHOne (toGroups A) t
          (Cover.Hom.pullbackHOne (toGroups A) p𝒰 x) *
        Cover.Hom.pullbackHOne (toGroups A) t
          (Cover.Hom.pullbackHOne (toGroups A) p𝒱 y) = _
      rw [← Cover.Hom.pullbackHOne_comp, ← Cover.Hom.pullbackHOne_comp,
        Cover.Hom.pullbackHOne_eq (toGroups A)
          (PreZeroHypercover.Hom.comp t p𝒰) r x,
        Cover.Hom.pullbackHOne_eq (toGroups A)
          (PreZeroHypercover.Hom.comp t p𝒱) s y]
      rfl

/-- Refining the right-hand representative does not change its global product. -/
lemma mulClass_pullback_right
    (𝒰 𝒱 𝒱' : Cover.{v} fppfPrecoverage X) (r : 𝒱'.Hom 𝒱)
    (x : H1 A 𝒰.overFamily) (y : H1 A 𝒱.overFamily) :
    mulClass A 𝒰 𝒱' x (Cover.Hom.pullbackCommHOneHom A r y) =
      mulClass A 𝒰 𝒱 x y := by
  let 𝒬 : Cover.{v} fppfPrecoverage X := 𝒰.inter 𝒱'
  let p𝒰 : Cover.Hom 𝒬 𝒰 := Cover.interFst 𝒰 𝒱'
  let p𝒱' : Cover.Hom 𝒬 𝒱' := Cover.interSnd 𝒰 𝒱'
  let p𝒱 : Cover.Hom 𝒬 𝒱 := PreZeroHypercover.Hom.comp p𝒱' r
  rw [mulClass_eq_mk_of_commonRefinement A 𝒰 𝒱' 𝒬 p𝒰 p𝒱',
    mulClass_eq_mk_of_commonRefinement A 𝒰 𝒱 𝒬 p𝒰 p𝒱]
  congr 1
  change Cover.Hom.pullbackHOne (toGroups A) p𝒰 x *
      Cover.Hom.pullbackHOne (toGroups A) p𝒱'
        (Cover.Hom.pullbackHOne (toGroups A) r y) =
    Cover.Hom.pullbackHOne (toGroups A) p𝒰 x *
      Cover.Hom.pullbackHOne (toGroups A) p𝒱 y
  rw [← Cover.Hom.pullbackHOne_comp]

/-- Refining the left-hand representative does not change its global product. -/
lemma mulClass_pullback_left
    (𝒰 𝒰' 𝒱 : Cover.{v} fppfPrecoverage X) (r : 𝒰'.Hom 𝒰)
    (x : H1 A 𝒰.overFamily) (y : H1 A 𝒱.overFamily) :
    mulClass A 𝒰' 𝒱 (Cover.Hom.pullbackCommHOneHom A r x) y =
      mulClass A 𝒰 𝒱 x y := by
  let 𝒬 : Cover.{v} fppfPrecoverage X := 𝒰'.inter 𝒱
  let p𝒰' : Cover.Hom 𝒬 𝒰' := Cover.interFst 𝒰' 𝒱
  let p𝒰 : Cover.Hom 𝒬 𝒰 := PreZeroHypercover.Hom.comp p𝒰' r
  let p𝒱 : Cover.Hom 𝒬 𝒱 := Cover.interSnd 𝒰' 𝒱
  rw [mulClass_eq_mk_of_commonRefinement A 𝒰' 𝒱 𝒬 p𝒰' p𝒱,
    mulClass_eq_mk_of_commonRefinement A 𝒰 𝒱 𝒬 p𝒰 p𝒱]
  congr 1
  change Cover.Hom.pullbackHOne (toGroups A) p𝒰'
      (Cover.Hom.pullbackHOne (toGroups A) r x) *
        Cover.Hom.pullbackHOne (toGroups A) p𝒱 y =
    Cover.Hom.pullbackHOne (toGroups A) p𝒰 x *
      Cover.Hom.pullbackHOne (toGroups A) p𝒱 y
  rw [← Cover.Hom.pullbackHOne_comp]

/-- Multiplication on global fppf `H¹`, descended from multiplication on cover-level classes. -/
def mul : Scheme.FppfHOne.{w, v, u} X (toGroups A) →
    Scheme.FppfHOne.{w, v, u} X (toGroups A) →
      Scheme.FppfHOne.{w, v, u} X (toGroups A) :=
  lift
    (fun 𝒰 x ↦
      lift
        (fun 𝒱 y ↦ mulClass A 𝒰 𝒱 x y)
        (fun 𝒱 𝒱' r y ↦ mulClass_pullback_right A 𝒰 𝒱 𝒱' r x y))
    (by
      intro 𝒰 𝒰' r x
      apply FppfHOne.funext
      intro 𝒱 y
      exact mulClass_pullback_left A 𝒰 𝒰' 𝒱 r x y)

@[simp]
lemma mul_mk (𝒰 𝒱 : Cover.{v} fppfPrecoverage X)
    (x : H1 A 𝒰.overFamily) (y : H1 A 𝒱.overFamily) :
    mul A (mk 𝒰 x) (mk 𝒱 y) = mulClass A 𝒰 𝒱 x y :=
  rfl

/-- Global multiplication may be evaluated on any supplied common refinement. -/
theorem mul_mk_eq_mk_of_commonRefinement
    (𝒰 𝒱 𝒲 : Cover.{v} fppfPrecoverage X)
    (r : 𝒲.Hom 𝒰) (s : 𝒲.Hom 𝒱)
    (x : H1 A 𝒰.overFamily) (y : H1 A 𝒱.overFamily) :
    mul A (mk 𝒰 x) (mk 𝒱 y) =
      mk 𝒲 (Cover.Hom.pullbackCommHOneHom A r x *
        Cover.Hom.pullbackCommHOneHom A s y) :=
  mulClass_eq_mk_of_commonRefinement A 𝒰 𝒱 𝒲 r s x y

/-- Inversion on global fppf `H¹`, descended on each representative cover. -/
def inv : Scheme.FppfHOne.{w, v, u} X (toGroups A) →
    Scheme.FppfHOne.{w, v, u} X (toGroups A) :=
  lift
    (fun 𝒰 x ↦ mk 𝒰 x⁻¹)
    (by
      intro 𝒰 𝒱 r x
      rw [← Cover.Hom.pullbackHOne_inv A r x]
      exact class_pullback 𝒰 𝒱 r x⁻¹)

@[simp]
lemma inv_mk (𝒰 : Cover.{v} fppfPrecoverage X) (x : H1 A 𝒰.overFamily) :
    inv A (mk 𝒰 x) = mk 𝒰 x⁻¹ :=
  rfl

lemma one_mul_global (z : Scheme.FppfHOne.{w, v, u} X (toGroups A)) :
    mul A 1 z = z := by
  induction z using Quot.inductionOn with
  | _ a =>
      rcases a with ⟨𝒰, x⟩
      let e : Cover.Hom 𝒰 𝒰 := PreZeroHypercover.Hom.id 𝒰.toPreZeroHypercover
      change mul A (mk (identityCover X) 1) (mk 𝒰 x) = mk 𝒰 x
      rw [mul_mk_eq_mk_of_commonRefinement A (identityCover X) 𝒰 𝒰
        (toIdentityCover 𝒰) e]
      congr 1
      change Cover.Hom.pullbackHOne (toGroups A) (toIdentityCover 𝒰) 1 *
          Cover.Hom.pullbackHOne (toGroups A) e x = x
      rw [Cover.Hom.pullbackHOne_one, Cover.Hom.pullbackHOne_id, one_mul]

lemma mul_one_global (z : Scheme.FppfHOne.{w, v, u} X (toGroups A)) :
    mul A z 1 = z := by
  induction z using Quot.inductionOn with
  | _ a =>
      rcases a with ⟨𝒰, x⟩
      let e : Cover.Hom 𝒰 𝒰 := PreZeroHypercover.Hom.id 𝒰.toPreZeroHypercover
      change mul A (mk 𝒰 x) (mk (identityCover X) 1) = mk 𝒰 x
      rw [mul_mk_eq_mk_of_commonRefinement A 𝒰 (identityCover X) 𝒰
        e (toIdentityCover 𝒰)]
      congr 1
      change Cover.Hom.pullbackHOne (toGroups A) e x *
          Cover.Hom.pullbackHOne (toGroups A) (toIdentityCover 𝒰) 1 = x
      rw [Cover.Hom.pullbackHOne_one, Cover.Hom.pullbackHOne_id, mul_one]

lemma inv_mul_cancel_global (z : Scheme.FppfHOne.{w, v, u} X (toGroups A)) :
    mul A (inv A z) z = 1 := by
  induction z using Quot.inductionOn with
  | _ a =>
      rcases a with ⟨𝒰, x⟩
      let e : Cover.Hom 𝒰 𝒰 := PreZeroHypercover.Hom.id 𝒰.toPreZeroHypercover
      change mul A (inv A (mk 𝒰 x)) (mk 𝒰 x) = 1
      rw [inv_mk, mul_mk_eq_mk_of_commonRefinement A 𝒰 𝒰 𝒰 e e]
      change mk 𝒰 (Cover.Hom.pullbackHOne (toGroups A) e x⁻¹ *
        Cover.Hom.pullbackHOne (toGroups A) e x) = 1
      simp only [e, Cover.Hom.pullbackHOne_id, inv_mul_cancel, mk_one]

lemma mul_comm_global (x y : Scheme.FppfHOne.{w, v, u} X (toGroups A)) :
    mul A x y = mul A y x := by
  induction x using Quot.inductionOn with
  | _ a =>
      rcases a with ⟨𝒰, x⟩
      induction y using Quot.inductionOn with
      | _ b =>
          rcases b with ⟨𝒱, y⟩
          let 𝒬 : Cover.{v} fppfPrecoverage X := 𝒰.inter 𝒱
          let p𝒰 : Cover.Hom 𝒬 𝒰 := Cover.interFst 𝒰 𝒱
          let p𝒱 : Cover.Hom 𝒬 𝒱 := Cover.interSnd 𝒰 𝒱
          change mul A (mk 𝒰 x) (mk 𝒱 y) = mul A (mk 𝒱 y) (mk 𝒰 x)
          rw [mul_mk_eq_mk_of_commonRefinement A 𝒰 𝒱 𝒬 p𝒰 p𝒱,
            mul_mk_eq_mk_of_commonRefinement A 𝒱 𝒰 𝒬 p𝒱 p𝒰]
          congr 1
          exact _root_.mul_comm _ _

lemma mul_assoc_global
    (x y z : Scheme.FppfHOne.{w, v, u} X (toGroups A)) :
    mul A (mul A x y) z = mul A x (mul A y z) := by
  induction x using Quot.inductionOn with
  | _ a =>
      rcases a with ⟨𝒰, x⟩
      induction y using Quot.inductionOn with
      | _ b =>
          rcases b with ⟨𝒱, y⟩
          induction z using Quot.inductionOn with
          | _ c =>
              rcases c with ⟨𝒲, z⟩
              let 𝒰𝒱 : Cover.{v} fppfPrecoverage X := 𝒰.inter 𝒱
              let 𝒯 : Cover.{v} fppfPrecoverage X := 𝒰𝒱.inter 𝒲
              let p𝒰𝒱 : Cover.Hom 𝒯 𝒰𝒱 := Cover.interFst 𝒰𝒱 𝒲
              let p𝒲 : Cover.Hom 𝒯 𝒲 := Cover.interSnd 𝒰𝒱 𝒲
              let p𝒰₀ : Cover.Hom 𝒰𝒱 𝒰 := Cover.interFst 𝒰 𝒱
              let p𝒱₀ : Cover.Hom 𝒰𝒱 𝒱 := Cover.interSnd 𝒰 𝒱
              let p𝒰 : Cover.Hom 𝒯 𝒰 := PreZeroHypercover.Hom.comp p𝒰𝒱 p𝒰₀
              let p𝒱 : Cover.Hom 𝒯 𝒱 := PreZeroHypercover.Hom.comp p𝒰𝒱 p𝒱₀
              let e : Cover.Hom 𝒯 𝒯 := PreZeroHypercover.Hom.id 𝒯.toPreZeroHypercover
              let x𝒯 : H1 A 𝒯.overFamily := Cover.Hom.pullbackCommHOneHom A p𝒰 x
              let y𝒯 : H1 A 𝒯.overFamily := Cover.Hom.pullbackCommHOneHom A p𝒱 y
              let z𝒯 : H1 A 𝒯.overFamily := Cover.Hom.pullbackCommHOneHom A p𝒲 z
              change mul A (mul A (mk 𝒰 x) (mk 𝒱 y)) (mk 𝒲 z) =
                mul A (mk 𝒰 x) (mul A (mk 𝒱 y) (mk 𝒲 z))
              calc
                mul A (mul A (mk 𝒰 x) (mk 𝒱 y)) (mk 𝒲 z) =
                    mul A (mk 𝒯 (x𝒯 * y𝒯)) (mk 𝒲 z) := by
                  rw [mul_mk_eq_mk_of_commonRefinement A 𝒰 𝒱 𝒯 p𝒰 p𝒱]
                _ = mk 𝒯 ((x𝒯 * y𝒯) * z𝒯) := by
                  rw [mul_mk_eq_mk_of_commonRefinement A 𝒯 𝒲 𝒯 e p𝒲]
                  congr 1
                  change Cover.Hom.pullbackHOne (toGroups A) e (x𝒯 * y𝒯) * z𝒯 =
                    (x𝒯 * y𝒯) * z𝒯
                  simp only [e, Cover.Hom.pullbackHOne_id]
                _ = mk 𝒯 (x𝒯 * (y𝒯 * z𝒯)) :=
                  congrArg (mk 𝒯) (_root_.mul_assoc x𝒯 y𝒯 z𝒯)
                _ = mul A (mk 𝒰 x) (mk 𝒯 (y𝒯 * z𝒯)) := by
                  symm
                  rw [mul_mk_eq_mk_of_commonRefinement A 𝒰 𝒯 𝒯 p𝒰 e]
                  congr 1
                  change x𝒯 * Cover.Hom.pullbackHOne (toGroups A) e (y𝒯 * z𝒯) =
                    x𝒯 * (y𝒯 * z𝒯)
                  simp only [e, Cover.Hom.pullbackHOne_id]
                _ = mul A (mk 𝒰 x) (mul A (mk 𝒱 y) (mk 𝒲 z)) := by
                  rw [mul_mk_eq_mk_of_commonRefinement A 𝒱 𝒲 𝒯 p𝒱 p𝒲]

/-- The canonical commutative group structure on relative global fppf `H¹` with commutative
coefficients.  Its operations are descended from the actual cover-level cocycle operations. -/
noncomputable instance commGroup :
    CommGroup (Scheme.FppfHOne.{w, v, u} X (toGroups A)) where
  mul := mul A
  one := (1 : Scheme.FppfHOne.{w, v, u} X (toGroups A))
  inv := inv A
  mul_assoc := mul_assoc_global A
  one_mul := one_mul_global A
  mul_one := mul_one_global A
  inv_mul_cancel := inv_mul_cancel_global A
  mul_comm := mul_comm_global A

@[simp]
lemma mk_mul_mk (𝒰 𝒱 : Cover.{v} fppfPrecoverage X)
    (x : H1 A 𝒰.overFamily) (y : H1 A 𝒱.overFamily) :
    mk 𝒰 x * mk 𝒱 y = mulClass A 𝒰 𝒱 x y :=
  rfl

theorem mk_mul_mk_eq_mk_of_commonRefinement
    (𝒰 𝒱 𝒲 : Cover.{v} fppfPrecoverage X)
    (r : 𝒲.Hom 𝒰) (s : 𝒲.Hom 𝒱)
    (x : H1 A 𝒰.overFamily) (y : H1 A 𝒱.overFamily) :
    mk 𝒰 x * mk 𝒱 y =
      mk 𝒲 (Cover.Hom.pullbackCommHOneHom A r x *
        Cover.Hom.pullbackCommHOneHom A s y) :=
  mul_mk_eq_mk_of_commonRefinement A 𝒰 𝒱 𝒲 r s x y

@[simp]
lemma inv_mk' (𝒰 : Cover.{v} fppfPrecoverage X) (x : H1 A 𝒰.overFamily) :
    (mk 𝒰 x)⁻¹ = mk 𝒰 x⁻¹ :=
  rfl

end AlgebraicGeometry.Scheme.FppfHOne

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

universe v u

open CategoryTheory.PresheafOfCommGroups

variable {S : Scheme.{u}}

/-- The canonical commutative group structure on fppf `H¹` of an actual finite-flat
commutative group scheme. -/
noncomputable instance fppfHOneCommGroup (G : FiniteFlatCommGroupScheme S) :
    CommGroup G.FppfHOne.{v} :=
  Scheme.FppfHOne.commGroup (A := commPointPresheaf G)

/-- Multiplication of global finite-flat group-scheme classes is computed by pulling their
actual cover-level cocycles to any supplied common refinement. -/
theorem fppfHOneClass_mul_of_commonRefinement (G : FiniteFlatCommGroupScheme S)
    (𝒰 𝒱 𝒲 : Scheme.Cover.{v} Scheme.fppfPrecoverage S)
    (r : 𝒲.Hom 𝒰) (s : 𝒲.Hom 𝒱)
    (x : H1 (commPointPresheaf G) 𝒰.overFamily)
    (y : H1 (commPointPresheaf G) 𝒱.overFamily) :
    fppfHOneClass G 𝒰 x * fppfHOneClass G 𝒱 y =
      fppfHOneClass G 𝒲
        (Scheme.Cover.Hom.pullbackCommHOneHom (commPointPresheaf G) r x *
          Scheme.Cover.Hom.pullbackCommHOneHom (commPointPresheaf G) s y) :=
  Scheme.FppfHOne.mk_mul_mk_eq_mk_of_commonRefinement
    (commPointPresheaf G) 𝒰 𝒱 𝒲 r s x y

/-- Inversion of a global finite-flat group-scheme class is induced by inversion of its actual
cover-level cocycle class. -/
@[simp]
theorem fppfHOneClass_inv (G : FiniteFlatCommGroupScheme S)
    (𝒰 : Scheme.Cover.{v} Scheme.fppfPrecoverage S)
    (x : H1 (commPointPresheaf G) 𝒰.overFamily) :
    (fppfHOneClass G 𝒰 x)⁻¹ =
      fppfHOneClass G 𝒰
        (x⁻¹ : H1 (commPointPresheaf G) 𝒰.overFamily) :=
  Scheme.FppfHOne.inv_mk' (commPointPresheaf G) 𝒰 x

end AlgebraicGeometry.FiniteFlatCommGroupScheme

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Algebra.Category.Grp.Ulift
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.FppfHOneFunctoriality

/-!
# Universe invariance of the checked global fppf `H¹`

The concrete sheafification API for the relative fppf site uses universe-lifted coefficient
groups.  This file proves that the checked common-refinement model of global `H¹` is unchanged
by that lift.  The proof acts explicitly on zero-cochains, one-cocycles, cover-level quotient
classes, and finally the common-refinement quotient; universe invariance is not assumed.
-/

noncomputable section

open CategoryTheory

namespace CategoryTheory.PresheafOfCommGroups.UniverseLift

universe w' wI w v u

variable {C : Type u} [Category.{v} C]
variable (A : Cᵒᵖ ⥤ CommGrpCat.{w})
variable {I : Type wI} {U : I → C}

open PresheafOfGroups

private abbrev lifted : Cᵒᵖ ⥤ CommGrpCat.{max w w'} :=
  A ⋙ CommGrpCat.uliftFunctor.{w'}

private def zeroUp (a : ZeroCochain (toGroups A) U) :
    ZeroCochain (toGroups (lifted.{w'} A)) U :=
  fun i ↦ ULift.up (a i)

private def zeroDown (a : ZeroCochain (toGroups (lifted.{w'} A)) U) :
    ZeroCochain (toGroups A) U :=
  fun i ↦ (a i).down

private def cochainUp (c : OneCochain (toGroups A) U) :
    OneCochain (toGroups (lifted.{w'} A)) U where
  ev i j T a b := ULift.up (c.ev i j a b)
  ev_precomp i j T T' φ a b := by
    exact congrArg ULift.up (c.ev_precomp i j φ a b)

private def cochainDown (c : OneCochain (toGroups (lifted.{w'} A)) U) :
    OneCochain (toGroups A) U where
  ev i j T a b := (c.ev i j a b).down
  ev_precomp i j T T' φ a b := by
    exact congrArg ULift.down (c.ev_precomp i j φ a b)

private def cocycleUp (c : OneCocycle (toGroups A) U) :
    OneCocycle (toGroups (lifted.{w'} A)) U where
  toOneCochain := cochainUp A c.toOneCochain
  ev_trans i j k T a b d := by
    exact congrArg ULift.up (c.ev_trans i j k a b d)

private def cocycleDown (c : OneCocycle (toGroups (lifted.{w'} A)) U) :
    OneCocycle (toGroups A) U where
  toOneCochain := cochainDown A c.toOneCochain
  ev_trans i j k T a b d := by
    exact congrArg ULift.down (c.ev_trans i j k a b d)

private lemma relation_up {c d : OneCocycle (toGroups A) U}
    (h : c.IsCohomologous d) :
    (cocycleUp A c).IsCohomologous (cocycleUp A d) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨zeroUp A a, ?_⟩
  intro i j T f g
  exact congrArg ULift.up (ha i j f g)

private lemma relation_down {c d : OneCocycle (toGroups (lifted.{w'} A)) U}
    (h : c.IsCohomologous d) :
    (cocycleDown A c).IsCohomologous (cocycleDown A d) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨zeroDown A a, ?_⟩
  intro i j T f g
  exact congrArg ULift.down (ha i j f g)

private def hOneUp : H1 A U → H1 (lifted.{w'} A) U :=
  Quot.lift
    (fun c ↦ (cocycleUp A c).class)
    (fun _ _ h ↦ (relation_up A h).class_eq)

private def hOneDown : H1 (lifted.{w'} A) U → H1 A U :=
  Quot.lift
    (fun c ↦ (cocycleDown A c).class)
    (fun _ _ h ↦ (relation_down A h).class_eq)

private lemma cocycle_down_up (c : OneCocycle (toGroups A) U) :
    cocycleDown A (cocycleUp A c) = c := by
  apply PresheafOfGroups.FamilyRefinement.oneCocycle_ext
  apply OneCochain.ext
  funext i j T f g
  rfl

private lemma cocycle_up_down
    (c : OneCocycle (toGroups (lifted.{w'} A)) U) :
    cocycleUp A (cocycleDown A c) = c := by
  apply PresheafOfGroups.FamilyRefinement.oneCocycle_ext
  apply OneCochain.ext
  funext i j T f g
  rfl

private lemma hOne_down_up (x : H1 A U) :
    hOneDown A (hOneUp A x) = x := by
  induction x using Quot.inductionOn with
  | _ c => exact congrArg OneCocycle.class (cocycle_down_up A c)

private lemma hOne_up_down (x : H1 (lifted.{w'} A) U) :
    hOneUp A (hOneDown A x) = x := by
  induction x using Quot.inductionOn with
  | _ c => exact congrArg OneCocycle.class (cocycle_up_down A c)

private lemma cocycle_up_mul (c d : OneCocycle (toGroups A) U) :
    cocycleUp A (OneCocycle.mul A c d) =
      OneCocycle.mul (lifted.{w'} A) (cocycleUp A c) (cocycleUp A d) := by
  apply PresheafOfGroups.FamilyRefinement.oneCocycle_ext
  apply OneCochain.ext
  funext i j T f g
  rfl

private lemma hOne_up_mul (x y : H1 A U) :
    hOneUp A (x * y) = hOneUp A x * hOneUp A y := by
  induction x using Quot.inductionOn with
  | _ c =>
      induction y using Quot.inductionOn with
      | _ d => exact congrArg OneCocycle.class (cocycle_up_mul A c d)

private lemma cocycle_up_pullback {J : Type*} {V : J → C}
    (r : FamilyRefinement V U) (c : OneCocycle (toGroups A) U) :
    cocycleUp A (r.pullbackOneCocycle c) =
      r.pullbackOneCocycle (cocycleUp A c) := by
  apply PresheafOfGroups.FamilyRefinement.oneCocycle_ext
  apply OneCochain.ext
  funext i j T f g
  rfl

private lemma hOne_up_pullback {J : Type*} {V : J → C}
    (r : FamilyRefinement V U) (x : H1 A U) :
    hOneUp A (r.pullbackHOne x) = r.pullbackHOne (hOneUp A x) := by
  induction x using Quot.inductionOn with
  | _ c => exact congrArg OneCocycle.class (cocycle_up_pullback A r c)

private lemma cocycle_down_pullback {J : Type*} {V : J → C}
    (r : FamilyRefinement V U)
    (c : OneCocycle (toGroups (lifted.{w'} A)) U) :
    cocycleDown A (r.pullbackOneCocycle c) =
      r.pullbackOneCocycle (cocycleDown A c) := by
  apply PresheafOfGroups.FamilyRefinement.oneCocycle_ext
  apply OneCochain.ext
  funext i j T f g
  rfl

private lemma hOne_down_pullback {J : Type*} {V : J → C}
    (r : FamilyRefinement V U) (x : H1 (lifted.{w'} A) U) :
    hOneDown A (r.pullbackHOne x) = r.pullbackHOne (hOneDown A x) := by
  induction x using Quot.inductionOn with
  | _ c => exact congrArg OneCocycle.class (cocycle_down_pullback A r c)

end CategoryTheory.PresheafOfCommGroups.UniverseLift

namespace AlgebraicGeometry.Scheme.FppfHOne

universe w' w v u

open CategoryTheory.PresheafOfCommGroups
open CategoryTheory.PresheafOfCommGroups.UniverseLift

variable {X : Scheme.{u}}
variable (A : (Over X)ᵒᵖ ⥤ CommGrpCat.{w})

private abbrev lifted : (Over X)ᵒᵖ ⥤ CommGrpCat.{max w w'} :=
  A ⋙ CommGrpCat.uliftFunctor.{w'}

private def globalUp :
    Scheme.FppfHOne.{w, v, u} X (toGroups A) →
      Scheme.FppfHOne.{max w w', v, u} X (toGroups (lifted.{w'} A)) :=
  FppfHOne.lift
    (fun cover x ↦ FppfHOne.mk cover (hOneUp A x))
    (fun cover₁ cover₂ r x ↦ by
      rw [show hOneUp A (Cover.Hom.pullbackHOne (toGroups A) r x) =
          Cover.Hom.pullbackHOne (toGroups (lifted.{w'} A)) r (hOneUp A x) by
        simpa only [Cover.Hom.pullbackHOne] using
          hOne_up_pullback A (Cover.Hom.toOverFamilyRefinement r) x]
      exact FppfHOne.class_pullback cover₁ cover₂ r (hOneUp A x))

private def globalDown :
    Scheme.FppfHOne.{max w w', v, u} X (toGroups (lifted.{w'} A)) →
      Scheme.FppfHOne.{w, v, u} X (toGroups A) :=
  FppfHOne.lift
    (fun cover x ↦ FppfHOne.mk cover (hOneDown A x))
    (fun cover₁ cover₂ r x ↦ by
      rw [show hOneDown A
          (Cover.Hom.pullbackHOne (toGroups (lifted.{w'} A)) r x) =
          Cover.Hom.pullbackHOne (toGroups A) r (hOneDown A x) by
        simpa only [Cover.Hom.pullbackHOne] using
          hOne_down_pullback A (Cover.Hom.toOverFamilyRefinement r) x]
      exact FppfHOne.class_pullback cover₁ cover₂ r (hOneDown A x))

private lemma global_down_up
    (x : Scheme.FppfHOne.{w, v, u} X (toGroups A)) :
    globalDown A (globalUp A x :
      Scheme.FppfHOne.{max w w', v, u} X (toGroups (lifted.{w'} A))) = x := by
  induction x using Quot.inductionOn with
  | _ a => exact congrArg (FppfHOne.mk a.cover) (hOne_down_up A a.value)

private lemma global_up_down
    (x : Scheme.FppfHOne.{max w w', v, u} X (toGroups (lifted.{w'} A))) :
    (globalUp A (globalDown A x) :
      Scheme.FppfHOne.{max w w', v, u} X (toGroups (lifted.{w'} A))) = x := by
  induction x using Quot.inductionOn with
  | _ a => exact congrArg (FppfHOne.mk a.cover) (hOne_up_down A a.value)

private lemma global_up_mul
    (x y : Scheme.FppfHOne.{w, v, u} X (toGroups A)) :
    (globalUp A (x * y) :
        Scheme.FppfHOne.{max w w', v, u} X (toGroups (lifted.{w'} A))) =
      (globalUp A x :
          Scheme.FppfHOne.{max w w', v, u} X (toGroups (lifted.{w'} A))) *
        (globalUp A y :
          Scheme.FppfHOne.{max w w', v, u} X (toGroups (lifted.{w'} A))) := by
  induction x using Quot.inductionOn with
  | _ a =>
      induction y using Quot.inductionOn with
      | _ b =>
          change (globalUp A (FppfHOne.mk a.cover a.value *
              FppfHOne.mk b.cover b.value) =
            globalUp A (FppfHOne.mk a.cover a.value) *
              globalUp A (FppfHOne.mk b.cover b.value) : Prop)
          let common : Cover.{v} fppfPrecoverage X := a.cover.inter b.cover
          let pa : common.Hom a.cover := Cover.interFst a.cover b.cover
          let pb : common.Hom b.cover := Cover.interSnd a.cover b.cover
          rw [mk_mul_mk_eq_mk_of_commonRefinement A a.cover b.cover common pa pb]
          change FppfHOne.mk common (hOneUp A
              (Cover.Hom.pullbackCommHOneHom A pa a.value *
                Cover.Hom.pullbackCommHOneHom A pb b.value)) =
            FppfHOne.mk a.cover (hOneUp A a.value) *
              FppfHOne.mk b.cover (hOneUp A b.value)
          calc
            FppfHOne.mk common (hOneUp A
                (Cover.Hom.pullbackCommHOneHom A pa a.value *
                  Cover.Hom.pullbackCommHOneHom A pb b.value)) =
                FppfHOne.mk common
                  (hOneUp A (Cover.Hom.pullbackCommHOneHom A pa a.value) *
                    hOneUp A (Cover.Hom.pullbackCommHOneHom A pb b.value)) :=
              congrArg (FppfHOne.mk common) (hOne_up_mul A _ _)
            _ = FppfHOne.mk common
                (Cover.Hom.pullbackCommHOneHom (lifted.{w'} A) pa (hOneUp A a.value) *
                  Cover.Hom.pullbackCommHOneHom (lifted.{w'} A) pb (hOneUp A b.value)) := by
              apply congrArg (FppfHOne.mk common)
              apply congrArg₂ (· * ·)
              · simpa only [Cover.Hom.pullbackCommHOneHom,
                  PresheafOfCommGroups.pullbackHOneHom_apply] using
                  hOne_up_pullback A (Cover.Hom.toOverFamilyRefinement pa) a.value
              · simpa only [Cover.Hom.pullbackCommHOneHom,
                  PresheafOfCommGroups.pullbackHOneHom_apply] using
                  hOne_up_pullback A (Cover.Hom.toOverFamilyRefinement pb) b.value
            _ = FppfHOne.mk a.cover (hOneUp A a.value) *
                FppfHOne.mk b.cover (hOneUp A b.value) :=
              (mk_mul_mk_eq_mk_of_commonRefinement (lifted.{w'} A)
                a.cover b.cover common pa pb (hOneUp A a.value) (hOneUp A b.value)).symm

/-- Global fppf `H¹` is invariant under the standard universe-lift functor on commutative
coefficient groups.  Both directions are induced explicitly on cocycles and commute with genuine
cover refinements. -/
noncomputable def mulEquivUlift :
    Scheme.FppfHOne.{w, v, u} X (toGroups A) ≃*
      Scheme.FppfHOne.{max w w', v, u} X
        (toGroups (A ⋙ CommGrpCat.uliftFunctor.{w'})) where
  toFun := globalUp A
  invFun := globalDown A
  left_inv := global_down_up A
  right_inv := global_up_down A
  map_mul' := global_up_mul A

end AlgebraicGeometry.Scheme.FppfHOne

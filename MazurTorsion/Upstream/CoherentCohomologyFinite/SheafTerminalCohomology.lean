/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import Mathlib.Algebra.FreeAbelianGroup.Finsupp

/-!
# Cohomology at a terminal site object

Mathlib's Mayer--Vietoris sequence is phrased using `Sheaf.H'`, whose source
is the sheafified free abelian presheaf on a representable.  At a terminal
object that source is the constant sheaf `ℤ`, so `H'` agrees with global
sheaf cohomology `Sheaf.H`.
-/

open CategoryTheory Limits Opposite

universe u v

namespace CategoryTheory.Sheaf

/-- The free abelian group on one generator is the universe lift of `ℤ`. -/
noncomputable def freePUnitIsoULiftZ :
    AddCommGrpCat.free.{v}.obj PUnit ≅
      AddCommGrpCat.of (ULift.{v} ℤ) :=
  (FreeAbelianGroup.equivFinsupp PUnit).trans
    ((Finsupp.uniqueAddEquiv PUnit.unit : (PUnit →₀ ℤ) ≃+ ℤ).trans
      (AddEquiv.ulift.symm : ℤ ≃+ ULift.{v} ℤ))
    |>.toAddCommGrpIso

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrpCat.{v}]

/--
At a terminal object, the source sheaf used to define `H'` is the constant
abelian sheaf with value `ULift ℤ`.
-/
noncomputable def H'_terminal_sourceIso
    {T : C} (hT : IsTerminal T) :
    (presheafToSheaf J _).obj
        ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj
          AddCommGrpCat.free).obj T)
      ≅ (constantSheaf J AddCommGrpCat.{v}).obj
          (AddCommGrpCat.of (ULift ℤ)) :=
  (presheafToSheaf J _).mapIso
    (Functor.isoWhiskerRight
        (NatIso.ofComponents
          (fun _ => Equiv.toIso
            { toFun := fun _ => PUnit.unit
              invFun := fun _ => hT.from _
              left_inv := fun _ => hT.hom_ext _ _
              right_inv := fun _ => rfl })
          (fun _ => by ext; rfl))
        AddCommGrpCat.free ≪≫
      Functor.constComp _ PUnit AddCommGrpCat.free ≪≫
      (Functor.const Cᵒᵖ).mapIso freePUnitIsoULiftZ)

variable [HasExt (Sheaf J AddCommGrpCat.{v})]

/-- Cohomology evaluated at a terminal site object agrees with global cohomology. -/
noncomputable def H'_terminal_addEquiv_H
    (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ)
    {T : C} (hT : IsTerminal T) :
    F.H' n T ≃+ F.H n :=
  let α := H'_terminal_sourceIso (J := J) hT
  { toEquiv :=
      { toFun := (Abelian.Ext.mk₀ α.inv).precomp F (zero_add n)
        invFun := (Abelian.Ext.mk₀ α.hom).precomp F (zero_add n)
        left_inv := by
          intro x
          change Abelian.Ext
            ((presheafToSheaf J AddCommGrpCat).obj
              ((yoneda ⋙ (Functor.whiskeringRight _ _ _).obj
                AddCommGrpCat.free).obj T)) F n at x
          change (Abelian.Ext.mk₀ α.hom).comp
            ((Abelian.Ext.mk₀ α.inv).comp x (zero_add n)) (zero_add n) = x
          exact
            (Abelian.Ext.comp_assoc_of_second_deg_zero
              (Abelian.Ext.mk₀ α.hom)
              (Abelian.Ext.mk₀ α.inv) x (zero_add n)).symm.trans (by
                rw [Abelian.Ext.mk₀_comp_mk₀, α.hom_inv_id,
                  Abelian.Ext.mk₀_id_comp])
        right_inv := by
          intro y
          change Abelian.Ext
            ((constantSheaf J AddCommGrpCat).obj
              (AddCommGrpCat.of (ULift ℤ))) F n at y
          change (Abelian.Ext.mk₀ α.inv).comp
            ((Abelian.Ext.mk₀ α.hom).comp y (zero_add n)) (zero_add n) = y
          exact
            (Abelian.Ext.comp_assoc_of_second_deg_zero
              (Abelian.Ext.mk₀ α.inv)
              (Abelian.Ext.mk₀ α.hom) y (zero_add n)).symm.trans (by
                rw [Abelian.Ext.mk₀_comp_mk₀, α.inv_hom_id,
                  Abelian.Ext.mk₀_id_comp]) }
    map_add' := by
      intro x y
      exact ((Abelian.Ext.mk₀ α.inv).precomp F (zero_add n)).map_add x y }

end CategoryTheory.Sheaf

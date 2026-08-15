/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Finite presentations of finite free sheaves

The free sheaf on a finite type has its tautological presentation: the
chosen free generators and no relations.  The one-generator specialization
gives a finite presentation of the unit module.
-/

open CategoryTheory Limits

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafFinitePresentation

universe u v

variable {C : Type u} [Category.{v} C]
  {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose
    (forget₂ RingCat.{u} AddCommGrpCat.{u})]

/-- The tautological presentation of a free sheaf: its free basis generates
and the kernel of the identity generating map is zero. -/
def freePresentation (I : Type u) :
    (SheafOfModules.free (R := R) I).Presentation where
  generators := SheafOfModules.free.generatingSections I
  relations :=
    { I := PEmpty.{u + 1}
      s := PEmpty.elim
      epi := by
        have hzero :
            IsZero
              (kernel
                (SheafOfModules.free.generatingSections
                  (R := R) I).π) :=
          isZero_kernel_of_mono _
        exact ⟨fun g h _ => hzero.eq_of_src g h⟩ }

instance (I : Type u) [Finite I] :
    (freePresentation R I).IsFinite where
  isFiniteType_generators := ⟨inferInstanceAs (Finite I)⟩
  isFiniteType_relations :=
    ⟨inferInstanceAs (Finite PEmpty.{u + 1})⟩

/-- The free sheaf on one generator is canonically the unit sheaf. -/
private noncomputable def freePUnitIso :
    SheafOfModules.free (R := R) PUnit.{u + 1} ≅
      SheafOfModules.unit R := by
  let f : SheafOfModules.free (R := R) PUnit.{u + 1} ⟶
      SheafOfModules.unit R :=
    (SheafOfModules.unit R).freeHomEquiv.symm
      (fun _ => (SheafOfModules.unit R).unitHomEquiv (𝟙 _))
  let g : SheafOfModules.unit R ⟶
      SheafOfModules.free (R := R) PUnit.{u + 1} :=
    SheafOfModules.ιFree PUnit.unit
  have hgf : g ≫ f = 𝟙 _ := by
    change SheafOfModules.ιFree PUnit.unit ≫ f = 𝟙 _
    calc
      _ = (SheafOfModules.unit R).unitHomEquiv.symm
          ((SheafOfModules.unit R).freeHomEquiv f PUnit.unit) :=
        (SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply
          f PUnit.unit).symm
      _ = (SheafOfModules.unit R).unitHomEquiv.symm
          ((SheafOfModules.unit R).unitHomEquiv (𝟙 _)) := by
        rw [show
          (SheafOfModules.unit R).freeHomEquiv f =
            fun _ => (SheafOfModules.unit R).unitHomEquiv (𝟙 _) from
          Equiv.apply_symm_apply _ _]
      _ = _ := Equiv.symm_apply_apply _ _
  have hfg : f ≫ g = 𝟙 _ := by
    apply Cofan.IsColimit.hom_ext
      (SheafOfModules.isColimitFreeCofan PUnit.{u + 1})
    intro i
    cases i
    change SheafOfModules.ιFree PUnit.unit ≫ f ≫ g =
      SheafOfModules.ιFree PUnit.unit ≫ 𝟙 _
    rw [← Category.assoc, hgf,
      Category.id_comp, Category.comp_id]
  exact ⟨f, g, hfg, hgf⟩

/-- The canonical one-element generating family of the unit sheaf. -/
def unitGenerators :
    (SheafOfModules.unit R).GeneratingSections where
  I := PUnit.{u + 1}
  s := (SheafOfModules.unit R).freeHomEquiv
    (freePUnitIso R).hom
  epi := by
    rw [Equiv.symm_apply_apply]
    letI : IsIso (freePUnitIso R).hom :=
      (freePUnitIso R).isIso_hom
    infer_instance

/-- The one-generator, zero-relation presentation of the unit sheaf. -/
def unitPresentation :
    (SheafOfModules.unit R).Presentation where
  generators := unitGenerators R
  relations :=
    { I := PEmpty.{u + 1}
      s := PEmpty.elim
      epi := by
        have hmono : Mono (unitGenerators R).π := by
          dsimp only [unitGenerators,
            SheafOfModules.GeneratingSections.π]
          rw [Equiv.symm_apply_apply]
          infer_instance
        have hzero :
            IsZero (kernel (unitGenerators R).π) :=
          isZero_kernel_of_mono _
        exact ⟨fun g h _ => hzero.eq_of_src g h⟩ }

instance : (unitPresentation R).IsFinite where
  isFiniteType_generators :=
    ⟨inferInstanceAs (Finite PUnit.{u + 1})⟩
  isFiniteType_relations :=
    ⟨inferInstanceAs (Finite PEmpty.{u + 1})⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafFinitePresentation

/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SheafCechCochains
import MazurTorsion.Upstream.AINTLIB.ForMathlib.TopCatSheafRestrict

/-!
# Sheaf-level Cech terms

This file defines the terms in the sheaf-level Cech resolution associated to a family of
open subsets. In degree `n`, the term is the product of the pushforwards of the restrictions
to all `(n + 1)`-fold intersections. Its sections on an open `V` are identified with families
of sections on the intersections of `V` with those tuple intersections.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}}
variable (F : Sheaf AddCommGrpCat.{u} X) {ι : Type u}
variable (U : ι → Opens X) (n : ℕ)

/-- The restriction-pushforward factor in a sheaf-level Cech term. -/
noncomputable abbrev cechTermFactor (i : Fin (n + 1) → ι) :
    Sheaf AddCommGrpCat.{u} X :=
  (restrict AddCommGrpCat
    (∏ᶜ fun k : Fin (n + 1) => U (i k)).isOpenEmbedding ⋙
    pushforward AddCommGrpCat
      (∏ᶜ fun k : Fin (n + 1) => U (i k)).inclusion').obj F

/-- Degree `n` of the sheaf-level Cech resolution associated to the open family `U`. -/
noncomputable def cechTerm : Sheaf AddCommGrpCat.{u} X :=
  ∏ᶜ cechTermFactor F U n

private noncomputable def cechTermFactorSectionsIso (V : Opens X)
    (i : Fin (n + 1) → ι) :
    (cechTermFactor F U n i).obj.obj (op V) ≅
      F.obj.obj (op (V ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i k))) :=
  eqToIso (by
    rw [toRestrict_obj_obj_obj, Opens.functor_map_eq_inf])

private noncomputable def cechTermForgetDiagramIso :
    Discrete.functor (cechTermFactor F U n) ⋙ forget AddCommGrpCat X ≅
      Discrete.functor fun i : Fin (n + 1) → ι =>
        (cechTermFactor F U n i).obj :=
  Discrete.natIso (fun _ => Iso.refl _)

private noncomputable def cechTermForgetIso :
    (cechTerm F U n).obj ≅
      ∏ᶜ fun i : Fin (n + 1) → ι => (cechTermFactor F U n i).obj := by
  letI : HasLimit (Discrete.functor (cechTermFactor F U n) ⋙
      forget AddCommGrpCat X) :=
    hasLimit_of_iso (cechTermForgetDiagramIso F U n).symm
  exact preservesLimitIso (forget AddCommGrpCat X)
      (Discrete.functor (cechTermFactor F U n)) ≪≫
    HasLimit.isoOfNatIso (cechTermForgetDiagramIso F U n)

private theorem cechTermForgetIso_hom_π (i : Fin (n + 1) → ι) :
    (cechTermForgetIso F U n).hom ≫
        Pi.π (fun i : Fin (n + 1) → ι => (cechTermFactor F U n i).obj) i =
      (Pi.π (cechTermFactor F U n) i).hom := by
  change (cechTermForgetIso F U n).hom ≫
      limit.π (Discrete.functor fun i : Fin (n + 1) → ι =>
        (cechTermFactor F U n i).obj) ⟨i⟩ =
      (forget AddCommGrpCat X).map
        (limit.π (Discrete.functor (cechTermFactor F U n)) ⟨i⟩)
  letI : HasLimit (Discrete.functor (cechTermFactor F U n) ⋙
      forget AddCommGrpCat X) := hasLimit_of_iso
    (cechTermForgetDiagramIso F U n).symm
  have hnat :
      (HasLimit.isoOfNatIso (cechTermForgetDiagramIso F U n)).hom ≫
          limit.π (Discrete.functor fun i : Fin (n + 1) → ι =>
            (cechTermFactor F U n i).obj) ⟨i⟩ =
        limit.π (Discrete.functor (cechTermFactor F U n) ⋙
          forget AddCommGrpCat X) ⟨i⟩ := by
    have happ : (cechTermForgetDiagramIso F U n).hom.app ⟨i⟩ =
        𝟙 ((cechTermFactor F U n i).obj) := rfl
    have hbase :
        (HasLimit.isoOfNatIso (cechTermForgetDiagramIso F U n)).hom ≫
            limit.π (Discrete.functor fun i : Fin (n + 1) → ι ↦
              (cechTermFactor F U n i).obj) ⟨i⟩ =
          limit.π (Discrete.functor (cechTermFactor F U n) ⋙
              forget AddCommGrpCat X) ⟨i⟩ ≫
            (cechTermForgetDiagramIso F U n).hom.app ⟨i⟩ :=
      HasLimit.isoOfNatIso_hom_π (cechTermForgetDiagramIso F U n) ⟨i⟩
    have hcomp : limit.π (Discrete.functor (cechTermFactor F U n) ⋙
          forget AddCommGrpCat X) ⟨i⟩ ≫
          (cechTermForgetDiagramIso F U n).hom.app ⟨i⟩ =
        limit.π (Discrete.functor (cechTermFactor F U n) ⋙
          forget AddCommGrpCat X) ⟨i⟩ := by
      rw [happ]
      exact Category.comp_id _
    exact hbase.trans hcomp
  have hpreserves :
      (preservesLimitIso (forget AddCommGrpCat X)
          (Discrete.functor (cechTermFactor F U n))).hom ≫
          limit.π (Discrete.functor (cechTermFactor F U n) ⋙
            forget AddCommGrpCat X) ⟨i⟩ =
        (forget AddCommGrpCat X).map
          (limit.π (Discrete.functor (cechTermFactor F U n)) ⟨i⟩) :=
    preservesLimitIso_hom_π (forget AddCommGrpCat X)
      (Discrete.functor (cechTermFactor F U n)) ⟨i⟩
  have hcombined :
      (preservesLimitIso (forget AddCommGrpCat X)
          (Discrete.functor (cechTermFactor F U n))).hom ≫
          ((HasLimit.isoOfNatIso (cechTermForgetDiagramIso F U n)).hom ≫
            limit.π (Discrete.functor fun i : Fin (n + 1) → ι =>
              (cechTermFactor F U n i).obj) ⟨i⟩) =
        (forget AddCommGrpCat X).map
          (limit.π (Discrete.functor (cechTermFactor F U n)) ⟨i⟩) := by
    rw [hnat]
    exact hpreserves
  change
    (preservesLimitIso (forget AddCommGrpCat X)
        (Discrete.functor (cechTermFactor F U n))).hom ≫
        ((HasLimit.isoOfNatIso (cechTermForgetDiagramIso F U n)).hom ≫
          limit.π (Discrete.functor fun i : Fin (n + 1) → ι =>
            (cechTermFactor F U n i).obj) ⟨i⟩) =
      (forget AddCommGrpCat X).map
        (limit.π (Discrete.functor (cechTermFactor F U n)) ⟨i⟩)
  exact hcombined

private noncomputable def cechTermForgetSectionsIso (V : Opens X) :
    (cechTerm F U n).obj.obj (op V) ≅
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)).obj
        (∏ᶜ fun i : Fin (n + 1) → ι => (cechTermFactor F U n i).obj) :=
  ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)).mapIso
    (cechTermForgetIso F U n)

private noncomputable def cechTermEvaluationDiagramIso (V : Opens X) :
    (Discrete.functor fun i : Fin (n + 1) → ι =>
        (cechTermFactor F U n i).obj) ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V) ≅
      Discrete.functor fun i : Fin (n + 1) → ι =>
        (cechTermFactor F U n i).obj.obj (op V) :=
  Discrete.natIso (fun _ => Iso.refl _)

private noncomputable def cechTermEvaluationIso (V : Opens X) :
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)).obj
        (∏ᶜ fun i : Fin (n + 1) → ι => (cechTermFactor F U n i).obj) ≅
      ∏ᶜ fun i : Fin (n + 1) → ι =>
        (cechTermFactor F U n i).obj.obj (op V) := by
  letI : HasLimit (Discrete.functor
      (fun i : Fin (n + 1) → ι => (cechTermFactor F U n i).obj) ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)) :=
    hasLimit_of_iso (cechTermEvaluationDiagramIso F U n V).symm
  exact preservesLimitIso ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V))
      (Discrete.functor fun i : Fin (n + 1) → ι => (cechTermFactor F U n i).obj) ≪≫
    HasLimit.isoOfNatIso (cechTermEvaluationDiagramIso F U n V)

private theorem cechTermEvaluationIso_hom_π (V : Opens X)
    (i : Fin (n + 1) → ι) :
    (cechTermEvaluationIso F U n V).hom ≫
        Pi.π (fun i : Fin (n + 1) → ι =>
          (cechTermFactor F U n i).obj.obj (op V)) i =
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)).map
        (Pi.π (fun i : Fin (n + 1) → ι =>
          (cechTermFactor F U n i).obj) i) := by
  change (cechTermEvaluationIso F U n V).hom ≫
      limit.π (Discrete.functor fun i : Fin (n + 1) → ι =>
        (cechTermFactor F U n i).obj.obj (op V)) ⟨i⟩ =
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)).map
        (limit.π (Discrete.functor fun i : Fin (n + 1) → ι =>
          (cechTermFactor F U n i).obj) ⟨i⟩)
  letI : HasLimit ((Discrete.functor fun i : Fin (n + 1) → ι =>
      (cechTermFactor F U n i).obj) ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)) := hasLimit_of_iso
    (cechTermEvaluationDiagramIso F U n V).symm
  have hnat :
      (HasLimit.isoOfNatIso (cechTermEvaluationDiagramIso F U n V)).hom ≫
          limit.π (Discrete.functor fun i : Fin (n + 1) → ι =>
            (cechTermFactor F U n i).obj.obj (op V)) ⟨i⟩ =
        limit.π ((Discrete.functor fun i : Fin (n + 1) → ι =>
          (cechTermFactor F U n i).obj) ⋙
            (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)) ⟨i⟩ := by
    calc
      _ = limit.π ((Discrete.functor fun i : Fin (n + 1) → ι =>
            (cechTermFactor F U n i).obj) ⋙
              (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)) ⟨i⟩ ≫
          (cechTermEvaluationDiagramIso F U n V).hom.app ⟨i⟩ :=
        HasLimit.isoOfNatIso_hom_π (cechTermEvaluationDiagramIso F U n V) ⟨i⟩
      _ = _ := Category.comp_id _
  have hpreserves :
      (preservesLimitIso
          ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V))
          (Discrete.functor fun i : Fin (n + 1) → ι =>
            (cechTermFactor F U n i).obj)).hom ≫
          limit.π ((Discrete.functor fun i : Fin (n + 1) → ι =>
            (cechTermFactor F U n i).obj) ⋙
              (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)) ⟨i⟩ =
        ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)).map
          (limit.π (Discrete.functor fun i : Fin (n + 1) → ι =>
            (cechTermFactor F U n i).obj) ⟨i⟩) :=
    preservesLimitIso_hom_π
      ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V))
      (Discrete.functor fun i : Fin (n + 1) → ι =>
        (cechTermFactor F U n i).obj) ⟨i⟩
  have hcombined :
      (preservesLimitIso
          ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V))
          (Discrete.functor fun i : Fin (n + 1) → ι =>
            (cechTermFactor F U n i).obj)).hom ≫
          ((HasLimit.isoOfNatIso (cechTermEvaluationDiagramIso F U n V)).hom ≫
            limit.π (Discrete.functor fun i : Fin (n + 1) → ι =>
              (cechTermFactor F U n i).obj.obj (op V)) ⟨i⟩) =
        ((evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)).map
          (limit.π (Discrete.functor fun i : Fin (n + 1) → ι =>
            (cechTermFactor F U n i).obj) ⟨i⟩) := by
    rw [hnat]
    exact hpreserves
  simpa only [cechTermEvaluationIso, Iso.trans_hom, Category.assoc] using hcombined

private noncomputable def cechTermSectionsRawIso (V : Opens X) :
    (cechTerm F U n).obj.obj (op V) ≅
      ∏ᶜ fun i : Fin (n + 1) → ι =>
        (cechTermFactor F U n i).obj.obj (op V) :=
  cechTermForgetSectionsIso F U n V ≪≫ cechTermEvaluationIso F U n V

@[reassoc]
private theorem cechTermSectionsRawIso_hom_π (V : Opens X)
    (i : Fin (n + 1) → ι) :
    (cechTermSectionsRawIso F U n V).hom ≫
        Pi.π (fun i : Fin (n + 1) → ι =>
          (cechTermFactor F U n i).obj.obj (op V)) i =
      (Pi.π (cechTermFactor F U n) i).hom.app (op V) := by
  rw [cechTermSectionsRawIso, Iso.trans_hom, Category.assoc,
    cechTermEvaluationIso_hom_π]
  exact congr_app (cechTermForgetIso_hom_π F U n i) (op V)

private noncomputable def cechTermSectionsProductIso (V : Opens X) :
    (cechTerm F U n).obj.obj (op V) ≅
      ∏ᶜ fun i : Fin (n + 1) → ι =>
        F.obj.obj (op (V ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i k))) :=
  cechTermSectionsRawIso F U n V ≪≫
    Pi.mapIso (cechTermFactorSectionsIso F U n V)

private theorem cechTermSectionsProductIso_hom_π (V : Opens X)
    (i : Fin (n + 1) → ι) :
    (cechTermSectionsProductIso F U n V).hom ≫
        Pi.π (fun i : Fin (n + 1) → ι =>
          F.obj.obj (op (V ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i k)))) i =
      (Pi.π (cechTermFactor F U n) i).hom.app (op V) ≫
        (cechTermFactorSectionsIso F U n V i).hom := by
  rw [cechTermSectionsProductIso, Iso.trans_hom, Category.assoc,
    Pi.mapIso_hom_π]
  exact congrArg (fun k ↦ k ≫ (cechTermFactorSectionsIso F U n V i).hom)
    (cechTermSectionsRawIso_hom_π F U n V i)

/-- Sections of a sheaf-level Cech term are families of sections on tuple intersections. -/
noncomputable def cechTermSectionsAddEquiv (V : Opens X) :
    (cechTerm F U n).obj.obj (op V) ≃+
      ∀ i : Fin (n + 1) → ι,
        F.obj.obj (op (V ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i k))) :=
  ((cechTermSectionsProductIso F U n V) ≪≫
    AddCommGrpCat.productIsoPi fun i : Fin (n + 1) → ι =>
      F.obj.obj (op (V ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i k)))).addCommGroupIsoToAddEquiv

/-- The component of `cechTermSectionsAddEquiv` at a tuple is restriction to the
corresponding intersection. -/
theorem cechTermSectionsAddEquiv_apply (V : Opens X)
    (x : (cechTerm F U n).obj.obj (op V)) (i : Fin (n + 1) → ι) :
    cechTermSectionsAddEquiv F U n V x i =
      ((eqToIso (by
          rw [toRestrict_obj_obj_obj, Opens.functor_map_eq_inf])) :
        (cechTermFactor F U n i).obj.obj (op V) ≅
          F.obj.obj (op (V ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i k)))).hom
        ((Pi.π (cechTermFactor F U n) i).hom.app (op V) x) := by
  rw [show cechTermSectionsAddEquiv F U n V x i =
    (AddCommGrpCat.productIsoPi (fun i : Fin (n + 1) → ι =>
      F.obj.obj (op (V ⊓ ∏ᶜ fun k : Fin (n + 1) => U (i k))))).hom
        ((cechTermSectionsProductIso F U n V).hom x) i from rfl,
    AddCommGrpCat.productIsoPi_hom_apply]
  exact ConcreteCategory.congr_hom (cechTermSectionsProductIso_hom_π F U n V i) x

end TopCat.Sheaf

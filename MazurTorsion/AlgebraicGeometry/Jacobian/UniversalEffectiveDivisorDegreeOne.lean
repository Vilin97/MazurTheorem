/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.SymmetricPower
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# The universal effective divisor in degree one

The first symmetric power of a challenge curve is canonically the curve.
Consequently its universal degree-one divisor is the graph of the inverse
identification `C ≅ Sym¹(C)`.  This file packages the graph and proves that
its projection to `Sym¹(C)` is finite flat of constant rank one.

This is the base case for the higher-degree local root-chart construction;
the named downstream consumer is the Abel map in `PicardRepresentability`.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.UniversalEffectiveDivisorDegreeOne

variable (K : Type u) [Field K]
variable (C : Over (Spec (.of K)))
variable [GeometricallyIrreducible C.hom] [IsProper C.hom]
variable [SmoothOfRelativeDimension 1 C.hom]

/-- The degree-one universal divisor as a graph over the ground field. -/
noncomputable def overHom :
    C ⟶ C ⨯ SymmetricPower.curveSchemeSucc K C 0 :=
  Limits.prod.lift (𝟙 C) (SymmetricPower.curveSchemeSuccZeroIso K C).inv

/-- The underlying graph morphism into `C × Sym¹(C)`. -/
noncomputable def ι : C.left ⟶
    (C ⨯ SymmetricPower.curveSchemeSucc K C 0).left :=
  (overHom K C).left

/-- Projection of the degree-one universal divisor to its parameter space. -/
noncomputable def projection :
    C.left ⟶ (SymmetricPower.curveSchemeSucc K C 0).left :=
  ι K C ≫
    (Limits.prod.snd :
      C ⨯ SymmetricPower.curveSchemeSucc K C 0 ⟶
        SymmetricPower.curveSchemeSucc K C 0).left

@[reassoc]
theorem ι_comp_fst :
    ι K C ≫
        (Limits.prod.fst :
          C ⨯ SymmetricPower.curveSchemeSucc K C 0 ⟶ C).left =
      𝟙 C.left := by
  exact congrArg Over.Hom.left
    (Limits.prod.lift_fst (𝟙 C)
      (SymmetricPower.curveSchemeSuccZeroIso K C).inv)

@[reassoc]
theorem projection_eq :
    projection K C =
      (SymmetricPower.curveSchemeSuccZeroIso K C).inv.left := by
  exact congrArg Over.Hom.left
    (Limits.prod.lift_snd (𝟙 C)
      (SymmetricPower.curveSchemeSuccZeroIso K C).inv)

instance projection_isIso : IsIso (projection K C) := by
  rw [projection_eq]
  exact inferInstanceAs (IsIso ((Over.forget _).map
    (SymmetricPower.curveSchemeSuccZeroIso K C).inv))

instance projection_isFinite : IsFinite (projection K C) := by
  infer_instance

instance projection_flat : Flat (projection K C) := by
  infer_instance

/-- The degree-one family has constant rank one. -/
theorem projection_finrank :
    (projection K C).finrank = fun _ ↦ 1 := by
  change (projection K C).finrank = 1
  exact Scheme.Hom.finrank_eq_one_of_isIso (projection K C)

/-- The degree-one universal divisor is a closed graph in
`C × Sym¹(C)`. -/
instance ι_isClosedImmersion : IsClosedImmersion (ι K C) := by
  let Y := SymmetricPower.curveSchemeSucc K C 0
  let e := SymmetricPower.curveSchemeSuccZeroIso K C
  letI : IsSeparated Y.hom := by
    dsimp only [Y]
    infer_instance
  let pbIso : pullback C.hom Y.hom ≅
      pullback (e.inv.left ≫ Y.hom) Y.hom :=
    pullback.congrHom e.inv.w.symm rfl
  let ambientIso : (C ⨯ Y).left ≅
      pullback (e.inv.left ≫ Y.hom) Y.hom :=
    Over.prodLeftIsoPullback C Y ≪≫ pbIso
  let graph : C.left ⟶ pullback (e.inv.left ≫ Y.hom) Y.hom :=
    pullback.lift (𝟙 C.left) e.inv.left
      (Category.id_comp (e.inv.left ≫ Y.hom))
  have hgraph : ι K C ≫ ambientIso.hom = graph := by
    apply pullback.hom_ext
    · dsimp only [ambientIso, pbIso]
      simp only [Iso.trans_hom, Category.assoc, pullback.congrHom_hom]
      dsimp only [pullback.map]
      erw [pullback.lift_fst, Category.comp_id,
        Over.prodLeftIsoPullback_hom_fst]
      rw [ι_comp_fst]
      simp only [graph, pullback.lift_fst]
    · dsimp only [ambientIso, pbIso]
      simp only [Iso.trans_hom, Category.assoc, pullback.congrHom_hom]
      dsimp only [pullback.map]
      erw [pullback.lift_snd, Category.comp_id,
        Over.prodLeftIsoPullback_hom_snd]
      change projection K C =
        graph ≫ pullback.snd (e.inv.left ≫ Y.hom) Y.hom
      rw [projection_eq]
      simp only [graph, pullback.lift_snd]
      dsimp only [e]
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _
    ambientIso.hom]
  rw [hgraph]
  infer_instance

end MazurTorsion.AlgebraicGeometry.Jacobian.UniversalEffectiveDivisorDegreeOne

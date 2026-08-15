/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentBaseChange

/-!
# Pasting coherence for pullback comparisons

These solved forms of pseudofunctorial pullback associativity and
congruence are the small algebraic steps used when pasting commutative
squares of scheme morphisms.
-/


open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.CoverDescentData

/-- Ungroup an outer pullback and then regroup the inner pullback. -/
@[reassoc]
lemma pullbackComp_inv_app_comp_map_pullbackComp_hom_app
    {X Y Z Q : Scheme.{0}}
    (p : X ⟶ Y) (q : Y ⟶ Z) (r : Z ⟶ Q)
    (M : Q.Modules) :
    (pullbackComp p q).inv.app ((pullback r).obj M) ≫
        (pullback p).map
          ((pullbackComp q r).hom.app M) =
      (pullbackComp (p ≫ q) r).hom.app M ≫
        (pullbackCongr
          (Category.assoc p q r).symm).inv.app M ≫
        (pullbackComp p (q ≫ r)).inv.app M := by
  rw [pullbackComp_comp_fst_hom_app]
  simp

/-- Regroup two hom-side pullback-composition comparisons. -/
@[reassoc]
lemma pullback_map_pullbackComp_hom_app_comp_pullbackComp_hom_app
    {X Y Z Q : Scheme.{0}}
    (p : X ⟶ Y) (q : Y ⟶ Z) (r : Z ⟶ Q)
    (M : Q.Modules) :
    (pullback p).map
          ((pullbackComp q r).hom.app M) ≫
        (pullbackComp p (q ≫ r)).hom.app M =
      (pullbackComp p q).hom.app ((pullback r).obj M) ≫
        (pullbackComp (p ≫ q) r).hom.app M ≫
        (pullbackCongr
          (Category.assoc p q r).symm).inv.app M := by
  rw [pullbackComp_comp_fst_hom_app]
  simp

/-- Congruence compatibility for inverse regrouping, hom side. -/
@[reassoc]
lemma pullbackComp_inv_app_comp_map_pullbackCongr_hom_app
    {X Y Z : Scheme.{0}} (p : X ⟶ Y)
    {q r : Y ⟶ Z} (h : q = r) (M : Z.Modules) :
    (pullbackComp p q).inv.app M ≫
        (pullback p).map
          ((pullbackCongr h).hom.app M) =
      (pullbackCongr
        (show p ≫ q = p ≫ r by rw [h])).hom.app M ≫
        (pullbackComp p r).inv.app M := by
  subst r
  simp [pullbackCongr]

/-- Move a congruence comparison across the hom side of a pullback
composition comparison. -/
@[reassoc]
lemma pullbackCongr_hom_app_comp_pullbackComp_hom_app
    {X Y Z : Scheme.{0}} {p q : X ⟶ Y}
    (h : p = q) (r : Y ⟶ Z) (M : Z.Modules) :
    (pullbackCongr h).hom.app ((pullback r).obj M) ≫
        (pullbackComp q r).hom.app M =
      (pullbackComp p r).hom.app M ≫
        (pullbackCongr
          (show p ≫ r = q ≫ r by rw [h])).hom.app M := by
  subst q
  simp [pullbackCongr]

/-- Move the inverse congruence comparison across the inverse side of a
pullback-composition comparison. -/
@[reassoc]
lemma pullbackComp_inv_app_comp_pullbackCongr_inv_app
    {X Y Z : Scheme.{0}} {p q : X ⟶ Y}
    (h : p = q) (r : Y ⟶ Z) (M : Z.Modules) :
    (pullbackComp q r).inv.app M ≫
        (pullbackCongr h).inv.app ((pullback r).obj M) =
      (pullbackCongr
        (show p ≫ r = q ≫ r by rw [h])).inv.app M ≫
        (pullbackComp p r).inv.app M := by
  subst q
  simp [pullbackCongr]

/-- A canonical comparison between two equal first legs remains the
canonical comparison after both legs are postcomposed. -/
lemma pullbackComp_inv_trans_congr_trans_pullbackComp
    {X Y Z : Scheme.{0}} {p q : X ⟶ Y}
    (h : p = q) (r : Y ⟶ Z) (M : Z.Modules) :
    (pullbackComp p r).symm.app M ≪≫
        (pullbackCongr h).app
          ((pullback r).obj M) ≪≫
        (pullbackComp q r).app M =
      (pullbackCongr
        (show p ≫ r = q ≫ r by rw [h])).app M := by
  subst q
  apply Iso.ext
  change
    (pullbackComp p r).inv.app M ≫
          𝟙 _ ≫
        (pullbackComp p r).hom.app M =
      𝟙 _
  simp

/-- Hom-side form of
`pullbackComp_inv_trans_congr_trans_pullbackComp`. -/
@[reassoc]
lemma pullbackComp_inv_hom_comp_congr_hom_comp_pullbackComp_hom
    {X Y Z : Scheme.{0}} {p q : X ⟶ Y}
    (h : p = q) (r : Y ⟶ Z) (M : Z.Modules) :
    (pullbackComp p r).inv.app M ≫
        (pullbackCongr h).hom.app
          ((pullback r).obj M) ≫
        (pullbackComp q r).hom.app M =
      (pullbackCongr
        (show p ≫ r = q ≫ r by rw [h])).hom.app M :=
  congrArg Iso.hom
    (pullbackComp_inv_trans_congr_trans_pullbackComp
      h r M)

/-- Pasting a transition between two pullback squares gives the direct
threefold-pullback comparison.  The equality `houter` is allowed as an
explicit argument so callers can retain the geometrically meaningful
proof of commutativity; proof irrelevance identifies it with the pasted
one used internally. -/
lemma pullbackSquareIso_paste_transition_hom
    {X Y Y' Z Z' P Q : Scheme.{0}}
    (q : X ⟶ Y) (a : Y ⟶ Z)
    (q' : X ⟶ Y') (a' : Y' ⟶ Z')
    (p : X ⟶ P) (r : P ⟶ Z) (r' : P ⟶ Z')
    (u : Z ⟶ Q) (u' : Z' ⟶ Q)
    (hsource : q ≫ a = p ≫ r)
    (htarget : q' ≫ a' = p ≫ r')
    (hmiddle : r ≫ u = r' ≫ u')
    (houter : (q ≫ a) ≫ u = (q' ≫ a') ≫ u')
    (M : Q.Modules) :
    (pullbackSquareIso q a p r hsource
          ((pullback u).obj M) ≪≫
        (pullback p).mapIso
          ((pullbackComp r u).app M ≪≫
            (pullbackCongr hmiddle).app M ≪≫
            (pullbackComp r' u').symm.app M) ≪≫
        (pullbackSquareIso q' a' p r' htarget
          ((pullback u').obj M)).symm).hom =
      ((pullbackComp q a).app ((pullback u).obj M) ≪≫
        (pullbackComp (q ≫ a) u).app M ≪≫
        (pullbackCongr houter).app M ≪≫
        (pullbackComp (q' ≫ a') u').symm.app M ≪≫
        (pullbackComp q' a').symm.app
          ((pullback u').obj M)).hom := by
  simp [pullbackSquareIso]
  simp only [
    pullbackComp_inv_app_comp_map_pullbackComp_hom_app_assoc,
    pullback_map_inv_comp_hom_app_assoc,
    pullbackComp_inv_app_comp_map_pullbackCongr_hom_app_assoc,
    pullbackCongr_hom_app_comp_pullbackComp_hom_app_assoc,
    pullbackComp_inv_app_comp_pullbackCongr_inv_app_assoc,
    Iso.inv_hom_id_app_assoc]
  simp only [
    pullbackCongr_hom_app_eqToHom,
    pullbackCongr_inv_app_eqToHom,
    eqToHom_trans_assoc]

/-- Transporting a canonical transition through pullback-square chart
comparisons gives the same direct threefold-pullback comparison. -/
lemma pullbackSquareIso_transport_transition_hom
    {X Y Y' Z Z' P Q : Scheme.{0}}
    (q : X ⟶ Y) (d : Y ⟶ P) (a : Y ⟶ Z)
    (q' : X ⟶ Y') (d' : Y' ⟶ P) (a' : Y' ⟶ Z')
    (g : P ⟶ Q) (u : Z ⟶ Q) (u' : Z' ⟶ Q)
    (hleft : d ≫ g = a ≫ u)
    (hright : d' ≫ g = a' ≫ u')
    (hmiddle : q ≫ d = q' ≫ d')
    (houter : (q ≫ a) ≫ u = (q' ≫ a') ≫ u')
    (M : Q.Modules) :
    ((pullback q).mapIso
          (pullbackSquareIso d g a u hleft M).symm ≪≫
        ((pullbackComp q d).app ((pullback g).obj M) ≪≫
          (pullbackCongr hmiddle).app ((pullback g).obj M) ≪≫
          (pullbackComp q' d').symm.app
            ((pullback g).obj M)) ≪≫
        (pullback q').mapIso
          (pullbackSquareIso d' g a' u' hright M)).hom =
      ((pullbackComp q a).app ((pullback u).obj M) ≪≫
        (pullbackComp (q ≫ a) u).app M ≪≫
        (pullbackCongr houter).app M ≪≫
        (pullbackComp (q' ≫ a') u').symm.app M ≪≫
        (pullbackComp q' a').symm.app
          ((pullback u').obj M)).hom := by
  simp [pullbackSquareIso]
  simp only [
    pullbackComp_inv_app_comp_map_pullbackComp_hom_app_assoc,
    pullback_map_inv_comp_hom_app_assoc,
    pullback_map_congr_inv_comp_hom_app_assoc,
    pullback_map_pullbackComp_hom_app_comp_pullbackComp_hom_app_assoc,
    pullbackComp_inv_app_comp_map_pullbackCongr_hom_app_assoc,
    pullbackComp_inv_comp_map_inv_app,
    pullbackComp_inv_hom_comp_congr_hom_comp_pullbackComp_hom_assoc]
  simp only [
    pullbackCongr_hom_app_eqToHom,
    pullbackCongr_inv_app_eqToHom,
    eqToHom_trans_assoc]

end AlgebraicGeometry.Scheme.Modules.CoverDescentData

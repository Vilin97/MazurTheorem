/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleDescentEffectiveBridge

/-!
# Morphisms between descended module sheaves

Effective descent for module sheaves is useful functorially only after
compatible chartwise morphisms can be glued.  This file supplies that small
interface and records how the resulting global morphism restricts to each
chart.
-/

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable (D : Scheme.GlueData.{0})
  (M N : ∀ i, (D.U i).Modules)
  (g : ∀ i j,
    (pullback (D.f i j)).obj (M i) ≅
      (pullback (D.t i j ≫ D.f j i)).obj (M j))
  (h : ∀ i j,
    (pullback (D.f i j)).obj (N i) ≅
      (pullback (D.t i j ≫ D.f j i)).obj (N j))
  (gIdentity : ∀ i, g i i =
    eqToIso (congrArg
      (fun f => (pullback f).obj (M i))
      (show D.f i i = D.t i i ≫ D.f i i by
        rw [D.t_id i, Category.id_comp])))
  (hIdentity : ∀ i, h i i =
    eqToIso (congrArg
      (fun f => (pullback f).obj (N i))
      (show D.f i i = D.t i i ≫ D.f i i by
        rw [D.t_id i, Category.id_comp])))
  (gCocycle : ∀ i j k,
    pullbackBaseChangeTransport
        (pullback.fst (D.f i j) (D.f i k))
        (D.f i j) (D.t i j ≫ D.f j i) (g i j) ≪≫
      (pullbackCongr
        (glueData_bridge_mid D i j k)).app (M j) ≪≫
      pullbackBaseChangeTransport
        (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
        (D.f j k) (D.t j k ≫ D.f k j) (g j k) ≪≫
      (pullbackCongr
        (glueData_bridge_tgt D i j k)).app (M k) =
    (pullbackCongr
      (glueData_bridge_src D i j k)).app (M i) ≪≫
      pullbackBaseChangeTransport
        (pullback.snd (D.f i j) (D.f i k))
        (D.f i k) (D.t i k ≫ D.f k i) (g i k))
  (hCocycle : ∀ i j k,
    pullbackBaseChangeTransport
        (pullback.fst (D.f i j) (D.f i k))
        (D.f i j) (D.t i j ≫ D.f j i) (h i j) ≪≫
      (pullbackCongr
        (glueData_bridge_mid D i j k)).app (N j) ≪≫
      pullbackBaseChangeTransport
        (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
        (D.f j k) (D.t j k ≫ D.f k j) (h j k) ≪≫
      (pullbackCongr
        (glueData_bridge_tgt D i j k)).app (N k) =
    (pullbackCongr
      (glueData_bridge_src D i j k)).app (N i) ≪≫
      pullbackBaseChangeTransport
        (pullback.snd (D.f i j) (D.f i k))
        (D.f i k) (D.t i k ≫ D.f k i) (h i k))

/-- A family of chartwise maps is compatible with two descent data when it
commutes with every transition isomorphism. -/
def DescentMorphismCompatible (φ : ∀ i, M i ⟶ N i) : Prop :=
  ∀ i j,
    (pullback (D.f i j)).map (φ i) ≫ (h i j).hom =
      (g i j).hom ≫
        (pullback (D.t i j ≫ D.f j i)).map (φ j)

/-- Identity maps are compatible with every descent datum. -/
lemma descentMorphismCompatible_id :
    DescentMorphismCompatible D M M g g (fun i => 𝟙 (M i)) := by
  intro i j
  simp

/-- Pointwise composites of compatible chart maps are compatible. -/
lemma DescentMorphismCompatible.comp
    {P : ∀ i, (D.U i).Modules}
    {k : ∀ i j,
      (pullback (D.f i j)).obj (P i) ≅
        (pullback (D.t i j ≫ D.f j i)).obj (P j)}
    {φ : ∀ i, M i ⟶ N i} {ψ : ∀ i, N i ⟶ P i}
    (hφ : DescentMorphismCompatible D M N g h φ)
    (hψ : DescentMorphismCompatible D N P h k ψ) :
    DescentMorphismCompatible D M P g k
      (fun i => φ i ≫ ψ i) := by
  intro i j
  simp only [Functor.map_comp, Category.assoc]
  rw [hψ i j]
  rw [← Category.assoc, hφ i j]
  simp only [Category.assoc]

namespace DescentMorphism

variable (φ : ∀ i, M i ⟶ N i)
  (hφ : DescentMorphismCompatible D M N g h φ)

include hφ in
private lemma compatible_inv (i j : D.J) :
    (g i j).inv ≫ (pullback (D.f i j)).map (φ i) =
      (pullback (D.t i j ≫ D.f j i)).map (φ j) ≫
        (h i j).inv := by
  apply (cancel_mono (h i j).hom).1
  simp only [Category.assoc]
  rw [hφ i j]
  simp

include hφ
/-- The global morphism obtained from a compatible family of morphisms
between two module descent data. -/
noncomputable def glueMap :
    glue D M g gIdentity gCocycle ⟶
      glue D N h hIdentity hCocycle :=
  glueLift D N h hIdentity hCocycle
    (fun i =>
      (pullbackPushforwardAdjunction (D.ι i)).homEquiv _ _
        (glueRestrictionHom D M g gIdentity gCocycle i ≫ φ i))
    (by
      intro p
      apply (glueLift_cond_iff D N h
        (fun i =>
          glueRestrictionHom D M g gIdentity gCocycle i ≫ φ i)
        p.1 p.2).2
      calc
        (pullbackComp (D.f p.1 p.2) (D.ι p.1)).inv.app
              (glue D M g gIdentity gCocycle) ≫
            (pullback (D.f p.1 p.2)).map
              (glueRestrictionHom D M g gIdentity gCocycle p.1 ≫
                φ p.1) =
            ((pullbackComp (D.f p.1 p.2) (D.ι p.1)).inv.app
                (glue D M g gIdentity gCocycle) ≫
              (pullback (D.f p.1 p.2)).map
                (glueRestrictionHom D M g gIdentity gCocycle p.1)) ≫
              (pullback (D.f p.1 p.2)).map (φ p.1) := by
                rw [Functor.map_comp]
                exact (Category.assoc _ _ _).symm
        _ =
            ((pullbackCongr
                (show
                  (D.t p.1 p.2 ≫ D.f p.2 p.1) ≫ D.ι p.2 =
                    D.f p.1 p.2 ≫ D.ι p.1 by
                  rw [Category.assoc]
                  exact D.glue_condition p.1 p.2)).inv.app
                  (glue D M g gIdentity gCocycle) ≫
              (pullbackComp
                (D.t p.1 p.2 ≫ D.f p.2 p.1)
                (D.ι p.2)).inv.app
                  (glue D M g gIdentity gCocycle) ≫
              (pullback
                (D.t p.1 p.2 ≫ D.f p.2 p.1)).map
                  (glueRestrictionHom
                    D M g gIdentity gCocycle p.2) ≫
              (g p.1 p.2).inv) ≫
                (pullback (D.f p.1 p.2)).map (φ p.1) :=
          eq_whisker
            (glueRestriction_overlap_compat
              D M g gIdentity gCocycle p.1 p.2) _
        _ =
            (pullbackCongr
                (show
                  (D.t p.1 p.2 ≫ D.f p.2 p.1) ≫ D.ι p.2 =
                    D.f p.1 p.2 ≫ D.ι p.1 by
                  rw [Category.assoc]
                  exact D.glue_condition p.1 p.2)).inv.app
                  (glue D M g gIdentity gCocycle) ≫
              (pullbackComp
                (D.t p.1 p.2 ≫ D.f p.2 p.1)
                (D.ι p.2)).inv.app
                  (glue D M g gIdentity gCocycle) ≫
              (pullback
                (D.t p.1 p.2 ≫ D.f p.2 p.1)).map
                  (glueRestrictionHom
                    D M g gIdentity gCocycle p.2) ≫
              (pullback
                (D.t p.1 p.2 ≫ D.f p.2 p.1)).map (φ p.2) ≫
              (h p.1 p.2).inv := by
          simp only [Category.assoc]
          rw [compatible_inv D M N g h φ hφ]
        _ =
            (pullbackCongr
                (show
                  (D.t p.1 p.2 ≫ D.f p.2 p.1) ≫ D.ι p.2 =
                    D.f p.1 p.2 ≫ D.ι p.1 by
                  rw [Category.assoc]
                  exact D.glue_condition p.1 p.2)).inv.app
                  (glue D M g gIdentity gCocycle) ≫
              (pullbackComp
                (D.t p.1 p.2 ≫ D.f p.2 p.1)
                (D.ι p.2)).inv.app
                  (glue D M g gIdentity gCocycle) ≫
              (pullback
                (D.t p.1 p.2 ≫ D.f p.2 p.1)).map
                  (glueRestrictionHom D M g gIdentity gCocycle p.2 ≫
                    φ p.2) ≫
              (h p.1 p.2).inv := by
          rw [Functor.map_comp]
          exact whisker_eq _ (whisker_eq _
            (Category.assoc _ _ _).symm))

/-- On each chart, `glueMap` is the prescribed chartwise map, after the
effective-descent restriction isomorphisms. -/
lemma pullback_map_glueMap (i : D.J) :
    (pullback (D.ι i)).map
        (glueMap D M N g h gIdentity hIdentity
          gCocycle hCocycle φ hφ) ≫
      glueRestrictionHom D N h hIdentity hCocycle i =
    glueRestrictionHom D M g gIdentity gCocycle i ≫ φ i := by
  unfold glueMap
  rw [pullback_map_glueLift_glueRestrictionHom]
  exact Equiv.apply_symm_apply _ _

omit hφ
/-- Gluing the identity family gives the identity global morphism. -/
theorem glueMap_id
    (hId : DescentMorphismCompatible D M M g g
      (fun i => 𝟙 (M i))) :
    glueMap D M M g g gIdentity gIdentity
        gCocycle gCocycle (fun i => 𝟙 (M i)) hId =
      𝟙 (glue D M g gIdentity gCocycle) := by
  apply pullback_map_jointly_faithful D
  intro i
  letI := isIso_glueRestrictionHom
    D M g gIdentity gCocycle i
  apply (cancel_mono
    (glueRestrictionHom D M g gIdentity gCocycle i)).1
  rw [pullback_map_glueMap]
  simp

variable {P : ∀ i, (D.U i).Modules}
  (k : ∀ i j,
    (pullback (D.f i j)).obj (P i) ≅
      (pullback (D.t i j ≫ D.f j i)).obj (P j))
  (kIdentity : ∀ i, k i i =
    eqToIso (congrArg
      (fun f => (pullback f).obj (P i))
      (show D.f i i = D.t i i ≫ D.f i i by
        rw [D.t_id i, Category.id_comp])))
  (kCocycle : ∀ i j q,
    pullbackBaseChangeTransport
        (pullback.fst (D.f i j) (D.f i q))
        (D.f i j) (D.t i j ≫ D.f j i) (k i j) ≪≫
      (pullbackCongr
        (glueData_bridge_mid D i j q)).app (P j) ≪≫
      pullbackBaseChangeTransport
        (D.t' i j q ≫ pullback.fst (D.f j q) (D.f j i))
        (D.f j q) (D.t j q ≫ D.f q j) (k j q) ≪≫
      (pullbackCongr
        (glueData_bridge_tgt D i j q)).app (P q) =
    (pullbackCongr
      (glueData_bridge_src D i j q)).app (P i) ≪≫
      pullbackBaseChangeTransport
        (pullback.snd (D.f i j) (D.f i q))
        (D.f i q) (D.t i q ≫ D.f q i) (k i q))
  (ψ : ∀ i, N i ⟶ P i)
  (hψ : DescentMorphismCompatible D N P h k ψ)

include hφ hψ
/-- Gluing commutes with pointwise composition of compatible chart maps. -/
theorem glueMap_comp :
    glueMap D M N g h gIdentity hIdentity
        gCocycle hCocycle φ hφ ≫
      glueMap D N P h k hIdentity kIdentity
        hCocycle kCocycle ψ hψ =
    glueMap D M P g k gIdentity kIdentity
      gCocycle kCocycle (fun i => φ i ≫ ψ i)
      (DescentMorphismCompatible.comp D M N g h hφ hψ) := by
  apply pullback_map_jointly_faithful D
  intro i
  letI := isIso_glueRestrictionHom
    D P k kIdentity kCocycle i
  apply (cancel_mono
    (glueRestrictionHom D P k kIdentity kCocycle i)).1
  calc
    (pullback (D.ι i)).map
          (glueMap D M N g h gIdentity hIdentity
              gCocycle hCocycle φ hφ ≫
            glueMap D N P h k hIdentity kIdentity
              hCocycle kCocycle ψ hψ) ≫
        glueRestrictionHom D P k kIdentity kCocycle i =
      (pullback (D.ι i)).map
          (glueMap D M N g h gIdentity hIdentity
            gCocycle hCocycle φ hφ) ≫
        ((pullback (D.ι i)).map
            (glueMap D N P h k hIdentity kIdentity
              hCocycle kCocycle ψ hψ) ≫
          glueRestrictionHom D P k kIdentity kCocycle i) :=
      (eq_whisker ((pullback (D.ι i)).map_comp _ _) _).trans
        (Category.assoc _ _ _)
    _ = (pullback (D.ι i)).map
          (glueMap D M N g h gIdentity hIdentity
            gCocycle hCocycle φ hφ) ≫
        (glueRestrictionHom D N h hIdentity hCocycle i ≫ ψ i) :=
      whisker_eq _
        (pullback_map_glueMap D N P h k hIdentity kIdentity
          hCocycle kCocycle ψ hψ i)
    _ = ((pullback (D.ι i)).map
          (glueMap D M N g h gIdentity hIdentity
            gCocycle hCocycle φ hφ) ≫
        glueRestrictionHom D N h hIdentity hCocycle i) ≫ ψ i :=
      (Category.assoc _ _ _).symm
    _ = (glueRestrictionHom D M g gIdentity gCocycle i ≫ φ i) ≫
        ψ i :=
      eq_whisker
        (pullback_map_glueMap D M N g h gIdentity hIdentity
          gCocycle hCocycle φ hφ i) _
    _ = glueRestrictionHom D M g gIdentity gCocycle i ≫
        (φ i ≫ ψ i) :=
      Category.assoc _ _ _
    _ = (pullback (D.ι i)).map
          (glueMap D M P g k gIdentity kIdentity
            gCocycle kCocycle (fun q => φ q ≫ ψ q)
              (DescentMorphismCompatible.comp D M N g h hφ hψ)) ≫
        glueRestrictionHom D P k kIdentity kCocycle i :=
      (pullback_map_glueMap D M P g k gIdentity kIdentity
        gCocycle kCocycle (fun q => φ q ≫ ψ q)
          (DescentMorphismCompatible.comp D M N g h hφ hψ) i).symm

end DescentMorphism

end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleDescentObject

/-!
# The explicit equalizer presentation of a descended module

This file re-exposes the products and the two maps occurring in
`ModuleDescent.glueObject`.  Keeping these names out of the construction file
makes it possible to use the equalizer API without unfolding the object in
downstream section calculations.
-/

open CategoryTheory Limits

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ModuleDescent

open _root_.AlgebraicGeometry

variable (D : Scheme.GlueData.{0})
  (M : ∀ i, (D.U i).Modules)

/-- Product of the chartwise direct images. -/
def chartProduct : D.glued.Modules :=
  ∏ᶜ fun i => (Scheme.Modules.pushforward (D.ι i)).obj (M i)

/-- Product of the direct images from all pairwise overlaps. -/
def overlapProduct : D.glued.Modules :=
  ∏ᶜ fun p : D.J × D.J =>
    (Scheme.Modules.pushforward
      (D.f p.1 p.2 ≫ D.ι p.1)).obj
        ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1))

/-- Projection from the named overlap product to one pairwise factor. -/
private def overlapProjection (p : D.J × D.J) :
    overlapProduct D M ⟶
      (Scheme.Modules.pushforward
        (D.f p.1 p.2 ≫ D.ι p.1)).obj
          ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1)) := by
  unfold overlapProduct
  exact Pi.π _ p

/-- Restrict the first chart of a pair to its overlap. -/
def firstComponent (p : D.J × D.J) :
    (Scheme.Modules.pushforward (D.ι p.1)).obj (M p.1) ⟶
      (Scheme.Modules.pushforward
        (D.f p.1 p.2 ≫ D.ι p.1)).obj
          ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1)) :=
  (Scheme.Modules.pushforward (D.ι p.1)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction
        (D.f p.1 p.2)).unit.app (M p.1)) ≫
    (Scheme.Modules.pushforwardComp
      (D.f p.1 p.2) (D.ι p.1)).hom.app
        ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1))

/-- Restrict the second chart, apply the inverse transition, and reindex its
direct image using the gluing equality. -/
def secondComponent
    (e : ∀ i j,
      (Scheme.Modules.pullback (D.f i j)).obj (M i) ≅
        (Scheme.Modules.pullback
          (D.t i j ≫ D.f j i)).obj (M j))
    (p : D.J × D.J) :
    (Scheme.Modules.pushforward (D.ι p.2)).obj (M p.2) ⟶
      (Scheme.Modules.pushforward
        (D.f p.1 p.2 ≫ D.ι p.1)).obj
          ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1)) :=
  (Scheme.Modules.pushforward (D.ι p.2)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction
        (D.t p.1 p.2 ≫ D.f p.2 p.1)).unit.app (M p.2)) ≫
    (Scheme.Modules.pushforwardComp
      (D.t p.1 p.2 ≫ D.f p.2 p.1) (D.ι p.2)).hom.app
        ((Scheme.Modules.pullback
          (D.t p.1 p.2 ≫ D.f p.2 p.1)).obj (M p.2)) ≫
    (Scheme.Modules.pushforward
      ((D.t p.1 p.2 ≫ D.f p.2 p.1) ≫ D.ι p.2)).map
        (e p.1 p.2).inv ≫
    (Scheme.Modules.pushforwardCongr
      (show
        (D.t p.1 p.2 ≫ D.f p.2 p.1) ≫ D.ι p.2 =
          D.f p.1 p.2 ≫ D.ι p.1 by
        rw [Category.assoc]
        exact D.glue_condition p.1 p.2)).hom.app
          ((Scheme.Modules.pullback
            (D.f p.1 p.2)).obj (M p.1))

/-- First map of the descent equalizer. -/
def firstLeg : chartProduct D M ⟶ overlapProduct D M :=
  Pi.lift fun p =>
    Pi.π _ p.1 ≫ firstComponent D M p

/-- Second map of the descent equalizer. -/
def secondLeg
    (e : ∀ i j,
      (Scheme.Modules.pullback (D.f i j)).obj (M i) ≅
        (Scheme.Modules.pullback
          (D.t i j ≫ D.f j i)).obj (M j)) :
    chartProduct D M ⟶ overlapProduct D M :=
  Pi.lift fun p =>
    Pi.π _ p.2 ≫ secondComponent D M e p

variable
  (e : ∀ i j,
    (Scheme.Modules.pullback (D.f i j)).obj (M i) ≅
      (Scheme.Modules.pullback
        (D.t i j ≫ D.f j i)).obj (M j))
  (hIdentity : ∀ i, e i i =
    eqToIso (congrArg
      (fun f => (Scheme.Modules.pullback f).obj (M i))
      (show D.f i i = D.t i i ≫ D.f i i by
        rw [D.t_id i, Category.id_comp])))
  (hCocycle : ∀ i j k,
    pullbackTransport
        (pullback.fst (D.f i j) (D.f i k))
        (D.f i j) (D.t i j ≫ D.f j i) (e i j) ≪≫
      (Scheme.Modules.pullbackCongr
        (bridgeMiddle D i j k)).app (M j) ≪≫
      pullbackTransport
        (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
        (D.f j k) (D.t j k ≫ D.f k j) (e j k) ≪≫
      (Scheme.Modules.pullbackCongr
        (bridgeTarget D i j k)).app (M k) =
    (Scheme.Modules.pullbackCongr
      (bridgeSource D i j k)).app (M i) ≪≫
      pullbackTransport
        (pullback.snd (D.f i j) (D.f i k))
        (D.f i k) (D.t i k ≫ D.f k i) (e i k))

/-- `glueObject` is definitionally the displayed equalizer. -/
def glueIsoEqualizer :
    glueObject D M e hIdentity hCocycle ≅
      equalizer (firstLeg D M) (secondLeg D M e) :=
  Iso.refl _

/-- Projection of the descended object to one chartwise direct-image
factor. -/
def projection (i : D.J) :
    glueObject D M e hIdentity hCocycle ⟶
      (Scheme.Modules.pushforward (D.ι i)).obj (M i) :=
  (glueIsoEqualizer D M e hIdentity hCocycle).hom ≫
    equalizer.ι (firstLeg D M) (secondLeg D M e) ≫
    Pi.π _ i

@[reassoc]
lemma firstLeg_projection (p : D.J × D.J) :
    firstLeg D M ≫
        overlapProjection D M p =
      Pi.π (fun i =>
        (Scheme.Modules.pushforward (D.ι i)).obj (M i)) p.1 ≫
        firstComponent D M p :=
  Limits.Pi.lift_π _ _

@[reassoc]
lemma secondLeg_projection (p : D.J × D.J) :
    secondLeg D M e ≫
        overlapProjection D M p =
      Pi.π (fun i =>
        (Scheme.Modules.pushforward (D.ι i)).obj (M i)) p.2 ≫
        secondComponent D M e p :=
  Limits.Pi.lift_π _ _

/-- The chart projections of the equalizer satisfy the pairwise
compatibility equation. -/
lemma projection_compatibility (p : D.J × D.J) :
    projection D M e hIdentity hCocycle p.1 ≫
        firstComponent D M p =
      projection D M e hIdentity hCocycle p.2 ≫
        secondComponent D M e p := by
  have heq :
      equalizer.ι (firstLeg D M) (secondLeg D M e) ≫
          firstLeg D M =
        equalizer.ι (firstLeg D M) (secondLeg D M e) ≫
          secondLeg D M e :=
    equalizer.condition _ _
  calc
    projection D M e hIdentity hCocycle p.1 ≫
          firstComponent D M p =
        (glueIsoEqualizer D M e hIdentity hCocycle).hom ≫
          equalizer.ι (firstLeg D M) (secondLeg D M e) ≫
          (Pi.π (fun i =>
            (Scheme.Modules.pushforward (D.ι i)).obj (M i)) p.1 ≫
            firstComponent D M p) := by
      rw [projection]
      exact (Category.assoc _ _ _).symm
    _ = (glueIsoEqualizer D M e hIdentity hCocycle).hom ≫
          equalizer.ι (firstLeg D M) (secondLeg D M e) ≫
          (firstLeg D M ≫
            overlapProjection D M p) :=
      congrArg
        (fun z =>
          (glueIsoEqualizer D M e hIdentity hCocycle).hom ≫
            equalizer.ι (firstLeg D M) (secondLeg D M e) ≫ z)
        (firstLeg_projection D M p).symm
    _ = (glueIsoEqualizer D M e hIdentity hCocycle).hom ≫
          (equalizer.ι (firstLeg D M) (secondLeg D M e) ≫
            firstLeg D M) ≫
          overlapProjection D M p := by
      simp only [Category.assoc]
    _ = (glueIsoEqualizer D M e hIdentity hCocycle).hom ≫
          (equalizer.ι (firstLeg D M) (secondLeg D M e) ≫
            secondLeg D M e) ≫
          overlapProjection D M p :=
      congrArg
        (fun z =>
          (glueIsoEqualizer D M e hIdentity hCocycle).hom ≫ z ≫
            overlapProjection D M p)
        heq
    _ = (glueIsoEqualizer D M e hIdentity hCocycle).hom ≫
          equalizer.ι (firstLeg D M) (secondLeg D M e) ≫
          (secondLeg D M e ≫
            overlapProjection D M p) := by
      simp only [Category.assoc]
    _ = (glueIsoEqualizer D M e hIdentity hCocycle).hom ≫
          equalizer.ι (firstLeg D M) (secondLeg D M e) ≫
          (Pi.π (fun i =>
            (Scheme.Modules.pushforward (D.ι i)).obj (M i)) p.2 ≫
            secondComponent D M e p) :=
      congrArg
        (fun z =>
          (glueIsoEqualizer D M e hIdentity hCocycle).hom ≫
            equalizer.ι (firstLeg D M) (secondLeg D M e) ≫ z)
        (secondLeg_projection D M e p)
    _ = projection D M e hIdentity hCocycle p.2 ≫
          secondComponent D M e p := by
      rw [projection]
      exact (Category.assoc _ _ _).symm

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ModuleDescent

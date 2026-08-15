/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteEtaleRelativeProduct
import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteEtaleCoproductPower
import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteEtaleFamilyPointSplitChart
import MazurTorsion.AlgebraicGeometry.Jacobian.PermutationPower
import MazurTorsion.AlgebraicGeometry.Jacobian.SmoothCurveEtaleCoordinate

/-!
# Étale coordinates for a finite ordered support

An ordered lift of a degree-`d` divisor gives `d` actual curve points by
projection.  Choose an affine one-variable étale coordinate chart at every
one of those points.  Repeated support points are intentionally retained:
their multiplicities are needed by the residual stabilizer and monic-root
calculations.

The named downstream consumer is the pointwise local comparison in
`PointedIncidenceDescent`.
-/

noncomputable section

universe u

open scoped TensorProduct
open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.FiniteSupportEtaleCoordinates

open FiniteEtaleRelativeProduct
open FiniteEtaleCoproductPower
open SmoothCurveEtaleCoordinate

variable (K : Type u) [Field K]
variable (C : Over (Spec (.of K)))
variable [SmoothOfRelativeDimension 1 C.hom]

/-- The `i`-th curve point of an ordered lift of a divisor. -/
noncomputable def point (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (i : Fin d) : C.left :=
  (Pi.π (fun _ : Fin d ↦ C) i).left z

/-- A compatible finite family of affine étale coordinate charts, one for
every occurrence in the ordered support. -/
abbrev Charts (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left) :=
  ∀ i : Fin d, PointChart K C.left C.hom (point K C d z i)

/-- Every finite ordered support admits a family of affine étale
one-dimensional coordinate charts. -/
theorem nonempty_charts (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left) :
    Nonempty (Charts K C d z) := by
  exact ⟨fun i ↦ Classical.choice
    (exists_pointChart K C.left C.hom (point K C d z i))⟩

/-- A chosen finite family of étale coordinate charts for an ordered
support.  The subsequent construction is independent of this choice after
fpqc descent. -/
noncomputable def charts (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left) :
    Charts K C d z :=
  Classical.choice (nonempty_charts K C d z)

/-- A finite étale point neighborhood for every chosen coordinate chart. -/
abbrev Neighborhoods (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) :=
  ∀ i : Fin d, PointChart.FiniteNeighborhood (c i)

/-- The chosen Zariski-main neighborhoods of all occurrences in the ordered
support. -/
noncomputable def neighborhoods (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) : Neighborhoods K C d z c :=
  fun i ↦ (c i).finiteNeighborhood

/-- The common relative product of the étale bases of a finite family of
point neighborhoods. -/
noncomputable abbrev commonBase (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) :
    Over (coordinateBase K) :=
  ∏ᶜ fun i : Fin d ↦ (n i).baseOver

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- The common product base has a point because every selected étale base
contains the point supplied by Zariski's main theorem and the ground-field
spectrum has one underlying point. -/
theorem commonBase_nonempty (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) :
    Nonempty (commonBase K C d z c n).left := by
  apply product_nonempty
  intro i
  exact ⟨(n i).basePoint⟩

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- The selected base points lift simultaneously to a point of the relative
product, with the prescribed value under every projection. -/
theorem exists_commonBasePoint_with_projections (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) :
    ∃ y : (commonBase K C d z c n).left,
      ∀ i, (Pi.π (fun j : Fin d ↦ (n j).baseOver) i).left y =
        (n i).basePoint := by
  exact exists_fin_product_point (coordinateBase K) d
    (fun i ↦ (n i).baseOver) (fun i ↦ (n i).basePoint)

/-- A chosen point of the common product base. -/
noncomputable def commonBasePoint (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) :
    (commonBase K C d z c n).left :=
  Classical.choose (exists_commonBasePoint_with_projections K C d z c n)

omit [SmoothOfRelativeDimension 1 C.hom] in
@[simp]
theorem commonBasePoint_projection (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) (i : Fin d) :
    (Pi.π (fun j : Fin d ↦ (n j).baseOver) i).left
        (commonBasePoint K C d z c n) = (n i).basePoint :=
  Classical.choose_spec
    (exists_commonBasePoint_with_projections K C d z c n) i

/-- Pull the `i`-th selected finite étale component to the common product
base. -/
noncomputable abbrev pulledComponent (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) (i : Fin d) :
    Over (coordinateBase K) :=
  pullback (n i).componentToBase
    (Pi.π (fun j : Fin d ↦ (n j).baseOver) i)

/-- The base-changed selected component over the common product base. -/
noncomputable def pulledComponentToCommonBase (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) (i : Fin d) :
    pulledComponent K C d z c n i ⟶ commonBase K C d z c n :=
  pullback.snd (n i).componentToBase
    (Pi.π (fun j : Fin d ↦ (n j).baseOver) i)

/-- A model of the base-changed component whose structure morphism is
definitionally the scheme-theoretic pullback projection.  This form exposes
finite and étale base-change instances directly. -/
noncomputable abbrev pulledComponentOverCommonBase (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) (i : Fin d) :
    Over (commonBase K C d z c n).left :=
  Over.mk (pullback.snd (n i).componentToBase.left
    (Pi.π (fun j : Fin d ↦ (n j).baseOver) i).left)

instance pulledComponentOverCommonBase_isFinite (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) (i : Fin d) :
    IsFinite (pulledComponentOverCommonBase K C d z c n i).hom := by
  exact MorphismProperty.pullback_snd (P := @IsFinite) _ _
    (show IsFinite (n i).componentToBase.left from inferInstance)

instance pulledComponentOverCommonBase_etale (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) (i : Fin d) :
    Etale (pulledComponentOverCommonBase K C d z c n i).hom := by
  exact MorphismProperty.pullback_snd (P := @Etale) _ _
    (show Etale (n i).componentToBase.left from inferInstance)

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- The selected component point and the common base point lift together to
the base-changed component. -/
theorem exists_pulledComponentPoint (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) (i : Fin d) :
    ∃ p : (pulledComponentOverCommonBase K C d z c n i).left,
      pullback.fst (n i).componentToBase.left
          (Pi.π (fun j : Fin d ↦ (n j).baseOver) i).left p =
        (n i).selectedPoint ∧
      pullback.snd (n i).componentToBase.left
          (Pi.π (fun j : Fin d ↦ (n j).baseOver) i).left p =
        commonBasePoint K C d z c n := by
  apply Scheme.Pullback.exists_preimage_pullback
  simpa using (commonBasePoint_projection K C d z c n i).symm

/-- The chosen lift of the selected support point to its common-base
component. -/
noncomputable def pulledComponentPoint (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) (i : Fin d) :
    (pulledComponentOverCommonBase K C d z c n i).left :=
  Classical.choose (exists_pulledComponentPoint K C d z c n i)

omit [SmoothOfRelativeDimension 1 C.hom] in
@[simp]
theorem pulledComponentPoint_fst (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) (i : Fin d) :
    pullback.fst (n i).componentToBase.left
        (Pi.π (fun j : Fin d ↦ (n j).baseOver) i).left
          (pulledComponentPoint K C d z c n i) = (n i).selectedPoint :=
  (Classical.choose_spec (exists_pulledComponentPoint K C d z c n i)).1

omit [SmoothOfRelativeDimension 1 C.hom] in
@[simp]
theorem pulledComponentPoint_snd (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) (i : Fin d) :
    pullback.snd (n i).componentToBase.left
        (Pi.π (fun j : Fin d ↦ (n j).baseOver) i).left
          (pulledComponentPoint K C d z c n i) =
      commonBasePoint K C d z c n :=
  (Classical.choose_spec (exists_pulledComponentPoint K C d z c n i)).2

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- Every selected support component has positive fiber rank at the chosen
common-base point. -/
theorem one_le_pulledComponent_finrank (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) (i : Fin d) :
    1 ≤ (pulledComponentOverCommonBase K C d z c n i).hom.finrank
      (commonBasePoint K C d z c n) := by
  rw [← pulledComponentPoint_snd K C d z c n i]
  exact Scheme.Hom.one_le_finrank_map
    (pulledComponentOverCommonBase K C d z c n i).hom
      (pulledComponentPoint K C d z c n i)

/-- The relative product of all selected components over their common base. -/
noncomputable abbrev commonComponentFamily (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) :
    Over (commonBase K C d z c n).left :=
  ∏ᶜ fun i : Fin d ↦ pulledComponentOverCommonBase K C d z c n i

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- The assembled family is finite étale over the common product base. -/
theorem commonComponentFamily_isFiniteEtale (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) :
    finiteEtaleOver (commonBase K C d z c n).left
      (commonComponentFamily K C d z c n) := by
  apply product_isFiniteEtale
  intro i
  exact ⟨inferInstance, inferInstance⟩

instance commonComponentFamily_isFinite (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) :
    IsFinite (commonComponentFamily K C d z c n).hom :=
  (commonComponentFamily_isFiniteEtale K C d z c n).1

instance commonComponentFamily_etale (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) :
    Etale (commonComponentFamily K C d z c n).hom :=
  (commonComponentFamily_isFiniteEtale K C d z c n).2

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- The lifted support points assemble to a point of the simultaneous finite
étale component family over the chosen common-base point. -/
theorem exists_commonComponentFamilyPoint (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) :
    ∃ p : (commonComponentFamily K C d z c n).left,
      (commonComponentFamily K C d z c n).hom p =
          commonBasePoint K C d z c n ∧
        ∀ i, (Pi.π
          (fun j : Fin d ↦ pulledComponentOverCommonBase K C d z c n j)
          i).left p = pulledComponentPoint K C d z c n i := by
  exact exists_fin_product_point_over
    (commonBase K C d z c n).left d
    (fun i ↦ pulledComponentOverCommonBase K C d z c n i)
    (commonBasePoint K C d z c n)
    (fun i ↦ pulledComponentPoint K C d z c n i)
    (fun i ↦ pulledComponentPoint_snd K C d z c n i)

/-- The chosen point of the simultaneous finite étale component family
lifting the original ordered support. -/
noncomputable def commonComponentFamilyPoint (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) :
    (commonComponentFamily K C d z c n).left :=
  Classical.choose (exists_commonComponentFamilyPoint K C d z c n)

omit [SmoothOfRelativeDimension 1 C.hom] in
@[simp]
theorem commonComponentFamilyPoint_structure (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) :
    (commonComponentFamily K C d z c n).hom
        (commonComponentFamilyPoint K C d z c n) =
      commonBasePoint K C d z c n :=
  (Classical.choose_spec
    (exists_commonComponentFamilyPoint K C d z c n)).1

omit [SmoothOfRelativeDimension 1 C.hom] in
@[simp]
theorem commonComponentFamilyPoint_projection (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) (i : Fin d) :
    (Pi.π
      (fun j : Fin d ↦ pulledComponentOverCommonBase K C d z c n j)
      i).left (commonComponentFamilyPoint K C d z c n) =
        pulledComponentPoint K C d z c n i :=
  (Classical.choose_spec
    (exists_commonComponentFamilyPoint K C d z c n)).2 i

/-- The `i`-th common-base component still maps to the original curve. -/
noncomputable def pulledComponentToCurve (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) (i : Fin d) :
    (pulledComponentOverCommonBase K C d z c n i).left ⟶ C.left :=
  pullback.fst (n i).componentToBase.left
      (Pi.π (fun j : Fin d ↦ (n j).baseOver) i).left ≫
    (n i).componentToCurve

/-- The exact scheme-theoretic common-base pullback component, regarded over
the coordinate copy of the ground field. -/
noncomputable def pulledComponentOverCoordinateBase (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) (i : Fin d) :
    Over (coordinateBase K) :=
  Over.mk ((pulledComponentOverCommonBase K C d z c n i).hom ≫
    (commonBase K C d z c n).hom)

/-- The exact pullback component maps to its original Zariski-main
component over the coordinate base. -/
noncomputable def pulledComponentToComponentOver (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) (i : Fin d) :
    pulledComponentOverCoordinateBase K C d z c n i ⟶
      (n i).componentOver :=
  Over.homMk
    (pullback.fst (n i).componentToBase.left
      (Pi.π (fun j : Fin d ↦ (n j).baseOver) i).left) (by
        let π := Pi.π (fun j : Fin d ↦ (n j).baseOver) i
        have hpb := pullback.condition
          (f := (n i).componentToBase.left) (g := π.left)
        have hc := (n i).componentToBase.w
        have hπ := π.w
        change pullback.fst (n i).componentToBase.left π.left ≫
            (n i).componentOver.hom =
          pullback.snd (n i).componentToBase.left π.left ≫
            (commonBase K C d z c n).hom
        calc
          pullback.fst (n i).componentToBase.left π.left ≫
              (n i).componentOver.hom =
            pullback.fst (n i).componentToBase.left π.left ≫
              ((n i).componentToBase.left ≫ (n i).baseOver.hom) :=
            congrArg
              (fun a ↦ pullback.fst (n i).componentToBase.left π.left ≫ a)
              hc.symm
          _ = (pullback.fst (n i).componentToBase.left π.left ≫
                (n i).componentToBase.left) ≫ (n i).baseOver.hom :=
            (Category.assoc _ _ _).symm
          _ = (pullback.snd (n i).componentToBase.left π.left ≫
                π.left) ≫ (n i).baseOver.hom := congrArg
            (fun a ↦ a ≫ (n i).baseOver.hom) hpb
          _ = pullback.snd (n i).componentToBase.left π.left ≫
                (π.left ≫ (n i).baseOver.hom) := Category.assoc _ _ _
          _ = pullback.snd (n i).componentToBase.left π.left ≫
                (commonBase K C d z c n).hom := congrArg
            (fun a ↦ pullback.snd (n i).componentToBase.left π.left ≫ a)
            hπ)

/-- The common-base pullback component maps to the curve over the coordinate
copy of the ground field. -/
noncomputable def pulledComponentToCurveOverCoordinateBase (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) (i : Fin d) :
    pulledComponentOverCoordinateBase K C d z c n i ⟶
      PointChart.curveOverCoordinateBase K C.left C.hom :=
  pulledComponentToComponentOver K C d z c n i ≫
    (n i).componentToCurveOver

omit [SmoothOfRelativeDimension 1 C.hom] in
theorem pulledComponentToCurveOverCoordinateBase_left (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) (i : Fin d) :
    (pulledComponentToCurveOverCoordinateBase K C d z c n i).left =
      pulledComponentToCurve K C d z c n i :=
  rfl

/-- The same pulled component, with its structure map transported back to
the original ground-field spectrum. -/
noncomputable def pulledComponentOverGround (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) (i : Fin d) :
    Over (Spec (.of K)) :=
  Over.mk ((pulledComponentOverCoordinateBase K C d z c n i).hom ≫
    (coordinateBaseIso K).hom)

/-- The pulled component maps to the original curve as a morphism over the
ground field. -/
noncomputable def pulledComponentToCurveOverGround (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) (i : Fin d) :
    pulledComponentOverGround K C d z c n i ⟶ C :=
  Over.homMk (pulledComponentToCurve K C d z c n i) (by
    change pulledComponentToCurve K C d z c n i ≫ C.hom =
      (pulledComponentOverCoordinateBase K C d z c n i).hom ≫
        (coordinateBaseIso K).hom
    have h := (pulledComponentToCurveOverCoordinateBase K C d z c n i).w
    have hpost := congrArg (fun q ↦ q ≫ (coordinateBaseIso K).hom) h
    change (pulledComponentToCurveOverCoordinateBase K C d z c n i).left ≫
        ((C.hom ≫ (coordinateBaseIso K).inv) ≫
          (coordinateBaseIso K).hom) =
      (pulledComponentOverCoordinateBase K C d z c n i).hom ≫
        (coordinateBaseIso K).hom at hpost
    rw [pulledComponentToCurveOverCoordinateBase_left] at hpost
    have hcancel :
        (C.hom ≫ (coordinateBaseIso K).inv) ≫
            (coordinateBaseIso K).hom = C.hom := by
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hpref := congrArg
      (fun a ↦ pulledComponentToCurve K C d z c n i ≫ a) hcancel
    exact hpref.symm.trans hpost)

omit [SmoothOfRelativeDimension 1 C.hom] in
@[simp]
theorem pulledComponentToCurve_point (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) (i : Fin d) :
    pulledComponentToCurve K C d z c n i
        (pulledComponentPoint K C d z c n i) = point K C d z i := by
  change (n i).componentToCurve
    (pullback.fst (n i).componentToBase.left
      (Pi.π (fun j : Fin d ↦ (n j).baseOver) i).left
        (pulledComponentPoint K C d z c n i)) = point K C d z i
  rw [pulledComponentPoint_fst]
  exact (n i).componentToCurve_selectedPoint

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- The product of the selected pulled components contains a point mapping
to the original ordered support point.  Unlike a coordinatewise point
construction, this statement retains the residue-field correlation encoded
by the point of the relative power. -/
theorem exists_pulledComponentProductPoint_over_support (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) :
    ∃ w : (∏ᶜ fun i : Fin d ↦
        pulledComponentOverGround K C d z c n i).left,
      (Limits.Pi.map (fun i ↦
        pulledComponentToCurveOverGround K C d z c n i)).left w = z ∧
      ∀ i, (Pi.π (fun j : Fin d ↦
        pulledComponentOverGround K C d z c n j) i).left w =
          pulledComponentPoint K C d z c n i := by
  apply exists_fin_product_preimage (Spec (.of K)) d
    (fun _ : Fin d ↦ C)
    (fun i ↦ pulledComponentOverGround K C d z c n i)
    (fun i ↦ pulledComponentToCurveOverGround K C d z c n i)
    z (fun i ↦ pulledComponentPoint K C d z c n i)
  intro i
  exact pulledComponentToCurve_point K C d z c n i

/-- Restrict the `i`-th pulled component over an open neighborhood of the
common-base point, then regard it as a scheme over the original ground
field through its map to the curve. -/
noncomputable def restrictedPulledComponentOverGround (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens) (i : Fin d) :
    Over (Spec (.of K)) :=
  Over.mk (((pulledComponentOverCommonBase K C d z c n i).hom ⁻¹ᵁ V).ι ≫
    pulledComponentToCurve K C d z c n i ≫ C.hom)

/-- The restricted component maps to the curve over the ground field. -/
noncomputable def restrictedPulledComponentToCurveOverGround (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens) (i : Fin d) :
    restrictedPulledComponentOverGround K C d z c n V i ⟶ C :=
  Over.homMk
    (((pulledComponentOverCommonBase K C d z c n i).hom ⁻¹ᵁ V).ι ≫
      pulledComponentToCurve K C d z c n i) rfl

/-- The prescribed component point belongs to every restriction whose base
open contains the common-base point. -/
noncomputable def restrictedPulledComponentPoint (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (hV : commonBasePoint K C d z c n ∈ V) (i : Fin d) :
    ((pulledComponentOverCommonBase K C d z c n i).hom ⁻¹ᵁ V).toScheme :=
  ⟨pulledComponentPoint K C d z c n i, by
    change (pulledComponentOverCommonBase K C d z c n i).hom
      (pulledComponentPoint K C d z c n i) ∈ V
    have hp : (pulledComponentOverCommonBase K C d z c n i).hom
        (pulledComponentPoint K C d z c n i) =
          commonBasePoint K C d z c n :=
      pulledComponentPoint_snd K C d z c n i
    rw [hp]
    exact hV⟩

omit [SmoothOfRelativeDimension 1 C.hom] in
@[simp]
theorem restrictedPulledComponentToCurve_point (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (hV : commonBasePoint K C d z c n ∈ V) (i : Fin d) :
    (restrictedPulledComponentToCurveOverGround K C d z c n V i).left
        (restrictedPulledComponentPoint K C d z c n V hV i) =
      point K C d z i := by
  change pulledComponentToCurve K C d z c n i
    (pulledComponentPoint K C d z c n i) = point K C d z i
  exact pulledComponentToCurve_point K C d z c n i

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- Restricting every component to a common-base neighborhood still gives a
product chart containing the exact original ordered-support point. -/
theorem exists_restrictedPulledComponentProductPoint_over_support (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (hV : commonBasePoint K C d z c n ∈ V) :
    ∃ w : (∏ᶜ fun i : Fin d ↦
        restrictedPulledComponentOverGround K C d z c n V i).left,
      (Limits.Pi.map (fun i ↦
        restrictedPulledComponentToCurveOverGround K C d z c n V i)).left w = z ∧
      ∀ i, (Pi.π (fun j : Fin d ↦
        restrictedPulledComponentOverGround K C d z c n V j) i).left w =
          restrictedPulledComponentPoint K C d z c n V hV i := by
  apply exists_fin_product_preimage (Spec (.of K)) d
    (fun _ : Fin d ↦ C)
    (fun i ↦ restrictedPulledComponentOverGround K C d z c n V i)
    (fun i ↦ restrictedPulledComponentToCurveOverGround K C d z c n V i)
    z (fun i ↦ restrictedPulledComponentPoint K C d z c n V hV i)
  intro i
  exact restrictedPulledComponentToCurve_point K C d z c n V hV i

/-- The restriction of the `i`-th component to a common-base open. -/
noncomputable def restrictedPulledComponentToBase (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens) (i : Fin d) :
    ((pulledComponentOverCommonBase K C d z c n i).hom ⁻¹ᵁ V).toScheme ⟶
      V.toScheme :=
  (pulledComponentOverCommonBase K C d z c n i).hom ∣_ V

/-- The chosen common-base open, regarded over the original ground field. -/
noncomputable def restrictedCommonBaseOverGround (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens) : Over (Spec (.of K)) :=
  Over.mk (V.ι ≫ (commonBase K C d z c n).hom ≫ (coordinateBaseIso K).hom)

/-- The restricted selected component maps to the common-base open over the
original ground field. -/
noncomputable def restrictedPulledComponentToBaseOverGround (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens) (i : Fin d) :
    restrictedPulledComponentOverGround K C d z c n V i ⟶
      restrictedCommonBaseOverGround K C d z c n V :=
  Over.homMk (restrictedPulledComponentToBase K C d z c n V i) (by
    unfold restrictedPulledComponentToBase
    change ((pulledComponentOverCommonBase K C d z c n i).hom ∣_ V) ≫ V.ι ≫
          (commonBase K C d z c n).hom ≫ (coordinateBaseIso K).hom =
      ((pulledComponentOverCommonBase K C d z c n i).hom ⁻¹ᵁ V).ι ≫
        pulledComponentToCurve K C d z c n i ≫ C.hom
    rw [← Category.assoc, morphismRestrict_ι]
    have hcurve := (pulledComponentToCurveOverGround K C d z c n i).w
    change pulledComponentToCurve K C d z c n i ≫ C.hom =
      (pulledComponentOverCommonBase K C d z c n i).hom ≫
        (commonBase K C d z c n).hom ≫ (coordinateBaseIso K).hom at hcurve
    rw [hcurve]
    simp only [Category.assoc])

/-- A further common cover of the restricted base, regarded over the
original ground field. -/
noncomputable def commonCoverOverGround (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) : Over (Spec (.of K)) :=
  Over.mk (q ≫ (restrictedCommonBaseOverGround K C d z c n V).hom)

/-- Pull a restricted component to a further common fpqc base, then regard
it over the original ground field through its curve map. -/
noncomputable def fpqcPulledComponentOverGround (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    Over (Spec (.of K)) :=
  Over.mk (pullback.fst
      (restrictedPulledComponentToBase K C d z c n V i) q ≫
    (restrictedPulledComponentToCurveOverGround K C d z c n V i).left ≫
    C.hom)

/-- The fpqc-pulled component maps back to the restricted component. -/
noncomputable def fpqcPulledComponentToRestrictedOverGround (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    fpqcPulledComponentOverGround K C d z c n V T q i ⟶
      restrictedPulledComponentOverGround K C d z c n V i :=
  Over.homMk
    (pullback.fst (restrictedPulledComponentToBase K C d z c n V i) q) rfl

/-- The base-changed component maps to the common cover over the ground
field through the second pullback projection. -/
noncomputable def fpqcPulledComponentToCoverOverGround (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    fpqcPulledComponentOverGround K C d z c n V T q i ⟶
      commonCoverOverGround K C d z c n V T q :=
  Over.homMk
    (pullback.snd (restrictedPulledComponentToBase K C d z c n V i) q) (by
      unfold commonCoverOverGround restrictedCommonBaseOverGround
      let f := restrictedPulledComponentToBase K C d z c n V i
      let π₁ := pullback.fst f q
      let π₂ := pullback.snd f q
      let b : V.toScheme ⟶ Spec (.of K) :=
        V.ι ≫ (commonBase K C d z c n).hom ≫ (coordinateBaseIso K).hom
      have hpb : π₁ ≫ f = π₂ ≫ q := pullback.condition
      have hf : f ≫ b =
          (restrictedPulledComponentOverGround K C d z c n V i).hom := by
        exact (restrictedPulledComponentToBaseOverGround
          K C d z c n V i).w
      have hπ₁ : π₁ ≫
          (restrictedPulledComponentOverGround K C d z c n V i).hom =
            (fpqcPulledComponentOverGround K C d z c n V T q i).hom := by
        exact (fpqcPulledComponentToRestrictedOverGround
          K C d z c n V T q i).w
      change π₂ ≫ q ≫ b =
        (fpqcPulledComponentOverGround K C d z c n V T q i).hom
      have hpbPost :
          π₂ ≫ q ≫ b = π₁ ≫ f ≫ b := by
        simpa only [Category.assoc] using
          congrArg (fun a ↦ a ≫ b) hpb.symm
      have hfPost :
          π₁ ≫ f ≫ b =
            π₁ ≫
              (restrictedPulledComponentOverGround K C d z c n V i).hom :=
        congrArg (fun a ↦ π₁ ≫ a) hf
      exact hpbPost.trans (hfPost.trans hπ₁))

/-- The fpqc-pulled component maps to the original curve. -/
noncomputable def fpqcPulledComponentToCurveOverGround (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    fpqcPulledComponentOverGround K C d z c n V T q i ⟶ C :=
  fpqcPulledComponentToRestrictedOverGround K C d z c n V T q i ≫
    restrictedPulledComponentToCurveOverGround K C d z c n V i

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- A surjective further base change has a point above the prescribed
restricted component point. -/
theorem exists_fpqcPulledComponentPoint (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (hV : commonBasePoint K C d z c n ∈ V)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) [Surjective q] (i : Fin d) :
    ∃ p : (fpqcPulledComponentOverGround K C d z c n V T q i).left,
      pullback.fst (restrictedPulledComponentToBase K C d z c n V i) q p =
        restrictedPulledComponentPoint K C d z c n V hV i := by
  obtain ⟨t, ht⟩ := q.surjective
    ((restrictedPulledComponentToBase K C d z c n V i)
      (restrictedPulledComponentPoint K C d z c n V hV i))
  obtain ⟨p, hp, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (restrictedPulledComponentPoint K C d z c n V hV i) t ht.symm
  exact ⟨p, hp⟩

/-- A chosen point of the fpqc-pulled component above the prescribed
restricted point. -/
noncomputable def fpqcPulledComponentPoint (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (hV : commonBasePoint K C d z c n ∈ V)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) [Surjective q] (i : Fin d) :
    (fpqcPulledComponentOverGround K C d z c n V T q i).left :=
  Classical.choose
    (exists_fpqcPulledComponentPoint K C d z c n V hV T q i)

omit [SmoothOfRelativeDimension 1 C.hom] in
@[simp]
theorem fpqcPulledComponentPoint_fst (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (hV : commonBasePoint K C d z c n ∈ V)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) [Surjective q] (i : Fin d) :
    pullback.fst (restrictedPulledComponentToBase K C d z c n V i) q
        (fpqcPulledComponentPoint K C d z c n V hV T q i) =
      restrictedPulledComponentPoint K C d z c n V hV i :=
  Classical.choose_spec
    (exists_fpqcPulledComponentPoint K C d z c n V hV T q i)

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- After a common surjective base change, the product of all pulled
components still contains a point mapping to the exact ordered support. -/
theorem exists_fpqcPulledComponentProductPoint_over_support
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (hV : commonBasePoint K C d z c n ∈ V)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) [Surjective q] :
    ∃ p : (∏ᶜ fun i : Fin d ↦
        fpqcPulledComponentOverGround K C d z c n V T q i).left,
      (Limits.Pi.map (fun i ↦
        fpqcPulledComponentToCurveOverGround K C d z c n V T q i)).left p = z := by
  obtain ⟨w, hwz, hw⟩ :=
    exists_restrictedPulledComponentProductPoint_over_support
      K C d z c n V hV
  obtain ⟨p, hpw, _⟩ := exists_fin_product_preimage (Spec (.of K)) d
    (fun i ↦ restrictedPulledComponentOverGround K C d z c n V i)
    (fun i ↦ fpqcPulledComponentOverGround K C d z c n V T q i)
    (fun i ↦ fpqcPulledComponentToRestrictedOverGround K C d z c n V T q i)
    w (fun i ↦ fpqcPulledComponentPoint K C d z c n V hV T q i) (by
      intro i
      exact (fpqcPulledComponentPoint_fst K C d z c n V hV T q i).trans
        (hw i).symm)
  refine ⟨p, ?_⟩
  have hcomp := Limits.Pi.map_comp_map
    (fun i ↦ fpqcPulledComponentToRestrictedOverGround K C d z c n V T q i)
    (fun i ↦ restrictedPulledComponentToCurveOverGround K C d z c n V i)
  have hcompLeft := congrArg Over.Hom.left hcomp
  have hcompPoint := congrArg
    (fun a : (∏ᶜ fun i : Fin d ↦
      fpqcPulledComponentOverGround K C d z c n V T q i).left ⟶
        (PermutationPower.power (Spec (.of K)) (Fin d) C).left ↦ a p)
    hcompLeft
  calc
    (Limits.Pi.map (fun i ↦
        fpqcPulledComponentToCurveOverGround K C d z c n V T q i)).left p =
      (Limits.Pi.map (fun i ↦
        restrictedPulledComponentToCurveOverGround K C d z c n V i)).left
          ((Limits.Pi.map (fun i ↦
            fpqcPulledComponentToRestrictedOverGround
              K C d z c n V T q i)).left p) := hcompPoint.symm
    _ = (Limits.Pi.map (fun i ↦
        restrictedPulledComponentToCurveOverGround K C d z c n V i)).left w :=
      congrArg _ hpw
    _ = z := hwz

/-- The family consisting of one copy of the common cover for every ordered
support coordinate. -/
noncomputable abbrev commonCoverFamily (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) :
    Fin d → Over (Spec (.of K)) :=
  fun _ ↦ commonCoverOverGround K C d z c n V T q

/-- The independently based family of pulled support components. -/
noncomputable abbrev fpqcPulledComponentFamily (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) :
    Fin d → Over (Spec (.of K)) :=
  fun i ↦ fpqcPulledComponentOverGround K C d z c n V T q i

/-- Pull every independently based component to one product of the common
cover, using the matching base projection in its ordered coordinate. -/
noncomputable abbrev coherentFpqcPulledComponent (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :=
  independentPullback (Spec (.of K)) d
    (commonCoverFamily K C d z c n V T q)
    (fpqcPulledComponentFamily K C d z c n V T q)
    (fun j ↦ fpqcPulledComponentToCoverOverGround
      K C d z c n V T q j) i

/-- The product of the coordinate copies of the common splitting cover. -/
noncomputable abbrev coherentFpqcBase (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) : Scheme.{u} :=
  (∏ᶜ commonCoverFamily K C d z c n V T q).left

/-- One coherent pulled component maps back to the curve. -/
noncomputable def coherentFpqcPulledComponentToCurve (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    (coherentFpqcPulledComponent K C d z c n V T q i).left ⟶ C.left :=
  pullback.fst
      (fpqcPulledComponentToCoverOverGround K C d z c n V T q i).left
      (Pi.π (commonCoverFamily K C d z c n V T q) i).left ≫
    (fpqcPulledComponentToCurveOverGround K C d z c n V T q i).left

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- The coherent component-to-curve map is compatible with the map from the
product splitting base to the ground field. -/
theorem coherentFpqcPulledComponentToCurve_comp_structureMap (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    coherentFpqcPulledComponentToCurve K C d z c n V T q i ≫ C.hom =
      (coherentFpqcPulledComponent K C d z c n V T q i).hom ≫
        (∏ᶜ commonCoverFamily K C d z c n V T q).hom := by
  let f := fpqcPulledComponentToCoverOverGround K C d z c n V T q i
  let π := Pi.π (commonCoverFamily K C d z c n V T q) i
  let g := fpqcPulledComponentToCurveOverGround K C d z c n V T q i
  have hpb : pullback.fst f.left π.left ≫ f.left =
      pullback.snd f.left π.left ≫ π.left := pullback.condition
  have hf := f.w
  have hπ := π.w
  have hg := g.w
  calc
    coherentFpqcPulledComponentToCurve K C d z c n V T q i ≫ C.hom =
        pullback.fst f.left π.left ≫ (g.left ≫ C.hom) := by
          rfl
    _ = pullback.fst f.left π.left ≫
          (fpqcPulledComponentFamily K C d z c n V T q i).hom := by
            rw [hg]
    _ = pullback.fst f.left π.left ≫
          (f.left ≫ (commonCoverFamily K C d z c n V T q i).hom) := by
            rw [hf]
    _ = pullback.snd f.left π.left ≫
          (π.left ≫ (commonCoverFamily K C d z c n V T q i).hom) := by
            simpa only [Category.assoc] using congrArg
              (fun a ↦ a ≫ (commonCoverFamily K C d z c n V T q i).hom) hpb
    _ = pullback.snd f.left π.left ≫
          (∏ᶜ commonCoverFamily K C d z c n V T q).hom := by
            rw [hπ]

/-- The coherent components, assembled as one disjoint family over the
product splitting base. -/
noncomputable abbrev coherentFpqcFamilyCoproduct (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) : Over
      (coherentFpqcBase K C d z c n V T q) :=
  familyCoproduct (coherentFpqcBase K C d z c n V T q) d
    (coherentFpqcPulledComponent K C d z c n V T q)

/-- The ordered power of the disjoint coherent family, regarded over the
ground field. -/
noncomputable abbrev coherentFpqcFamilyCoproductPowerOverGround (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) : Over (Spec (.of K)) :=
  coproductPowerOverOriginalBase
    (coherentFpqcBase K C d z c n V T q) (Spec (.of K))
    (∏ᶜ commonCoverFamily K C d z c n V T q).hom d
    (coherentFpqcPulledComponent K C d z c n V T q)

/-- The coherent relative product, transported back to the original ground
field.  Its base is the product of the common split cover, once for each
ordered coordinate. -/
noncomputable abbrev coherentFpqcComponentFamilyOverGround (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) : Over (Spec (.of K)) :=
  independentRelativeProductOverOriginalBase (Spec (.of K)) d
    (commonCoverFamily K C d z c n V T q)
    (fpqcPulledComponentFamily K C d z c n V T q)
    (fun i ↦ fpqcPulledComponentToCoverOverGround
      K C d z c n V T q i)

/-- The coherent product chart maps to the original ordered curve power. -/
noncomputable def coherentFpqcComponentFamilyToCurvePower (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) :
    coherentFpqcComponentFamilyOverGround K C d z c n V T q ⟶
      PermutationPower.power (Spec (.of K)) (Fin d) C :=
  independentRelativeProductToTargets (Spec (.of K)) d
    (commonCoverFamily K C d z c n V T q)
    (fpqcPulledComponentFamily K C d z c n V T q)
    (fun _ : Fin d ↦ C)
    (fun i ↦ fpqcPulledComponentToCoverOverGround
      K C d z c n V T q i)
    (fun i ↦ fpqcPulledComponentToCurveOverGround
      K C d z c n V T q i)

/-- Insert the `i`-th coherent component into the `i`-th coordinate of the
ordered power of their disjoint union. -/
noncomputable def coherentFpqcComponentFamilyToCoproductPower (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) :
    coherentFpqcComponentFamilyOverGround K C d z c n V T q ⟶
      coherentFpqcFamilyCoproductPowerOverGround K C d z c n V T q :=
  productToCoproductPowerOverOriginalBase
    (coherentFpqcBase K C d z c n V T q) (Spec (.of K))
    (∏ᶜ commonCoverFamily K C d z c n V T q).hom d
    (coherentFpqcPulledComponent K C d z c n V T q)

/-- Forget the ordered power of the disjoint coherent family back to the
original ordered curve power. -/
noncomputable def coherentFpqcFamilyCoproductPowerToCurvePower (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) :
    coherentFpqcFamilyCoproductPowerOverGround K C d z c n V T q ⟶
      PermutationPower.power (Spec (.of K)) (Fin d) C :=
  coproductPowerToTargetPower
    (coherentFpqcBase K C d z c n V T q) (Spec (.of K))
    (∏ᶜ commonCoverFamily K C d z c n V T q).hom d
    (coherentFpqcPulledComponent K C d z c n V T q) C
    (coherentFpqcPulledComponentToCurve K C d z c n V T q)
    (coherentFpqcPulledComponentToCurve_comp_structureMap
      K C d z c n V T q)

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- The direct coherent-family map to the curve power is the target map
induced by its individual component-to-curve morphisms. -/
theorem productToTargetPower_eq_coherentFpqcComponentFamilyToCurvePower
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) :
    productToTargetPower
        (coherentFpqcBase K C d z c n V T q) (Spec (.of K))
        (∏ᶜ commonCoverFamily K C d z c n V T q).hom d
        (coherentFpqcPulledComponent K C d z c n V T q) C
        (coherentFpqcPulledComponentToCurve K C d z c n V T q)
        (coherentFpqcPulledComponentToCurve_comp_structureMap
          K C d z c n V T q) =
      coherentFpqcComponentFamilyToCurvePower K C d z c n V T q := by
  apply Pi.hom_ext
  intro i
  unfold productToTargetPower coherentFpqcComponentFamilyToCurvePower
    independentRelativeProductToTargets
  rw [Pi.lift_π, Pi.lift_π]
  apply Over.OverMorphism.ext
  rfl

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- Passing from the coherent product to the ordered power of its disjoint
family preserves the exact map to the original curve power. -/
theorem coherentFpqcComponentFamilyToCoproductPower_comp_curvePower
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) :
    coherentFpqcComponentFamilyToCoproductPower K C d z c n V T q ≫
        coherentFpqcFamilyCoproductPowerToCurvePower K C d z c n V T q =
      coherentFpqcComponentFamilyToCurvePower K C d z c n V T q := by
  exact (productToCoproductPower_comp_targetPower
    (coherentFpqcBase K C d z c n V T q) (Spec (.of K))
    (∏ᶜ commonCoverFamily K C d z c n V T q).hom d
    (coherentFpqcPulledComponent K C d z c n V T q) C
    (coherentFpqcPulledComponentToCurve K C d z c n V T q)
    (coherentFpqcPulledComponentToCurve_comp_structureMap
      K C d z c n V T q)).trans
    (productToTargetPower_eq_coherentFpqcComponentFamilyToCurvePower
      K C d z c n V T q)

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- The exact ordered-support point survives transport from the independent
product to the coherent product over one product splitting base. -/
theorem exists_coherentFpqcComponentFamilyPoint_over_support
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (hV : commonBasePoint K C d z c n ∈ V)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) [Surjective q] :
    ∃ p : (coherentFpqcComponentFamilyOverGround
        K C d z c n V T q).left,
      (coherentFpqcComponentFamilyToCurvePower
        K C d z c n V T q).left p = z := by
  obtain ⟨w, hw⟩ := exists_fpqcPulledComponentProductPoint_over_support
    K C d z c n V hV T q
  let f := fun i ↦ fpqcPulledComponentToCoverOverGround
    K C d z c n V T q i
  let g := fun i ↦ fpqcPulledComponentToCurveOverGround
    K C d z c n V T q i
  let toCoherent := independentProductToRelativeProductOverOriginalBase
    (Spec (.of K)) d
      (commonCoverFamily K C d z c n V T q)
      (fpqcPulledComponentFamily K C d z c n V T q) f
  let p := toCoherent.left w
  refine ⟨p, ?_⟩
  have hmap := independentProductToRelativeProduct_comp_targets
    (Spec (.of K)) d
      (commonCoverFamily K C d z c n V T q)
      (fpqcPulledComponentFamily K C d z c n V T q)
      (fun _ : Fin d ↦ C) f g
  have hmapLeft := congrArg Over.Hom.left hmap
  have hmapPoint := congrArg
    (fun a : (∏ᶜ fpqcPulledComponentFamily K C d z c n V T q).left ⟶
        (PermutationPower.power (Spec (.of K)) (Fin d) C).left ↦ a w)
    hmapLeft
  exact hmapPoint.trans hw

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- The exact ordered-support point lies in the ordered power of the single
disjoint coherent family. -/
theorem exists_coherentFpqcFamilyCoproductPowerPoint_over_support
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (hV : commonBasePoint K C d z c n ∈ V)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) [Surjective q] :
    ∃ p : (coherentFpqcFamilyCoproductPowerOverGround
        K C d z c n V T q).left,
      (coherentFpqcFamilyCoproductPowerToCurvePower
        K C d z c n V T q).left p = z := by
  obtain ⟨p, hp⟩ := exists_coherentFpqcComponentFamilyPoint_over_support
    K C d z c n V hV T q
  let toPower := coherentFpqcComponentFamilyToCoproductPower
    K C d z c n V T q
  refine ⟨toPower.left p, ?_⟩
  have hcomp := coherentFpqcComponentFamilyToCoproductPower_comp_curvePower
    K C d z c n V T q
  have hcompLeft := congrArg Over.Hom.left hcomp
  have hpoint := congrArg
    (fun a : (coherentFpqcComponentFamilyOverGround
        K C d z c n V T q).left ⟶
          (PermutationPower.power (Spec (.of K)) (Fin d) C).left ↦ a p)
    hcompLeft
  exact hpoint.trans hp

/-- The complete pointwise split-chart assertion for an ordered support:
one affine rank neighborhood, one common finite étale fpqc splitting cover,
and an exact preimage of the original ordered support on that cover. -/
def HasCommonSplitChartAtSupport (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) : Prop :=
    ∃ (V : (commonBase K C d z c n).left.Opens) (hV : IsAffineOpen V),
      commonBasePoint K C d z c n ∈ V ∧
      let f : ∀ i, (pulledComponentOverCommonBase K C d z c n i).left ⟶
          (commonBase K C d z c n).left :=
        fun i ↦ (pulledComponentOverCommonBase K C d z c n i).hom
      let fV : ∀ i, (f i ⁻¹ᵁ V).toScheme ⟶ V.toScheme :=
        fun i ↦ f i ∣_ V
      letI : IsAffine V.toScheme := hV
      letI (i : Fin d) : IsAffine (f i ⁻¹ᵁ V).toScheme :=
        isAffine_of_isAffineHom (fV i)
      letI (i : Fin d) : Algebra Γ(V, ⊤) Γ(f i ⁻¹ᵁ V, ⊤) :=
        (fV i).appTop.hom.toAlgebra
      ∃ (T : Type u) (_ : CommRing T) (_ : Algebra Γ(V, ⊤) T)
        (_ : Module.FaithfullyFlat Γ(V, ⊤) T)
        (_ : Module.Finite Γ(V, ⊤) T)
        (_ : Algebra.Etale Γ(V, ⊤) T)
        (q : Spec (.of T) ⟶ V.toScheme),
        Etale q ∧ Flat q ∧ Surjective q ∧ QuasiCompact q ∧
          (∀ i, ∃ (m : ℕ)
            (_e : T ⊗[Γ(V, ⊤)] Γ(f i ⁻¹ᵁ V, ⊤) ≃ₐ[T] (Fin m → T)),
            ∃ E : pullback (fV i) q ≅ Spec (.of (Fin m → T)),
              E.hom ≫ EtaleSplitChart.splitProjection T m =
                pullback.snd (fV i) q ∧
              m = (f i).finrank (commonBasePoint K C d z c n)) ∧
          ∃ p : (coherentFpqcFamilyCoproductPowerOverGround
              K C d z c n V (Spec (.of T)) q).left,
            (coherentFpqcFamilyCoproductPowerToCurvePower
              K C d z c n V (Spec (.of T)) q).left p = z

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- Near the chosen common-base point, all selected support components have
constant rank and split simultaneously after one finite étale fpqc cover. -/
theorem exists_commonSplitChartAtSupport (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) :
    HasCommonSplitChartAtSupport K C d z c n := by
  unfold HasCommonSplitChartAtSupport
  obtain ⟨V, hV, hmem, T, hT, hAlg, hFF, hFin, hEtale, q,
      hEtaleQ, hFlat, hSurj, hQC, hSplit⟩ :=
    FiniteEtaleFamilyPointSplitChart.exists_affineOpen_fpqc_common_splitCover
      d (fun i ↦ (pulledComponentOverCommonBase K C d z c n i).left)
        (fun i ↦ (pulledComponentOverCommonBase K C d z c n i).hom)
          (commonBasePoint K C d z c n)
  refine ⟨V, hV, hmem, T, hT, hAlg, hFF, hFin, hEtale, q,
    hEtaleQ, hFlat, hSurj, hQC, hSplit, ?_⟩
  letI : Surjective q := hSurj
  exact exists_coherentFpqcFamilyCoproductPowerPoint_over_support
    K C d z c n V hmem (Spec (.of T)) q

end MazurTorsion.AlgebraicGeometry.Jacobian.FiniteSupportEtaleCoordinates

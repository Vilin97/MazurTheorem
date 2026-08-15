/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteSupportCoordinateMaps

/-!
# Coherent support components as direct base changes

The coherent support chart is built in three stages: restrict a selected
finite component to an open of the common base, pull it to one fpqc cover,
and pull it once more along the matching projection from the product of all
copies of that cover.  This file pastes those three cartesian squares.

The result identifies the nested construction with the direct base change of
the original selected component.  Its two projections are recorded because
the incidence comparison needs both the map back to the component and the
map to the coherent base.  The named downstream consumer is the actual
ordered-support specialization in `PointedIncidenceDescent`.
-/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.CoherentComponentBaseChange

open FiniteSupportEtaleCoordinates
open FiniteSupportCoordinateMaps

variable (K : Type u) [Field K]
variable (C : Over (Spec (.of K)))
variable [SmoothOfRelativeDimension 1 C.hom]

/-- The map from the coherent product of the splitting bases back to the
original common support base, using its `i`-th coordinate. -/
noncomputable def coherentBaseToCommonBase
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    coherentFpqcBase K C d z c n V T q ⟶
      (commonBase K C d z c n).left :=
  (Pi.π (commonCoverFamily K C d z c n V T q) i).left ≫ q ≫ V.ι

/-- Forget the three successive base changes and return a coherent component
to the original selected component over the common support base. -/
noncomputable def coherentPulledComponentToOriginal
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    (coherentFpqcPulledComponent K C d z c n V T q i).left ⟶
      (pulledComponentOverCommonBase K C d z c n i).left :=
  pullback.fst
      (fpqcPulledComponentToCoverOverGround K C d z c n V T q i).left
      (Pi.π (commonCoverFamily K C d z c n V T q) i).left ≫
    (fpqcPulledComponentToRestrictedOverGround
      K C d z c n V T q i).left ≫
    ((pulledComponentOverCommonBase K C d z c n i).hom ⁻¹ᵁ V).ι

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- The coherent component is the direct base change of the original
selected component along the matching coherent-base coordinate. -/
theorem coherentPulledComponent_isPullback
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    IsPullback
      (coherentPulledComponentToOriginal K C d z c n V T q i)
      (coherentFpqcPulledComponent K C d z c n V T q i).hom
      (pulledComponentOverCommonBase K C d z c n i).hom
      (coherentBaseToCommonBase K C d z c n V T q i) := by
  let f := (pulledComponentOverCommonBase K C d z c n i).hom
  let fV := restrictedPulledComponentToBase K C d z c n V i
  let r := (fpqcPulledComponentToRestrictedOverGround
    K C d z c n V T q i).left
  let p := (fpqcPulledComponentToCoverOverGround
    K C d z c n V T q i).left
  let π := (Pi.π (commonCoverFamily K C d z c n V T q) i).left
  let a := pullback.fst p π
  let b := pullback.snd p π
  let j := (f ⁻¹ᵁ V).ι
  have hOuter : IsPullback a b p π := IsPullback.of_hasPullback p π
  have hMiddle : IsPullback r p fV q :=
    IsPullback.of_hasPullback fV q
  have hRestrict : IsPullback j fV f V.ι :=
    (isPullback_morphismRestrict f V).flip
  change IsPullback ((a ≫ r) ≫ j) b f ((π ≫ q) ≫ V.ι)
  exact (hOuter.paste_horiz hMiddle).paste_horiz hRestrict

/-- Canonical comparison from the nested coherent component to the direct
pullback of its original component. -/
noncomputable def coherentPulledComponentDirectIso
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    (coherentFpqcPulledComponent K C d z c n V T q i).left ≅
      pullback (pulledComponentOverCommonBase K C d z c n i).hom
        (coherentBaseToCommonBase K C d z c n V T q i) :=
  (coherentPulledComponent_isPullback K C d z c n V T q i).isoPullback

omit [SmoothOfRelativeDimension 1 C.hom] in
@[reassoc]
theorem coherentPulledComponentDirectIso_hom_fst
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    (coherentPulledComponentDirectIso K C d z c n V T q i).hom ≫
        pullback.fst (pulledComponentOverCommonBase K C d z c n i).hom
          (coherentBaseToCommonBase K C d z c n V T q i) =
      coherentPulledComponentToOriginal K C d z c n V T q i :=
  IsPullback.isoPullback_hom_fst
    (coherentPulledComponent_isPullback K C d z c n V T q i)

omit [SmoothOfRelativeDimension 1 C.hom] in
@[reassoc]
theorem coherentPulledComponentDirectIso_hom_snd
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    (coherentPulledComponentDirectIso K C d z c n V T q i).hom ≫
        pullback.snd (pulledComponentOverCommonBase K C d z c n i).hom
          (coherentBaseToCommonBase K C d z c n V T q i) =
      (coherentFpqcPulledComponent K C d z c n V T q i).hom :=
  IsPullback.isoPullback_hom_snd
    (coherentPulledComponent_isPullback K C d z c n V T q i)

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- Forgetting a coherent component to the original selected component and
then to the curve chart is its already defined coherent chart map. -/
@[reassoc]
theorem coherentPulledComponentToOriginal_comp_chart
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    coherentPulledComponentToOriginal K C d z c n V T q i ≫
        pulledComponentToChart K C d z c n i =
      coherentPulledComponentToChart K C d z c n V T q i := by
  let a : (coherentFpqcPulledComponent K C d z c n V T q i).left ⟶
      (fpqcPulledComponentOverGround K C d z c n V T q i).left :=
    pullback.fst
      (fpqcPulledComponentToCoverOverGround K C d z c n V T q i).left
      (Pi.π (commonCoverFamily K C d z c n V T q) i).left
  let r := (fpqcPulledComponentToRestrictedOverGround
    K C d z c n V T q i).left
  let j := ((pulledComponentOverCommonBase K C d z c n i).hom ⁻¹ᵁ V).ι
  let t := pulledComponentToChart K C d z c n i
  change (a ≫ (r ≫ j)) ≫ t = a ≫ (r ≫ (j ≫ t))
  exact (Category.assoc a (r ≫ j) t).trans
    (congrArg (fun b ↦ a ≫ b) (Category.assoc r j t))

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- The two ways from a coherent component to the original common support
base agree. -/
@[reassoc]
theorem coherentPulledComponentToOriginal_comp_structure
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    coherentPulledComponentToOriginal K C d z c n V T q i ≫
        (pulledComponentOverCommonBase K C d z c n i).hom =
      (coherentFpqcPulledComponent K C d z c n V T q i).hom ≫
        coherentBaseToCommonBase K C d z c n V T q i :=
  (coherentPulledComponent_isPullback K C d z c n V T q i).w

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- The affine-line coordinate on the coherent base factors through the
original common-base coordinate. -/
theorem coherentBaseToCommonBase_comp_coordinateLine
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    coherentBaseToCommonBase K C d z c n V T q i ≫
        commonBaseToCoordinateLine K C d z c n i =
      coherentBaseToCoordinateLine K C d z c n V T q i := by
  let π : coherentFpqcBase K C d z c n V T q ⟶ T :=
    (Pi.π (commonCoverFamily K C d z c n V T q) i).left
  let t := commonBaseToCoordinateLine K C d z c n i
  change (π ≫ (q ≫ V.ι)) ≫ t = π ≫ (q ≫ (V.ι ≫ t))
  exact (Category.assoc π (q ≫ V.ι) t).trans
    (congrArg (fun a ↦ π ≫ a) (Category.assoc q V.ι t))

/-- Transport the original open-and-closed selected component through the
direct coherent base change and into the matching base-changed curve chart. -/
noncomputable def coherentComponentToCoordinatePullback
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    (coherentFpqcPulledComponent K C d z c n V T q i).left ⟶
      pullback (c i).schemeMap
        (coherentBaseToCoordinateLine K C d z c n V T q i) :=
  let f := (c i).schemeMap
  let g := commonBaseToCoordinateLine K C d z c n i
  let π := coherentBaseToCommonBase K C d z c n V T q i
  let j := pulledComponentToCoordinatePullback K C d z c n i
  (coherentPulledComponentDirectIso K C d z c n V T q i).hom ≫
    (pullback.congrHom
      (pulledComponentToCoordinatePullback_snd K C d z c n i).symm rfl).hom ≫
    EtaleGraphCoproduct.baseChangedComponentInclusion f g π j ≫
    (pullback.congrHom rfl
      (coherentBaseToCommonBase_comp_coordinateLine
        K C d z c n V T q i)).hom

omit [SmoothOfRelativeDimension 1 C.hom] in
instance coherentComponentToCoordinatePullback_isOpenImmersion
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    IsOpenImmersion
      (coherentComponentToCoordinatePullback K C d z c n V T q i) := by
  unfold coherentComponentToCoordinatePullback
  infer_instance

omit [SmoothOfRelativeDimension 1 C.hom] in
instance coherentComponentToCoordinatePullback_isClosedImmersion
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    IsClosedImmersion
      (coherentComponentToCoordinatePullback K C d z c n V T q i) := by
  unfold coherentComponentToCoordinatePullback
  infer_instance

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- The coherent open-and-closed inclusion retains the map back to the
original affine curve chart. -/
theorem coherentComponentToCoordinatePullback_fst
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    coherentComponentToCoordinatePullback K C d z c n V T q i ≫
        pullback.fst (c i).schemeMap
          (coherentBaseToCoordinateLine K C d z c n V T q i) =
      coherentPulledComponentToChart K C d z c n V T q i := by
  simp only [coherentComponentToCoordinatePullback, Category.assoc,
    pullback.congrHom_hom]
  dsimp only [pullback.map]
  simp only [pullback.lift_fst, Category.comp_id]
  rw [EtaleGraphCoproduct.baseChangedComponentInclusion_fst]
  rw [pulledComponentToCoordinatePullback_fst]
  simp only [pullback.lift_fst_assoc,
    coherentPulledComponentDirectIso_hom_fst_assoc]
  exact coherentPulledComponentToOriginal_comp_chart K C d z c n V T q i

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- The coherent open-and-closed inclusion retains the projection to the
coherent product base. -/
theorem coherentComponentToCoordinatePullback_snd
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    coherentComponentToCoordinatePullback K C d z c n V T q i ≫
        pullback.snd (c i).schemeMap
          (coherentBaseToCoordinateLine K C d z c n V T q i) =
      (coherentFpqcPulledComponent K C d z c n V T q i).hom := by
  simp only [coherentComponentToCoordinatePullback, Category.assoc,
    pullback.congrHom_hom]
  dsimp only [pullback.map]
  simp only [pullback.lift_snd, Category.comp_id]
  rw [EtaleGraphCoproduct.baseChangedComponentInclusion_snd]
  rw [pullback.lift_snd]
  exact coherentPulledComponentDirectIso_hom_snd K C d z c n V T q i

omit [SmoothOfRelativeDimension 1 C.hom] in
/-- The whole coherent finite component, before choosing one of its split
sheets, is a coproduct summand of the curve-coordinate pullback. -/
theorem coherentComponent_exists_coordinatePullbackCoproduct
    (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c)
    (V : (commonBase K C d z c n).left.Opens)
    (T : Scheme.{u}) (q : T ⟶ V.toScheme) (i : Fin d) :
    ∃ (W : Scheme.{u})
      (E : pullback (c i).schemeMap
          (coherentBaseToCoordinateLine K C d z c n V T q i) ≅
        (coherentFpqcPulledComponent K C d z c n V T q i).left ⨿ W),
      coherentComponentToCoordinatePullback K C d z c n V T q i ≫ E.hom =
        coprod.inl :=
  EtaleGraphCoproduct.exists_coproduct_of_isOpenImmersion_isClosedImmersion
    (coherentComponentToCoordinatePullback K C d z c n V T q i)

end MazurTorsion.AlgebraicGeometry.Jacobian.CoherentComponentBaseChange

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.FiniteEtaleRelativeProduct
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

/-- The `i`-th common-base component still maps to the original curve. -/
noncomputable def pulledComponentToCurve (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) (i : Fin d) :
    (pulledComponentOverCommonBase K C d z c n i).left ⟶ C.left :=
  pullback.fst (n i).componentToBase.left
      (Pi.π (fun j : Fin d ↦ (n j).baseOver) i).left ≫
    (n i).componentToCurve

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
/-- Near the chosen common-base point, all selected support components have
constant rank and split simultaneously after one finite étale fpqc cover. -/
theorem exists_commonSplitChartAtSupport (d : ℕ)
    (z : (PermutationPower.power (Spec (.of K)) (Fin d) C).left)
    (c : Charts K C d z) (n : Neighborhoods K C d z c) :
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
        Flat q ∧ Surjective q ∧ QuasiCompact q ∧
          ∀ i, ∃ (m : ℕ)
            (_e : T ⊗[Γ(V, ⊤)] Γ(f i ⁻¹ᵁ V, ⊤) ≃ₐ[T] (Fin m → T)),
            ∃ E : pullback (fV i) q ≅ Spec (.of (Fin m → T)),
              E.hom ≫ EtaleSplitChart.splitProjection T m =
                pullback.snd (fV i) q ∧
              m = (f i).finrank (commonBasePoint K C d z c n) := by
  exact FiniteEtaleFamilyPointSplitChart.exists_affineOpen_fpqc_common_splitCover
    d (fun i ↦ (pulledComponentOverCommonBase K C d z c n i).left)
      (fun i ↦ (pulledComponentOverCommonBase K C d z c n i).hom)
        (commonBasePoint K C d z c n)

end MazurTorsion.AlgebraicGeometry.Jacobian.FiniteSupportEtaleCoordinates

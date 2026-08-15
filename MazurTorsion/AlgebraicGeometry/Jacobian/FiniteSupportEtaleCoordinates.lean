/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

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

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.FiniteSupportEtaleCoordinates

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

end MazurTorsion.AlgebraicGeometry.Jacobian.FiniteSupportEtaleCoordinates

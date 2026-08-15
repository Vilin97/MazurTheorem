/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.NoetherianCommonDenseAffineCover
import MazurTorsion.Upstream.CoherentCohomologyFinite.NoetherianReduction
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeAffineCoverData

/-!
# Relative affine covers with a common dense domain

For a Noetherian separated scheme, enlarge every member of a finite
affine cover by the componentwise construction.  We include one extra
member coming from the componentwise dense affine open itself; this
makes the indexing type nonempty even for the empty scheme.

The enlarged affine opens still form a finite cover, each contains the
same dense affine intersection, and the structural morphisms of their
canonical spectrum presentations remain of finite type over the fixed
affine base.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.Chow

open MazurTorsion.AlgebraicGeometry.CoherentCohomology

/-- The seed affine opens used to form a common-domain cover.  Existing
cover members are retained, and one componentwise dense affine open is
added to make the family canonically nonempty. -/
def commonDomainSeedOpen
    {X : Scheme.{u}} [IsNoetherian X]
    (D : NoetherianComponentAffineOpenData X)
    (c : AffineCoverData X) :
    Option c.ι → X.Opens
  | none => D.denseAffineOpen
  | some i => (c.f i).opensRange

/-- Every seed member is affine. -/
theorem isAffineOpen_commonDomainSeedOpen
    {X : Scheme.{u}} [IsNoetherian X]
    (D : NoetherianComponentAffineOpenData X)
    (c : AffineCoverData X)
    (i : Option c.ι) :
    IsAffineOpen (commonDomainSeedOpen D c i) := by
  cases i with
  | none =>
      exact D.isAffineOpen_denseAffineOpen
  | some i =>
      exact isAffineOpen_opensRange (c.f i)

/-- Enlarge each seed member by the affine opens in the components it
misses. -/
def commonDomainCoverOpen
    {X : Scheme.{u}} [IsNoetherian X]
    (D : NoetherianComponentAffineOpenData X)
    (c : AffineCoverData X)
    (i : Option c.ι) : X.Opens :=
  D.componentEnvelope (commonDomainSeedOpen D c i)

/-- Every enlarged cover member is affine. -/
theorem isAffineOpen_commonDomainCoverOpen
    {X : Scheme.{u}} [IsNoetherian X]
    (D : NoetherianComponentAffineOpenData X)
    (c : AffineCoverData X)
    (i : Option c.ι) :
    IsAffineOpen (commonDomainCoverOpen D c i) :=
  D.isAffineOpen_componentEnvelope
    (commonDomainSeedOpen D c i)
    (isAffineOpen_commonDomainSeedOpen D c i)

/-- The common dense affine open obtained by intersecting all enlarged
cover members. -/
def commonDomainOpen
    {X : Scheme.{u}} [IsNoetherian X]
    (D : NoetherianComponentAffineOpenData X)
    (c : AffineCoverData X) : X.Opens :=
  D.commonComponentEnvelope (commonDomainSeedOpen D c)

/-- On a separated scheme, the common domain is affine. -/
theorem isAffineOpen_commonDomainOpen
    {X : Scheme.{u}} [IsNoetherian X] [X.IsSeparated]
    (D : NoetherianComponentAffineOpenData X)
    (c : AffineCoverData X) :
    IsAffineOpen (commonDomainOpen D c) := by
  letI :
      IsAffineHom (pullback.diagonal (terminal.from X)) :=
    inferInstance
  exact
    D.isAffineOpen_commonComponentEnvelope
      (commonDomainSeedOpen D c)
      (isAffineOpen_commonDomainSeedOpen D c)

/-- The common domain is dense. -/
theorem dense_commonDomainOpen
    {X : Scheme.{u}} [IsNoetherian X]
    (D : NoetherianComponentAffineOpenData X)
    (c : AffineCoverData X) :
    Dense (commonDomainOpen D c : Set X) :=
  D.dense_commonComponentEnvelope
    (commonDomainSeedOpen D c)

/-- The common domain lies in every enlarged chart. -/
theorem commonDomainOpen_le_coverOpen
    {X : Scheme.{u}} [IsNoetherian X]
    (D : NoetherianComponentAffineOpenData X)
    (c : AffineCoverData X)
    (i : Option c.ι) :
    commonDomainOpen D c ≤ commonDomainCoverOpen D c i :=
  iInf_le _ i

/-- Canonical spectrum presentation of an enlarged affine chart,
followed by its inclusion in `X`. -/
def commonDomainCoverMap
    {X : Scheme.{u}} [IsNoetherian X]
    (D : NoetherianComponentAffineOpenData X)
    (c : AffineCoverData X)
    (i : Option c.ι) :
    Spec Γ((commonDomainCoverOpen D c i).toScheme, ⊤) ⟶ X :=
  by
    letI : IsAffine
        (commonDomainCoverOpen D c i).toScheme :=
      isAffineOpen_commonDomainCoverOpen D c i
    exact
      (commonDomainCoverOpen D c i).toScheme.isoSpec.inv ≫
        (commonDomainCoverOpen D c i).ι

instance isOpenImmersion_commonDomainCoverMap
    {X : Scheme.{u}} [IsNoetherian X]
    (D : NoetherianComponentAffineOpenData X)
    (c : AffineCoverData X)
    (i : Option c.ι) :
    IsOpenImmersion (commonDomainCoverMap D c i) :=
  by
    dsimp only [commonDomainCoverMap]
    infer_instance

/-- The range of the canonical spectrum presentation is the enlarged
cover open. -/
theorem opensRange_commonDomainCoverMap
    {X : Scheme.{u}} [IsNoetherian X]
    (D : NoetherianComponentAffineOpenData X)
    (c : AffineCoverData X)
    (i : Option c.ι) :
    (commonDomainCoverMap D c i).opensRange =
      commonDomainCoverOpen D c i := by
  letI : IsAffine
      (commonDomainCoverOpen D c i).toScheme :=
    isAffineOpen_commonDomainCoverOpen D c i
  change
    ((commonDomainCoverOpen D c i).toScheme.isoSpec.inv ≫
      (commonDomainCoverOpen D c i).ι).opensRange =
        commonDomainCoverOpen D c i
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact Scheme.Opens.opensRange_ι _

/-- The enlarged spectrum presentations still cover `X`. -/
theorem commonDomainCoverMap_covers
    {X : Scheme.{u}} [IsNoetherian X]
    (D : NoetherianComponentAffineOpenData X)
    (c : AffineCoverData X)
    (x : X) :
    ∃ i : Option c.ι,
      x ∈ Set.range (commonDomainCoverMap D c i).base := by
  obtain ⟨i, y, hy⟩ := c.covers x
  let V := (c.f i).opensRange
  have hyV :
      x ∈ V := by
    rw [← hy]
    exact ⟨y, rfl⟩
  have hxE :
      x ∈ commonDomainCoverOpen D c (some i) := by
    exact
      D.le_componentEnvelope V hyV
  letI : IsAffine
      (commonDomainCoverOpen D c (some i)).toScheme :=
    isAffineOpen_commonDomainCoverOpen D c (some i)
  let z :=
    (commonDomainCoverOpen D c (some i)).toScheme.isoSpec.hom.base
      ⟨x, hxE⟩
  refine ⟨some i, z, ?_⟩
  change
    (commonDomainCoverOpen D c (some i)).ι.base
      ((commonDomainCoverOpen D c (some i)).toScheme.isoSpec.inv.base z) =
      x
  have hpoint :
      (commonDomainCoverOpen D c (some i)).toScheme.isoSpec.inv.base
          ((commonDomainCoverOpen D c (some i)).toScheme.isoSpec.hom.base
            ⟨x, hxE⟩) =
        ⟨x, hxE⟩ := by
    exact congrArg
      (fun q => q.base ⟨x, hxE⟩)
      (commonDomainCoverOpen D c (some i)).toScheme.isoSpec.hom_inv_id
  exact congrArg
    (fun q => (commonDomainCoverOpen D c (some i)).ι.base q) hpoint

/-- A relative affine cover together with a specified common dense
affine open contained in every member. -/
structure CommonDenseRelativeAffineCoverData
    (k : Type u) [CommRing k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))
    extends RelativeAffineCoverData k f where
  nonempty_chartIndex :
    Nonempty toAffineCoverData.ι
  commonOpen : X.Opens
  isAffineOpen_commonOpen : IsAffineOpen commonOpen
  dense_commonOpen : Dense (commonOpen : Set X)
  commonOpen_le_chart :
    ∀ i : toAffineCoverData.ι,
      commonOpen ≤
        (toAffineCoverData.f i).opensRange

attribute [instance]
  CommonDenseRelativeAffineCoverData.nonempty_chartIndex

namespace CommonDenseRelativeAffineCoverData

variable
    {k : Type u} [CommRing k] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)}

/-- The common dense affine open as a scheme. -/
abbrev domain (c : CommonDenseRelativeAffineCoverData k f) :
    Scheme.{u} :=
  c.commonOpen.toScheme

/-- Its inclusion into the original scheme. -/
abbrev domainInclusion
    (c : CommonDenseRelativeAffineCoverData k f) :
    c.domain ⟶ X :=
  c.commonOpen.ι

instance (c : CommonDenseRelativeAffineCoverData k f) :
    IsAffine c.domain :=
  c.isAffineOpen_commonOpen

instance (c : CommonDenseRelativeAffineCoverData k f) :
    IsOpenImmersion c.domainInclusion :=
  inferInstance

/-- The common-domain inclusion has dense image. -/
theorem dense_range_domainInclusion
    (c : CommonDenseRelativeAffineCoverData k f) :
    Dense (Set.range c.domainInclusion.base) := by
  simpa [Scheme.Opens.range_ι] using c.dense_commonOpen

/-- The common-domain inclusion is quasi-compact on a locally
Noetherian scheme. -/
instance [IsLocallyNoetherian X]
    (c : CommonDenseRelativeAffineCoverData k f) :
    QuasiCompact c.domainInclusion :=
  inferInstance

end CommonDenseRelativeAffineCoverData

/-- Enlarge an arbitrary finite affine cover to a relative affine cover
whose members contain a common dense affine open. -/
def commonDenseRelativeAffineCoverData
    (k : Type u) [CommRing k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))
    [IsProper f] [IsNoetherian X] [X.IsSeparated]
    (D : NoetherianComponentAffineOpenData X)
    (c : AffineCoverData X) :
    CommonDenseRelativeAffineCoverData k f := by
  let R (i : Option c.ι) : CommRingCat.{u} :=
    Γ((commonDomainCoverOpen D c i).toScheme, ⊤)
  let g (i : Option c.ι) : Spec (R i) ⟶ X :=
    commonDomainCoverMap D c i
  let baseMap (i : Option c.ι) :
      CommRingCat.of k ⟶ R i :=
    Spec.preimage (g i ≫ f)
  refine
    {
      toAffineCoverData :=
        {
          ι := Option c.ι
          R := R
          f := g
          isOpenImmersion := fun i => inferInstance
          covers := commonDomainCoverMap_covers D c
          ambientRing := R
          embedding := fun i => 𝟙 (Spec (R i))
          isClosedImmersion := fun i => inferInstance
        }
      baseMap := baseMap
      finiteType_baseMap := ?_
      chart_toBase := ?_
      nonempty_chartIndex := inferInstance
      commonOpen := commonDomainOpen D c
      isAffineOpen_commonOpen :=
        isAffineOpen_commonDomainOpen D c
      dense_commonOpen := dense_commonDomainOpen D c
      commonOpen_le_chart := ?_
    }
  · intro i
    apply
      (HasRingHomProperty.Spec_iff
        (P := @LocallyOfFiniteType)).mp
    simpa [baseMap, g] using
      (inferInstance :
        LocallyOfFiniteType
          (commonDomainCoverMap D c i ≫ f))
  · intro i
    exact (Spec.map_preimage (g i ≫ f)).symm
  · intro i
    change
      commonDomainOpen D c ≤
        (commonDomainCoverMap D c i).opensRange
    rw [opensRange_commonDomainCoverMap]
    exact commonDomainOpen_le_coverOpen D c i

/-- Every scheme proper over a field admits a finite relative affine
cover whose members share a common dense affine open. -/
theorem exists_commonDenseRelativeAffineCoverData_of_proper
    (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f] :
    Nonempty (CommonDenseRelativeAffineCoverData k f) := by
  letI : IsNoetherian X :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.isNoetherian_of_isProper_to_field f
  letI : X.IsSeparated :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.schemeIsSeparated_of_isProper_to_field f
  obtain ⟨D⟩ :=
    NoetherianComponentAffineOpenData.exists_noetherianComponentAffineOpenData
      (X := X)
  obtain ⟨c⟩ :=
    exists_affineCoverData_of_proper f
  exact
    ⟨commonDenseRelativeAffineCoverData k f D c⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.Chow

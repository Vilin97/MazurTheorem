/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.CategoryTheory.Abelian.SerreClass.MorphismProperty
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.SupportedFppfLocalization

/-!
# The Serre class of fppf sheaves supported on a closed complement

Restriction of abelian fppf sheaves to an open subscheme preserves finite limits and finite
colimits.  Consequently the sheaves whose restriction is zero form a Serre class: support on the
closed complement is stable under subobjects, quotients, and extensions.

This gives the exact localization interface needed for Mazur's bad-level factors without making
an open-closed recollement or representability claim.  A morphism is an isomorphism modulo the
supported Serre class exactly when its open restriction is an isomorphism.  The actual
constant-flat and multiplicative-flat point-sheaf inclusions are compiled consumers.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.CommGroupScheme

universe u

variable {S : Scheme.{u}}

section SupportedSerre

variable (U : S.Opens)

/-- Fppf sheaves supported on the closed complement of `U` form a Serre class.  This is a
formal consequence of exact open restriction, not a recollement assertion. -/
noncomputable instance fppfSheafSupportedOnClosedComplementProperty_isSerreClass :
    (fppfSheafSupportedOnClosedComplementProperty U).IsSerreClass := by
  change (ObjectProperty.inverseImage
    (IsZero (C := Sheaf (Scheme.fppfTopology.over U.toScheme)
      AddCommGrpCat.{u + 1}))
    (Scheme.fppfTopology.overMapPullback AddCommGrpCat.{u + 1} U.ι)).IsSerreClass
  infer_instance

/-- An extension of two fppf sheaves supported on the closed complement remains supported. -/
theorem fppfSheafSupportedOnClosedComplement_of_shortExact
    {T : ShortComplex
      (Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1})}
    (hT : T.ShortExact)
    (h₁ : fppfSheafSupportedOnClosedComplementProperty U T.X₁)
    (h₃ : fppfSheafSupportedOnClosedComplementProperty U T.X₃) :
    fppfSheafSupportedOnClosedComplementProperty U T.X₂ :=
  (fppfSheafSupportedOnClosedComplementProperty U).prop_X₂_of_shortExact hT h₁ h₃

/-- Restriction to `U` inverts every morphism whose kernel and cokernel are supported on the
closed complement. -/
theorem fppfOverOpenRestriction_inverts_isoModSupported :
    (fppfSheafSupportedOnClosedComplementProperty U).isoModSerre.IsInvertedBy
      (Scheme.fppfTopology.overMapPullback AddCommGrpCat.{u + 1} U.ι) := by
  apply ((fppfSheafSupportedOnClosedComplementProperty U).isoModSerre_isInvertedBy_iff _).2
  intro F hF
  exact hF

/-- Exact open restriction detects precisely the isomorphisms modulo the supported Serre class.
Equivalently, a map restricts to an isomorphism iff both its kernel and cokernel vanish on `U`. -/
theorem isoModSupported_iff_openRestriction_isIso
    {F G : Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}}
    (f : F ⟶ G) :
    (fppfSheafSupportedOnClosedComplementProperty U).isoModSerre f ↔
      IsIso ((Scheme.fppfTopology.overMapPullback
        AddCommGrpCat.{u + 1} U.ι).map f) := by
  let R := Scheme.fppfTopology.overMapPullback AddCommGrpCat.{u + 1} U.ι
  constructor
  · intro hf
    exact fppfOverOpenRestriction_inverts_isoModSupported U f hf
  · intro hf
    letI : IsIso (R.map f) := hf
    rw [(fppfSheafSupportedOnClosedComplementProperty U).isoModSerre_iff]
    constructor
    · change IsZero (R.obj (kernel f))
      exact (isZero_kernel_of_mono (R.map f)).of_iso
        (PreservesKernel.iso R f)
    · change IsZero (R.obj (cokernel f))
      exact (isZero_cokernel_of_epi (R.map f)).of_iso
        (PreservesCokernel.iso R f)

end SupportedSerre

end AlgebraicGeometry.CommGroupScheme

namespace AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme

universe u

open CommGroupScheme

/-! ### Mazur's two bad-level consumers -/

section ConstantFlat

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]

/-- The constant-flat inclusion is an isomorphism modulo fppf sheaves supported on the level
closed fibre. -/
theorem constantFlatAddPointFppfMap_isoModSupported (level : R) :
    (fppfSheafSupportedOnClosedComplementProperty (levelOpen level)).isoModSerre
      (addPointFppfMap (constantFlatInclusion (G := G) level)) := by
  apply (isoModSupported_iff_openRestriction_isIso (levelOpen level) _).2
  exact constantFlatAddPointFppfMapAway_isIso (G := G) level

end ConstantFlat

section MultiplicativeFlat

variable {coeffPrime level : ℕ} [NeZero coeffPrime]

/-- The multiplicative-flat inclusion is an isomorphism modulo fppf sheaves supported on the
level closed fibre. -/
theorem muFlatAddPointFppfMap_isoModSupported
    (datum : MuFlatDatum coeffPrime level) :
    (fppfSheafSupportedOnClosedComplementProperty
      (levelOpen (level : ℤ))).isoModSerre
        (addPointFppfMap (muFlatInclusion coeffPrime level datum)) := by
  apply (isoModSupported_iff_openRestriction_isIso
    (levelOpen (level : ℤ)) _).2
  exact muFlatAddPointFppfMapAway_isIso datum

end MultiplicativeFlat

end AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme

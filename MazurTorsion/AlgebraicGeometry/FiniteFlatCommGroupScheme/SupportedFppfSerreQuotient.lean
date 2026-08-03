/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.CategoryTheory.Abelian.SerreClass.Localization
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.SupportedFppfSerre

/-!
# The Serre quotient by bad-fibre-supported fppf sheaves

For an open subscheme `U` of a base scheme `S`, this file forms the categorical localization of
abelian fppf sheaves on `S` at morphisms whose kernel and cokernel are supported on `S ∖ U`.
Mathlib's localization of an abelian category at a Serre class supplies an abelian quotient.

The quotient functor detects exactly the same isomorphisms as restriction to `U`.  The actual
constant-flat and multiplicative-flat bad-level inclusions are checked consumers.  No equivalence
with the category of sheaves on `U`, recollement, or cohomological localization sequence is claimed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.CommGroupScheme

universe u

variable {S : Scheme.{u}} {G H : CommGroupScheme S}

/-- The abstract Serre quotient of abelian fppf sheaves by sheaves supported on the closed
complement of `U`. -/
abbrev fppfSheafSupportedQuotient (U : S.Opens) :=
  (fppfSheafSupportedOnClosedComplementProperty U).isoModSerre.Localization

/-- The canonical functor to the Serre quotient by bad-fibre-supported sheaves. -/
noncomputable abbrev fppfSheafSupportedQuotientFunctor (U : S.Opens) :=
  (fppfSheafSupportedOnClosedComplementProperty U).isoModSerre.Q

/-- The quotient by closed-complement-supported fppf sheaves is an abelian category. -/
noncomputable instance fppfSheafSupportedQuotient_abelian (U : S.Opens) :
    Abelian (fppfSheafSupportedQuotient U) :=
  ObjectProperty.SerreClassLocalization.abelian
    (fppfSheafSupportedQuotientFunctor U)
    (fppfSheafSupportedOnClosedComplementProperty U)

/-- The canonical Serre quotient functor preserves finite limits. -/
noncomputable instance fppfSheafSupportedQuotientFunctor_preservesFiniteLimits
    (U : S.Opens) :
    PreservesFiniteLimits (fppfSheafSupportedQuotientFunctor U) :=
  ObjectProperty.SerreClassLocalization.preservesFiniteLimits
    (fppfSheafSupportedQuotientFunctor U)
    (fppfSheafSupportedOnClosedComplementProperty U)

/-- The canonical Serre quotient functor preserves finite colimits. -/
noncomputable instance fppfSheafSupportedQuotientFunctor_preservesFiniteColimits
    (U : S.Opens) :
    PreservesFiniteColimits (fppfSheafSupportedQuotientFunctor U) :=
  ObjectProperty.SerreClassLocalization.preservesFiniteColimits
    (fppfSheafSupportedQuotientFunctor U)
    (fppfSheafSupportedOnClosedComplementProperty U)

/-- The canonical functor to the supported Serre quotient, bundled as an exact functor. -/
noncomputable def fppfSheafSupportedQuotientExactFunctor (U : S.Opens) :
    Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1} ⥤ₑ
      fppfSheafSupportedQuotient U :=
  ExactFunctor.of (fppfSheafSupportedQuotientFunctor U)

/-- A morphism becomes an isomorphism in the supported Serre quotient exactly when its
restriction to the complementary open is an isomorphism. -/
theorem fppfSheafSupportedQuotientFunctor_map_isIso_iff_openRestriction_isIso
    (U : S.Opens)
    {F G : Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}}
    (f : F ⟶ G) :
    IsIso ((fppfSheafSupportedQuotientFunctor U).map f) ↔
      IsIso ((Scheme.fppfTopology.overMapPullback
        AddCommGrpCat.{u + 1} U.ι).map f) := by
  rw [ObjectProperty.SerreClassLocalization.isIso_map_iff
      (fppfSheafSupportedQuotientFunctor U)
      (fppfSheafSupportedOnClosedComplementProperty U),
    isoModSupported_iff_openRestriction_isIso]

/-- The represented-point cokernel sequence after passage to the supported Serre quotient. -/
noncomputable def pointCokernelFppfSequenceSupportedQuotient
    (f : G ⟶ H) (U : S.Opens) :
    ShortComplex (fppfSheafSupportedQuotient U) :=
  (pointCokernelFppfSequence f).map (fppfSheafSupportedQuotientFunctor U)

/-- A monic represented-point cokernel sequence remains short exact in the supported Serre
quotient. -/
theorem pointCokernelFppfSequenceSupportedQuotient_shortExact_of_mono
    (f : G ⟶ H) [Mono f.hom.hom.hom.left] (U : S.Opens) :
    (pointCokernelFppfSequenceSupportedQuotient f U).ShortExact :=
  (pointCokernelFppfSequence_shortExact_of_mono f).map_of_exact _

/-- A point-cokernel sheaf supported on the closed complement becomes zero in the supported
Serre quotient. -/
theorem pointCokernelFppfSequenceSupportedQuotient_X₃_isZero
    (f : G ⟶ H) (U : S.Opens)
    (h : fppfSheafSupportedOnClosedComplementProperty U
      (pointCokernelFppfSheaf f)) :
    IsZero (pointCokernelFppfSequenceSupportedQuotient f U).X₃ := by
  change IsZero ((fppfSheafSupportedQuotientFunctor U).obj
    (pointCokernelFppfSheaf f))
  exact (ObjectProperty.SerreClassLocalization.isZero_obj_iff
    (fppfSheafSupportedQuotientFunctor U)
    (fppfSheafSupportedOnClosedComplementProperty U) _).2 h

/-- For a monic represented group-scheme map with supported cokernel, the point-sheaf map becomes
an isomorphism in the supported Serre quotient. -/
theorem addPointFppfMap_supportedQuotient_isIso_of_supported
    (f : G ⟶ H) [Mono f.hom.hom.hom.left] (U : S.Opens)
    (h : fppfSheafSupportedOnClosedComplementProperty U
      (pointCokernelFppfSheaf f)) :
    IsIso ((fppfSheafSupportedQuotientFunctor U).map (addPointFppfMap f)) := by
  change IsIso (pointCokernelFppfSequenceSupportedQuotient f U).f
  rw [(pointCokernelFppfSequenceSupportedQuotient_shortExact_of_mono f U).isIso_f_iff]
  exact pointCokernelFppfSequenceSupportedQuotient_X₃_isZero f U h

end AlgebraicGeometry.CommGroupScheme

namespace AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme

universe u

open CommGroupScheme

section ConstantFlat

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]

/-- The actual constant-flat bad-level inclusion becomes an isomorphism in the supported Serre
quotient. -/
theorem constantFlatAddPointFppfMap_supportedQuotient_isIso (level : R) :
    IsIso ((fppfSheafSupportedQuotientFunctor (levelOpen level)).map
      (addPointFppfMap (constantFlatInclusion (G := G) level))) := by
  exact addPointFppfMap_supportedQuotient_isIso_of_supported
    (constantFlatInclusion (G := G) level) (levelOpen level)
    (constantFlatPointCokernelFppfSheafAway_isZero (G := G) level)

end ConstantFlat

section MultiplicativeFlat

variable {coeffPrime level : ℕ} [NeZero coeffPrime]

/-- The actual multiplicative-flat bad-level inclusion becomes an isomorphism in the supported
Serre quotient. -/
theorem muFlatAddPointFppfMap_supportedQuotient_isIso
    (datum : MuFlatDatum coeffPrime level) :
    IsIso ((fppfSheafSupportedQuotientFunctor (levelOpen (level : ℤ))).map
      (addPointFppfMap (muFlatInclusion coeffPrime level datum))) := by
  exact addPointFppfMap_supportedQuotient_isIso_of_supported
    (muFlatInclusion coeffPrime level datum) (levelOpen (level : ℤ))
    (muFlatPointCokernelFppfSheafAway_isZero datum)

end MultiplicativeFlat

end AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme

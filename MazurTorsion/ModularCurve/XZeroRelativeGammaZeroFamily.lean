/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/

import MazurTorsion.ModularCurve.XZeroSplitGammaZeroObject
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Relative locally constant `Gamma_0(N)` families

This module starts the arbitrary-base moduli layer needed before one can state
representability of the open modular curve.  It constructs the constant cyclic
finite-flat group over an arbitrary scheme, defines finite-flat subgroups which
become that group on an fppf cover, and bundles such a subgroup with a proper,
geometrically integral, smooth relative curve of dimension one.

The boundary is deliberately narrower than the full Deligne--Rapoport moduli
problem.  `LocallyConstantCyclicSubgroup` describes the finite-etale locus; it
does not encode generalized cyclic subgroups in characteristics dividing the
level.  This is the locus needed over `Q` and at the auxiliary residue
characteristics used by the current Mazur argument, where the levels are
prime to the residue characteristic.

No pullback functor, isomorphism quotient, representing scheme, compactification,
or point of `X_0(N)` is asserted here.  The named downstream consumer is
`MazurTorsion.XZeroFortyNine.locallyConstantGammaZeroFamilyOfOrderFortyNineTorsion`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry
open TauCeti.AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroModuli

open XZeroFiniteFlatModuli

universe u

variable (S : Scheme.{u}) (N : ℕ) [NeZero N]

/-- The constant cyclic finite-flat group of order `N` over an arbitrary base
scheme.  It is obtained from its universal model over the universe-compatible
copy of `Spec Z`. -/
abbrev constantCyclicOver : FiniteFlatCommGroupScheme S :=
  (FiniteFlatCommGroupScheme.baseChange (specULiftZIsTerminal.from S)).obj
    (cyclicConstant (ULift.{u} ℤ) N)

/-- The arbitrary-base constant cyclic group has geometric order `N`. -/
theorem constantCyclicOver_hasConstantOrder :
    (constantCyclicOver S N).HasConstantOrder N :=
  FiniteFlatCommGroupScheme.hasConstantOrder_baseChange
    (cyclicConstant_hasConstantOrder (ULift.{u} ℤ) N)
      (specULiftZIsTerminal.from S)

/-- Pulling a finite-flat commutative group scheme back along the identity
recovers it canonically. -/
noncomputable def finiteFlatBaseChangeIdIso
    (G : FiniteFlatCommGroupScheme S) :
    (FiniteFlatCommGroupScheme.baseChange (𝟙 S)).obj G ≅ G :=
  ObjectProperty.isoMk (finiteFlatCommGroupSchemeProperty S)
    ((Functor.mapCommGrpNatIso Over.pullbackId).app G.obj ≪≫
      Functor.mapCommGrpIdIso.app G.obj)

/-- The singleton identity fppf cover. -/
def identityFppfCover : Scheme.Cover.{u} Scheme.fppfPrecoverage S :=
  Precoverage.ZeroHypercover.singleton (𝟙 S) (by
    exact Scheme.Hom.singleton_mem_fppfPrecoverage (𝟙 S))

/-- A finite-flat closed subgroup which is cyclic and constant on an fppf
cover.

The local isomorphisms do not choose generators, so this is `Gamma_0(N)` data
rather than `Gamma_1(N)` data.  The condition isolates the locally constant
(finite-etale) locus and intentionally excludes the extra generalized
cyclicity geometry required at bad characteristics. -/
structure LocallyConstantCyclicSubgroup
    (E : CommGroupScheme S) extends FiniteLocallyFreeSubgroup E where
  /-- An fppf cover on which the carrier is constant cyclic. -/
  trivializingCover : Scheme.Cover.{u} Scheme.fppfPrecoverage S
  /-- A local cyclic trivialization, without a chosen generator. -/
  localTrivialization (i : trivializingCover.I₀) : Nonempty
    ((FiniteFlatCommGroupScheme.baseChange (trivializingCover.f i)).obj
        toFiniteLocallyFreeSubgroup.carrier ≅
      constantCyclicOver (trivializingCover.X i) N)

namespace LocallyConstantCyclicSubgroup

variable {S N} {E : CommGroupScheme S}

/-- A globally constant cyclic subgroup is fppf-locally constant, witnessed
by the identity cover. -/
noncomputable def ofGlobalTrivialization
    (C : FiniteLocallyFreeSubgroup E)
    (e : Nonempty (C.carrier ≅ constantCyclicOver S N)) :
    LocallyConstantCyclicSubgroup S N E where
  toFiniteLocallyFreeSubgroup := C
  trivializingCover := identityFppfCover S
  localTrivialization _ := by
    obtain ⟨e⟩ := e
    exact ⟨finiteFlatBaseChangeIdIso S C.carrier ≪≫ e⟩

/-- Fppf-local cyclicity forces the global finite-flat carrier to have
constant geometric order `N`. -/
theorem hasConstantOrder (C : LocallyConstantCyclicSubgroup S N E) :
    C.carrier.HasConstantOrder N := by
  letI : Scheme.JointlySurjective Scheme.fppfPrecoverage := by
    change Scheme.JointlySurjective
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation))
    infer_instance
  funext s
  obtain ⟨i, t, ht⟩ := C.trivializingCover.exists_eq s
  obtain ⟨e⟩ := C.localTrivialization i
  calc
    C.carrier.orderAt s =
        C.carrier.orderAt (C.trivializingCover.f i t) := by rw [ht]
    _ = ((FiniteFlatCommGroupScheme.baseChange
          (C.trivializingCover.f i)).obj C.carrier).orderAt t :=
      (FiniteFlatCommGroupScheme.orderAt_baseChange
        (C.trivializingCover.f i) C.carrier t).symm
    _ = (constantCyclicOver (C.trivializingCover.X i) N).orderAt t :=
      congrFun (FiniteFlatCommGroupScheme.orderAt_eq_of_iso e) t
    _ = N := congrFun
      (constantCyclicOver_hasConstantOrder (C.trivializingCover.X i) N) t

end LocallyConstantCyclicSubgroup

/-- Over an affine base, the arbitrary-base constant object agrees with the
usual named constant cyclic group scheme. -/
noncomputable def constantCyclicOverSpecIso
    (K : Type u) [CommRing K] [Nontrivial K] :
    constantCyclicOver (Spec (.of K)) N ≅ cyclicConstant K N := by
  letI : Algebra (ULift.{u} ℤ) K := ULift.algebra' ℤ K
  have hmap : specULiftZIsTerminal.from (Spec (.of K)) =
      Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) K)) :=
    specULiftZIsTerminal.hom_ext _ _
  rw [constantCyclicOver, hmap]
  exact FiniteFlatCommGroupScheme.constantBaseChangeIso
    (R := ULift.{u} ℤ) (K := K) (CyclicIndex.{u} N)

/-- A split cyclic subgroup over a field supplies the identity-cover instance
of a locally constant cyclic subgroup. -/
noncomputable def LocallyConstantCyclicSubgroup.ofSplit
    (K : Type u) [Field K]
    {E : CommGroupScheme (Spec (.of K))}
    (C : SplitCyclicSubgroup E (N := N)) :
    LocallyConstantCyclicSubgroup (Spec (.of K)) N E :=
  LocallyConstantCyclicSubgroup.ofGlobalTrivialization
    C.toFiniteLocallyFreeSubgroup (by
      obtain ⟨e⟩ := C.isSplit
      exact ⟨e ≪≫ (constantCyclicOverSpecIso N K).symm⟩)

/-- A relative elliptic curve with fppf-locally constant `Gamma_0(N)`
structure.  This is a family-level moduli object, not a represented modular
curve. -/
structure LocallyConstantGammaZeroFamily (S : Scheme.{u})
    (N : ℕ) [NeZero N] where
  /-- The ambient relative commutative group scheme. -/
  curve : CommGroupScheme S
  /-- Properness of the relative curve. -/
  isProper : IsProper curve.X.hom
  /-- Geometric integrality of the relative curve. -/
  geometricallyIntegral : GeometricallyIntegral curve.X.hom
  /-- Smooth relative dimension one. -/
  smoothOfRelativeDimensionOne : SmoothOfRelativeDimension 1 curve.X.hom
  /-- The fppf-locally constant cyclic subgroup. -/
  subgroup : LocallyConstantCyclicSubgroup S N curve

namespace LocallyConstantGammaZeroFamily

variable {S N}

attribute [instance] LocallyConstantGammaZeroFamily.isProper
  LocallyConstantGammaZeroFamily.geometricallyIntegral
  LocallyConstantGammaZeroFamily.smoothOfRelativeDimensionOne

/-- The existing split field-valued datum is the field fiber of the relative
locally constant moduli problem. -/
noncomputable def ofSplitGeometricDatum
    (K : Type u) [Field K] (D : SplitGeometricDatum K N) :
    LocallyConstantGammaZeroFamily (Spec (.of K)) N where
  curve := D.curve
  isProper := D.isProper
  geometricallyIntegral := D.geometricallyIntegral
  smoothOfRelativeDimensionOne := D.smoothOfRelativeDimensionOne
  subgroup := LocallyConstantCyclicSubgroup.ofSplit N K D.subgroup

@[simp]
theorem ofSplitGeometricDatum_curve
    (K : Type u) [Field K] (D : SplitGeometricDatum K N) :
    (ofSplitGeometricDatum K D).curve = D.curve :=
  rfl

@[simp]
theorem ofSplitGeometricDatum_subgroup_carrier
    (K : Type u) [Field K] (D : SplitGeometricDatum K N) :
    (ofSplitGeometricDatum K D).subgroup.carrier = D.subgroup.carrier :=
  rfl

end LocallyConstantGammaZeroFamily

end MazurTorsion.ModularCurve.XZeroModuli

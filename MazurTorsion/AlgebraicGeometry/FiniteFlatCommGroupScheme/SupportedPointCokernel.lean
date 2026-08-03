/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Whiskering
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.ConstantFlat
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.MultiplicativeFlat

/-!
# Pointwise cokernels preceding the bad-fibre supported quotient sheaves

Mazur's two bad-level localization sequences have quotient terms supported on the bad fibre.
Those terms are fppf sheaves, not quasi-finite flat group schemes.  This file constructs the
honest presheaf precursor: the pointwise additive cokernel of an ambient commutative
group-scheme morphism.  Its projection is objectwise surjective and its defining sequence is
categorically exact.

The file deliberately makes no sheaf or support claim.  The next layer must sheafify this
presheaf, prove local surjectivity of the resulting projection, and use the checked principal-open
range theorems to prove that the sheaf vanishes over `D(level)`.  The constant-flat and
multiplicative-flat inclusions below are concrete consumers which ensure that this precursor has
the exact coefficient maps needed by that layer.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.CommGroupScheme

universe u

variable {S : Scheme.{u}} {G H K : CommGroupScheme S}

/-- The represented point presheaf written additively.  Passing through the standard
commutative-group/additive-commutative-group equivalence lets us form categorical cokernels
without changing any point sets. -/
noncomputable abbrev addPointPresheaf (G : CommGroupScheme S) :
    (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  G.commPointPresheaf ⋙ commGroupAddCommGroupEquivalence.functor

/-- The natural transformation on additive point presheaves induced by a group-scheme map. -/
noncomputable def addPointPresheafMap (f : G ⟶ H) :
    addPointPresheaf G ⟶ addPointPresheaf H :=
  Functor.whiskerRight (commPointPresheafMap f)
    commGroupAddCommGroupEquivalence.functor

@[simp]
theorem addPointPresheafMap_id (G : CommGroupScheme S) :
    addPointPresheafMap (CategoryStruct.id G) = CategoryStruct.id (addPointPresheaf G) := by
  rw [addPointPresheafMap, commPointPresheafMap_id]
  exact Functor.whiskerRight_id' commGroupAddCommGroupEquivalence.functor

theorem addPointPresheafMap_comp (f : G ⟶ H) (g : H ⟶ K) :
    addPointPresheafMap (f ≫ g) = addPointPresheafMap f ≫ addPointPresheafMap g := by
  rw [addPointPresheafMap, commPointPresheafMap_comp]
  exact Functor.whiskerRight_comp _ _ commGroupAddCommGroupEquivalence.functor

/-- The pointwise additive cokernel presheaf of an ambient group-scheme map.  This is the input
to, not a replacement for, the eventual fppf supported-quotient sheaf. -/
noncomputable abbrev pointCokernelPresheaf (f : G ⟶ H) :
    (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  cokernel (addPointPresheafMap f)

/-- The canonical projection to the pointwise cokernel presheaf. -/
noncomputable abbrev pointCokernelProjection (f : G ⟶ H) :
    addPointPresheaf H ⟶ pointCokernelPresheaf f :=
  cokernel.π (addPointPresheafMap f)

/-- Before sheafification, the cokernel projection is already surjective on every test scheme. -/
theorem pointCokernelProjection_app_surjective (f : G ⟶ H) (T : (Over S)ᵒᵖ) :
    Function.Surjective ((pointCokernelProjection f).app T) := by
  rw [← AddCommGrpCat.epi_iff_surjective]
  exact (NatTrans.epi_iff_epi_app (pointCokernelProjection f)).mp (by infer_instance) T

/-- The exact presheaf sequence consisting of the point map and its categorical cokernel. -/
noncomputable def pointCokernelSequence (f : G ⟶ H) :
    ShortComplex ((Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  ShortComplex.mk (addPointPresheafMap f) (pointCokernelProjection f)
    (cokernel.condition _)

/-- The pointwise cokernel sequence is exact by its actual categorical construction. -/
theorem pointCokernelSequence_exact (f : G ⟶ H) :
    (pointCokernelSequence f).Exact :=
  ShortComplex.exact_cokernel _

end AlgebraicGeometry.CommGroupScheme

namespace AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme

universe u

open CommGroupScheme

section ConstantFlat

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]

/-- The actual point-cokernel presheaf attached to the constant-flat open subgroup. -/
noncomputable abbrev constantFlatPointCokernelPresheaf (level : R) :=
  pointCokernelPresheaf (constantFlatInclusion (G := G) level)

/-- The concrete constant-flat cokernel projection is surjective on every test scheme. -/
theorem constantFlatPointCokernelProjection_app_surjective (level : R)
    (T : (Over (Spec (.of R)))ᵒᵖ) :
    Function.Surjective
      ((pointCokernelProjection (constantFlatInclusion (G := G) level)).app T) :=
  pointCokernelProjection_app_surjective _ _

/-- The constant-flat inclusion supplies a concrete exact point-cokernel sequence. -/
theorem constantFlatPointCokernelSequence_exact (level : R) :
    (pointCokernelSequence (constantFlatInclusion (G := G) level)).Exact :=
  pointCokernelSequence_exact _

end ConstantFlat

section MultiplicativeFlat

variable {coeffPrime level : ℕ} [NeZero coeffPrime]

/-- The actual point-cokernel presheaf attached to the multiplicative-flat open subgroup. -/
noncomputable abbrev muFlatPointCokernelPresheaf
    (datum : MuFlatDatum coeffPrime level) :=
  pointCokernelPresheaf (muFlatInclusion coeffPrime level datum)

/-- The concrete multiplicative-flat cokernel projection is surjective on every test scheme. -/
theorem muFlatPointCokernelProjection_app_surjective
    (datum : MuFlatDatum coeffPrime level) (T : (Over (Spec (.of ℤ)))ᵒᵖ) :
    Function.Surjective
      ((pointCokernelProjection (muFlatInclusion coeffPrime level datum)).app T) :=
  pointCokernelProjection_app_surjective _ _

/-- The multiplicative-flat inclusion supplies the second concrete exact point-cokernel
sequence required before constructing Mazur's supported quotient sheaf. -/
theorem muFlatPointCokernelSequence_exact (datum : MuFlatDatum coeffPrime level) :
    (pointCokernelSequence (muFlatInclusion coeffPrime level datum)).Exact :=
  pointCokernelSequence_exact _

end MultiplicativeFlat

end AlgebraicGeometry.QuasiFiniteFlatCommGroupScheme

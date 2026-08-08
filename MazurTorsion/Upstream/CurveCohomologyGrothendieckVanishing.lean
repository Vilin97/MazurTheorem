/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.LeanPool.GrothendieckVanishing.GrothendieckVanishing
import MazurTorsion.Upstream.SchemeModuleCohomologyHZero
import TauCeti.AlgebraicGeometry.Dimension
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.ProductFormula.Smooth

/-!
# Grothendieck vanishing for smooth proper curves

This file consumes the LeanPool port of Grothendieck's vanishing theorem for
the underlying additive sheaf of an actual scheme module.  Tau Ceti's
codimension-one theorem for a smooth relative curve supplies the dimension
bound, while properness supplies quasi-compactness and hence the Noetherian
hypothesis.

No coherence or finite-dimensionality assertion is made here: the conclusion
is precisely vanishing of Zariski sheaf cohomology in degrees at least two.
-/

noncomputable section

universe u

open CategoryTheory Order TopologicalSpace
open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.SchemeWeilDivisor
open scoped AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry

/-- A smooth integral relative curve over a field has topological Krull
dimension at most one. -/
theorem topologicalKrullDim_le_one_of_smoothRelativeDimension_one
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f] :
    topologicalKrullDim X ≤ 1 := by
  letI : PartialOrder X := specializationOrder X
  letI : OrderTop X :=
    { top := genericPoint X
      le_top a := genericPoint_specializes a }
  rw [topologicalKrullDim_eq_iSup_coheight]
  refine iSup_le fun x ↦ ?_
  by_cases hx : x = genericPoint X
  · subst x
    change (Order.coheight (⊤ : X) : WithBot ℕ∞) ≤ 1
    simp
  · rw [coheight_eq_one_of_ne_genericPoint_of_smoothRelativeDimension_one
      K X f x hx]
    norm_num

/-- A proper smooth relative curve over a field is a Noetherian scheme. -/
theorem isNoetherian_of_proper_smoothRelativeDimension_one
    (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f] :
    IsNoetherian X := by
  letI : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  letI : LocallyOfFiniteType f := inferInstance
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : QuasiCompact f := inferInstance
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  exact _root_.AlgebraicGeometry.IsNoetherian.mk

namespace SchemeModuleCohomology

/-- The Zariski cohomology of the underlying additive sheaf of a module on a
smooth proper integral curve vanishes in every degree at least two.  This is
the concrete scheme-module consumer of `GrothendieckVanishing`. -/
theorem smoothProperCurve_H_subsingleton
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (M : X.Modules) (n : ℕ) (hn : 2 ≤ n) :
    Subsingleton (H M n) := by
  letI : IsNoetherian X :=
    isNoetherian_of_proper_smoothRelativeDimension_one K X f
  letI : NoetherianSpace X := inferInstance
  change Subsingleton
    (CategoryTheory.Sheaf.H
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n)
  apply GrothendieckVanishing X n
  refine lt_of_le_of_lt
    (topologicalKrullDim_le_one_of_smoothRelativeDimension_one K X f) ?_
  exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hn)

/-- Elementwise form of proper-curve vanishing above degree one. -/
theorem smoothProperCurve_H_eq_zero
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (M : X.Modules) (n : ℕ) (hn : 2 ≤ n) (x : H M n) :
    x = 0 := by
  letI : Subsingleton (H M n) :=
    smoothProperCurve_H_subsingleton K X f M n hn
  exact Subsingleton.elim _ _

end SchemeModuleCohomology
end MazurTorsion.AlgebraicGeometry

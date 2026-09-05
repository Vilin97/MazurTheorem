/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Upstream.ProperCurveFiniteSupportCech
import MazurTorsion.Upstream.SchemeModuleProperBaseChange

/-!
# Pointed proper-curve cohomology facade

This file packages the checked cohomological inputs for a coherent module on a pointed smooth
proper integral curve.  The facade contains finite-dimensional canonical `H⁰` and `H¹`,
vanishing above degree one, and cover-independent `H⁰`/`H¹` base change along field extensions.

The design boundary is the absolute, pointed curve needed by later Riemann--Roch and Picard
consumers.  It does not assert general proper-flat base change, semicontinuity, or
representability.  The named constructor and downstream entry point is
`PointedProperCurveCohomology.ofRationalSection`.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules

namespace MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

/-- The complete checked low-degree cohomology package for a coherent module on a pointed smooth
proper integral curve. -/
structure PointedProperCurveCohomology
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (s : SmoothCurveRationalSection K X f)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] where
  zeroFiniteDimensional :
    letI := hZeroCanonicalFieldModule K X f M
    FiniteDimensional K (H M 0)
  oneFiniteDimensional :
    letI := hOneCanonicalFieldModule K X f M
    FiniteDimensional K (H M 1)
  higherSubsingleton : ∀ n : ℕ, 2 ≤ n → Subsingleton (H M n)
  fieldExtensionLowDegreeBaseChange
      (L : Type u) [Field L] {P : Scheme.{u}}
      (fst : P ⟶ X) (snd : P ⟶ Spec (.of L))
      (g : Spec (.of L) ⟶ Spec (.of K))
      (h : IsPullback fst snd f g) :
      let N := (Scheme.Modules.pullback fst).obj M
      letI := baseSectionsHZeroModule f M
      letI := baseSectionsHZeroModule snd N
      let sourceZero := ModuleCat.of Γ(Spec (.of K), ⊤) (H M 0)
      let targetZero := ModuleCat.of Γ(Spec (.of L), ⊤) (H N 0)
      letI := baseSectionsHOneModule f M
      letI := baseSectionsHOneModule snd N
      let sourceOne := ModuleCat.of Γ(Spec (.of K), ⊤) (H M 1)
      let targetOne := ModuleCat.of Γ(Spec (.of L), ⊤) (H N 1)
      LowDegreeBaseChangeData g.appTop.hom
        sourceZero sourceOne targetZero targetOne

namespace PointedProperCurveCohomology

/-- Assemble the pointed proper-curve facade from the unconditional coherent `H⁰` theorem, the
finite-map proof of coherent `H¹` finiteness, Grothendieck vanishing, and canonical-cover base
change. -/
noncomputable def ofRationalSection
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (s : SmoothCurveRationalSection K X f)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    PointedProperCurveCohomology K X f s M where
  zeroFiniteDimensional :=
    hZeroCanonical_finiteDimensional_of_coherent K X f s M
  oneFiniteDimensional :=
    genuineSheafHOneCanonical_finiteDimensional_of_rationalSection
      K X f s M
  higherSubsingleton := fun n hn ↦
    smoothProperCurve_H_subsingleton K X f M n hn
  fieldExtensionLowDegreeBaseChange := by
    intro L _ P fst snd g h
    exact properCurveFieldExtensionLowDegreeBaseChange
      K L fst snd f g h M

/-- Elementwise higher-cohomology vanishing exposed directly from the packaged facade. -/
theorem higher_eq_zero
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    {f : X ⟶ Spec (.of K)} [IsProper f] [SmoothOfRelativeDimension 1 f]
    {s : SmoothCurveRationalSection K X f}
    {M : X.Modules} [M.IsQuasicoherent] [M.IsFiniteType]
    (D : PointedProperCurveCohomology K X f s M)
    (n : ℕ) (hn : 2 ≤ n) (x : H M n) : x = 0 := by
  letI : Subsingleton (H M n) := D.higherSubsingleton n hn
  exact Subsingleton.elim _ _

end PointedProperCurveCohomology
end MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

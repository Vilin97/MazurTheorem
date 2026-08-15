/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.SplitSymmetricQuotientChart
import MazurTorsion.AlgebraicGeometry.Jacobian.AffineLineMonicCoordinates

/-!
# Monic polynomials on a split quotient component

The residual-stabilizer quotient chart and the sheetwise universal root
family use the same monic coordinates.  After including invariant functions
into ordered-root coordinates, each sheet's universal monic polynomial is
the product of its ordered linear root factors.

The named downstream consumer is the split ordered-incidence comparison in
`PointedIncidenceDescent`.
-/

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.Jacobian.SplitComponentMonicCoordinates

open BlockPermutationInvariants
open AffineLineMonicCoordinates
open SplitFiniteSymmetricQuotient
open SplitComponentUniversalRoot
open SplitSymmetricQuotientChart

variable (R : Type u) [CommRing R] [Nontrivial R]
variable (d m : ℕ) (c : splitComponentIndex d m)

local instance : MulAction (Equiv.Perm (Fin d)) (Fin d → Fin m) :=
  tuplePermutationAction d (Fin m)

/-- Include monic coefficient functions on a split quotient component into
the ordered-root polynomial ring. -/
noncomputable def componentMonicCoefficientToRoots :
    coefficientRing R d m c →ₐ[R] coefficientRing R d m c := by
  letI := componentStabilizerRootAction R d m c
  letI := componentStabilizerRootSMulCommClass R d m c
  exact (FixedPoints.subalgebra R (coefficientRing R d m c)
    (MulAction.stabilizer (Equiv.Perm (Fin d)) c.out)).val.comp
      (componentStabilizerInvariantAlgEquiv R d m c).toAlgHom

omit [Nontrivial R] in
/-- Formula for a component monic coefficient in ordered-root coordinates. -/
theorem componentMonicCoefficientToRoots_X
    (x : componentRootIndex d m c) :
    componentMonicCoefficientToRoots R d m c (MvPolynomial.X x) =
      MvPolynomial.C ((-1 : R) ^
        (sheetMultiplicity d m c x.1 - (x.2 : ℕ))) *
        blockElementarySymmetric R (Fin m)
          (fun j ↦ Fin (sheetMultiplicity d m c j)) x.1
          (sheetMultiplicity d m c x.1 - (x.2 : ℕ)) := by
  letI := componentStabilizerRootAction R d m c
  letI := componentStabilizerRootSMulCommClass R d m c
  exact componentStabilizerInvariantAlgEquiv_X R d m c x

/-- Product of the ordered linear factors in one sheet, embedded into the
joint ordered-root coordinate ring. -/
noncomputable def sheetOrderedRootPolynomial (j : Fin m) :
    Polynomial (coefficientRing R d m c) :=
  (orderedRootPolynomial R (sheetMultiplicity d m c j)).map
    (sheetCoefficientHom R d m c j).toRingHom

/-- Pulling a sheet's universal monic polynomial to ordered-root coordinates
gives the product of the ordered linear factors in that sheet. -/
theorem sheetPolynomial_map_componentMonicCoefficientToRoots (j : Fin m) :
    (sheetPolynomial R d m c j).1.map
        (componentMonicCoefficientToRoots R d m c).toRingHom =
      sheetOrderedRootPolynomial R d m c j := by
  have hcomp :
      (componentMonicCoefficientToRoots R d m c).toRingHom.comp
          (sheetCoefficientHom R d m c j).toRingHom =
        (sheetCoefficientHom R d m c j).toRingHom.comp
          (monicCoefficientToRoots R
            (sheetMultiplicity d m c j)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      simp only [RingHom.comp_apply]
      change componentMonicCoefficientToRoots R d m c
          (sheetCoefficientHom R d m c j (MvPolynomial.X i)) =
        sheetCoefficientHom R d m c j
          (monicCoefficientToRoots R
            (sheetMultiplicity d m c j) (MvPolynomial.X i))
      rw [sheetCoefficientHom, MvPolynomial.rename_X]
      rw [componentMonicCoefficientToRoots_X,
        monicCoefficientToRoots_X]
      simp [blockElementarySymmetric]
  rw [sheetPolynomial, Polynomial.MonicDegreeEq.map_coe,
    Polynomial.map_map, hcomp, ← Polynomial.map_map]
  simpa [sheetOrderedRootPolynomial] using congrArg
    (Polynomial.map (sheetCoefficientHom R d m c j).toRingHom)
    (freeMonic_map_monicCoefficientToRoots R
      (sheetMultiplicity d m c j))

end MazurTorsion.AlgebraicGeometry.Jacobian.SplitComponentMonicCoordinates

/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentSections

/-!
# Laurent descriptions of projective standard-intersection sections over a base

This file gives the objectwise part of the Laurent Čech model over an
arbitrary commutative coefficient ring.  In particular, no domain or
characteristic-zero hypothesis is imposed on the affine base.

The equivalences are stated additively because the geometric
standard-intersection comparison is presently packaged as a ring
equivalence rather than as an algebra equivalence.  The Laurent basis
equivalence itself remains linear over the coefficient ring.
-/

open CategoryTheory AlgebraicGeometry


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafModuleIsoSections
open MazurTorsion.AlgebraicGeometry.CoherentCohomology
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

noncomputable section

/-- Sections of the structure sheaf on a nonempty standard intersection
are additively equivalent to admissible degree-zero Laurent monomials.
This holds over every commutative coefficient ring, including rings with
zero divisors. -/
def standardIntersectionDegreeZeroSectionsAddEquiv
    (k : Type) [CommRing k] (d : ℕ)
    (I : Finset (Fin (d + 1))) [Nonempty ↥I] :
    MonomialModule (ι := Fin (d + 1)) k 0 I ≃+
      Γ((standardIntersection k
        (fun i : ↥I => i.1)).toScheme, ⊤) := by
  classical
  let h :
      coordinateProduct k (fun i : ↥I => i.1) =
        variableProduct (k := k) I :=
    coordinateProduct_subtype_eq_variableProduct k d I
  let e :
      HomogeneousLocalization.Away
          (homogeneousGrading k d) (variableProduct (k := k) I) ≃+*
        Γ((standardIntersection k
          (fun i : ↥I => i.1)).toScheme, ⊤) := by
    exact h ▸
      standardIntersectionAwayRingEquiv
        k d (fun i : ↥I => i.1)
  exact
    (degreeZeroFractionLinearEquiv
      (k := k) I).toAddEquiv.trans e.toAddEquiv

/-- Trivialization of an integer Serre twist on a nonempty standard
intersection, expressed on additive groups of sections over an arbitrary
commutative base. -/
def integerIntersectionSectionsAddEquivOver
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) [Nonempty ↥I] (j : ↥I) :
    Γ(OInt k d m, standardIntersection k
        (fun i : ↥I => i.1)) ≃+
      Γ((standardIntersection k
        (fun i : ↥I => i.1)).toScheme, ⊤) := by
  let U := standardIntersection k (fun i : ↥I => i.1)
  exact
    (sectionsRestrictTopAddEquiv (OInt k d m) U).trans <|
      (sectionsAddEquivOfIso
        (integerIntersectionRestrictIso'
          k d m (fun i : ↥I => i.1) j)).trans <|
        unitTopSectionsAddEquiv U.toScheme

/-- Changing the chosen trivializing coordinate shifts Laurent degree by
the exponent concentrated at that coordinate. -/
def monomialModuleShiftAddEquiv
    {k ι : Type} [Semiring k] [Fintype ι] [DecidableEq ι]
    (I : Finset ι) (j : ↥I) (m : ℤ) :
    MonomialModule (ι := ι) k 0 I ≃+
      MonomialModule (ι := ι) k m I :=
  (monomialModuleShiftLinearEquiv (k := k) I j m).toAddEquiv

/-- Sections of `𝒪(m)` on a nonempty projective standard intersection
are additively equivalent to admissible Laurent monomials of total degree
`m`, over an arbitrary commutative base ring. -/
def integerIntersectionLaurentSectionsAddEquivOver
    (k : Type) [CommRing k] (d : ℕ) (m : ℤ)
    (I : Finset (Fin (d + 1))) [Nonempty ↥I] (j : ↥I) :
    Γ(OInt k d m, standardIntersection k
        (fun i : ↥I => i.1)) ≃+
      MonomialModule (ι := Fin (d + 1)) k m I :=
  (integerIntersectionSectionsAddEquivOver k d m I j).trans <|
    (standardIntersectionDegreeZeroSectionsAddEquiv k d I).symm.trans <|
      monomialModuleShiftAddEquiv I j m

end

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.Algebra.Algebra.Subalgebra.Operations
import MazurTorsion.Upstream.AINTLIB.ForMathlib.AffineQuotient

/-!
# The symmetric power of the affine line

The symmetric group acts on a multivariable polynomial ring by permuting its
variables.  This file identifies its fixed subring with the symmetric
polynomials and hence, by the fundamental theorem of symmetric polynomials,
with a polynomial ring on the elementary-symmetric coefficients.  On spectra
this realizes affine coefficient space as the categorical quotient

`(A¹)^n ⟶ Sym^n(A¹)`.

The named downstream consumer is `UniversalEffectiveDivisorDescent`: together
with `UniversalRootFactorization`, the identification recognizes the universal
root equation as the pointed symmetric-power incidence family.

The permutation action is kept as a local reducible definition rather than a
global instance.  This avoids competing instances for actions on polynomial
rings while retaining the arbitrary-base, characteristic-free statement.
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.AffineLineSymmetricPower

variable (R : Type u) [CommRing R] (σ : Type*)

/-- The action of coordinate permutations on a multivariable polynomial ring,
presented as a homomorphism to ring automorphisms. -/
noncomputable def coordinatePermutationRingAut :
    Equiv.Perm σ →* RingAut (MvPolynomial σ R) where
  toFun e := (MvPolynomial.renameEquiv R e).toRingEquiv
  map_one' := by
    ext i
    simp
  map_mul' e f := by
    ext i
    simp [MvPolynomial.renameEquiv, MvPolynomial.rename_rename]

/-- The coordinate-permutation semiring action used to form the invariant
subring. -/
@[instance_reducible]
noncomputable def coordinatePermutationAction :
    MulSemiringAction (Equiv.Perm σ) (MvPolynomial σ R) :=
  MulSemiringAction.compHom (MvPolynomial σ R)
    (coordinatePermutationRingAut R σ)

theorem smul_eq_rename (e : Equiv.Perm σ) (p : MvPolynomial σ R) :
    letI := coordinatePermutationAction R σ
    e • p = MvPolynomial.rename e p := by
  change (coordinatePermutationRingAut R σ e) p = _
  rfl

/-- Coordinate permutations commute with the scalar action of the coefficient
ring. -/
theorem coordinatePermutationSMulCommClass :
    letI := coordinatePermutationAction R σ
    SMulCommClass (Equiv.Perm σ) R (MvPolynomial σ R) := by
  letI := coordinatePermutationAction R σ
  constructor
  intro e r p
  change MvPolynomial.rename e (r • p) = r • MvPolynomial.rename e p
  simp [Algebra.smul_def]

/-- Being fixed by every coordinate permutation is exactly Mathlib's predicate
of being a symmetric polynomial. -/
theorem mem_fixedPoints_iff_isSymmetric (p : MvPolynomial σ R) :
    letI := coordinatePermutationAction R σ
    letI := coordinatePermutationSMulCommClass R σ
    p ∈ FixedPoints.subalgebra R (MvPolynomial σ R) (Equiv.Perm σ) ↔
      p.IsSymmetric := by
  letI := coordinatePermutationAction R σ
  letI := coordinatePermutationSMulCommClass R σ
  change (∀ e : Equiv.Perm σ, e • p = p) ↔
    ∀ e : Equiv.Perm σ, MvPolynomial.rename e p = p
  exact forall_congr' fun e ↦ by rw [smul_eq_rename]

/-- The fixed subring and the symmetric-polynomial subalgebra are the same
subalgebra, packaged as an algebra equivalence. -/
noncomputable def fixedPointsEquivSymmetricSubalgebra :
    letI := coordinatePermutationAction R σ
    letI := coordinatePermutationSMulCommClass R σ
    FixedPoints.subalgebra R (MvPolynomial σ R) (Equiv.Perm σ) ≃ₐ[R]
      MvPolynomial.symmetricSubalgebra σ R := by
  letI := coordinatePermutationAction R σ
  letI := coordinatePermutationSMulCommClass R σ
  apply AlgEquiv.ofAlgHom
    ((FixedPoints.subalgebra R (MvPolynomial σ R) (Equiv.Perm σ)).inclusion
      (by
        intro p hp
        exact (mem_fixedPoints_iff_isSymmetric R σ p).mp hp))
    ((MvPolynomial.symmetricSubalgebra σ R).inclusion
      (by
        intro p hp
        exact (mem_fixedPoints_iff_isSymmetric R σ p).mpr hp))
  · ext p
    rfl
  · ext p
    rfl

/-- Elementary symmetric functions identify affine coefficient space with the
fixed subring of ordered roots. -/
noncomputable def coefficientEquivFixedPoints (n : ℕ) :
    letI := coordinatePermutationAction R (Fin n)
    letI := coordinatePermutationSMulCommClass R (Fin n)
    MvPolynomial (Fin n) R ≃ₐ[R]
      FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
        (Equiv.Perm (Fin n)) := by
  letI := coordinatePermutationAction R (Fin n)
  letI := coordinatePermutationSMulCommClass R (Fin n)
  exact (MvPolynomial.esymmAlgEquiv (Fin n) R (Fintype.card_fin n)).trans
    (fixedPointsEquivSymmetricSubalgebra R (Fin n)).symm

/-- The ordered-root affine scheme `(A¹)^n`. -/
abbrev orderedRootScheme (n : ℕ) :=
  Spec (CommRingCat.of (MvPolynomial (Fin n) R))

/-- The affine quotient target obtained as the spectrum of the invariant
subring. -/
noncomputable abbrev invariantRootScheme (n : ℕ) := by
  letI := coordinatePermutationAction R (Fin n)
  letI := coordinatePermutationSMulCommClass R (Fin n)
  exact Spec (CommRingCat.of
    (FixedPoints.subalgebra R (MvPolynomial (Fin n) R)
      (Equiv.Perm (Fin n))))

/-- The canonical affine quotient map from ordered roots to invariant
coefficients. -/
noncomputable def coordinateQuotientProjection (n : ℕ) :
    orderedRootScheme R n ⟶ invariantRootScheme R n := by
  letI := coordinatePermutationAction R (Fin n)
  letI := coordinatePermutationSMulCommClass R (Fin n)
  exact invariantsπ (Equiv.Perm (Fin n)) (MvPolynomial (Fin n) R) R

/-- The invariant quotient is affine `n`-space, with coordinates the
elementary symmetric functions. -/
noncomputable def invariantRootSchemeIsoCoefficientSpace (n : ℕ) :
    invariantRootScheme R n ≅ Spec (CommRingCat.of (MvPolynomial (Fin n) R)) := by
  letI := coordinatePermutationAction R (Fin n)
  letI := coordinatePermutationSMulCommClass R (Fin n)
  exact (Scheme.Spec.mapIso
    (coefficientEquivFixedPoints R n).toRingEquiv.toCommRingCatIso.op)

/-- The automorphism of ordered-root affine space induced by a coordinate
permutation. -/
noncomputable def coordinatePermutationSpecSMul (n : ℕ)
    (g : Equiv.Perm (Fin n)) : orderedRootScheme R n ⟶ orderedRootScheme R n := by
  letI := coordinatePermutationAction R (Fin n)
  exact specSMul g

/-- The affine ordered-root projection is the categorical quotient by
coordinate permutations. -/
theorem coordinateQuotientProjection_existsUnique_lift (n : ℕ)
    {Y : Scheme.{u}} (f : orderedRootScheme R n ⟶ Y)
    (hf : ∀ g : Equiv.Perm (Fin n),
      coordinatePermutationSpecSMul R n g ≫ f = f) :
    ∃! q : invariantRootScheme R n ⟶ Y,
      coordinateQuotientProjection R n ≫ q = f := by
  letI := coordinatePermutationAction R (Fin n)
  letI := coordinatePermutationSMulCommClass R (Fin n)
  exact existsUnique_invariantsπ_lift (Equiv.Perm (Fin n))
    (MvPolynomial (Fin n) R) R f (by
      intro g
      exact hf g)

end MazurTorsion.AlgebraicGeometry.Jacobian.AffineLineSymmetricPower

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.MvPolynomialFixedCoefficients
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-!
# Simultaneous coordinate and coefficient invariants

Let one symmetric group permute the variables of a polynomial ring while a
second group acts on its coefficients.  The common fixed ring is a polynomial
ring in the elementary-symmetric coordinates over the fixed coefficient
ring.  This packages one full induction step for blockwise symmetric
polynomials.

The named downstream consumer is `SplitSymmetricQuotientChart`, which applies
the theorem recursively to the sheet fibers of a split finite étale chart.
-/

noncomputable section

universe u v w x

namespace MazurTorsion.AlgebraicGeometry.Jacobian.CoordinateCoefficientInvariants

open MvPolynomialFixedCoefficients

variable (G : Type u) [Group G]
variable (R : Type v) [CommRing R]
variable (A : Type w) [CommRing A] [Algebra R A]
variable (σ : Type x)
variable [MulSemiringAction G A] [SMulCommClass G R A]

/-- The product action that permutes polynomial variables and acts on
coefficients. -/
@[instance_reducible]
noncomputable def coordinateCoefficientAction :
    MulSemiringAction (Equiv.Perm σ × G) (MvPolynomial σ A) where
  smul hg p := MvPolynomial.rename hg.1
    (MvPolynomial.map (MulSemiringAction.toRingHom G A hg.2) p)
  one_smul p := by
    change MvPolynomial.rename (1 : Equiv.Perm σ)
      (MvPolynomial.map (MulSemiringAction.toRingHom G A (1 : G)) p) = p
    have hmap : MvPolynomial.map
        (MulSemiringAction.toRingHom G A (1 : G)) p = p := by
      ext m
      rw [MvPolynomial.coeff_map]
      exact one_smul G (MvPolynomial.coeff m p)
    rw [hmap]
    simp
  mul_smul hg kl p := by
    change MvPolynomial.rename (hg.1 * kl.1)
        (MvPolynomial.map
          (MulSemiringAction.toRingHom G A (hg.2 * kl.2)) p) =
      MvPolynomial.rename hg.1
        (MvPolynomial.map (MulSemiringAction.toRingHom G A hg.2)
          (MvPolynomial.rename kl.1
            (MvPolynomial.map (MulSemiringAction.toRingHom G A kl.2) p)))
    induction p using MvPolynomial.induction_on with
    | C r =>
        simp only [MvPolynomial.map_C, MvPolynomial.rename_C]
        congr 1
        change (hg.2 * kl.2) • r = hg.2 • kl.2 • r
        exact mul_smul hg.2 kl.2 r
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp =>
        simp only [map_mul, MvPolynomial.map_X, MvPolynomial.rename_X, hp]
        rfl
  smul_zero hg := by
    change MvPolynomial.rename hg.1
      (MvPolynomial.map (MulSemiringAction.toRingHom G A hg.2) 0) = 0
    rw [map_zero, map_zero]
  smul_add hg p q := by
    change MvPolynomial.rename hg.1
        (MvPolynomial.map (MulSemiringAction.toRingHom G A hg.2) (p + q)) =
      MvPolynomial.rename hg.1
          (MvPolynomial.map (MulSemiringAction.toRingHom G A hg.2) p) +
        MvPolynomial.rename hg.1
          (MvPolynomial.map (MulSemiringAction.toRingHom G A hg.2) q)
    rw [map_add, map_add]
  smul_one hg := by
    change MvPolynomial.rename hg.1
      (MvPolynomial.map (MulSemiringAction.toRingHom G A hg.2) 1) = 1
    rw [map_one, map_one]
  smul_mul hg p q := by
    change MvPolynomial.rename hg.1
        (MvPolynomial.map (MulSemiringAction.toRingHom G A hg.2) (p * q)) =
      MvPolynomial.rename hg.1
          (MvPolynomial.map (MulSemiringAction.toRingHom G A hg.2) p) *
        MvPolynomial.rename hg.1
          (MvPolynomial.map (MulSemiringAction.toRingHom G A hg.2) q)
    rw [map_mul, map_mul]

/-- The product action fixes scalars from the base ring. -/
theorem coordinateCoefficientSMulCommClass :
    letI := coordinateCoefficientAction G A σ
    SMulCommClass (Equiv.Perm σ × G) R (MvPolynomial σ A) := by
  letI := coordinateCoefficientAction G A σ
  constructor
  intro hg r p
  change MvPolynomial.rename hg.1
      (MvPolynomial.map (MulSemiringAction.toRingHom G A hg.2) (r • p)) =
    r • MvPolynomial.rename hg.1
      (MvPolynomial.map (MulSemiringAction.toRingHom G A hg.2) p)
  simp only [Algebra.smul_def, map_mul]
  congr 1
  change MvPolynomial.rename hg.1
      (MvPolynomial.map (MulSemiringAction.toRingHom G A hg.2)
        (MvPolynomial.C (algebraMap R A r))) =
    MvPolynomial.C (algebraMap R A r)
  rw [MvPolynomial.map_C]
  change MvPolynomial.rename hg.1
      (MvPolynomial.C (hg.2 • algebraMap R A r)) = _
  rw [smul_algebraMap]
  simp

/-- Polynomials fixed simultaneously by every coordinate permutation and by
the coefficientwise `G`-action. -/
noncomputable def coordinateCoefficientFixedSubalgebra :
    Subalgebra R (MvPolynomial σ A) where
  carrier := { p | ∀ h : Equiv.Perm σ, ∀ g : G,
    MvPolynomial.rename h
      (MvPolynomial.map (MulSemiringAction.toRingHom G A g) p) = p }
  zero_mem' h g := by simp
  add_mem' {p q} hp hq h g := by
    rw [map_add, map_add, hp h g, hq h g]
  one_mem' h g := by simp
  mul_mem' {p q} hp hq h g := by
    rw [map_mul, map_mul, hp h g, hq h g]
  algebraMap_mem' r h g := by
    change MvPolynomial.rename h
        (MvPolynomial.map (MulSemiringAction.toRingHom G A g)
          (MvPolynomial.C (algebraMap R A r))) =
      MvPolynomial.C (algebraMap R A r)
    rw [MvPolynomial.map_C]
    change MvPolynomial.rename h
        (MvPolynomial.C (g • algebraMap R A r)) = _
    rw [smul_algebraMap]
    simp

/-- The explicit simultaneous-invariant subalgebra agrees with Mathlib's
fixed-point subalgebra for the product action. -/
noncomputable def fixedPointsEquivCoordinateCoefficientFixed :
    letI := coordinateCoefficientAction G A σ
    letI := coordinateCoefficientSMulCommClass G R A σ
    FixedPoints.subalgebra R (MvPolynomial σ A) (Equiv.Perm σ × G) ≃ₐ[R]
      coordinateCoefficientFixedSubalgebra G R A σ := by
  letI := coordinateCoefficientAction G A σ
  letI := coordinateCoefficientSMulCommClass G R A σ
  apply AlgEquiv.ofAlgHom
    ((FixedPoints.subalgebra R (MvPolynomial σ A)
      (Equiv.Perm σ × G)).inclusion (by
        intro p hp h g
        exact hp (h, g)))
    ((coordinateCoefficientFixedSubalgebra G R A σ).inclusion (by
        intro p hp hg
        exact hp hg.1 hg.2))
  · ext p
    rfl
  · ext p
    rfl

variable [Fintype σ]

/-- Mapping a symmetric polynomial over the fixed coefficient ring into the
ambient coefficient ring lands in the simultaneous fixed subring. -/
noncomputable def symmetricFixedCoefficientsToCombined :
    (MvPolynomial.symmetricSubalgebra σ
      (FixedPoints.subalgebra R A G)).restrictScalars R →ₐ[R]
      coordinateCoefficientFixedSubalgebra G R A σ := by
  refine ((MvPolynomial.mapAlgHom
    (FixedPoints.subalgebra R A G).val).comp
      (Subalgebra.val _)).codRestrict _ ?_
  intro p h g
  have hg : MvPolynomial.map (MulSemiringAction.toRingHom G A g)
      (MvPolynomial.map (FixedPoints.subalgebra R A G).val.toRingHom p.1) =
        MvPolynomial.map (FixedPoints.subalgebra R A G).val.toRingHom p.1 :=
    (mapFixedCoefficientsToFixedPoints G R A σ p.1).2 g
  change MvPolynomial.rename h
      (MvPolynomial.map (MulSemiringAction.toRingHom G A g)
        (MvPolynomial.map (FixedPoints.subalgebra R A G).val.toRingHom p.1)) =
    MvPolynomial.map (FixedPoints.subalgebra R A G).val.toRingHom p.1
  rw [hg]
  rw [← MvPolynomial.map_rename]
  rw [p.2 h]

/-- One blockwise fundamental-theorem step: simultaneous invariants are freely
generated by elementary-symmetric variables over the fixed coefficient
subring. -/
noncomputable def coefficientCoordinateAlgHom (n : ℕ)
    (hn : Fintype.card σ = n) :
    MvPolynomial (Fin n) (FixedPoints.subalgebra R A G) →ₐ[R]
      coordinateCoefficientFixedSubalgebra G R A σ :=
  (symmetricFixedCoefficientsToCombined G R A σ).comp
    ((MvPolynomial.esymmAlgEquiv σ
      (FixedPoints.subalgebra R A G) hn).toAlgHom.restrictScalars R)

@[simp]
theorem coefficientCoordinateAlgHom_apply_val (n : ℕ)
    (hn : Fintype.card σ = n)
    (p : MvPolynomial (Fin n) (FixedPoints.subalgebra R A G)) :
    ((coefficientCoordinateAlgHom G R A σ n hn) p).1 =
      MvPolynomial.map (FixedPoints.subalgebra R A G).val.toRingHom
        ((MvPolynomial.esymmAlgEquiv σ
          (FixedPoints.subalgebra R A G) hn p).1) := rfl

/-- The combined invariant map is bijective. -/
theorem coefficientCoordinateAlgHom_bijective (n : ℕ)
    (hn : Fintype.card σ = n) :
    Function.Bijective (coefficientCoordinateAlgHom G R A σ n hn) := by
  constructor
  · intro p q hpq
    apply (MvPolynomial.esymmAlgEquiv σ
      (FixedPoints.subalgebra R A G) hn).injective
    apply Subtype.ext
    apply MvPolynomial.map_injective
      (f := (FixedPoints.subalgebra R A G).val.toRingHom)
      Subtype.val_injective
    exact congrArg Subtype.val hpq
  · intro p
    let pc : fixedCoefficientPolynomialSubalgebra G R A σ :=
      ⟨p.1, fun g ↦ by
        simpa using p.2 (1 : Equiv.Perm σ) g⟩
    let q : MvPolynomial σ (FixedPoints.subalgebra R A G) :=
      packageFixedCoefficients G R A σ pc
    have hq_map : MvPolynomial.map
        (FixedPoints.subalgebra R A G).val.toRingHom q = p.1 :=
      map_packageFixedCoefficients G R A σ pc
    have hq_symm : q.IsSymmetric := by
      intro h
      apply MvPolynomial.map_injective
        (f := (FixedPoints.subalgebra R A G).val.toRingHom)
        Subtype.val_injective
      rw [MvPolynomial.map_rename, hq_map]
      have hp := p.2 h (1 : G)
      have hone : MvPolynomial.map
          (MulSemiringAction.toRingHom G A (1 : G)) p.1 = p.1 := by
        ext m
        rw [MvPolynomial.coeff_map]
        exact one_smul G (MvPolynomial.coeff m p.1)
      rw [hone] at hp
      exact hp
    let s : MvPolynomial.symmetricSubalgebra σ
        (FixedPoints.subalgebra R A G) := ⟨q, hq_symm⟩
    refine ⟨(MvPolynomial.esymmAlgEquiv σ
      (FixedPoints.subalgebra R A G) hn).symm s, ?_⟩
    apply Subtype.ext
    rw [coefficientCoordinateAlgHom_apply_val,
      (MvPolynomial.esymmAlgEquiv σ
        (FixedPoints.subalgebra R A G) hn).apply_symm_apply]
    exact hq_map

/-- Algebra equivalence form of the coordinate/coefficient invariant
calculation. -/
noncomputable def coefficientCoordinateAlgEquiv (n : ℕ)
    (hn : Fintype.card σ = n) :
    MvPolynomial (Fin n) (FixedPoints.subalgebra R A G) ≃ₐ[R]
      coordinateCoefficientFixedSubalgebra G R A σ :=
  AlgEquiv.ofBijective (coefficientCoordinateAlgHom G R A σ n hn)
    (coefficientCoordinateAlgHom_bijective G R A σ n hn)

end MazurTorsion.AlgebraicGeometry.Jacobian.CoordinateCoefficientInvariants

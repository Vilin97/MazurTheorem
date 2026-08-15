/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.GroupTheory.GroupAction.FixedPoints

/-!
# Fixed coefficients in multivariable polynomial rings

When a group acts on the coefficient ring and fixes the scalar ring, its
coefficientwise action on a multivariable polynomial ring has exactly the
polynomials whose individual coefficients are fixed.  Consequently the fixed
subring is a polynomial ring over the fixed coefficient subring.

The named downstream consumer is `SplitSymmetricQuotientChart`: after one
fiber has been treated by the fundamental theorem of symmetric polynomials,
this equivalence moves the remaining fiber invariants into the coefficient
ring and supplies the induction step for all fibers.
-/

noncomputable section

universe u v w x

namespace MazurTorsion.AlgebraicGeometry.Jacobian.MvPolynomialFixedCoefficients

variable (G : Type u) [Group G]
variable (R : Type v) [CommRing R]
variable (A : Type w) [CommRing A] [Algebra R A]
variable (σ : Type x)
variable [MulSemiringAction G A] [SMulCommClass G R A]

/-- The coefficientwise action on a multivariable polynomial ring. -/
@[instance_reducible]
noncomputable def coefficientAction :
    MulSemiringAction G (MvPolynomial σ A) where
  smul g p := MvPolynomial.map (MulSemiringAction.toRingHom G A g) p
  one_smul p := by
    change MvPolynomial.map (MulSemiringAction.toRingHom G A 1) p = p
    ext m
    rw [MvPolynomial.coeff_map]
    exact one_smul G (MvPolynomial.coeff m p)
  mul_smul g h p := by
    change MvPolynomial.map (MulSemiringAction.toRingHom G A (g * h)) p =
      MvPolynomial.map (MulSemiringAction.toRingHom G A g)
        (MvPolynomial.map (MulSemiringAction.toRingHom G A h) p)
    ext m
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_map,
      MvPolynomial.coeff_map]
    exact mul_smul g h (MvPolynomial.coeff m p)
  smul_zero g := (MvPolynomial.map
    (MulSemiringAction.toRingHom G A g)).map_zero
  smul_add g p q := (MvPolynomial.map
    (MulSemiringAction.toRingHom G A g)).map_add p q
  smul_one g := (MvPolynomial.map
    (MulSemiringAction.toRingHom G A g)).map_one
  smul_mul g p q := (MvPolynomial.map
    (MulSemiringAction.toRingHom G A g)).map_mul p q

theorem coefficient_smul_eq_map (g : G) (p : MvPolynomial σ A) :
    letI : MulSemiringAction G (MvPolynomial σ A) := coefficientAction G A σ
    g • p = MvPolynomial.map (MulSemiringAction.toRingHom G A g) p := rfl

/-- The coefficientwise action fixes scalars from the base ring. -/
theorem coefficientSMulCommClass :
    letI : MulSemiringAction G (MvPolynomial σ A) := coefficientAction G A σ
    SMulCommClass G R (MvPolynomial σ A) := by
  letI := coefficientAction G A σ
  constructor
  intro g r p
  change MvPolynomial.map (MulSemiringAction.toRingHom G A g) (r • p) =
    r • MvPolynomial.map (MulSemiringAction.toRingHom G A g) p
  simp only [Algebra.smul_def, map_mul]
  congr 1
  change MvPolynomial.map (MulSemiringAction.toRingHom G A g)
      (MvPolynomial.C (algebraMap R A r)) =
    MvPolynomial.C (algebraMap R A r)
  rw [MvPolynomial.map_C]
  congr 1
  change g • algebraMap R A r = algebraMap R A r
  exact smul_algebraMap g r

/-- The fixed subring for the coefficientwise polynomial action, written
explicitly so its carrier is independent of reducible-instance choices. -/
noncomputable def fixedCoefficientPolynomialSubalgebra :
    Subalgebra R (MvPolynomial σ A) where
  carrier := { p | ∀ g : G,
    MvPolynomial.map (MulSemiringAction.toRingHom G A g) p = p }
  zero_mem' g := (MvPolynomial.map
    (MulSemiringAction.toRingHom G A g)).map_zero
  add_mem' {p q} hp hq g := by
    rw [(MvPolynomial.map
      (MulSemiringAction.toRingHom G A g)).map_add, hp g, hq g]
  one_mem' g := (MvPolynomial.map
    (MulSemiringAction.toRingHom G A g)).map_one
  mul_mem' {p q} hp hq g := by
    rw [(MvPolynomial.map
      (MulSemiringAction.toRingHom G A g)).map_mul, hp g, hq g]
  algebraMap_mem' r g := by
    change MvPolynomial.map (MulSemiringAction.toRingHom G A g)
        (MvPolynomial.C (algebraMap R A r)) =
      MvPolynomial.C (algebraMap R A r)
    rw [MvPolynomial.map_C]
    congr 1
    change g • algebraMap R A r = algebraMap R A r
    exact smul_algebraMap g r

/-- A coefficient of a fixed polynomial is itself fixed. -/
theorem coeff_mem_fixedPoints
    (p : MvPolynomial σ A)
    (hp : p ∈ fixedCoefficientPolynomialSubalgebra G R A σ)
    (m : σ →₀ ℕ) :
    MvPolynomial.coeff m p ∈ FixedPoints.subalgebra R A G := by
  intro g
  have h := congrArg (MvPolynomial.coeff m) (hp g)
  simpa [MvPolynomial.coeff_map] using h

/-- Replace every coefficient of a fixed polynomial by the same coefficient
packaged as an element of the fixed coefficient subring. -/
noncomputable def packageFixedCoefficients :
    fixedCoefficientPolynomialSubalgebra
      (G := G) (R := R) (A := A) (σ := σ) →
      MvPolynomial σ (FixedPoints.subalgebra R A G) := by
  intro p
  exact AddMonoidAlgebra.ofCoeff (Finsupp.onFinset p.1.support
    (fun m ↦ (⟨MvPolynomial.coeff m p.1,
      coeff_mem_fixedPoints G R A σ p.1 p.2 m⟩ :
        FixedPoints.subalgebra R A G))
    (by
      intro m hm
      exact Finsupp.mem_support_iff.mpr (fun hzero ↦
        hm (Subtype.ext hzero))))

/-- Mapping packaged fixed coefficients back into the ambient coefficient
ring recovers the original polynomial. -/
theorem map_packageFixedCoefficients :
    ∀ p : fixedCoefficientPolynomialSubalgebra
      (G := G) (R := R) (A := A) (σ := σ),
    MvPolynomial.map
        (FixedPoints.subalgebra R A G).val.toRingHom
        (packageFixedCoefficients G R A σ p) = p.1 := by
  intro p
  classical
  ext m
  rfl

/-- Mapping the inclusion of the fixed coefficient subring lands in the fixed
polynomial subring. -/
noncomputable def mapFixedCoefficientsToFixedPoints :
    MvPolynomial σ (FixedPoints.subalgebra R A G) →ₐ[R]
      fixedCoefficientPolynomialSubalgebra
        (G := G) (R := R) (A := A) (σ := σ) := by
  refine (MvPolynomial.mapAlgHom
    (FixedPoints.subalgebra R A G).val).codRestrict _ ?_
  intro p g
  apply MvPolynomial.ext
  intro m
  simp only [MvPolynomial.mapAlgHom_apply, MvPolynomial.coeff_map]
  exact (MvPolynomial.coeff m p).2 g

/-- Fixed points of a coefficientwise action are precisely polynomials over
the fixed coefficient subring. -/
noncomputable def fixedPointsEquivMvPolynomialFixedCoefficients :
    MvPolynomial σ (FixedPoints.subalgebra R A G) ≃ₐ[R]
      fixedCoefficientPolynomialSubalgebra
        (G := G) (R := R) (A := A) (σ := σ) := by
  apply AlgEquiv.ofBijective (mapFixedCoefficientsToFixedPoints G R A σ)
  constructor
  · intro p q h
    apply MvPolynomial.map_injective
      (f := (FixedPoints.subalgebra R A G).val.toRingHom)
      Subtype.val_injective
    exact congrArg Subtype.val h
  · intro p
    refine ⟨packageFixedCoefficients G R A σ p, ?_⟩
    apply Subtype.ext
    exact map_packageFixedCoefficients G R A σ p

end MazurTorsion.AlgebraicGeometry.Jacobian.MvPolynomialFixedCoefficients

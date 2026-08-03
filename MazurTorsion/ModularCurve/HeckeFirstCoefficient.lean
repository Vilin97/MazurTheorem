/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.QExpansionFirstCoefficient

/-!
# First-coefficient detection for a Hecke eigen-expansion

The degree-one formal-immersion argument does not need a multi-operator linear-independence
criterion.  If a nonzero q-expansion `Q` is a simultaneous eigenvector and the first coefficient
of `Tₙ Q` is the `n`-th coefficient of `Q`, then a vanishing first coefficient would force every
coefficient of `Q` to vanish.

This file proves that exact linear-algebra statement on formal power series.  Its downstream
consumer applies the result to the completed pullback of a target local parameter and invokes the
checked degree-one formal-immersion theorem.  Construction of the modular Hecke operators and the
proof of their q-expansion formula remain separate geometric inputs.
-/

namespace MazurTorsion.ModularCurve

open _root_.AlgebraicGeometry
open CategoryTheory

universe u

namespace HeckeFirstCoefficient

variable {K : Type u} [Field K]

/-- A nonzero simultaneous Hecke eigen-expansion has nonzero first coefficient when `Tₙ`
recovers the `n`-th coefficient in first position. -/
theorem coeff_one_ne_zero_of_simultaneousEigenvector
    (Q : PowerSeries K) (hQ : Q ≠ 0)
    (T : ℕ → Module.End K (PowerSeries K)) (eigenvalue : ℕ → K)
    (hfirst : ∀ n, PowerSeries.coeff 1 (T n Q) = PowerSeries.coeff n Q)
    (heigen : ∀ n, T n Q = eigenvalue n • Q) :
    PowerSeries.coeff 1 Q ≠ 0 := by
  intro hone
  apply hQ
  apply (PowerSeries.forall_coeff_eq_zero Q).mp
  intro n
  calc
    PowerSeries.coeff n Q = PowerSeries.coeff 1 (T n Q) := (hfirst n).symm
    _ = PowerSeries.coeff 1 (eigenvalue n • Q) := by rw [heigen n]
    _ = eigenvalue n • PowerSeries.coeff 1 Q := PowerSeries.coeff_smul 1 Q (eigenvalue n)
    _ = 0 := by rw [hone, smul_zero]

end HeckeFirstCoefficient

namespace DegreeOneCotangentCertificate

variable {X Y : Scheme.{u}}

/-- A nonzero simultaneous Hecke eigen-expansion of the pulled-back target parameter proves the
actual completed-stalk formal-immersion predicate.  The Hecke action and its first-coefficient
formula are explicit inputs; this theorem is their checked downstream consumer. -/
theorem isFormalImmersionAt_of_heckeEigen_qExpansion
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 π]
    (Y : Scheme.{u}) [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (g : Spec (.of K) ⟶ X)
    [IsIso (X.descResidueField (Scheme.stalkClosedPointTo g))]
    [IsIso (Y.descResidueField (Scheme.stalkClosedPointTo (g ≫ f)))]
    (hx : g (IsLocalRing.closedPoint K) ≠ genericPoint X)
    (qCoordinate :
      Scheme.CompletedStalk X (g (IsLocalRing.closedPoint K)) ≃+* PowerSeries K)
    (targetParameter : IsLocalRing.maximalIdeal
      (Y.presheaf.stalk (f (g (IsLocalRing.closedPoint K)))))
    (Q : PowerSeries K)
    (hqExpansion :
      qCoordinate (algebraMap
        (X.presheaf.stalk (g (IsLocalRing.closedPoint K)))
        (Scheme.CompletedStalk X (g (IsLocalRing.closedPoint K)))
        ((f.stalkMap (g (IsLocalRing.closedPoint K))).hom targetParameter)) = Q)
    (hQ : Q ≠ 0)
    (T : ℕ → Module.End K (PowerSeries K)) (eigenvalue : ℕ → K)
    (hfirst : ∀ n, PowerSeries.coeff 1 (T n Q) = PowerSeries.coeff n Q)
    (heigen : ∀ n, T n Q = eigenvalue n • Q) :
    AlgebraicGeometry.IsFormalImmersionAt f (g (IsLocalRing.closedPoint K)) := by
  apply isFormalImmersionAt_of_smoothRelativeCurve_rationalPoint_of_qExpansionCoeffOne
    K X π Y f g hx qCoordinate targetParameter
  rw [hqExpansion]
  exact HeckeFirstCoefficient.coeff_one_ne_zero_of_simultaneousEigenvector
    Q hQ T eigenvalue hfirst heigen

end DegreeOneCotangentCertificate

end MazurTorsion.ModularCurve

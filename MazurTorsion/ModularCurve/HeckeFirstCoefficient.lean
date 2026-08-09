/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.SmoothCurveRationalSection
import MazurTorsion.ModularCurve.QExpansionFirstCoefficient
import Mathlib.Data.PNat.Basic

/-!
# First-coefficient detection for Hecke-stable q-expansions

The degree-one formal-immersion argument does not need a multi-operator linear-independence
criterion.  If a nonzero q-expansion `Q` is a simultaneous eigenvector and the first coefficient
of `Tₙ Q` is the `n`-th coefficient of `Q`, then a vanishing first coefficient would force every
coefficient of `Q` to vanish.

This file proves that exact linear-algebra statement on formal power series.  Its downstream
consumer applies the result to the completed pullback of a target local parameter and invokes the
checked degree-one formal-immersion theorem.  Construction of the modular Hecke operators and the
proof of their q-expansion formula remain separate geometric inputs.

For a prime-to-level fibre, the eigenvector step is unnecessary.  On a nonzero Hecke-stable
module with an injective cuspidal q-expansion, vanishing of the first coefficient on the whole
module would make every positive coefficient vanish by applying the positive-index Hecke
operators.  The constant coefficient vanishes separately because the expansions are cuspidal.
-/

namespace MazurTorsion.ModularCurve

open _root_.AlgebraicGeometry
open CategoryTheory

universe u v

namespace HeckeFirstCoefficient

variable {K : Type u} [Field K]

/-- A nonzero Hecke-stable module with an injective cuspidal q-expansion contains a vector with
nonzero first coefficient.

The operators are indexed by `ℕ+`, so there is no artificial zeroth Hecke operator.  The
constant coefficient is required to vanish explicitly, while the Hecke identity recovers every
genuine positive coefficient.  No eigenvector, commutativity, or splitting hypothesis is needed.
-/
theorem exists_coeff_one_ne_zero_of_heckeStable_qExpansion
    {M : Type v} [AddCommGroup M] [Module K M] [Nontrivial M]
    (qExpansion : M →ₗ[K] PowerSeries K)
    (hqExpansion : Function.Injective qExpansion)
    (positiveHecke : ℕ+ → Module.End K M)
    (hconstant : ∀ v, PowerSeries.coeff 0 (qExpansion v) = 0)
    (hfirst : ∀ (n : ℕ+) v,
      PowerSeries.coeff 1 (qExpansion (positiveHecke n v)) =
        PowerSeries.coeff (n : ℕ) (qExpansion v)) :
    ∃ v, PowerSeries.coeff 1 (qExpansion v) ≠ 0 := by
  by_contra hdetect
  have hone : ∀ v, PowerSeries.coeff 1 (qExpansion v) = 0 := by
    intro v
    by_contra hv
    exact hdetect ⟨v, hv⟩
  have hzero : ∀ v, qExpansion v = 0 := by
    intro v
    apply (PowerSeries.forall_coeff_eq_zero (qExpansion v)).mp
    intro n
    cases n with
    | zero => exact hconstant v
    | succ n =>
        let n' : ℕ+ := ⟨n.succ, Nat.succ_pos n⟩
        calc
          PowerSeries.coeff n.succ (qExpansion v) =
              PowerSeries.coeff 1 (qExpansion (positiveHecke n' v)) :=
            (hfirst n' v).symm
          _ = 0 := hone (positiveHecke n' v)
  obtain ⟨v, w, hvw⟩ := exists_pair_ne M
  apply hvw
  apply hqExpansion
  rw [hzero v, hzero w]

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

/-- A Hecke-stable q-expansion of the actual target stalk cotangent space proves formal
immersion at a rational point.

The q-expansion is taken over the target residue field.  Its first coefficient is compared,
through the rational target residue-field map, with the first coefficient of the actual
completed-stalk pullback of every representative of a cotangent class.  First-coefficient
detection supplies a cotangent class, `Ideal.toCotangent_surjective` supplies a representative,
and the existing completed-pullback consumer proves the genuine formal-immersion predicate.
-/
theorem isFormalImmersionAt_of_heckeStable_cotangentQExpansion
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 π]
    (Y : Scheme.{u}) [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (g : Spec (.of K) ⟶ X)
    [IsIso (X.descResidueField (Scheme.stalkClosedPointTo g))]
    [IsIso (Y.descResidueField (Scheme.stalkClosedPointTo (g ≫ f)))]
    (hx : g (IsLocalRing.closedPoint K) ≠ genericPoint X)
    (qCoordinate :
      Scheme.CompletedStalk X (g (IsLocalRing.closedPoint K)) ≃+* PowerSeries K)
    [Nontrivial (Scheme.Hom.targetStalkCotangent f
      (g (IsLocalRing.closedPoint K)))]
    (qExpansion :
      Scheme.Hom.targetStalkCotangent f (g (IsLocalRing.closedPoint K))
        →ₗ[IsLocalRing.ResidueField
          (Y.presheaf.stalk (f (g (IsLocalRing.closedPoint K))))]
        PowerSeries
          (IsLocalRing.ResidueField
            (Y.presheaf.stalk (f (g (IsLocalRing.closedPoint K))))))
    (hqExpansion : Function.Injective qExpansion)
    (positiveHecke : ℕ+ → Module.End
      (IsLocalRing.ResidueField
        (Y.presheaf.stalk (f (g (IsLocalRing.closedPoint K)))))
      (Scheme.Hom.targetStalkCotangent f
        (g (IsLocalRing.closedPoint K))))
    (hconstant : ∀ v, PowerSeries.coeff 0 (qExpansion v) = 0)
    (hfirst : ∀ (n : ℕ+) v,
      PowerSeries.coeff 1 (qExpansion (positiveHecke n v)) =
        PowerSeries.coeff (n : ℕ) (qExpansion v))
    (hcoeffCompatibility :
      ∀ a : IsLocalRing.maximalIdeal
          (Y.presheaf.stalk (f (g (IsLocalRing.closedPoint K)))),
        PowerSeries.coeff 1
            (qCoordinate (algebraMap
              (X.presheaf.stalk (g (IsLocalRing.closedPoint K)))
              (Scheme.CompletedStalk X (g (IsLocalRing.closedPoint K)))
              ((f.stalkMap (g (IsLocalRing.closedPoint K))).hom a))) =
          (Y.descResidueField
              (Scheme.stalkClosedPointTo (g ≫ f))).hom
            (PowerSeries.coeff 1
              (qExpansion (Ideal.toCotangent
                (IsLocalRing.maximalIdeal
                  (Y.presheaf.stalk (f (g (IsLocalRing.closedPoint K))))) a)))) :
    AlgebraicGeometry.IsFormalImmersionAt f
      (g (IsLocalRing.closedPoint K)) := by
  obtain ⟨v, hv⟩ :=
    HeckeFirstCoefficient.exists_coeff_one_ne_zero_of_heckeStable_qExpansion
      qExpansion hqExpansion positiveHecke hconstant hfirst
  obtain ⟨a, rfl⟩ := Ideal.toCotangent_surjective
    (IsLocalRing.maximalIdeal
      (Y.presheaf.stalk (f (g (IsLocalRing.closedPoint K))))) v
  apply isFormalImmersionAt_of_smoothRelativeCurve_rationalPoint_of_qExpansionCoeffOne
    K X π Y f g hx qCoordinate a
  rw [hcoeffCompatibility a]
  exact (map_ne_zero
    (Y.descResidueField (Scheme.stalkClosedPointTo (g ≫ f))).hom).mpr hv

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

/-- A represented rational section discharges the non-genericity input in
the degree-one Hecke criterion. The section law and relative-dimension-one
geometry prove that its image cannot be the generic point; the remaining
inputs are the genuine completed-local-ring and Hecke calculations. -/
theorem isFormalImmersionAt_of_rationalSection_heckeEigen_qExpansion
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 π]
    (Y : Scheme.{u}) [IsLocallyNoetherian Y]
    (f : X ⟶ Y)
    (x : MazurTorsion.AlgebraicGeometry.SmoothCurveRationalSection K X π)
    [IsIso (X.descResidueField (Scheme.stalkClosedPointTo x.hom))]
    [IsIso (Y.descResidueField
      (Scheme.stalkClosedPointTo (x.hom ≫ f)))]
    (qCoordinate :
      Scheme.CompletedStalk X
        (x.hom (IsLocalRing.closedPoint K)) ≃+* PowerSeries K)
    (targetParameter : IsLocalRing.maximalIdeal
      (Y.presheaf.stalk (f (x.hom (IsLocalRing.closedPoint K)))))
    (Q : PowerSeries K)
    (hqExpansion :
      qCoordinate (algebraMap
        (X.presheaf.stalk (x.hom (IsLocalRing.closedPoint K)))
        (Scheme.CompletedStalk X (x.hom (IsLocalRing.closedPoint K)))
        ((f.stalkMap
          (x.hom (IsLocalRing.closedPoint K))).hom targetParameter)) = Q)
    (hQ : Q ≠ 0)
    (T : ℕ → Module.End K (PowerSeries K)) (eigenvalue : ℕ → K)
    (hfirst : ∀ n, PowerSeries.coeff 1 (T n Q) = PowerSeries.coeff n Q)
    (heigen : ∀ n, T n Q = eigenvalue n • Q) :
    AlgebraicGeometry.IsFormalImmersionAt f
      (x.hom (IsLocalRing.closedPoint K)) :=
  isFormalImmersionAt_of_heckeEigen_qExpansion K X π Y f x.hom
    x.ne_generic qCoordinate targetParameter Q hqExpansion hQ T eigenvalue
      hfirst heigen

end DegreeOneCotangentCertificate

end MazurTorsion.ModularCurve

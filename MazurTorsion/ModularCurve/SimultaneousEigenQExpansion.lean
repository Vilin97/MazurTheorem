/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.ModularCurve.HeckeDifferentialQExpansion
import Mathlib.LinearAlgebra.Eigenspace.Pi

/-!
# Simultaneous Hecke eigenvectors and q-expansions

A commuting family of endomorphisms of a nonzero finite-dimensional vector space over an
algebraically closed field has a common nonzero eigenvector.  The proof here is the elementary
dimension induction: a non-scalar member has a proper nonzero eigenspace, and commutativity makes
that eigenspace invariant under the whole family.

The second half of the file applies this result to a finite-dimensional Hecke module equipped with
an injective, cuspidal, Hecke-equivariant q-expansion map.  It produces an actual nonzero
simultaneous eigen-expansion for the explicit weight-two operators and proves that its coefficient
of `q` is nonzero using `coeff_one_ne_zero_of_simultaneousEigenDifferential`.

This is purely linear algebra plus the checked formal-series operator.  Constructing the geometric
Hecke module and proving that its geometric q-expansion map is injective and equivariant remain
separate modular-curve inputs.
-/

namespace MazurTorsion.ModularCurve

open Function Module Set

universe u v w

namespace SimultaneousEigenQExpansion

variable {K : Type u} [Field K] [IsAlgClosed K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {ι : Type w}

/-- A commuting family of endomorphisms of a nonzero finite-dimensional vector space over an
algebraically closed field has a common nonzero eigenvector. -/
theorem exists_simultaneousEigenvector [Nontrivial V]
    (T : ι → Module.End K V)
    (hcomm : Pairwise fun i j ↦ Commute (T i) (T j)) :
    ∃ (v : V) (eigenvalue : ι → K),
      v ≠ 0 ∧ ∀ i, T i v = eigenvalue i • v := by
  classical
  generalize hdim : finrank K V = d
  induction d using Nat.strong_induction_on generalizing V with
  | h d ih =>
      by_cases hscalar : ∀ i, ∃ μ : K, T i = μ • (1 : Module.End K V)
      · choose eigenvalue heigenvalue using hscalar
        obtain ⟨v, hv⟩ := exists_ne (0 : V)
        refine ⟨v, eigenvalue, hv, fun i ↦ ?_⟩
        rw [heigenvalue i]
        simp
      · push Not at hscalar
        obtain ⟨i, hi⟩ := hscalar
        obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (T i)
        let E : Submodule K V := (T i).eigenspace μ
        have hE_ne_bot : E ≠ ⊥ := hμ
        have hE_ne_top : E ≠ ⊤ := by
          intro hE
          apply hi μ
          ext x
          have hx : x ∈ E := by rw [hE]; exact Submodule.mem_top
          have hx' : T i x = μ • x := Module.End.mem_eigenspace_iff.mp hx
          simpa using hx'
        have hcomm_all (j k : ι) : Commute (T j) (T k) := by
          rcases eq_or_ne j k with rfl | hjk
          · exact Commute.refl _
          · exact hcomm hjk
        have hmaps (j : ι) : MapsTo (T j) E E := by
          intro x hx
          apply Module.End.mem_eigenspace_iff.mpr
          calc
            T i (T j x) = T j (T i x) := by
              exact LinearMap.congr_fun (hcomm_all i j).eq x
            _ = T j (μ • x) := by rw [Module.End.mem_eigenspace_iff.mp hx]
            _ = μ • T j x := by rw [map_smul]
        let T' : ι → Module.End K E := fun j ↦ (T j).restrict (hmaps j)
        have hcomm' : Pairwise fun j k ↦ Commute (T' j) (T' k) := by
          intro j k hjk
          ext x
          change T j (T k (x : V)) = T k (T j (x : V))
          exact LinearMap.congr_fun (hcomm hjk).eq x
        have hdimE : finrank K E < d := by
          rw [← hdim]
          exact Submodule.finrank_lt hE_ne_top
        letI : Nontrivial E := Submodule.nontrivial_iff_ne_bot.mpr hE_ne_bot
        obtain ⟨v, eigenvalue, hv, heigen⟩ :=
          ih (finrank K E) hdimE T' hcomm' rfl
        refine ⟨(v : V), eigenvalue, ?_, fun j ↦ ?_⟩
        · intro h
          apply hv
          apply Subtype.ext
          exact h
        · exact congrArg Subtype.val (heigen j)

omit [IsAlgClosed K] [FiniteDimensional K V] in
/-- Transport a simultaneous eigenvector through an injective, Hecke-equivariant q-expansion map.
The zero constant coefficient is the cusp condition.  The first positive coefficient is forced to
be nonzero by the explicit weight-two Hecke recursion. -/
theorem qExpansion_coeff_one_ne_zero_of_simultaneousEigenvector
    (level : {n : ℕ // 0 < n})
    (T : {n : ℕ // 0 < n} → Module.End K V)
    (qExpansion : V →ₗ[K] PowerSeries K)
    (hqInjective : Function.Injective qExpansion)
    (hcuspidal : ∀ v, PowerSeries.coeff 0 (qExpansion v) = 0)
    (hHeckeEquivariant : ∀ n v,
      qExpansion (T n v) =
        HeckeDifferentialQExpansion.weightTwoHeckeQExpansion level n (qExpansion v))
    (v : V) (hv : v ≠ 0)
    (eigenvalue : {n : ℕ // 0 < n} → K)
    (heigen : ∀ n, T n v = eigenvalue n • v) :
    qExpansion v ≠ 0 ∧
      (∀ n, HeckeDifferentialQExpansion.weightTwoHeckeQExpansion level n (qExpansion v) =
        eigenvalue n • qExpansion v) ∧
      PowerSeries.coeff 1 (qExpansion v) ≠ 0 := by
  have hq_ne_zero : qExpansion v ≠ 0 := by
    intro hq
    apply hv
    apply hqInjective
    simpa using hq
  have hqEigen : ∀ n,
      HeckeDifferentialQExpansion.weightTwoHeckeQExpansion level n (qExpansion v) =
        eigenvalue n • qExpansion v := by
    intro n
    rw [← hHeckeEquivariant, heigen, map_smul]
  refine ⟨hq_ne_zero, hqEigen, ?_⟩
  exact
    HeckeDifferentialQExpansion.coeff_one_ne_zero_of_simultaneousEigenDifferential
      (qExpansion v) hq_ne_zero (hcuspidal v)
      (HeckeDifferentialQExpansion.weightTwoHeckeQExpansion level) eigenvalue
      (fun n ↦ HeckeDifferentialQExpansion.coeff_one_weightTwoHeckeQExpansion
        level n (qExpansion v)) hqEigen

/-- An injective, cuspidal, equivariant q-expansion map on a nonzero finite-dimensional commuting
Hecke module supplies a nonzero simultaneous eigen-expansion with nonzero coefficient of `q`. -/
theorem exists_simultaneousEigen_qExpansion_coeff_one_ne_zero [Nontrivial V]
    (level : {n : ℕ // 0 < n})
    (T : {n : ℕ // 0 < n} → Module.End K V)
    (hcomm : Pairwise fun m n ↦ Commute (T m) (T n))
    (qExpansion : V →ₗ[K] PowerSeries K)
    (hqInjective : Function.Injective qExpansion)
    (hcuspidal : ∀ v, PowerSeries.coeff 0 (qExpansion v) = 0)
    (hHeckeEquivariant : ∀ n v,
      qExpansion (T n v) =
        HeckeDifferentialQExpansion.weightTwoHeckeQExpansion level n (qExpansion v)) :
    ∃ (v : V) (eigenvalue : {n : ℕ // 0 < n} → K),
      v ≠ 0 ∧ qExpansion v ≠ 0 ∧
        (∀ n, HeckeDifferentialQExpansion.weightTwoHeckeQExpansion level n (qExpansion v) =
          eigenvalue n • qExpansion v) ∧
        PowerSeries.coeff 1 (qExpansion v) ≠ 0 := by
  obtain ⟨v, eigenvalue, hv, heigen⟩ := exists_simultaneousEigenvector T hcomm
  obtain ⟨hq, hqEigen, hcoeff⟩ :=
    qExpansion_coeff_one_ne_zero_of_simultaneousEigenvector level T qExpansion
      hqInjective hcuspidal hHeckeEquivariant v hv eigenvalue heigen
  exact ⟨v, eigenvalue, hv, hq, hqEigen, hcoeff⟩

end SimultaneousEigenQExpansion

end MazurTorsion.ModularCurve

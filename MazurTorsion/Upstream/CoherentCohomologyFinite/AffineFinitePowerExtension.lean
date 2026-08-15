/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineExtensionData
import MazurTorsion.Upstream.CoherentCohomologyFinite.FinitePowerClearing

/-!
# Uniform extension on an affine basic open

Quasicoherent affine localization extends one section after multiplying by a
power of the basic-open equation.  Over a finite family of sections the same
power can be chosen uniformly.
-/

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.QuasicoherentTilde

variable {R : CommRingCat.{u}}

namespace BasicOpenExtensionData

/-- A finite family of sections on `D(f)` extends to the ambient open after
multiplication by one common power of `f`. -/
theorem exists_uniform_extension
    {M : (Spec R).Modules} {V : (Spec R).Opens}
    (hV : BasicOpenExtensionData M V)
    (f : R) (hf : PrimeSpectrum.basicOpen f ≤ V)
    {ι : Type*} [Finite ι]
    (s : ι → Γ(M, PrimeSpectrum.basicOpen f)) :
    ∃ (N : ℕ) (t : ι → Γ(M, V)), ∀ i,
      M.presheaf.map (homOfLE hf).op (t i) =
        sectionSmul (f ^ N) (s i) := by
  let ρ := restrictionLinearMap (M := M) hf
  have hpre : ∀ i, ∃ (n : ℕ) (t : Γ(M, V)),
      ρ t = sectionSmul (f ^ n) (s i) := by
    intro i
    obtain ⟨n, t, ht⟩ := hV.existence f hf (s i)
    exact ⟨n, t, ht⟩
  obtain ⟨N, t, ht⟩ :=
    @MazurTorsion.AlgebraicGeometry.CoherentCohomology.exists_uniform_pow_smul_preimage
      R _ Γ(M, V) Γ(M, PrimeSpectrum.basicOpen f)
      _ _ (sectionModule V)
      (sectionModule (PrimeSpectrum.basicOpen f))
      ι _ ρ f s hpre
  exact ⟨N, t, ht⟩

/-- If each member of a finite family of ambient sections vanishes on
`D(f)`, then a common power of `f` annihilates every member. -/
theorem exists_uniform_pow_smul_eq_zero_of_restrict_eq_zero
    {M : (Spec R).Modules} {V : (Spec R).Opens}
    (hV : BasicOpenExtensionData M V)
    (f : R) (hf : PrimeSpectrum.basicOpen f ≤ V)
    {ι : Type*} [Finite ι] (t : ι → Γ(M, V))
    (ht : ∀ i,
      M.presheaf.map (homOfLE hf).op (t i) = 0) :
    ∃ N : ℕ, ∀ i, sectionSmul (f ^ N) (t i) = 0 := by
  apply
    @MazurTorsion.AlgebraicGeometry.CoherentCohomology.exists_uniform_pow_smul_eq_zero
      R _ Γ(M, V) _ (sectionModule V) ι _ f t
  intro i
  exact hV.uniqueness f hf (t i) (ht i)

end BasicOpenExtensionData

end AlgebraicGeometry.QuasicoherentTilde

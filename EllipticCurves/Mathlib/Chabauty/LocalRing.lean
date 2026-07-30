/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
-- Vendored from the Chabauty project (`Chabauty/ForMathlib/LocalRing.lean`).

module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.Data.Nat.Prime.Basic

public import Mathlib.RingTheory.Coprime.Lemmas

@[expose] public section

/-!
# Units in a local ring of prescribed residue characteristic

In a local ring `O` whose maximal ideal contains a prime `p` (equivalently, of residue
characteristic `p`), every integer prime to `p` is a unit.
-/


open IsLocalRing

/-- Integers prime to `p` are units in a local ring whose maximal ideal contains `p`
(equivalently, of residue characteristic `p`). -/
theorem isUnit_natCast_of_not_dvd {O : Type*} [CommRing O] [IsLocalRing O] {p : ℕ}
    (hp : p.Prime) (hpmem : (p : O) ∈ maximalIdeal O) {n : ℕ} (hn : ¬ p ∣ n) :
    IsUnit (n : O) := by
  by_contra hu
  have hmem : (n : O) ∈ maximalIdeal O := hu
  obtain ⟨a, b, hab⟩ := (hp.coprime_iff_not_dvd.mpr hn).symm.cast (R := O)
  have h1 : (1 : O) ∈ maximalIdeal O := by
    rw [← hab]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ hpmem)
  exact (maximalIdeal.isMaximal O).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)

/-- In a local ring, elements with distinct residues differ by a unit. -/
theorem isUnit_sub_of_residue_ne {O : Type*} [CommRing O] [IsLocalRing O] {a b : O}
    (h : residue O a ≠ residue O b) : IsUnit (a - b) := by
  refine notMem_maximalIdeal.mp fun hmem ↦ h ?_
  have := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rw [map_sub] at this
  exact sub_eq_zero.mp this

end

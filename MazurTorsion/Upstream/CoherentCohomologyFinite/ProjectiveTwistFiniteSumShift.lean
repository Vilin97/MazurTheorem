/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectivePositiveTwistAcyclicity
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveBaseTwistGeneration

/-!
# Shifting finite sums of integer projective twists

If a functor sends every `𝒪(m)` to `𝒪(m+n)` and preserves finite
coproducts, it sends any finite sum of integer twists to a finite sum whose
degrees become nonnegative once `n` is large enough.
-/


open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open SerreTwist

variable {R : Type} [CommRing R]
variable {d : ℕ}

/--
A finite-coproduct-preserving functor which shifts every integer twist by
`n` carries a finite sum of twists to the correspondingly shifted sum.
-/
theorem isBaseFiniteNonnegativeTwistSum_map_of_shift
    (F : (scheme R d).Modules ⥤ (scheme R d).Modules)
    [PreservesFiniteCoproducts F]
    (n : ℕ)
    (hOInt :
      ∀ m : ℤ,
        Nonempty
          (F.obj (OInt R d m) ≅
            OInt R d (m + (n : ℤ))))
    {ι : Type} (hι : Fintype ι)
    (degree : ι → ℤ)
    (E : (scheme R d).Modules)
    (eE :
      Nonempty
        (E ≅
          @finiteIntegerSum R inferInstance d ι hι degree))
    (hdegree : ∀ i, 0 ≤ degree i + (n : ℤ)) :
    IsBaseFiniteNonnegativeTwistSum R d (F.obj E) := by
  letI : Fintype ι := hι
  let degree' : ι → ℤ :=
    fun i => degree i + (n : ℤ)
  let eShift (i : ι) :
      F.obj (OInt R d (degree i)) ≅
        OInt R d (degree' i) :=
    Classical.choice (hOInt (degree i))
  let eSum :
      F.obj (finiteIntegerSum R d degree) ≅
        finiteIntegerSum R d degree' :=
    PreservesCoproduct.iso F
        (fun i => OInt R d (degree i)) ≪≫
      HasColimit.isoOfNatIso
        (Discrete.natIso fun i => eShift i.as)
  exact
    ⟨ι, hι, degree',
      hdegree,
      ⟨F.mapIso (Classical.choice eE) ≪≫ eSum⟩⟩

/--
For a family of finite-coproduct-preserving twist functors satisfying
`F n (𝒪(m)) ≅ 𝒪(m+n)`, every finite integer-twist sum is eventually sent
to a finite sum of nonnegative twists.
-/
theorem eventually_isBaseFiniteNonnegativeTwistSum_map
    (F : ℕ → (scheme R d).Modules ⥤ (scheme R d).Modules)
    [∀ n, PreservesFiniteCoproducts (F n)]
    (hOInt :
      ∀ (n : ℕ) (m : ℤ),
        Nonempty
          ((F n).obj (OInt R d m) ≅
            OInt R d (m + (n : ℤ))))
    (E : (scheme R d).Modules)
    (hE : IsBaseFiniteIntegerTwistSum R d E) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      IsBaseFiniteNonnegativeTwistSum R d
        ((F n).obj E) := by
  obtain ⟨ι, hι, degree, eE⟩ := hE
  letI : Fintype ι := hι
  let b : ℕ :=
    Finset.univ.sup fun i : ι =>
      Int.toNat (-degree i)
  refine ⟨b, fun n hn => ?_⟩
  apply
    isBaseFiniteNonnegativeTwistSum_map_of_shift
      (F n) n (hOInt n) hι degree E eE
  intro i
  have hib :
      Int.toNat (-degree i) ≤ b :=
    Finset.le_sup
      (f := fun j : ι => Int.toNat (-degree j))
      (Finset.mem_univ i)
  have hinNat :
      Int.toNat (-degree i) ≤ n :=
    hib.trans hn
  have hinInt :
      (Int.toNat (-degree i) : ℤ) ≤
        (n : ℤ) := by
    exact_mod_cast hinNat
  by_cases hnonnegative : 0 ≤ degree i
  · omega
  · have hnegative :
        0 ≤ -degree i := by
      omega
    have hcast :
        (Int.toNat (-degree i) : ℤ) =
          -degree i :=
      Int.toNat_of_nonneg hnegative
    omega

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

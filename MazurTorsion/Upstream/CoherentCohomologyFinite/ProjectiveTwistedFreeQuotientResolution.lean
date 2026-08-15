/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.CoherentKernel
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteAcyclicQuotientResolution
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveBaseTwistGeneration
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveFactorization

/-!
# Finite twisted-free quotient resolutions on projective space

Iterating the finite twisted-free presentation theorem produces a
quotient resolution of any prescribed finite length.  Coherence of
successive kernels is supplied by Noetherianity.
-/


open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open SerreTwist

variable {R : Type} [CommRing R] [IsNoetherianRing R]
variable {d : ℕ}

/--
Every coherent module on projective space admits a finite quotient
resolution of any prescribed length by finite sums of integer twists.
-/
theorem exists_finiteIntegerTwistSum_quotientResolution
    (hcoordinate :
      ∀ N : ℕ,
        IntegerOverChartCoordinateTransition R d N)
    (M : (scheme R d).Modules)
    [M.IsFiniteType] [M.IsQuasicoherent]
    (r : ℕ) :
    ∃ Z : (scheme R d).Modules,
      CoherentModule Z ∧
        FiniteQuotientResolution
          (IsBaseFiniteIntegerTwistSum R d) r M Z := by
  letI : IsLocallyNoetherian (scheme R d) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (toSpec R d)
  induction r generalizing M with
  | zero =>
      exact
        ⟨M, ⟨inferInstance, inferInstance⟩,
          FiniteQuotientResolution.nil M⟩
  | succ r ih =>
      obtain ⟨E, e, hepi, hEcoherent, hEtwist⟩ :=
        exists_baseFiniteIntegerTwistSum_epi
          R d hcoordinate M
      letI : E.IsFiniteType := hEcoherent.1
      letI : E.IsQuasicoherent := hEcoherent.2
      letI : Epi e := hepi
      have hkernel :
          CoherentModule (kernel e) :=
        Scheme.Modules.kernel_isFiniteType_and_isQuasicoherent e
      letI : (kernel e).IsFiniteType := hkernel.1
      letI : (kernel e).IsQuasicoherent := hkernel.2
      obtain ⟨Z, hZ, T⟩ := ih (kernel e)
      exact
        ⟨Z, hZ,
          FiniteQuotientResolution.cons
            E e hepi hEtwist T⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

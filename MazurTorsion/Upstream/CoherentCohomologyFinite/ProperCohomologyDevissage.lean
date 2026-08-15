/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.BoundedSheafCohomologyDevissage
import MazurTorsion.Upstream.CoherentCohomologyFinite.CoherentKernel
import MazurTorsion.Upstream.CoherentCohomologyFinite.NoetherianReduction
import MazurTorsion.Upstream.CoherentCohomologyFinite.SeparatedAffineCoverBound

/-!
# Proper coherent cohomology from finite-cohomology presentations

Properness over a field supplies a concrete uniform cohomological bound:
the cardinality of a finite affine cover.  Coherence is stable under the
kernels appearing in quotient presentations.  This file combines those
facts with bounded descending dévissage, isolating the one geometric input
still required in applications: construction of enough quotients whose
cohomology is already known to be finite.
-/


open CategoryTheory Limits AlgebraicGeometry TensorProduct
open TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

noncomputable local instance properCohomologyAddCommGroup
    {Z : TopCat.{0}} (G : Z.Sheaf AddCommGrpCat.{0}) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H G n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

/-- The finite-type quasicoherent modules used as the coherent class on a
locally Noetherian scheme. -/
def CoherentModule {X : Scheme.{0}} (M : X.Modules) : Prop :=
  M.IsFiniteType ∧ M.IsQuasicoherent

/--
Let `X` be proper over `ℚ`.  If every coherent module is a quotient of an
object with finite rationalized cohomology in every degree, then every
coherent module has finite rationalized cohomology.

The kernel condition needed for descending induction is discharged
internally by coherence of kernels on a locally Noetherian scheme.
-/
theorem proper_coherent_cohomology_finite_of_presentations
    {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of ℚ)) [IsProper f]
    (Good : X.Modules → Prop)
    (hpresentation :
      ∀ (Y : X.Modules) [Y.IsFiniteType] [Y.IsQuasicoherent],
        ∃ (E : X.Modules) (e : E ⟶ Y),
          Epi e ∧ CoherentModule E ∧ Good E)
    (hgood :
      ∀ (E : X.Modules), Good E → ∀ n : ℕ,
        Module.Finite ℚ (ℚ ⊗[ℤ] E.sheaf.H n))
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent]
    (n : ℕ) :
    Module.Finite ℚ (ℚ ⊗[ℤ] M.sheaf.H n) := by
  letI : IsNoetherian X :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.isNoetherian_of_isProper_to_field f
  letI : X.IsSeparated :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.schemeIsSeparated_of_isProper_to_field f
  let bound :=
    Fintype.card
      (Option (Scheme.finiteAffineSubcover X).I₀)
  apply
    rationalizedSheafH_finite_of_bounded_quotient_presentations
      CoherentModule Good bound
  · intro Y hY q hq
    letI : Y.IsFiniteType := hY.1
    letI : Y.IsQuasicoherent := hY.2
    apply
      Scheme.Modules.subsingleton_H_of_finiteAffineCover_card_le
        Y q
    dsimp [bound] at hq ⊢
    omega
  · intro Y hY
    letI : Y.IsFiniteType := hY.1
    letI : Y.IsQuasicoherent := hY.2
    obtain ⟨E, e, hepi, hEcoherent, hE⟩ :=
      hpresentation Y
    letI : E.IsFiniteType := hEcoherent.1
    letI : E.IsQuasicoherent := hEcoherent.2
    letI : Epi e := hepi
    have hkernel :
        (kernel e).IsFiniteType ∧
          (kernel e).IsQuasicoherent :=
      Scheme.Modules.kernel_isFiniteType_and_isQuasicoherent e
    exact ⟨E, e, hepi, hE, hkernel⟩
  · exact hgood
  · exact ⟨inferInstance, inferInstance⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology

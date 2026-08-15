/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistFiniteSumCoherence
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveStandardCoverEpimorphism

/-!
# Assembling generators from integer Serre twists

A finite family of maps from integer twists has a canonical map from their
coproduct.  Pullback of this map to a standard chart agrees, through the
coproduct comparison isomorphism, with the coproduct of the pulled-back maps.
Consequently chartwise generation implies global generation.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

variable (k : Type) [CommRing k] (d : ℕ)

/-- The map out of a finite sum of integer twists determined by its
components. -/
def finiteIntegerSumDesc {ι : Type} [Fintype ι]
    (degree : ι → ℤ) {M : (scheme k d).Modules}
    (component : ∀ i, OInt k d (degree i) ⟶ M) :
    finiteIntegerSum k d degree ⟶ M :=
  Sigma.desc component

/-- Pulling back a map out of a finite sum of twists gives the coproduct of
the pulled-back component maps, after the canonical coproduct comparison. -/
theorem standardChartPullback_finiteIntegerSumDesc
    {ι : Type} [Fintype ι] (degree : ι → ℤ)
    {M : (scheme k d).Modules}
    (component : ∀ i, OInt k d (degree i) ⟶ M)
    (j : Fin (d + 1)) :
    (PreservesCoproduct.iso
        (Scheme.Modules.pullback ((cover k d).f j))
        (fun i => OInt k d (degree i))).inv ≫
      (Scheme.Modules.pullback ((cover k d).f j)).map
        (finiteIntegerSumDesc k d degree component) =
      Sigma.desc (fun i =>
        (Scheme.Modules.pullback ((cover k d).f j)).map
          (component i)) := by
  simpa only [finiteIntegerSumDesc, PreservesCoproduct.inv_hom] using
    sigmaComparison_map_desc
      (Scheme.Modules.pullback ((cover k d).f j))
      (fun i => OInt k d (degree i)) M component

/-- A finite family of integer-twist maps which generates after pullback to
every standard chart generates globally. -/
theorem finiteIntegerSumDesc_epi_of_standardChart_epi
    {ι : Type} [Fintype ι] (degree : ι → ℤ)
    {M : (scheme k d).Modules}
    (component : ∀ i, OInt k d (degree i) ⟶ M)
    (hcomponent : ∀ j : Fin (d + 1),
      Epi (Sigma.desc (fun i =>
        (Scheme.Modules.pullback ((cover k d).f j)).map
          (component i)))) :
    Epi (finiteIntegerSumDesc k d degree component) := by
  apply epi_of_standardChartPullback_epi k d
  intro j
  letI : Epi (Sigma.desc (fun i =>
      (Scheme.Modules.pullback ((cover k d).f j)).map
        (component i))) :=
    hcomponent j
  rw [← standardChartPullback_finiteIntegerSumDesc
    k d degree component j] at this
  exact epi_of_epi
    (PreservesCoproduct.iso
      (Scheme.Modules.pullback ((cover k d).f j))
      (fun i => OInt k d (degree i))).inv
    ((Scheme.Modules.pullback ((cover k d).f j)).map
      (finiteIntegerSumDesc k d degree component))

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteCoproductSubfamily
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveTwistGeneratorAssembly

/-!
# Combining twisted generators from all projective charts

For every standard chart, suppose a finite family of global maps from
integer Serre twists generates after restriction to that chart.  The
dependent sum of all these finite families is still finite.  Its
coproduct map is an epimorphism on every chart, hence globally.
-/


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

variable (k : Type) [CommRing k] (d : ℕ)

/--
Finite chart-anchored families of global twist maps assemble to one
epimorphism from a finite sum of integer twists.
-/
theorem finiteIntegerSumDesc_epi_of_anchorFamilies
    {M : (scheme k d).Modules}
    (count : Fin (d + 1) → ℕ)
    (degree : ∀ j, Fin (count j) → ℤ)
    (component :
      ∀ j a, OInt k d (degree j a) ⟶ M)
    (hanchor :
      ∀ j : Fin (d + 1),
        Epi
          (Limits.Sigma.desc
            (fun a =>
              (Scheme.Modules.pullback ((cover k d).f j)).map
                (component j a)))) :
    Epi
      (finiteIntegerSumDesc k d
        (fun p : Σ j, Fin (count j) => degree p.1 p.2)
        (fun p => component p.1 p.2)) := by
  let combinedDegree :
      (Σ j, Fin (count j)) → ℤ :=
    fun p => degree p.1 p.2
  let combinedComponent :
      ∀ p : Σ j, Fin (count j),
        OInt k d (combinedDegree p) ⟶ M :=
    fun p => component p.1 p.2
  apply finiteIntegerSumDesc_epi_of_standardChart_epi
    k d combinedDegree combinedComponent
  intro j
  apply
    epi_sigmaDesc_of_epi_subfamily
      (fun p : Σ l, Fin (count l) =>
        (Scheme.Modules.pullback ((cover k d).f j)).obj
          (OInt k d (combinedDegree p)))
      (fun a : Fin (count j) =>
        (Scheme.Modules.pullback ((cover k d).f j)).obj
          (OInt k d (degree j a)))
      (fun a => ⟨j, a⟩)
      (fun _ => 𝟙 _)
      (fun p =>
        (Scheme.Modules.pullback ((cover k d).f j)).map
          (combinedComponent p))
  simpa only [Category.id_comp, combinedDegree,
    combinedComponent] using hanchor j

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteEventualUniformBound
import MazurTorsion.Upstream.CoherentCohomologyFinite.RationalAlgebraFlat
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveSerreVanishingAffineRestriction
import MazurTorsion.Upstream.CoherentCohomologyFinite.SeparatedAffineCoverBound

/-!
# A uniform relative Serre bound on a finite affine base cover

For a compact separated locally Noetherian rational scheme, the
canonical finite affine family has only finitely many nonempty
intersections.  Affine-local relative Serre vanishing can therefore be
made uniform over all those intersections.
-/


open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace
namespace IsRelativeProjectiveFactorization

open SerreTwist
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafCechComparison

variable {Y S : Scheme.{0}}
  {s : S ⟶ Spec (CommRingCat.of ℚ)}
  {f : Y ⟶ S}

/-- One common twist degree makes all nonempty inverse-image
intersections of the canonical finite affine base family acyclic in
positive degree. -/
theorem eventually_finiteAffineIntersections_restrict_sheafH_subsingleton
    [CompactSpace S] [S.IsSeparated] [IsLocallyNoetherian S]
    (h : IsRelativeProjectiveFactorization s f)
    (M : Y.Modules)
    [M.IsFiniteType] [M.IsQuasicoherent]
    (hrestrict : h.AffineRestrictionTwistCompatible M)
    (hpushforward : h.AffineTwistPushforwardCompatible) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      ∀ (t : Finset
          (Option (Scheme.finiteAffineSubcover S).I₀)),
        t.Nonempty →
        ∀ q : ℕ, 0 < q →
          Subsingleton
            ((((relativeProjectiveSerreTwistEquivalence
              ℚ h.chosenDimension h.chosenProjectiveMap
              (n : ℤ)).functor.obj M).restrict
                (f ⁻¹ᵁ finiteIntersection
                  (Scheme.finiteAffineOpenFamily S) t).ι).sheaf.H q) := by
  classical
  let ι :=
    Option (Scheme.finiteAffineSubcover S).I₀
  let V : ι → S.Opens :=
    Scheme.finiteAffineOpenFamily S
  let I := {t : Finset ι // t.Nonempty}
  let P : I → ℕ → Prop :=
    fun t n =>
      ∀ q : ℕ, 0 < q →
        Subsingleton
          ((((relativeProjectiveSerreTwistEquivalence
            ℚ h.chosenDimension h.chosenProjectiveMap
            (n : ℤ)).functor.obj M).restrict
              (f ⁻¹ᵁ finiteIntersection V t.1).ι).sheaf.H q)
  have hP :
      ∀ t : I, ∃ b : ℕ, ∀ n : ℕ, b ≤ n → P t n := by
    intro t
    let U : S.Opens := finiteIntersection V t.1
    have hU : IsAffineOpen U := by
      dsimp only [U, V, ι]
      exact
        Scheme.finiteIntersection_finiteAffineOpenFamily_isAffineOpen
          S t.1 t.2
    letI : Algebra ℚ Γ(S, U) :=
      (affineOpenCoefficientMap s U hU).hom.toAlgebra
    letI : Module.Flat ℤ Γ(S, U) :=
      moduleFlat_int_of_algebra_rat Γ(S, U)
    letI : IsNoetherianRing Γ(S, U) :=
      IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    simpa only [P, U] using
      h.eventually_restrict_relativeProjectiveSerreTwist_sheafH_subsingleton
        M hrestrict hpushforward U hU
  obtain ⟨b, hb⟩ :=
    exists_uniform_eventual_bound P hP
  refine ⟨b, fun n hn t ht q hq => ?_⟩
  exact hb n hn ⟨t, ht⟩ q hq

end IsRelativeProjectiveFactorization
end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

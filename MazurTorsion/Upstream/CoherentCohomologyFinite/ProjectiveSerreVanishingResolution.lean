/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.BaseRingModuleSheafFunctor
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteAcyclicQuotientResolution
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectivePositiveTwistAcyclicity
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveStandardCoverModuleExt
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveTwistedFreeQuotientResolution
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAffineQuasicoherent

/-!
# Serre vanishing from an exact family of twists

A coherent module admits a finite quotient resolution by finite sums of
integer Serre twists.  If an exact functorial family of twists eventually
moves every such finite sum into nonnegative degrees, one common parameter
makes every middle object acyclic.  Dimension shifting through a resolution
of length `d`, together with the standard-cover cohomological bound on
`ℙ^d`, then proves positive-degree vanishing.

This file deliberately separates that homological argument from the
construction of the twisting functors by descent.
-/


open CategoryTheory Limits AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
open SerreTwist

variable {R : Type} [CommRing R] [Module.Flat ℤ R]
  [IsNoetherianRing R]
variable {d : ℕ}

local instance projectiveSpaceOverBaseForSerreVanishing :
    (scheme R d).Over (Spec (CommRingCat.of R)) :=
  ⟨toSpec R d⟩

/-- A base-linear sheaf is represented by the module sheaf of a finite
sum of nonnegative integer twists. -/
def IsModuleSheafOfBaseFiniteNonnegativeTwistSum
    (Y :
      Sheaf (Opens.grothendieckTopology (scheme R d))
        (ModuleCat R)) : Prop :=
  ∃ E : (scheme R d).Modules,
    IsBaseFiniteNonnegativeTwistSum R d E ∧
      Nonempty (Y ≅ moduleSheaf (k := R) E)

/--
An exact natural-number-indexed family of twists which eventually sends
each finite integer-twist sum to a nonnegative-twist sum satisfies
eventual positive-degree Serre vanishing on every coherent module.
-/
theorem eventually_moduleSheafExt_subsingleton_of_twistFamily
    (htransition :
      ∀ N : ℕ,
        IntegerOverChartCoordinateTransition R d N)
    (hchart :
      ∀ m : ℤ,
        BaseStandardCoverCoordinatesNatural R d m)
    (F : ℕ → (scheme R d).Modules ⥤ (scheme R d).Modules)
    [∀ n, PreservesFiniteLimits (F n)]
    [∀ n, (F n).PreservesEpimorphisms]
    (hshift :
      ∀ (E : (scheme R d).Modules),
        IsBaseFiniteIntegerTwistSum R d E →
          ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
            IsBaseFiniteNonnegativeTwistSum R d
              ((F n).obj E))
    (hquasicoherent :
      ∀ (n : ℕ) (E : (scheme R d).Modules),
        E.IsQuasicoherent →
          ((F n).obj E).IsQuasicoherent)
    (M : (scheme R d).Modules)
    [M.IsFiniteType] [M.IsQuasicoherent] :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      ∀ q : ℕ, 0 < q →
        Subsingleton
          (Abelian.Ext
            (constantRankOneSheaf (R := R) (scheme R d))
            (moduleSheaf (k := R) ((F n).obj M)) q) := by
  obtain ⟨Z, hZ, T⟩ :=
    exists_finiteIntegerTwistSum_quotientResolution
      htransition M d
  obtain ⟨b, hb⟩ :=
    T.map_eventually
      (IsBaseFiniteIntegerTwistSum R d)
      (IsBaseFiniteNonnegativeTwistSum R d)
      F hshift
  refine ⟨b, fun n hn q hq => ?_⟩
  obtain ⟨Z', ⟨eZ'⟩, Tn⟩ :=
    hb n hn
  let G :=
    moduleSheafFunctor (k := R) (X := scheme R d)
  obtain ⟨ZS, ⟨eZS⟩, TS⟩ :=
    Tn.map
      (IsBaseFiniteNonnegativeTwistSum R d)
      (IsModuleSheafOfBaseFiniteNonnegativeTwistSum
        (R := R) (d := d))
      G
      (fun E hE =>
        ⟨E, hE, ⟨Iso.refl _⟩⟩)
  letI : ((F n).obj Z).IsQuasicoherent :=
    hquasicoherent n Z hZ.2
  letI : Z'.IsQuasicoherent :=
    Scheme.isQuasicoherent_of_iso eZ'.symm
  apply
    TS.ext_subsingleton_of_bound
      (constantRankOneSheaf (R := R) (scheme R d))
      (IsModuleSheafOfBaseFiniteNonnegativeTwistSum
        (R := R) (d := d))
      d
  · intro E hE r hr
    obtain ⟨E₀, hE₀, ⟨eE⟩⟩ := hE
    have htarget :
        Subsingleton
          (Abelian.Ext
            (constantRankOneSheaf (R := R) (scheme R d))
            (moduleSheaf (k := R) E₀) r) := by
      obtain ⟨s, rfl⟩ :=
        Nat.exists_eq_succ_of_ne_zero
          (Nat.ne_of_gt hr)
      exact
        moduleSheafExt_succ_subsingleton_of_nonnegativeTwistSum
          R d hchart E₀ hE₀ s
    let e :
        Abelian.Ext
            (constantRankOneSheaf (R := R) (scheme R d))
            E r ≃+
          Abelian.Ext
            (constantRankOneSheaf (R := R) (scheme R d))
            (moduleSheaf (k := R) E₀) r :=
      ExtAdjunction.postcompIsoAddEquiv
        (X := constantRankOneSheaf (R := R) (scheme R d))
        eE r
    exact
      ⟨fun x y =>
        e.injective (htarget.elim (e x) (e y))⟩
  · intro r hr
    have htarget :
        Subsingleton
          (Abelian.Ext
            (constantRankOneSheaf (R := R) (scheme R d))
            (moduleSheaf (k := R) Z') r) :=
      constantBaseExt_subsingleton_of_dimension_lt
        Z' r hr
    let e :
        Abelian.Ext
            (constantRankOneSheaf (R := R) (scheme R d))
            ZS r ≃+
          Abelian.Ext
            (constantRankOneSheaf (R := R) (scheme R d))
            (moduleSheaf (k := R) Z') r :=
      ExtAdjunction.postcompIsoAddEquiv
        (X := constantRankOneSheaf (R := R) (scheme R d))
        eZS r
    exact
      ⟨fun x y =>
        e.injective (htarget.elim (e x) (e y))⟩
  · exact hq

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteAffineSupportAnnihilation
import MazurTorsion.Upstream.CoherentCohomologyFinite.IdealSheafPowerSubscheme
import MazurTorsion.Upstream.CoherentCohomologyFinite.IdealSheafSubschemeRestrictPullbackUnit
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeModuleOpenCoverIso
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeModuleOpenUnitBaseChangeIso

/-!
# A finite ideal-sheaf thickening supporting a module

For a finite-type quasicoherent module on a Noetherian scheme whose
closed stalk support is contained in the support of an ideal sheaf, one
positive power of that ideal sheaf makes the canonical
pullback--pushforward unit along its closed subscheme an isomorphism.

The exponent is chosen uniformly on a finite affine subcover.  The
affine quotient theorem proves the result on every chart, open base
change identifies those local units with restrictions of the global
unit, and stalkwise descent over the cover finishes the proof.
-/

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/--
A finite-type quasicoherent module supported on an ideal-sheaf support
is pulled back from the closed subscheme defined by one positive power
of that ideal sheaf.
-/
theorem exists_positivePower_isIso_pullbackPushforward_unit
    [IsNoetherian X]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (J : X.IdealSheafData)
    (hSupport : closedStalkSupport F ≤ J.support) :
    ∃ n : ℕ,
      IsIso
        ((pullbackPushforwardAdjunction
          ((J ^ (n + 1)).subschemeι)).unit.app F) := by
  obtain ⟨n, hn⟩ :=
    exists_uniform_succ_pow_isTorsionBySet_on_finiteAffineSubcover
      F J hSupport
  refine ⟨n, ?_⟩
  let f := (J ^ (n + 1)).subschemeι
  let U (i : X.affineCover.finiteSubcover.I₀) :=
    Scheme.finiteAffineSubcoverAffineOpen X i
  letI hLocal
      (i : X.affineCover.finiteSubcover.I₀) :
      IsIso
        ((restrictFunctor (U i).1.ι).map
          ((pullbackPushforwardAdjunction f).unit.app F)) := by
    haveI hRestrictedUnit :
        IsIso
          ((pullbackPushforwardAdjunction
            (f ∣_ (U i).1)).unit.app
              ((restrictFunctor (U i).1.ι).obj F)) := by
      dsimp only [f]
      apply
        isIso_pullbackPushforward_unit_subschemeι_restrict
          F (J ^ (n + 1)) (U i)
      simpa only [U, Scheme.IdealSheafData.ideal_pow,
        Pi.pow_apply] using hn i
    exact
      isIso_restrict_pullbackPushforward_unit_of_restrict
        f (U i).1 F
  apply
    isIso_of_isIso_restrict_openCover
      ((pullbackPushforwardAdjunction f).unit.app F)
      (fun i => (U i).1)
  intro x
  obtain ⟨i, y, hxy⟩ :=
    X.affineCover.finiteSubcover.exists_eq x
  refine ⟨i, ?_⟩
  change x ∈
    (X.affineCover.finiteSubcover.f i).opensRange
  exact ⟨y, hxy⟩

end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.BaseRingQcqsPushforwardCoherence
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAffineQuasicoherent

/-!
# Quasicoherent pushforward to an affine target

The fixed-base localization theorem applies after identifying an affine
target with the spectrum of its ring of global sections.  Pushing back
along that identification gives the corresponding result for an
arbitrary affine scheme.
-/


open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing

variable {X Y : Scheme.{u}}

/-- A quasi-compact, quasi-separated direct image into an affine scheme
is quasicoherent. -/
theorem isQuasicoherent_pushforward_affineTarget
    (f : X ⟶ Y) [IsAffine Y] [QuasiCompact f]
    [QuasiSeparated f] (M : X.Modules)
    [M.IsQuasicoherent] :
    ((pushforward f).obj M).IsQuasicoherent := by
  letI : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace f
  letI : QuasiSeparatedSpace X :=
    quasiSeparatedSpace_of_quasiSeparated f
  letI :
      X.Over
        (Spec (CommRingCat.of Γ(Y, ⊤))) :=
    ⟨f ≫ Y.isoSpec.hom⟩
  haveI :
      ((pushforward
        (f ≫ Y.isoSpec.hom)).obj M).IsQuasicoherent :=
    isQuasicoherent_pushforward_structural
      (k := Γ(Y, ⊤)) M
  rw [show f =
      (f ≫ Y.isoSpec.hom) ≫ Y.isoSpec.inv by
    simp]
  have hsource :
      ((pushforward (f ≫ Y.isoSpec.hom) ⋙
        pushforward Y.isoSpec.inv).obj M).IsQuasicoherent := by
    simp only [Functor.comp_obj]
    infer_instance
  letI := hsource
  exact
    isQuasicoherent_of_iso
      ((pushforwardComp
        (f ≫ Y.isoSpec.hom)
        Y.isoSpec.inv).app M)

end AlgebraicGeometry.Scheme.Modules

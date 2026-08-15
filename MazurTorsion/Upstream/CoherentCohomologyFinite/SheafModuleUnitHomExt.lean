/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleTopSectionHom

/-!
# Extensionality for maps from the unit module sheaf

On a scheme, a morphism from the unit module sheaf is determined by the
image of `1` over the terminal open.  This is the rank-one extensionality
principle used to turn a coordinate calculation on a whole affine overlap
into equality of the corresponding sheaf morphisms.
-/

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M : X.Modules}

/-- Two maps from the unit module sheaf agree if they agree on `1` over
the terminal open. -/
theorem unitHom_ext_top_one
    (f g : SheafOfModules.unit X.ringCatSheaf ⟶ M)
    (h :
      f.val.app (op (⊤ : X.Opens))
          (1 : X.ringCatSheaf.obj.obj (op ⊤)) =
        g.val.app (op (⊤ : X.Opens))
          (1 : X.ringCatSheaf.obj.obj (op ⊤))) :
    f = g := by
  apply M.unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro V
  let i :=
    (homOfLE
      (show V.unop ≤ (⊤ : X.Opens) from le_top)).op
  rw [← PresheafOfModules.sections_property
        (M.unitHomEquiv f) i,
      ← PresheafOfModules.sections_property
        (M.unitHomEquiv g) i]
  exact congrArg (fun z => M.val.map i z) h

end AlgebraicGeometry.Scheme.Modules

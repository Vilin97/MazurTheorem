/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.BaseRingMorphismBasicOpen
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Fixed-base module sheaves on an affine spectrum

On `Spec k` over itself, the fixed-base module sheaf agrees with Mathlib's
`modulesSpecToSheaf` construction.
-/


open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing

variable {k : Type u} [CommRing k]

/-- Sectionwise comparison between the two fixed-`k` sheaf wrappers on
`Spec k`. -/
noncomputable def moduleSheafSpecAppIso
    (N : (Spec (CommRingCat.of k)).Modules)
    (U : (Spec (CommRingCat.of k)).Opensᵒᵖ) :
    (moduleSheaf (k := k) N).obj.obj U ≅
      (modulesSpecToSheaf.obj N).obj.obj U where
  hom :=
    ConcreteCategory.ofHom
      (C := ModuleCat.{u} k)
      { toFun := id
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  inv :=
    ConcreteCategory.ofHom
      (C := ModuleCat.{u} k)
      { toFun := id
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  hom_inv_id := by
    ext x
    rfl
  inv_hom_id := by
    ext x
    rfl

/-- On an affine spectrum over itself, `moduleSheaf` and
`modulesSpecToSheaf` are naturally isomorphic. -/
noncomputable def moduleSheafSpecIso
    (N : (Spec (CommRingCat.of k)).Modules) :
    moduleSheaf (k := k) N ≅
      modulesSpecToSheaf.obj N :=
  ObjectProperty.isoMk _
    (NatIso.ofComponents
      (fun U => moduleSheafSpecAppIso (k := k) N U)
      (fun {U V} i => by
        ext x
        rfl))

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing

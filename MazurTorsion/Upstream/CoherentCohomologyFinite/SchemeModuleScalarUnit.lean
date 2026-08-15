/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeModuleScalarAutomorphism
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafScalar

/-!
# Scalar automorphisms of the unit module

The general scalar automorphism of a scheme module specializes on the unit
module to the rank-one automorphism used in the projective transition
functions.
-/


open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafScalar

/-- On the unit module, the general scalar endomorphism is the original
rank-one multiplication endomorphism. -/
lemma scalarEndomorphism_unit_eq_endomorphism
    {X : Scheme.{u}} (a : Γ(X, ⊤)) :
    Scheme.Modules.scalarEndomorphism
        (SheafOfModules.unit X.ringCatSheaf) a =
      endomorphism a := by
  apply
    (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.injective
  rw [unitHomEquiv_endomorphism]
  refine PresheafOfModules.sections_ext _ _ (fun U => ?_)
  change
    (show X.ringCatSheaf.obj.obj U from
        Scheme.Modules.globalFunctionAt a U) •
        (1 : X.ringCatSheaf.obj.obj U) =
      X.ringCatSheaf.obj.map (homOfLE le_top).op a
  rw [smul_eq_mul, mul_one]
  change
    (X.presheaf.map
      (homOfLE (show U.unop ≤ ⊤ from le_top)).op).hom a =
      (X.presheaf.map
        (homOfLE (show U.unop ≤ ⊤ from le_top)).op).hom a
  rfl

/-- The general scalar isomorphism agrees with `unitIso` on the unit
module. -/
lemma scalarIso_unit_eq_unitIso
    {X : Scheme.{u}} (a : Γ(X, ⊤)ˣ) :
    Scheme.Modules.scalarIso
        (SheafOfModules.unit X.ringCatSheaf) a =
      unitIso a := by
  apply Iso.ext
  exact scalarEndomorphism_unit_eq_endomorphism a.val

/-- Composition of rank-one unit automorphisms multiplies their units. -/
lemma unitIso_mul {X : Scheme.{u}}
    (a b : Γ(X, ⊤)ˣ) :
    unitIso a ≪≫ unitIso b = unitIso (a * b) := by
  apply Iso.ext
  simp only [Iso.trans_hom, unitIso_hom, Units.val_mul]
  exact endomorphism_comp a.val b.val

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.SheafScalar

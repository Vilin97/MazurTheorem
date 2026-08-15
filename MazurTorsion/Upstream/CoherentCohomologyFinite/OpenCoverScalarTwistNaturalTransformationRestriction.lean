/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverScalarTwistNaturalTransformation
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenCoverScalarTwistChartNaturality
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleScalarTwistGluedRestriction

/-!
# Local invertibility of open-cover scalar-twist maps

If a compatible chart function is one on a chosen member of an open
cover, the transported scalar-twist natural map is an isomorphism after
restriction to that member.
-/


open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open CoverDescentData

variable {X : Scheme.{0}} (𝒰 : X.OpenCover)
variable
    (a : ∀ i j,
      Γ(𝒰.gluedCover.V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1)
    (hcocycle :
      CoverUnitCocycleCondition 𝒰.gluedCover a)
    (b : ∀ i, Γ(𝒰.gluedCover.U i, ⊤))
    (hb : CoverScalarSectionCompatibility a b)

/--
The open-cover scalar-twist natural map is locally invertible on every
chart where its defining scalar function is one.
-/
theorem isIso_openCoverScalarTwistNatTrans_restrict_of_eq_one
    (M : X.Modules) (i : 𝒰.I₀)
    (hi : b i = 1) :
    IsIso
      ((pullback (𝒰.f i)).map
        ((openCoverScalarTwistNatTrans
          𝒰 a hself hcocycle b hb).app M)) := by
  let E := modulesToGluedEquivalence 𝒰
  let W := E.functor.obj M
  let φ :=
    (scalarTwistGluedNatTrans
      a hself hcocycle b hb).app W
  letI hφ :
      IsIso
        ((pullback (𝒰.gluedCover.ι i)).map φ) :=
    isIso_scalarTwistGluedNatTrans_restrict_of_eq_one
      a hself hcocycle b hb W i hi
  letI hinverse :
      IsIso
        ((pullback (𝒰.f i)).map
          (E.inverse.map φ)) := by
    change
      IsIso
        ((E.inverse ⋙ pullback (𝒰.f i)).map φ)
    exact
      (NatIso.isIso_map_iff
        (gluedToModulesChartRestrictionNatIso
          𝒰 i) φ).mpr hφ
  change
    IsIso
      ((pullback (𝒰.f i)).map
        (E.unitIso.hom.app M ≫
          E.inverse.map φ))
  rw [Functor.map_comp]
  infer_instance

end AlgebraicGeometry.Scheme.Modules

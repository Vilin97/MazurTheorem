/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.BaseRingModuleSheafPushforward
import MazurTorsion.Upstream.CoherentCohomologyFinite.BaseRingSpecModuleSheaf
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAffineTildeCounit

/-!
# Quasicoherent pushforward for qcqs morphisms

The fixed-base qcqs localization theorem identifies the direct image over
an affine base with a localizing module sheaf.  Affine reconstruction then
shows that the scheme-module pushforward is quasicoherent.
-/


open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing

variable {k : Type u} [CommRing k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]

/-- The topological direct image of the fixed-base module sheaf along the
structural morphism is localizing. -/
theorem isLocalizing_pushforward_structural
    (M : X.Modules) [M.IsQuasicoherent]
    [CompactSpace X] [QuasiSeparatedSpace X] :
    IsLocalizing
      ((TopCat.Sheaf.pushforward
        (ModuleCat.{u} k)
        (X ↘ Spec (CommRingCat.of k)).base).obj
        (moduleSheaf (k := k) M :
          (X.toPresheafedSpace : TopCat).Sheaf
            (ModuleCat.{u} k))) := by
  intro r
  let p := X ↘ Spec (CommRingCat.of k)
  let F :=
    (moduleSheaf (k := k) M :
      (X.toPresheafedSpace : TopCat).Sheaf
        (ModuleCat.{u} k))
  let D : (Spec (CommRingCat.of k)).Opens :=
    PrimeSpectrum.basicOpen r
  let UTop : X.Opens := p ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of k)).Opens)
  let UD : X.Opens := p ⁻¹ᵁ D
  have hTop : UTop = ⊤ := by
    ext x
    simp [UTop]
  have hD :
      UD = baseBasicOpen (k := k) (X := X) ⊤ r := by
    exact (baseBasicOpen_top_eq_preimage (k := k) r).symm
  let eTopCat : F.obj.obj (op UTop) ≅ F.obj.obj (op ⊤) :=
    (F.obj.mapIso (eqToIso hTop).op).symm
  let eDCat :
      F.obj.obj (op UD) ≅
        F.obj.obj
          (op (baseBasicOpen (k := k) (X := X) ⊤ r)) :=
    (F.obj.mapIso (eqToIso hD).op).symm
  let eTop := eTopCat.toLinearEquiv
  let eD := eDCat.toLinearEquiv
  let fPush :
      F.obj.obj (op UTop) →ₗ[k] F.obj.obj (op UD) :=
    ((TopCat.Sheaf.pushforward
      (ModuleCat.{u} k) p.base).obj F).obj.map D.leTop.op |>.hom
  let fBasic :
      F.obj.obj (op ⊤) →ₗ[k]
        F.obj.obj
          (op (baseBasicOpen (k := k) (X := X) ⊤ r)) :=
    sectionRestrictionLinearMap
      (k := k) M (baseBasicOpen_le (k := k) ⊤ r)
  have hloc :=
    BasicOpenExtensionData.isLocalizedModule_baseBasicOpen_of_isCompact_of_isQuasiSeparated
      (k := k) M
      (U := (⊤ : X.Opens))
      isCompact_univ isQuasiSeparated_univ r
  have hsquare :
      eD.toLinearMap ∘ₗ fPush =
        fBasic ∘ₗ eTop.toLinearMap := by
    apply LinearMap.ext
    intro x
    change
      eDCat.hom
          (F.obj.map
            ((Opens.map p.base).map D.leTop).op x) =
        F.obj.map
          (homOfLE
            (baseBasicOpen_le (k := k) ⊤ r)).op
          (eTopCat.hom x)
    change
      (F.obj.map
          ((Opens.map p.base).map D.leTop).op ≫
        eDCat.hom) x =
      (eTopCat.hom ≫
        F.obj.map
          (homOfLE
            (baseBasicOpen_le (k := k) ⊤ r)).op) x
    congr 1
    dsimp only [eDCat, eTopCat]
    simp only [Iso.symm_hom, Functor.mapIso_inv]
    rw [← F.obj.map_comp, ← F.obj.map_comp]
    congr 1
  have hconj :
      IsLocalizedModule (Submonoid.powers r)
        (eD.toLinearMap ∘ₗ fPush ∘ₗ eTop.symm.toLinearMap) := by
    rw [show
      eD.toLinearMap ∘ₗ fPush ∘ₗ eTop.symm.toLinearMap =
        fBasic by
          apply LinearMap.ext
          intro x
          have hx :=
            congrArg
              (fun q :
                F.obj.obj (op UTop) →ₗ[k]
                  F.obj.obj
                    (op (baseBasicOpen
                      (k := k) (X := X) ⊤ r)) =>
                q (eTop.symm x))
              hsquare
          change
            eD (fPush (eTop.symm x)) = fBasic x
          calc
            _ = fBasic (eTop (eTop.symm x)) := by
              exact hx
            _ = fBasic x := by
              rw [eTop.apply_symm_apply]]
    exact hloc
  have hpost :
      IsLocalizedModule (Submonoid.powers r)
        (eD.toLinearMap ∘ₗ fPush) :=
    (IsLocalizedModule.comp_iff_of_bijective_right
      (Submonoid.powers r)
      eTop.symm.toLinearMap
      eTop.symm.bijective).mp hconj
  exact
    (IsLocalizedModule.comp_iff_of_bijective_left
      (Submonoid.powers r)
      eD.toLinearMap eD.bijective).mp hpost

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing

/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.BaseRingModuleSheaf
import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# Basic-open extension data over a fixed affine base

Let `X` be a scheme over `Spec k`.  Every section module of an
`𝒪_X`-module is then a `k`-module, compatibly with restriction.  This file
packages the elementwise existence and uniqueness clauses for localization
at an element of `k`.
-/


open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing

variable {k : Type u} [CommRing k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]

attribute [local instance] sectionsModule

/-- The basic open in `U` cut out by the image of a base-ring element. -/
noncomputable def baseBasicOpen (U : X.Opens) (r : k) : X.Opens :=
  X.basicOpen (algebraMapOnOpen (k := k) U r)

@[sheaf_restrict]
lemma baseBasicOpen_le (U : X.Opens) (r : k) :
    baseBasicOpen (k := k) U r ≤ U :=
  X.basicOpen_le _

/-- Restricting a base basic open to a smaller ambient open is intersection
with that open. -/
lemma baseBasicOpen_res {U V : X.Opens} (hVU : V ≤ U) (r : k) :
    baseBasicOpen (k := k) V r =
      V ⊓ baseBasicOpen (k := k) U r := by
  unfold baseBasicOpen
  rw [← algebraMapOnOpen_apply_restriction
    (k := k) (homOfLE hVU).op r]
  exact X.basicOpen_res
    (f := algebraMapOnOpen (k := k) U r) (homOfLE hVU).op

/-- Base basic opens are monotone in the ambient open. -/
lemma baseBasicOpen_mono {U V : X.Opens} (hVU : V ≤ U) (r : k) :
    baseBasicOpen (k := k) V r ≤
      baseBasicOpen (k := k) U r := by
  rw [baseBasicOpen_res (k := k) hVU r]
  exact inf_le_right

/-- Restriction of module sections, regarded as a map over the fixed base
ring. -/
noncomputable def sectionRestrictionLinearMap
    (M : X.Modules) {U V : X.Opens} (hVU : V ≤ U) :
    Γ(M, U) →ₗ[k] Γ(M, V) :=
  ((moduleSheaf (k := k) M).obj.map (homOfLE hVU).op).hom

@[simp]
lemma sectionRestrictionLinearMap_apply
    (M : X.Modules) {U V : X.Opens} (hVU : V ≤ U)
    (x : Γ(M, U)) :
    sectionRestrictionLinearMap (k := k) M hVU x =
      M.presheaf.map (homOfLE hVU).op x :=
  rfl

/-- Transitivity of restriction, in fixed-base linear form. -/
lemma sectionRestrictionLinearMap_trans
    (M : X.Modules) {U V W : X.Opens}
    (hWV : W ≤ V) (hVU : V ≤ U) (x : Γ(M, U)) :
    sectionRestrictionLinearMap (k := k) M hWV
        (sectionRestrictionLinearMap (k := k) M hVU x) =
      sectionRestrictionLinearMap (k := k) M (hWV.trans hVU) x := by
  change
    (moduleSheaf (k := k) M).obj.map (homOfLE hWV).op
        ((moduleSheaf (k := k) M).obj.map (homOfLE hVU).op x) =
      (moduleSheaf (k := k) M).obj.map
        (homOfLE (hWV.trans hVU)).op x
  erw [← ModuleCat.comp_apply,
    ← (moduleSheaf (k := k) M).obj.map_comp]
  rfl

/-- An extension identity remains an extension identity after shrinking the
ambient open. -/
lemma sectionRestriction_baseBasicOpen
    (M : X.Modules) {U V : X.Opens} (hVU : V ≤ U)
    (r : k) (n : ℕ)
    (x : Γ(M, baseBasicOpen (k := k) U r))
    (y : Γ(M, U))
    (hy :
      sectionRestrictionLinearMap
          (k := k) M (baseBasicOpen_le (k := k) U r) y =
        r ^ n • x) :
    sectionRestrictionLinearMap
        (k := k) M (baseBasicOpen_le (k := k) V r)
        (sectionRestrictionLinearMap (k := k) M hVU y) =
      r ^ n •
        sectionRestrictionLinearMap
          (k := k) M (baseBasicOpen_mono (k := k) hVU r) x := by
  let hD :
      baseBasicOpen (k := k) V r ≤
        baseBasicOpen (k := k) U r :=
    baseBasicOpen_mono (k := k) hVU r
  calc
    sectionRestrictionLinearMap
          (k := k) M (baseBasicOpen_le (k := k) V r)
          (sectionRestrictionLinearMap (k := k) M hVU y) =
        sectionRestrictionLinearMap
          (k := k) M
          ((baseBasicOpen_le (k := k) V r).trans hVU) y :=
      sectionRestrictionLinearMap_trans (k := k) M _ _ y
    _ =
        sectionRestrictionLinearMap
          (k := k) M hD
          (sectionRestrictionLinearMap
            (k := k) M (baseBasicOpen_le (k := k) U r) y) := by
      symm
      exact sectionRestrictionLinearMap_trans (k := k) M _ _ y
    _ = sectionRestrictionLinearMap (k := k) M hD (r ^ n • x) := by
      rw [hy]
    _ = r ^ n • sectionRestrictionLinearMap (k := k) M hD x := by
      rw [map_smul]

/--
The elementwise localization property for a module sheaf on an open `U`.

The scalar is always an element of the fixed base ring `k`; its basic open
is formed from the structural image in `Γ(X,U)`.
-/
structure BasicOpenExtensionData (M : X.Modules) (U : X.Opens) : Prop where
  existence (r : k) (x : Γ(M, baseBasicOpen (k := k) U r)) :
    ∃ (n : ℕ) (y : Γ(M, U)),
      sectionRestrictionLinearMap
          (k := k) M (baseBasicOpen_le (k := k) U r) y =
        r ^ n • x
  uniqueness (r : k) (y : Γ(M, U)) :
    sectionRestrictionLinearMap
          (k := k) M (baseBasicOpen_le (k := k) U r) y = 0 →
      ∃ n : ℕ, r ^ n • y = 0

namespace BasicOpenExtensionData

/-- A family of localization statements supplies basic-open extension
data. -/
theorem of_isLocalizedModule
    (M : X.Modules) (U : X.Opens)
    (h : ∀ r : k,
      IsLocalizedModule (Submonoid.powers r)
        (sectionRestrictionLinearMap
          (k := k) M (baseBasicOpen_le (k := k) U r))) :
    BasicOpenExtensionData (k := k) M U := by
  constructor
  · intro r x
    have hr := h r
    obtain ⟨⟨y, c⟩, hy⟩ :=
      IsLocalizedModule.surj (Submonoid.powers r)
        (sectionRestrictionLinearMap
          (k := k) M (baseBasicOpen_le (k := k) U r)) x
    obtain ⟨n, hn⟩ :=
      (Submonoid.mem_powers_iff c.1 r).mp c.2
    refine ⟨n, y, ?_⟩
    exact hy.symm.trans
      (congrArg (fun a : k => a • x) hn.symm)
  · intro r y hy
    have hr := h r
    have hy' :
        sectionRestrictionLinearMap
            (k := k) M (baseBasicOpen_le (k := k) U r) y =
          sectionRestrictionLinearMap
            (k := k) M (baseBasicOpen_le (k := k) U r) 0 := by
      simpa using hy
    obtain ⟨c, hc⟩ :=
      IsLocalizedModule.exists_of_eq
        (S := Submonoid.powers r)
        (f := sectionRestrictionLinearMap
          (k := k) M (baseBasicOpen_le (k := k) U r)) hy'
    obtain ⟨n, hn⟩ :=
      (Submonoid.mem_powers_iff c.1 r).mp c.2
    refine ⟨n, ?_⟩
    calc
      r ^ n • y = c • y :=
        congrArg (fun a : k => a • y) hn
      _ = c • (0 : Γ(M, U)) := hc
      _ = 0 := smul_zero _

end BasicOpenExtensionData

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing

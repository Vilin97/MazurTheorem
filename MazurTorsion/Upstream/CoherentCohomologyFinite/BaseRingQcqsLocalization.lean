/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.BaseRingAffineLocalization
import MazurTorsion.Upstream.CoherentCohomologyFinite.BaseRingQcqsExtension

/-!
# The fixed-base qcqs localization theorem

Basic-open extension and power-uniqueness give the surjectivity and
equalizer clauses of `IsLocalizedModule`.  The remaining unit clause follows
because the structural image of the defining element is a unit on its own
basic open.
-/


open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing

variable {k : Type u} [CommRing k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]

attribute [local instance] sectionsModule

/-- A base-ring element acts invertibly on module sections over the base
basic open that it defines. -/
lemma isUnit_algebraMap_end_baseBasicOpen
    (M : X.Modules) (U : X.Opens) (r : k) :
    IsUnit
      (algebraMap k
        (Module.End k
          Γ(M, baseBasicOpen (k := k) U r)) r) := by
  rw [Module.End.isUnit_iff]
  have hr :
      IsUnit
        (algebraMapOnOpen
          (k := k) (baseBasicOpen (k := k) U r) r) := by
    have h :=
      RingedSpace.isUnit_res_basicOpen X.toRingedSpace
        (algebraMapOnOpen (k := k) U r)
    change
      IsUnit
        ((X.presheaf.map
          (homOfLE (baseBasicOpen_le (k := k) U r)).op).hom
          (algebraMapOnOpen (k := k) U r)) at h
    rw [algebraMapOnOpen_apply_restriction
      (k := k)
      (homOfLE (baseBasicOpen_le (k := k) U r)).op r] at h
    exact h
  change
    Function.Bijective
      (fun x : Γ(M, baseBasicOpen (k := k) U r) =>
        algebraMapOnOpen
          (k := k) (baseBasicOpen (k := k) U r) r • x)
  exact hr.smul_bijective

namespace BasicOpenExtensionData

/-- Elementwise extension data is equivalent to the three defining clauses
of localization for the fixed-base restriction map. -/
theorem isLocalizedModule
    (M : X.Modules) (U : X.Opens)
    (h : BasicOpenExtensionData (k := k) M U)
    (r : k) :
    IsLocalizedModule (Submonoid.powers r)
      (sectionRestrictionLinearMap
        (k := k) M (baseBasicOpen_le (k := k) U r)) where
  map_units c := by
    obtain ⟨n, hn⟩ :=
      (Submonoid.mem_powers_iff c.1 r).mp c.2
    change IsUnit
      (algebraMap k
        (Module.End k
          Γ(M, baseBasicOpen (k := k) U r)) c.1)
    rw [← hn, map_pow]
    exact (isUnit_algebraMap_end_baseBasicOpen
      (k := k) M U r).pow n
  surj x := by
    obtain ⟨n, y, hy⟩ := h.existence r x
    refine ⟨⟨y,
      ⟨r ^ n,
        (Submonoid.mem_powers_iff (r ^ n) r).mpr
          ⟨n, rfl⟩⟩⟩, ?_⟩
    exact hy.symm
  exists_of_eq {x y} hxy := by
    have hz :
        sectionRestrictionLinearMap
            (k := k) M (baseBasicOpen_le (k := k) U r)
            (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨n, hn⟩ := h.uniqueness r (x - y) hz
    refine ⟨
      ⟨r ^ n,
        (Submonoid.mem_powers_iff (r ^ n) r).mpr
          ⟨n, rfl⟩⟩,
      ?_⟩
    have hzero : r ^ n • x - r ^ n • y = 0 := by
      simpa only [smul_sub] using hn
    exact sub_eq_zero.mp hzero

/--
The fixed-base qcqs localization theorem, reduced only to its affine-open
case.
-/
theorem isLocalizedModule_of_isCompact_of_isQuasiSeparated
    (M : X.Modules)
    (hAffine :
      ∀ (V : X.affineOpens) (r : k),
        IsLocalizedModule (Submonoid.powers r)
          (sectionRestrictionLinearMap
            (k := k) M
            (baseBasicOpen_le (k := k) (V : X.Opens) r)))
    {U : X.Opens} (hU : IsCompact U.1)
    (hU' : IsQuasiSeparated U.1)
    (r : k) :
    IsLocalizedModule (Submonoid.powers r)
      (sectionRestrictionLinearMap
        (k := k) M (baseBasicOpen_le (k := k) U r)) := by
  let hAffineData :
      ∀ V : X.affineOpens,
        BasicOpenExtensionData (k := k) M (V : X.Opens) :=
    fun V =>
      of_isLocalizedModule M (V : X.Opens) (hAffine V)
  exact isLocalizedModule M U
    (of_isCompact_of_isQuasiSeparated
      M hAffineData hU hU') r

/-- Restriction of a quasicoherent module to a base basic open of a compact
quasi-separated open is localization at the defining base-ring element. -/
theorem isLocalizedModule_baseBasicOpen_of_isCompact_of_isQuasiSeparated
    (M : X.Modules) [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsCompact U.1)
    (hU' : IsQuasiSeparated U.1)
    (r : k) :
    IsLocalizedModule (Submonoid.powers r)
      (sectionRestrictionLinearMap
        (k := k) M (baseBasicOpen_le (k := k) U r)) :=
  isLocalizedModule_of_isCompact_of_isQuasiSeparated
    M
    (fun V =>
      isLocalizedModule_baseBasicOpen_of_isAffineOpen M V.2)
    hU hU' r

/-- Elementwise fixed-base basic-open extension data on a compact
quasi-separated open. -/
theorem qcqsBasicOpenExtensionData
    (M : X.Modules) [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsCompact U.1)
    (hU' : IsQuasiSeparated U.1) :
    BasicOpenExtensionData (k := k) M U :=
  of_isCompact_of_isQuasiSeparated
    M (fun V => affineBasicOpenExtensionData M V.2) hU hU'

end BasicOpenExtensionData

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing

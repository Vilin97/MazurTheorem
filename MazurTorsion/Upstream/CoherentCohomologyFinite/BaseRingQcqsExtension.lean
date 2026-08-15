/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.BaseRingBasicOpenExtension
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Qcqs extension of fixed-base module sections

This file adapts the standard qcqs lemma from structure-sheaf sections to
sections of a module sheaf.  The affine case is supplied as
`BasicOpenExtensionData`; compactness makes the annihilating exponent
uniform, while quasi-separatedness controls the overlaps needed for gluing
extensions.
-/


open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing

variable {k : Type u} [CommRing k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]

attribute [local instance] sectionsModule

namespace BasicOpenExtensionData

private theorem exists_section_sup_of_eq_on_inf
    (M : X.Modules) {U V : X.Opens}
    (xU : Γ(M, U)) (xV : Γ(M, V))
    (h :
      sectionRestrictionLinearMap (k := k) M inf_le_left xU =
        sectionRestrictionLinearMap (k := k) M inf_le_right xV) :
    ∃ x : Γ(M, U ⊔ V),
      sectionRestrictionLinearMap (k := k) M le_sup_left x = xU ∧
      sectionRestrictionLinearMap (k := k) M le_sup_right x = xV := by
  classical
  let W : Bool → X.Opens
    | false => U
    | true => V
  let x : ∀ b, Γ(M, W b)
    | false => xU
    | true => xV
  have hx :
      TopCat.Presheaf.IsCompatible
        (moduleSheaf (k := k) M).obj W x := by
    intro i j
    cases i <;> cases j
    · rfl
    · exact h
    · change
        (moduleSheaf (k := k) M).obj.map
            (homOfLE (inf_le_left : V ⊓ U ≤ V)).op xV =
          (moduleSheaf (k := k) M).obj.map
            (homOfLE (inf_le_right : V ⊓ U ≤ U)).op xU
      let e : V ⊓ U ⟶ U ⊓ V := eqToHom (inf_comm V U)
      calc
        _ = (moduleSheaf (k := k) M).obj.map e.op
              ((moduleSheaf (k := k) M).obj.map
                (homOfLE (inf_le_right : U ⊓ V ≤ V)).op xV) := by
          erw [← ModuleCat.comp_apply,
            ← (moduleSheaf (k := k) M).obj.map_comp]
          rfl
        _ = (moduleSheaf (k := k) M).obj.map e.op
              ((moduleSheaf (k := k) M).obj.map
                (homOfLE (inf_le_left : U ⊓ V ≤ U)).op xU) :=
          congrArg
            (fun z => (moduleSheaf (k := k) M).obj.map e.op z)
            h.symm
        _ = _ := by
          erw [← ModuleCat.comp_apply,
            ← (moduleSheaf (k := k) M).obj.map_comp]
          rfl
    · rfl
  have hcover : U ⊔ V ≤ iSup W := by
    rw [sup_le_iff]
    exact ⟨le_iSup W false, le_iSup W true⟩
  let iW : ∀ b, W b ≤ U ⊔ V
    | false => le_sup_left
    | true => le_sup_right
  obtain ⟨y, hy, _⟩ :=
    TopCat.Sheaf.existsUnique_gluing'
      (moduleSheaf (k := k) M) W (U ⊔ V)
      (fun b => homOfLE (iW b)) hcover x hx
  exact ⟨y, hy false, hy true⟩

/--
On a compact open, vanishing after restriction to a base basic open is
killed by a uniform power of the defining base-ring element.
-/
theorem exists_pow_smul_eq_zero_of_restrict_eq_zero_of_isCompact
    (M : X.Modules)
    (hAffine :
      ∀ V : X.affineOpens,
        BasicOpenExtensionData (k := k) M (V : X.Opens))
    {U : X.Opens} (hU : IsCompact U.1)
    (r : k) (y : Γ(M, U))
    (hy :
      sectionRestrictionLinearMap
          (k := k) M (baseBasicOpen_le (k := k) U r) y = 0) :
    ∃ n : ℕ, r ^ n • y = 0 := by
  obtain ⟨s, hs, e⟩ :=
    isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp
      ⟨hU, U.2⟩
  have heq : U = iSup fun i : s => (i.1 : X.Opens) := by
    ext1
    simpa using e
  have hsub (i : s) : (i.1 : X.Opens) ≤ U := by
    rw [heq]
    exact le_iSup (fun j : s => (j.1 : X.Opens)) i
  have hzero (i : s) :
      sectionRestrictionLinearMap
          (k := k) M
          (baseBasicOpen_le (k := k) (i.1 : X.Opens) r)
          (sectionRestrictionLinearMap (k := k) M (hsub i) y) = 0 := by
    let hD :
        baseBasicOpen (k := k) (i.1 : X.Opens) r ≤
          baseBasicOpen (k := k) U r :=
      baseBasicOpen_mono (k := k) (hsub i) r
    calc
      sectionRestrictionLinearMap
            (k := k) M
            (baseBasicOpen_le (k := k) (i.1 : X.Opens) r)
            (sectionRestrictionLinearMap (k := k) M (hsub i) y) =
          sectionRestrictionLinearMap
            (k := k) M
            ((baseBasicOpen_le
              (k := k) (i.1 : X.Opens) r).trans (hsub i)) y :=
        sectionRestrictionLinearMap_trans
          (k := k) M _ _ y
      _ =
          sectionRestrictionLinearMap
            (k := k) M hD
            (sectionRestrictionLinearMap
              (k := k) M
              (baseBasicOpen_le (k := k) U r) y) := by
        symm
        exact sectionRestrictionLinearMap_trans
          (k := k) M _ _ y
      _ = 0 := by
        rw [hy]
        exact map_zero _
  have hpow (i : s) :
      ∃ n : ℕ,
        r ^ n •
          sectionRestrictionLinearMap (k := k) M (hsub i) y = 0 :=
    (hAffine i.1).uniqueness r _ (hzero i)
  choose n hn using hpow
  haveI := hs.to_subtype
  cases nonempty_fintype s
  let N := Finset.univ.sup n
  refine ⟨N, ?_⟩
  subst U
  apply TopCat.Sheaf.eq_of_locally_eq
    (moduleSheaf (k := k) M)
    (fun i : s => (i.1 : X.Opens))
  intro i
  change
    sectionRestrictionLinearMap (k := k) M (hsub i)
        (r ^ N • y) =
      sectionRestrictionLinearMap (k := k) M (hsub i) 0
  rw [map_zero]
  have hni : n i ≤ N :=
    Finset.le_sup (Finset.mem_univ i)
  have hN : N = (N - n i) + n i :=
    (Nat.sub_add_cancel hni).symm
  calc
    sectionRestrictionLinearMap (k := k) M (hsub i)
        (r ^ N • y) =
      r ^ N • sectionRestrictionLinearMap
        (k := k) M (hsub i) y := by
          rw [map_smul]
    _ = 0 := by
      rw [hN, pow_add, mul_smul, hn i, smul_zero]

/--
Sections over a base basic open of a compact quasi-separated open extend
after multiplication by a power of the defining base-ring element.
-/
theorem exists_extension_of_isCompact_of_isQuasiSeparated
    (M : X.Modules)
    (hAffine :
      ∀ V : X.affineOpens,
        BasicOpenExtensionData (k := k) M (V : X.Opens))
    {U : X.Opens} (hU : IsCompact U.1)
    (hU' : IsQuasiSeparated U.1)
    (r : k) (x : Γ(M, baseBasicOpen (k := k) U r)) :
    ∃ (n : ℕ) (y : Γ(M, U)),
      sectionRestrictionLinearMap
          (k := k) M (baseBasicOpen_le (k := k) U r) y =
        r ^ n • x := by
  revert hU' r x
  refine compact_open_induction_on U hU ?_ ?_
  · intro _ r x
    refine ⟨0, 0, ?_⟩
    have hD : baseBasicOpen (k := k) (⊥ : X.Opens) r = ⊥ :=
      le_antisymm (baseBasicOpen_le (k := k) ⊥ r) bot_le
    apply (Scheme.Modules.isSheaf M).section_ext
    intro p hp
    have : (p : X) ∈ (⊥ : X.Opens) := by
      rw [← hD]
      exact hp
    exact this.elim
  · intro S hS V hInd hSV r x
    let A : X.Opens := S ⊔ (V : X.Opens)
    have hSA : S ≤ A := le_sup_left
    have hVA : (V : X.Opens) ≤ A := le_sup_right
    have hDSA :
        baseBasicOpen (k := k) S r ≤
          baseBasicOpen (k := k) A r :=
      baseBasicOpen_mono (k := k) hSA r
    have hDVA :
        baseBasicOpen (k := k) (V : X.Opens) r ≤
          baseBasicOpen (k := k) A r :=
      baseBasicOpen_mono (k := k) hVA r
    let xS : Γ(M, baseBasicOpen (k := k) S r) :=
      sectionRestrictionLinearMap (k := k) M hDSA x
    let xV : Γ(M, baseBasicOpen (k := k) (V : X.Opens) r) :=
      sectionRestrictionLinearMap (k := k) M hDVA x
    obtain ⟨nS, yS, hyS⟩ :=
      hInd (hSV.of_subset Set.subset_union_left) r xS
    obtain ⟨nV, yV, hyV⟩ :=
      (hAffine V).existence r xV
    let W : X.Opens := S ⊓ (V : X.Opens)
    have hWS : W ≤ S := inf_le_left
    have hWV : W ≤ (V : X.Opens) := inf_le_right
    have hWA : W ≤ A := hWS.trans hSA
    have hDWA :
        baseBasicOpen (k := k) W r ≤
          baseBasicOpen (k := k) A r :=
      baseBasicOpen_mono (k := k) hWA r
    let xW : Γ(M, baseBasicOpen (k := k) W r) :=
      sectionRestrictionLinearMap (k := k) M hDWA x
    let ySW : Γ(M, W) :=
      sectionRestrictionLinearMap (k := k) M hWS yS
    let yVW : Γ(M, W) :=
      sectionRestrictionLinearMap (k := k) M hWV yV
    have hxSW :
        sectionRestrictionLinearMap
            (k := k) M
            (baseBasicOpen_mono (k := k) hWS r) xS =
          xW := by
      dsimp only [xS, xW]
      exact sectionRestrictionLinearMap_trans
        (k := k) M _ _ x
    have hxVW :
        sectionRestrictionLinearMap
            (k := k) M
            (baseBasicOpen_mono (k := k) hWV r) xV =
          xW := by
      dsimp only [xV, xW]
      exact sectionRestrictionLinearMap_trans
        (k := k) M _ _ x
    have hySW :
        sectionRestrictionLinearMap
            (k := k) M (baseBasicOpen_le (k := k) W r) ySW =
          r ^ nS • xW := by
      dsimp only [ySW]
      rw [sectionRestriction_baseBasicOpen
        (k := k) M hWS r nS xS yS hyS, hxSW]
    have hyVW :
        sectionRestrictionLinearMap
            (k := k) M (baseBasicOpen_le (k := k) W r) yVW =
          r ^ nV • xW := by
      dsimp only [yVW]
      rw [sectionRestriction_baseBasicOpen
        (k := k) M hWV r nV xV yV hyV, hxVW]
    let z : Γ(M, W) := r ^ nV • ySW - r ^ nS • yVW
    have hz :
        sectionRestrictionLinearMap
            (k := k) M (baseBasicOpen_le (k := k) W r) z = 0 := by
      dsimp only [z]
      rw [map_sub, map_smul, map_smul, hySW, hyVW,
        smul_smul, smul_smul, mul_comm, sub_self]
    have hWcompact : IsCompact W.1 :=
      hSV _ _ Set.subset_union_left S.2 hS
        Set.subset_union_right V.1.2 V.2.isCompact
    obtain ⟨N, hN⟩ :=
      exists_pow_smul_eq_zero_of_restrict_eq_zero_of_isCompact
        M hAffine hWcompact r z hz
    let aS : Γ(M, S) := r ^ (N + nV) • yS
    let aV : Γ(M, (V : X.Opens)) := r ^ (N + nS) • yV
    have ha :
        sectionRestrictionLinearMap (k := k) M hWS aS =
          sectionRestrictionLinearMap (k := k) M hWV aV := by
      apply sub_eq_zero.mp
      calc
        sectionRestrictionLinearMap (k := k) M hWS aS -
              sectionRestrictionLinearMap (k := k) M hWV aV =
            r ^ (N + nV) • ySW -
              r ^ (N + nS) • yVW := by
          dsimp only [aS, aV, ySW, yVW]
          rw [map_smul, map_smul]
        _ = r ^ N • z := by
          dsimp only [z]
          rw [smul_sub, pow_add, pow_add, mul_smul, mul_smul]
        _ = 0 := hN
    obtain ⟨y, hyS', hyV'⟩ :=
      exists_section_sup_of_eq_on_inf M aS aV ha
    let L := N + nS + nV
    refine ⟨L, y, ?_⟩
    let D := baseBasicOpen (k := k) A r
    have hDA : D ≤ A := baseBasicOpen_le (k := k) A r
    have hcover :
        D ≤
          baseBasicOpen (k := k) S r ⊔
            baseBasicOpen (k := k) (V : X.Opens) r := by
      rw [baseBasicOpen_res (k := k) hSA r,
        baseBasicOpen_res (k := k) hVA r, ← inf_sup_right]
      exact le_inf (baseBasicOpen_le (k := k) A r) le_rfl
    apply TopCat.Sheaf.eq_of_locally_eq₂
      (moduleSheaf (k := k) M)
      (homOfLE hDSA) (homOfLE hDVA) hcover
    · calc
        sectionRestrictionLinearMap (k := k) M hDSA
              (sectionRestrictionLinearMap (k := k) M hDA y) =
            sectionRestrictionLinearMap
              (k := k) M
              ((baseBasicOpen_le (k := k) S r).trans hSA) y := by
          rw [sectionRestrictionLinearMap_trans]
        _ = sectionRestrictionLinearMap
              (k := k) M (baseBasicOpen_le (k := k) S r)
              (sectionRestrictionLinearMap (k := k) M hSA y) := by
          symm
          exact sectionRestrictionLinearMap_trans (k := k) M _ _ y
        _ = sectionRestrictionLinearMap
              (k := k) M (baseBasicOpen_le (k := k) S r) aS := by
          rw [hyS']
        _ = r ^ (N + nV) •
              sectionRestrictionLinearMap
                (k := k) M (baseBasicOpen_le (k := k) S r) yS := by
          dsimp only [aS]
          rw [map_smul]
        _ = r ^ (N + nV) • (r ^ nS • xS) := by rw [hyS]
        _ = r ^ L • xS := by
          dsimp only [L]
          rw [smul_smul, ← pow_add]
          congr 2
          omega
        _ = sectionRestrictionLinearMap (k := k) M hDSA
              (r ^ L • x) := by
          dsimp only [xS]
          rw [map_smul]
    · calc
        sectionRestrictionLinearMap (k := k) M hDVA
              (sectionRestrictionLinearMap (k := k) M hDA y) =
            sectionRestrictionLinearMap
              (k := k) M
              ((baseBasicOpen_le
                (k := k) (V : X.Opens) r).trans hVA) y := by
          rw [sectionRestrictionLinearMap_trans]
        _ = sectionRestrictionLinearMap
              (k := k) M
              (baseBasicOpen_le (k := k) (V : X.Opens) r)
              (sectionRestrictionLinearMap (k := k) M hVA y) := by
          symm
          exact sectionRestrictionLinearMap_trans (k := k) M _ _ y
        _ = sectionRestrictionLinearMap
              (k := k) M
              (baseBasicOpen_le (k := k) (V : X.Opens) r) aV := by
          rw [hyV']
        _ = r ^ (N + nS) •
              sectionRestrictionLinearMap
                (k := k) M
                (baseBasicOpen_le (k := k) (V : X.Opens) r) yV := by
          dsimp only [aV]
          rw [map_smul]
        _ = r ^ (N + nS) • (r ^ nV • xV) := by rw [hyV]
        _ = r ^ L • xV := by
          dsimp only [L]
          rw [smul_smul, ← pow_add]
        _ = sectionRestrictionLinearMap (k := k) M hDVA
              (r ^ L • x) := by
          dsimp only [xV]
          rw [map_smul]

/-- Affine basic-open extension data propagates to every compact
quasi-separated open. -/
theorem of_isCompact_of_isQuasiSeparated
    (M : X.Modules)
    (hAffine :
      ∀ V : X.affineOpens,
        BasicOpenExtensionData (k := k) M (V : X.Opens))
    {U : X.Opens} (hU : IsCompact U.1)
    (hU' : IsQuasiSeparated U.1) :
    BasicOpenExtensionData (k := k) M U where
  existence r x :=
    exists_extension_of_isCompact_of_isQuasiSeparated
      M hAffine hU hU' r x
  uniqueness r y hy :=
    exists_pow_smul_eq_zero_of_restrict_eq_zero_of_isCompact
      M hAffine hU r y hy

end BasicOpenExtensionData

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing

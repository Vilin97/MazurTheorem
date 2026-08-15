/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineBasicOpenPresentation

/-!
# Extension data for sections on affine schemes

The two clauses below are the elementwise form of the statement that
sections on distinguished opens are localizations of sections on a larger
open.  They are stable under passage to a smaller distinguished open.
-/

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.QuasicoherentTilde

variable {R : CommRingCat.{u}}

local instance sectionModule
    {M : (Spec R).Modules} (U : (Spec R).Opens) :
    Module R Γ(M, U) :=
  inferInstanceAs <| Module R
    ((AlgebraicGeometry.modulesSpecToSheaf.obj M).obj.obj (.op U))

local instance sectionDistribMulAction
    {M : (Spec R).Modules} (U : (Spec R).Opens) :
    DistribMulAction R Γ(M, U) :=
  @Module.toDistribMulAction R Γ(M, U) _ _ (sectionModule U)

local instance sectionMulAction
    {M : (Spec R).Modules} (U : (Spec R).Opens) :
    MulAction R Γ(M, U) :=
  @DistribMulAction.toMulAction R Γ(M, U) _ _
    (sectionDistribMulAction U)

local instance sectionDistribSMul
    {M : (Spec R).Modules} (U : (Spec R).Opens) :
    DistribSMul R Γ(M, U) :=
  @DistribMulAction.toDistribSMul R Γ(M, U) _ _
    (sectionDistribMulAction U)

local instance sectionSMulZeroClass
    {M : (Spec R).Modules} (U : (Spec R).Opens) :
    SMulZeroClass R Γ(M, U) :=
  @DistribSMul.toSMulZeroClass R Γ(M, U) _
    (sectionDistribSMul U)

/-- The affine-coordinate scalar action on sections, with its codomain
made explicit so that elaboration does not unfold the opaque `Γ` wrapper. -/
noncomputable abbrev sectionSmul
    {M : (Spec R).Modules} {U : (Spec R).Opens}
    (r : R) (s : Γ(M, U)) : Γ(M, U) :=
  @SMul.smul R Γ(M, U) (sectionModule U).toSMul r s

theorem sectionSmul_eq_algebraMapEnd
    {M : (Spec R).Modules} {U : (Spec R).Opens}
    (r : R) (x : Γ(M, U)) :
    sectionSmul r x =
      (algebraMap R (Module.End R Γ(M, U)) r) x :=
  rfl

theorem sectionSmul_mul
    {M : (Spec R).Modules} {U : (Spec R).Opens}
    (r s : R) (x : Γ(M, U)) :
    sectionSmul (r * s) x = sectionSmul r (sectionSmul s x) := by
  exact @SemigroupAction.mul_smul R Γ(M, U) _
    (sectionMulAction (M := M) U).toSemigroupAction r s x

theorem sectionSmul_comm
    {M : (Spec R).Modules} {U : (Spec R).Opens}
    (r s : R) (x : Γ(M, U)) :
    sectionSmul r (sectionSmul s x) =
      sectionSmul s (sectionSmul r x) := by
  exact (sectionSmul_mul r s x).symm.trans
    ((congrArg (fun a : R => sectionSmul a x) (mul_comm r s)).trans
      (sectionSmul_mul s r x))

theorem sectionSmul_sub
    {M : (Spec R).Modules} {U : (Spec R).Opens}
    (r : R) (x y : Γ(M, U)) :
    sectionSmul r (x - y) = sectionSmul r x - sectionSmul r y := by
  exact @smul_sub R Γ(M, U) _ (sectionDistribSMul (M := M) U)
    r x y

theorem sectionSmul_zero
    {M : (Spec R).Modules} {U : (Spec R).Opens} (r : R) :
    sectionSmul r (0 : Γ(M, U)) = 0 := by
  exact @smul_zero R Γ(M, U) _
    (sectionSMulZeroClass (M := M) U) r

/-- Restriction maps commute with the explicit affine-coordinate scalar
action on sections. -/
theorem map_sectionSmul_Spec
    {M : (Spec R).Modules} {U V : (Spec R).Opens}
    (hUV : .op V ⟶ .op U) (r : R) (x : Γ(M, V)) :
    M.presheaf.map hUV (sectionSmul r x) =
      sectionSmul r (M.presheaf.map hUV x) := by
  exact M.map_smul_Spec hUV r x

/-- The standard restriction isomorphism for a map of affine spectra
intertwines the explicit coordinate-ring actions on sections. -/
theorem restrictAppIso_sectionSmul_Spec
    {S : CommRingCat.{u}} (f : R ⟶ S)
    [IsOpenImmersion (Spec.map f)]
    {M : (Spec R).Modules} {U : (Spec S).Opens}
    (r : R) (x : Γ(M.restrict (Spec.map f), U)) :
    (M.restrictAppIso (Spec.map f) U).hom
        (sectionSmul (M := M.restrict (Spec.map f)) (f r) x) =
      sectionSmul (M := M) r
        ((M.restrictAppIso (Spec.map f) U).hom x) := by
  exact Scheme.Modules.restrictAppIso_smul_Spec f r x

/-- Existence and uniqueness up to powers for extending sections from
distinguished opens. -/
structure BasicOpenExtensionData
    (M : (Spec R).Modules) (V : (Spec R).Opens) where
  existence (f : R) (hf : PrimeSpectrum.basicOpen f ≤ V)
      (s : Γ(M, PrimeSpectrum.basicOpen f)) :
    ∃ (n : ℕ) (t : Γ(M, V)),
      M.presheaf.map (homOfLE hf).op t = sectionSmul (f ^ n) s
  uniqueness (f : R) (hf : PrimeSpectrum.basicOpen f ≤ V)
      (t : Γ(M, V)) :
    M.presheaf.map (homOfLE hf).op t =
        (0 : Γ(M, PrimeSpectrum.basicOpen f)) →
      ∃ n : ℕ, sectionSmul (f ^ n) t = 0

namespace BasicOpenExtensionData

/-- Restriction of sections as a linear map over the affine coordinate
ring. -/
noncomputable def restrictionLinearMap
    {M : (Spec R).Modules}
    {A B : (Spec R).Opens} (hAB : A ≤ B) :
    Γ(M, B) →ₗ[R] Γ(M, A) :=
  ((AlgebraicGeometry.modulesSpecToSheaf.obj M).presheaf.map
    (homOfLE hAB).op).hom

@[simp]
theorem restrictionLinearMap_apply
    {M : (Spec R).Modules}
    {A B : (Spec R).Opens} (hAB : A ≤ B)
    (s : Γ(M, B)) :
    restrictionLinearMap hAB s =
      M.presheaf.map (homOfLE hAB).op s :=
  rfl

theorem restriction_trans
    {M : (Spec R).Modules}
    {A B C : (Spec R).Opens}
    (hAB : A ≤ B) (hBC : B ≤ C) (s : Γ(M, C)) :
    M.presheaf.map (homOfLE hAB).op
        (M.presheaf.map (homOfLE hBC).op s) =
      M.presheaf.map (homOfLE (hAB.trans hBC)).op s := by
  rw [← AddCommGrpCat.comp_apply, ← M.presheaf.map_comp]
  rfl

/-- Restriction maps commute with the scalar action from the affine
coordinate ring. -/
theorem restriction_smul
    {M : (Spec R).Modules}
    {A B : (Spec R).Opens} (hAB : A ≤ B)
    (r : R) (s : Γ(M, B)) :
    restrictionLinearMap hAB (sectionSmul r s) =
      sectionSmul r (restrictionLinearMap hAB s) :=
  map_smul _ r s

/-- Restriction maps preserve zero, in the section-module notation. -/
theorem restriction_zero
    {M : (Spec R).Modules}
    {A B : (Spec R).Opens} (hAB : A ≤ B) :
    M.presheaf.map (homOfLE hAB).op
        (0 : Γ(M, B)) = (0 : Γ(M, A)) :=
  map_zero _

/-- Extension data descends from an open to a contained distinguished
open. -/
theorem of_le {M : (Spec R).Modules} {V : (Spec R).Opens}
    (g : R) (hg : PrimeSpectrum.basicOpen g ≤ V)
    (hV : BasicOpenExtensionData M V) :
    BasicOpenExtensionData M (PrimeSpectrum.basicOpen g) where
  existence f hfg s := by
    obtain ⟨n, t, ht⟩ :=
      hV.existence f (le_trans hfg hg) s
    exact ⟨n, M.presheaf.map (homOfLE hg).op t,
      (restriction_trans hfg hg t).trans ht⟩
  uniqueness f hfg t ht := by
    obtain ⟨n, t', ht'⟩ := hV.existence g hg t
    have hmap :
        M.presheaf.map (homOfLE hfg).op
            (sectionSmul (g ^ n) t) =
          sectionSmul (g ^ n)
            (M.presheaf.map (homOfLE hfg).op t) := by
      exact M.map_smul_Spec (homOfLE hfg).op (g ^ n) t
    have hz :
        M.presheaf.map (homOfLE (hfg.trans hg)).op t' = 0 := by
      have h₁ :
          M.presheaf.map (homOfLE (hfg.trans hg)).op t' =
            M.presheaf.map (homOfLE hfg).op
              (M.presheaf.map (homOfLE hg).op t') :=
        (restriction_trans hfg hg t').symm
      have h₂ :
          M.presheaf.map (homOfLE hfg).op
              (M.presheaf.map (homOfLE hg).op t') =
            M.presheaf.map (homOfLE hfg).op
              (sectionSmul (g ^ n) t) :=
        congrArg (fun x => M.presheaf.map (homOfLE hfg).op x) ht'
      have h₄ :
          sectionSmul (g ^ n)
              (M.presheaf.map (homOfLE hfg).op t) = 0 := by
        rw [ht]
        exact @smul_zero R Γ(M, PrimeSpectrum.basicOpen f) _
          (sectionSMulZeroClass (M := M)
            (PrimeSpectrum.basicOpen f)) (g ^ n)
      exact h₁.trans (h₂.trans (hmap.trans h₄))
    obtain ⟨m, hm⟩ :=
      hV.uniqueness _ (le_trans hfg hg) t' hz
    have hreg :
        @IsSMulRegular R Γ(M, PrimeSpectrum.basicOpen g)
          (sectionModule (M := M) (PrimeSpectrum.basicOpen g)).toSMul
          (g ^ n) :=
      @IsSMulRegular.pow R Γ(M, PrimeSpectrum.basicOpen g) g _
        (sectionMulAction (M := M) (PrimeSpectrum.basicOpen g)) n
        (M.isSMulRegular_of_le_basicOpen le_rfl)
    refine ⟨m, @IsSMulRegular.right_eq_zero_of_smul
      R Γ(M, PrimeSpectrum.basicOpen g) _
      (sectionSMulZeroClass (M := M) (PrimeSpectrum.basicOpen g))
      (g ^ n) (sectionSmul (f ^ m) t) hreg ?_⟩
    have h₁ :
        sectionSmul (g ^ n) (sectionSmul (f ^ m) t) =
          sectionSmul (f ^ m) (sectionSmul (g ^ n) t) := by
      exact
        (@SemigroupAction.mul_smul R
          Γ(M, PrimeSpectrum.basicOpen g) _
          (sectionMulAction (M := M)
            (PrimeSpectrum.basicOpen g)).toSemigroupAction
          (g ^ n) (f ^ m) t).symm.trans
          ((congrArg (fun r : R => sectionSmul r t)
            (mul_comm (g ^ n) (f ^ m))).trans
          (@SemigroupAction.mul_smul R
            Γ(M, PrimeSpectrum.basicOpen g) _
            (sectionMulAction (M := M)
              (PrimeSpectrum.basicOpen g)).toSemigroupAction
            (f ^ m) (g ^ n) t))
    have h₂ :
        sectionSmul (f ^ m) (sectionSmul (g ^ n) t) =
          sectionSmul (f ^ m)
            (M.presheaf.map (homOfLE hg).op t') := by
      rw [ht']
    have h₃ :
        sectionSmul (f ^ m)
            (M.presheaf.map (homOfLE hg).op t') =
          M.presheaf.map (homOfLE hg).op
            (sectionSmul (f ^ m) t') := by
      exact (M.map_smul_Spec
        (homOfLE hg).op (f ^ m) t').symm
    have h₄ :
        M.presheaf.map (homOfLE hg).op
            (sectionSmul (f ^ m) t') = 0 := by
      rw [hm]
      exact map_zero _
    exact h₁.trans (h₂.trans (h₃.trans h₄))

end BasicOpenExtensionData

end AlgebraicGeometry.QuasicoherentTilde

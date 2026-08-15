/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineExtensionData

/-!
# Gluing affine extension data

Extension and power-uniqueness of sections glue across a finite cover by
distinguished opens.  This is the elementwise affine patching argument.
-/

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.QuasicoherentTilde

variable {R : CommRingCat.{u}}

local instance sectionModuleForGluing
    {M : (Spec R).Modules} (U : (Spec R).Opens) :
    Module R Γ(M, U) :=
  inferInstanceAs <| Module R
    ((AlgebraicGeometry.modulesSpecToSheaf.obj M).obj.obj (.op U))

local instance sectionDistribMulActionForGluing
    {M : (Spec R).Modules} (U : (Spec R).Opens) :
    DistribMulAction R Γ(M, U) :=
  @Module.toDistribMulAction R Γ(M, U) _ _
    (sectionModuleForGluing U)

local instance sectionMulActionForGluing
    {M : (Spec R).Modules} (U : (Spec R).Opens) :
    MulAction R Γ(M, U) :=
  @DistribMulAction.toMulAction R Γ(M, U) _ _
    (sectionDistribMulActionForGluing U)

local instance sectionDistribSMulForGluing
    {M : (Spec R).Modules} (U : (Spec R).Opens) :
    DistribSMul R Γ(M, U) :=
  @DistribMulAction.toDistribSMul R Γ(M, U) _ _
    (sectionDistribMulActionForGluing U)

local instance sectionSMulZeroClassForGluing
    {M : (Spec R).Modules} (U : (Spec R).Opens) :
    SMulZeroClass R Γ(M, U) :=
  @DistribSMul.toSMulZeroClass R Γ(M, U) _
    (sectionDistribSMulForGluing U)

local infixr:73 " •ₛ " => sectionSmul

namespace BasicOpenExtensionData

private theorem presheaf_map_comp_apply
    {M : (Spec R).Modules}
    {A B C : (Spec R).Opensᵒᵖ}
    (a : A ⟶ B) (b : B ⟶ C)
    (x : M.presheaf.obj A) :
    M.presheaf.map b (M.presheaf.map a x) =
      M.presheaf.map (a ≫ b) x := by
  rw [← AddCommGrpCat.comp_apply, ← M.presheaf.map_comp]

/-- Extension data glues across a finite distinguished-open cover. -/
theorem of_eq_iSup_basicOpen
    {M : (Spec R).Modules} (V : (Spec R).Opens)
    {ι : Type*} [Finite ι] (g : ι → R)
    (hg : V = ⨆ i, PrimeSpectrum.basicOpen (g i))
    (h₁ : ∀ i, BasicOpenExtensionData M
      (PrimeSpectrum.basicOpen (g i))) :
    BasicOpenExtensionData M V := by
  have h₂ (i j : ι) :
      BasicOpenExtensionData M
        (PrimeSpectrum.basicOpen (g i * g j)) :=
    .of_le _ (PrimeSpectrum.basicOpen_mul_le_left _ _) (h₁ i)
  have hgle (i : ι) :
      PrimeSpectrum.basicOpen (g i) ≤ V := by
    rw [hg]
    exact le_iSup_of_le _ le_rfl
  have hug (i : ι) (m : ℕ) :=
    (Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen
      (M := M) (U := PrimeSpectrum.basicOpen (g i))
      (g i) le_rfl).pow m
  refine ⟨fun f hf s => ?_, fun f hf t hs => ?_⟩
  · have hfgi (i : ι) :
        PrimeSpectrum.basicOpen (f * g i) ≤
          PrimeSpectrum.basicOpen (g i) :=
      PrimeSpectrum.basicOpen_mul_le_right f (g i)
    let s' (i : ι) :
        Γ(M, PrimeSpectrum.basicOpen (f * g i)) :=
      M.presheaf.map
        (homOfLE (PrimeSpectrum.basicOpen_mul_le_left
          f (g i))).op s
    obtain ⟨N, t, ht⟩ :
        ∃ (N : ℕ)
          (t : ∀ i, Γ(M, PrimeSpectrum.basicOpen (g i))),
          ∀ i, f ^ N •ₛ s' i =
            M.presheaf.map (homOfLE (hfgi i)).op (t i) := by
      have hi (i : ι) :
          ∃ (n : ℕ)
            (t : Γ(M, PrimeSpectrum.basicOpen (g i))),
            f ^ n •ₛ s' i =
              M.presheaf.map (homOfLE (hfgi i)).op t := by
        obtain ⟨n, t', ht'⟩ :=
          (h₁ i).existence (f * g i) (hfgi i) (s' i)
        erw [mul_pow, sectionSmul_mul, sectionSmul_comm] at ht'
        obtain ⟨ψ, hψ⟩ := IsUnit.exists_right_inv (hug i n)
        use n, ψ t'
        have hreg :
            @IsSMulRegular R
              Γ(M, PrimeSpectrum.basicOpen (f * g i))
              (sectionModuleForGluing (M := M)
                (PrimeSpectrum.basicOpen (f * g i))).toSMul
              (g i ^ n) :=
          @IsSMulRegular.pow R
            Γ(M, PrimeSpectrum.basicOpen (f * g i)) (g i) _
            (sectionMulActionForGluing (M := M)
              (PrimeSpectrum.basicOpen (f * g i))) n
            (M.isSMulRegular_of_le_basicOpen
              (PrimeSpectrum.basicOpen_mul_le_right f (g i)))
        apply hreg
        have hψ' : g i ^ n •ₛ ψ t' = t' := by
          letI : Module R Γ(M, PrimeSpectrum.basicOpen (g i)) :=
            sectionModuleForGluing (M := M)
              (PrimeSpectrum.basicOpen (g i))
          have happ := congrArg (fun q => q t') hψ
          rw [← map_pow] at happ
          rw [Module.End.mul_apply] at happ
          exact (sectionSmul_eq_algebraMapEnd
            (M := M) (U := PrimeSpectrum.basicOpen (g i))
            (g i ^ n) (ψ t')).trans happ
        calc
          g i ^ n •ₛ (f ^ n •ₛ s' i) =
              restrictionLinearMap (hfgi i) t' :=
            ht'.symm.trans
              (restrictionLinearMap_apply (hfgi i) t').symm
          _ = restrictionLinearMap (hfgi i)
              (g i ^ n •ₛ ψ t') :=
            congrArg (restrictionLinearMap (hfgi i)) hψ'.symm
          _ = g i ^ n •ₛ restrictionLinearMap (hfgi i) (ψ t') :=
            restriction_smul (hfgi i) (g i ^ n) (ψ t')
      choose n t' ht' using hi
      have hnle (i : ι) : n i ≤ ⨆ i, n i :=
        le_ciSup (Finite.bddAbove_range _) _
      have hN (i : ι) :
          ⨆ i, n i = ((⨆ i, n i) - n i) + n i := by
        grind
      refine ⟨⨆ i, n i,
        fun i => f ^ ((⨆ i, n i) - n i) •ₛ t' i,
        fun i => ?_⟩
      conv_lhs => rw [hN i]
      erw [pow_add, sectionSmul_mul, ht' i]
      exact (restriction_smul (hfgi i)
        (f ^ ((⨆ i, n i) - n i)) (t' i)).symm
    obtain ⟨K, hK⟩ :
        ∃ K : ℕ, ∀ i j : ι,
          M.presheaf.map
              (homOfLE
                (PrimeSpectrum.basicOpen_mul_le_left
                  (g i) (g j))).op
              (f ^ K •ₛ t i) =
            M.presheaf.map
              (homOfLE
                (PrimeSpectrum.basicOpen_mul_le_right
                  (g i) (g j))).op
              (f ^ K •ₛ t j) := by
      have hij (i j : ι) :
          ∃ m : ℕ,
            M.presheaf.map
                (homOfLE
                  (PrimeSpectrum.basicOpen_mul_le_left
                    (g i) (g j))).op
                (f ^ m •ₛ t i) =
              M.presheaf.map
                (homOfLE
                  (PrimeSpectrum.basicOpen_mul_le_right
                    (g i) (g j))).op
                (f ^ m •ₛ t j) := by
        have hu := (h₂ i j).uniqueness
          (f * (g i * g j))
          (PrimeSpectrum.basicOpen_mul_le_right _ _)
          (M.presheaf.map
              (homOfLE
                (PrimeSpectrum.basicOpen_mul_le_left
                  (g i) (g j))).op (t i) -
            M.presheaf.map
              (homOfLE
                (PrimeSpectrum.basicOpen_mul_le_right
                  (g i) (g j))).op (t j)) (by
            have hfgigi :
                PrimeSpectrum.basicOpen (f * (g i * g j)) ≤
                  PrimeSpectrum.basicOpen (f * g i) := by
              rw [← mul_assoc]
              exact PrimeSpectrum.basicOpen_mul_le_left _ _
            have hfgigj :
                PrimeSpectrum.basicOpen (f * (g i * g j)) ≤
                  PrimeSpectrum.basicOpen (f * g j) := by
              rw [mul_comm (g i) (g j), ← mul_assoc]
              exact PrimeSpectrum.basicOpen_mul_le_left _ _
            let hpair :
                PrimeSpectrum.basicOpen (f * (g i * g j)) ≤
                  PrimeSpectrum.basicOpen (g i * g j) :=
              PrimeSpectrum.basicOpen_mul_le_right _ _
            let hleft :
                PrimeSpectrum.basicOpen (g i * g j) ≤
                  PrimeSpectrum.basicOpen (g i) :=
              PrimeSpectrum.basicOpen_mul_le_left _ _
            let hright :
                PrimeSpectrum.basicOpen (g i * g j) ≤
                  PrimeSpectrum.basicOpen (g j) :=
              PrimeSpectrum.basicOpen_mul_le_right _ _
            let hfi :
                PrimeSpectrum.basicOpen (f * g i) ≤
                  PrimeSpectrum.basicOpen f :=
              PrimeSpectrum.basicOpen_mul_le_left _ _
            let hfj :
                PrimeSpectrum.basicOpen (f * g j) ≤
                  PrimeSpectrum.basicOpen f :=
              PrimeSpectrum.basicOpen_mul_le_left _ _
            have ei :
                M.presheaf.map (homOfLE hpair).op
                    (M.presheaf.map (homOfLE hleft).op (t i)) =
                  f ^ N •ₛ
                    (show Γ(M,
                      PrimeSpectrum.basicOpen (f * (g i * g j))) from
                      M.presheaf.map (homOfLE hfgigi).op (s' i)) := by
              have e₁ :=
                (restriction_trans hpair hleft (t i)).trans
                  (restriction_trans hfgigi (hfgi i) (t i)).symm
              have e₂ :
                  M.presheaf.map (homOfLE hfgigi).op
                      (M.presheaf.map (homOfLE (hfgi i)).op (t i)) =
                    M.presheaf.map (homOfLE hfgigi).op
                      (f ^ N •ₛ s' i) :=
                congrArg (fun x => M.presheaf.map
                  (homOfLE hfgigi).op x) (ht i).symm
              have e₃ :
                  M.presheaf.map (homOfLE hfgigi).op
                      (f ^ N •ₛ s' i) =
                    f ^ N •ₛ M.presheaf.map
                      (homOfLE hfgigi).op (s' i) :=
                M.map_smul_Spec (homOfLE hfgigi).op
                  (f ^ N) (s' i)
              exact e₁.trans (e₂.trans e₃)
            have ej :
                M.presheaf.map (homOfLE hpair).op
                    (M.presheaf.map (homOfLE hright).op (t j)) =
                  f ^ N •ₛ
                    (show Γ(M,
                      PrimeSpectrum.basicOpen (f * (g i * g j))) from
                      M.presheaf.map (homOfLE hfgigj).op (s' j)) := by
              have e₁ :=
                (restriction_trans hpair hright (t j)).trans
                  (restriction_trans hfgigj (hfgi j) (t j)).symm
              have e₂ :
                  M.presheaf.map (homOfLE hfgigj).op
                      (M.presheaf.map (homOfLE (hfgi j)).op (t j)) =
                    M.presheaf.map (homOfLE hfgigj).op
                      (f ^ N •ₛ s' j) :=
                congrArg (fun x => M.presheaf.map
                  (homOfLE hfgigj).op x) (ht j).symm
              have e₃ :
                  M.presheaf.map (homOfLE hfgigj).op
                      (f ^ N •ₛ s' j) =
                    f ^ N •ₛ M.presheaf.map
                      (homOfLE hfgigj).op (s' j) :=
                M.map_smul_Spec (homOfLE hfgigj).op
                  (f ^ N) (s' j)
              exact e₁.trans (e₂.trans e₃)
            have es :
                M.presheaf.map (homOfLE hfgigi).op (s' i) =
                  M.presheaf.map (homOfLE hfgigj).op (s' j) := by
              exact (restriction_trans hfgigi hfi s).trans
                (restriction_trans hfgigj hfj s).symm
            rw [map_sub, ei, ej, es]
            exact sub_self _)
        obtain ⟨m, hm⟩ := hu
        have hm' :
            (f * (g i * g j)) ^ m •ₛ
                restrictionLinearMap
                  (PrimeSpectrum.basicOpen_mul_le_left
                    (g i) (g j)) (t i) =
              (f * (g i * g j)) ^ m •ₛ
                restrictionLinearMap
                  (PrimeSpectrum.basicOpen_mul_le_right
                    (g i) (g j)) (t j) := by
          erw [← sub_eq_zero, ← sectionSmul_sub]
          exact hm
        use m
        calc
          restrictionLinearMap
              (PrimeSpectrum.basicOpen_mul_le_left
                (g i) (g j)) (f ^ m •ₛ t i) =
              f ^ m •ₛ restrictionLinearMap
                (PrimeSpectrum.basicOpen_mul_le_left
                  (g i) (g j)) (t i) :=
            restriction_smul
              (PrimeSpectrum.basicOpen_mul_le_left
                (g i) (g j)) (f ^ m) (t i)
          _ = f ^ m •ₛ restrictionLinearMap
                (PrimeSpectrum.basicOpen_mul_le_right
                  (g i) (g j)) (t j) := by
            have hreg :
                @IsSMulRegular R
                  Γ(M, PrimeSpectrum.basicOpen (g i * g j))
                  (sectionModuleForGluing (M := M)
                    (PrimeSpectrum.basicOpen (g i * g j))).toSMul
                  ((g i * g j) ^ m) :=
              @IsSMulRegular.pow R
                Γ(M, PrimeSpectrum.basicOpen (g i * g j))
                (g i * g j) _
                (sectionMulActionForGluing (M := M)
                  (PrimeSpectrum.basicOpen (g i * g j))) m
                (M.isSMulRegular_of_le_basicOpen le_rfl)
            apply hreg
            have hpow :
                (f * (g i * g j)) ^ m =
                  f ^ m * (g i * g j) ^ m :=
              mul_pow _ _ _
            rw [hpow] at hm'
            have hm'' :
                f ^ m •ₛ ((g i * g j) ^ m •ₛ
                    restrictionLinearMap
                      (PrimeSpectrum.basicOpen_mul_le_left
                        (g i) (g j)) (t i)) =
                  f ^ m •ₛ ((g i * g j) ^ m •ₛ
                    restrictionLinearMap
                      (PrimeSpectrum.basicOpen_mul_le_right
                        (g i) (g j)) (t j)) :=
              (sectionSmul_mul _ _ _).symm.trans
                (hm'.trans (sectionSmul_mul _ _ _))
            calc
              (g i * g j) ^ m •ₛ
                  (f ^ m •ₛ restrictionLinearMap
                    (PrimeSpectrum.basicOpen_mul_le_left
                      (g i) (g j)) (t i)) =
                  f ^ m •ₛ ((g i * g j) ^ m •ₛ
                    restrictionLinearMap
                      (PrimeSpectrum.basicOpen_mul_le_left
                        (g i) (g j)) (t i)) :=
                sectionSmul_comm _ _ _
              _ = f ^ m •ₛ ((g i * g j) ^ m •ₛ
                    restrictionLinearMap
                      (PrimeSpectrum.basicOpen_mul_le_right
                        (g i) (g j)) (t j)) := hm''
              _ = (g i * g j) ^ m •ₛ
                  (f ^ m •ₛ restrictionLinearMap
                    (PrimeSpectrum.basicOpen_mul_le_right
                      (g i) (g j)) (t j)) :=
                (sectionSmul_comm _ _ _).symm
          _ = restrictionLinearMap
              (PrimeSpectrum.basicOpen_mul_le_right
                (g i) (g j)) (f ^ m •ₛ t j) :=
            (restriction_smul
              (PrimeSpectrum.basicOpen_mul_le_right
                (g i) (g j)) (f ^ m) (t j)).symm
      choose m hm using hij
      let K := ⨆ i, ⨆ j, m i j
      refine ⟨K, fun i j => ?_⟩
      have hmle : m i j ≤ K :=
        le_ciSup_of_le (Finite.bddAbove_range _) i
          (le_ciSup (Finite.bddAbove_range _) _)
      have hKm : K = (K - m i j) + m i j := by
        lia
      have hpowLeft :
          M.presheaf.map
            (homOfLE
              (PrimeSpectrum.basicOpen_mul_le_left
                (g i) (g j))).op (f ^ K •ₛ t i) =
            M.presheaf.map
              (homOfLE
                (PrimeSpectrum.basicOpen_mul_le_left
                (g i) (g j))).op
              (f ^ (K - m i j) •ₛ
                (f ^ (m i j) •ₛ t i)) := by
          apply congrArg
            (fun x : Γ(M, PrimeSpectrum.basicOpen (g i)) =>
              M.presheaf.map
                (homOfLE
                  (PrimeSpectrum.basicOpen_mul_le_left
                    (g i) (g j))).op x)
          conv_lhs => rw [hKm]
          erw [pow_add, sectionSmul_mul]
      have hmapLeft :
          M.presheaf.map
              (homOfLE (PrimeSpectrum.basicOpen_mul_le_left
                (g i) (g j))).op
              (f ^ (K - m i j) •ₛ (f ^ (m i j) •ₛ t i)) =
          sectionSmul (M := M)
            (U := PrimeSpectrum.basicOpen (g i * g j))
            (f ^ (K - m i j))
            (M.presheaf.map
              (homOfLE (PrimeSpectrum.basicOpen_mul_le_left
              (g i) (g j))).op (f ^ (m i j) •ₛ t i)) :=
        map_sectionSmul_Spec (M := M)
            (homOfLE (PrimeSpectrum.basicOpen_mul_le_left
              (g i) (g j))).op
            (f ^ (K - m i j)) (f ^ (m i j) •ₛ t i)
      have htransport :
          sectionSmul (M := M)
            (U := PrimeSpectrum.basicOpen (g i * g j))
            (f ^ (K - m i j))
            (M.presheaf.map
              (homOfLE (PrimeSpectrum.basicOpen_mul_le_left
                (g i) (g j))).op (f ^ (m i j) •ₛ t i)) =
          sectionSmul (M := M)
            (U := PrimeSpectrum.basicOpen (g i * g j))
            (f ^ (K - m i j))
            (M.presheaf.map
              (homOfLE (PrimeSpectrum.basicOpen_mul_le_right
              (g i) (g j))).op (f ^ (m i j) •ₛ t j)) :=
        congrArg (fun x => f ^ (K - m i j) •ₛ x) (hm i j)
      have hmapRight :
          sectionSmul (M := M)
            (U := PrimeSpectrum.basicOpen (g i * g j))
            (f ^ (K - m i j))
            (M.presheaf.map
              (homOfLE (PrimeSpectrum.basicOpen_mul_le_right
                (g i) (g j))).op (f ^ (m i j) •ₛ t j)) =
          M.presheaf.map
            (homOfLE (PrimeSpectrum.basicOpen_mul_le_right
              (g i) (g j))).op
              (f ^ (K - m i j) •ₛ (f ^ (m i j) •ₛ t j)) :=
        (map_sectionSmul_Spec (M := M)
            (homOfLE (PrimeSpectrum.basicOpen_mul_le_right
              (g i) (g j))).op
            (f ^ (K - m i j)) (f ^ (m i j) •ₛ t j)).symm
      have hpowRight :
          M.presheaf.map
            (homOfLE (PrimeSpectrum.basicOpen_mul_le_right
              (g i) (g j))).op
              (f ^ (K - m i j) •ₛ (f ^ (m i j) •ₛ t j)) =
          M.presheaf.map
            (homOfLE (PrimeSpectrum.basicOpen_mul_le_right
              (g i) (g j))).op (f ^ K •ₛ t j) := by
          apply congrArg (M.presheaf.map
            (homOfLE (PrimeSpectrum.basicOpen_mul_le_right
              (g i) (g j))).op)
          conv_rhs => rw [hKm]
          erw [pow_add, sectionSmul_mul]
      exact hpowLeft.trans
        (hmapLeft.trans (htransport.trans (hmapRight.trans hpowRight)))
    refine ⟨N + K, ?_⟩
    have hglue := TopCat.Sheaf.existsUnique_gluing'
      ⟨_, M.isSheaf⟩
      (fun i => PrimeSpectrum.basicOpen (g i)) V
      (fun i => homOfLE (by
        rw [hg]
        exact le_iSup_of_le _ le_rfl))
      (by rw [hg]; exact le_rfl)
      (fun i => f ^ K •ₛ t i) (by
        intro i j
        dsimp [TopologicalSpace.Opens.infLELeft,
          TopologicalSpace.Opens.infLERight]
        let e :
            Opposite.op
                (PrimeSpectrum.basicOpen (g i * g j)) ≅
              Opposite.op
                (PrimeSpectrum.basicOpen (g i) ⊓
                  PrimeSpectrum.basicOpen (g j)) :=
          eqToIso (congrArg Opposite.op
            (PrimeSpectrum.basicOpen_mul (g i) (g j)))
        have hleft :
            M.presheaf.map (homOfLE inf_le_left).op
                (f ^ K •ₛ t i) =
              M.presheaf.map e.hom
                (M.presheaf.map
                  (homOfLE
                    (PrimeSpectrum.basicOpen_mul_le_left
                      (g i) (g j))).op
                  (f ^ K •ₛ t i)) := by
          have h₁ :
              M.presheaf.map (homOfLE inf_le_left).op
                  (f ^ K •ₛ t i) =
                M.presheaf.map
                  ((homOfLE
                    (PrimeSpectrum.basicOpen_mul_le_left
                      (g i) (g j))).op ≫ e.hom)
                  (f ^ K •ₛ t i) := by congr 1
          exact h₁.trans (presheaf_map_comp_apply _ _ _).symm
        have hright :
            M.presheaf.map (homOfLE inf_le_right).op
                (f ^ K •ₛ t j) =
              M.presheaf.map e.hom
                (M.presheaf.map
                  (homOfLE
                    (PrimeSpectrum.basicOpen_mul_le_right
                      (g i) (g j))).op
                  (f ^ K •ₛ t j)) := by
          have h₁ :
              M.presheaf.map (homOfLE inf_le_right).op
                  (f ^ K •ₛ t j) =
                M.presheaf.map
                  ((homOfLE
                    (PrimeSpectrum.basicOpen_mul_le_right
                      (g i) (g j))).op ≫ e.hom)
                  (f ^ K •ₛ t j) := by congr 1
          exact h₁.trans (presheaf_map_comp_apply _ _ _).symm
        exact Eq.trans hleft
          (Eq.trans
            (congrArg (fun x => M.presheaf.map e.hom x) (hK i j))
            (Eq.symm hright)))
    obtain ⟨a, ha, _⟩ := hglue
    use a
    refine TopCat.Sheaf.eq_of_locally_eq'
      ⟨_, M.isSheaf⟩
      (fun i => PrimeSpectrum.basicOpen (f * g i)) _
      (fun i => homOfLE
        (PrimeSpectrum.basicOpen_mul_le_left f (g i)))
      ?_ _ _ ?_
    · rw [left_eq_inf.mpr hf, hg, inf_iSup_eq]
      simp_rw [PrimeSpectrum.basicOpen_mul]
      exact le_rfl
    · intro i
      let hfi :
          PrimeSpectrum.basicOpen (f * g i) ≤
            PrimeSpectrum.basicOpen f :=
        PrimeSpectrum.basicOpen_mul_le_left _ _
      let hgi :
          PrimeSpectrum.basicOpen (f * g i) ≤
            PrimeSpectrum.basicOpen (g i) :=
        hfgi i
      change
        M.presheaf.map (homOfLE hfi).op
            (M.presheaf.map (homOfLE hf).op a) =
          M.presheaf.map (homOfLE hfi).op
            (f ^ (N + K) •ₛ s)
      have hcompose :
          M.presheaf.map (homOfLE hfi).op
            (M.presheaf.map (homOfLE hf).op a) =
            M.presheaf.map (homOfLE hgi).op
              (M.presheaf.map (homOfLE (hgle i)).op a) :=
        (restriction_trans hfi hf a).trans
          (restriction_trans hgi (hgle i) a).symm
      have hlocal :
          M.presheaf.map (homOfLE hgi).op
              (M.presheaf.map (homOfLE (hgle i)).op a) =
            M.presheaf.map (homOfLE hgi).op
              (f ^ K •ₛ t i) := congrArg
          (fun x => M.presheaf.map (homOfLE hgi).op x)
          (ha i)
      have hmap :
          M.presheaf.map (homOfLE hgi).op (f ^ K •ₛ t i) =
          sectionSmul (M := M)
            (U := PrimeSpectrum.basicOpen (f * g i)) (f ^ K)
            (M.presheaf.map (homOfLE hgi).op (t i)) :=
        map_sectionSmul_Spec (M := M)
          (homOfLE hgi).op (f ^ K) (t i)
      have ht' :
          f ^ K •ₛ M.presheaf.map (homOfLE hgi).op (t i) =
            f ^ K •ₛ (f ^ N •ₛ s' i) :=
        congrArg (fun x => f ^ K •ₛ x) (ht i).symm
      have hpowers :
          f ^ K •ₛ (f ^ N •ₛ s' i) =
            f ^ (N + K) •ₛ s' i := by
        erw [pow_add, sectionSmul_mul, sectionSmul_comm]
      have hsection :
          f ^ (N + K) •ₛ s' i =
            f ^ (N + K) •ₛ restrictionLinearMap hfi s := rfl
      have hrestrict :
          f ^ (N + K) •ₛ restrictionLinearMap hfi s =
            restrictionLinearMap hfi (f ^ (N + K) •ₛ s) :=
        (restriction_smul hfi (f ^ (N + K)) s).symm
      exact hcompose.trans
        (hlocal.trans
          (hmap.trans (ht'.trans (hpowers.trans (hsection.trans hrestrict)))))
  · have hi (i : ι) :
        ∃ n : ℕ,
          M.presheaf.map (homOfLE (hgle i)).op
            (f ^ n •ₛ t) = 0 := by
      have hu := (h₁ i).uniqueness (f * g i)
        (PrimeSpectrum.basicOpen_mul_le_right f (g i))
        (M.presheaf.map (homOfLE (hgle i)).op t) (by
          let hfi :
              PrimeSpectrum.basicOpen (f * g i) ≤
                PrimeSpectrum.basicOpen f :=
            PrimeSpectrum.basicOpen_mul_le_left _ _
          let hgi :
              PrimeSpectrum.basicOpen (f * g i) ≤
                PrimeSpectrum.basicOpen (g i) :=
            PrimeSpectrum.basicOpen_mul_le_right _ _
          calc
            M.presheaf.map (homOfLE hgi).op
                (M.presheaf.map (homOfLE (hgle i)).op t) =
                M.presheaf.map (homOfLE hfi).op
                  (M.presheaf.map (homOfLE hf).op t) :=
              (restriction_trans hgi (hgle i) t).trans
                (restriction_trans hfi hf t).symm
            _ = M.presheaf.map (homOfLE hfi).op 0 := by
              rw [hs]
              rfl
            _ = 0 := map_zero _)
      obtain ⟨n, hn⟩ := hu
      use n
      have hreg :
          @IsSMulRegular R Γ(M, PrimeSpectrum.basicOpen (g i))
            (sectionModuleForGluing (M := M)
              (PrimeSpectrum.basicOpen (g i))).toSMul (g i ^ n) :=
        @IsSMulRegular.pow R Γ(M, PrimeSpectrum.basicOpen (g i))
          (g i) _
          (sectionMulActionForGluing (M := M)
            (PrimeSpectrum.basicOpen (g i))) n
          (M.isSMulRegular_of_le_basicOpen le_rfl)
      refine @IsSMulRegular.right_eq_zero_of_smul
        R Γ(M, PrimeSpectrum.basicOpen (g i)) _
        (sectionSMulZeroClassForGluing (M := M)
          (PrimeSpectrum.basicOpen (g i)))
        (g i ^ n)
        (restrictionLinearMap (hgle i) (f ^ n •ₛ t)) hreg ?_
      calc
        g i ^ n •ₛ restrictionLinearMap (hgle i)
                (f ^ n •ₛ t) =
            g i ^ n •ₛ
              (f ^ n •ₛ restrictionLinearMap (hgle i) t) :=
          congrArg (fun x => g i ^ n •ₛ x)
            (restriction_smul (hgle i) (f ^ n) t)
        _ = (f * g i) ^ n •ₛ
              restrictionLinearMap (hgle i) t := by
          erw [mul_pow, sectionSmul_mul, sectionSmul_comm]
        _ = 0 := hn
    choose n hn using hi
    use ⨆ i, n i
    apply TopCat.Sheaf.eq_of_locally_eq'
      ⟨_, M.isSheaf⟩
      (fun i => PrimeSpectrum.basicOpen (g i)) _
      (fun i => homOfLE (by
        rw [hg]
        exact le_iSup_of_le _ le_rfl))
    · rw [hg]
      exact le_rfl
    · intro i
      have hnle : n i ≤ ⨆ i, n i :=
        le_ciSup (Finite.bddAbove_range _) _
      have hsup :
          ⨆ i, n i = ((⨆ i, n i) - n i) + n i := by
        lia
      change M.presheaf.map (homOfLE (hgle i)).op
          (f ^ (⨆ i, n i) •ₛ t) =
        M.presheaf.map (homOfLE (hgle i)).op 0
      rw [map_zero (M.presheaf.map (homOfLE (hgle i)).op).hom]
      have hpowers :
          M.presheaf.map (homOfLE (hgle i)).op
            (f ^ (⨆ i, n i) •ₛ t) =
            M.presheaf.map (homOfLE (hgle i)).op
              (f ^ ((⨆ i, n i) - n i) •ₛ
                (f ^ n i •ₛ t)) := by
          apply congrArg
            (fun x : Γ(M, V) =>
              M.presheaf.map (homOfLE (hgle i)).op x)
          conv_lhs => rw [hsup]
          erw [pow_add, sectionSmul_mul]
      have hmap :
          M.presheaf.map (homOfLE (hgle i)).op
              (f ^ ((⨆ i, n i) - n i) •ₛ (f ^ n i •ₛ t)) =
          sectionSmul (M := M)
              (U := PrimeSpectrum.basicOpen (g i))
              (f ^ ((⨆ i, n i) - n i))
              (M.presheaf.map (homOfLE (hgle i)).op
                (f ^ n i •ₛ t)) :=
        map_sectionSmul_Spec (M := M) (homOfLE (hgle i)).op
          (f ^ ((⨆ i, n i) - n i)) (f ^ n i •ₛ t)
      have hzero :
          sectionSmul (M := M)
              (U := PrimeSpectrum.basicOpen (g i))
              (f ^ ((⨆ i, n i) - n i))
              (M.presheaf.map (homOfLE (hgle i)).op
                (f ^ n i •ₛ t)) =
            (0 : M.presheaf.obj
              (Opposite.op (PrimeSpectrum.basicOpen (g i)))) := by
        have hni :
            M.presheaf.map (homOfLE (hgle i)).op
                (f ^ n i •ₛ t) = 0 :=
          hn i
        exact (congrArg
          (fun x : Γ(M, PrimeSpectrum.basicOpen (g i)) =>
            f ^ ((⨆ i, n i) - n i) •ₛ x)
          hni).trans
            (show f ^ ((⨆ i, n i) - n i) •ₛ
                (0 : Γ(M, PrimeSpectrum.basicOpen (g i))) = 0
              from sectionSmul_zero _)
      exact hpowers.trans (hmap.trans hzero)

end BasicOpenExtensionData

end AlgebraicGeometry.QuasicoherentTilde

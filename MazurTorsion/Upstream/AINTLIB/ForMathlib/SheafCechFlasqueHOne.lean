/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SheafCechGlobalSections

/-!
# Degree-one Cech acyclicity for flasque sheaves

For a flasque sheaf, the native Cech complex of an open cover is exact in degree one.
The proof factors the first Cech differential through the cycle sheaf, uses the
sheaf-level Cech resolution to obtain a short exact sequence with the original sheaf as
kernel, and then applies global section lifting for a flasque kernel.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

noncomputable section

variable {X : TopCat.{u}}
variable (F : Sheaf AddCommGrpCat.{u} X)
variable {ι : Type u} (U : ι → Opens X)

/-- The first two differentials of the sheaf-level Cech complex. -/
private noncomputable abbrev cechOneShortComplex :
    ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk (cechDifferential F U 0) (cechDifferential F U 1)
    (cechDifferential_comp F U 0)

/-- The augmentation followed by the induced map to the cycles of the first two
sheaf-level Cech differentials. -/
private noncomputable abbrev cechCycleShortComplex :
    ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
  let T := cechOneShortComplex F U
  ShortComplex.mk (cechAugmentation F U) T.toCycles (by
    rw [← cancel_mono T.iCycles, Category.assoc, T.toCycles_i, zero_comp,
      cechAugmentation_comp])

/-- For an open cover, the augmentation and the induced map to degree-one cycles form
a short exact sequence. -/
private theorem cechCycleShortComplex_shortExact (hU : ⨆ i, U i = ⊤) :
    (cechCycleShortComplex F U).ShortExact := by
  let T := cechOneShortComplex F U
  let A := cechCycleShortComplex F U
  let B := cechAugmentedShortComplex F U
  have hB : B.Exact := cechAugmentedShortComplex_exact F U hU
  haveI : Mono A.f := by
    change Mono (cechAugmentation F U)
    exact cechAugmentation_mono F U hU
  haveI : Mono B.f := by
    change Mono (cechAugmentation F U)
    exact cechAugmentation_mono F U hU
  have hker : IsLimit (KernelFork.ofι A.f A.zero) :=
    isKernelOfComp T.iCycles T.f hB.fIsKernel A.zero T.toCycles_i
  have hA : A.Exact := ShortComplex.exact_of_f_is_kernel A hker
  have hT : T.Exact := cechShortComplex_exact F U hU 0
  haveI : Epi A.g := by
    change Epi T.toCycles
    exact hT.epi_toCycles
  exact { exact := hA }

private theorem cechTopSections_exact_one [IsFlasque F]
    (hU : ⨆ i, U i = ⊤)
    (x : (cechTerm F U 1).obj.obj (op ⊤))
    (hx : (cechDifferential F U 1).hom.app (op ⊤) x = 0) :
    ∃ y : (cechTerm F U 0).obj.obj (op ⊤),
      (cechDifferential F U 0).hom.app (op ⊤) y = x := by
  let T := cechOneShortComplex F U
  let A := cechCycleShortComplex F U
  have hA : A.ShortExact := cechCycleShortComplex_shortExact F U hU
  let K := ShortComplex.mk T.iCycles T.g T.iCycles_g
  have hK : K.Exact := ShortComplex.exact_of_f_is_kernel K T.cyclesIsKernel
  obtain ⟨z, hz⟩ := Sheaf.sections_exact_of_left_exact hK (inferInstance : Mono K.f) x hx
  letI : IsFlasque A.X₁ := by change IsFlasque F; infer_instance
  haveI : Epi (A.g.hom.app (op (⊤ : Opens X))) := IsFlasque.epi_of_shortExact hA
  have hsurj : Function.Surjective (A.g.hom.app (op (⊤ : Opens X))) :=
    (AddCommGrpCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨y, hy⟩ := hsurj z
  refine ⟨y, ?_⟩
  calc
    T.f.hom.app (op (⊤ : Opens X)) y =
        (T.toCycles ≫ T.iCycles).hom.app (op (⊤ : Opens X)) y := by
      rw [T.toCycles_i]
    _ = T.iCycles.hom.app (op (⊤ : Opens X))
        (T.toCycles.hom.app (op (⊤ : Opens X)) y) := rfl
    _ = T.iCycles.hom.app (op (⊤ : Opens X)) z := congrArg _ hy
    _ = x := hz

private abbrev globalSections (X : TopCat.{u}) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      AddCommGrpCat.{u} :=
  CategoryTheory.Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u}

noncomputable local instance : (globalSections X).Additive :=
  (CategoryTheory.constantSheafΓAdj
    (Opens.grothendieckTopology X) AddCommGrpCat.{u}).right_adjoint_additive

private abbrev cechSiteDifferential (n : ℕ) :
    toSiteSheaf (cechTerm F U n) ⟶ toSiteSheaf (cechTerm F U (n + 1)) :=
  cechDifferential F U n

private theorem cechGlobalSections_exactAt_one [IsFlasque F]
    (hU : ⨆ i, U i = ⊤) :
    (((globalSections X).mapHomologicalComplex (.up ℕ)).obj
      (cechComplex F U)).ExactAt 1 := by
  let S : ShortComplex AddCommGrpCat.{u} :=
    ShortComplex.mk
      ((globalSections X).map (cechSiteDifferential F U 0))
      ((globalSections X).map (cechSiteDifferential F U 1)) (by
        calc
          _ = (globalSections X).map
              (cechSiteDifferential F U 0 ≫ cechSiteDifferential F U 1) :=
            ((globalSections X).map_comp _ _).symm
          _ = (globalSections X).map 0 :=
            congrArg (globalSections X).map (cechDifferential_comp F U 0)
          _ = 0 := (globalSections X).map_zero
            (toSiteSheaf (cechTerm F U 0)) (toSiteSheaf (cechTerm F U 2)))
  have hS : S.Exact := by
    rw [ShortComplex.ab_exact_iff]
    intro x hx
    let eΓ := CategoryTheory.Sheaf.ΓNatIsoSheafSections
      (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop
    let xTop := eΓ.hom.app (toSiteSheaf (cechTerm F U 1)) x
    have hxTop : (cechDifferential F U 1).hom.app (op ⊤) xTop = 0 := by
      calc
        _ = eΓ.hom.app (toSiteSheaf (cechTerm F U 2))
            ((globalSections X).map (cechSiteDifferential F U 1) x) :=
          (ConcreteCategory.congr_hom
            (eΓ.hom.naturality (cechSiteDifferential F U 1)) x).symm
        _ = 0 := by rw [hx, map_zero]
    obtain ⟨yTop, hyTop⟩ := cechTopSections_exact_one F U hU xTop hxTop
    let y := eΓ.inv.app (toSiteSheaf (cechTerm F U 0)) yTop
    have hyInv : eΓ.hom.app (toSiteSheaf (cechTerm F U 0)) y = yTop := by
      exact Iso.inv_hom_id_apply (eΓ.app (toSiteSheaf (cechTerm F U 0))) yTop
    have hyTop' :
        (cechDifferential F U 0).hom.app (op (⊤ : Opens X)) yTop = xTop := by
      exact hyTop
    refine ⟨y, ?_⟩
    change (globalSections X).map (cechSiteDifferential F U 0) y = x
    apply (AddCommGrpCat.mono_iff_injective
      (eΓ.hom.app (toSiteSheaf (cechTerm F U 1)))).mp inferInstance
    have hnat :
        eΓ.hom.app (toSiteSheaf (cechTerm F U 1))
            ((globalSections X).map (cechSiteDifferential F U 0) y) =
          (cechDifferential F U 0).hom.app (op (⊤ : Opens X))
            (eΓ.hom.app (toSiteSheaf (cechTerm F U 0)) y) :=
      ConcreteCategory.congr_hom
        (eΓ.hom.naturality (cechSiteDifferential F U 0)) y
    refine hnat.trans ?_
    rw [hyInv]
    exact hyTop'
  rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp)]
  change S.Exact
  exact hS

/-- The native Cech complex of a flasque sheaf is exact in degree one. -/
theorem cechComplex_exactAt_one_of_isFlasque [IsFlasque F]
    (hU : ⨆ i, U i = ⊤) :
    ((cechComplexFunctor U).obj F.obj).ExactAt 1 :=
  (cechGlobalSections_exactAt_one F U hU).of_iso
    (cechGlobalSectionsComplexIso F U)

end
end TopCat.Sheaf

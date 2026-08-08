/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

Adapted from the Apache-licensed
`CoherentCohomologyFinite/ModuleSupport.lean` in Vilin97/Clawristotle.
-/
import Mathlib.RingTheory.Spectrum.Prime.Module
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Topology.Sheaves.Abelian
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleClosedStalkSupport
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleQuasicoherent

/-!
# Support of a finite-type quasicoherent module

The nonzero-stalk locus of a finite-type quasicoherent module is closed. This file packages
that locus as a closed subset and records its behavior in short exact sequences.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.tilde

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

@[simp]
lemma mem_stalkSupport_iff (M : X.Modules) (x : X) :
    x ∈ stalkSupport M ↔
      ¬ IsZero ((underlyingStalkFunctor x).obj M) :=
  Iff.rfl

@[simp]
lemma mem_closedStalkSupport_iff (M : X.Modules) (x : X) :
    x ∈ closedStalkSupport M ↔
      x ∈ closure (stalkSupport M) :=
  Iff.rfl

lemma isZero_X₂_iff_of_shortExact
    {C : Type*} [Category C] [Abelian C]
    {S : ShortComplex C} (hS : S.ShortExact) :
    IsZero S.X₂ ↔ IsZero S.X₁ ∧ IsZero S.X₃ := by
  letI : Mono S.f := hS.mono_f
  letI : Epi S.g := hS.epi_g
  constructor
  · intro h₂
    exact ⟨IsZero.of_mono S.f h₂, IsZero.of_epi S.g h₂⟩
  · rintro ⟨h₁, h₃⟩
    exact hS.exact.isZero_X₂
      (h₁.eq_of_src S.f 0) (h₃.eq_of_tgt S.g 0)

/-- Nonzero-stalk support is additive across a short exact sequence. -/
lemma stalkSupport_eq_union
    {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    stalkSupport S.X₂ =
      stalkSupport S.X₁ ∪ stalkSupport S.X₃ := by
  ext x
  let Fx := underlyingStalkFunctor x
  have hFx : (S.map Fx).ShortExact :=
    ShortComplex.ShortExact.map_of_exact hS Fx
  have hz := isZero_X₂_iff_of_shortExact hFx
  change
    (¬ IsZero ((S.map Fx).X₂)) ↔
      (¬ IsZero ((S.map Fx).X₁)) ∨
        (¬ IsZero ((S.map Fx).X₃))
  tauto

/-- Closed stalk support is additive across a short exact sequence. -/
lemma closedStalkSupport_eq_sup
    {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    closedStalkSupport S.X₂ =
      closedStalkSupport S.X₁ ⊔ closedStalkSupport S.X₃ := by
  apply Closeds.ext
  change
    closure (stalkSupport S.X₂) =
      closure (stalkSupport S.X₁) ∪
        closure (stalkSupport S.X₃)
  rw [stalkSupport_eq_union hS, closure_union]

/-- A zero module has empty closed stalk support. -/
lemma closedStalkSupport_eq_bot_of_isZero
    (M : X.Modules) (hM : IsZero M) :
    closedStalkSupport M = ⊥ := by
  apply Closeds.ext
  change closure (stalkSupport M) = ∅
  have hs : stalkSupport M = ∅ := by
    ext x
    simp only [stalkSupport, Set.mem_setOf_eq, Set.mem_empty_iff_false,
      iff_false, not_not]
    exact (underlyingStalkFunctor x).map_isZero hM
  rw [hs, closure_empty]

/-- A scheme module with zero underlying stalk at every point is zero. -/
lemma isZero_of_forall_underlyingStalk_isZero
    (M : X.Modules)
    (h : ∀ x : X, IsZero ((underlyingStalkFunctor x).obj M)) :
    IsZero M := by
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  have hs : IsZero (F.obj M) := by
    apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero (F.obj M)).2
    intro x
    exact h x
  constructor
  · intro N
    refine ⟨⟨⟨0⟩, fun f ↦ ?_⟩⟩
    apply F.map_injective
    exact hs.eq_of_src _ _
  · intro N
    refine ⟨⟨⟨0⟩, fun f ↦ ?_⟩⟩
    apply F.map_injective
    exact hs.eq_of_tgt _ _

/-- Empty closed stalk support characterizes the zero module. -/
lemma isZero_iff_closedStalkSupport_eq_bot (M : X.Modules) :
    IsZero M ↔ closedStalkSupport M = ⊥ := by
  refine ⟨closedStalkSupport_eq_bot_of_isZero M, ?_⟩
  intro hs
  have hclosure : closure (stalkSupport M) = ∅ := by
    simpa [closedStalkSupport] using
      congr_arg (fun Z : Closeds X => (Z : Set X)) hs
  have hstalks :
      ∀ x : X, IsZero ((underlyingStalkFunctor x).obj M) := by
    intro x
    by_contra hx
    have hxSupport : x ∈ stalkSupport M := hx
    have hxClosure : x ∈ closure (stalkSupport M) :=
      subset_closure hxSupport
    rw [hclosure] at hxClosure
    exact hxClosure
  exact isZero_of_forall_underlyingStalk_isZero M hstalks

/-- On an affine spectrum, the stalk of a tilde module vanishes exactly away from the
ordinary commutative-algebra support. -/
lemma isZero_underlyingStalkFunctor_tilde_iff_not_mem_support
    {R : CommRingCat.{u}} (N : ModuleCat.{u} R) (x : Spec R) :
    IsZero ((underlyingStalkFunctor x).obj (tilde N)) ↔
      x ∉ Module.support R N := by
  letI : x.asIdeal.IsPrime := x.isPrime
  letI : Module R ((tilde N).presheaf.stalk x) :=
    AlgebraicGeometry.tilde.instModuleCarrierCarrierStalkAbPresheaf N x
  letI : IsLocalizedModule x.asIdeal.primeCompl
      (tilde.toStalk N x).hom :=
    instIsLocalizedModuleCarrierCarrierOfCarrierStalkAbPresheafPrimeComplAsIdealHomToStalk
      N x
  let e :=
    IsLocalizedModule.linearEquiv x.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap x.asIdeal.primeCompl N)
      (tilde.toStalk N x).hom
  constructor
  · intro h
    apply Module.notMem_support_iff.mpr
    haveI : Subsingleton ((tilde N).presheaf.stalk x) :=
      AddCommGrpCat.subsingleton_of_isZero h
    exact e.toEquiv.subsingleton
  · intro h
    rw [AddCommGrpCat.isZero_iff_subsingleton]
    change Subsingleton ((tilde N).presheaf.stalk x)
    haveI : Subsingleton (LocalizedModule x.asIdeal.primeCompl N) :=
      Module.notMem_support_iff.mp h
    exact e.toEquiv.subsingleton_congr.mp inferInstance

/-- The nonzero-stalk support of a quasicoherent module on a spectrum is the support of its
affine module of sections. -/
lemma stalkSupport_eq_moduleSupport_of_spectrum
    {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [M.IsQuasicoherent] :
    stalkSupport M =
      Module.support R (moduleSpecΓFunctor.obj M) := by
  letI := isIso_fromTildeΓ_of_isQuasicoherent M
  ext x
  let e :=
    (underlyingStalkFunctor x).mapIso
      (asIso M.fromTildeΓ)
  have hz :
      IsZero ((underlyingStalkFunctor x).obj M) ↔
        x ∉ Module.support R (moduleSpecΓFunctor.obj M) :=
    e.isZero_iff.symm.trans
      (isZero_underlyingStalkFunctor_tilde_iff_not_mem_support
        (moduleSpecΓFunctor.obj M) x)
  change
    (¬ IsZero ((underlyingStalkFunctor x).obj M)) ↔
      x ∈ Module.support R (moduleSpecΓFunctor.obj M)
  tauto

/-- The nonzero-stalk support of a finite-type quasicoherent module on a spectrum is closed. -/
lemma isClosed_stalkSupport_of_spectrum
    {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [M.IsFiniteType] [M.IsQuasicoherent] :
    IsClosed (stalkSupport M) := by
  rw [stalkSupport_eq_moduleSupport_of_spectrum M]
  letI : Module.Finite R (moduleSpecΓFunctor.obj M) := by
    change Module.Finite R Γ(M, ⊤)
    exact globalSections_module_finite_of_isFiniteType M
  exact Module.isClosed_support

/-- Restriction along an open immersion identifies nonzero-stalk support with its inverse
image. -/
lemma preimage_stalkSupport_of_openImmersion
    {Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) :
    f ⁻¹' stalkSupport M =
      stalkSupport (M.restrict f) := by
  ext x
  let e := (restrictStalkNatIso f x).app M
  change
    (¬ IsZero ((underlyingStalkFunctor (f x)).obj M)) ↔
      ¬ IsZero
        ((underlyingStalkFunctor x).obj
          ((restrictFunctor f).obj M))
  exact not_congr e.isZero_iff.symm

private lemma isFiniteType_of_generatingSections
    (M : X.Modules) (G : M.GeneratingSections) [G.IsFiniteType] :
    M.IsFiniteType := by
  let qFull := G.localGeneratorsData
  let q : SheafOfModules.LocalGeneratorsData.{u} M := qFull
  have hq : q.IsFiniteType := by
    constructor
    intro i
    exact ⟨by
      change Finite G.I
      exact SheafOfModules.GeneratingSections.IsFiniteType.finite⟩
  refine { exists_localGeneratorsData := ?_ }
  exact ⟨q, hq⟩

private lemma exists_generatingSections_restrict_fromSpec
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ G : (M.restrict hU.fromSpec).GeneratingSections, G.IsFiniteType := by
  let AU : X.affineOpens := ⟨U, hU⟩
  obtain ⟨G, hG⟩ :=
    exists_generatingSections_restrict_of_isFiniteType_of_isAffineOpen M AU
  letI : G.IsFiniteType := hG
  let F := restrictFunctor hU.isoSpec.inv
  letI : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1} F := by
    dsimp [F]
    infer_instance
  have hF : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1} F :=
    inferInstance
  let G' := @SheafOfModules.GeneratingSections.map
    _ _ _ _ _ _ _ _ _ _ _ _ _ G F hF
      (restrictUnitIso hU.isoSpec.inv).symm
  let e := (restrictFunctorComp hU.isoSpec.inv U.ι).symm.app M
  let G'' := SheafOfModules.GeneratingSections.equivOfIso e G'
  have hG'' : G''.IsFiniteType := ⟨by
    change Finite G.I
    exact hG.finite⟩
  exact ⟨G'', hG''⟩

/-- Restriction of a finite-type quasicoherent module along an affine open's
canonical spectrum presentation is finite type. -/
theorem isFiniteType_restrict_fromSpec
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (U : X.Opens) (hU : IsAffineOpen U) :
    (M.restrict hU.fromSpec).IsFiniteType := by
  obtain ⟨G, hG⟩ := exists_generatingSections_restrict_fromSpec M U hU
  letI : G.IsFiniteType := hG
  exact isFiniteType_of_generatingSections (M.restrict hU.fromSpec) G

/-- The nonzero-stalk locus of a finite-type quasicoherent module is closed. -/
lemma isClosed_stalkSupport
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent] :
    IsClosed (stalkSupport M) := by
  rw [TopologicalSpace.IsOpenCover.isClosed_iff_coe_preimage
    (iSup_affineOpens_eq_top X)]
  intro U
  have hU : IsAffineOpen U.1 := U.property
  have hpre :
      IsClosed (hU.fromSpec ⁻¹' stalkSupport M) := by
    rw [preimage_stalkSupport_of_openImmersion]
    obtain ⟨G, hG⟩ :=
      exists_generatingSections_restrict_fromSpec M U.1 hU
    letI : G.IsFiniteType := hG
    letI : (M.restrict hU.fromSpec).IsFiniteType :=
      isFiniteType_of_generatingSections (M.restrict hU.fromSpec) G
    exact
      isClosed_stalkSupport_of_spectrum
        (M.restrict hU.fromSpec)
  let e :=
    TopCat.homeoOfIso
      (Scheme.forgetToTop.mapIso hU.isoSpec)
  apply e.symm.isClosed_preimage.mp
  convert hpre using 1
  · rfl
  · ext x
    rfl

/-- For a finite-type quasicoherent module, the closure in `closedStalkSupport` is
redundant. -/
lemma coe_closedStalkSupport_eq_stalkSupport
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent] :
    (closedStalkSupport M : Set X) = stalkSupport M :=
  (isClosed_stalkSupport M).closure_eq

/-- A submodule has support contained in that of the ambient module. -/
lemma closedStalkSupport_le_of_mono
    {M N : X.Modules} (f : M ⟶ N) [Mono f] :
    closedStalkSupport M ≤ closedStalkSupport N := by
  let S := ShortComplex.cokernelSequence f
  haveI : Mono S.f := by
    dsimp [S, ShortComplex.cokernelSequence]
    infer_instance
  have hS : S.ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact f }
  have hle :
      closedStalkSupport S.X₁ ≤ closedStalkSupport S.X₂ := by
    rw [closedStalkSupport_eq_sup hS]
    exact le_sup_left
  simpa [S, ShortComplex.cokernelSequence] using hle

/-- The support of a quotient is contained in that of its source. -/
lemma closedStalkSupport_le_of_epi
    {M N : X.Modules} (f : M ⟶ N) [Epi f] :
    closedStalkSupport N ≤ closedStalkSupport M := by
  let S := ShortComplex.kernelSequence f
  haveI : Epi S.g := by
    dsimp [S, ShortComplex.kernelSequence]
    infer_instance
  have hS : S.ShortExact :=
    { exact := ShortComplex.kernelSequence_exact f }
  have hle :
      closedStalkSupport S.X₃ ≤ closedStalkSupport S.X₂ := by
    rw [closedStalkSupport_eq_sup hS]
    exact le_sup_right
  simpa [S, ShortComplex.kernelSequence] using hle

end AlgebraicGeometry.Scheme.Modules

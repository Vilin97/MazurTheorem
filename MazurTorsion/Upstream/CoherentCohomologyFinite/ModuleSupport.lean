/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenRestrictionFiniteSections
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAffineCover
import Mathlib.RingTheory.Spectrum.Prime.Module
import Mathlib.Topology.Sheaves.Abelian

/-!
# Support of a finite-type quasicoherent module

For a finite-type quasicoherent module `M` on a scheme `X`, its restriction
to every affine open `U` is represented by the finite `Γ(X, U)`-module
`Γ(M, U)`.  The complement of the support of that module is open in
`Spec Γ(X, U)`.  Mapping these open loci into `X` and taking their union
gives the nonsupport locus of `M`; its complement is therefore a canonical
closed subset of `X`.

This presentation avoids choosing a particular affine cover.  It is the
closed-set measure used by Noetherian support dévissage.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The affine-open predicate carried by an element of `X.affineOpens`,
with the defining set membership unfolded explicitly. -/
lemma isAffineOpen_coe (U : X.affineOpens) :
    IsAffineOpen U.1 := by
  change IsAffine (↑U.1 : Scheme)
  infer_instance

section StalkSupport

/-- The underlying abelian-group stalk functor at a point of a scheme. -/
noncomputable def underlyingStalkFunctor (x : X) :
    X.Modules ⥤ AddCommGrpCat.{u} :=
  toUnderlyingSheaf X ⋙
    TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x

noncomputable instance underlyingStalkFunctor_additive (x : X) :
    (underlyingStalkFunctor x).Additive := by
  dsimp [underlyingStalkFunctor]
  infer_instance

noncomputable instance underlyingStalkFunctor_preservesFiniteLimits
    (x : X) :
    PreservesFiniteLimits (underlyingStalkFunctor x) := by
  dsimp [underlyingStalkFunctor]
  infer_instance

noncomputable instance underlyingStalkFunctor_preservesFiniteColimits
    (x : X) :
    PreservesFiniteColimits (underlyingStalkFunctor x) := by
  dsimp [underlyingStalkFunctor]
  infer_instance

/-- The set of points where the underlying sheaf stalk is nonzero. -/
def stalkSupport (M : X.Modules) : Set X :=
  {x | ¬ IsZero ((underlyingStalkFunctor x).obj M)}

/-- The closed support measure obtained by closing the nonzero-stalk
locus.  For coherent modules the locus itself is already closed; taking
the closure makes the support measure available before that local theorem
is used. -/
def closedStalkSupport (M : X.Modules) : Closeds X :=
  ⟨closure (stalkSupport M), isClosed_closure⟩

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
  have hz :=
    isZero_X₂_iff_of_shortExact hFx
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

/-- A module whose underlying abelian sheaf is zero is itself zero. -/
lemma isZero_of_isZero_toUnderlyingSheaf
    (M : X.Modules)
    (hM : IsZero ((toUnderlyingSheaf X).obj M)) :
    IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  apply (toUnderlyingSheaf X).map_injective
  exact hM.eq_of_src _ _

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
  apply isZero_of_isZero_toUnderlyingSheaf M
  rw [TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero]
  exact hstalks

/-- On an affine spectrum, the stalk of a tilde module vanishes exactly
away from the ordinary commutative-algebra support. -/
lemma isZero_underlyingStalkFunctor_tilde_iff_not_mem_support
    {R : CommRingCat.{u}} (N : ModuleCat R) (x : Spec R) :
    IsZero ((underlyingStalkFunctor x).obj (tilde N)) ↔
      x ∉ Module.support R N := by
  letI : x.asIdeal.IsPrime := x.isPrime
  letI : Module R ((tilde N).presheaf.stalk x) :=
    tilde.instModuleCarrierCarrierStalkAbPresheaf N x
  letI : IsLocalizedModule x.asIdeal.primeCompl
      (tilde.toStalk N x).hom :=
    tilde.instIsLocalizedModuleCarrierCarrierOfCarrierStalkAbPresheafPrimeComplAsIdealHomToStalk
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

/-- The nonzero-stalk support of a quasicoherent module on a spectrum is
the support of its affine module of sections. -/
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

/-- The nonzero-stalk support of a finite-type quasicoherent module on a
spectrum is closed. -/
lemma isClosed_stalkSupport_of_spectrum
    {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [M.IsFiniteType] [M.IsQuasicoherent] :
    IsClosed (stalkSupport M) := by
  rw [stalkSupport_eq_moduleSupport_of_spectrum M]
  letI : Module.Finite R (moduleSpecΓFunctor.obj M) :=
    finite_top_sections_of_isFiniteType_isQuasicoherent M
  exact Module.isClosed_support

/-- Restriction along an open immersion identifies nonzero-stalk support
with the inverse image of support. -/
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

/-- The nonzero-stalk locus of a finite-type quasicoherent module on an
arbitrary scheme is closed. -/
lemma isClosed_stalkSupport
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent] :
    IsClosed (stalkSupport M) := by
  rw [TopologicalSpace.IsOpenCover.isClosed_iff_coe_preimage
    (iSup_affineOpens_eq_top X)]
  intro U
  have hpre :
      IsClosed ((isAffineOpen_coe U).fromSpec ⁻¹' stalkSupport M) := by
    rw [preimage_stalkSupport_of_openImmersion]
    exact
      isClosed_stalkSupport_of_spectrum
        (M.restrict (isAffineOpen_coe U).fromSpec)
  let e :=
    TopCat.homeoOfIso
      (Scheme.forgetToTop.mapIso (isAffineOpen_coe U).isoSpec)
  apply e.symm.isClosed_preimage.mp
  convert hpre using 1
  · rfl
  · ext x
    rfl

/-- For a finite-type quasicoherent module, taking the closure in the
definition of `closedStalkSupport` changes nothing. -/
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

end StalkSupport

section AffineSupport

variable (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent]

/-- Sections on an affine open form a finite module over the ring of
functions on that open. -/
noncomputable instance affineSections_finite (U : X.affineOpens) :
    Module.Finite Γ(X, U.1) Γ(M, U.1) :=
  finiteSections_of_isAffineOpen M U.2

/-- The open complement of the support of the affine coordinate module
`Γ(U, M)`. -/
def affineNonSupportOpen (U : X.affineOpens) :
    (Spec Γ(X, U.1)).Opens :=
  ⟨(Module.support Γ(X, U.1) Γ(M, U.1))ᶜ,
    Module.isClosed_support.isOpen_compl⟩

@[simp]
lemma mem_affineNonSupportOpen_iff
    (U : X.affineOpens) (p : Spec Γ(X, U.1)) :
    p ∈ affineNonSupportOpen M U ↔
      p ∉ Module.support Γ(X, U.1) Γ(M, U.1) :=
  Iff.rfl

/-- The nonsupport locus, obtained by taking the union of the affine
local nonsupport loci. -/
def nonSupportOpen : X.Opens :=
  ⨆ U : X.affineOpens,
    (isAffineOpen_coe U).fromSpec ''ᵁ affineNonSupportOpen M U

/-- The support of a finite-type quasicoherent module as a closed subset
of its scheme. -/
def support : Closeds X :=
  ⟨(nonSupportOpen M : Set X)ᶜ, (nonSupportOpen M).2.isClosed_compl⟩

@[simp]
lemma mem_support_iff (x : X) :
    x ∈ support M ↔ x ∉ nonSupportOpen M :=
  Iff.rfl

@[simp]
lemma not_mem_support_iff (x : X) :
    x ∉ support M ↔ x ∈ nonSupportOpen M := by
  simp [mem_support_iff]

/-- Every affine-local nonsupport locus maps into the global nonsupport
locus. -/
lemma image_affineNonSupportOpen_le_nonSupportOpen
    (U : X.affineOpens) :
    (isAffineOpen_coe U).fromSpec ''ᵁ affineNonSupportOpen M U ≤
      nonSupportOpen M :=
  le_iSup (fun V : X.affineOpens =>
    (isAffineOpen_coe V).fromSpec ''ᵁ affineNonSupportOpen M V) U

/-- A prime outside the support of the affine section module maps outside
the global support. -/
lemma fromSpec_not_mem_support
    (U : X.affineOpens) (p : Spec Γ(X, U.1))
    (hp : p ∉ Module.support Γ(X, U.1) Γ(M, U.1)) :
    (isAffineOpen_coe U).fromSpec p ∉ support M := by
  rw [not_mem_support_iff]
  apply image_affineNonSupportOpen_le_nonSupportOpen M U
  exact ⟨p, hp, rfl⟩

end AffineSupport

end AlgebraicGeometry.Scheme.Modules

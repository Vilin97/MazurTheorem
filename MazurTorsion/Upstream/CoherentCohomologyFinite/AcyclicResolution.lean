/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Acyclic resolutions compute right-derived functors

This file provides the abstract homological-algebra core underlying the Čech
computation of higher direct images (Stacks Tag 015E, Leray's acyclicity lemma):
**an acyclic resolution computes every right-derived functor**.

Throughout, `𝒜` and `ℬ` are abelian categories, `𝒜` has injective resolutions
(so that `G.rightDerived n` is everywhere defined), and `G : 𝒜 ⥤ ℬ` is an
additive functor.

## Declarations

* `CategoryTheory.Functor.IsRightAcyclic` — typeclass for right-`G`-acyclic objects.
* Instance: every injective object is right-acyclic (from Mathlib's
  `Functor.isZero_rightDerived_obj_injective_succ`).

The following declarations are all constructed and proved axiom-clean in this file
(P4 complete — see the marker at the end of the file):

* `CategoryTheory.InjectiveResolution.ofShortExact` — dual Horseshoe Lemma:
  lift `0 → A → B → C → 0` to a degreewise-split SES of injective resolutions.
* `CategoryTheory.Functor.rightDerivedShiftIsoOfAcyclic` — dimension-shift
  isomorphism `(Rᵏ G)(Z) ≅ (Rᵏ⁺¹ G)(A)` across a SES with acyclic middle term.
* `CategoryTheory.Functor.rightDerivedIsoOfAcyclicResolution` — main theorem:
  `(Rⁿ G)(A) ≅ Hⁿ(G(J•))` for any acyclic resolution `J•` of `A`.

See `blueprint/src/chapters/Cohomology_AcyclicResolution.tex` and
`.archon/analogies/p4-derived-les.md` for the full informal argument.

## Mathlib building blocks (all verified present)

All from `Mathlib/CategoryTheory/Abelian/RightDerived.lean`:
- `CategoryTheory.InjectiveResolution.isoRightDerivedObj` — iso
  `(F.rightDerived n).obj X ≅ Hⁿ(F.mapHomologicalComplex.obj I.cocomplex)`.
- `CategoryTheory.Functor.rightDerivedZeroIsoSelf` — `R⁰G ≅ G` (left-exact `G`).
- `CategoryTheory.Functor.isZero_rightDerived_obj_injective_succ` — vanishing on
  injectives: `IsZero ((F.rightDerived (n+1)).obj J)` for `[Injective J]`.

From `Mathlib/Algebra/Homology/HomologySequence.lean`:
- `CategoryTheory.ShortComplex.ShortExact.homology_exact₁`
- `CategoryTheory.ShortComplex.ShortExact.homology_exact₂`
- `CategoryTheory.ShortComplex.ShortExact.homology_exact₃`
- `CategoryTheory.ShortComplex.ShortExact.δ`

## Source

Stacks Project, Derived Categories:
- Tag 0157 (definition-derived-functor, items 3–4)
- Tag 015C (lemma-F-acyclic, part 2)
- Tag 015D (lemma-F-acyclic-ses)
- Tag 015E (lemma-leray-acyclicity)
- Tag 05TA (proposition-enough-acyclics)
-/

/-! ## Project-local Mathlib supplement — middle-term quasi-isomorphism transfer

Given a morphism `φ : S₁ ⟶ S₂` between two short exact sequences of homological complexes
in an abelian category, Mathlib proves that if `φ.τ₁` and `φ.τ₂` are quasi-isomorphisms then so
is `φ.τ₃` (`HomologicalComplex.HomologySequence.quasiIso_τ₃`). The companion statements for `φ.τ₁`
and `φ.τ₂` are an explicit Mathlib TODO (see `HomologySequenceLemmas.lean`). We supply the `φ.τ₂`
version here: it is the engine that proves the horseshoe middle complex `I_B` is an injective
*resolution* of `B` (the outer verticals `I_A.ι`, `I_C.ι` are quasi-isos, hence so is the middle
augmentation). The proof mirrors Mathlib's `τ₃` argument: a homology four-lemma on the windows of
`composableArrows₅`, with the boundary degrees (no predecessor / no successor) handled by
`mono_homologyMap_of_mono_of_not_rel` / `epi_homologyMap_of_epi_of_not_rel`. -/

namespace HomologicalComplex.HomologySequence

open CategoryTheory ComposableArrows Abelian Limits

variable {C ι : Type*} [Category C] [Abelian C] {c : ComplexShape ι}
  {S₁ S₂ : ShortComplex (HomologicalComplex C c)} (φ : S₁ ⟶ S₂)
  (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)

include hS₁ hS₂ in
/-- **Middle-term quasi-isomorphism transfer** (the `τ₂` companion of Mathlib's `quasiIso_τ₃`).
If `φ.τ₁` and `φ.τ₃` are quasi-isomorphisms then so is `φ.τ₂`, provided that at each boundary
degree (one with no incoming / no outgoing differential) the middle component `φ.τ₂.f i` is a
mono / epi respectively. This is the `lean_aux` infrastructure behind
`InjectiveResolution.ofShortExact_resolvesMiddle`. -/
lemma quasiIso_τ₂ (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃)
    (hbMono : ∀ i, (∀ k, ¬ c.Rel k i) → Mono (φ.τ₂.f i))
    (hbEpi : ∀ i, (∀ j, ¬ c.Rel i j) → Epi (φ.τ₂.f i)) :
    QuasiIso φ.τ₂ := by
  have hI1 : ∀ d, IsIso (homologyMap φ.τ₁ d) := fun d => by
    rw [← quasiIsoAt_iff_isIso_homologyMap]; exact (quasiIso_iff φ.τ₁).1 h₁ d
  have hI3 : ∀ d, IsIso (homologyMap φ.τ₃ d) := fun d => by
    rw [← quasiIsoAt_iff_isIso_homologyMap]; exact (quasiIso_iff φ.τ₃).1 h₃ d
  have hE1 : ∀ d, Epi (homologyMap φ.τ₁ d) := fun d => have := hI1 d; inferInstance
  have hM1 : ∀ d, Mono (homologyMap φ.τ₁ d) := fun d => have := hI1 d; inferInstance
  have hE3 : ∀ d, Epi (homologyMap φ.τ₃ d) := fun d => have := hI3 d; inferInstance
  have hM3 : ∀ d, Mono (homologyMap φ.τ₃ d) := fun d => have := hI3 d; inferInstance
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hEpi : Epi (homologyMap φ.τ₂ i) := by
    by_cases hi : ∃ j, c.Rel i j
    · obtain ⟨j, hij⟩ := hi
      apply epi_of_epi_of_epi_of_mono
        ((δlastFunctor ⋙ δlastFunctor).map (mapComposableArrows₅ φ hS₁ hS₂ i j hij))
      · exact (composableArrows₅_exact hS₁ i j hij).δlast.δlast
      · exact (composableArrows₅_exact hS₂ i j hij).δlast.δlast
      · exact hE1 i
      · exact hE3 i
      · exact hM1 j
    · have hi' : ∀ j, ¬ c.Rel i j := fun j hj => hi ⟨j, hj⟩
      have := hbEpi i hi'
      exact epi_homologyMap_of_epi_of_not_rel φ.τ₂ i hi'
  have hMono : Mono (homologyMap φ.τ₂ i) := by
    by_cases hi : ∃ k, c.Rel k i
    · obtain ⟨k, hki⟩ := hi
      apply mono_of_epi_of_mono_of_mono
        ((δ₀Functor ⋙ δ₀Functor).map (mapComposableArrows₅ φ hS₁ hS₂ k i hki))
      · exact (composableArrows₅_exact hS₁ k i hki).δ₀.δ₀
      · exact (composableArrows₅_exact hS₂ k i hki).δ₀.δ₀
      · exact hE3 k
      · exact hM1 i
      · exact hM3 i
    · have hi' : ∀ k, ¬ c.Rel k i := fun k hk => hi ⟨k, hk⟩
      have := hbMono i hi'
      exact mono_homologyMap_of_mono_of_not_rel φ.τ₂ i hi'
  exact isIso_of_mono_of_epi _

end HomologicalComplex.HomologySequence

namespace CategoryTheory

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasInjectiveResolutions 𝒜]
variable {ℬ : Type*} [Category ℬ] [Abelian ℬ]

/-!
### Right-acyclic objects
Blueprint: `def:right_acyclic` (§ "Right-acyclic objects").
-/

/-- An object `J : 𝒜` is *right-`G`-acyclic* when every higher right-derived
functor of `G` vanishes at `J`:
```
(Rᵏ⁺¹ G)(J) = 0   for all k : ℕ.
```
The index-shifted quantifier `k + 1` matches the statement of
`Functor.isZero_rightDerived_obj_injective_succ` and avoids an inequality
side-condition; it is equivalent to `(Rⁿ G)(J) = 0` for all `n ≥ 1`.

Blueprint: `CategoryTheory.Functor.IsRightAcyclic` (`def:right_acyclic`).
-/
class Functor.IsRightAcyclic (G : 𝒜 ⥤ ℬ) [G.Additive] (J : 𝒜) : Prop where
  vanish : ∀ k : ℕ, Limits.IsZero ((G.rightDerived (k + 1)).obj J)

/-- Every injective object is right-`G`-acyclic.
Follows immediately from `Functor.isZero_rightDerived_obj_injective_succ`. -/
instance (priority := 100) Functor.IsRightAcyclic.ofInjective
    (G : 𝒜 ⥤ ℬ) [G.Additive] (J : 𝒜) [Injective J] : Functor.IsRightAcyclic G J where
  vanish k := Functor.isZero_rightDerived_obj_injective_succ G k J
-- Note: `Functor.isZero_rightDerived_obj_injective_succ` returns
-- `Limits.IsZero ((G.rightDerived (k+1)).obj J)`, matching the class field.

/-! ## Project-local Mathlib supplement — acyclic resolutions

The declarations in this section are project-local infrastructure feeding the
dimension-shift and acyclic-resolution comparison theorems (Stacks Tag 015D/015E).
They are not yet in Mathlib. -/

open Limits

/-- The cohomology of the `G`-image of an injective resolution of a right-`G`-acyclic
object `J` vanishes in every positive degree. This is the homology-level form of
right-acyclicity, obtained by transporting the vanishing of `(R^{k+1} G)(J)` across
`InjectiveResolution.isoRightDerivedObj`. It is the input that kills the middle terms
of the homology long exact sequence in the dimension-shift step. -/
lemma Functor.isZero_homology_mapHomologicalComplex_of_isRightAcyclic
    (G : 𝒜 ⥤ ℬ) [G.Additive] {J : 𝒜} (I : InjectiveResolution J)
    [G.IsRightAcyclic J] (k : ℕ) :
    IsZero ((HomologicalComplex.homologyFunctor ℬ (ComplexShape.up ℕ) (k + 1)).obj
      ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)) :=
  (Functor.IsRightAcyclic.vanish (G := G) (J := J) k).of_iso
    (I.isoRightDerivedObj G (k + 1)).symm

omit [HasInjectiveResolutions 𝒜] in
/-- A short complex of cochain complexes that is *degreewise split* (each degree carries a
`ShortComplex.Splitting`) is short exact. Project-local because Mathlib only provides the
degreewise-short-exact criterion `shortExact_of_degreewise_shortExact`; this packages the
common special case where the degreewise data is a splitting. -/
lemma shortExact_of_degreewise_splitting
    {S : ShortComplex (CochainComplex 𝒜 ℕ)}
    (splits : ∀ n, (S.map (HomologicalComplex.eval 𝒜 (ComplexShape.up ℕ) n)).Splitting) :
    S.ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact S (fun n => (splits n).shortExact)

omit [HasInjectiveResolutions 𝒜] in
/-- An additive functor applied degreewise to a degreewise-split short complex of cochain
complexes yields a short exact short complex. This is the step where degreewise splitness is
essential: `G` is not assumed exact, but it preserves the *split* short exact sequences in each
degree (`ShortComplex.Splitting.map`), and degreewise short exactness then assembles to a short
exact sequence of complexes. -/
lemma shortExact_map_mapHomologicalComplex_of_degreewise_splitting
    {S : ShortComplex (CochainComplex 𝒜 ℕ)}
    (splits : ∀ n, (S.map (HomologicalComplex.eval 𝒜 (ComplexShape.up ℕ) n)).Splitting)
    (G : 𝒜 ⥤ ℬ) [G.Additive] :
    (S.map (G.mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => ((splits n).map G).shortExact)

/-- **Dimension shift, part (1), from a degreewise-split SES of injective resolutions.**
Given a short exact sequence `0 → A → J → Z → 0` lifted (via the horseshoe) to a
degreewise-split short exact sequence of injective resolutions
`0 → I_A → I_J → I_Z → 0`, presented here as chain maps `φ, ψ` with degreewise splittings,
and with the middle object `J` right-`G`-acyclic, the connecting map of the homology long
exact sequence of `G(I_•)` is an isomorphism in every positive degree:
`(R^{k+1} G)(Z) ≅ (R^{k+2} G)(A)`.

This is the engine of the staircase induction (`rightDerivedIsoOfAcyclicResolution`).
It is stated over the *resolution-level* SES because the object-level dimension-shift theorem
`rightDerivedShiftIsoOfAcyclic` requires the horseshoe lift to produce that SES; once the
horseshoe is available, the object-level statement follows by feeding its output here. -/
noncomputable def Functor.rightDerivedShiftIsoOfSplitResolutionSES
    (G : 𝒜 ⥤ ℬ) [G.Additive] {A J Z : 𝒜}
    (I_A : InjectiveResolution A) (I_J : InjectiveResolution J) (I_Z : InjectiveResolution Z)
    [G.IsRightAcyclic J]
    (φ : I_A.cocomplex ⟶ I_J.cocomplex) (ψ : I_J.cocomplex ⟶ I_Z.cocomplex)
    (w : φ ≫ ψ = 0)
    (splits : ∀ n, ((ShortComplex.mk φ ψ w).map
      (HomologicalComplex.eval 𝒜 (ComplexShape.up ℕ) n)).Splitting)
    (k : ℕ) :
    (G.rightDerived (k + 1)).obj Z ≅ (G.rightDerived (k + 2)).obj A :=
  have hSG : ((ShortComplex.mk φ ψ w).map
      (G.mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact :=
    shortExact_map_mapHomologicalComplex_of_degreewise_splitting splits G
  (I_Z.isoRightDerivedObj G (k + 1)) ≪≫
    hSG.δIso (k + 1) (k + 2) (by simp)
      (G.isZero_homology_mapHomologicalComplex_of_isRightAcyclic I_J k)
      (G.isZero_homology_mapHomologicalComplex_of_isRightAcyclic I_J (k + 1)) ≪≫
    (I_A.isoRightDerivedObj G (k + 2)).symm

omit [HasInjectiveResolutions 𝒜] in
/-- **Horseshoe per-stage monomorphism.** Given an exact short complex
`A → B → C` with `A → B` a monomorphism, and monomorphisms `α : A ↪ P`, `γ : C ↪ Q` with `P`
injective, the map `B → P ⊞ Q` whose first component is the injective extension of `α` along
`A ↪ B` (`Injective.factorThru α S.f`) and whose second component is `B ↠ C ↪ Q` is itself a
monomorphism. This is the cokernel/kernel step driving each stage of the dual Horseshoe Lemma
`InjectiveResolution.ofShortExact`: applied to the `n`-th cosyzygy short exact sequence with
`P = I_A.X (n+1)`, `Q = I_C.X (n+1)`, it produces the monomorphism into the next biproduct term
whose cokernel feeds the following stage. -/
lemma mono_biprod_lift_factorThru_of_exact {S : ShortComplex 𝒜} (hS : S.Exact) [Mono S.f]
    {P Q : 𝒜} [Injective P] (α : S.X₁ ⟶ P) [Mono α] (γ : S.X₃ ⟶ Q) [Mono γ] :
    Mono (biprod.lift (Injective.factorThru α S.f) (S.g ≫ γ)) := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro T x hx
  have h1 : x ≫ Injective.factorThru α S.f = 0 := by simpa using hx =≫ biprod.fst
  have h2 : x ≫ S.g ≫ γ = 0 := by simpa using hx =≫ biprod.snd
  have hxg : x ≫ S.g = 0 := by rw [← cancel_mono γ, zero_comp, Category.assoc]; exact h2
  have hyf : hS.lift x hxg ≫ S.f = x := hS.lift_f x hxg
  have hya : hS.lift x hxg ≫ α = 0 := by
    have h3 : hS.lift x hxg ≫ S.f ≫ Injective.factorThru α S.f = 0 := by
      rw [← Category.assoc, hyf]; exact h1
    rwa [Injective.comp_factorThru] at h3
  have hy0 : hS.lift x hxg = 0 := by rw [← cancel_mono α, zero_comp]; exact hya
  rw [← hyf, hy0, zero_comp]

/-! ## Project-local Mathlib supplement — twisted biproduct of cochain complexes

This block builds the *structural* core of the dual Horseshoe Lemma as a general, injective-free
construction. Given two cochain complexes `K`, `L` and a degreewise family
`τ n : L.X n ⟶ K.X (n+1)` satisfying the cocycle identity
`L.d n (n+1) ≫ τ (n+1) = -(τ n ≫ K.d (n+1) (n+2))`, the biproduct objects `K.X n ⊞ L.X n` with the
twisted matrix differential `[[d_K, τ], [0, d_L]]` form a cochain complex `twistedBiprod τ hτ`,
the coprojection `K ⟶ twistedBiprod` and projection `twistedBiprod ⟶ L` are chain maps, and every
degree is the canonical split short exact sequence of the biproduct.

This is exactly the content of the blueprint sub-lemmas `lem:horseshoe_dComp` (the differential
squares to zero) and `lem:horseshoe_chainMap` (the coprojection/projection are chain maps and the
degrees split); it is isolated here free of injectivity because the only inputs are the cocycle
identity and the biproduct structure. The horseshoe specialises it to `K = I_A.cocomplex`,
`L = I_C.cocomplex` once the twist `τ` has been produced by injectivity. -/

section TwistedBiprod

omit [HasInjectiveResolutions 𝒜]

variable {K L : CochainComplex 𝒜 ℕ} (τ : ∀ n, L.X n ⟶ K.X (n + 1))

/-- The twisted matrix differential `[[d_K, τ], [0, d_L]]` on the degreewise biproduct
`K.X n ⊞ L.X n ⟶ K.X (n+1) ⊞ L.X (n+1)`. -/
noncomputable def twistedBiprodD (n : ℕ) :
    (K.X n ⊞ L.X n) ⟶ (K.X (n + 1) ⊞ L.X (n + 1)) :=
  biprod.lift (biprod.fst ≫ K.d n (n + 1) + biprod.snd ≫ τ n) (biprod.snd ≫ L.d n (n + 1))

@[reassoc (attr := simp)]
lemma twistedBiprodD_fst (n : ℕ) :
    twistedBiprodD τ n ≫ biprod.fst = biprod.fst ≫ K.d n (n + 1) + biprod.snd ≫ τ n := by
  simp [twistedBiprodD]

@[reassoc (attr := simp)]
lemma twistedBiprodD_snd (n : ℕ) :
    twistedBiprodD τ n ≫ biprod.snd = biprod.snd ≫ L.d n (n + 1) := by
  simp [twistedBiprodD]

variable (hτ : ∀ n, L.d n (n + 1) ≫ τ (n + 1) = -(τ n ≫ K.d (n + 1) (n + 2)))

include hτ in
lemma twistedBiprodD_comp (n : ℕ) :
    twistedBiprodD τ n ≫ twistedBiprodD τ (n + 1) = 0 := by
  apply biprod.hom_ext
  · simp only [Category.assoc, twistedBiprodD_fst, Preadditive.comp_add,
      twistedBiprodD_fst_assoc, twistedBiprodD_snd_assoc, zero_comp]
    rw [Preadditive.add_comp, Category.assoc, Category.assoc, HomologicalComplex.d_comp_d,
      comp_zero, zero_add, ← Preadditive.comp_add, hτ n, add_neg_cancel, comp_zero]
  · simp only [Category.assoc, twistedBiprodD_snd, twistedBiprodD_snd_assoc, zero_comp]
    rw [HomologicalComplex.d_comp_d, comp_zero]

/-- The twisted biproduct cochain complex with differential `[[d_K, τ], [0, d_L]]`. -/
noncomputable def twistedBiprod : CochainComplex 𝒜 ℕ :=
  CochainComplex.of (fun n => K.X n ⊞ L.X n) (twistedBiprodD τ) (twistedBiprodD_comp τ hτ)

@[simp]
lemma twistedBiprod_X (n : ℕ) : (twistedBiprod τ hτ).X n = (K.X n ⊞ L.X n) := rfl

@[simp]
lemma twistedBiprod_d (n : ℕ) : (twistedBiprod τ hτ).d n (n + 1) = twistedBiprodD τ n := by
  simp [twistedBiprod, CochainComplex.of_d]

/-- The coprojection `K ⟶ twistedBiprod τ hτ`, degreewise `biprod.inl`. -/
noncomputable def twistedBiprodInl : K ⟶ twistedBiprod τ hτ where
  f n := biprod.inl
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    simp only [twistedBiprod_d]
    apply biprod.hom_ext <;> simp

/-- The projection `twistedBiprod τ hτ ⟶ L`, degreewise `biprod.snd`. -/
noncomputable def twistedBiprodSnd : twistedBiprod τ hτ ⟶ L where
  f n := biprod.snd
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    simp [twistedBiprod_d]

@[simp]
lemma twistedBiprodInl_f (n : ℕ) : (twistedBiprodInl τ hτ).f n = biprod.inl := rfl

@[simp]
lemma twistedBiprodSnd_f (n : ℕ) : (twistedBiprodSnd τ hτ).f n = biprod.snd := rfl

lemma twistedBiprodInl_comp_Snd : twistedBiprodInl τ hτ ≫ twistedBiprodSnd τ hτ = 0 := by
  ext n
  simp

/-- Each degree of `0 → K → twistedBiprod → L → 0` is the canonical split short exact sequence of
the biproduct `K.X n ⊞ L.X n`. -/
noncomputable def twistedBiprodSplitting (n : ℕ) :
    ((ShortComplex.mk _ _ (twistedBiprodInl_comp_Snd τ hτ)).map
      (HomologicalComplex.eval 𝒜 (ComplexShape.up ℕ) n)).Splitting where
  r := biprod.fst
  s := biprod.inr
  -- v4.31.0: `ShortComplex.Splitting` gained `f_r`/`s_g` fields whose default `cat_disch` doesn't
  -- reduce the `eval`-mapped biprod; the biprod identities close them by defeq.
  f_r := biprod.inl_fst
  s_g := biprod.inr_snd
  id := biprod.total

end TwistedBiprod

/-! ## Project-local Mathlib supplement — the horseshoe twist family

Given a short exact sequence `ses : 0 → A → B → C → 0` and chosen injective resolutions
`I_A`, `I_C`, this block constructs the off-diagonal twist family
`τ n : I_C.X n ⟶ I_A.X (n+1)` together with the augmentation first component, satisfying the
cocycle identity `d_C n ≫ τ (n+1) = -(τ n ≫ d_A (n+1))`. Each `τ` is produced by the universal
lifting property of injectives (`Injective.factorThru` / `ShortComplex.Exact.descToInjective`)
against the cosyzygy monomorphisms of `I_C`. This is the blueprint sub-lemma `lem:horseshoe_twist`
(the recursion kernel). Combined with the `twistedBiprod` construction above it yields the middle
complex of the dual Horseshoe Lemma. -/

namespace InjectiveResolution

section OfShortExact

variable {ses : ShortComplex 𝒜} (hses : ses.ShortExact)
  (I_A : InjectiveResolution ses.X₁) (I_C : InjectiveResolution ses.X₃)

/-- First component `B ⟶ I_A^0` of the horseshoe augmentation: the injective extension of the
augmentation `A ⟶ I_A^0` along the monomorphism `A ↪ B`. -/
noncomputable def horseshoeβ₁ : ses.X₂ ⟶ I_A.cocomplex.X 0 :=
  @Injective.factorThru _ _ _ _ _ (I_A.injective 0) (I_A.ι.f 0) ses.f hses.mono_f

@[reassoc (attr := simp)]
lemma f_comp_horseshoeβ₁ : ses.f ≫ horseshoeβ₁ hses I_A = I_A.ι.f 0 :=
  @Injective.comp_factorThru _ _ _ _ _ (I_A.injective 0) (I_A.ι.f 0) ses.f hses.mono_f

/-- Auxiliary map `C ⟶ I_A^1` through which `β₁ ≫ d_A^0` factors (since it kills `A`). -/
noncomputable def horseshoeH : ses.X₃ ⟶ I_A.cocomplex.X 1 :=
  hses.exact.descToInjective (horseshoeβ₁ hses I_A ≫ I_A.cocomplex.d 0 1) (by
    rw [← Category.assoc, f_comp_horseshoeβ₁]; exact I_A.ι_f_zero_comp_complex_d)

@[reassoc (attr := simp)]
lemma g_comp_horseshoeH :
    ses.g ≫ horseshoeH hses I_A = horseshoeβ₁ hses I_A ≫ I_A.cocomplex.d 0 1 :=
  hses.exact.comp_descToInjective _ _

lemma horseshoeH_comp_d : horseshoeH hses I_A ≫ I_A.cocomplex.d 1 2 = 0 := by
  haveI := hses.epi_g
  rw [← cancel_epi ses.g, comp_zero, ← Category.assoc, g_comp_horseshoeH, Category.assoc,
    HomologicalComplex.d_comp_d, comp_zero]

/-- The base twist `τ⁰ : I_C^0 ⟶ I_A^1`, extending `-(C ⟶ I_A^1)` along `C ↪ I_C^0`. -/
noncomputable def horseshoeτZero : I_C.cocomplex.X 0 ⟶ I_A.cocomplex.X 1 :=
  @Injective.factorThru _ _ _ _ _ (I_A.injective 1) (-horseshoeH hses I_A) (I_C.ι.f 0)
    (mono_of_isLimit_fork I_C.isLimitKernelFork)

@[reassoc (attr := simp)]
lemma ιC_comp_horseshoeτZero :
    I_C.ι.f 0 ≫ horseshoeτZero hses I_A I_C = -horseshoeH hses I_A :=
  @Injective.comp_factorThru _ _ _ _ _ (I_A.injective 1) (-horseshoeH hses I_A) (I_C.ι.f 0)
    (mono_of_isLimit_fork I_C.isLimitKernelFork)

lemma horseshoeτZero_hf :
    I_C.ι.f 0 ≫ (-(horseshoeτZero hses I_A I_C ≫ I_A.cocomplex.d 1 2)) = 0 := by
  have e : (-horseshoeH hses I_A) ≫ I_A.cocomplex.d 1 2 = 0 := by
    rw [Preadditive.neg_comp, horseshoeH_comp_d, neg_zero]
  rw [Preadditive.comp_neg, neg_eq_zero, ← Category.assoc, ιC_comp_horseshoeτZero]
  exact e

/-- The recursion carrying, at each degree `n`, consecutive twists `τⁿ`, `τⁿ⁺¹` together with the
cocycle identity `d_C^n ≫ τⁿ⁺¹ = -(τⁿ ≫ d_A^{n+1})`. The step uses the lifting property of the
injective `I_A^{n+3}` against the cosyzygy mono of `I_C` (`exact_succ`); the base uses the
augmentation exactness `exact₀`. -/
noncomputable def twistPair : (n : ℕ) →
    Σ' (t0 : I_C.cocomplex.X n ⟶ I_A.cocomplex.X (n + 1))
       (_t1 : I_C.cocomplex.X (n + 1) ⟶ I_A.cocomplex.X (n + 2)),
       I_C.cocomplex.d n (n + 1) ≫ _t1 = -(t0 ≫ I_A.cocomplex.d (n + 1) (n + 2))
  | 0 => ⟨horseshoeτZero hses I_A I_C,
      I_C.exact₀.descToInjective (-(horseshoeτZero hses I_A I_C ≫ I_A.cocomplex.d 1 2))
        (horseshoeτZero_hf hses I_A I_C),
      I_C.exact₀.comp_descToInjective _ _⟩
  | (n + 1) =>
      let p := twistPair n
      ⟨p.2.1,
        (I_C.exact_succ n).descToInjective (-(p.2.1 ≫ I_A.cocomplex.d (n + 2) (n + 3))) (by
          have e : (-(p.1 ≫ I_A.cocomplex.d (n + 1) (n + 2))) ≫ I_A.cocomplex.d (n + 2) (n + 3)
              = 0 := by
            rw [Preadditive.neg_comp, Category.assoc, HomologicalComplex.d_comp_d, comp_zero,
              neg_zero]
          rw [Preadditive.comp_neg, neg_eq_zero, ← Category.assoc, p.2.2]
          exact e),
        (I_C.exact_succ n).comp_descToInjective _ _⟩

/-- The horseshoe off-diagonal twist family `τⁿ : I_C^n ⟶ I_A^{n+1}`. -/
noncomputable def horseshoeτ (n : ℕ) : I_C.cocomplex.X n ⟶ I_A.cocomplex.X (n + 1) :=
  (twistPair hses I_A I_C n).1

/-- The cocycle identity for the horseshoe twist: `d_C^n ≫ τⁿ⁺¹ = -(τⁿ ≫ d_A^{n+1})`. -/
lemma horseshoeτ_cocycle (n : ℕ) :
    I_C.cocomplex.d n (n + 1) ≫ horseshoeτ hses I_A I_C (n + 1) =
      -(horseshoeτ hses I_A I_C n ≫ I_A.cocomplex.d (n + 1) (n + 2)) :=
  (twistPair hses I_A I_C n).2.2

/-- The middle cochain complex `I_B` of the horseshoe: the twisted biproduct of `I_A` and `I_C`
along the horseshoe twist family. -/
noncomputable def horseshoeMid : CochainComplex 𝒜 ℕ :=
  twistedBiprod (horseshoeτ hses I_A I_C) (horseshoeτ_cocycle hses I_A I_C)

/-- The short complex `0 → I_A → I_B → I_C → 0` of the horseshoe, with the coprojection and
projection chain maps. -/
noncomputable def horseshoeSES : ShortComplex (CochainComplex 𝒜 ℕ) :=
  ShortComplex.mk _ _
    (twistedBiprodInl_comp_Snd (horseshoeτ hses I_A I_C) (horseshoeτ_cocycle hses I_A I_C))

/-- Each degree of the horseshoe short complex is the canonical biproduct splitting. -/
noncomputable def horseshoeSES_splitting (n : ℕ) :
    ((horseshoeSES hses I_A I_C).map
      (HomologicalComplex.eval 𝒜 (ComplexShape.up ℕ) n)).Splitting :=
  twistedBiprodSplitting (horseshoeτ hses I_A I_C) (horseshoeτ_cocycle hses I_A I_C) n

/-- The horseshoe short complex `0 → I_A → I_B → I_C → 0` is short exact (degreewise split). -/
lemma horseshoeSES_shortExact : (horseshoeSES hses I_A I_C).ShortExact :=
  shortExact_of_degreewise_splitting (horseshoeSES_splitting hses I_A I_C)

@[simp]
lemma horseshoeτ_zero : horseshoeτ hses I_A I_C 0 = horseshoeτZero hses I_A I_C := rfl

/-- Clean-domain degree-0 augmentation map of `I_C` (definitionally `I_C.ι.f 0`, but with syntactic
domain `ses.X₃` so it composes cleanly on the left with `ses.g`; the bundled `I_C.ι.f 0` carries the
single-complex domain `((single₀).obj ses.X₃).X 0`, which blocks rewriting under `ses.g ≫ -`). -/
noncomputable def ιC0 : ses.X₃ ⟶ I_C.cocomplex.X 0 := I_C.ι.f 0

lemma ιC0_comp_d : ιC0 I_C ≫ I_C.cocomplex.d 0 1 = 0 := I_C.ι_f_zero_comp_complex_d

lemma ιC0_comp_τZero :
    ιC0 I_C ≫ horseshoeτZero hses I_A I_C = -horseshoeH hses I_A :=
  ιC_comp_horseshoeτZero hses I_A I_C

/-- The horseshoe augmentation `β : B ⟶ I_A^0 ⊞ I_C^0`. -/
noncomputable def horseshoeβ : ses.X₂ ⟶ I_A.cocomplex.X 0 ⊞ I_C.cocomplex.X 0 :=
  biprod.lift (horseshoeβ₁ hses I_A) (ses.g ≫ ιC0 I_C)

@[reassoc (attr := simp)]
lemma horseshoeβ_fst : horseshoeβ hses I_A I_C ≫ biprod.fst = horseshoeβ₁ hses I_A := by
  rw [horseshoeβ, biprod.lift_fst]

@[reassoc (attr := simp)]
lemma horseshoeβ_snd : horseshoeβ hses I_A I_C ≫ biprod.snd = ses.g ≫ ιC0 I_C := by
  rw [horseshoeβ, biprod.lift_snd]

/-- The augmentation composes to zero with the first horseshoe differential, so it descends to a
chain map from `B` (in degree 0) into the middle complex. -/
lemma horseshoeβ_comp_d :
    horseshoeβ hses I_A I_C ≫ twistedBiprodD (horseshoeτ hses I_A I_C) 0 = 0 := by
  have e : ses.g ≫ ιC0 I_C ≫ horseshoeτZero hses I_A I_C
      = -(horseshoeβ₁ hses I_A ≫ I_A.cocomplex.d 0 (0 + 1)) := by
    rw [ιC0_comp_τZero, Preadditive.comp_neg, g_comp_horseshoeH]
  have e2 : ses.g ≫ ιC0 I_C ≫ I_C.cocomplex.d 0 (0 + 1) = 0 := by
    have h0 : ιC0 I_C ≫ I_C.cocomplex.d 0 (0 + 1) = 0 := I_C.ι_f_zero_comp_complex_d
    rw [h0, comp_zero]
  apply biprod.hom_ext
  · simp only [Category.assoc, twistedBiprodD_fst, Preadditive.comp_add,
      horseshoeβ_fst_assoc, horseshoeβ_snd_assoc, horseshoeτ_zero, zero_comp]
    rw [e, add_neg_cancel]
  · simp only [Category.assoc, twistedBiprodD_snd, horseshoeβ_snd_assoc, zero_comp]
    exact e2

/-- Maps out of a `single₀` cochain complex are determined by their degree-`0` component. -/
private lemma single₀_hom_ext {X : 𝒜} {D : CochainComplex 𝒜 ℕ}
    {g h : (CochainComplex.single₀ 𝒜).obj X ⟶ D} (h0 : g.f 0 = h.f 0) : g = h := by
  apply (CochainComplex.fromSingle₀Equiv D X).injective
  ext
  exact h0

/-- The horseshoe augmentation packaged as a chain map `(single₀ B) ⟶ I_B`, with degree-`0`
component the augmentation `β : B ⟶ I_A^0 ⊞ I_C^0`. -/
noncomputable def horseshoeι :
    (CochainComplex.single₀ 𝒜).obj ses.X₂ ⟶ horseshoeMid hses I_A I_C :=
  (CochainComplex.fromSingle₀Equiv (horseshoeMid hses I_A I_C) ses.X₂).symm
    ⟨horseshoeβ hses I_A I_C, by
      show horseshoeβ hses I_A I_C ≫
          (twistedBiprod (horseshoeτ hses I_A I_C) (horseshoeτ_cocycle hses I_A I_C)).d 0 1 = 0
      rw [twistedBiprod_d]
      exact horseshoeβ_comp_d hses I_A I_C⟩

@[simp]
lemma horseshoeι_f_zero : (horseshoeι hses I_A I_C).f 0 = horseshoeβ hses I_A I_C := by
  exact CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

/-- The augmentation `β : B ⟶ I_A^0 ⊞ I_C^0` is a monomorphism (the base stage of the horseshoe
recursion: `mono_biprod_lift_factorThru_of_exact` applied to the original short exact sequence). -/
lemma mono_horseshoeβ : Mono (horseshoeβ hses I_A I_C) := by
  haveI := hses.mono_f
  haveI : Injective (I_A.cocomplex.X 0) := I_A.injective 0
  -- The domain of `I_A.ι.f 0` is `((single₀).obj ses.X₁).X 0`, not syntactically `ses.X₁`; we
  -- ascribe the clean domain so the `Mono` instance matches the lemma's `α : S.X₁ ⟶ P`.
  haveI : Mono (show ses.X₁ ⟶ I_A.cocomplex.X 0 from I_A.ι.f 0) :=
    mono_of_isLimit_fork I_A.isLimitKernelFork
  haveI : Mono (show ses.X₃ ⟶ I_C.cocomplex.X 0 from I_C.ι.f 0) :=
    mono_of_isLimit_fork I_C.isLimitKernelFork
  exact mono_biprod_lift_factorThru_of_exact hses.exact
    (show ses.X₁ ⟶ I_A.cocomplex.X 0 from I_A.ι.f 0)
    (show ses.X₃ ⟶ I_C.cocomplex.X 0 from I_C.ι.f 0)

/-- The horseshoe left square: `I_A.ι ≫ (I_A → I_B) = (single₀ A → single₀ B) ≫ horseshoeι`. -/
lemma horseshoeφ_comm₁₂ :
    I_A.ι ≫ (horseshoeSES hses I_A I_C).f =
      (ses.map (CochainComplex.single₀ 𝒜)).f ≫ horseshoeι hses I_A I_C := by
  apply single₀_hom_ext
  change (I_A.ι ≫ twistedBiprodInl (horseshoeτ hses I_A I_C)
      (horseshoeτ_cocycle hses I_A I_C)).f 0 =
    ((CochainComplex.single₀ 𝒜).map ses.f ≫ horseshoeι hses I_A I_C).f 0
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, twistedBiprodInl_f,
    CochainComplex.single₀_map_f_zero, horseshoeι_f_zero, horseshoeβ]
  -- The biproduct projections from `twistedBiprod` carry a `(twistedBiprod).X 0`-flavoured
  -- domain; ascribe the clean biproduct so the `biprod.*` simp lemmas fire.
  change I_A.ι.f 0 ≫ (biprod.inl : I_A.cocomplex.X 0 ⟶ I_A.cocomplex.X 0 ⊞ I_C.cocomplex.X 0) =
    ses.f ≫ biprod.lift (horseshoeβ₁ hses I_A) (ses.g ≫ ιC0 I_C)
  let a₀ : ses.X₁ ⟶ I_A.cocomplex.X 0 := I_A.ι.f 0
  have hfa₀ : ses.f ≫ horseshoeβ₁ hses I_A = a₀ := f_comp_horseshoeβ₁ hses I_A
  have e :
      a₀ ≫ (biprod.inl : I_A.cocomplex.X 0 ⟶ I_A.cocomplex.X 0 ⊞ I_C.cocomplex.X 0) =
        ses.f ≫ biprod.lift (horseshoeβ₁ hses I_A) (ses.g ≫ ιC0 I_C) := by
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.inl_fst, Category.comp_id, biprod.lift_fst, hfa₀]
    · have hleft :
          (a₀ ≫ (biprod.inl : I_A.cocomplex.X 0 ⟶
              I_A.cocomplex.X 0 ⊞ I_C.cocomplex.X 0)) ≫ biprod.snd = 0 := by
        rw [Category.assoc, biprod.inl_snd, comp_zero]
      have hright :
          (ses.f ≫ biprod.lift (horseshoeβ₁ hses I_A) (ses.g ≫ ιC0 I_C)) ≫
              (biprod.snd : I_A.cocomplex.X 0 ⊞ I_C.cocomplex.X 0 ⟶
                I_C.cocomplex.X 0) = 0 := by
        rw [Category.assoc, biprod.lift_snd, ← Category.assoc, ses.zero, zero_comp]
      exact hleft.trans hright.symm
  exact e

/-- The horseshoe right square: `horseshoeι ≫ (I_B → I_C) = (single₀ B → single₀ C) ≫ I_C.ι`. -/
lemma horseshoeφ_comm₂₃ :
    horseshoeι hses I_A I_C ≫ (horseshoeSES hses I_A I_C).g =
      (ses.map (CochainComplex.single₀ 𝒜)).g ≫ I_C.ι := by
  apply single₀_hom_ext
  change (horseshoeι hses I_A I_C).f 0 ≫
      (twistedBiprodSnd (horseshoeτ hses I_A I_C)
        (horseshoeτ_cocycle hses I_A I_C)).f 0 =
    ((CochainComplex.single₀ 𝒜).map ses.g).f 0 ≫ I_C.ι.f 0
  rw [twistedBiprodSnd_f,
    CochainComplex.single₀_map_f_zero, horseshoeι_f_zero, horseshoeβ]
  change biprod.lift (horseshoeβ₁ hses I_A) (ses.g ≫ ιC0 I_C) ≫
    (biprod.snd : I_A.cocomplex.X 0 ⊞ I_C.cocomplex.X 0 ⟶ I_C.cocomplex.X 0) = ses.g ≫ I_C.ι.f 0
  rw [biprod.lift_snd]
  rfl

/-- The morphism of short complexes of cochain complexes
`(single₀ A → single₀ B → single₀ C) ⟶ (I_A → I_B → I_C)` whose outer verticals are the
resolution augmentations `I_A.ι`, `I_C.ι` and whose middle vertical is the horseshoe augmentation
`horseshoeι`. -/
noncomputable def horseshoeφ :
    ses.map (CochainComplex.single₀ 𝒜) ⟶ horseshoeSES hses I_A I_C :=
  ShortComplex.homMk I_A.ι (horseshoeι hses I_A I_C) I_C.ι
    (horseshoeφ_comm₁₂ hses I_A I_C) (horseshoeφ_comm₂₃ hses I_A I_C)

@[simp] lemma horseshoeφ_τ₁ : (horseshoeφ hses I_A I_C).τ₁ = I_A.ι := rfl
@[simp] lemma horseshoeφ_τ₂ : (horseshoeφ hses I_A I_C).τ₂ = horseshoeι hses I_A I_C := rfl
@[simp] lemma horseshoeφ_τ₃ : (horseshoeφ hses I_A I_C).τ₃ = I_C.ι := rfl

/-- The horseshoe augmentation `(single₀ B) ⟶ I_B` is a quasi-isomorphism: by the middle-term
quasi-isomorphism transfer `quasiIso_τ₂`, since the outer augmentations `I_A.ι`, `I_C.ι` are
quasi-isomorphisms (they are injective resolutions) and `β` is mono. -/
lemma quasiIso_horseshoeι : QuasiIso (horseshoeι hses I_A I_C) := by
  have key := HomologicalComplex.HomologySequence.quasiIso_τ₂ (horseshoeφ hses I_A I_C)
    (hses.map_of_exact (CochainComplex.single₀ 𝒜))
    (horseshoeSES_shortExact hses I_A I_C)
    (h₁ := I_A.quasiIso) (h₃ := I_C.quasiIso)
    (hbMono := by
      intro i hi
      obtain rfl : i = 0 := by
        rcases i with _ | m
        · rfl
        · exact absurd rfl (hi m)
      have h := mono_horseshoeβ hses I_A I_C
      simp only [horseshoeφ_τ₂, horseshoeι_f_zero] at h ⊢
      exact h)
    (hbEpi := by
      intro i hi
      exact absurd rfl (hi (i + 1)))
  simp only [horseshoeφ_τ₂] at key ⊢
  exact key

/-- **The middle complex resolves `B`** (blueprint `lem:horseshoe_resolvesMiddle`). The horseshoe
middle complex `I_B = twistedBiprod I_A I_C`, with augmentation `β`, is an injective resolution of
`B = ses.X₂`: its terms `I_A^n ⊞ I_C^n` are injective, and the augmentation is a quasi-isomorphism
by `quasiIso_horseshoeι`. -/
noncomputable def ofShortExact_resolvesMiddle : InjectiveResolution ses.X₂ where
  cocomplex := horseshoeMid hses I_A I_C
  injective n := by
    haveI : Injective (I_A.cocomplex.X n) := I_A.injective n
    haveI : Injective (I_C.cocomplex.X n) := I_C.injective n
    exact (inferInstance : Injective (I_A.cocomplex.X n ⊞ I_C.cocomplex.X n))
  ι := horseshoeι hses I_A I_C
  quasiIso := quasiIso_horseshoeι hses I_A I_C

/-- **Dual Horseshoe Lemma** (blueprint `lem:injective_resolution_of_ses`). From a short exact
sequence `0 → A → B → C → 0` and chosen injective resolutions `I_A`, `I_C`, the horseshoe produces
an injective resolution of the middle term `B` fitting into the degreewise-split short exact
sequence of cochain complexes `0 → I_A → I_B → I_C → 0` (`horseshoeSES`, short exact by
`horseshoeSES_shortExact` and degreewise split by `horseshoeSES_splitting`). -/
noncomputable def ofShortExact : InjectiveResolution ses.X₂ :=
  ofShortExact_resolvesMiddle hses I_A I_C

end OfShortExact

end InjectiveResolution

/-! ## Project-local Mathlib supplement — the dimension-shift isomorphism -/

/-- **Dimension shift across an acyclic short exact sequence** (blueprint
`lem:acyclic_dimension_shift`, TARGET 2). Given an additive functor `G` and a short exact sequence
`0 → A → J → Z → 0` with middle term `J` right-`G`-acyclic, the connecting maps of the long exact
sequence of right-derived functors furnish isomorphisms
`(R^{k+1} G)(Z) ≅ (R^{k+2} G)(A)` for all `k`.

The proof feeds the dual Horseshoe Lemma (`InjectiveResolution.ofShortExact_resolvesMiddle`) — a
degreewise-split short exact sequence of injective resolutions `0 → I_A → I_B → I_C → 0` — into the
resolution-level dimension shift `rightDerivedShiftIsoOfSplitResolutionSES`. -/
noncomputable def Functor.rightDerivedShiftIsoOfAcyclic
    (G : 𝒜 ⥤ ℬ) [G.Additive] {ses : ShortComplex 𝒜} (hses : ses.ShortExact)
    [G.IsRightAcyclic ses.X₂] (k : ℕ) :
    (G.rightDerived (k + 1)).obj ses.X₃ ≅ (G.rightDerived (k + 2)).obj ses.X₁ :=
  let I_A : InjectiveResolution ses.X₁ := (inferInstance : HasInjectiveResolution ses.X₁).out.some
  let I_C : InjectiveResolution ses.X₃ := (inferInstance : HasInjectiveResolution ses.X₃).out.some
  G.rightDerivedShiftIsoOfSplitResolutionSES I_A
    (InjectiveResolution.ofShortExact_resolvesMiddle hses I_A I_C) I_C
    (InjectiveResolution.horseshoeSES hses I_A I_C).f
    (InjectiveResolution.horseshoeSES hses I_A I_C).g
    (InjectiveResolution.horseshoeSES hses I_A I_C).zero
    (InjectiveResolution.horseshoeSES_splitting hses I_A I_C) k

/-! ## Project-local Mathlib supplement — lowest-degree cokernel description -/

/-- **Lowest-degree cokernel description across an acyclic short exact sequence** (blueprint
`lem:acyclic_one_iso_coker`, leaf of TARGET 3). For an additive left-exact functor `G` and a short
exact sequence `0 → A → J → Z → 0` with middle term `J` right-`G`-acyclic, the first right-derived
functor at `A` is the cokernel of `G` applied to the surjection `J ↠ Z`:
`(R¹ G)(A) ≅ coker(G(J) → G(Z))`.

The proof reads the bottom of the homology long exact sequence of the horseshoe-lifted,
degreewise-split short exact sequence of injective resolutions `0 → I_A → I_J → I_Z → 0` after
applying `G`. There `δ⁰ : H⁰(GI_Z) → H¹(GI_A)` is epi (because `H¹(GI_J) = 0` by acyclicity of `J`)
and exact after `homologyMap(Gψ) 0 : H⁰(GI_J) → H⁰(GI_Z)`, so `δ⁰` exhibits `H¹(GI_A) ≅ (R¹G)(A)`
as the cokernel of `homologyMap(Gψ) 0`. The naturality of `isoRightDerivedObj` (lifting `ses.g` to
`ψ`) and of `rightDerivedZeroIsoSelf` (`R⁰G ≅ G`) identify `homologyMap(Gψ) 0` with `G.map ses.g`.
-/
noncomputable def Functor.rightDerivedOneIsoCokerOfAcyclic
    (G : 𝒜 ⥤ ℬ) [G.Additive] [PreservesFiniteLimits G]
    {ses : ShortComplex 𝒜} (hses : ses.ShortExact) [G.IsRightAcyclic ses.X₂] :
    (G.rightDerived 1).obj ses.X₁ ≅ cokernel (G.map ses.g) := by
  classical
  let I_A : InjectiveResolution ses.X₁ := (inferInstance : HasInjectiveResolution ses.X₁).out.some
  let I_C : InjectiveResolution ses.X₃ := (inferInstance : HasInjectiveResolution ses.X₃).out.some
  let I_J : InjectiveResolution ses.X₂ :=
    InjectiveResolution.ofShortExact_resolvesMiddle hses I_A I_C
  let ψ : I_J.cocomplex ⟶ I_C.cocomplex := (InjectiveResolution.horseshoeSES hses I_A I_C).g
  have hSG : ((InjectiveResolution.horseshoeSES hses I_A I_C).map
      (G.mapHomologicalComplex (ComplexShape.up ℕ))).ShortExact :=
    shortExact_map_mapHomologicalComplex_of_degreewise_splitting
      (InjectiveResolution.horseshoeSES_splitting hses I_A I_C) G
  haveI hepi : Epi (hSG.δ 0 1 (by simp)) :=
    hSG.epi_δ 0 1 (by simp)
      (G.isZero_homology_mapHomologicalComplex_of_isRightAcyclic I_J 0)
  have hex := hSG.homology_exact₃ 0 1 (by simp)
  have hcok := hex.gIsCokernel
  have comm : I_J.ι.f 0 ≫ ψ.f 0 = ses.g ≫ I_C.ι.f 0 := by
    have h0 := congrArg (fun m => HomologicalComplex.Hom.f m 0)
      (InjectiveResolution.horseshoeφ_comm₂₃ hses I_A I_C)
    change (InjectiveResolution.horseshoeι hses I_A I_C).f 0 ≫
        (InjectiveResolution.horseshoeSES hses I_A I_C).g.f 0 =
      ((CochainComplex.single₀ 𝒜).map ses.g).f 0 ≫ I_C.ι.f 0 at h0
    rw [CochainComplex.single₀_map_f_zero] at h0
    change (InjectiveResolution.horseshoeι hses I_A I_C).f 0 ≫
        (InjectiveResolution.horseshoeSES hses I_A I_C).g.f 0 =
      ses.g ≫ I_C.ι.f 0
    exact h0
  refine (I_A.isoRightDerivedObj G 1) ≪≫
    (IsColimit.coconePointUniqueUpToIso
      (cokernelIsCokernel (HomologicalComplex.homologyMap
        ((InjectiveResolution.horseshoeSES hses I_A I_C).map
          (G.mapHomologicalComplex (ComplexShape.up ℕ))).g 0)) hcok).symm ≪≫
    (cokernel.mapIso _ ((G.rightDerived 0).map ses.g)
      (I_J.isoRightDerivedObj G 0).symm (I_C.isoRightDerivedObj G 0).symm ?_) ≪≫
    cokernel.mapIso _ (G.map ses.g)
      ((G.rightDerivedZeroIsoSelf).app ses.X₂) ((G.rightDerivedZeroIsoSelf).app ses.X₃)
      ((G.rightDerivedZeroIsoSelf).hom.naturality ses.g)
  exact
    (InjectiveResolution.isoRightDerivedObj_inv_naturality ses.g I_J I_C ψ comm G 0).symm

/-! ## Project-local Mathlib supplement — cosyzygy short exact sequences

For an exact cochain complex `K` (the augmentation-dropped resolution `J⁰ → J¹ → ⋯`), the
cosyzygies `Zⁿ := K.cycles n = ker(dⁿ)` fit into short exact sequences
`(Sₙ) : 0 → Zⁿ → Kⁿ → Zⁿ⁺¹ → 0`, where the inclusion is `iCycles` and the surjection is the
corestriction `toCycles` of the differential onto the next cycles. These are the sequences cut
out of the resolution that drive the dimension-shift staircase in the comparison theorem
`rightDerivedIsoOfAcyclicResolution` (blueprint `lem:cosyzygy_ses`). The construction is purely
abelian-categorical; the right-`G`-acyclicity of the middle terms `Kⁿ` is carried as a typeclass
hypothesis only at the point of use. These declarations are not in Mathlib. -/

section Cosyzygy

omit [HasInjectiveResolutions 𝒜]

/-- The cosyzygy composite `Zⁿ ↪ Kⁿ ↠ Zⁿ⁺¹` vanishes: the cycles inclusion lands in the kernel
of the differential, hence in the kernel of its corestriction `toCycles`. -/
theorem cosyzygy_iCycles_comp_toCycles (K : CochainComplex 𝒜 ℕ) (n : ℕ) :
    K.iCycles n ≫ K.toCycles n (n + 1) = 0 := by
  rw [← cancel_mono (K.iCycles (n + 1)), Category.assoc, HomologicalComplex.toCycles_i,
    HomologicalComplex.iCycles_d, zero_comp]

/-- If the complex `K` is exact at `n + 1`, the corestriction `toCycles n (n+1) : Kⁿ → Zⁿ⁺¹` is an
epimorphism: its cokernel is the homology `Hⁿ⁺¹(K)`, which vanishes by exactness. -/
theorem epi_toCycles_of_exactAt (K : CochainComplex 𝒜 ℕ) (n : ℕ) (h : K.ExactAt (n + 1)) :
    Epi (K.toCycles n (n + 1)) := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology] at h
  have hcok := K.homologyIsCokernel n (n + 1) (by simp)
  rw [Preadditive.epi_iff_cancel_zero]
  intro T g hg
  set d := hcok.desc (CokernelCofork.ofπ g (by simpa using hg)) with hdd
  have hd : K.homologyπ (n + 1) ≫ d = g := hcok.fac _ Limits.WalkingParallelPair.one
  have hz : K.homologyπ (n + 1) = 0 := h.eq_of_tgt _ _
  rw [← hd, hz]; exact zero_comp

/-- The cycles inclusion `iCycles n` is the kernel of the corestriction `toCycles n (n+1)`: both
`d n (n+1)` and `toCycles n (n+1)` have the same kernel, since `d = toCycles ≫ (mono iCycles)`. -/
noncomputable def cosyzygyKernelFork (K : CochainComplex 𝒜 ℕ) (n : ℕ) :
    Limits.IsLimit
      (Limits.KernelFork.ofι (K.iCycles n) (cosyzygy_iCycles_comp_toCycles K n)) := by
  have hk := K.cyclesIsKernel n (n + 1) (by simp)
  have key : ∀ {T : 𝒜} (x : T ⟶ K.X n),
      x ≫ K.toCycles n (n + 1) = 0 → x ≫ K.d n (n + 1) = 0 := by
    intro T x hx
    rw [← K.toCycles_i n (n + 1), ← Category.assoc, hx, zero_comp]
  refine Limits.KernelFork.IsLimit.ofι _ _
    (fun {T} x hx => hk.lift (Limits.KernelFork.ofι x (key x hx)))
    (fun {T} x hx => hk.fac _ Limits.WalkingParallelPair.zero)
    (fun {T} x hx m hmeq => by
      have e2 : hk.lift (Limits.KernelFork.ofι x (key x hx)) ≫ K.iCycles n = x :=
        hk.fac _ Limits.WalkingParallelPair.zero
      rw [← cancel_mono (K.iCycles n)]
      exact hmeq.trans e2.symm)

/-- The `n`-th cosyzygy short complex `Zⁿ → Kⁿ → Zⁿ⁺¹` (`iCycles` then `toCycles`). -/
noncomputable def Functor.cosyzygyShortComplex (K : CochainComplex 𝒜 ℕ) (n : ℕ) :
    ShortComplex 𝒜 :=
  ShortComplex.mk (K.iCycles n) (K.toCycles n (n + 1)) (cosyzygy_iCycles_comp_toCycles K n)

/-- **Cosyzygy short exact sequence** (blueprint `lem:cosyzygy_ses`). For a complex `K` exact at
`n + 1`, the cosyzygy short complex `0 → Zⁿ → Kⁿ → Zⁿ⁺¹ → 0` is short exact: the inclusion
`iCycles n` is a monomorphism and a kernel of the corestriction `toCycles n (n+1)`, which is an
epimorphism by exactness. -/
theorem Functor.cosyzygyShortExact (K : CochainComplex 𝒜 ℕ) (n : ℕ)
    (h : K.ExactAt (n + 1)) : (Functor.cosyzygyShortComplex K n).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (cosyzygyKernelFork K n)
  mono_f := by dsimp [Functor.cosyzygyShortComplex]; infer_instance
  epi_g := epi_toCycles_of_exactAt K n h

/-- **Applied cosyzygy is the cocycle object** (core of blueprint `lem:applied_cosyzygy_cycles`).
A finite-limit-preserving (e.g. left-exact) functor `G` carries the cycles object
`Zⁿ = K.cycles n` of a complex to the cycles object of the applied complex `G(K)` — that is, to
the `n`-th cocycle object `ker(G(dⁿ) : G(Kⁿ) → G(Kⁿ⁺¹))`. This is the left-exactness
identification `G(Zⁿ) ≅ ker(G(Jⁿ) → G(J^{n+1}))`: `G` preserves the kernel
`iCycles n` defining the cycles, transported to the canonical cycles kernel of `G(K)`. -/
noncomputable def Functor.gCosyzygyIsoCocycles (G : 𝒜 ⥤ ℬ) [G.Additive]
    [Limits.PreservesFiniteLimits G] (K : CochainComplex 𝒜 ℕ) (n : ℕ) :
    G.obj (K.cycles n) ≅ ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).cycles n :=
  Limits.IsLimit.conePointUniqueUpToIso
    (Limits.isLimitForkMapOfIsLimit' G (K.iCycles_d n (n + 1))
      (K.cyclesIsKernel n (n + 1) (by simp)))
    (((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).cyclesIsKernel n (n + 1) (by simp))

/-- The cycles iso `Functor.gCosyzygyIsoCocycles` is compatible with the cycles inclusions:
composing with the cycles inclusion of `G(K)` recovers `G` applied to the cycles inclusion of `K`.
This expresses that the iso identifies `G(Zⁿ)`, as a subobject of `G(Kⁿ)`, with the cocycle
object. -/
@[reassoc]
lemma Functor.gCosyzygyIsoCocycles_hom_iCycles (G : 𝒜 ⥤ ℬ) [G.Additive]
    [Limits.PreservesFiniteLimits G] (K : CochainComplex 𝒜 ℕ) (n : ℕ) :
    (G.gCosyzygyIsoCocycles K n).hom ≫
        ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).iCycles n =
      G.map (K.iCycles n) :=
  Limits.IsLimit.conePointUniqueUpToIso_hom_comp _ _ Limits.WalkingParallelPair.zero

/-- Compatibility of `Functor.gCosyzygyIsoCocycles` with the cosyzygy surjections `toCycles`:
`G` applied to the corestriction `Jᵐ ↠ Z^{m+1}` followed by the cycles iso is the corestriction of
the applied complex `G(K•)`. This is the naturality square that lets the cosyzygy iso transport the
cohomology cokernel in `Functor.cohomologyAppliedResolutionIso`. -/
lemma Functor.gCosyzygyIsoCocycles_toCycles (G : 𝒜 ⥤ ℬ) [G.Additive]
    [Limits.PreservesFiniteLimits G] (K : CochainComplex 𝒜 ℕ) (m : ℕ) :
    G.map (K.toCycles m (m + 1)) ≫ (G.gCosyzygyIsoCocycles K (m + 1)).hom =
      ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).toCycles m (m + 1) := by
  have hL : G.map (K.toCycles m (m + 1)) ≫ G.map (K.iCycles (m + 1)) = G.map (K.d m (m + 1)) := by
    rw [← G.map_comp, K.toCycles_i]
  have hR := ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).toCycles_i m (m + 1)
  erw [← cancel_mono (((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).iCycles (m + 1)),
    Category.assoc, G.gCosyzygyIsoCocycles_hom_iCycles]
  exact hL.trans hR.symm

/-- **Cohomology of the applied resolution, positive degrees** (positive-degree case of blueprint
`lem:cohomology_of_applied_resolution`). For a finite-limit-preserving `G` and `n = m+1 ≥ 1`, the
`n`-th cohomology of the applied complex `G(K•)` is the cokernel of `G` applied to the cosyzygy
surjection `J^{n-1} ↠ Zⁿ`:
`Hⁿ(G(K•)) ≅ coker(G(J^{n-1}) → G(Zⁿ))`.
The homology in degree `n` is the cokernel of the corestriction `(G(K•)).toCycles m (m+1)`
(`homologyIsCokernel`); the cosyzygy iso `gCosyzygyIsoCocycles` rewrites that corestriction as
`G(Jᵐ ↠ Z^{m+1})` post-composed with an isomorphism (`gCosyzygyIsoCocycles_toCycles`), and a
post-composed isomorphism does not change the cokernel (`cokernel.mapIso`). -/
noncomputable def Functor.cohomologyAppliedResolutionIso (G : 𝒜 ⥤ ℬ) [G.Additive]
    [Limits.PreservesFiniteLimits G] (K : CochainComplex 𝒜 ℕ) (m : ℕ) :
    ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology (m + 1) ≅
      cokernel (G.map (K.toCycles m (m + 1))) :=
  have iso2 : cokernel (((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).toCycles m (m + 1)) ≅
      cokernel (G.map (K.toCycles m (m + 1))) :=
    cokernel.mapIso _ (G.map (K.toCycles m (m + 1))) (Iso.refl _)
      (G.gCosyzygyIsoCocycles K (m + 1)).symm (by
        simp only [Iso.symm_hom, Iso.refl_hom, Iso.comp_inv_eq]
        erw [Category.id_comp]
        erw [G.gCosyzygyIsoCocycles_toCycles K m])
  Limits.IsColimit.coconePointUniqueUpToIso
      (((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homologyIsCokernel m (m + 1) (by simp))
      (cokernelIsCokernel _) ≪≫ iso2

/-- **Degree-zero cohomology of the applied resolution** (degree-`0` case of blueprint
`lem:cohomology_of_applied_resolution`). For a finite-limit-preserving `G`, the zeroth cohomology
of the applied complex `G(K•)` is `G` of the zeroth cosyzygy `Z⁰ = K.cycles 0`:
`H⁰(G(K•)) ≅ G(Z⁰)`. Since the complex starts in degree `0` there is no incoming differential, so
`H⁰` coincides with the cocycle object `ker(G(K⁰) → G(K¹))`, which `Functor.gCosyzygyIsoCocycles`
identifies with `G(Z⁰)`. Composed with an augmentation iso `A ≅ Z⁰` this gives the blueprint's
`H⁰(G(J•)) ≅ G(A)`. -/
noncomputable def Functor.gHomologyZeroIso (G : 𝒜 ⥤ ℬ) [G.Additive]
    [Limits.PreservesFiniteLimits G] (K : CochainComplex 𝒜 ℕ) :
    G.obj (K.cycles 0) ≅ ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology 0 :=
  G.gCosyzygyIsoCocycles K 0 ≪≫
    CochainComplex.isoHomologyπ₀ ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)

end Cosyzygy

/-! ## Project-local Mathlib supplement — the acyclic-resolution comparison theorem -/

/-- **An acyclic resolution computes the right-derived functor** (blueprint
`lem:acyclic_resolution_computes_derived`, TARGET 3; Stacks Tag 015E, Leray's acyclicity lemma).
Let `G` be an additive, finite-limit-preserving (hence left-exact) functor, and let `K` be a cochain
complex with every term `K.X n` right-`G`-acyclic, exact in every positive degree
(`hexact : ∀ n, K.ExactAt (n+1)`), and resolving `A` (presented as `e : A ≅ K.cycles 0`). Then for
every `n` the `n`-th right-derived functor of `G` at `A` is the `n`-th cohomology of the applied
complex `G(K•)`:
`(Rⁿ G)(A) ≅ Hⁿ(G(K•))`.

The proof is the classical dimension shift. *Degree 0:* `R⁰G ≅ G` (`rightDerivedZeroIsoSelf`) and
the left-exact identification `H⁰(G K) ≅ G(Z⁰)` (`gHomologyZeroIso`) together with `e`. *Positive
degrees `m+1`:* the staircase `stairGen` composes the dimension-shift isomorphisms
`rightDerivedShiftIsoOfAcyclic` across the cosyzygy short exact sequences down to
`(R¹ G)(Zᵐ)`, which the lowest-degree cokernel description `rightDerivedOneIsoCokerOfAcyclic`
identifies with `coker(G(Kᵐ) → G(Zᵐ⁺¹))`, finally matched to `Hᵐ⁺¹(G K)` by
`cohomologyAppliedResolutionIso`. -/
noncomputable def Functor.rightDerivedIsoOfAcyclicResolution
    (G : 𝒜 ⥤ ℬ) [G.Additive] [PreservesFiniteLimits G]
    (K : CochainComplex 𝒜 ℕ) (A : 𝒜) (e : A ≅ K.cycles 0)
    (hexact : ∀ n, K.ExactAt (n + 1)) [∀ n, G.IsRightAcyclic (K.X n)] (n : ℕ) :
    (G.rightDerived n).obj A ≅
      ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology n := by
  -- staircase: `(R^{m+1} G)(Zˢ) ≅ (R¹ G)(Z^{s+m})` by iterating the dimension shift `m` times
  have stairGen : ∀ (m s : ℕ), (G.rightDerived (m + 1)).obj (K.cycles s) ≅
      (G.rightDerived 1).obj (K.cycles (s + m)) := by
    intro m
    induction m with
    | zero => exact fun s => Iso.refl _
    | succ m ih =>
        intro s
        haveI : G.IsRightAcyclic (Functor.cosyzygyShortComplex K s).X₂ :=
          inferInstanceAs (G.IsRightAcyclic (K.X s))
        exact (G.rightDerivedShiftIsoOfAcyclic (Functor.cosyzygyShortExact K s (hexact s)) m).symm
          ≪≫ ih (s + 1) ≪≫
          eqToIso (congrArg (fun i => (G.rightDerived 1).obj (K.cycles i))
            (by omega : s + 1 + m = s + (m + 1)))
  cases n with
  | zero =>
      exact (G.rightDerivedZeroIsoSelf.app A) ≪≫ G.mapIso e ≪≫ G.gHomologyZeroIso K
  | succ m =>
      haveI : G.IsRightAcyclic (Functor.cosyzygyShortComplex K m).X₂ :=
        inferInstanceAs (G.IsRightAcyclic (K.X m))
      exact (G.rightDerived (m + 1)).mapIso e ≪≫ stairGen m 0 ≪≫
        eqToIso (congrArg (fun i => (G.rightDerived 1).obj (K.cycles i)) (by omega : 0 + m = m)) ≪≫
        G.rightDerivedOneIsoCokerOfAcyclic (Functor.cosyzygyShortExact K m (hexact m)) ≪≫
        (G.cohomologyAppliedResolutionIso K m).symm

/-! ### P4 complete — `rightDerivedIsoOfAcyclicResolution` is proved axiom-clean above. -/

end CategoryTheory

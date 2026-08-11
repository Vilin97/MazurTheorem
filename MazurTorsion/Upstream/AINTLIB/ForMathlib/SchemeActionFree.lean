/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.InvariantTorsor
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import MazurTorsion.Upstream.AINTLIB.ForMathlib.EtaleCancellation
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeQuotient
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import MazurTorsion.Upstream.AINTLIB.ForMathlib.BaseChangeAlongCompat

/-!
# Geometric freeness ⟹ algebraic freeness (the T-Q2 bridge)

`ForMathlib/InvariantTorsor.lean` proves the Katz–Mazur A7.1.1 package (finite, unramified,
étale, torsor, base change) from `IsFreeAlgebraAction G R A` — KM's *"for any non-zero
`R`-algebra `R'`, and any `g ≠ 1`, `g` operates without fixed points on
`Hom_{R-alg}(A, R')`"*.

`ForMathlib/SchemeQuotient.lean` proves the quotient `X/G` from a *geometric* freeness
statement: no `γ ≠ 1` fixes a `T`-point of `X` over a nonempty `T`.

This file is the bridge: on a `G`-stable **affine** open, geometric freeness gives
`IsFreeAlgebraAction` on the section ring. It is the input that turns the local quotient
`V ⟶ Spec Γ(X,V)ᴳ` into a finite étale `G`-torsor.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/-- The chart ring map of a finite morphism over an affine open is module-finite
(`Scheme.Hom.finite_appTop` of the restriction, transported through
`morphismRestrict_app'`). -/
theorem Scheme.Hom.finite_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    {U : Y.Opens} (hU : IsAffineOpen U) :
    (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom.Finite := by
  haveI : IsAffine (U : Scheme.{u}) := hU
  haveI : IsFinite (f ∣_ U) := IsZariskiLocalAtTarget.restrict (P := @IsFinite) inferInstance U
  have h : ((f ∣_ U).app ⊤).hom.Finite := Scheme.Hom.finite_appTop (f ∣_ U)
  rw [morphismRestrict_app'] at h
  exact (f.appLE_congr _ (by simp) (by simp) (fun φ => φ.hom.Finite)).mp h

namespace SchemeAction

variable {G : Type*} [Group G] {X : Scheme.{u}} (σ : SchemeAction G X)

/-- **(T-Q2 bridge)** If no `γ ≠ 1` fixes a `T`-point of `X` over a nonempty `T`, then on every
`G`-stable affine open `U` the induced action on the section ring `Γ(X, U)` is free in the sense
of Katz–Mazur A7.1.1 (`IsFreeAlgebraAction`).

Given a ring point `φ : Γ(X, U) →ₐ[ℤ] R'` with `R'` nontrivial and
`φ ∘ (γ • ·) = φ`, the morphism `t : Spec R' ⟶ Spec Γ(X, U) ≅ U ↪ X` is `γ`-fixed
(`specSMul_isoSpec_inv` is exactly the statement that `Spec` of the ring action *is* the
restricted geometric action), so `Spec R'` is empty — impossible, since a nontrivial ring
has a prime ideal. -/
theorem isFreeAlgebraAction_of_free {U : X.Opens} (hU : σ.IsStableOpen U)
    (hUa : IsAffineOpen U)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X),
      t ≫ σ.hom γ = t → IsEmpty T) :
    letI := σ.gammaMulSemiringAction hU
    IsFreeAlgebraAction G ℤ ↑Γ(X, U) := by
  letI := σ.gammaMulSemiringAction hU
  intro γ hγ R' _ _ _ φ
  by_contra hcon
  push Not at hcon
  -- `φ` is `γ`-invariant, hence `Spec φ` equalises the action
  have hring : (CommRingCat.ofHom (MulSemiringAction.toRingHom G (↑Γ(X, U)) γ)) ≫
      CommRingCat.ofHom φ.toRingHom = CommRingCat.ofHom φ.toRingHom := by
    ext a
    exact hcon a
  have hspec : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ specSMul γ =
      Spec.map (CommRingCat.ofHom φ.toRingHom) := by
    change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G (↑Γ(X, U)) γ)) = _
    rw [← Spec.map_comp, hring]
  -- the resulting point of `X` is `γ`-fixed
  set t : Spec (CommRingCat.of R') ⟶ X :=
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ hUa.isoSpec.inv ≫ U.ι with ht
  have h1 : U.ι ≫ σ.hom γ = (σ.hom γ).resLE U U (hU.le_preimage γ) ≫ U.ι :=
    (Scheme.Hom.resLE_comp_ι _ _).symm
  have h2 : hUa.isoSpec.inv ≫ (σ.hom γ).resLE U U (hU.le_preimage γ) =
      specSMul γ ≫ hUa.isoSpec.inv := (specSMul_isoSpec_inv σ hU hUa γ).symm
  have hfix : t ≫ σ.hom γ = t := by
    rw [ht]
    simp only [Category.assoc]
    rw [h1, ← Category.assoc hUa.isoSpec.inv, h2, Category.assoc,
      ← Category.assoc (Spec.map (CommRingCat.ofHom φ.toRingHom)) (specSMul γ), hspec]
  -- but `Spec R'` is nonempty
  haveI hE : IsEmpty (Spec (CommRingCat.of R')) := hfree γ hγ _ t hfix
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum R') := inferInstance
  exact hE.false p

/-- **(T-Q2 on a chart)** On a `G`-stable affine open of a scheme with a free `G`-action, the
section ring is a finite module over its invariants (KM A7.1.1, finiteness part). -/
theorem finite_gamma_of_free [Finite G] {U : X.Opens} (hU : σ.IsStableOpen U)
    (hUa : IsAffineOpen U)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X),
      t ≫ σ.hom γ = t → IsEmpty T) :
    letI := σ.gammaMulSemiringAction hU
    Module.Finite (FixedPoints.subalgebra ℤ (↑Γ(X, U)) G) ↑Γ(X, U) := by
  letI := σ.gammaMulSemiringAction hU
  exact Module.Finite.of_isFreeAlgebraAction G ℤ _ (σ.isFreeAlgebraAction_of_free hU hUa hfree)

/-- **(T-Q2 on a chart)** The torsor identity `Γ(X,U) ⊗_{Γ(X,U)ᴳ} Γ(X,U) ≅ ∏_G Γ(X,U)`
(KM A7.1.1, torsor part; SGA III Exp. V 4.1 (iv)) holds on every `G`-stable affine open of a
scheme with a free `G`-action. Geometrically: `U ⟶ U/G` is a `G`-torsor. -/
theorem torsorMul_bijective_of_free [Finite G] {U : X.Opens} (hU : σ.IsStableOpen U)
    (hUa : IsAffineOpen U)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X),
      t ≫ σ.hom γ = t → IsEmpty T) :
    letI := σ.gammaMulSemiringAction hU
    Function.Bijective (MulSemiringAction.torsorMul G ℤ (↑Γ(X, U))) := by
  letI := σ.gammaMulSemiringAction hU
  exact torsorMul_bijective_of_isFreeAlgebraAction G ℤ _
    (σ.isFreeAlgebraAction_of_free hU hUa hfree)

section Quotient

variable [Finite G] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
  (V : X → X.Opens) (hVs : ∀ x, σ.IsStableOpen (V x)) (hVa : ∀ x, IsAffineOpen (V x))
  (hVmem : ∀ x, x ∈ V x)
  (hfree : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X),
    t ≫ σ.hom γ = t → IsEmpty T)

include hfree in
/-- **(T-Q2, geometric)** For a **free** action, the quotient projection `X ⟶ X/G` is a **finite**
morphism.

`IsFinite` is Zariski-local at the target, the quotient charts cover `X/G`, and over the `x`-th
chart the projection *is* `V x ⟶ Spec Γ(X, V x)ᴳ` (`morphismRestrict_quotientπ`), i.e. `Spec`
of `Γ(X,V x)ᴳ ↪ Γ(X,V x)`, which is module-finite by `finite_gamma_of_free` (KM A7.1.1). -/
theorem isFinite_quotientπ : IsFinite (σ.quotientπ V hVs hVa hVmem) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsFinite) (σ.quotientChart V hVs hVa)
    (σ.iSup_quotientChart_eq_top V hVs hVa) fun x => ?_
  rw [morphismRestrict_quotientπ σ V hVs hVa hVmem x,
    MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite),
    MorphismProperty.cancel_right_of_respectsIso (P := @IsFinite),
    localQuotientπ_eq σ (hVs x) (hVa x),
    MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite)]
  letI := σ.gammaMulSemiringAction (hVs x)
  haveI := σ.finite_gamma_of_free (hVs x) (hVa x) hfree
  rw [invariantsπ, IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr inferInstance

include hfree in
/-- **(T-Q2, geometric)** For a **free** action, the quotient projection `X ⟶ X/G` is **étale**.

Same local-to-global argument, with `Algebra.Etale.of_isFreeAlgebraAction` (KM A7.1.1, general
base — the [A711-FP] gap having been closed) at the chart level. -/
theorem etale_quotientπ : Etale (σ.quotientπ V hVs hVa hVmem) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @Etale) (σ.quotientChart V hVs hVa)
    (σ.iSup_quotientChart_eq_top V hVs hVa) fun x => ?_
  rw [morphismRestrict_quotientπ σ V hVs hVa hVmem x,
    MorphismProperty.cancel_left_of_respectsIso (P := @Etale),
    MorphismProperty.cancel_right_of_respectsIso (P := @Etale),
    localQuotientπ_eq σ (hVs x) (hVa x),
    MorphismProperty.cancel_left_of_respectsIso (P := @Etale)]
  letI := σ.gammaMulSemiringAction (hVs x)
  haveI : Algebra.Etale (FixedPoints.subalgebra ℤ (↑Γ(X, V x)) G) ↑Γ(X, V x) :=
    Algebra.Etale.of_isFreeAlgebraAction G ℤ _
      (σ.isFreeAlgebraAction_of_free (hVs x) (hVa x) hfree)
  rw [invariantsπ, HasRingHomProperty.Spec_iff (P := @Etale)]
  exact RingHom.etale_algebraMap.mpr inferInstance

omit [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))] in
/-- **(T-Q2, geometric)** For a **free** action, `localQuotientπ : ↥U ⟶ Spec Γ(X,U)ᴳ` is an
**epimorphism** — it is an fppf cover (finite étale surjection = flat + surjective). Used to
cancel `localQuotientπ` when identifying the descended structure map with the invariant quotient
map on a chart (`[a3-ii]`). -/
theorem epi_localQuotientπ {U : X.Opens} (hU : σ.IsStableOpen U) (hUa : IsAffineOpen U)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X),
      t ≫ σ.hom γ = t → IsEmpty T) :
    Epi (σ.localQuotientπ hU hUa) := by
  letI := σ.gammaMulSemiringAction hU
  haveI : Module.Finite (FixedPoints.subalgebra ℤ (↑Γ(X, U)) G) ↑Γ(X, U) :=
    Module.Finite.of_isFreeAlgebraAction G ℤ _ (σ.isFreeAlgebraAction_of_free hU hUa hfree)
  haveI : Module.Projective (FixedPoints.subalgebra ℤ (↑Γ(X, U)) G) ↑Γ(X, U) :=
    Module.Projective.of_isFreeAlgebraAction G ℤ _ (σ.isFreeAlgebraAction_of_free hU hUa hfree)
  haveI : Module.Flat (FixedPoints.subalgebra ℤ (↑Γ(X, U)) G) ↑Γ(X, U) :=
    Module.Flat.of_projective
  haveI : Flat (invariantsπ G (↑Γ(X, U)) ℤ) := by
    rw [invariantsπ, AlgebraicGeometry.Flat.SpecMap_iff, CommRingCat.hom_ofHom,
      RingHom.flat_algebraMap_iff]
    infer_instance
  haveI : Surjective (invariantsπ G (↑Γ(X, U)) ℤ) := ⟨invariantsπ_surjective G _ ℤ⟩
  haveI : Epi (invariantsπ G (↑Γ(X, U)) ℤ) :=
    AlgebraicGeometry.Flat.epi_of_flat_of_surjective _
  rw [SchemeAction.localQuotientπ_eq]
  infer_instance

end Quotient

section QuotientDesc

/-! ### [GHB6] The descended structure map of a free quotient is finite étale

`X ⟶ X/G ⟶ S` with `X ⟶ S` finite étale invariant and the action free: over each affine
chart `US x ⊆ S` the descended map *is* `Spec` of the corestricted chart map
`Γ(S, US x) ⟶ Γ(X, f⁻¹US x)ᴳ`, which is finite étale by the split-cover cancellation
(`ForMathlib/EtaleCancellation.lean`); over the (open) complement of the closed image of
`f` the descended map has empty source. -/

variable [Finite G] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
  {S : Scheme.{u}} (f : X ⟶ S)

omit [Finite G] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))] in
/-- The chart ring map of an invariant morphism is `G`-invariant: `appLE`-functoriality
applied to `σ.hom g ≫ f = f`. -/
theorem gamma_appLE_invariant (hover : ∀ γ : G, σ.hom γ ≫ f = f)
    {U : S.Opens} {V : X.Opens} (hVst : σ.IsStableOpen V) (hle : V ≤ f ⁻¹ᵁ U) (g : G)
    (r : Γ(S, U)) :
    letI := σ.gammaMulSemiringAction hVst
    g • ((f.appLE U V hle).hom r) = (f.appLE U V hle).hom r := by
  letI := σ.gammaMulSemiringAction hVst
  have key : ∀ {m m' : X ⟶ S} (_ : m = m') (e : V ≤ m ⁻¹ᵁ U) (e' : V ≤ m' ⁻¹ᵁ U),
      m.appLE U V e = m'.appLE U V e' := by
    rintro m m' rfl e e'; rfl
  have hcomp : f.appLE U V hle ≫ (σ.hom g).appLE V V (hVst.le_preimage g) =
      f.appLE U V hle := by
    rw [Scheme.Hom.appLE_comp_appLE]
    exact key (hover g) _ _
  change ((σ.hom g).appLE V V (hVst.le_preimage g)).hom ((f.appLE U V hle).hom r) = _
  rw [← CommRingCat.comp_apply, hcomp]

omit [Finite G] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))] in
/-- The descended chart ring map `Γ(S, W) ⟶ Γ(X, f⁻¹W)ᴳ` of an invariant morphism: the
corestriction of `f.appLE` to the invariants of the section-ring action. -/
noncomputable def quotientDescRing (hover : ∀ γ : G, σ.hom γ ≫ f = f) (W : S.Opens)
    (hVst : σ.IsStableOpen (f ⁻¹ᵁ W)) :
    letI := σ.gammaMulSemiringAction hVst
    Γ(S, W) →+* FixedPoints.subalgebra ℤ ↑Γ(X, f ⁻¹ᵁ W) G :=
  letI := σ.gammaMulSemiringAction hVst
  (f.appLE W (f ⁻¹ᵁ W) le_rfl).hom.invariantsCorestrict (R₀ := ℤ)
    (fun g r => σ.gamma_appLE_invariant f hover hVst le_rfl g r)

omit [Finite G] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))] in
/-- The composition of the descended chart ring map with the invariants inclusion is the
chart ring map itself. -/
theorem ofHom_quotientDescRing_algebraMap (hover : ∀ γ : G, σ.hom γ ≫ f = f) (W : S.Opens)
    (hVst : σ.IsStableOpen (f ⁻¹ᵁ W)) :
    letI := σ.gammaMulSemiringAction hVst
    CommRingCat.ofHom (σ.quotientDescRing f hover W hVst) ≫
      CommRingCat.ofHom (algebraMap (FixedPoints.subalgebra ℤ ↑Γ(X, f ⁻¹ᵁ W) G)
        ↑Γ(X, f ⁻¹ᵁ W)) = f.appLE W (f ⁻¹ᵁ W) le_rfl := by
  ext r
  rw [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom]
  rfl

/-- **The quotient charts are the `f₀`-preimages of the atlas charts**: for the preimage
atlas `V x = f⁻¹(US x)` and any descent `f₀` of `f`, the `f₀`-preimage of `US x` is
exactly the `x`-th quotient chart (both are the `π₀`-image of `V x`; uses surjectivity of
`π₀` and `quotientπ_preimage_quotientChart`). -/
theorem quotient_desc_preimage_eq_chart (US : X → S.Opens)
    (hVs : ∀ x, σ.IsStableOpen (f ⁻¹ᵁ US x)) (hVa : ∀ x, IsAffineOpen (f ⁻¹ᵁ US x))
    (hVmem : ∀ x, x ∈ f ⁻¹ᵁ US x)
    (f₀ : σ.quotient (fun x => f ⁻¹ᵁ US x) hVs hVa ⟶ S)
    (hf₀ : σ.quotientπ (fun x => f ⁻¹ᵁ US x) hVs hVa hVmem ≫ f₀ = f) (x : X) :
    f₀ ⁻¹ᵁ US x = σ.quotientChart (fun x => f ⁻¹ᵁ US x) hVs hVa x := by
  have hπf₀ : ∀ z : X, f₀ (σ.quotientπ (fun x => f ⁻¹ᵁ US x) hVs hVa hVmem z) = f z :=
    fun z => by rw [← Scheme.Hom.comp_apply, hf₀]
  refine TopologicalSpace.Opens.ext (Set.ext fun q => ?_)
  obtain ⟨z, rfl⟩ := σ.quotientπ_surjective (fun x => f ⁻¹ᵁ US x) hVs hVa hVmem q
  constructor
  · intro hq
    have hz : z ∈ f ⁻¹ᵁ US x := show f z ∈ US x by
      rw [← hπf₀ z]; exact hq
    have hmem : z ∈ σ.quotientπ (fun x => f ⁻¹ᵁ US x) hVs hVa hVmem ⁻¹ᵁ
        σ.quotientChart (fun x => f ⁻¹ᵁ US x) hVs hVa x := by
      rw [quotientπ_preimage_quotientChart]
      exact hz
    exact hmem
  · intro hq
    have hz : z ∈ f ⁻¹ᵁ US x := by
      rw [← quotientπ_preimage_quotientChart σ (fun x => f ⁻¹ᵁ US x) hVs hVa hVmem x]
      exact hq
    change f₀ (σ.quotientπ (fun x => f ⁻¹ᵁ US x) hVs hVa hVmem z) ∈ US x
    rw [hπf₀ z]
    exact hz

/-- **The descended map over a chart is `Spec` of the descended chart ring map**: over the
affine chart `US x ⊆ S`, the descent `f₀` restricts to
`Spec (Γ(S, US x) ⟶ Γ(X, f⁻¹US x)ᴳ)`, conjugated by the chart identifications. Proven by
cancelling the epi `localQuotientπ` (free actions) against the mono `(US x).ι`. -/
theorem morphismRestrict_quotient_desc (hover : ∀ γ : G, σ.hom γ ≫ f = f)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X), t ≫ σ.hom γ = t → IsEmpty T)
    (US : X → S.Opens) (hUSa : ∀ x, IsAffineOpen (US x))
    (hVs : ∀ x, σ.IsStableOpen (f ⁻¹ᵁ US x)) (hVa : ∀ x, IsAffineOpen (f ⁻¹ᵁ US x))
    (hVmem : ∀ x, x ∈ f ⁻¹ᵁ US x)
    (f₀ : σ.quotient (fun x => f ⁻¹ᵁ US x) hVs hVa ⟶ S)
    (hf₀ : σ.quotientπ (fun x => f ⁻¹ᵁ US x) hVs hVa hVmem ≫ f₀ = f) (x : X) :
    f₀ ∣_ US x =
      ((σ.quotient (fun x => f ⁻¹ᵁ US x) hVs hVa).isoOfEq
          (σ.quotient_desc_preimage_eq_chart f US hVs hVa hVmem f₀ hf₀ x)).hom ≫
        (σ.quotientChartIso (fun x => f ⁻¹ᵁ US x) hVs hVa x).inv ≫
        Spec.map (CommRingCat.ofHom (σ.quotientDescRing f hover (US x) (hVs x))) ≫
        (hUSa x).isoSpec.inv := by
  letI := σ.gammaMulSemiringAction (hVs x)
  haveI : Epi (σ.localQuotientπ (hVs x) (hVa x)) :=
    σ.epi_localQuotientπ (hVs x) (hVa x) hfree
  set e₁ := (σ.quotient (fun x => f ⁻¹ᵁ US x) hVs hVa).isoOfEq
    (σ.quotient_desc_preimage_eq_chart f US hVs hVa hVmem f₀ hf₀ x) with he₁
  rw [← cancel_mono (US x).ι, morphismRestrict_ι,
    ← cancel_epi (σ.localQuotientπ (hVs x) (hVa x) ≫
      (σ.quotientChartIso (fun x => f ⁻¹ᵁ US x) hVs hVa x).hom ≫ e₁.inv)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
  -- left side: collapse to `(V x).ι ≫ f` through the chart square and `hf₀`
  rw [show e₁.inv ≫ (f₀ ⁻¹ᵁ US x).ι ≫ f₀ = (e₁.inv ≫ (f₀ ⁻¹ᵁ US x).ι) ≫ f₀ from
      (Category.assoc _ _ _).symm,
    Scheme.isoOfEq_inv_ι,
    show σ.localQuotientπ (hVs x) (hVa x) ≫
        (σ.quotientChartIso (fun x => f ⁻¹ᵁ US x) hVs hVa x).hom ≫
        (σ.quotientChart (fun x => f ⁻¹ᵁ US x) hVs hVa x).ι ≫ f₀ =
        (σ.localQuotientπ (hVs x) (hVa x) ≫
          (σ.quotientChartIso (fun x => f ⁻¹ᵁ US x) hVs hVa x).hom ≫
          (σ.quotientChart (fun x => f ⁻¹ᵁ US x) hVs hVa x).ι) ≫ f₀ by
      simp only [Category.assoc],
    localQuotientπ_quotientChartIso σ (fun x => f ⁻¹ᵁ US x) hVs hVa hVmem x,
    Category.assoc, hf₀]
  -- right side: fuse the `Spec.map`s and apply `isoSpec`/`appLE` naturality
  rw [localQuotientπ_eq σ (hVs x) (hVa x), invariantsπ, Category.assoc,
    ← Spec.map_comp_assoc, ofHom_quotientDescRing_algebraMap σ f hover (US x) (hVs x),
    IsAffineOpen.isoSpec_hom, Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc,
    IsAffineOpen.toSpecΓ_isoSpec_inv_assoc, Scheme.Hom.resLE_comp_ι]

/-- **[GHB6, concrete] The descended structure map of a free quotient is finite étale**:
for `f : X ⟶ S` finite étale invariant under a free action, any descent `f₀` of `f` along
the concrete quotient (over the preimage atlas of affine opens `US`) is finite étale. Over
each `US x` this is the split-cover étale cancellation (`EtaleCancellation.lean`) applied
to `Γ(S, US x) → Γ(X, f⁻¹US x)ᴳ → Γ(X, f⁻¹US x)`; over the open complement of the closed
image of `f` the descent has empty source. -/
theorem isFinite_etale_quotient_desc (hover : ∀ γ : G, σ.hom γ ≫ f = f)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X), t ≫ σ.hom γ = t → IsEmpty T)
    (hfin : IsFinite f) (het : Etale f)
    (US : X → S.Opens) (hUSa : ∀ x, IsAffineOpen (US x))
    (hVs : ∀ x, σ.IsStableOpen (f ⁻¹ᵁ US x)) (hVa : ∀ x, IsAffineOpen (f ⁻¹ᵁ US x))
    (hVmem : ∀ x, x ∈ f ⁻¹ᵁ US x)
    (f₀ : σ.quotient (fun x => f ⁻¹ᵁ US x) hVs hVa ⟶ S)
    (hf₀ : σ.quotientπ (fun x => f ⁻¹ᵁ US x) hVs hVa hVmem ≫ f₀ = f) :
    IsFinite f₀ ∧ Etale f₀ := by
  classical
  haveI := hfin
  haveI := het
  -- `S` is covered by the atlas charts and affine pieces of the complement of the
  -- (closed) image of `f`
  have hclosed : IsClosed (Set.range ⇑f) := (Scheme.Hom.isClosedMap f).isClosed_range
  have hcov : ∀ s : S, ∃ Wo : S.Opens, (IsAffineOpen Wo ∧ s ∈ Wo) ∧
      ((∃ x : X, Wo = US x) ∨ ∀ z : X, f z ∉ Wo) := by
    intro s
    by_cases hs : s ∈ Set.range ⇑f
    · obtain ⟨x, hx⟩ := hs
      exact ⟨US x, ⟨hUSa x, hx ▸ hVmem x⟩, Or.inl ⟨x, rfl⟩⟩
    · obtain ⟨Wo, hWa, hsW, hWsub⟩ := exists_isAffineOpen_mem_and_subset
        (U := ⟨(Set.range ⇑f)ᶜ, hclosed.isOpen_compl⟩) hs
      exact ⟨Wo, ⟨hWa, hsW⟩, Or.inr fun z hz => (hWsub hz) (Set.mem_range_self z)⟩
  choose W hW hWor using hcov
  have htop : ⨆ s : S, W s = ⊤ :=
    top_le_iff.mp fun s _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨s, (hW s).2⟩
  have hkey : ∀ (P : MorphismProperty Scheme.{u}) (_ : IsZariskiLocalAtTarget P)
      (_ : ∀ x : X, P (f₀ ∣_ US x))
      (_ : ∀ s : S, IsEmpty (f₀ ⁻¹ᵁ W s) → P (f₀ ∣_ W s)), P f₀ := by
    intro P hP hchart hempty
    refine IsZariskiLocalAtTarget.of_iSup_eq_top W htop fun s => ?_
    rcases hWor s with ⟨x, hWx⟩ | hmiss
    · rw [hWx]; exact hchart x
    · refine hempty s ⟨fun q => ?_⟩
      obtain ⟨z, hz⟩ := σ.quotientπ_surjective (fun x => f ⁻¹ᵁ US x) hVs hVa hVmem q.1
      have hq : f₀ q.1 ∈ W s := q.2
      rw [← hz, ← Scheme.Hom.comp_apply, hf₀] at hq
      exact hmiss z hq
  constructor
  · refine hkey @IsFinite inferInstance (fun x => ?_) (fun s hs => ?_)
    · letI := σ.gammaMulSemiringAction (hVs x)
      rw [σ.morphismRestrict_quotient_desc f hover hfree US hUSa hVs hVa hVmem f₀ hf₀ x,
        MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite),
        MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite),
        MorphismProperty.cancel_right_of_respectsIso (P := @IsFinite),
        IsFinite.SpecMap_iff]
      exact RingHom.invariantsCorestrict_finite (f.appLE (US x) (f ⁻¹ᵁ US x) le_rfl).hom
        (fun g r => σ.gamma_appLE_invariant f hover (hVs x) le_rfl g r)
        (σ.isFreeAlgebraAction_of_free (hVs x) (hVa x) hfree) (f.finite_appLE (hUSa x))
    · haveI := hs
      infer_instance
  · refine hkey @Etale inferInstance (fun x => ?_) (fun s hs => ?_)
    · letI := σ.gammaMulSemiringAction (hVs x)
      have hetR : RingHom.Etale (f.appLE (US x) (f ⁻¹ᵁ US x) le_rfl).hom :=
        HasRingHomProperty.appLE (P := @Etale) (f := f) het ⟨US x, hUSa x⟩
          ⟨f ⁻¹ᵁ US x, hVa x⟩ le_rfl
      rw [σ.morphismRestrict_quotient_desc f hover hfree US hUSa hVs hVa hVmem f₀ hf₀ x,
        MorphismProperty.cancel_left_of_respectsIso (P := @Etale),
        MorphismProperty.cancel_left_of_respectsIso (P := @Etale),
        MorphismProperty.cancel_right_of_respectsIso (P := @Etale),
        HasRingHomProperty.Spec_iff (P := @Etale)]
      exact RingHom.invariantsCorestrict_etale (f.appLE (US x) (f ⁻¹ᵁ US x) le_rfl).hom
        (fun g r => σ.gamma_appLE_invariant f hover (hVs x) le_rfl g r)
        (σ.isFreeAlgebraAction_of_free (hVs x) (hVa x) hfree) (f.finite_appLE (hUSa x)) hetR
    · haveI := hs
      infer_instance

/-- **[GHB6] (KM 7.1.3(6), freeness-sharpened)** — the descended structure map of ANY
quotient datum of a free action is finite étale, given the total map finite étale. Stated
against any `(Z₀, π, f₀, hdesc)` satisfying the quotient universal property (all such are
canonically isomorphic to the constructed quotient, as in
`quotientπ_finite_etale_surjective`). -/
theorem quotient_desc_finite_etale {Z₀ : Scheme.{u}}
    (hover : ∀ γ : G, σ.hom γ ≫ f = f)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ (T : Scheme.{u}) (t : T ⟶ X), t ≫ σ.hom γ = t → IsEmpty T)
    (hfin : IsFinite f) (het : Etale f)
    (π : X ⟶ Z₀) (f₀ : Z₀ ⟶ S) (hπf : π ≫ f₀ = f)
    (hπinv : ∀ γ : G, σ.hom γ ≫ π = π)
    (hdesc : ∀ {Y : Scheme.{u}} (F : X ⟶ Y), (∀ γ : G, σ.hom γ ≫ F = F) →
      ∃! q : Z₀ ⟶ Y, π ≫ q = F) :
    IsFinite f₀ ∧ Etale f₀ := by
  classical
  -- the concrete quotient over the preimage atlas (as in [GHB3]/[GHB4])
  have hcov : ∀ x : X, ∃ Wo : S.Opens, IsAffineOpen Wo ∧ f.base x ∈ Wo := fun x => by
    obtain ⟨Wo, hWo, hmem, -⟩ := exists_isAffineOpen_mem_and_subset (X := S)
      (TopologicalSpace.Opens.mem_top (f.base x))
    exact ⟨Wo, hWo, hmem⟩
  choose US hUSa hUSmem using hcov
  have hVs : ∀ x, σ.IsStableOpen (f ⁻¹ᵁ US x) := fun x g => by
    change (σ.hom g ≫ f) ⁻¹ᵁ US x = f ⁻¹ᵁ US x
    rw [hover g]
  have hVa : ∀ x, IsAffineOpen (f ⁻¹ᵁ US x) := fun x => (hUSa x).preimage f
  have hVmem : ∀ x, x ∈ f ⁻¹ᵁ US x := fun x => hUSmem x
  obtain ⟨f₀c, hf₀c, -⟩ :=
    σ.existsUnique_quotientπ_lift (fun x => f ⁻¹ᵁ US x) hVs hVa hVmem f hover
  obtain ⟨hfinc, hetc⟩ := σ.isFinite_etale_quotient_desc f hover hfree hfin het US hUSa
    hVs hVa hVmem f₀c hf₀c
  -- the unique iso between the abstract and the concrete quotient
  obtain ⟨q, hq, -⟩ := hdesc (σ.quotientπ (fun x => f ⁻¹ᵁ US x) hVs hVa hVmem)
    (σ.hom_quotientπ (fun x => f ⁻¹ᵁ US x) hVs hVa hVmem)
  obtain ⟨q', hq', -⟩ :=
    σ.existsUnique_quotientπ_lift (fun x => f ⁻¹ᵁ US x) hVs hVa hVmem π hπinv
  have hqq' : q ≫ q' = 𝟙 Z₀ := by
    obtain ⟨_, -, huniq⟩ := hdesc π hπinv
    rw [huniq (q ≫ q') (show π ≫ (q ≫ q') = π by rw [← Category.assoc, hq, hq']),
      huniq (𝟙 Z₀) (show π ≫ 𝟙 Z₀ = π by rw [Category.comp_id])]
  have hq'q : q' ≫ q = 𝟙 _ := by
    obtain ⟨_, -, huniq⟩ := σ.existsUnique_quotientπ_lift (fun x => f ⁻¹ᵁ US x) hVs hVa
      hVmem (σ.quotientπ (fun x => f ⁻¹ᵁ US x) hVs hVa hVmem)
      (σ.hom_quotientπ (fun x => f ⁻¹ᵁ US x) hVs hVa hVmem)
    rw [huniq (q' ≫ q) (show σ.quotientπ (fun x => f ⁻¹ᵁ US x) hVs hVa hVmem ≫ (q' ≫ q) =
          σ.quotientπ (fun x => f ⁻¹ᵁ US x) hVs hVa hVmem by
        rw [← Category.assoc, hq', hq]),
      huniq (𝟙 _) (show σ.quotientπ (fun x => f ⁻¹ᵁ US x) hVs hVa hVmem ≫ 𝟙 _ =
          σ.quotientπ (fun x => f ⁻¹ᵁ US x) hVs hVa hVmem by rw [Category.comp_id])]
  haveI : IsIso q := ⟨q', hqq', hq'q⟩
  -- `f₀` is the transport of the concrete descent along the iso
  have hf₀q : f₀ = q ≫ f₀c := by
    obtain ⟨_, -, huniq⟩ := hdesc f hover
    rw [huniq f₀ hπf, huniq (q ≫ f₀c)
      (show π ≫ (q ≫ f₀c) = f by rw [← Category.assoc, hq, hf₀c])]
  rw [hf₀q]
  exact ⟨(MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite) q f₀c).mpr hfinc,
    (MorphismProperty.cancel_left_of_respectsIso (P := @Etale) q f₀c).mpr hetc⟩

end QuotientDesc

end SchemeAction

variable {G : Type u} [Group G] {B : Type u} [CommRing B] [MulSemiringAction G B]

/-- **The invariants morphism of a free action is an fppf cover**: `Spec B ⟶ Spec Bᴳ` is
surjective, flat and quasi-compact (indeed finite locally free). Abstracts the body of
`epi_localQuotientπ` for reuse in the `[a5-P-fppf]` comparison
(`isIso_of_isPullback_of_fppf`). -/
theorem fppf_invariantsπ [Finite G] (hfree : IsFreeAlgebraAction G ℤ B) :
    Surjective (invariantsπ G B ℤ) ∧ Flat (invariantsπ G B ℤ)
      ∧ QuasiCompact (invariantsπ G B ℤ) := by
  haveI : Module.Finite (FixedPoints.subalgebra ℤ B G) B :=
    Module.Finite.of_isFreeAlgebraAction G ℤ _ hfree
  haveI : Module.Projective (FixedPoints.subalgebra ℤ B G) B :=
    Module.Projective.of_isFreeAlgebraAction G ℤ _ hfree
  haveI : Module.Flat (FixedPoints.subalgebra ℤ B G) B := Module.Flat.of_projective
  refine ⟨⟨invariantsπ_surjective G B ℤ⟩, ?_, ?_⟩
  · rw [invariantsπ, AlgebraicGeometry.Flat.SpecMap_iff, CommRingCat.hom_ofHom,
      RingHom.flat_algebraMap_iff]
    infer_instance
  · rw [invariantsπ]
    infer_instance

end AlgebraicGeometry

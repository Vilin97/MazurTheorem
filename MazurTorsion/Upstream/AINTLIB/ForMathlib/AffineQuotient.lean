/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Ticket T-Q3.
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SpecGroupAction
import MazurTorsion.Upstream.AINTLIB.ForMathlib.InvariantLocalization
import MazurTorsion.Upstream.AINTLIB.ForMathlib.InvariantTorsor
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.PullbackCarrier
import MazurTorsion.Upstream.AINTLIB.ForMathlib.BaseChangeAlongCompat

/-!
# The affine quotient by a finite group action: universal property

For a finite group `G` acting on a commutative ring `B` (over a base `R`), the
invariants morphism `invariantsπ : Spec B ⟶ Spec Bᴳ` is the **categorical quotient**
of `Spec B` by `G` in the category of schemes:

* `existsUnique_factor_fixedPoints_away` — the algebra engine: a ring hom into `B_a`
  (`a` an invariant) with `G`-fixed image factors uniquely through `(Bᴳ)_a`.
* `invariantsπ_hom_ext_of_isOpenImmersion` — uniqueness of descent, in a form stable
  under restriction: two morphisms out of an open `W ⊆ Spec Bᴳ` agreeing after
  precomposition with (the pullback of) `invariantsπ` are equal. `W = Spec Bᴳ`
  (`j = 𝟙`) is `invariantsπ_hom_ext`.
* `exists_invariantsπ_lift` — existence of descent: every `G`-invariant morphism
  `Spec B ⟶ Y` factors through `invariantsπ`.
* `existsUnique_invariantsπ_lift` — the universal property ([Loeffler, *Modular
  curves*, Prop 3.6.1], affine case: "for X = Spec(A) affine, Spec(A^G) works").

The proof is the standard one (SGA I V.1.1; Stacks 07S5/07S7): `invariantsπ` is
integral, surjective, with fibres the `G`-orbits (`SpecGroupAction.lean`); an
invariant morphism `f : Spec B ⟶ Y` is descended affine-locally on the target —
around each `p : Spec Bᴳ` one finds an invariant basic open `D(a) ∋ p` with
`π ⁻¹(D(a)) ⊆ f ⁻¹(V)` for an affine chart `V ∋ f(π⁻¹ p)` (integrality makes `π`
closed), and there the factorization is the algebra statement "invariants of the
localization = localization of the invariants" (`InvariantLocalization.lean`).
-/

universe u v

open TensorProduct AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

variable {G : Type*} [Group G]
variable {B : Type u} [CommRing B] [MulSemiringAction G B]
variable (R : Type v) [CommRing R] [Algebra R B] [SMulCommClass G R B]

section Algebra

variable [Finite G]

/-- **Factorization through the localized invariants** (the algebra engine of the
affine quotient): a ring hom `φ : C →+* B_a`, `a` an invariant, whose image is fixed
by the localized `G`-action factors uniquely through the localized inclusion
`(Bᴳ)_a →+* B_a`. -/
theorem existsUnique_factor_fixedPoints_away {C : Type u} [CommRing C]
    (a : FixedPoints.subalgebra R B G)
    (φ : C →+* Localization.Away ((a : B)))
    (hφ : ∀ (g : G) (c : C), MulSemiringAction.awayHom (fun g => a.2 g) g (φ c) = φ c) :
    ∃! ψ : C →+* Localization.Away a,
      (IsLocalization.map (Localization.Away ((a : B)))
        (algebraMap (FixedPoints.subalgebra R B G) B)
        (Submonoid.powers_le_comap_algebraMap R a)).comp ψ = φ := by
  set inclMap : Localization.Away a →+* Localization.Away ((a : B)) :=
    IsLocalization.map (Localization.Away ((a : B)))
      (algebraMap (FixedPoints.subalgebra R B G) B)
      (Submonoid.powers_le_comap_algebraMap R a) with hinclMap
  have hinj : Function.Injective inclMap := fixedPoints_awayMap_injective R a
  have hrange : ∀ c : C, φ c ∈ inclMap.range := by
    intro c
    rw [RingHom.mem_range]
    obtain ⟨y, hy⟩ := (mem_range_fixedPoints_awayMap_iff R a (φ c)).mpr
      (fun g => hφ g c)
    exact ⟨y, hy⟩
  have hinv : Function.LeftInverse (Function.invFun inclMap) inclMap :=
    Function.leftInverse_invFun hinj
  set e := RingEquiv.ofLeftInverse hinv with he
  have hfac : ∀ c : C,
      inclMap (e.symm.toRingHom.comp (φ.codRestrict inclMap.range hrange) c) = φ c := by
    intro c
    change inclMap (e.symm (φ.codRestrict inclMap.range hrange c)) = φ c
    rw [he, RingEquiv.ofLeftInverse_symm_apply]
    exact Function.invFun_eq (RingHom.mem_range.mp (hrange c))
  refine ⟨e.symm.toRingHom.comp (φ.codRestrict inclMap.range hrange), ?_, ?_⟩
  · ext c
    exact hfac c
  · intro ψ' hψ'
    ext c
    refine hinj ?_
    have h2 : inclMap (ψ' c) = φ c := by
      rw [← RingHom.comp_apply, hψ']
    rw [h2, hfac c]

end Algebra

section UniversalProperty

variable (G B) in
/-- Uniqueness of descent along the invariants morphism, in restriction-stable form:
for an open immersion `j : W ⟶ Spec Bᴳ`, two morphisms out of `W` agreeing after
precomposition with the pullback of `invariantsπ` along `j` are equal.

(`invariantsπ` is surjective with `Γ`-injectivity on basic opens — it is an effective
epimorphism; this is the epimorphism half, in the generality needed to glue local
descents at overlaps.) -/
theorem invariantsπ_hom_ext_of_isOpenImmersion [Finite G] {W Y : Scheme.{u}}
    (j : W ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G)))
    [IsOpenImmersion j] (h₁ h₂ : W ⟶ Y)
    (H : pullback.snd (invariantsπ G B R) j ≫ h₁ =
      pullback.snd (invariantsπ G B R) j ≫ h₂) :
    h₁ = h₂ := by
  -- `pullback.snd π j` is surjective (`Surjective` is stable under base change),
  -- so `h₁` and `h₂` agree on points.
  have hπ : Surjective (invariantsπ G B R) := ⟨invariantsπ_surjective G B R⟩
  have hsnd : Surjective (pullback.snd (invariantsπ G B R) j) :=
    MorphismProperty.pullback_snd _ _ hπ
  have hbase : ∀ w : W, h₁ w = h₂ w := by
    intro w
    obtain ⟨z, hz⟩ := hsnd.surj w
    rw [← hz, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, H]
  -- Around every point of `W` there is an open chart on which `h₁` and `h₂` agree.
  have key : ∀ w : W, ∃ (Z : Scheme.{u}) (ℓ : Z ⟶ W),
      IsOpenImmersion ℓ ∧ (∃ z, ℓ z = w) ∧ ℓ ≫ h₁ = ℓ ≫ h₂ := by
    intro w
    -- an affine chart `ι` of `Y` around `h₁ w`
    obtain ⟨i₀, y₀, hy₀⟩ := Y.affineCover.exists_eq (h₁ w)
    set ι := Y.affineCover.f i₀ with hι
    -- `T`: the locus where `h₁` (equivalently `h₂`) lands in the chart
    set T : Set W := h₁.base ⁻¹' Set.range ι with hT
    have hTopen : IsOpen T := ι.isOpenEmbedding.isOpen_range.preimage h₁.continuous
    have hwT : w ∈ T := ⟨y₀, hy₀⟩
    -- push into `Spec Bᴳ` along `j` and find an invariant basic open inside
    have hOopen : IsOpen (j.base '' T) := j.isOpenEmbedding.isOpenMap _ hTopen
    obtain ⟨s, ⟨a, rfl⟩, hjws, hsO⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (⟨w, hwT, rfl⟩ : j w ∈ j.base '' T) hOopen
    -- the localization chart over `D(a)` and its lift `ℓ` to `W`
    set κ : Spec (CommRingCat.of (Localization.Away a)) ⟶
        Spec (CommRingCat.of (FixedPoints.subalgebra R B G)) :=
      Spec.map (CommRingCat.ofHom
        (algebraMap (FixedPoints.subalgebra R B G) (Localization.Away a))) with hκ
    have hκrange : Set.range ⇑κ = (↑(PrimeSpectrum.basicOpen a) :
        Set (PrimeSpectrum (FixedPoints.subalgebra R B G))) :=
      PrimeSpectrum.localization_away_comap_range (Localization.Away a) a
    have hκj : Set.range ⇑κ ⊆ Set.range ⇑j := by
      rw [hκrange]
      exact hsO.trans (Set.image_subset_range _ _)
    set ℓ := IsOpenImmersion.lift j κ hκj with hℓ
    have hℓj : ℓ ≫ j = κ := IsOpenImmersion.lift_fac j κ hκj
    have hℓimm : IsOpenImmersion ℓ := by
      have : IsOpenImmersion (ℓ ≫ j) := hℓj ▸ inferInstance
      exact IsOpenImmersion.of_comp ℓ j
    -- the range of `ℓ` lies in `T` and contains `w`
    have hrangeT : ∀ v, ℓ v ∈ T := by
      intro v
      have h5 : j (ℓ v) ∈ j.base '' T := by
        refine hsO ?_
        change j (ℓ v) ∈ (↑(PrimeSpectrum.basicOpen a) :
          Set (PrimeSpectrum (FixedPoints.subalgebra R B G)))
        rw [← hκrange]
        exact ⟨v, by rw [← hℓj, Scheme.Hom.comp_apply]⟩
      obtain ⟨t, htT, ht⟩ := h5
      rwa [← j.isOpenEmbedding.injective ht]
    have hwℓ : ∃ z, ℓ z = w := by
      have h6 : j w ∈ Set.range ⇑κ := by
        rw [hκrange]
        exact hjws
      obtain ⟨v, hv⟩ := h6
      refine ⟨v, j.isOpenEmbedding.injective ?_⟩
      rw [← hℓj, Scheme.Hom.comp_apply] at hv
      exact hv
    -- lift `ℓ ≫ hᵢ` into the affine chart
    have hrange₁ : Set.range ⇑(ℓ ≫ h₁) ⊆ Set.range ⇑ι := by
      rintro _ ⟨v, rfl⟩
      exact hrangeT v
    have hrange₂ : Set.range ⇑(ℓ ≫ h₂) ⊆ Set.range ⇑ι := by
      rintro _ ⟨v, rfl⟩
      have h7 : (ℓ ≫ h₂) v = h₁ (ℓ v) := by
        rw [Scheme.Hom.comp_apply, hbase (ℓ v)]
      rw [Scheme.Hom.comp_apply] at h7 ⊢
      rw [h7]
      exact hrangeT v
    set t₁ := IsOpenImmersion.lift ι (ℓ ≫ h₁) hrange₁ with ht₁def
    set t₂ := IsOpenImmersion.lift ι (ℓ ≫ h₂) hrange₂ with ht₂def
    have ht₁ : t₁ ≫ ι = ℓ ≫ h₁ := IsOpenImmersion.lift_fac ι (ℓ ≫ h₁) hrange₁
    have ht₂ : t₂ ≫ ι = ℓ ≫ h₂ := IsOpenImmersion.lift_fac ι (ℓ ≫ h₂) hrange₂
    -- the B-side chart and the comparison map into the pullback
    set κB : Spec (CommRingCat.of (Localization.Away ((a : B)))) ⟶
        Spec (CommRingCat.of B) :=
      Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away ((a : B))))) with hκB
    set πa : Spec (CommRingCat.of (Localization.Away ((a : B)))) ⟶
        Spec (CommRingCat.of (Localization.Away a)) :=
      Spec.map (CommRingCat.ofHom (IsLocalization.map
        (Localization.Away ((a : B)))
        (algebraMap (FixedPoints.subalgebra R B G) B)
        (Submonoid.powers_le_comap_algebraMap R a))) with hπa
    have hsquare : κB ≫ invariantsπ G B R = πa ≫ κ := by
      rw [hκB, hπa, hκ, invariantsπ, ← Spec.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact (IsLocalization.map_comp _).symm
    set ρ := pullback.lift κB (πa ≫ ℓ)
      (by rw [hsquare, Category.assoc, hℓj]) with hρ
    have hρsnd : ρ ≫ pullback.snd (invariantsπ G B R) j = πa ≫ ℓ :=
      pullback.lift_snd _ _ _
    -- the localized invariants morphism coequalizes `h₁, h₂` after `ℓ`
    have hπaℓ : πa ≫ ℓ ≫ h₁ = πa ≫ ℓ ≫ h₂ := by
      rw [← Category.assoc, ← hρsnd, Category.assoc, H, ← Category.assoc, hρsnd,
        Category.assoc]
    have hπat : πa ≫ t₁ = πa ≫ t₂ := by
      rw [← cancel_mono ι, Category.assoc, Category.assoc, ht₁, ht₂]
      exact hπaℓ
    -- cancel `πa` on `Γ`-level: the localized inclusion is injective
    have ht : t₁ = t₂ := by
      rw [← cancel_mono (Y.affineCover.X i₀).isoSpec.hom]
      obtain ⟨φ₁, hφ₁⟩ := Spec.map_surjective (t₁ ≫ (Y.affineCover.X i₀).isoSpec.hom)
      obtain ⟨φ₂, hφ₂⟩ := Spec.map_surjective (t₂ ≫ (Y.affineCover.X i₀).isoSpec.hom)
      rw [← hφ₁, ← hφ₂]
      congr 1
      have h8 : πa ≫ Spec.map φ₁ = πa ≫ Spec.map φ₂ := by
        rw [hφ₁, hφ₂, ← Category.assoc, ← Category.assoc, hπat]
      rw [hπa, ← Spec.map_comp, ← Spec.map_comp] at h8
      have h9 := Spec.map_injective h8
      ext c
      have h10 := congrArg (fun ψ => ψ.hom c) h9
      exact fixedPoints_awayMap_injective R a h10
    refine ⟨_, ℓ, hℓimm, hwℓ, ?_⟩
    rw [← ht₁, ← ht₂, ht]
  -- glue: the charts form an open cover of `W`
  choose Z ℓ himm hcov heq using key
  have := himm
  exact Scheme.Cover.hom_ext
    (Scheme.Cover.mkOfCovers W Z ℓ
      (fun x => ⟨x, (hcov x).choose, (hcov x).choose_spec⟩)
      (fun w => himm w))
    h₁ h₂ heq

variable (G B) in
/-- Uniqueness of descent along the invariants morphism: `invariantsπ` is an
epimorphism of schemes. -/
theorem invariantsπ_hom_ext [Finite G] {Y : Scheme.{u}}
    (h₁ h₂ : Spec (CommRingCat.of (FixedPoints.subalgebra R B G)) ⟶ Y)
    (H : invariantsπ G B R ≫ h₁ = invariantsπ G B R ≫ h₂) :
    h₁ = h₂ := by
  refine invariantsπ_hom_ext_of_isOpenImmersion G B R (𝟙 _) h₁ h₂ ?_
  have hc := pullback.condition (f := invariantsπ G B R)
    (g := 𝟙 (Spec (CommRingCat.of (FixedPoints.subalgebra R B G))))
  rw [Category.comp_id] at hc
  rw [← hc, Category.assoc, Category.assoc, H]

/-- The basic-open chart of `Spec Bᴳ` at an invariant `a`. -/
private noncomputable def chartA (a : FixedPoints.subalgebra R B G) :
    Spec (CommRingCat.of (Localization.Away a)) ⟶
      Spec (CommRingCat.of (FixedPoints.subalgebra R B G)) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (FixedPoints.subalgebra R B G) (Localization.Away a)))

/-- The basic-open chart of `Spec B` at (the image of) an invariant `a`. -/
private noncomputable def chartB (a : FixedPoints.subalgebra R B G) :
    Spec (CommRingCat.of (Localization.Away ((a : B)))) ⟶ Spec (CommRingCat.of B) :=
  Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away ((a : B)))))

/-- The localized invariants morphism over the chart at `a`. -/
private noncomputable def chartπ (a : FixedPoints.subalgebra R B G) :
    Spec (CommRingCat.of (Localization.Away ((a : B)))) ⟶
      Spec (CommRingCat.of (Localization.Away a)) :=
  Spec.map (CommRingCat.ofHom (IsLocalization.map
    (Localization.Away ((a : B)))
    (algebraMap (FixedPoints.subalgebra R B G) B)
    (Submonoid.powers_le_comap_algebraMap R a)))

private theorem chartπ_def (a : FixedPoints.subalgebra R B G) :
    chartπ R a = Spec.map (CommRingCat.ofHom (IsLocalization.map
      (Localization.Away ((a : B)))
      (algebraMap (FixedPoints.subalgebra R B G) B)
      (Submonoid.powers_le_comap_algebraMap R a))) := rfl

private theorem chartA_def (a : FixedPoints.subalgebra R B G) :
    chartA R a = Spec.map (CommRingCat.ofHom
      (algebraMap (FixedPoints.subalgebra R B G) (Localization.Away a))) := rfl

private theorem chartB_def (a : FixedPoints.subalgebra R B G) :
    chartB R a = Spec.map (CommRingCat.ofHom
      (algebraMap B (Localization.Away ((a : B))))) := rfl

private instance (a : FixedPoints.subalgebra R B G) : IsOpenImmersion (chartA R a) :=
  inferInstanceAs (IsOpenImmersion (Spec.map _))

private instance (a : FixedPoints.subalgebra R B G) : IsOpenImmersion (chartB R a) :=
  inferInstanceAs (IsOpenImmersion (Spec.map _))

private theorem chartA_opensRange (a : FixedPoints.subalgebra R B G) :
    (chartA R a).opensRange = PrimeSpectrum.basicOpen a :=
  Scheme.Hom.opensRange_localizationAway
    (R := CommRingCat.of (FixedPoints.subalgebra R B G)) a

private theorem chartB_opensRange (a : FixedPoints.subalgebra R B G) :
    (chartB R a).opensRange = PrimeSpectrum.basicOpen ((a : B)) :=
  Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of B) ((a : B))

variable (G B) in
private theorem chart_square (a : FixedPoints.subalgebra R B G) :
    chartB R a ≫ invariantsπ G B R = chartπ R a ≫ chartA R a := by
  rw [chartB_def, chartπ_def, chartA_def, invariantsπ, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact (IsLocalization.map_comp _).symm

variable (G B) in
/-- The chart square is cartesian: `D(a) ×_{Spec Bᴳ} Spec B = D((a : B))`. -/
private theorem isPullback_chart (a : FixedPoints.subalgebra R B G) :
    IsPullback (chartπ R a) (chartB R a) (chartA R a) (invariantsπ G B R) := by
  refine IsOpenImmersion.isPullback (chartπ R a) (chartB R a) (chartA R a)
    (invariantsπ G B R) (chart_square G B R a) ?_
  rw [chartA_opensRange, chartB_opensRange]
  exact TopologicalSpace.Opens.ext rfl

variable (G B) in
/-- One leg of the gluing compatibility: over any morphism `j'` into `Spec Bᴳ` that
factors through the chart at an invariant `r`, a local descent `qr` of `f` pulls back
to `pullback.fst π j' ≫ f`. -/
private theorem chart_descent_side [Finite G] {Y : Scheme.{u}}
    (f : Spec (CommRingCat.of B) ⟶ Y)
    {P : Scheme.{u}} (j' : P ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G)))
    (r : FixedPoints.subalgebra R B G)
    (qr : Spec (CommRingCat.of (Localization.Away r)) ⟶ Y)
    (hqr : chartπ R r ≫ qr = chartB R r ≫ f)
    (pr : P ⟶ Spec (CommRingCat.of (Localization.Away r)))
    (hpr : pr ≫ chartA R r = j') :
    pullback.snd (invariantsπ G B R) j' ≫ (pr ≫ qr) =
      pullback.fst (invariantsπ G B R) j' ≫ f := by
  have hcone : (pullback.snd (invariantsπ G B R) j' ≫ pr) ≫ chartA R r =
      pullback.fst (invariantsπ G B R) j' ≫ invariantsπ G B R := by
    rw [Category.assoc, hpr]
    exact pullback.condition.symm
  have hu₁ := (isPullback_chart G B R r).lift_fst
    (pullback.snd (invariantsπ G B R) j' ≫ pr)
    (pullback.fst (invariantsπ G B R) j') hcone
  have hu₂ := (isPullback_chart G B R r).lift_snd
    (pullback.snd (invariantsπ G B R) j' ≫ pr)
    (pullback.fst (invariantsπ G B R) j') hcone
  rw [← Category.assoc, ← hu₁, Category.assoc, hqr, ← Category.assoc, hu₂]

variable (G B) in
/-- Around every point of `Spec Bᴳ` there is an invariant basic open over which a
`G`-invariant morphism out of `Spec B` descends. -/
private theorem exists_chart_descent [Finite G] {Y : Scheme.{u}}
    (f : Spec (CommRingCat.of B) ⟶ Y) (hf : ∀ g : G, specSMul g ≫ f = f)
    (p : Spec (CommRingCat.of (FixedPoints.subalgebra R B G))) :
    ∃ a : FixedPoints.subalgebra R B G,
      p ∈ PrimeSpectrum.basicOpen a ∧
      ∃ qa : Spec (CommRingCat.of (Localization.Away a)) ⟶ Y,
        chartπ R a ≫ qa = chartB R a ≫ f := by
  -- `f` is constant on the fibres of `invariantsπ` (they are orbits)
  have hconst : ∀ x y : Spec (CommRingCat.of B),
      invariantsπ G B R x = invariantsπ G B R y → f x = f y := by
    intro x y hxy
    obtain ⟨g, hg⟩ := (invariantsπ_apply_eq_iff G B R x y).mp hxy
    rw [← hg, ← Scheme.Hom.comp_apply, hf g]
  -- `invariantsπ` is a closed map (it is integral)
  have hclosed : IsClosedMap ⇑(invariantsπ G B R) := by
    have hint : (algebraMap (FixedPoints.subalgebra R B G) B).IsIntegral :=
      Algebra.isIntegral_def.mp
        (Algebra.IsInvariant.isIntegral (FixedPoints.subalgebra R B G) B G)
    exact PrimeSpectrum.isClosedMap_comap_of_isIntegral _ hint
  -- a point of the fibre and an affine chart of `Y` around its image
  obtain ⟨x, hx⟩ := invariantsπ_surjective G B R p
  obtain ⟨i₀, y₀, hy₀⟩ := Y.affineCover.exists_eq (f x)
  set ι := Y.affineCover.f i₀ with hι
  -- the saturated open `U` and the separating invariant basic open
  set U : Set (Spec (CommRingCat.of B)) := f.base ⁻¹' Set.range ι with hU
  have hUopen : IsOpen U := ι.isOpenEmbedding.isOpen_range.preimage f.continuous
  have hfibU : ∀ x', invariantsπ G B R x' = p → x' ∈ U := by
    intro x' hx'
    have h4 : f x' = f x := hconst x' x (by rw [hx', hx])
    change f x' ∈ Set.range ⇑ι
    rw [h4]
    exact ⟨y₀, hy₀⟩
  have hpZ : p ∉ (invariantsπ G B R).base '' Uᶜ := by
    rintro ⟨x', hx'U, hx'⟩
    exact hx'U (hfibU x' hx')
  have hZclosed : IsClosed ((invariantsπ G B R).base '' Uᶜ) :=
    hclosed _ hUopen.isClosed_compl
  obtain ⟨s, ⟨a, rfl⟩, hps, hsZ⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (show p ∈ ((invariantsπ G B R).base '' Uᶜ)ᶜ from hpZ) hZclosed.isOpen_compl
  refine ⟨a, hps, ?_⟩
  -- the `B`-side chart lands in `U`
  have hchartU : ∀ v, chartB R a v ∈ U := by
    intro v
    by_contra hvU
    have hmemA : ∀ z, chartA R a z ∈ PrimeSpectrum.basicOpen a := by
      intro z
      have h9 : chartA R a z ∈ Set.range ⇑(chartA R a) := ⟨z, rfl⟩
      exact chartA_opensRange R a ▸ h9
    refine hsZ ?_ ⟨chartB R a v, hvU, rfl⟩
    change invariantsπ G B R (chartB R a v) ∈
      (↑(PrimeSpectrum.basicOpen a) :
        Set (PrimeSpectrum (FixedPoints.subalgebra R B G)))
    rw [← Scheme.Hom.comp_apply, chart_square G B R a, Scheme.Hom.comp_apply]
    exact hmemA _
  -- lift `chartB ≫ f` into the affine chart of `Y`
  have hrange : Set.range ⇑(chartB R a ≫ f) ⊆ Set.range ⇑ι := by
    rintro _ ⟨v, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hchartU v
  set t := IsOpenImmersion.lift ι (chartB R a ≫ f) hrange with htdef
  have ht : t ≫ ι = chartB R a ≫ f := IsOpenImmersion.lift_fac ι _ hrange
  -- the Γ-level ring hom of the lifted restriction
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (t ≫ (Y.affineCover.X i₀).isoSpec.hom)
  -- `φ` has `G`-fixed image: transport the invariance of `f` through the chart
  have hspec : ∀ g : G,
      Spec.map (CommRingCat.ofHom (MulSemiringAction.awayHom (fun g => a.2 g) g)) ≫
        chartB R a = chartB R a ≫ specSMul g := by
    intro g
    rw [chartB_def, specSMul, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact IsLocalization.map_comp _
  have hφfix : ∀ (g : G) (c), MulSemiringAction.awayHom (fun g => a.2 g) g
      (φ.hom c) = φ.hom c := by
    intro g
    have h11 : Spec.map (CommRingCat.ofHom
        (MulSemiringAction.awayHom (fun g => a.2 g) g)) ≫ t = t := by
      rw [← cancel_mono ι, Category.assoc, ht, ← Category.assoc, hspec g,
        Category.assoc, hf g]
    have h12 : Spec.map (CommRingCat.ofHom
          (MulSemiringAction.awayHom (fun g => a.2 g) g)) ≫ Spec.map φ =
        Spec.map φ := by
      rw [hφ, ← Category.assoc, h11]
    rw [← Spec.map_comp] at h12
    have h13 := Spec.map_injective h12
    intro c
    exact congrArg (fun ψ => ψ.hom c) h13
  -- factor through the invariants (the algebra engine)
  obtain ⟨ψ, hψ, -⟩ := existsUnique_factor_fixedPoints_away R a φ.hom hφfix
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ (Y.affineCover.X i₀).isoSpec.inv ≫ ι, ?_⟩
  have h14 : chartπ R a ≫ Spec.map (CommRingCat.ofHom ψ) = Spec.map φ := by
    rw [chartπ_def, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h14' : CommRingCat.ofHom ((IsLocalization.map
        (Localization.Away ((a : B)))
        (algebraMap (FixedPoints.subalgebra R B G) B)
        (Submonoid.powers_le_comap_algebraMap R a)).comp ψ) = φ := by
      rw [hψ]
      exact CommRingCat.ofHom_hom φ
    rw [h14']
  rw [← Category.assoc, h14, hφ, Category.assoc, Iso.hom_inv_id_assoc, ht]

variable (G B) in
/-- Existence of descent: every `G`-invariant morphism out of `Spec B` factors
through the invariants morphism. -/
theorem exists_invariantsπ_lift [Finite G] {Y : Scheme.{u}}
    (f : Spec (CommRingCat.of B) ⟶ Y) (hf : ∀ g : G, specSMul g ≫ f = f) :
    ∃ q : Spec (CommRingCat.of (FixedPoints.subalgebra R B G)) ⟶ Y,
      invariantsπ G B R ≫ q = f := by
  choose a hmem qa hqa using exists_chart_descent G B R f hf
  have hcoverA : ∀ p : Spec (CommRingCat.of (FixedPoints.subalgebra R B G)),
      ∃ v, chartA R (a p) v = p := by
    intro p
    have h15' : p ∈ (chartA R (a p)).opensRange := by
      rw [chartA_opensRange]
      exact hmem p
    exact h15'
  set 𝒰 : (Spec (CommRingCat.of (FixedPoints.subalgebra R B G))).OpenCover :=
    Scheme.Cover.mkOfCovers
    (J := ↥(Spec (CommRingCat.of (FixedPoints.subalgebra R B G))))
    (fun p => Spec (CommRingCat.of (Localization.Away (a p))))
    (fun p => chartA R (a p))
    (fun p => ⟨p, hcoverA p⟩)
    (fun p => inferInstance) with h𝒰
  -- compatibility on overlaps, via the restriction-stable uniqueness
  have hcompat : ∀ p q : Spec (CommRingCat.of (FixedPoints.subalgebra R B G)),
      pullback.fst (chartA R (a p)) (chartA R (a q)) ≫ qa p =
        pullback.snd (chartA R (a p)) (chartA R (a q)) ≫ qa q := by
    intro p q
    refine invariantsπ_hom_ext_of_isOpenImmersion G B R
      (pullback.fst (chartA R (a p)) (chartA R (a q)) ≫ chartA R (a p)) _ _ ?_
    rw [chart_descent_side G B R f _ (a p) (qa p) (hqa p)
        (pullback.fst (chartA R (a p)) (chartA R (a q))) rfl,
      chart_descent_side G B R f _ (a q) (qa q) (hqa q)
        (pullback.snd (chartA R (a p)) (chartA R (a q))) pullback.condition.symm]
  refine ⟨𝒰.glueMorphisms (fun p => qa p) hcompat, ?_⟩
  -- verify the factorization on the `B`-side cover
  have hcoverB : ∀ x : Spec (CommRingCat.of B),
      ∃ v, chartB R (a (invariantsπ G B R x)) v = x := by
    intro x
    have h17 : x ∈ (chartB R (a (invariantsπ G B R x))).opensRange := by
      rw [chartB_opensRange]
      exact hmem (invariantsπ G B R x)
    exact h17
  refine Scheme.Cover.hom_ext
    ((Scheme.Cover.mkOfCovers
      (J := ↥(Spec (CommRingCat.of B)))
      (fun x => Spec (CommRingCat.of
        (Localization.Away ((a (invariantsπ G B R x) : B)))))
      (fun x => chartB R (a (invariantsπ G B R x)))
      (fun x => ⟨x, hcoverB x⟩)
      (fun x => inferInstance) : (Spec (CommRingCat.of B)).OpenCover))
    _ _ (fun x => ?_)
  change chartB R (a (invariantsπ G B R x)) ≫ invariantsπ G B R ≫
      𝒰.glueMorphisms (fun p => qa p) hcompat =
    chartB R (a (invariantsπ G B R x)) ≫ f
  rw [← Category.assoc, chart_square G B R, Category.assoc]
  have h18 : chartA R (a (invariantsπ G B R x)) ≫
      𝒰.glueMorphisms (fun p => qa p) hcompat = qa (invariantsπ G B R x) :=
    𝒰.ι_glueMorphisms _ hcompat (invariantsπ G B R x)
  rw [h18]
  exact hqa (invariantsπ G B R x)

variable (G B) in
/-- **The affine quotient by a finite group** ([Loeffler, *Modular curves*,
Prop 3.6.1], affine case; SGA I V.1.1; Stacks 07S7): `Spec Bᴳ` together with the
invariants morphism represents the functor `Y ↦ {G-invariant morphisms Spec B ⟶ Y}`
— every `G`-invariant morphism out of `Spec B` factors uniquely through
`invariantsπ : Spec B ⟶ Spec Bᴳ`. In particular `Spec Bᴳ` is the categorical
quotient of `Spec B` by `G` in the category of all schemes. -/
theorem existsUnique_invariantsπ_lift [Finite G] {Y : Scheme.{u}}
    (f : Spec (CommRingCat.of B) ⟶ Y) (hf : ∀ g : G, specSMul g ≫ f = f) :
    ∃! q : Spec (CommRingCat.of (FixedPoints.subalgebra R B G)) ⟶ Y,
      invariantsπ G B R ≫ q = f := by
  obtain ⟨q, hq⟩ := exists_invariantsπ_lift G B R f hf
  exact ⟨q, hq, fun q' hq' => invariantsπ_hom_ext G B R q' q (hq'.trans hq.symm)⟩

variable (G B) in
/-- **Invariant basic opens form a basis of the stable opens** (the separation step
of the quotient construction, isolated): inside `Spec B`, every `G`-stable open
neighbourhood of a point contains an invariant basic open neighbourhood
`D((a : B))`, `a ∈ Bᴳ`. -/
theorem exists_mem_basicOpen_subset_of_stable [Finite G]
    {U : Set (Spec (CommRingCat.of B))} (hU : IsOpen U)
    (hstable : ∀ (g : G) (x : Spec (CommRingCat.of B)), x ∈ U → specSMul g x ∈ U)
    (x : Spec (CommRingCat.of B)) (hx : x ∈ U) :
    ∃ a : FixedPoints.subalgebra R B G,
      x ∈ PrimeSpectrum.basicOpen ((a : B)) ∧
      (↑(PrimeSpectrum.basicOpen ((a : B))) : Set (PrimeSpectrum B)) ⊆ U := by
  have hclosed : IsClosedMap ⇑(invariantsπ G B R) := by
    have hint : (algebraMap (FixedPoints.subalgebra R B G) B).IsIntegral :=
      Algebra.isIntegral_def.mp
        (Algebra.IsInvariant.isIntegral (FixedPoints.subalgebra R B G) B G)
    exact PrimeSpectrum.isClosedMap_comap_of_isIntegral _ hint
  -- the fibre through `x` lies in `U`
  have hfibU : ∀ x', invariantsπ G B R x' = invariantsπ G B R x → x' ∈ U := by
    intro x' hx'
    obtain ⟨g, hg⟩ := (invariantsπ_apply_eq_iff G B R x x').mp hx'.symm
    rw [← hg]
    exact hstable g x hx
  have hpZ : invariantsπ G B R x ∉ (invariantsπ G B R).base '' Uᶜ := by
    rintro ⟨x', hx'U, hx'⟩
    exact hx'U (hfibU x' hx')
  have hZclosed : IsClosed ((invariantsπ G B R).base '' Uᶜ) :=
    hclosed _ hU.isClosed_compl
  obtain ⟨s, ⟨a, rfl⟩, hps, hsZ⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (show invariantsπ G B R x ∈ ((invariantsπ G B R).base '' Uᶜ)ᶜ from hpZ)
      hZclosed.isOpen_compl
  refine ⟨a, ?_, ?_⟩
  · exact hps
  · intro y hy
    by_contra hyU
    refine hsZ ?_ ⟨y, hyU, rfl⟩
    change invariantsπ G B R y ∈
      (↑(PrimeSpectrum.basicOpen a) :
        Set (PrimeSpectrum (FixedPoints.subalgebra R B G)))
    exact hy
  -- (membership dictionary: `y ∈ D((a : B)) ↔ π y ∈ D(a)` is definitional)

variable (G B) in
/-- The invariants morphism is a topological quotient map (it is a closed
surjection). -/
theorem invariantsπ_isQuotientMap [Finite G] :
    Topology.IsQuotientMap ⇑(invariantsπ G B R).base := by
  have hclosed : IsClosedMap ⇑(invariantsπ G B R) := by
    have hint : (algebraMap (FixedPoints.subalgebra R B G) B).IsIntegral :=
      Algebra.isIntegral_def.mp
        (Algebra.IsInvariant.isIntegral (FixedPoints.subalgebra R B G) B G)
    exact PrimeSpectrum.isClosedMap_comap_of_isIntegral _ hint
  exact hclosed.isQuotientMap (invariantsπ G B R).base.hom.continuous
    (invariantsπ_surjective G B R)

variable (G B) in
/-- Images of `G`-stable opens under the invariants morphism are open. -/
theorem isOpen_image_invariantsπ_of_stable [Finite G]
    {U : Set (Spec (CommRingCat.of B))} (hU : IsOpen U)
    (hstable : ∀ (g : G) (x : Spec (CommRingCat.of B)), x ∈ U → specSMul g x ∈ U) :
    IsOpen (⇑(invariantsπ G B R).base '' U) := by
  have hsat : ⇑(invariantsπ G B R).base ⁻¹' (⇑(invariantsπ G B R).base '' U) = U := by
    ext y
    constructor
    · rintro ⟨x, hxU, hxy⟩
      obtain ⟨g, hg⟩ := (invariantsπ_apply_eq_iff G B R x y).mp hxy
      rw [← hg]
      exact hstable g x hxU
    · intro hy
      exact ⟨y, hy, rfl⟩
  rw [← (invariantsπ_isQuotientMap G B R).isOpen_preimage, hsat]
  exact hU

variable (G B) in
/-- The `G`-action on `pullback π j` covering `specSMul` (the `j`-relative action
of the descent theory). -/
noncomputable def pullbackSpecSMul {Q' : Scheme.{u}}
    (j : Q' ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G))) (g : G) :
    pullback (invariantsπ G B R) j ⟶ pullback (invariantsπ G B R) j :=
  pullback.lift (pullback.fst _ _ ≫ specSMul g) (pullback.snd _ _)
    (by rw [Category.assoc, specSMul_invariantsπ]; exact pullback.condition)

@[reassoc (attr := simp)]
theorem pullbackSpecSMul_fst {Q' : Scheme.{u}}
    (j : Q' ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G))) (g : G) :
    pullbackSpecSMul G B R j g ≫ pullback.fst (invariantsπ G B R) j =
      pullback.fst (invariantsπ G B R) j ≫ specSMul g :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pullbackSpecSMul_snd {Q' : Scheme.{u}}
    (j : Q' ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G))) (g : G) :
    pullbackSpecSMul G B R j g ≫ pullback.snd (invariantsπ G B R) j =
      pullback.snd (invariantsπ G B R) j :=
  pullback.lift_snd _ _ _

variable (G B) in
/-- **Overlap comparison for the relative chart descent.** Given a chart at an
invariant `a` with a local descent `qa` of `f` (through `κB'a`) and its lift `ℓa` to
`Q'`, any factorization `pr` of an overlap `j''` through `ℓa` yields a comparison map
`m : pullback π j'' ⟶ pullback π j` with `m ≫ pullback.fst = pullback.fst` and
`pullback.snd _ j'' ≫ (pr ≫ qa) = m ≫ f`. This is the per-chart building block of the
gluing compatibility in `exists_invariantsπ_lift_of_isOpenImmersion`. -/
private theorem relative_chart_descent_comparison {Y Q' J'' : Scheme.{u}}
    (j : Q' ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G)))
    (f : pullback (invariantsπ G B R) j ⟶ Y)
    (a : FixedPoints.subalgebra R B G)
    (qa : Spec (CommRingCat.of (Localization.Away a)) ⟶ Y)
    (κB'a : Spec (CommRingCat.of (Localization.Away ((a : B)))) ⟶
      pullback (invariantsπ G B R) j)
    (hκB'fst : κB'a ≫ pullback.fst (invariantsπ G B R) j = chartB R a)
    (hqa : chartπ R a ≫ qa = κB'a ≫ f)
    (ℓa : Spec (CommRingCat.of (Localization.Away a)) ⟶ Q')
    (hℓj : ℓa ≫ j = chartA R a)
    (j'' : J'' ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G)))
    (pr : J'' ⟶ Spec (CommRingCat.of (Localization.Away a)))
    (hpr : pr ≫ ℓa ≫ j = j'') :
    ∃ m : pullback (invariantsπ G B R) j'' ⟶ pullback (invariantsπ G B R) j,
      m ≫ pullback.fst (invariantsπ G B R) j =
        pullback.fst (invariantsπ G B R) j'' ∧
      pullback.snd (invariantsπ G B R) j'' ≫ (pr ≫ qa) = m ≫ f := by
  have hcone : (pullback.snd (invariantsπ G B R) j'' ≫ pr) ≫ chartA R a =
      pullback.fst (invariantsπ G B R) j'' ≫ invariantsπ G B R := by
    rw [Category.assoc, ← hℓj, hpr]
    exact pullback.condition.symm
  have hu₁ := (isPullback_chart G B R a).lift_fst
    (pullback.snd (invariantsπ G B R) j'' ≫ pr)
    (pullback.fst (invariantsπ G B R) j'') hcone
  have hu₂ := (isPullback_chart G B R a).lift_snd
    (pullback.snd (invariantsπ G B R) j'' ≫ pr)
    (pullback.fst (invariantsπ G B R) j'') hcone
  refine ⟨(isPullback_chart G B R a).lift _ _ hcone ≫ κB'a, ?_, ?_⟩
  · rw [Category.assoc, hκB'fst, hu₂]
  · have h40 : ((isPullback_chart G B R a).lift _ _ hcone ≫ chartπ R a) ≫ qa =
        (pullback.snd (invariantsπ G B R) j'' ≫ pr) ≫ qa := by
      rw [hu₁]
    calc pullback.snd (invariantsπ G B R) j'' ≫ (pr ≫ qa)
        = (pullback.snd (invariantsπ G B R) j'' ≫ pr) ≫ qa := by rw [Category.assoc]
      _ = ((isPullback_chart G B R a).lift _ _ hcone ≫ chartπ R a) ≫ qa := h40.symm
      _ = (isPullback_chart G B R a).lift _ _ hcone ≫ (chartπ R a ≫ qa) := by
          rw [Category.assoc]
      _ = (isPullback_chart G B R a).lift _ _ hcone ≫ (κB'a ≫ f) := by rw [hqa]
      _ = ((isPullback_chart G B R a).lift _ _ hcone ≫ κB'a) ≫ f := by
          rw [Category.assoc]

variable (G B) in
/-- **Per-point local descent for the relative quotient.** For an open immersion
`j : Q' ⟶ Spec Bᴳ` and a relatively-`G`-invariant morphism `f` out of `pullback π j`,
around every point of `Q'` there is an invariant basic open `D(a) ⊆ range j` together
with a local descent `qa` of `f` over the chart at `a`. This is the `j`-relative
analogue of `exists_chart_descent`; it supplies the local data glued in
`exists_invariantsπ_lift_of_isOpenImmersion`. -/
private theorem exists_relative_chart_descent [Finite G] {Q' Y : Scheme.{u}}
    (j : Q' ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G)))
    [IsOpenImmersion j]
    (f : pullback (invariantsπ G B R) j ⟶ Y)
    (hf : ∀ g : G, pullbackSpecSMul G B R j g ≫ f = f)
    (p : Q') :
    ∃ a : FixedPoints.subalgebra R B G,
      j p ∈ PrimeSpectrum.basicOpen a ∧
      (↑(PrimeSpectrum.basicOpen a) :
        Set (PrimeSpectrum (FixedPoints.subalgebra R B G))) ⊆ Set.range ⇑j ∧
      ∃ qa : Spec (CommRingCat.of (Localization.Away a)) ⟶ Y,
        ∀ (κB' : Spec (CommRingCat.of (Localization.Away ((a : B)))) ⟶
            pullback (invariantsπ G B R) j),
          κB' ≫ pullback.fst (invariantsπ G B R) j = chartB R a →
          chartπ R a ≫ qa = κB' ≫ f := by
    classical
    have hπ : Surjective (invariantsπ G B R) := ⟨invariantsπ_surjective G B R⟩
    have hsnd : Surjective (pullback.snd (invariantsπ G B R) j) :=
      MorphismProperty.pullback_snd _ _ hπ
    obtain ⟨z, hz⟩ := hsnd.surj p
    obtain ⟨i₀, y₀, hy₀⟩ := Y.affineCover.exists_eq (f z)
    set ι := Y.affineCover.f i₀ with hι
    -- the stable open `U ⊆ Spec B` where `f` (through `fst`) lands in the chart
    set U : Set (Spec (CommRingCat.of B)) :=
      ⇑(pullback.fst (invariantsπ G B R) j) '' (⇑f ⁻¹' Set.range ⇑ι) with hU
    have hUopen : IsOpen U :=
      (pullback.fst (invariantsπ G B R) j).isOpenEmbedding.isOpenMap _
        (ι.isOpenEmbedding.isOpen_range.preimage f.continuous)
    have hUstable : ∀ (g : G) (x' : Spec (CommRingCat.of B)),
        x' ∈ U → specSMul g x' ∈ U := by
      rintro g _ ⟨z', hz', rfl⟩
      refine ⟨pullbackSpecSMul G B R j g z', ?_, ?_⟩
      · change f _ ∈ Set.range ⇑ι
        rw [← Scheme.Hom.comp_apply, hf g]
        exact hz'
      · rw [← Scheme.Hom.comp_apply, pullbackSpecSMul_fst, Scheme.Hom.comp_apply]
    have hxU : pullback.fst (invariantsπ G B R) j z ∈ U := ⟨z, ⟨y₀, hy₀⟩, rfl⟩
    have hπx : invariantsπ G B R (pullback.fst (invariantsπ G B R) j z) = j p := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hz]
    -- an invariant basic open inside `π(U) ∩ range j` around `j p`
    have hO : IsOpen ((⇑(invariantsπ G B R).base '' U) ∩ Set.range ⇑j) :=
      (isOpen_image_invariantsπ_of_stable G B R hUopen hUstable).inter
        j.isOpenEmbedding.isOpen_range
    obtain ⟨s, ⟨a, rfl⟩, hjs, hsO⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (⟨⟨_, hxU, hπx⟩, ⟨p, rfl⟩⟩ :
          j p ∈ (⇑(invariantsπ G B R).base '' U) ∩ Set.range ⇑j) hO
    refine ⟨a, hjs, fun t ht => (hsO ht).2, ?_⟩
    -- `D((a : B)) ⊆ U` by saturation
    have hDU : (↑(PrimeSpectrum.basicOpen ((a : B))) : Set (PrimeSpectrum B)) ⊆ U := by
      intro y hy
      obtain ⟨u, huU, hu⟩ := (hsO (show invariantsπ G B R y ∈
        (↑(PrimeSpectrum.basicOpen a) :
          Set (PrimeSpectrum (FixedPoints.subalgebra R B G))) from hy)).1
      obtain ⟨g, hg⟩ := (invariantsπ_apply_eq_iff G B R u y).mp hu
      rw [← hg]
      exact hUstable g u huU
    -- lift the `B`-side chart through `fst`
    have hrangeκ : Set.range ⇑(chartB R a) ⊆
        Set.range ⇑(pullback.fst (invariantsπ G B R) j) := by
      rintro _ ⟨v, rfl⟩
      have h8 : chartB R a v ∈ U := hDU (by
        have h9 : chartB R a v ∈ (chartB R a).opensRange := ⟨v, rfl⟩
        rwa [chartB_opensRange] at h9)
      obtain ⟨z', _, hz'⟩ := h8
      exact ⟨z', hz'⟩
    set κB₀ := IsOpenImmersion.lift (pullback.fst (invariantsπ G B R) j)
      (chartB R a) hrangeκ with hκB₀
    have hκB₀fst : κB₀ ≫ pullback.fst (invariantsπ G B R) j = chartB R a :=
      IsOpenImmersion.lift_fac _ _ hrangeκ
    -- `κB₀ ≫ f` lands in the affine chart of `Y`
    have hrangeY : Set.range ⇑(κB₀ ≫ f) ⊆ Set.range ⇑ι := by
      rintro _ ⟨v, rfl⟩
      have h10 : chartB R a v ∈ U := hDU (by
        have h9 : chartB R a v ∈ (chartB R a).opensRange := ⟨v, rfl⟩
        rwa [chartB_opensRange] at h9)
      obtain ⟨z', hz'mem, hz'⟩ := h10
      have h11 : κB₀ v = z' :=
        (pullback.fst (invariantsπ G B R) j).isOpenEmbedding.injective (by
          rw [← Scheme.Hom.comp_apply, hκB₀fst, hz'])
      rw [Scheme.Hom.comp_apply, h11]
      exact hz'mem
    set t := IsOpenImmersion.lift ι (κB₀ ≫ f) hrangeY with htdef
    have ht : t ≫ ι = κB₀ ≫ f := IsOpenImmersion.lift_fac ι _ hrangeY
    -- the equivariance square for `κB₀`, via `fst`-monomorphy
    have hspec : ∀ g : G,
        Spec.map (CommRingCat.ofHom (MulSemiringAction.awayHom (fun g => a.2 g) g)) ≫
          κB₀ = κB₀ ≫ pullbackSpecSMul G B R j g := by
      intro g
      rw [← cancel_mono (pullback.fst (invariantsπ G B R) j)]
      rw [Category.assoc, Category.assoc, hκB₀fst, pullbackSpecSMul_fst,
        ← Category.assoc, hκB₀fst]
      rw [chartB_def, specSMul, ← Spec.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact IsLocalization.map_comp _
    -- the Γ-level ring hom of the lifted restriction, with G-fixed image
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (t ≫ (Y.affineCover.X i₀).isoSpec.hom)
    have hφfix : ∀ (g : G) (c), MulSemiringAction.awayHom (fun g => a.2 g) g
        (φ.hom c) = φ.hom c := by
      intro g
      have h11 : Spec.map (CommRingCat.ofHom
          (MulSemiringAction.awayHom (fun g => a.2 g) g)) ≫ t = t := by
        rw [← cancel_mono ι, Category.assoc, ht, ← Category.assoc, hspec g,
          Category.assoc, hf g]
      have h12 : Spec.map (CommRingCat.ofHom
            (MulSemiringAction.awayHom (fun g => a.2 g) g)) ≫ Spec.map φ =
          Spec.map φ := by
        rw [hφ, ← Category.assoc, h11]
      rw [← Spec.map_comp] at h12
      have h13 := Spec.map_injective h12
      intro c
      exact congrArg (fun ψ => ψ.hom c) h13
    obtain ⟨ψ, hψ, -⟩ := existsUnique_factor_fixedPoints_away R a φ.hom hφfix
    refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ (Y.affineCover.X i₀).isoSpec.inv ≫ ι,
      fun κB' hκB' => ?_⟩
    -- any factorization agrees with `κB₀` (fst is mono)
    have hκκ : κB' = κB₀ :=
      (cancel_mono (pullback.fst (invariantsπ G B R) j)).mp (by rw [hκB₀fst, hκB'])
    have h14 : chartπ R a ≫ Spec.map (CommRingCat.ofHom ψ) = Spec.map φ := by
      rw [chartπ_def, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have h14' : CommRingCat.ofHom ((IsLocalization.map
          (Localization.Away ((a : B)))
          (algebraMap (FixedPoints.subalgebra R B G) B)
          (Submonoid.powers_le_comap_algebraMap R a)).comp ψ) = φ := by
        rw [hψ]
        exact CommRingCat.ofHom_hom φ
      rw [h14']
    rw [hκκ, ← Category.assoc, h14, hφ, Category.assoc, Iso.hom_inv_id_assoc, ht]

variable (G B) in
/-- **`j`-relative existence of descent** (the keystone of the glued quotient): for
an open immersion `j : Q' ⟶ Spec Bᴳ`, every morphism out of `pullback π j` that is
invariant for the relative action descends to `Q'`. At `j = 𝟙` this recovers
`exists_invariantsπ_lift`; applied to the image of a stable open it produces the
open-immersion property of the local quotient maps; applied chart-wise it glues the
global quotient (T-Q5d). -/
theorem exists_invariantsπ_lift_of_isOpenImmersion [Finite G] {Q' Y : Scheme.{u}}
    (j : Q' ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G)))
    [IsOpenImmersion j]
    (f : pullback (invariantsπ G B R) j ⟶ Y)
    (hf : ∀ g : G, pullbackSpecSMul G B R j g ≫ f = f) :
    ∃ q : Q' ⟶ Y, pullback.snd (invariantsπ G B R) j ≫ q = f := by
  classical
  -- per-point local descent data (`exists_relative_chart_descent`), glued over `Q'`
  choose a hmem hrange qa hqa using exists_relative_chart_descent G B R j f hf
  have hliftA : ∀ p : Q', Set.range ⇑(chartA R (a p)) ⊆ Set.range ⇑j := by
    intro p t ht
    refine hrange p ?_
    obtain ⟨v, rfl⟩ := ht
    have h15 : chartA R (a p) v ∈ (chartA R (a p)).opensRange := ⟨v, rfl⟩
    rwa [chartA_opensRange] at h15
  -- the cover pieces: charts lifted through `j`
  have hcoverQ' : ∀ p : Q',
      ∃ v, IsOpenImmersion.lift j (chartA R (a p)) (hliftA p) v = p := by
    intro p
    have h16 : j p ∈ Set.range ⇑(chartA R (a p)) := by
      have h17 : j p ∈ (chartA R (a p)).opensRange := by
        rw [chartA_opensRange]
        exact hmem p
      exact h17
    obtain ⟨v, hv⟩ := h16
    refine ⟨v, j.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, IsOpenImmersion.lift_fac]
    exact hv
  -- notation for the cover pieces and the B-side witnesses
  set ℓ : ∀ p : Q', Spec (CommRingCat.of (Localization.Away (a p))) ⟶ Q' :=
    fun p => IsOpenImmersion.lift j (chartA R (a p)) (hliftA p) with hℓdef
  have hℓj : ∀ p, ℓ p ≫ j = chartA R (a p) :=
    fun p => IsOpenImmersion.lift_fac _ _ _
  haveI hℓimm : ∀ p, IsOpenImmersion (ℓ p) := by
    intro p
    have : IsOpenImmersion (ℓ p ≫ j) := (hℓj p) ▸ inferInstance
    exact IsOpenImmersion.of_comp _ j
  have hrangeκB : ∀ p : Q', Set.range ⇑(chartB R (a p)) ⊆
      Set.range ⇑(pullback.fst (invariantsπ G B R) j) := by
    intro p t ht
    rw [IsOpenImmersion.range_pullbackFst]
    change invariantsπ G B R t ∈ j.opensRange
    obtain ⟨v, rfl⟩ := ht
    have h20 : invariantsπ G B R (chartB R (a p) v) =
        chartA R (a p) (chartπ R (a p) v) := by
      rw [← Scheme.Hom.comp_apply, chart_square G B R (a p), Scheme.Hom.comp_apply]
    rw [h20]
    exact hrange p (by
      have h21 : chartA R (a p) (chartπ R (a p) v) ∈
          (chartA R (a p)).opensRange := ⟨_, rfl⟩
      rwa [chartA_opensRange] at h21)
  set κB' : ∀ p : Q', Spec (CommRingCat.of (Localization.Away ((a p : B)))) ⟶
      pullback (invariantsπ G B R) j :=
    fun p => IsOpenImmersion.lift (pullback.fst (invariantsπ G B R) j)
      (chartB R (a p)) (hrangeκB p) with hκB'def
  have hκB'fst : ∀ p, κB' p ≫ pullback.fst (invariantsπ G B R) j =
      chartB R (a p) := fun p => IsOpenImmersion.lift_fac _ _ _
  have hκB'snd : ∀ p, κB' p ≫ pullback.snd (invariantsπ G B R) j =
      chartπ R (a p) ≫ ℓ p := by
    intro p
    rw [← cancel_mono j, Category.assoc, Category.assoc, hℓj p, ← pullback.condition,
      ← Category.assoc, hκB'fst, chart_square G B R (a p)]
  -- gluing compatibility on overlaps, via the relative uniqueness
  have hcompat : ∀ p r : Q', pullback.fst (ℓ p) (ℓ r) ≫ qa p =
      pullback.snd (ℓ p) (ℓ r) ≫ qa r := by
    intro p r
    obtain ⟨j'', hj''⟩ : ∃ j'', pullback.fst (ℓ p) (ℓ r) ≫ ℓ p ≫ j = j'' := ⟨_, rfl⟩
    haveI : IsOpenImmersion j'' := hj'' ▸ inferInstance
    refine invariantsπ_hom_ext_of_isOpenImmersion G B R j'' _ _ ?_
    obtain ⟨m₁, hm₁f, hm₁⟩ := relative_chart_descent_comparison G B R j f (a p) (qa p)
      (κB' p) (hκB'fst p) (hqa p (κB' p) (hκB'fst p)) (ℓ p) (hℓj p)
      j'' (pullback.fst (ℓ p) (ℓ r)) hj''
    obtain ⟨m₂, hm₂f, hm₂⟩ := relative_chart_descent_comparison G B R j f (a r) (qa r)
      (κB' r) (hκB'fst r) (hqa r (κB' r) (hκB'fst r)) (ℓ r) (hℓj r)
      j'' (pullback.snd (ℓ p) (ℓ r)) (by
        rw [← Category.assoc, ← pullback.condition, Category.assoc, hj''])
    have hmm : m₁ = m₂ := by
      rw [← cancel_mono (pullback.fst (invariantsπ G B R) j), hm₁f, hm₂f]
    rw [← Category.assoc, Category.assoc, hm₁, ← Category.assoc, Category.assoc,
      hm₂, hmm]
  -- glue and verify the factorization on the lifted `B`-side cover
  set 𝒰Q : Q'.OpenCover := Scheme.Cover.mkOfCovers (J := ↥Q')
    (fun p => Spec (CommRingCat.of (Localization.Away (a p))))
    (fun p => ℓ p)
    (fun x => ⟨x, hcoverQ' x⟩)
    (fun p => hℓimm p) with h𝒰Q
  refine ⟨𝒰Q.glueMorphisms (fun p => qa p) hcompat, ?_⟩
  haveI hκB'imm : ∀ p, IsOpenImmersion (κB' p) := by
    intro p
    have : IsOpenImmersion (κB' p ≫ pullback.fst (invariantsπ G B R) j) :=
      (hκB'fst p) ▸ inferInstance
    exact IsOpenImmersion.of_comp _ (pullback.fst (invariantsπ G B R) j)
  have hcoverPB : ∀ w : ↥(pullback (invariantsπ G B R) j),
      ∃ v, κB' (pullback.snd (invariantsπ G B R) j w) v = w := by
    intro w
    have h31 : invariantsπ G B R (pullback.fst (invariantsπ G B R) j w) =
        j (pullback.snd (invariantsπ G B R) j w) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    have h30 : pullback.fst (invariantsπ G B R) j w ∈
        (chartB R (a (pullback.snd (invariantsπ G B R) j w))).opensRange := by
      rw [chartB_opensRange]
      change invariantsπ G B R (pullback.fst (invariantsπ G B R) j w) ∈
        PrimeSpectrum.basicOpen (a (pullback.snd (invariantsπ G B R) j w))
      rw [h31]
      exact hmem _
    obtain ⟨v, hv⟩ := h30
    exact ⟨v, (pullback.fst (invariantsπ G B R) j).isOpenEmbedding.injective (by
      rw [← Scheme.Hom.comp_apply, hκB'fst, hv])⟩
  refine Scheme.Cover.hom_ext
    ((Scheme.Cover.mkOfCovers
      (J := ↥((pullback (invariantsπ G B R) j : Scheme.{u})))
      (fun w =>
        Spec (CommRingCat.of (Localization.Away
          ((a (pullback.snd (invariantsπ G B R) j w) : B)))))
      (fun w => κB' (pullback.snd (invariantsπ G B R) j w))
      (fun w => ⟨w, hcoverPB w⟩)
      (fun w => hκB'imm _) : (pullback (invariantsπ G B R) j).OpenCover))
    _ _ (fun w => ?_)
  have hfinal : ∀ p' : Q', κB' p' ≫ pullback.snd (invariantsπ G B R) j ≫
      𝒰Q.glueMorphisms (fun p => qa p) hcompat = κB' p' ≫ f := by
    intro p'
    rw [← Category.assoc, hκB'snd, Category.assoc]
    have h50 : ℓ p' ≫ 𝒰Q.glueMorphisms (fun p => qa p) hcompat = qa p' :=
      𝒰Q.ι_glueMorphisms (fun p => qa p) hcompat p'
    rw [h50]
    exact hqa _ (κB' _) (hκB'fst _)
  exact hfinal (pullback.snd (invariantsπ G B R) j
    (show ↥(pullback (invariantsπ G B R) j) from w))

variable (G B) in
omit [SMulCommClass G R B] in
/-- Geometric freeness of the `G`-action on `Spec B` — no `g ≠ 1` fixes a `T`-point over a
nonempty `T` — gives Katz–Mazur A7.1.1 freeness of the action on `B`. Bare-`Spec` version
of `SchemeAction.isFreeAlgebraAction_of_free` (which lives downstream, on
`SchemeQuotient`'s `SchemeAction`): a `g`-invariant `R`-algebra point `φ : B →ₐ[R] R'` is
exactly a `g`-fixed `Spec R'`-point of `Spec B`, and a nontrivial ring has a prime. -/
theorem isFreeAlgebraAction_of_specSMul_free
    (hfree : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of B)) (g : G), g ≠ 1 →
      t ≫ specSMul g = t → IsEmpty T) :
    IsFreeAlgebraAction G R B := by
  intro g hg R' _ _ _ φ
  by_contra hcon
  push Not at hcon
  have hring : CommRingCat.ofHom (MulSemiringAction.toRingHom G B g) ≫
      CommRingCat.ofHom φ.toRingHom = CommRingCat.ofHom φ.toRingHom := by
    ext a
    exact hcon a
  have hspec : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ specSMul g =
      Spec.map (CommRingCat.ofHom φ.toRingHom) := by
    rw [specSMul, ← Spec.map_comp, hring]
  haveI hE : IsEmpty (Spec (CommRingCat.of R')) :=
    hfree (Spec.map (CommRingCat.ofHom φ.toRingHom)) g hg hspec
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum R') := inferInstance
  exact hE.false p

variable (G B) in
/-- For a **free** action the invariants morphism is finite flat surjective, so its base
change along ANY morphism is an epimorphism of schemes — uniqueness of descent over an
arbitrary base. (For non-free actions this fails: `invariantsπ` need not be flat.) -/
theorem epi_pullback_snd_invariantsπ_of_free [Finite G]
    (halg : IsFreeAlgebraAction G R B) {Q' : Scheme.{u}}
    (j : Q' ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G))) :
    Epi (pullback.snd (invariantsπ G B R) j) := by
  haveI : SMulCommClass R G B := SMulCommClass.symm G R B
  haveI : Module.Finite (FixedPoints.subalgebra R B G) B :=
    Module.Finite.of_isFreeAlgebraAction G R B halg
  haveI : Module.Projective (FixedPoints.subalgebra R B G) B :=
    Module.Projective.of_isFreeAlgebraAction G R B halg
  haveI : Module.Flat (FixedPoints.subalgebra R B G) B := Module.Flat.of_projective
  haveI : Flat (invariantsπ G B R) := by
    rw [invariantsπ, AlgebraicGeometry.Flat.SpecMap_iff, CommRingCat.hom_ofHom,
      RingHom.flat_algebraMap_iff]
    infer_instance
  haveI : Surjective (invariantsπ G B R) := ⟨invariantsπ_surjective G B R⟩
  haveI : Surjective (pullback.snd (invariantsπ G B R) j) :=
    MorphismProperty.pullback_snd _ _ ‹Surjective (invariantsπ G B R)›
  exact Flat.epi_of_flat_of_surjective _

variable (G B) in
/-- The comparison morphism between base changes of `invariantsπ`: for `u : W' ⟶ W''`
over `Spec Bᴳ` — i.e. `w = u ≫ j''` — the induced morphism
`pullback π w ⟶ pullback π j''`. Bundled as a definition so the gluing bookkeeping
rewrites cleanly. -/
private noncomputable def pullbackRes {W' W'' : Scheme.{u}}
    (j'' : W'' ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G)))
    (w : W' ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G)))
    (u : W' ⟶ W'') (hw : w = u ≫ j'') :
    pullback (invariantsπ G B R) w ⟶ pullback (invariantsπ G B R) j'' :=
  pullback.map _ _ _ _ (𝟙 _) u (𝟙 _) (by simp) (by rw [Category.comp_id, hw])

variable (G B) in
@[reassoc]
private theorem pullbackRes_fst {W' W'' : Scheme.{u}}
    (j'' : W'' ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G)))
    (w : W' ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G)))
    (u : W' ⟶ W'') (hw : w = u ≫ j'') :
    pullbackRes G B R j'' w u hw ≫ pullback.fst (invariantsπ G B R) j'' =
      pullback.fst (invariantsπ G B R) w :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

variable (G B) in
@[reassoc]
private theorem pullbackRes_snd {W' W'' : Scheme.{u}}
    (j'' : W'' ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G)))
    (w : W' ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G)))
    (u : W' ⟶ W'') (hw : w = u ≫ j'') :
    pullbackRes G B R j'' w u hw ≫ pullback.snd (invariantsπ G B R) j'' =
      pullback.snd (invariantsπ G B R) w ≫ u :=
  pullback.lift_snd _ _ _

variable (G B) in
/-- The comparison morphisms intertwine the relative actions: `pullbackSpecSMul` is
natural in the base. -/
private theorem pullbackSpecSMul_pullbackRes {W' W'' : Scheme.{u}}
    (j'' : W'' ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G)))
    (w : W' ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G)))
    (u : W' ⟶ W'') (hw : w = u ≫ j'') (g : G) :
    pullbackSpecSMul G B R w g ≫ pullbackRes G B R j'' w u hw =
      pullbackRes G B R j'' w u hw ≫ pullbackSpecSMul G B R j'' g := by
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, pullbackRes_fst, pullbackRes_fst_assoc,
      pullbackSpecSMul_fst]
  · simp only [Category.assoc, pullbackRes_snd, pullbackSpecSMul_snd,
      pullbackSpecSMul_snd_assoc]

variable (G B) in
/-- **The chart engine of free-action base change** (KM 7.1.3(3c) over an affine base):
for the base change of `invariantsπ` along `Spec ψ` with `ψ : Bᴳ →+* C` ARBITRARY, every
invariant morphism out of the base-changed total space descends to `Spec C`.

Route: the base-changed total space is `Spec (B ⊗[Bᴳ] C)` (`pullbackSpecIso`), the
base-changed action is the tensor action through the left factor, the base-changed
projection is the invariants morphism of that action (`exists_invariantsπ_lift` applies),
and its target `Spec ((B ⊗[Bᴳ] C)ᴳ)` is `Spec C` itself by
`bijective_includeRightFixedPoints` — the point where freeness enters ([A711-BC] at
ground `Bᴳ`). -/
private theorem exists_invariantsπ_lift_baseChange_spec [Finite G] {Y : Scheme.{u}}
    (halg : IsFreeAlgebraAction G R B) (C : Type u) [CommRing C]
    (ψ : FixedPoints.subalgebra R B G →+* C)
    (f : pullback (invariantsπ G B R) (Spec.map (CommRingCat.ofHom ψ)) ⟶ Y)
    (hf : ∀ g : G, pullbackSpecSMul G B R (Spec.map (CommRingCat.ofHom ψ)) g ≫ f = f) :
    ∃ q : Spec (CommRingCat.of C) ⟶ Y,
      pullback.snd (invariantsπ G B R) (Spec.map (CommRingCat.ofHom ψ)) ≫ q = f := by
  classical
  haveI : SMulCommClass R G B := SMulCommClass.symm G R B
  letI : Algebra ↥(FixedPoints.subalgebra R B G) C := ψ.toAlgebra
  -- the affine identification of the base-changed total space, retyped at `invariantsπ`
  set e : pullback (invariantsπ G B R) (Spec.map (CommRingCat.ofHom ψ)) ≅
      Spec (CommRingCat.of (B ⊗[↥(FixedPoints.subalgebra R B G)] C)) :=
    pullbackSpecIso ↥(FixedPoints.subalgebra R B G) B C with he
  have hefst : e.inv ≫
      pullback.fst (invariantsπ G B R) (Spec.map (CommRingCat.ofHom ψ)) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := ↥(FixedPoints.subalgebra R B G)) (A := B) (B := C))) := by
    rw [he]
    exact pullbackSpecIso_inv_fst ↥(FixedPoints.subalgebra R B G) B C
  have hesnd : e.inv ≫
      pullback.snd (invariantsπ G B R) (Spec.map (CommRingCat.ofHom ψ)) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := ↥(FixedPoints.subalgebra R B G)) (A := B) (B := C)).toRingHom) := by
    rw [he]
    exact pullbackSpecIso_inv_snd ↥(FixedPoints.subalgebra R B G) B C
  -- the identification intertwines the tensor action with the relative action
  have hact : ∀ g : G,
      e.inv ≫ pullbackSpecSMul G B R (Spec.map (CommRingCat.ofHom ψ)) g =
      specSMul g ≫ e.inv := by
    intro g
    have hsqL : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := ↥(FixedPoints.subalgebra R B G)) (A := B) (B := C))) ≫ specSMul g =
        specSMul g ≫ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom
            (R := ↥(FixedPoints.subalgebra R B G)) (A := B) (B := C))) := by
      rw [specSMul, specSMul, ← Spec.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
    have hsqR : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := ↥(FixedPoints.subalgebra R B G)) (A := B) (B := C)).toRingHom) =
        specSMul g ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := ↥(FixedPoints.subalgebra R B G)) (A := B) (B := C)).toRingHom) := by
      rw [specSMul, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext c
      change (1 : B) ⊗ₜ[↥(FixedPoints.subalgebra R B G)] c =
        g • ((1 : B) ⊗ₜ[↥(FixedPoints.subalgebra R B G)] c)
      rw [MulSemiringAction.smul_tmul_baseChange, smul_one]
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullbackSpecSMul_fst]
      rw [← Category.assoc, hefst]
      exact hsqL
    · simp only [Category.assoc, pullbackSpecSMul_snd]
      rw [hesnd]
      exact hsqR
  -- the descended morphism on `Spec (B ⊗ C)` is invariant for the tensor action
  have hf' : ∀ g : G, specSMul g ≫ (e.inv ≫ f) = e.inv ≫ f := by
    intro g
    rw [← Category.assoc, ← hact g, Category.assoc, hf g]
  -- descend through the invariants morphism of the tensor action
  obtain ⟨q₀, hq₀⟩ := exists_invariantsπ_lift G
    (B ⊗[↥(FixedPoints.subalgebra R B G)] C) ↥(FixedPoints.subalgebra R B G)
    (e.inv ≫ f) hf'
  -- identify the invariants of the tensor with `C` (freeness enters here)
  set χe : C ≃+* FixedPoints.subalgebra ↥(FixedPoints.subalgebra R B G)
      (B ⊗[↥(FixedPoints.subalgebra R B G)] C) G :=
    RingEquiv.ofBijective _ (bijective_includeRightFixedPoints halg C) with hχe
  refine ⟨Spec.map (CommRingCat.ofHom (χe.symm : _ →+* C)) ≫ q₀, ?_⟩
  rw [← cancel_epi e.inv, ← Category.assoc, hesnd, ← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  have hkey : CommRingCat.ofHom
      ((Algebra.TensorProduct.includeRight
        (R := ↥(FixedPoints.subalgebra R B G)) (A := B) (B := C)).toRingHom.comp
          (χe.symm : _ →+* C)) =
      CommRingCat.ofHom (algebraMap
        (FixedPoints.subalgebra ↥(FixedPoints.subalgebra R B G)
          (B ⊗[↥(FixedPoints.subalgebra R B G)] C) G)
        (B ⊗[↥(FixedPoints.subalgebra R B G)] C)) := by
    congr 1
    ext x
    change (1 : B) ⊗ₜ[↥(FixedPoints.subalgebra R B G)] (χe.symm x : C) = (x :
      B ⊗[↥(FixedPoints.subalgebra R B G)] C)
    rw [← includeRightFixedPoints_coe (G := G) (R := R) (A := B) C (χe.symm x)]
    exact congrArg Subtype.val (χe.apply_symm_apply x)
  rw [hkey]
  exact hq₀

variable (G B) in
/-- The chart engine over an abstract affine base: descent of invariant morphisms along
the base change of `invariantsπ` to ANY affine scheme over `Spec Bᴳ`. Reduction of
`exists_invariantsπ_lift_baseChange_spec` along `W.isoSpec`. -/
private theorem exists_invariantsπ_lift_baseChange_of_isAffine [Finite G]
    {W Y : Scheme.{u}} [IsAffine W] (halg : IsFreeAlgebraAction G R B)
    (w : W ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G)))
    (f : pullback (invariantsπ G B R) w ⟶ Y)
    (hf : ∀ g : G, pullbackSpecSMul G B R w g ≫ f = f) :
    ∃ q : W ⟶ Y, pullback.snd (invariantsπ G B R) w ≫ q = f := by
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (W.isoSpec.inv ≫ w)
  -- the comparison iso between the two base changes
  haveI : IsIso (pullbackRes G B R w (Spec.map ψ) W.isoSpec.inv hψ) := by
    unfold pullbackRes
    infer_instance
  -- transport the invariance and descend on the `Spec` model
  have hfρ : ∀ g : G, pullbackSpecSMul G B R (Spec.map ψ) g ≫
      (pullbackRes G B R w (Spec.map ψ) W.isoSpec.inv hψ ≫ f) =
      pullbackRes G B R w (Spec.map ψ) W.isoSpec.inv hψ ≫ f := by
    intro g
    rw [← Category.assoc, pullbackSpecSMul_pullbackRes, Category.assoc, hf g]
  obtain ⟨q₀, hq₀⟩ := exists_invariantsπ_lift_baseChange_spec G B R halg _ ψ.hom
    (pullbackRes G B R w (Spec.map ψ) W.isoSpec.inv hψ ≫ f) hfρ
  refine ⟨W.isoSpec.hom ≫ q₀, ?_⟩
  rw [← cancel_epi (pullbackRes G B R w (Spec.map ψ) W.isoSpec.inv hψ), ← Category.assoc,
    pullbackRes_snd, Category.assoc, Iso.inv_hom_id_assoc]
  exact hq₀

variable (G B) in
/-- **[GHB5a-i] Free-action affine base change of the quotient** (KM 7.1.3(3c),
condition (c); the per-chart engine of `SchemeAction.exists_quotientπ_lift_baseChange`).
For a FREE `G`-action on `Spec B` and an ARBITRARY base map `j : Q' ⟶ Spec Bᴳ`, every
`f : pullback (invariantsπ) j ⟶ Y` invariant under `pullbackSpecSMul` descends to `Q'`.

Unlike `exists_invariantsπ_lift_of_isOpenImmersion` — which needs `j` an open immersion,
so the base change is a (flat) localization — the free action makes `(B ⊗_{Bᴳ} C)ᴳ = C`
hold for EVERY `Bᴳ`-algebra `C`: this is [A711-BC]
`InvariantTorsor.fixedPointsBaseChange_bijective_of_isFreeAlgebraAction` instantiated at
ground `Bᴳ` (with `A := B`, `FixedPoints.subalgebra Bᴳ B G = Bᴳ`, so
`(B ⊗_{Bᴳ} C)ᴳ = Bᴳ ⊗_{Bᴳ} C = C`). Freeness is given in the scheme form (`IsEmpty` of
fixed-point loci, matching `SchemeAction`'s convention); the proof converts it to
`IsFreeAlgebraAction G Bᴳ B` (restriction of the ground-`R` freeness). -/
theorem exists_invariantsπ_lift_baseChange_of_free [Finite G] {Q' Y : Scheme.{u}}
    (hfree : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of B)) (g : G), g ≠ 1 →
      t ≫ specSMul g = t → IsEmpty T)
    (j : Q' ⟶ Spec (CommRingCat.of (FixedPoints.subalgebra R B G)))
    (f : Limits.pullback (invariantsπ G B R) j ⟶ Y)
    (hf : ∀ g : G, pullbackSpecSMul G B R j g ≫ f = f) :
    ∃ q : Q' ⟶ Y, Limits.pullback.snd (invariantsπ G B R) j ≫ q = f := by
  classical
  have halg : IsFreeAlgebraAction G R B := isFreeAlgebraAction_of_specSMul_free G B R hfree
  -- chart-wise descents of the restricted morphisms
  have hfx : ∀ (x : Q'.affineCover.I₀) (g : G),
      pullbackSpecSMul G B R (Q'.affineCover.f x ≫ j) g ≫
        (pullbackRes G B R j (Q'.affineCover.f x ≫ j) (Q'.affineCover.f x) rfl ≫ f) =
      pullbackRes G B R j (Q'.affineCover.f x ≫ j) (Q'.affineCover.f x) rfl ≫ f := by
    intro x g
    rw [← Category.assoc, pullbackSpecSMul_pullbackRes, Category.assoc, hf g]
  choose qx hqx using fun x : Q'.affineCover.I₀ =>
    exists_invariantsπ_lift_baseChange_of_isAffine G B R halg (Q'.affineCover.f x ≫ j)
      (pullbackRes G B R j (Q'.affineCover.f x ≫ j) (Q'.affineCover.f x) rfl ≫ f) (hfx x)
  -- gluing compatibility on overlaps, by cancelling the (epi) base-changed projection
  have hcompat : ∀ x z : Q'.affineCover.I₀,
      pullback.fst (Q'.affineCover.f x) (Q'.affineCover.f z) ≫ qx x =
      pullback.snd (Q'.affineCover.f x) (Q'.affineCover.f z) ≫ qx z := by
    intro x z
    have hbase : pullback.fst (Q'.affineCover.f x) (Q'.affineCover.f z) ≫
        Q'.affineCover.f x ≫ j =
        pullback.snd (Q'.affineCover.f x) (Q'.affineCover.f z) ≫ Q'.affineCover.f z ≫ j := by
      rw [← Category.assoc, ← Category.assoc, pullback.condition]
    have hσρ : pullbackRes G B R (Q'.affineCover.f x ≫ j)
          (pullback.fst (Q'.affineCover.f x) (Q'.affineCover.f z) ≫ Q'.affineCover.f x ≫ j)
          (pullback.fst (Q'.affineCover.f x) (Q'.affineCover.f z)) rfl ≫
          pullbackRes G B R j (Q'.affineCover.f x ≫ j) (Q'.affineCover.f x) rfl =
        pullbackRes G B R (Q'.affineCover.f z ≫ j)
          (pullback.fst (Q'.affineCover.f x) (Q'.affineCover.f z) ≫ Q'.affineCover.f x ≫ j)
          (pullback.snd (Q'.affineCover.f x) (Q'.affineCover.f z)) hbase ≫
          pullbackRes G B R j (Q'.affineCover.f z ≫ j) (Q'.affineCover.f z) rfl := by
      refine pullback.hom_ext ?_ ?_
      · simp only [Category.assoc, pullbackRes_fst]
      · simp only [Category.assoc, pullbackRes_snd, pullbackRes_snd_assoc]
        rw [pullback.condition]
    haveI := epi_pullback_snd_invariantsπ_of_free G B R halg
      (pullback.fst (Q'.affineCover.f x) (Q'.affineCover.f z) ≫ Q'.affineCover.f x ≫ j)
    refine (cancel_epi (pullback.snd (invariantsπ G B R)
      (pullback.fst (Q'.affineCover.f x) (Q'.affineCover.f z) ≫
        Q'.affineCover.f x ≫ j))).mp ?_
    calc pullback.snd (invariantsπ G B R)
          (pullback.fst (Q'.affineCover.f x) (Q'.affineCover.f z) ≫
            Q'.affineCover.f x ≫ j) ≫
          pullback.fst (Q'.affineCover.f x) (Q'.affineCover.f z) ≫ qx x
        = (pullback.snd (invariantsπ G B R)
            (pullback.fst (Q'.affineCover.f x) (Q'.affineCover.f z) ≫
              Q'.affineCover.f x ≫ j) ≫
            pullback.fst (Q'.affineCover.f x) (Q'.affineCover.f z)) ≫ qx x :=
          (Category.assoc _ _ _).symm
      _ = (pullbackRes G B R (Q'.affineCover.f x ≫ j)
            (pullback.fst (Q'.affineCover.f x) (Q'.affineCover.f z) ≫
              Q'.affineCover.f x ≫ j)
            (pullback.fst (Q'.affineCover.f x) (Q'.affineCover.f z)) rfl ≫
            pullback.snd (invariantsπ G B R) (Q'.affineCover.f x ≫ j)) ≫ qx x := by
          rw [pullbackRes_snd]
      _ = pullbackRes G B R (Q'.affineCover.f x ≫ j)
            (pullback.fst (Q'.affineCover.f x) (Q'.affineCover.f z) ≫
              Q'.affineCover.f x ≫ j)
            (pullback.fst (Q'.affineCover.f x) (Q'.affineCover.f z)) rfl ≫
            pullback.snd (invariantsπ G B R) (Q'.affineCover.f x ≫ j) ≫ qx x :=
          Category.assoc _ _ _
      _ = pullbackRes G B R (Q'.affineCover.f x ≫ j)
            (pullback.fst (Q'.affineCover.f x) (Q'.affineCover.f z) ≫
              Q'.affineCover.f x ≫ j)
            (pullback.fst (Q'.affineCover.f x) (Q'.affineCover.f z)) rfl ≫
            pullbackRes G B R j (Q'.affineCover.f x ≫ j) (Q'.affineCover.f x) rfl ≫ f := by
          rw [hqx x]
      _ = (pullbackRes G B R (Q'.affineCover.f x ≫ j)
            (pullback.fst (Q'.affineCover.f x) (Q'.affineCover.f z) ≫
              Q'.affineCover.f x ≫ j)
            (pullback.fst (Q'.affineCover.f x) (Q'.affineCover.f z)) rfl ≫
            pullbackRes G B R j (Q'.affineCover.f x ≫ j) (Q'.affineCover.f x) rfl) ≫ f :=
          (Category.assoc _ _ _).symm
      _ = (pullbackRes G B R (Q'.affineCover.f z ≫ j)
            (pullback.fst (Q'.affineCover.f x) (Q'.affineCover.f z) ≫
              Q'.affineCover.f x ≫ j)
            (pullback.snd (Q'.affineCover.f x) (Q'.affineCover.f z)) hbase ≫
            pullbackRes G B R j (Q'.affineCover.f z ≫ j) (Q'.affineCover.f z) rfl) ≫ f := by
          rw [hσρ]
      _ = pullbackRes G B R (Q'.affineCover.f z ≫ j)
            (pullback.fst (Q'.affineCover.f x) (Q'.affineCover.f z) ≫
              Q'.affineCover.f x ≫ j)
            (pullback.snd (Q'.affineCover.f x) (Q'.affineCover.f z)) hbase ≫
            pullbackRes G B R j (Q'.affineCover.f z ≫ j) (Q'.affineCover.f z) rfl ≫ f :=
          Category.assoc _ _ _
      _ = pullbackRes G B R (Q'.affineCover.f z ≫ j)
            (pullback.fst (Q'.affineCover.f x) (Q'.affineCover.f z) ≫
              Q'.affineCover.f x ≫ j)
            (pullback.snd (Q'.affineCover.f x) (Q'.affineCover.f z)) hbase ≫
            pullback.snd (invariantsπ G B R) (Q'.affineCover.f z ≫ j) ≫ qx z := by
          rw [← hqx z]
      _ = (pullbackRes G B R (Q'.affineCover.f z ≫ j)
            (pullback.fst (Q'.affineCover.f x) (Q'.affineCover.f z) ≫
              Q'.affineCover.f x ≫ j)
            (pullback.snd (Q'.affineCover.f x) (Q'.affineCover.f z)) hbase ≫
            pullback.snd (invariantsπ G B R) (Q'.affineCover.f z ≫ j)) ≫ qx z :=
          (Category.assoc _ _ _).symm
      _ = (pullback.snd (invariantsπ G B R)
            (pullback.fst (Q'.affineCover.f x) (Q'.affineCover.f z) ≫
              Q'.affineCover.f x ≫ j) ≫
            pullback.snd (Q'.affineCover.f x) (Q'.affineCover.f z)) ≫ qx z := by
          rw [pullbackRes_snd]
      _ = pullback.snd (invariantsπ G B R)
            (pullback.fst (Q'.affineCover.f x) (Q'.affineCover.f z) ≫
              Q'.affineCover.f x ≫ j) ≫
            pullback.snd (Q'.affineCover.f x) (Q'.affineCover.f z) ≫ qx z :=
          Category.assoc _ _ _
  refine ⟨Q'.affineCover.glueMorphisms qx hcompat, ?_⟩
  -- verify the factorization on the pullback cover of the global base change
  refine Scheme.Cover.hom_ext
    (Q'.affineCover.pullback₁ (pullback.snd (invariantsπ G B R) j)) _ _ fun x => ?_
  change pullback.fst (pullback.snd (invariantsπ G B R) j) (Q'.affineCover.f x) ≫
      pullback.snd (invariantsπ G B R) j ≫ Q'.affineCover.glueMorphisms qx hcompat =
    pullback.fst (pullback.snd (invariantsπ G B R) j) (Q'.affineCover.f x) ≫ f
  have hcond : pullback.fst (pullback.snd (invariantsπ G B R) j) (Q'.affineCover.f x) ≫
      pullback.snd (invariantsπ G B R) j =
      pullback.snd (pullback.snd (invariantsπ G B R) j) (Q'.affineCover.f x) ≫
        Q'.affineCover.f x :=
    pullback.condition
  rw [← Category.assoc, hcond, Category.assoc,
    Q'.affineCover.ι_glueMorphisms qx hcompat x]
  -- compare through the canonical map into the chart base change
  set θ : pullback (pullback.snd (invariantsπ G B R) j) (Q'.affineCover.f x) ⟶
      pullback (invariantsπ G B R) (Q'.affineCover.f x ≫ j) :=
    pullback.lift
      (pullback.fst (pullback.snd (invariantsπ G B R) j) (Q'.affineCover.f x) ≫
        pullback.fst (invariantsπ G B R) j)
      (pullback.snd (pullback.snd (invariantsπ G B R) j) (Q'.affineCover.f x))
      (by
        rw [Category.assoc, pullback.condition (f := invariantsπ G B R) (g := j),
          ← Category.assoc, hcond, Category.assoc])
      with hθ
  have hθsnd : θ ≫ pullback.snd (invariantsπ G B R) (Q'.affineCover.f x ≫ j) =
      pullback.snd (pullback.snd (invariantsπ G B R) j) (Q'.affineCover.f x) := by
    rw [hθ]
    exact pullback.lift_snd _ _ _
  have hθρ : θ ≫ pullbackRes G B R j (Q'.affineCover.f x ≫ j) (Q'.affineCover.f x) rfl =
      pullback.fst (pullback.snd (invariantsπ G B R) j) (Q'.affineCover.f x) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullbackRes_fst, hθ, pullback.lift_fst]
    · rw [Category.assoc, pullbackRes_snd, ← Category.assoc, hθsnd, hcond]
  rw [← hθsnd, Category.assoc, hqx x, ← Category.assoc, hθρ]

end UniversalProperty
end AlgebraicGeometry

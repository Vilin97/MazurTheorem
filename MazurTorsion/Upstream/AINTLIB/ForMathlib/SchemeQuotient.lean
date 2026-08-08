/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Ticket T-Q5 (leaf T-Q5a).
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.AffineQuotient
import MazurTorsion.Upstream.AINTLIB.ForMathlib.BaseChangeAlongCompat

/-!
# Group actions on schemes: vocabulary for the quotient construction

A `G`-action on a scheme `X` is recorded as a bare family `σ : G → (X ⟶ X)` with
the covariant composition laws (`SchemeAction`), matching the convention of
`AlgebraicGeometry.specSMul`. This file provides:

* `SchemeAction` — the two-law action structure, with `IsIso (σ.hom g)`;
* `SchemeAction.spec` — the tautological action on `Spec B` by `specSMul`;
* `SchemeAction.IsStableOpen` — `G`-stable opens (`(σ.hom g) ⁻¹ᵁ U = U`);
* `SchemeAction.gammaMulSemiringAction` — the induced ring action on the sections
  `Γ(X, U)` over a stable open, via `Scheme.Hom.appLE` (T-Q5a's Γ-bridge: over a
  stable *affine* open this reconnects to the affine quotient theory of
  `SpecGroupAction.lean`/`AffineQuotient.lean`).

This is the vocabulary layer of the quotient of a scheme by a finite group
([Loeffler, *Modular curves*, Prop 3.6.1]; the gluing itself is tickets T-Q5b–d).
-/

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

variable (G : Type*) [Group G]

/-- An action of a group `G` on a scheme `X`, as a family of endomorphisms with the
covariant composition laws (each `hom g` is automatically an isomorphism,
`SchemeAction.isIso_hom`). The composition convention matches `specSMul`:
`hom (g * h) = hom g ≫ hom h`. -/
structure SchemeAction (X : Scheme.{u}) where
  /-- The endomorphism attached to `g`. -/
  hom : G → (X ⟶ X)
  hom_one : hom 1 = 𝟙 X
  hom_mul : ∀ g h : G, hom (g * h) = hom g ≫ hom h

namespace SchemeAction

variable {G}

/-- The scheme action packaged from a group homomorphism into `Aut X`, taking
`g` to `(ψ g).inv` (the inversion converts `Aut`'s reversed composition into the
covariant `hom (g * h) = hom g ≫ hom h` convention). -/
def ofAut {X : Scheme.{u}} (ψ : G →* Aut X) : SchemeAction G X where
  hom g := (ψ g).inv
  hom_one := by rw [map_one]; rfl
  hom_mul g h := by rw [map_mul]; rfl

@[simp]
theorem ofAut_hom {X : Scheme.{u}} (ψ : G →* Aut X) (g : G) :
    (ofAut ψ).hom g = (ψ g).inv := rfl
variable {X : Scheme.{u}} (σ : SchemeAction G X)

instance isIso_hom (g : G) : IsIso (σ.hom g) :=
  ⟨σ.hom g⁻¹, by rw [← σ.hom_mul, mul_inv_cancel, σ.hom_one],
    by rw [← σ.hom_mul, inv_mul_cancel, σ.hom_one]⟩

variable (G) in
/-- The tautological action on `Spec B` induced by a ring action (`specSMul`). -/
noncomputable def spec (B : Type u) [CommRing B] [MulSemiringAction G B] :
    SchemeAction G (Spec (CommRingCat.of B)) where
  hom g := specSMul g
  hom_one := specSMul_one
  hom_mul := specSMul_mul

@[simp]
theorem spec_hom (B : Type u) [CommRing B] [MulSemiringAction G B] (g : G) :
    (spec G B).hom g = specSMul g := rfl

/-- A `G`-stable open of `X`: each `σ g` restricts to it. -/
def IsStableOpen (U : X.Opens) : Prop :=
  ∀ g : G, (σ.hom g) ⁻¹ᵁ U = U

theorem IsStableOpen.le_preimage {σ : SchemeAction G X} {U : X.Opens}
    (hU : σ.IsStableOpen U) (g : G) : U ≤ (σ.hom g) ⁻¹ᵁ U :=
  (hU g).ge

/-- Transport an action along an isomorphism `e : Y ≅ Z` by conjugation. Used to move the induced
action on a Weierstrass chart (`pullbackChartAction`) onto the projective model `projModel W`
through the local-model iso. -/
noncomputable def transport {Y Z : Scheme.{u}} (α : SchemeAction G Y) (e : Y ≅ Z) :
    SchemeAction G Z where
  hom g := e.inv ≫ α.hom g ≫ e.hom
  hom_one := by rw [α.hom_one, Category.id_comp, e.inv_hom_id]
  hom_mul g h := by rw [α.hom_mul]; simp only [Category.assoc, Iso.hom_inv_id_assoc]

@[simp] theorem transport_hom {Y Z : Scheme.{u}} (α : SchemeAction G Y) (e : Y ≅ Z) (g : G) :
    (α.transport e).hom g = e.inv ≫ α.hom g ≫ e.hom := rfl

/-- Restrict an action to a stable open, as an action on the open subscheme `U.toScheme`;
`hom g` is `(σ.hom g)` restricted via `resLE`. -/
noncomputable def restrict {U : X.Opens} (hU : σ.IsStableOpen U) : SchemeAction G U.toScheme where
  hom g := (σ.hom g).resLE U U (hU.le_preimage g)
  hom_one := by
    rw [← cancel_mono U.ι, Scheme.Hom.resLE_comp_ι, σ.hom_one, Category.comp_id, Category.id_comp]
  hom_mul g h := by
    rw [← cancel_mono U.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι,
      ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, σ.hom_mul]

@[simp] theorem restrict_hom {U : X.Opens} (hU : σ.IsStableOpen U) (g : G) :
    (σ.restrict hU).hom g = (σ.hom g).resLE U U (hU.le_preimage g) := rfl

/-- The action induced on the base-open chart `pullback π U.ι` of a curve `π : E ⟶ X`, from a
`π`-equivariant `G`-action (`σE` on `E` covering `σ` on `X`), via `pullback.map`. This is the raw
action whose transport onto `projModel W` (`transport` through the local-model iso) feeds the
`VariableChange` cocycle (`isVCocycle_of_curveActionFamily`). -/
noncomputable def pullbackChartAction {E : Scheme.{u}} (σE : SchemeAction G E) {π : E ⟶ X}
    (hπ : ∀ g, σE.hom g ≫ π = π ≫ σ.hom g) {U : X.Opens} (hU : σ.IsStableOpen U) :
    SchemeAction G (Limits.pullback π U.ι) where
  hom g := Limits.pullback.map π U.ι π U.ι (σE.hom g) ((σ.hom g).resLE U U (hU.le_preimage g))
    (σ.hom g) (hπ g).symm (Scheme.Hom.resLE_comp_ι ..).symm
  hom_one := by
    apply Limits.pullback.hom_ext
    · rw [Limits.pullback.lift_fst, σE.hom_one, Category.comp_id, Category.id_comp]
    · rw [Limits.pullback.lift_snd, Category.id_comp, ← cancel_mono U.ι, Category.assoc,
        Scheme.Hom.resLE_comp_ι, σ.hom_one, Category.comp_id]
  hom_mul g h := by
    apply Limits.pullback.hom_ext
    · rw [Limits.pullback.lift_fst, Category.assoc, Limits.pullback.lift_fst, ← Category.assoc,
        Limits.pullback.lift_fst, Category.assoc, σE.hom_mul]
    · rw [Limits.pullback.lift_snd, Category.assoc, Limits.pullback.lift_snd, ← Category.assoc,
        Limits.pullback.lift_snd, ← cancel_mono U.ι]
      simp only [Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc, σ.hom_mul]

/-- The induced action on the sections over a `G`-stable open, through
`Scheme.Hom.appLE` (no `eqToHom` transport). Over a stable *affine* open this is
the bridge back to the affine quotient theory. Not an instance (it depends on the
stability hypothesis): bring it into scope with `letI`. -/
@[implicit_reducible]
noncomputable def gammaMulSemiringAction {U : X.Opens} (hU : σ.IsStableOpen U) :
    MulSemiringAction G ↑Γ(X, U) where
  smul g s := ((σ.hom g).appLE U U (hU.le_preimage g)).hom s
  one_smul s := by
    show ((σ.hom 1).appLE U U (hU.le_preimage 1)).hom s = s
    simp only [σ.hom_one]
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
    have h1 : (homOfLE (show U ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ U from σ.hom_one ▸
        hU.le_preimage 1)).op = 𝟙 (Opposite.op U) := rfl
    rw [h1]
    erw [X.presheaf.map_id]
    rfl
  mul_smul g h s := by
    show ((σ.hom (g * h)).appLE U U (hU.le_preimage (g * h))).hom s =
      ((σ.hom g).appLE U U (hU.le_preimage g)).hom
        (((σ.hom h).appLE U U (hU.le_preimage h)).hom s)
    simp only [σ.hom_mul]
    rw [← Scheme.Hom.appLE_comp_appLE (σ.hom g) (σ.hom h) U U U
      (hU.le_preimage h) (hU.le_preimage g)]
    rfl
  smul_zero g := map_zero _
  smul_add g := map_add _
  smul_one g := map_one _
  smul_mul g := map_mul _

@[simp]
theorem gammaMulSemiringAction_smul_def {U : X.Opens} (hU : σ.IsStableOpen U)
    (g : G) (s : ↑Γ(X, U)) :
    (gammaMulSemiringAction σ hU).smul g s =
      ((σ.hom g).appLE U U (hU.le_preimage g)).hom s := rfl

/-- **Stable-affine refinement** (T-Q5b): if the `σ`-orbit of a point lies in an
affine open of a scheme with affine diagonal (e.g. any separated scheme), then the
point has a `G`-stable affine open neighbourhood, namely `⨅ g, (σ.hom g) ⁻¹ᵁ U`.
This is where "quasi-projective and `G` finite" enters Loeffler's Prop 3.6.1: quasi-
projectivity guarantees the orbit-in-affine hypothesis, and finiteness keeps the
refinement open and affine. -/
theorem exists_isStableOpen_isAffineOpen [Finite G]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    {U : X.Opens} (hU : IsAffineOpen U)
    (x : X) (horbit : ∀ g : G, σ.hom g x ∈ U) :
    ∃ V : X.Opens, σ.IsStableOpen V ∧ IsAffineOpen V ∧ x ∈ V := by
  refine ⟨⨅ g : G, (σ.hom g) ⁻¹ᵁ U, ?_, ?_, ?_⟩
  · intro g
    have hcoe : ∀ (f : X ⟶ X) (V : X.Opens), (↑(f ⁻¹ᵁ V) : Set X) = ⇑f.base ⁻¹' ↑V :=
      fun f V => rfl
    refine TopologicalSpace.Opens.ext ?_
    rw [hcoe, TopologicalSpace.Opens.coe_iInf, Set.preimage_iInter]
    have h1 : ∀ h : G, ⇑(σ.hom g).base ⁻¹' (↑(σ.hom h ⁻¹ᵁ U) : Set X) =
        ↑(σ.hom (g * h) ⁻¹ᵁ U) := by
      intro h
      rw [hcoe, hcoe, ← Set.preimage_comp]
      congr 1
      rw [σ.hom_mul]
      rfl
    rw [Set.iInter_congr h1]
    exact (Equiv.mulLeft g).surjective.iInter_comp
      (fun k => (↑(σ.hom k ⁻¹ᵁ U) : Set X))
  · exact IsAffineOpen.iInf (fun g => hU.preimage_of_isIso (σ.hom g))
  · show x ∈ (↑(⨅ g : G, (σ.hom g) ⁻¹ᵁ U) : Set X)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr (fun g => horbit g)

/-- The local quotient of a `G`-stable affine open: `Spec (Γ(X, V)ᴳ)` (T-Q5c,
local piece). -/
@[reducible]
noncomputable def localQuotient {V : X.Opens} (hV : σ.IsStableOpen V) : Scheme.{u} :=
  letI := σ.gammaMulSemiringAction hV
  Spec (CommRingCat.of (FixedPoints.subalgebra ℤ ↑Γ(X, V) G))

/-- The local quotient map `V ⟶ Spec (Γ(X, V)ᴳ)` on a `G`-stable affine open:
the affine identification followed by the invariants morphism of the section-ring
action. -/
noncomputable def localQuotientπ {V : X.Opens} (hV : σ.IsStableOpen V)
    (hVa : IsAffineOpen V) : (V : Scheme.{u}) ⟶ σ.localQuotient hV :=
  letI := σ.gammaMulSemiringAction hV
  hVa.isoSpec.hom ≫ invariantsπ G ↑Γ(X, V) ℤ

/-- The affine identification intertwines the geometric action restricted to a
stable affine open with the `Spec` of the section-ring action (the c3 bridge:
`resLE`/`isoSpec` naturality). -/
@[reassoc]
theorem resLE_isoSpec_hom {V : X.Opens} (hV : σ.IsStableOpen V)
    (hVa : IsAffineOpen V) (g : G) :
    letI := σ.gammaMulSemiringAction hV
    (σ.hom g).resLE V V (hV.le_preimage g) ≫ hVa.isoSpec.hom =
      hVa.isoSpec.hom ≫ specSMul g := by
  letI := σ.gammaMulSemiringAction hV
  haveI : IsAffine (V : Scheme.{u}) := hVa
  have hnat := Scheme.isoSpec_hom_naturality ((σ.hom g).resLE V V (hV.le_preimage g))
  -- unfold `IsAffineOpen.isoSpec` as `Scheme.isoSpec ≪≫ Spec.mapIso (topIso.symm.op)`
  show (σ.hom g).resLE V V (hV.le_preimage g) ≫
      ((V : Scheme.{u}).isoSpec ≪≫ Scheme.Spec.mapIso V.topIso.symm.op).hom = _
  rw [Iso.trans_hom, ← Category.assoc, ← hnat, Category.assoc]
  show _ = ((V : Scheme.{u}).isoSpec ≪≫ Scheme.Spec.mapIso V.topIso.symm.op).hom ≫ _
  rw [Iso.trans_hom, Category.assoc]
  congr 1
  -- now a pure `Spec.map` computation
  show Spec.map ((σ.hom g).resLE V V (hV.le_preimage g)).appTop ≫
      Spec.map V.topIso.inv =
    Spec.map V.topIso.inv ≫
      Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom G ↑Γ(X, V) g))
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  have hsq : V.topIso.hom ≫ (σ.hom g).appLE V V (hV.le_preimage g) =
      ((σ.hom g).resLE V V (hV.le_preimage g)).appTop ≫ V.topIso.hom :=
    (arrowResLEAppIso (σ.hom g) V V (hV.le_preimage g)).hom.w
  have hof : CommRingCat.ofHom (MulSemiringAction.toRingHom G ↑Γ(X, V) g) =
      (σ.hom g).appLE V V (hV.le_preimage g) := rfl
  rw [hof, Iso.inv_comp_eq, ← Category.assoc, hsq, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

theorem localQuotientπ_eq {V : X.Opens} (hV : σ.IsStableOpen V) (hVa : IsAffineOpen V) :
    letI := σ.gammaMulSemiringAction hV
    σ.localQuotientπ hV hVa = hVa.isoSpec.hom ≫ invariantsπ G ↑Γ(X, V) ℤ := rfl

private theorem localQuotientπ_def {V : X.Opens} (hV : σ.IsStableOpen V)
    (hVa : IsAffineOpen V) :
    letI := σ.gammaMulSemiringAction hV
    σ.localQuotientπ hV hVa = hVa.isoSpec.hom ≫ invariantsπ G ↑Γ(X, V) ℤ := rfl

/-- The local quotient map coequalizes the restricted action (T-Q5c, local
invariance). -/
@[reassoc]
theorem resLE_localQuotientπ {V : X.Opens} (hV : σ.IsStableOpen V)
    (hVa : IsAffineOpen V) (g : G) :
    (σ.hom g).resLE V V (hV.le_preimage g) ≫ σ.localQuotientπ hV hVa =
      σ.localQuotientπ hV hVa := by
  letI := σ.gammaMulSemiringAction hV
  have h1 := resLE_isoSpec_hom σ hV hVa g
  show (σ.hom g).resLE V V (hV.le_preimage g) ≫ hVa.isoSpec.hom ≫
      invariantsπ G ↑Γ(X, V) ℤ = hVa.isoSpec.hom ≫ invariantsπ G ↑Γ(X, V) ℤ
  rw [← Category.assoc, h1, Category.assoc, specSMul_invariantsπ]

/-- Inverse form of the intertwiner bridge. -/
@[reassoc]
theorem specSMul_isoSpec_inv {V : X.Opens} (hV : σ.IsStableOpen V)
    (hVa : IsAffineOpen V) (g : G) :
    letI := σ.gammaMulSemiringAction hV
    specSMul g ≫ hVa.isoSpec.inv =
      hVa.isoSpec.inv ≫ (σ.hom g).resLE V V (hV.le_preimage g) := by
  letI := σ.gammaMulSemiringAction hV
  rw [Iso.eq_inv_comp, ← Category.assoc, ← resLE_isoSpec_hom σ hV hVa g,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The restricted action commutes with the inclusion of a smaller stable open. -/
@[reassoc]
theorem resLE_homOfLE {W V : X.Opens} (hW : σ.IsStableOpen W)
    (hV : σ.IsStableOpen V) (hWV : W ≤ V) (g : G) :
    (σ.hom g).resLE W W (hW.le_preimage g) ≫ X.homOfLE hWV =
      X.homOfLE hWV ≫ (σ.hom g).resLE V V (hV.le_preimage g) := by
  rw [Scheme.Hom.resLE_map, Scheme.Hom.map_resLE]

variable [Finite G]

omit [Finite G] in
private theorem localQuotientMap_invariance {W V : X.Opens} (hW : σ.IsStableOpen W)
    (hWa : IsAffineOpen W) (hV : σ.IsStableOpen V) (hVa : IsAffineOpen V)
    (hWV : W ≤ V) :
    letI := σ.gammaMulSemiringAction hW
    ∀ g : G, specSMul g ≫
        (hWa.isoSpec.inv ≫ X.homOfLE hWV ≫ σ.localQuotientπ hV hVa) =
      hWa.isoSpec.inv ≫ X.homOfLE hWV ≫ σ.localQuotientπ hV hVa := by
  letI := σ.gammaMulSemiringAction hW
  intro g
  rw [specSMul_isoSpec_inv_assoc σ hW hWa g, resLE_homOfLE_assoc σ hW hV hWV g,
    resLE_localQuotientπ σ hV hVa g]

/-- The descended map between the local quotients of nested stable affine opens:
the (unique) morphism under `invariantsπ` induced by the inclusion `W ≤ V`. -/
noncomputable def localQuotientMap {W V : X.Opens} (hW : σ.IsStableOpen W)
    (hWa : IsAffineOpen W) (hV : σ.IsStableOpen V) (hVa : IsAffineOpen V)
    (hWV : W ≤ V) : σ.localQuotient hW ⟶ σ.localQuotient hV :=
  letI := σ.gammaMulSemiringAction hW
  (exists_invariantsπ_lift G ↑Γ(X, W) ℤ
    (hWa.isoSpec.inv ≫ X.homOfLE hWV ≫ σ.localQuotientπ hV hVa)
    (σ.localQuotientMap_invariance hW hWa hV hVa hWV)).choose

/-- Defining property of `localQuotientMap`. -/
theorem invariantsπ_localQuotientMap {W V : X.Opens} (hW : σ.IsStableOpen W)
    (hWa : IsAffineOpen W) (hV : σ.IsStableOpen V) (hVa : IsAffineOpen V)
    (hWV : W ≤ V) :
    letI := σ.gammaMulSemiringAction hW
    invariantsπ G ↑Γ(X, W) ℤ ≫ σ.localQuotientMap hW hWa hV hVa hWV =
      hWa.isoSpec.inv ≫ X.homOfLE hWV ≫ σ.localQuotientπ hV hVa :=
  letI := σ.gammaMulSemiringAction hW
  (exists_invariantsπ_lift G ↑Γ(X, W) ℤ
    (hWa.isoSpec.inv ≫ X.homOfLE hWV ≫ σ.localQuotientπ hV hVa)
    (σ.localQuotientMap_invariance hW hWa hV hVa hWV)).choose_spec

/-- The local quotient maps are compatible with the local quotient projections. -/
@[reassoc]
theorem localQuotientπ_localQuotientMap {W V : X.Opens} (hW : σ.IsStableOpen W)
    (hWa : IsAffineOpen W) (hV : σ.IsStableOpen V) (hVa : IsAffineOpen V)
    (hWV : W ≤ V) :
    σ.localQuotientπ hW hWa ≫ σ.localQuotientMap hW hWa hV hVa hWV =
      X.homOfLE hWV ≫ σ.localQuotientπ hV hVa := by
  letI := σ.gammaMulSemiringAction hW
  have h1 := σ.invariantsπ_localQuotientMap hW hWa hV hVa hWV
  show (hWa.isoSpec.hom ≫ invariantsπ G ↑Γ(X, W) ℤ) ≫
      σ.localQuotientMap hW hWa hV hVa hWV = _
  rw [Category.assoc, h1, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

section OpenImmersion

variable {W V : X.Opens}

/-- The "window" of a smaller open inside the affine identification of a stable
affine open: `W ⟶ Spec Γ(X, V)`. -/
private noncomputable def windowHom (hWV : W ≤ V) (hVa : IsAffineOpen V) :
    (W : Scheme.{u}) ⟶ Spec Γ(X, V) :=
  X.homOfLE hWV ≫ hVa.isoSpec.hom

private instance (hWV : W ≤ V) (hVa : IsAffineOpen V) :
    IsOpenImmersion (windowHom (X := X) hWV hVa) := by
  rw [windowHom]
  infer_instance

omit [Finite G] in
/-- The window intertwines the restricted geometric action with `specSMul` of the
section-ring action. -/
private theorem resLE_windowHom (hWV : W ≤ V) (hVa : IsAffineOpen V)
    (hW : σ.IsStableOpen W) (hV : σ.IsStableOpen V) (g : G) :
    letI := σ.gammaMulSemiringAction hV
    (σ.hom g).resLE W W (hW.le_preimage g) ≫ windowHom hWV hVa =
      windowHom hWV hVa ≫ specSMul g := by
  letI := σ.gammaMulSemiringAction hV
  show (σ.hom g).resLE W W (hW.le_preimage g) ≫ X.homOfLE hWV ≫ hVa.isoSpec.hom =
    (X.homOfLE hWV ≫ hVa.isoSpec.hom) ≫ specSMul g
  rw [← Category.assoc, resLE_homOfLE σ hW hV hWV g, Category.assoc,
    resLE_isoSpec_hom σ hV hVa g, Category.assoc]

omit [Finite G] in
/-- Stability of the window range under the section-ring action. -/
private theorem specSMul_mem_range_windowHom (hWV : W ≤ V) (hVa : IsAffineOpen V)
    (hW : σ.IsStableOpen W) (hV : σ.IsStableOpen V) (g : G)
    (x : Spec Γ(X, V))
    (hx : x ∈ Set.range ⇑(windowHom (X := X) hWV hVa)) :
    letI := σ.gammaMulSemiringAction hV
    specSMul g x ∈ Set.range ⇑(windowHom (X := X) hWV hVa) := by
  letI := σ.gammaMulSemiringAction hV
  obtain ⟨w, rfl⟩ := hx
  refine ⟨(σ.hom g).resLE W W (hW.le_preimage g) w, ?_⟩
  rw [← Scheme.Hom.comp_apply, resLE_windowHom σ hWV hVa hW hV g,
    Scheme.Hom.comp_apply]

/-- The open of the local quotient carved out by a smaller stable open. -/
private noncomputable def imageOpens (hWV : W ≤ V) (hVa : IsAffineOpen V)
    (hW : σ.IsStableOpen W) (hV : σ.IsStableOpen V) :
    (σ.localQuotient hV).Opens :=
  letI := σ.gammaMulSemiringAction hV
  ⟨⇑(invariantsπ G ↑Γ(X, V) ℤ).base '' Set.range ⇑(windowHom (X := X) hWV hVa),
    isOpen_image_invariantsπ_of_stable G ↑Γ(X, V) ℤ
      (windowHom (X := X) hWV hVa).isOpenEmbedding.isOpen_range
      (fun g x hx => specSMul_mem_range_windowHom σ hWV hVa hW hV g x hx)⟩

/-- Saturation: the pullback of the image open is exactly the window. -/
private theorem range_fst_imageOpens (hWV : W ≤ V) (hVa : IsAffineOpen V)
    (hW : σ.IsStableOpen W) (hV : σ.IsStableOpen V) :
    letI := σ.gammaMulSemiringAction hV
    Set.range ⇑(pullback.fst (invariantsπ G ↑Γ(X, V) ℤ)
        (imageOpens σ hWV hVa hW hV).ι) =
      Set.range ⇑(windowHom (X := X) hWV hVa) := by
  letI := σ.gammaMulSemiringAction hV
  rw [IsOpenImmersion.range_pullbackFst, Scheme.Opens.opensRange_ι]
  ext x
  constructor
  · intro hx
    obtain ⟨t, ht, htx⟩ := hx
    obtain ⟨g, hg⟩ := (invariantsπ_apply_eq_iff G ↑Γ(X, V) ℤ t x).mp htx
    rw [← hg]
    exact specSMul_mem_range_windowHom σ hWV hVa hW hV g t ht
  · intro hx
    show invariantsπ G ↑Γ(X, V) ℤ x ∈
      (imageOpens σ hWV hVa hW hV : Set (σ.localQuotient hV))
    exact ⟨x, hx, rfl⟩

/-- The window is the pullback of the image open: the canonical isomorphism. -/
private noncomputable def windowIso (hWV : W ≤ V) (hVa : IsAffineOpen V)
    (hW : σ.IsStableOpen W) (hV : σ.IsStableOpen V) :
    letI := σ.gammaMulSemiringAction hV
    (W : Scheme.{u}) ≅
      pullback (invariantsπ G ↑Γ(X, V) ℤ) (imageOpens σ hWV hVa hW hV).ι :=
  letI := σ.gammaMulSemiringAction hV
  IsOpenImmersion.isoOfRangeEq (windowHom (X := X) hWV hVa) (pullback.fst _ _)
    (range_fst_imageOpens σ hWV hVa hW hV).symm

private theorem windowIso_hom_fst (hWV : W ≤ V) (hVa : IsAffineOpen V)
    (hW : σ.IsStableOpen W) (hV : σ.IsStableOpen V) :
    letI := σ.gammaMulSemiringAction hV
    (windowIso σ hWV hVa hW hV).hom ≫
        pullback.fst (invariantsπ G ↑Γ(X, V) ℤ) (imageOpens σ hWV hVa hW hV).ι =
      windowHom (X := X) hWV hVa :=
  letI := σ.gammaMulSemiringAction hV
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

private theorem windowIso_inv_window (hWV : W ≤ V) (hVa : IsAffineOpen V)
    (hW : σ.IsStableOpen W) (hV : σ.IsStableOpen V) :
    letI := σ.gammaMulSemiringAction hV
    (windowIso σ hWV hVa hW hV).inv ≫ windowHom (X := X) hWV hVa =
      pullback.fst (invariantsπ G ↑Γ(X, V) ℤ) (imageOpens σ hWV hVa hW hV).ι :=
  letI := σ.gammaMulSemiringAction hV
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

/-- The relative action on the pullback of the image open is conjugate to the
restricted geometric action under the window isomorphism. -/
private theorem pullbackSpecSMul_windowIso_inv (hWV : W ≤ V) (hVa : IsAffineOpen V)
    (hW : σ.IsStableOpen W) (hV : σ.IsStableOpen V) (g : G) :
    letI := σ.gammaMulSemiringAction hV
    pullbackSpecSMul G ↑Γ(X, V) ℤ (imageOpens σ hWV hVa hW hV).ι g ≫
        (windowIso σ hWV hVa hW hV).inv =
      (windowIso σ hWV hVa hW hV).inv ≫
        (σ.hom g).resLE W W (hW.le_preimage g) := by
  letI := σ.gammaMulSemiringAction hV
  rw [← cancel_mono (windowHom (X := X) hWV hVa), Category.assoc, Category.assoc,
    resLE_windowHom σ hWV hVa hW hV g, windowIso_inv_window σ hWV hVa hW hV,
    pullbackSpecSMul_fst, ← Category.assoc, windowIso_inv_window σ hWV hVa hW hV]

/-- The local quotient projection is surjective on points. -/
private theorem localQuotientπ_surjective {V' : X.Opens} (hV' : σ.IsStableOpen V')
    (hV'a : IsAffineOpen V') :
    Function.Surjective ⇑(σ.localQuotientπ hV' hV'a) := by
  letI := σ.gammaMulSemiringAction hV'
  intro q₀
  obtain ⟨y, hy⟩ := invariantsπ_surjective G ↑Γ(X, V') ℤ q₀
  refine ⟨hV'a.isoSpec.inv y, ?_⟩
  show (σ.localQuotientπ hV' hV'a) (hV'a.isoSpec.inv y) = q₀
  rw [localQuotientπ_def, Scheme.Hom.comp_apply]
  have h60 : hV'a.isoSpec.hom (hV'a.isoSpec.inv y) = y := by
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  rw [h60]
  exact hy

/-- **The local quotient maps are open immersions** (T-Q5 (α)): the descended map
between the local quotients of nested stable affine opens is an isomorphism onto
the saturated image open. -/
instance isOpenImmersion_localQuotientMap (hW : σ.IsStableOpen W)
    (hWa : IsAffineOpen W) (hV : σ.IsStableOpen V) (hVa : IsAffineOpen V)
    (hWV : W ≤ V) :
    IsOpenImmersion (σ.localQuotientMap hW hWa hV hVa hWV) := by
  letI := σ.gammaMulSemiringAction hV
  letI := σ.gammaMulSemiringAction hW
  -- the inverse-up-to-inclusion, from the keystone
  obtain ⟨q, hq⟩ := exists_invariantsπ_lift_of_isOpenImmersion G ↑Γ(X, V) ℤ
    (imageOpens σ hWV hVa hW hV).ι
    ((windowIso σ hWV hVa hW hV).inv ≫ σ.localQuotientπ hW hWa)
    (fun g => by
      rw [← Category.assoc, pullbackSpecSMul_windowIso_inv σ hWV hVa hW hV g,
        Category.assoc, resLE_localQuotientπ σ hW hWa g])
  -- the corestriction through the image open
  have hrangeMap : Set.range ⇑(σ.localQuotientMap hW hWa hV hVa hWV) ⊆
      Set.range ⇑(imageOpens σ hWV hVa hW hV).ι := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨w, rfl⟩ := localQuotientπ_surjective σ hW hWa t
    rw [Scheme.Opens.range_ι]
    show (σ.localQuotientπ hW hWa ≫ σ.localQuotientMap hW hWa hV hVa hWV) w ∈
      (imageOpens σ hWV hVa hW hV : Set (σ.localQuotient hV))
    rw [localQuotientπ_localQuotientMap σ hW hWa hV hVa hWV]
    refine ⟨windowHom (X := X) hWV hVa w, ⟨w, rfl⟩, ?_⟩
    show invariantsπ G ↑Γ(X, V) ℤ (windowHom (X := X) hWV hVa w) =
      (X.homOfLE hWV ≫ σ.localQuotientπ hV hVa) w
    rw [Scheme.Hom.comp_apply, localQuotientπ_def, Scheme.Hom.comp_apply]
    rfl
  obtain ⟨m₀, hm₀⟩ : ∃ m₀, m₀ ≫ (imageOpens σ hWV hVa hW hV).ι =
      σ.localQuotientMap hW hWa hV hVa hWV :=
    ⟨IsOpenImmersion.lift _ _ hrangeMap, IsOpenImmersion.lift_fac _ _ hrangeMap⟩
  -- `π^W ≫ m₀` is the window followed by `snd`
  have hπm₀ : σ.localQuotientπ hW hWa ≫ m₀ =
      (windowIso σ hWV hVa hW hV).hom ≫
        pullback.snd (invariantsπ G ↑Γ(X, V) ℤ) (imageOpens σ hWV hVa hW hV).ι := by
    rw [← cancel_mono (imageOpens σ hWV hVa hW hV).ι, Category.assoc, hm₀,
      localQuotientπ_localQuotientMap σ hW hWa hV hVa hWV, Category.assoc,
      ← pullback.condition, ← Category.assoc, windowIso_hom_fst σ hWV hVa hW hV]
    show X.homOfLE hWV ≫ σ.localQuotientπ hV hVa =
      (X.homOfLE hWV ≫ hVa.isoSpec.hom) ≫ invariantsπ G ↑Γ(X, V) ℤ
    rw [localQuotientπ_def, Category.assoc]
  -- the projection expressed through the local quotient map
  have hπ' : invariantsπ G ↑Γ(X, W) ℤ = hWa.isoSpec.inv ≫ σ.localQuotientπ hW hWa := by
    rw [localQuotientπ_def, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  -- two-sided inverse
  have hmq : m₀ ≫ q = 𝟙 _ := by
    refine invariantsπ_hom_ext G ↑Γ(X, W) ℤ _ _ ?_
    rw [Category.comp_id, hπ', Category.assoc]
    congr 1
    rw [← Category.assoc, hπm₀, Category.assoc, hq, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp]
  have hqm : q ≫ m₀ = 𝟙 _ := by
    refine invariantsπ_hom_ext_of_isOpenImmersion G ↑Γ(X, V) ℤ
      (imageOpens σ hWV hVa hW hV).ι _ _ ?_
    rw [Category.comp_id, ← Category.assoc, hq, Category.assoc, hπm₀,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  haveI : IsIso m₀ := ⟨q, hmq, hqm⟩
  rw [← hm₀]
  infer_instance

omit [Finite G] in
/-- Intersections of stable opens are stable. -/
theorem IsStableOpen.inf {τ : SchemeAction G X} {U V : X.Opens}
    (hU : τ.IsStableOpen U) (hV : τ.IsStableOpen V) :
    τ.IsStableOpen (U ⊓ V) := by
  intro g
  rw [Scheme.Hom.preimage_inf, hU g, hV g]

/-- The local quotient map at equal opens is the identity. -/
theorem localQuotientMap_self {W : X.Opens} (hW : σ.IsStableOpen W)
    (hWa : IsAffineOpen W) :
    σ.localQuotientMap hW hWa hW hWa le_rfl = 𝟙 _ := by
  letI := σ.gammaMulSemiringAction hW
  refine invariantsπ_hom_ext G ↑Γ(X, W) ℤ _ _ ?_
  have h1 : invariantsπ G ↑Γ(X, W) ℤ =
      hWa.isoSpec.inv ≫ σ.localQuotientπ hW hWa := by
    rw [localQuotientπ_def, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [Category.comp_id, h1, Category.assoc]
  congr 1
  rw [localQuotientπ_localQuotientMap σ hW hWa hW hWa le_rfl, Scheme.homOfLE_rfl,
    Category.id_comp]

/-- The local quotient maps compose along inclusions. -/
@[reassoc]
theorem localQuotientMap_trans {W V U : X.Opens} (hW : σ.IsStableOpen W)
    (hWa : IsAffineOpen W) (hV : σ.IsStableOpen V) (hVa : IsAffineOpen V)
    (hU : σ.IsStableOpen U) (hUa : IsAffineOpen U) (hWV : W ≤ V) (hVU : V ≤ U) :
    σ.localQuotientMap hW hWa hV hVa hWV ≫ σ.localQuotientMap hV hVa hU hUa hVU =
      σ.localQuotientMap hW hWa hU hUa (hWV.trans hVU) := by
  letI := σ.gammaMulSemiringAction hW
  refine invariantsπ_hom_ext G ↑Γ(X, W) ℤ _ _ ?_
  have h1 : invariantsπ G ↑Γ(X, W) ℤ =
      hWa.isoSpec.inv ≫ σ.localQuotientπ hW hWa := by
    rw [localQuotientπ_def, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [h1, Category.assoc, Category.assoc]
  congr 1
  rw [← Category.assoc, localQuotientπ_localQuotientMap σ hW hWa hV hVa hWV,
    Category.assoc, localQuotientπ_localQuotientMap σ hV hVa hU hUa hVU,
    localQuotientπ_localQuotientMap σ hW hWa hU hUa (hWV.trans hVU),
    ← Category.assoc, ← Scheme.homOfLE_homOfLE (X := X) hWV hVU]

/-- The range of the local quotient map is exactly the saturated image open
(β2a). -/
private theorem range_localQuotientMap (hWV : W ≤ V) (hVa : IsAffineOpen V)
    (hW : σ.IsStableOpen W) (hWa : IsAffineOpen W) (hV : σ.IsStableOpen V) :
    Set.range ⇑(σ.localQuotientMap hW hWa hV hVa hWV) =
      (imageOpens σ hWV hVa hW hV : Set (σ.localQuotient hV)) := by
  letI := σ.gammaMulSemiringAction hV
  letI := σ.gammaMulSemiringAction hW
  apply Set.Subset.antisymm
  · rintro _ ⟨t, rfl⟩
    obtain ⟨w, rfl⟩ := localQuotientπ_surjective σ hW hWa t
    show (σ.localQuotientπ hW hWa ≫ σ.localQuotientMap hW hWa hV hVa hWV) w ∈
      (imageOpens σ hWV hVa hW hV : Set (σ.localQuotient hV))
    rw [localQuotientπ_localQuotientMap σ hW hWa hV hVa hWV]
    refine ⟨windowHom (X := X) hWV hVa w, ⟨w, rfl⟩, ?_⟩
    show invariantsπ G ↑Γ(X, V) ℤ (windowHom (X := X) hWV hVa w) =
      (X.homOfLE hWV ≫ σ.localQuotientπ hV hVa) w
    rw [Scheme.Hom.comp_apply, localQuotientπ_def, Scheme.Hom.comp_apply]
    rfl
  · rintro t ⟨s, ⟨w, rfl⟩, rfl⟩
    -- π(window w) = map (π^W w)
    refine ⟨σ.localQuotientπ hW hWa w, ?_⟩
    rw [← Scheme.Hom.comp_apply, localQuotientπ_localQuotientMap σ hW hWa hV hVa hWV]
    show (X.homOfLE hWV ≫ σ.localQuotientπ hV hVa) w =
      invariantsπ G ↑Γ(X, V) ℤ (windowHom (X := X) hWV hVa w)
    rw [Scheme.Hom.comp_apply, localQuotientπ_def, Scheme.Hom.comp_apply]
    rfl

omit [Finite G] in
private theorem range_windowHom (hWV : W ≤ V) (hVa : IsAffineOpen V) :
    Set.range ⇑(windowHom (X := X) hWV hVa) =
      ⇑hVa.isoSpec.hom '' ↑(V.ι ⁻¹ᵁ W) := by
  show Set.range (⇑hVa.isoSpec.hom ∘ ⇑(X.homOfLE hWV)) = _
  rw [Set.range_comp]
  congr 1
  have h70 := Scheme.opensRange_homOfLE (X := X) hWV
  exact congrArg (fun t : (V : Scheme.{u}).Opens => (t : Set (V : Scheme.{u}))) h70

/-- **Saturation, at the level of points**: a point of the local quotient of `V` lies in the
image open carved out by a smaller *stable* open `W` exactly when its preimage lies in `W`.

This is the point-set heart of "the quotient charts pull back to the atlas charts": the fibres of
`invariantsπ` are the `G`-orbits (`invariantsπ_apply_eq_iff`) and `W` is `G`-stable
(`specSMul_mem_range_windowHom`), so an orbit meets `W` iff it lies in `W`. -/
private theorem localQuotientπ_mem_imageOpens_iff (hWV : W ≤ V) (hVa : IsAffineOpen V)
    (hW : σ.IsStableOpen W) (hV : σ.IsStableOpen V) (w : (V : Scheme.{u})) :
    σ.localQuotientπ hV hVa w ∈ (imageOpens σ hWV hVa hW hV : Set (σ.localQuotient hV)) ↔
      w ∈ (V.ι ⁻¹ᵁ W : (V : Scheme.{u}).Opens) := by
  letI := σ.gammaMulSemiringAction hV
  have hπ : σ.localQuotientπ hV hVa w = invariantsπ G ↑Γ(X, V) ℤ (hVa.isoSpec.hom w) := by
    rw [localQuotientπ_def, Scheme.Hom.comp_apply]
    rfl
  constructor
  · rintro ⟨t, ht, hteq⟩
    rw [hπ] at hteq
    obtain ⟨g, hg⟩ := (invariantsπ_apply_eq_iff G ↑Γ(X, V) ℤ t (hVa.isoSpec.hom w)).mp hteq
    have hmem : hVa.isoSpec.hom w ∈ Set.range ⇑(windowHom (X := X) hWV hVa) := by
      rw [← hg]
      exact specSMul_mem_range_windowHom σ hWV hVa hW hV g t ht
    rw [range_windowHom (X := X) hWV hVa] at hmem
    obtain ⟨v, hv, hveq⟩ := hmem
    have hvw : v = w := hVa.isoSpec.hom.isOpenEmbedding.injective hveq
    exact hvw ▸ hv
  · intro hw
    refine ⟨hVa.isoSpec.hom w, ?_, hπ.symm⟩
    rw [range_windowHom (X := X) hWV hVa]
    exact ⟨w, hw, rfl⟩

omit [Finite G] in
/-- Windows intersect as expected (β2b, window level). -/
private theorem range_windowHom_inter {W₁ W₂ : X.Opens} (hW₁V : W₁ ≤ V)
    (hW₂V : W₂ ≤ V) (hVa : IsAffineOpen V) :
    Set.range ⇑(windowHom (X := X) hW₁V hVa) ∩
        Set.range ⇑(windowHom (X := X) hW₂V hVa) =
      Set.range ⇑(windowHom (X := X) (W := W₁ ⊓ W₂) (inf_le_left.trans hW₁V) hVa) := by
  rw [range_windowHom (X := X) hW₁V hVa, range_windowHom (X := X) hW₂V hVa,
    range_windowHom (X := X) (W := W₁ ⊓ W₂) (inf_le_left.trans hW₁V) hVa,
    ← Set.image_inter (hVa.isoSpec.hom.isOpenEmbedding.injective)]
  congr 1

/-- Saturated image opens intersect as expected (β2b). -/
private theorem imageOpens_inf {W₁ W₂ : X.Opens} (hW₁V : W₁ ≤ V) (hW₂V : W₂ ≤ V)
    (hVa : IsAffineOpen V) (hW₁ : σ.IsStableOpen W₁) (hW₂ : σ.IsStableOpen W₂)
    (hV : σ.IsStableOpen V) :
    imageOpens σ hW₁V hVa hW₁ hV ⊓ imageOpens σ hW₂V hVa hW₂ hV =
      imageOpens σ (inf_le_left.trans hW₁V) hVa (hW₁.inf hW₂) hV := by
  letI := σ.gammaMulSemiringAction hV
  refine TopologicalSpace.Opens.ext ?_
  show (imageOpens σ hW₁V hVa hW₁ hV : Set (σ.localQuotient hV)) ∩
      (imageOpens σ hW₂V hVa hW₂ hV : Set (σ.localQuotient hV)) = _
  apply Set.Subset.antisymm
  · rintro p ⟨⟨a, haA, ha⟩, ⟨b, hbB, hb⟩⟩
    -- both fibre points are in the same orbit; stability puts one in both windows
    obtain ⟨g, hg⟩ := (invariantsπ_apply_eq_iff G ↑Γ(X, V) ℤ a b).mp (by rw [ha, hb])
    have hbA : b ∈ Set.range ⇑(windowHom (X := X) hW₁V hVa) := by
      rw [← hg]
      exact specSMul_mem_range_windowHom σ hW₁V hVa hW₁ hV g a haA
    refine ⟨b, ?_, hb⟩
    rw [← range_windowHom_inter (X := X) hW₁V hW₂V hVa]
    exact ⟨hbA, hbB⟩
  · rintro p ⟨a, haA, ha⟩
    have h71 : a ∈ Set.range ⇑(windowHom (X := X) hW₁V hVa) ∩
        Set.range ⇑(windowHom (X := X) hW₂V hVa) := by
      rw [range_windowHom_inter (X := X) hW₁V hW₂V hVa]
      exact haA
    exact ⟨⟨a, h71.1, ha⟩, ⟨a, h71.2, ha⟩⟩

/-- The two saturated image opens of an intersection agree at the level of sets
(coe of `imageOpens_inf`). -/
private theorem range_inter_localQuotientMap {W₁ W₂ : X.Opens} (hW₁V : W₁ ≤ V)
    (hW₂V : W₂ ≤ V) (hVa : IsAffineOpen V) (hW₁ : σ.IsStableOpen W₁)
    (hW₁a : IsAffineOpen W₁) (hW₂ : σ.IsStableOpen W₂) (hW₂a : IsAffineOpen W₂)
    (hV : σ.IsStableOpen V) (hW₁₂a : IsAffineOpen (W₁ ⊓ W₂)) :
    Set.range ⇑(σ.localQuotientMap (hW₁.inf hW₂) hW₁₂a hV hVa
        (inf_le_left.trans hW₁V)) =
      Set.range ⇑(σ.localQuotientMap hW₁ hW₁a hV hVa hW₁V) ∩
        Set.range ⇑(σ.localQuotientMap hW₂ hW₂a hV hVa hW₂V) := by
  rw [range_localQuotientMap σ (inf_le_left.trans hW₁V) hVa (hW₁.inf hW₂) hW₁₂a hV,
    range_localQuotientMap σ hW₁V hVa hW₁ hW₁a hV,
    range_localQuotientMap σ hW₂V hVa hW₂ hW₂a hV]
  have h80 := imageOpens_inf σ hW₁V hW₂V hVa hW₁ hW₂ hV
  have h81 := congrArg
    (fun t : (σ.localQuotient hV).Opens => (t : Set (σ.localQuotient hV))) h80
  exact h81.symm

/-- **The triple-overlap comparison** (β2c): the pullback of two local quotient
immersions is the local quotient of the intersection. -/
private noncomputable def tripleIso {W₁ W₂ : X.Opens} (hW₁V : W₁ ≤ V) (hW₂V : W₂ ≤ V)
    (hVa : IsAffineOpen V) (hW₁ : σ.IsStableOpen W₁) (hW₁a : IsAffineOpen W₁)
    (hW₂ : σ.IsStableOpen W₂) (hW₂a : IsAffineOpen W₂) (hV : σ.IsStableOpen V)
    (hW₁₂a : IsAffineOpen (W₁ ⊓ W₂)) :
    σ.localQuotient (hW₁.inf hW₂) ≅
      pullback (σ.localQuotientMap hW₁ hW₁a hV hVa hW₁V)
        (σ.localQuotientMap hW₂ hW₂a hV hVa hW₂V) :=
  IsOpenImmersion.isoOfRangeEq
    (σ.localQuotientMap (hW₁.inf hW₂) hW₁₂a hV hVa (inf_le_left.trans hW₁V))
    (pullback.fst _ _ ≫ σ.localQuotientMap hW₁ hW₁a hV hVa hW₁V)
    (by
      rw [IsOpenImmersion.range_pullback_to_base_of_left]
      exact range_inter_localQuotientMap σ hW₁V hW₂V hVa hW₁ hW₁a hW₂ hW₂a hV hW₁₂a)

private theorem tripleIso_hom_comp {W₁ W₂ : X.Opens} (hW₁V : W₁ ≤ V) (hW₂V : W₂ ≤ V)
    (hVa : IsAffineOpen V) (hW₁ : σ.IsStableOpen W₁) (hW₁a : IsAffineOpen W₁)
    (hW₂ : σ.IsStableOpen W₂) (hW₂a : IsAffineOpen W₂) (hV : σ.IsStableOpen V)
    (hW₁₂a : IsAffineOpen (W₁ ⊓ W₂)) :
    (σ.tripleIso hW₁V hW₂V hVa hW₁ hW₁a hW₂ hW₂a hV hW₁₂a).hom ≫
        pullback.fst _ _ ≫ σ.localQuotientMap hW₁ hW₁a hV hVa hW₁V =
      σ.localQuotientMap (hW₁.inf hW₂) hW₁₂a hV hVa (inf_le_left.trans hW₁V) :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The first-projection compatibility of the triple comparison. -/
private theorem tripleIso_hom_fst {W₁ W₂ : X.Opens} (hW₁V : W₁ ≤ V) (hW₂V : W₂ ≤ V)
    (hVa : IsAffineOpen V) (hW₁ : σ.IsStableOpen W₁) (hW₁a : IsAffineOpen W₁)
    (hW₂ : σ.IsStableOpen W₂) (hW₂a : IsAffineOpen W₂) (hV : σ.IsStableOpen V)
    (hW₁₂a : IsAffineOpen (W₁ ⊓ W₂)) :
    (σ.tripleIso hW₁V hW₂V hVa hW₁ hW₁a hW₂ hW₂a hV hW₁₂a).hom ≫ pullback.fst _ _ =
      σ.localQuotientMap (hW₁.inf hW₂) hW₁₂a hW₁ hW₁a inf_le_left := by
  rw [← cancel_mono (σ.localQuotientMap hW₁ hW₁a hV hVa hW₁V), Category.assoc,
    tripleIso_hom_comp σ hW₁V hW₂V hVa hW₁ hW₁a hW₂ hW₂a hV hW₁₂a,
    localQuotientMap_trans σ (hW₁.inf hW₂) hW₁₂a hW₁ hW₁a hV hVa inf_le_left hW₁V]

/-- The second-projection compatibility of the triple comparison. -/
private theorem tripleIso_hom_snd {W₁ W₂ : X.Opens} (hW₁V : W₁ ≤ V) (hW₂V : W₂ ≤ V)
    (hVa : IsAffineOpen V) (hW₁ : σ.IsStableOpen W₁) (hW₁a : IsAffineOpen W₁)
    (hW₂ : σ.IsStableOpen W₂) (hW₂a : IsAffineOpen W₂) (hV : σ.IsStableOpen V)
    (hW₁₂a : IsAffineOpen (W₁ ⊓ W₂)) :
    (σ.tripleIso hW₁V hW₂V hVa hW₁ hW₁a hW₂ hW₂a hV hW₁₂a).hom ≫ pullback.snd _ _ =
      σ.localQuotientMap (hW₁.inf hW₂) hW₁₂a hW₂ hW₂a inf_le_right := by
  rw [← cancel_mono (σ.localQuotientMap hW₂ hW₂a hV hVa hW₂V), Category.assoc,
    ← pullback.condition, ← Category.assoc, Category.assoc,
    tripleIso_hom_comp σ hW₁V hW₂V hVa hW₁ hW₁a hW₂ hW₂a hV hW₁₂a,
    localQuotientMap_trans σ (hW₁.inf hW₂) hW₁₂a hW₂ hW₂a hV hVa inf_le_right hW₂V]

/-- Local quotient maps along equal opens are isomorphisms. -/
theorem isIso_localQuotientMap_of_le_le {W V : X.Opens} (hW : σ.IsStableOpen W)
    (hWa : IsAffineOpen W) (hV : σ.IsStableOpen V) (hVa : IsAffineOpen V)
    (hWV : W ≤ V) (hVW : V ≤ W) :
    IsIso (σ.localQuotientMap hW hWa hV hVa hWV) := by
  refine ⟨σ.localQuotientMap hV hVa hW hWa hVW, ?_, ?_⟩
  · rw [localQuotientMap_trans σ hW hWa hV hVa hW hWa hWV hVW]
    exact σ.localQuotientMap_self hW hWa
  · rw [localQuotientMap_trans σ hV hVa hW hWa hV hVa hVW hWV]
    exact σ.localQuotientMap_self hV hVa

/-- The first projection of the local-quotient pullback, through the triple
comparison. -/
private theorem fst_eq_tripleIso_inv {W₁ W₂ : X.Opens} (hW₁V : W₁ ≤ V)
    (hW₂V : W₂ ≤ V) (hVa : IsAffineOpen V) (hW₁ : σ.IsStableOpen W₁)
    (hW₁a : IsAffineOpen W₁) (hW₂ : σ.IsStableOpen W₂) (hW₂a : IsAffineOpen W₂)
    (hV : σ.IsStableOpen V) (hW₁₂a : IsAffineOpen (W₁ ⊓ W₂)) :
    pullback.fst (σ.localQuotientMap hW₁ hW₁a hV hVa hW₁V)
        (σ.localQuotientMap hW₂ hW₂a hV hVa hW₂V) =
      (σ.tripleIso hW₁V hW₂V hVa hW₁ hW₁a hW₂ hW₂a hV hW₁₂a).inv ≫
        σ.localQuotientMap (hW₁.inf hW₂) hW₁₂a hW₁ hW₁a inf_le_left := by
  rw [Iso.eq_inv_comp]
  exact tripleIso_hom_fst σ hW₁V hW₂V hVa hW₁ hW₁a hW₂ hW₂a hV hW₁₂a

/-- The second projection of the local-quotient pullback, through the triple
comparison. -/
private theorem snd_eq_tripleIso_inv {W₁ W₂ : X.Opens} (hW₁V : W₁ ≤ V)
    (hW₂V : W₂ ≤ V) (hVa : IsAffineOpen V) (hW₁ : σ.IsStableOpen W₁)
    (hW₁a : IsAffineOpen W₁) (hW₂ : σ.IsStableOpen W₂) (hW₂a : IsAffineOpen W₂)
    (hV : σ.IsStableOpen V) (hW₁₂a : IsAffineOpen (W₁ ⊓ W₂)) :
    pullback.snd (σ.localQuotientMap hW₁ hW₁a hV hVa hW₁V)
        (σ.localQuotientMap hW₂ hW₂a hV hVa hW₂V) =
      (σ.tripleIso hW₁V hW₂V hVa hW₁ hW₁a hW₂ hW₂a hV hW₁₂a).inv ≫
        σ.localQuotientMap (hW₁.inf hW₂) hW₁₂a hW₂ hW₂a inf_le_right := by
  rw [Iso.eq_inv_comp]
  exact tripleIso_hom_snd σ hW₁V hW₂V hVa hW₁ hW₁a hW₂ hW₂a hV hW₁₂a

omit [Finite G] in
private theorem triple_le {A B C : X.Opens} :
    (A ⊓ B) ⊓ (A ⊓ C) ≤ (B ⊓ C) ⊓ (B ⊓ A) :=
  le_inf (le_inf (inf_le_left.trans inf_le_right)
      (inf_le_right.trans inf_le_right))
    (le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_left))

/-- Affine diagonal (over `ℤ`) transfers along an affine morphism: if `S` has affine
diagonal and `f : Z ⟶ S` is affine, so does `Z`. This lets the quotient machinery's
`[IsAffineHom (pullback.diagonal (terminal.from Z))]` hypothesis be sourced from the
BASE of an affine (e.g. finite étale) structure morphism — the [GHB7-0] plumbing. -/
theorem _root_.AlgebraicGeometry.isAffineHom_diagonal_terminalFrom_of_isAffineHom
    {Z S : Scheme.{u}} (f : Z ⟶ S) [IsAffineHom f]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from S))] :
    IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from Z)) := by
  rw [← Limits.terminal.comp_from f]
  have h₁ : MorphismProperty.diagonal @IsAffineHom f := by
    rw [MorphismProperty.diagonal_iff]
    haveI : IsSeparated f := .of_isAffineHom f
    infer_instance
  have h₂ : MorphismProperty.diagonal @IsAffineHom (Limits.terminal.from S) := ‹_›
  exact MorphismProperty.IsStableUnderComposition.comp_mem
    (P := MorphismProperty.diagonal @IsAffineHom) f (Limits.terminal.from S) h₁ h₂

section Glue

variable [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
variable (V : X → X.Opens) (hVs : ∀ x, σ.IsStableOpen (V x))
  (hVa : ∀ x, IsAffineOpen (V x))

/-- The pairwise piece of the quotient glue data. -/
@[reducible]
private noncomputable def glueF (i j : X) :
    σ.localQuotient ((hVs i).inf (hVs j)) ⟶ σ.localQuotient (hVs i) :=
  σ.localQuotientMap ((hVs i).inf (hVs j)) ((hVa i).inf (hVa j)) (hVs i) (hVa i)
    inf_le_left

/-- The transition map of the quotient glue data. -/
@[reducible]
private noncomputable def glueT (i j : X) :
    σ.localQuotient ((hVs i).inf (hVs j)) ⟶
      σ.localQuotient ((hVs j).inf (hVs i)) :=
  σ.localQuotientMap ((hVs i).inf (hVs j)) ((hVa i).inf (hVa j))
    ((hVs j).inf (hVs i)) ((hVa j).inf (hVa i)) (le_inf inf_le_right inf_le_left)

/-- The triple transition of the quotient glue data. -/
@[reducible]
private noncomputable def glueT' (i j k : X) :
    pullback (glueF σ V hVs hVa i j) (glueF σ V hVs hVa i k) ⟶
      pullback (glueF σ V hVs hVa j k) (glueF σ V hVs hVa j i) :=
  (σ.tripleIso inf_le_left inf_le_left (hVa i) ((hVs i).inf (hVs j))
      ((hVa i).inf (hVa j)) ((hVs i).inf (hVs k)) ((hVa i).inf (hVa k)) (hVs i)
      (((hVa i).inf (hVa j)).inf ((hVa i).inf (hVa k)))).inv ≫
    σ.localQuotientMap (((hVs i).inf (hVs j)).inf ((hVs i).inf (hVs k)))
      (((hVa i).inf (hVa j)).inf ((hVa i).inf (hVa k)))
      (((hVs j).inf (hVs k)).inf ((hVs j).inf (hVs i)))
      (((hVa j).inf (hVa k)).inf ((hVa j).inf (hVa i))) triple_le ≫
    (σ.tripleIso inf_le_left inf_le_left (hVa j) ((hVs j).inf (hVs k))
      ((hVa j).inf (hVa k)) ((hVs j).inf (hVs i)) ((hVa j).inf (hVa i)) (hVs j)
      (((hVa j).inf (hVa k)).inf ((hVa j).inf (hVa i)))).hom

private theorem glueT'_fac (i j k : X) :
    glueT' σ V hVs hVa i j k ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ glueT σ V hVs hVa i j := by
  rw [glueT', Category.assoc, Category.assoc,
    snd_eq_tripleIso_inv σ inf_le_left inf_le_left (hVa j) ((hVs j).inf (hVs k))
      ((hVa j).inf (hVa k)) ((hVs j).inf (hVs i)) ((hVa j).inf (hVa i)) (hVs j)
      (((hVa j).inf (hVa k)).inf ((hVa j).inf (hVa i))),
    Iso.hom_inv_id_assoc,
    localQuotientMap_trans σ _ (((hVa i).inf (hVa j)).inf ((hVa i).inf (hVa k))) _
      (((hVa j).inf (hVa k)).inf ((hVa j).inf (hVa i))) _ ((hVa j).inf (hVa i))
      triple_le inf_le_right,
    fst_eq_tripleIso_inv σ inf_le_left inf_le_left (hVa i) ((hVs i).inf (hVs j))
      ((hVa i).inf (hVa j)) ((hVs i).inf (hVs k)) ((hVa i).inf (hVa k)) (hVs i)
      (((hVa i).inf (hVa j)).inf ((hVa i).inf (hVa k))),
    Category.assoc, glueT,
    localQuotientMap_trans σ _ (((hVa i).inf (hVa j)).inf ((hVa i).inf (hVa k))) _
      ((hVa i).inf (hVa j)) _ ((hVa j).inf (hVa i)) inf_le_left
      (le_inf inf_le_right inf_le_left)]

private theorem glueT'_cocycle (i j k : X) :
    glueT' σ V hVs hVa i j k ≫ glueT' σ V hVs hVa j k i ≫
      glueT' σ V hVs hVa k i j = 𝟙 _ := by
  show ((σ.tripleIso _ _ _ _ _ _ _ _ _).inv ≫ _ ≫ (σ.tripleIso _ _ _ _ _ _ _ _ _).hom) ≫
    ((σ.tripleIso _ _ _ _ _ _ _ _ _).inv ≫ _ ≫ (σ.tripleIso _ _ _ _ _ _ _ _ _).hom) ≫
    ((σ.tripleIso _ _ _ _ _ _ _ _ _).inv ≫ _ ≫ (σ.tripleIso _ _ _ _ _ _ _ _ _).hom) = 𝟙 _
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [localQuotientMap_trans_assoc σ _
      (((hVa i).inf (hVa j)).inf ((hVa i).inf (hVa k))) _
      (((hVa j).inf (hVa k)).inf ((hVa j).inf (hVa i))) _
      (((hVa k).inf (hVa i)).inf ((hVa k).inf (hVa j))) triple_le triple_le,
    localQuotientMap_trans_assoc σ _
      (((hVa i).inf (hVa j)).inf ((hVa i).inf (hVa k))) _
      (((hVa k).inf (hVa i)).inf ((hVa k).inf (hVa j))) _
      (((hVa i).inf (hVa j)).inf ((hVa i).inf (hVa k)))
      (triple_le.trans triple_le) triple_le,
    show σ.localQuotientMap _ (((hVa i).inf (hVa j)).inf ((hVa i).inf (hVa k))) _
        (((hVa i).inf (hVa j)).inf ((hVa i).inf (hVa k)))
        ((triple_le.trans triple_le).trans triple_le) = 𝟙 _ from
      σ.localQuotientMap_self _ _,
    Category.id_comp, Iso.inv_hom_id]

/-- **The quotient glue data** (T-Q5 c4): the local quotients of a stable affine
atlas, glued along the saturated overlaps. -/
@[reducible]
private noncomputable def quotientGlueData : Scheme.GlueData where
  J := X
  U := fun i => σ.localQuotient (hVs i)
  V := fun p => σ.localQuotient ((hVs p.1).inf (hVs p.2))
  f := fun i j => glueF σ V hVs hVa i j
  f_id := fun i =>
    σ.isIso_localQuotientMap_of_le_le ((hVs i).inf (hVs i))
      ((hVa i).inf (hVa i)) (hVs i) (hVa i) inf_le_left (le_inf le_rfl le_rfl)
  t := fun i j => glueT σ V hVs hVa i j
  t_id := fun i => σ.localQuotientMap_self ((hVs i).inf (hVs i)) ((hVa i).inf (hVa i))
  t' := fun i j k => glueT' σ V hVs hVa i j k
  t_fac := fun i j k => glueT'_fac σ V hVs hVa i j k
  cocycle := fun i j k => glueT'_cocycle σ V hVs hVa i j k
  f_open := fun i j => inferInstance

/-- **The quotient of a scheme by a finite group action** (T-Q5d): the local
quotients of a stable affine atlas, glued. -/
@[reducible]
noncomputable def quotient : Scheme.{u} := (quotientGlueData σ V hVs hVa).glued

/-- The chart composites into the quotient agree on overlaps. -/
private theorem chartCompat (i j : X) :
    X.homOfLE (inf_le_left : V i ⊓ V j ≤ V i) ≫ σ.localQuotientπ (hVs i) (hVa i) ≫
      (quotientGlueData σ V hVs hVa).ι i =
    X.homOfLE (inf_le_right : V i ⊓ V j ≤ V j) ≫ σ.localQuotientπ (hVs j) (hVa j) ≫
      (quotientGlueData σ V hVs hVa).ι j := by
  rw [← Category.assoc, ← localQuotientπ_localQuotientMap σ ((hVs i).inf (hVs j))
      ((hVa i).inf (hVa j)) (hVs i) (hVa i) inf_le_left,
    ← Category.assoc, ← localQuotientπ_localQuotientMap σ ((hVs i).inf (hVs j))
      ((hVa i).inf (hVa j)) (hVs j) (hVa j) inf_le_right,
    Category.assoc, Category.assoc]
  congr 1
  have h90 := (quotientGlueData σ V hVs hVa).glue_condition i j
  show σ.localQuotientMap _ _ _ _ _ ≫ (quotientGlueData σ V hVs hVa).ι i =
    σ.localQuotientMap _ _ _ _ _ ≫ (quotientGlueData σ V hVs hVa).ι j
  rw [← h90, ← Category.assoc]
  congr 1
  exact localQuotientMap_trans σ ((hVs i).inf (hVs j)) ((hVa i).inf (hVa j))
    ((hVs j).inf (hVs i)) ((hVa j).inf (hVa i)) (hVs j) (hVa j)
    (le_inf inf_le_right inf_le_left) inf_le_left

variable (hVmem : ∀ x : X, x ∈ V x)

/-- The atlas cover of `X` by the stable affine opens. -/
@[reducible]
private noncomputable def atlasCover : X.OpenCover :=
  Scheme.Cover.mkOfCovers (J := ↥X)
    (fun x => (V x : Scheme.{u}))
    (fun x => (V x).ι)
    (fun x => by
      have h : x ∈ Set.range ⇑(V x).ι := by
        rw [Scheme.Opens.range_ι]
        exact hVmem x
      obtain ⟨v, hv⟩ := h
      exact ⟨x, v, hv⟩)
    (fun x => inferInstance)

private theorem quotientπCompat (x y : X) :
    pullback.fst ((V x).ι) ((V y).ι) ≫
      (σ.localQuotientπ (hVs x) (hVa x) ≫ (quotientGlueData σ V hVs hVa).ι x) =
    pullback.snd ((V x).ι) ((V y).ι) ≫
      (σ.localQuotientπ (hVs y) (hVa y) ≫ (quotientGlueData σ V hVs hVa).ι y) := by
  have htop : (V y).ι ⁻¹ᵁ (V y) = ⊤ := by
    refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun v => ?_)
    show (V y).ι v ∈ (V y : Set X)
    rw [← Scheme.Opens.range_ι]
    exact ⟨v, rfl⟩
  have H := IsOpenImmersion.isPullback (X.homOfLE (inf_le_left : V x ⊓ V y ≤ V x))
    (X.homOfLE (inf_le_right : V x ⊓ V y ≤ V y)) (V x).ι (V y).ι
    (by simp)
    (by rw [Scheme.Opens.opensRange_ι, Scheme.opensRange_homOfLE,
      Scheme.Hom.preimage_inf, htop, inf_top_eq])
  rw [← cancel_epi H.isoPullback.hom, H.isoPullback_hom_fst_assoc,
    H.isoPullback_hom_snd_assoc]
  exact chartCompat σ V hVs hVa x y

/-- The quotient projection `X ⟶ X/G`, glued from the local quotient
projections. -/
noncomputable def quotientπ : X ⟶ σ.quotient V hVs hVa :=
  (atlasCover V hVmem).glueMorphisms
    (fun x => σ.localQuotientπ (hVs x) (hVa x) ≫ (quotientGlueData σ V hVs hVa).ι x)
    (fun x y => quotientπCompat σ V hVs hVa x y)

/-- Defining property of the quotient projection on each chart. -/
theorem opensι_quotientπ (x : X) :
    (V x).ι ≫ σ.quotientπ V hVs hVa hVmem =
      σ.localQuotientπ (hVs x) (hVa x) ≫ (quotientGlueData σ V hVs hVa).ι x :=
  (atlasCover V hVmem).ι_glueMorphisms
    (fun x => σ.localQuotientπ (hVs x) (hVa x) ≫ (quotientGlueData σ V hVs hVa).ι x)
    (fun x y => quotientπCompat σ V hVs hVa x y) x

/-- **Invariance of the quotient projection** (T-Q5d contract, part 1):
`σ.hom g ≫ quotientπ = quotientπ`. -/
theorem hom_quotientπ (g : G) :
    σ.hom g ≫ σ.quotientπ V hVs hVa hVmem = σ.quotientπ V hVs hVa hVmem := by
  have key : ∀ x' : X, (V x').ι ≫ σ.hom g ≫ σ.quotientπ V hVs hVa hVmem =
      (V x').ι ≫ σ.quotientπ V hVs hVa hVmem := by
    intro x'
    have hres : (V x').ι ≫ σ.hom g =
        (σ.hom g).resLE (V x') (V x') ((hVs x').le_preimage g) ≫ (V x').ι :=
      (Scheme.Hom.resLE_comp_ι _ _).symm
    rw [← Category.assoc, hres, Category.assoc,
      opensι_quotientπ σ V hVs hVa hVmem x',
      resLE_localQuotientπ_assoc σ (hVs x') (hVa x') g]
  exact (atlasCover V hVmem).hom_ext _ _ fun x => key x

/-- **Uniqueness of descent along the quotient projection** (T-Q5d contract,
part 2). -/
theorem quotientπ_hom_ext {Y : Scheme.{u}} (h₁ h₂ : σ.quotient V hVs hVa ⟶ Y)
    (H : σ.quotientπ V hVs hVa hVmem ≫ h₁ = σ.quotientπ V hVs hVa hVmem ≫ h₂) :
    h₁ = h₂ := by
  have key : ∀ x : X, (quotientGlueData σ V hVs hVa).ι x ≫ h₁ =
      (quotientGlueData σ V hVs hVa).ι x ≫ h₂ := by
    intro x
    letI := σ.gammaMulSemiringAction (hVs x)
    have hπ' : invariantsπ G ↑Γ(X, V x) ℤ =
        (hVa x).isoSpec.inv ≫ σ.localQuotientπ (hVs x) (hVa x) := by
      rw [localQuotientπ_def, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    refine invariantsπ_hom_ext G ↑Γ(X, V x) ℤ _ _ ?_
    rw [hπ', Category.assoc, Category.assoc]
    congr 1
    rw [← Category.assoc, ← opensι_quotientπ σ V hVs hVa hVmem x,
      ← Category.assoc, ← opensι_quotientπ σ V hVs hVa hVmem x,
      Category.assoc, Category.assoc, H]
  exact (quotientGlueData σ V hVs hVa).openCover.hom_ext _ _ fun x => key x

omit [IsAffineHom (pullback.diagonal (terminal.from X))] in
/-- The per-chart descent of an invariant morphism. -/
private theorem exists_chart_lift {Y : Scheme.{u}} (F : X ⟶ Y)
    (hF : ∀ g : G, σ.hom g ≫ F = F) (x : X) :
    ∃ qx : σ.localQuotient (hVs x) ⟶ Y,
      σ.localQuotientπ (hVs x) (hVa x) ≫ qx = (V x).ι ≫ F := by
  letI := σ.gammaMulSemiringAction (hVs x)
  have hres : ∀ g : G, (σ.hom g).resLE (V x) (V x) ((hVs x).le_preimage g) ≫
      ((V x).ι ≫ F) = (V x).ι ≫ F := by
    intro g
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hF g]
  obtain ⟨qx, hqx⟩ := exists_invariantsπ_lift G ↑Γ(X, V x) ℤ
    ((hVa x).isoSpec.inv ≫ (V x).ι ≫ F)
    (fun g => by
      rw [specSMul_isoSpec_inv_assoc σ (hVs x) (hVa x) g, hres g])
  refine ⟨qx, ?_⟩
  rw [localQuotientπ_def, Category.assoc, hqx, ← Category.assoc, Iso.hom_inv_id,
    Category.id_comp]

omit [IsAffineHom (pullback.diagonal (terminal.from X))] in
/-- A chart descent `qxk` of `V k`, pulled back through the local quotient of a
smaller stable affine open `W ≤ V k`, is the inclusion `W ↪ X` followed by `F`.
This is the `qx`-level refinement of `localQuotientπ_localQuotientMap`. -/
private theorem localQuotientπ_localQuotientMap_qx {Y : Scheme.{u}} (F : X ⟶ Y)
    {W : X.Opens} (hW : σ.IsStableOpen W) (hWa : IsAffineOpen W) (k : X)
    (hWk : W ≤ V k) (qxk : σ.localQuotient (hVs k) ⟶ Y)
    (hqxk : σ.localQuotientπ (hVs k) (hVa k) ≫ qxk = (V k).ι ≫ F) :
    σ.localQuotientπ hW hWa ≫
        σ.localQuotientMap hW hWa (hVs k) (hVa k) hWk ≫ qxk =
      W.ι ≫ F := by
  rw [← Category.assoc, localQuotientπ_localQuotientMap σ hW hWa (hVs k) (hVa k) hWk,
    Category.assoc, hqxk, ← Category.assoc]
  congr 1
  exact Scheme.homOfLE_ι X hWk

/-- **Overlap agreement of the chart descents**: over the overlap `V i ⊓ V j` the
two chart descents `qx i` and `qx j` agree, after the glue transition `glueT`. -/
private theorem qx_overlap_comm {Y : Scheme.{u}} (F : X ⟶ Y)
    (qx : ∀ x, σ.localQuotient (hVs x) ⟶ Y)
    (hqx : ∀ x, σ.localQuotientπ (hVs x) (hVa x) ≫ qx x = (V x).ι ≫ F) (i j : X) :
    σ.localQuotientMap ((hVs i).inf (hVs j)) ((hVa i).inf (hVa j))
          (hVs i) (hVa i) inf_le_left ≫ qx i =
      glueT σ V hVs hVa i j ≫
        σ.localQuotientMap ((hVs j).inf (hVs i)) ((hVa j).inf (hVa i))
          (hVs j) (hVa j) inf_le_left ≫ qx j := by
  letI := σ.gammaMulSemiringAction ((hVs i).inf (hVs j))
  have hπ' : invariantsπ G ↑Γ(X, V i ⊓ V j) ℤ =
      ((hVa i).inf (hVa j)).isoSpec.inv ≫
        σ.localQuotientπ ((hVs i).inf (hVs j)) ((hVa i).inf (hVa j)) := by
    rw [localQuotientπ_def, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  refine invariantsπ_hom_ext G ↑Γ(X, V i ⊓ V j) ℤ _ _ ?_
  rw [hπ', Category.assoc, Category.assoc]
  congr 1
  show σ.localQuotientπ ((hVs i).inf (hVs j)) ((hVa i).inf (hVa j)) ≫
      σ.localQuotientMap ((hVs i).inf (hVs j)) ((hVa i).inf (hVa j))
        (hVs i) (hVa i) inf_le_left ≫ qx i =
    σ.localQuotientπ ((hVs i).inf (hVs j)) ((hVa i).inf (hVa j)) ≫
      glueT σ V hVs hVa i j ≫
        σ.localQuotientMap ((hVs j).inf (hVs i)) ((hVa j).inf (hVa i))
          (hVs j) (hVa j) inf_le_left ≫ qx j
  rw [localQuotientπ_localQuotientMap_qx σ V hVs hVa F ((hVs i).inf (hVs j))
        ((hVa i).inf (hVa j)) i inf_le_left (qx i) (hqx i),
    localQuotientMap_trans_assoc σ ((hVs i).inf (hVs j)) ((hVa i).inf (hVa j))
      ((hVs j).inf (hVs i)) ((hVa j).inf (hVa i)) (hVs j) (hVa j)
      (le_inf inf_le_right inf_le_left) inf_le_left,
    localQuotientπ_localQuotientMap_qx σ V hVs hVa F ((hVs i).inf (hVs j))
      ((hVa i).inf (hVa j)) j inf_le_right (qx j) (hqx j)]

/-- **Compatibility of the chart descents over the glue overlaps**: the chart
descents `qx i`, `qx j` agree after pulling back along the glue-data inclusions,
so they glue to a single morphism out of the quotient (`glueMorphisms`). -/
private theorem qx_glueData_compat {Y : Scheme.{u}} (F : X ⟶ Y)
    (qx : ∀ x, σ.localQuotient (hVs x) ⟶ Y)
    (hqx : ∀ x, σ.localQuotientπ (hVs x) (hVa x) ≫ qx x = (V x).ι ≫ F) (i j : X) :
    pullback.fst ((quotientGlueData σ V hVs hVa).ι i)
          ((quotientGlueData σ V hVs hVa).ι j) ≫ qx i =
      pullback.snd _ _ ≫ qx j := by
  obtain ⟨ℓ, hℓ₁, hℓ₂⟩ :
      ∃ ℓ : pullback ((quotientGlueData σ V hVs hVa).ι i)
          ((quotientGlueData σ V hVs hVa).ι j) ⟶
        σ.localQuotient ((hVs i).inf (hVs j)),
        ℓ ≫ σ.localQuotientMap ((hVs i).inf (hVs j)) ((hVa i).inf (hVa j))
            (hVs i) (hVa i) inf_le_left = pullback.fst _ _ ∧
        ℓ ≫ glueT σ V hVs hVa i j ≫
            σ.localQuotientMap ((hVs j).inf (hVs i)) ((hVa j).inf (hVa i))
              (hVs j) (hVa j) inf_le_left = pullback.snd _ _ := by
    obtain ⟨ℓ, h₁, h₂⟩ := PullbackCone.IsLimit.lift'
      ((quotientGlueData σ V hVs hVa).vPullbackConeIsLimit i j)
      (pullback.fst ((quotientGlueData σ V hVs hVa).ι i)
        ((quotientGlueData σ V hVs hVa).ι j))
      (pullback.snd _ _) pullback.condition
    exact ⟨ℓ, h₁, h₂⟩
  rw [← hℓ₁, ← hℓ₂, Category.assoc, qx_overlap_comm σ V hVs hVa F qx hqx i j,
    Category.assoc, Category.assoc]

/-- **Existence of descent along the quotient projection** (T-Q5d contract,
part 3). -/
theorem exists_quotientπ_lift {Y : Scheme.{u}} (F : X ⟶ Y)
    (hF : ∀ g : G, σ.hom g ≫ F = F) :
    ∃ q : σ.quotient V hVs hVa ⟶ Y, σ.quotientπ V hVs hVa hVmem ≫ q = F := by
  choose qx hqx using exists_chart_lift σ V hVs hVa F hF
  refine ⟨(quotientGlueData σ V hVs hVa).openCover.glueMorphisms (fun x => qx x)
    (fun i j => qx_glueData_compat σ V hVs hVa F qx hqx i j), ?_⟩
  have hfac : ∀ x' : X, (V x').ι ≫ σ.quotientπ V hVs hVa hVmem ≫
      (quotientGlueData σ V hVs hVa).openCover.glueMorphisms (fun x => qx x)
        (fun i j => qx_glueData_compat σ V hVs hVa F qx hqx i j) = (V x').ι ≫ F := by
    intro x'
    have hι : (quotientGlueData σ V hVs hVa).ι x' ≫
        (quotientGlueData σ V hVs hVa).openCover.glueMorphisms (fun x => qx x)
          (fun i j => qx_glueData_compat σ V hVs hVa F qx hqx i j) = qx x' :=
      (quotientGlueData σ V hVs hVa).openCover.ι_glueMorphisms
        (fun x => qx x) (fun i j => qx_glueData_compat σ V hVs hVa F qx hqx i j) x'
    rw [← Category.assoc, opensι_quotientπ σ V hVs hVa hVmem x', Category.assoc,
      hι, hqx x']
  exact (atlasCover V hVmem).hom_ext _ _ fun x => hfac x

/-- The **base-changed action** on `pullback (quotientπ) j`: `g ∈ G` acts through the
`X`-factor (well-defined because `σ.hom g ≫ quotientπ = quotientπ`, `hom_quotientπ`).
The global-`quotientπ` analogue of `AffineQuotient.pullbackSpecSMul`. -/
noncomputable def pullbackQuotientπSMul {W : Scheme.{u}}
    (j : W ⟶ σ.quotient V hVs hVa) (g : G) :
    Limits.pullback (σ.quotientπ V hVs hVa hVmem) j ⟶
      Limits.pullback (σ.quotientπ V hVs hVa hVmem) j :=
  Limits.pullback.lift (Limits.pullback.fst _ _ ≫ σ.hom g) (Limits.pullback.snd _ _)
    (by rw [Category.assoc, hom_quotientπ]; exact Limits.pullback.condition)

@[reassoc (attr := simp)]
theorem pullbackQuotientπSMul_fst {W : Scheme.{u}}
    (j : W ⟶ σ.quotient V hVs hVa) (g : G) :
    σ.pullbackQuotientπSMul V hVs hVa hVmem j g ≫
        Limits.pullback.fst (σ.quotientπ V hVs hVa hVmem) j =
      Limits.pullback.fst (σ.quotientπ V hVs hVa hVmem) j ≫ σ.hom g :=
  Limits.pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pullbackQuotientπSMul_snd {W : Scheme.{u}}
    (j : W ⟶ σ.quotient V hVs hVa) (g : G) :
    σ.pullbackQuotientπSMul V hVs hVa hVmem j g ≫
        Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem) j =
      Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem) j :=
  Limits.pullback.lift_snd _ _ _

/-- The open image of the `i`-th piece of a glue data. -/
private noncomputable def chartOpens (D : Scheme.GlueData.{u}) (i : D.J) : D.glued.Opens :=
  (D.ι i).opensRange

private theorem mem_chartOpens_iff (D : Scheme.GlueData.{u}) (i : D.J) (q : D.glued) :
    q ∈ chartOpens D i ↔ ∃ p, D.ι i p = q := Iff.rfl

private theorem isAffineOpen_chartOpens (D : Scheme.GlueData.{u}) (i : D.J)
    [IsAffine (D.U i)] : IsAffineOpen (chartOpens D i) :=
  isAffineOpen_opensRange (D.ι i)

/-- **The `x`-th chart of the quotient**: the open image of the local quotient
`Spec Γ(X, V x)ᴳ` inside `X/G`. -/
noncomputable def quotientChart (x : X) : (σ.quotient V hVs hVa).Opens :=
  chartOpens (quotientGlueData σ V hVs hVa) x

theorem mem_quotientChart_iff (x : X) (q : σ.quotient V hVs hVa) :
    q ∈ σ.quotientChart V hVs hVa x ↔
      ∃ p, (quotientGlueData σ V hVs hVa).ι x p = q :=
  mem_chartOpens_iff _ _ _

/-- The quotient charts are affine — they are copies of `Spec Γ(X, V x)ᴳ`. -/
theorem isAffineOpen_quotientChart (x : X) :
    IsAffineOpen (σ.quotientChart V hVs hVa x) :=
  isAffineOpen_chartOpens (quotientGlueData σ V hVs hVa) x

/-- The quotient charts cover `X/G`. -/
theorem iSup_quotientChart_eq_top :
    ⨆ x : X, σ.quotientChart V hVs hVa x = ⊤ := by
  refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun q => ?_)
  obtain ⟨x, p, rfl⟩ := (quotientGlueData σ V hVs hVa).ι_jointly_surjective q
  rw [TopologicalSpace.Opens.coe_iSup]
  exact Set.mem_iUnion.mpr ⟨x, (σ.mem_quotientChart_iff V hVs hVa x _).mpr ⟨p, rfl⟩⟩

/-- The quotient projection, computed on a chart. -/
theorem quotientπ_apply_ι (x : X) (w : (V x : Scheme.{u})) :
    σ.quotientπ V hVs hVa hVmem ((V x).ι w) =
      (quotientGlueData σ V hVs hVa).ι x (σ.localQuotientπ (hVs x) (hVa x) w) := by
  rw [← Scheme.Hom.comp_apply, opensι_quotientπ σ V hVs hVa hVmem x, Scheme.Hom.comp_apply]

/-- **The charts pull back to the atlas** (T-Q5d contract, part 5): the preimage of the `x`-th
quotient chart under `X ⟶ X/G` is exactly the stable affine open `V x`.

This is what makes the quotient *local on the base*: over the chart `Spec Γ(X,V x)ᴳ`, the map
`X ⟶ X/G` restricts to the affine map `V x ⟶ Spec Γ(X,V x)ᴳ`. The `⊆` direction is where
stability of the atlas is used, through `localQuotientπ_mem_imageOpens_iff` (the fibres of
`invariantsπ` are the `G`-orbits, and `V x` is `G`-stable, so an orbit meets `V x` iff it lies
in `V x`). -/
theorem quotientπ_preimage_quotientChart (x : X) :
    σ.quotientπ V hVs hVa hVmem ⁻¹ᵁ σ.quotientChart V hVs hVa x = V x := by
  refine TopologicalSpace.Opens.ext (Set.ext fun e => ⟨fun he => ?_, fun he => ?_⟩)
  · obtain ⟨q, hq⟩ := (σ.mem_quotientChart_iff V hVs hVa x _).mp he
    have hπe : σ.quotientπ V hVs hVa hVmem e =
        (quotientGlueData σ V hVs hVa).ι e
          (σ.localQuotientπ (hVs e) (hVa e) ⟨e, hVmem e⟩) :=
      quotientπ_apply_ι σ V hVs hVa hVmem e ⟨e, hVmem e⟩
    rw [hπe] at hq
    obtain ⟨z, -, hz2⟩ :=
      ((quotientGlueData σ V hVs hVa).ι_eq_iff x e q
        (σ.localQuotientπ (hVs e) (hVa e) ⟨e, hVmem e⟩)).mp hq
    have hmem : σ.localQuotientπ (hVs e) (hVa e) ⟨e, hVmem e⟩ ∈
        Set.range ⇑(σ.localQuotientMap ((hVs e).inf (hVs x)) ((hVa e).inf (hVa x))
          (hVs e) (hVa e) inf_le_left) := ⟨_, hz2⟩
    rw [range_localQuotientMap σ inf_le_left (hVa e) ((hVs e).inf (hVs x))
      ((hVa e).inf (hVa x)) (hVs e)] at hmem
    exact ((localQuotientπ_mem_imageOpens_iff σ inf_le_left (hVa e)
      ((hVs e).inf (hVs x)) (hVs e) ⟨e, hVmem e⟩).mp hmem).2
  · exact (σ.mem_quotientChart_iff V hVs hVa x _).mpr
      ⟨σ.localQuotientπ (hVs x) (hVa x) ⟨e, he⟩,
        (quotientπ_apply_ι σ V hVs hVa hVmem x ⟨e, he⟩).symm⟩

/-- **The quotient projection is surjective.** -/
theorem quotientπ_surjective :
    Function.Surjective ⇑(σ.quotientπ V hVs hVa hVmem) := by
  intro q
  obtain ⟨x, p, rfl⟩ := (quotientGlueData σ V hVs hVa).ι_jointly_surjective q
  obtain ⟨w, rfl⟩ := localQuotientπ_surjective σ (hVs x) (hVa x) p
  exact ⟨(V x).ι w, quotientπ_apply_ι σ V hVs hVa hVmem x w⟩

private theorem isIso_ι_of_chartOpens_eq_top (D : Scheme.GlueData.{u}) (i : D.J)
    (h : chartOpens D i = ⊤) : IsIso (D.ι i) :=
  isIso_of_isOpenImmersion_of_opensRange_eq_top _ h

include hVmem in
/-- A chart of the whole space is a chart of the whole quotient. -/
theorem quotientChart_eq_top (x : X) (hx : V x = ⊤) :
    σ.quotientChart V hVs hVa x = ⊤ := by
  refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun q => ?_)
  obtain ⟨e, rfl⟩ := σ.quotientπ_surjective V hVs hVa hVmem q
  have he : e ∈ σ.quotientπ V hVs hVa hVmem ⁻¹ᵁ σ.quotientChart V hVs hVa x := by
    rw [quotientπ_preimage_quotientChart σ V hVs hVa hVmem x, hx]
    trivial
  exact he

include hVmem in
/-- **The quotient of an affine scheme is affine** (T-Q3): if some atlas member is all of `X`
— e.g. the constant `⊤` atlas of an affine `X` — then `X/G ≅ Spec Γ(X, ⊤)ᴳ`. -/
theorem isIso_quotientGlueData_ι (x : X) (hx : V x = ⊤) :
    IsIso ((quotientGlueData σ V hVs hVa).ι x) :=
  isIso_ι_of_chartOpens_eq_top (quotientGlueData σ V hVs hVa) x
    (σ.quotientChart_eq_top V hVs hVa hVmem x hx)

include hVmem in
theorem isAffine_quotient (x : X) (hx : V x = ⊤) :
    IsAffine (σ.quotient V hVs hVa) := by
  haveI := σ.isIso_quotientGlueData_ι V hVs hVa hVmem x hx
  exact (IsAffine.iff_of_isIso ((quotientGlueData σ V hVs hVa).ι x)).mp inferInstance

/-- The `i`-th piece of a glue data is isomorphic to its open image. -/
private noncomputable def glueChartIso (D : Scheme.GlueData.{u}) (i : D.J) :
    D.U i ≅ (chartOpens D i : Scheme.{u}) :=
  IsOpenImmersion.isoOfRangeEq (D.ι i) (chartOpens D i).ι
    (Scheme.Opens.range_ι (chartOpens D i)).symm

private theorem glueChartIso_hom_ι (D : Scheme.GlueData.{u}) (i : D.J) :
    (glueChartIso D i).hom ≫ (chartOpens D i).ι = D.ι i :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The local quotient `Spec Γ(X, V x)ᴳ` *is* the `x`-th chart of `X/G`. -/
noncomputable def quotientChartIso (x : X) :
    σ.localQuotient (hVs x) ≅ (σ.quotientChart V hVs hVa x : Scheme.{u}) :=
  glueChartIso (quotientGlueData σ V hVs hVa) x

include hVmem in
theorem localQuotientπ_quotientChartIso (x : X) :
    σ.localQuotientπ (hVs x) (hVa x) ≫ (σ.quotientChartIso V hVs hVa x).hom ≫
        (σ.quotientChart V hVs hVa x).ι =
      (V x).ι ≫ σ.quotientπ V hVs hVa hVmem := by
  show σ.localQuotientπ (hVs x) (hVa x) ≫
      (glueChartIso (quotientGlueData σ V hVs hVa) x).hom ≫
        (chartOpens (quotientGlueData σ V hVs hVa) x).ι = _
  rw [glueChartIso_hom_ι (quotientGlueData σ V hVs hVa) x,
    opensι_quotientπ σ V hVs hVa hVmem x]

include hVmem in
/-- **The atlas square is cartesian**: over the chart `Spec Γ(X, V x)ᴳ ⊆ X/G`, the quotient
projection `X ⟶ X/G` *is* the local quotient `V x ⟶ Spec Γ(X, V x)ᴳ`.

This is the local-to-global engine for the quotient: any property of `X ⟶ X/G` that is
Zariski-local at the target can be checked on the local quotients, where it is a statement about
`Aᴳ ↪ A` (finiteness, étaleness, the torsor property — the T-Q2 package). -/
theorem isPullback_quotientπ_quotientChart (x : X) :
    IsPullback ((V x).ι)
      (σ.localQuotientπ (hVs x) (hVa x) ≫ (σ.quotientChartIso V hVs hVa x).hom)
      (σ.quotientπ V hVs hVa hVmem) (σ.quotientChart V hVs hVa x).ι := by
  have hW : σ.quotientπ V hVs hVa hVmem ⁻¹ᵁ σ.quotientChart V hVs hVa x = V x :=
    quotientπ_preimage_quotientChart σ V hVs hVa hVmem x
  have h := isPullback_morphismRestrict (σ.quotientπ V hVs hVa hVmem)
    (σ.quotientChart V hVs hVa x)
  refine h.flip.of_iso (X.isoOfEq hW) (Iso.refl X) (Iso.refl _) (Iso.refl _)
    (by simp) ?_ (by simp) (by simp)
  rw [Iso.refl_hom, Category.comp_id,
    ← cancel_mono (σ.quotientChart V hVs hVa x).ι, morphismRestrict_ι, Category.assoc,
    Category.assoc, localQuotientπ_quotientChartIso σ V hVs hVa hVmem x, ← Category.assoc,
    Scheme.isoOfEq_hom_ι]

include hVmem in
/-- The restriction of the quotient projection over the `x`-th chart *is* the local quotient. -/
theorem morphismRestrict_quotientπ (x : X) :
    σ.quotientπ V hVs hVa hVmem ∣_ σ.quotientChart V hVs hVa x =
      (X.isoOfEq (quotientπ_preimage_quotientChart σ V hVs hVa hVmem x)).hom ≫
        σ.localQuotientπ (hVs x) (hVa x) ≫ (σ.quotientChartIso V hVs hVa x).hom := by
  rw [← cancel_mono (σ.quotientChart V hVs hVa x).ι, morphismRestrict_ι, Category.assoc,
    Category.assoc, localQuotientπ_quotientChartIso σ V hVs hVa hVmem x, ← Category.assoc,
    Scheme.isoOfEq_hom_ι]

include hVmem in
/-- **The quotient projection is an affine morphism** (T-Q5d contract, part 6). Over the chart
`Spec Γ(X, V x)ᴳ` the projection restricts to `V x ⟶ Spec Γ(X, V x)ᴳ`, an affine scheme over an
affine scheme; the charts cover `X/G`, and `IsAffineHom` is Zariski-local at the target. -/
instance isAffineHom_quotientπ : IsAffineHom (σ.quotientπ V hVs hVa hVmem) := by
  refine isAffineHom_of_forall_exists_isAffineOpen _ fun q => ?_
  obtain ⟨e, rfl⟩ := σ.quotientπ_surjective V hVs hVa hVmem q
  refine ⟨σ.quotientChart V hVs hVa e, ?_, σ.isAffineOpen_quotientChart V hVs hVa e, ?_⟩
  · have : e ∈ σ.quotientπ V hVs hVa hVmem ⁻¹ᵁ σ.quotientChart V hVs hVa e := by
      rw [quotientπ_preimage_quotientChart σ V hVs hVa hVmem e]
      exact hVmem e
    exact this
  · rw [quotientπ_preimage_quotientChart σ V hVs hVa hVmem e]
    exact hVa e

include hVa in
omit [Finite G] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))] in
/-- Geometric freeness on `X` restricts, through the affine identification of a stable
affine chart, to freeness of the section-ring action on `Spec Γ(X, V x)`: a `g`-fixed
`T`-point of `Spec Γ(X, V x)` is a `g`-fixed `T`-point of `X`. -/
private theorem specSMul_free_of_free
    (hfree : ∀ {T : Scheme.{u}} (t : T ⟶ X) (g : G), g ≠ 1 → t ≫ σ.hom g = t → IsEmpty T)
    (x : X) :
    letI := σ.gammaMulSemiringAction (hVs x)
    ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of ↑Γ(X, V x))) (g : G), g ≠ 1 →
      t ≫ specSMul g = t → IsEmpty T := by
  letI := σ.gammaMulSemiringAction (hVs x)
  intro T t g hg ht
  refine hfree (t ≫ (hVa x).isoSpec.inv ≫ (V x).ι) g hg ?_
  calc (t ≫ (hVa x).isoSpec.inv ≫ (V x).ι) ≫ σ.hom g
      = t ≫ (hVa x).isoSpec.inv ≫ (V x).ι ≫ σ.hom g := by
        rw [Category.assoc, Category.assoc]
    _ = t ≫ (hVa x).isoSpec.inv ≫
          (σ.hom g).resLE (V x) (V x) ((hVs x).le_preimage g) ≫ (V x).ι := by
        rw [Scheme.Hom.resLE_comp_ι]
    _ = t ≫ ((hVa x).isoSpec.inv ≫
          (σ.hom g).resLE (V x) (V x) ((hVs x).le_preimage g)) ≫ (V x).ι := by
        rw [Category.assoc]
    _ = t ≫ (specSMul g ≫ (hVa x).isoSpec.inv) ≫ (V x).ι := by
        rw [specSMul_isoSpec_inv σ (hVs x) (hVa x) g]
    _ = (t ≫ specSMul g) ≫ (hVa x).isoSpec.inv ≫ (V x).ι := by
        rw [Category.assoc, Category.assoc]
    _ = t ≫ (hVa x).isoSpec.inv ≫ (V x).ι := by rw [ht]

include hVmem in
/-- **The quotient projection of a free action is flat** (chart-locally `Bᴳ ↪ B` with `B`
projective over `Bᴳ` — KM A7.1.1's finiteness/projectivity package). -/
private theorem flat_quotientπ
    (hfree : ∀ {T : Scheme.{u}} (t : T ⟶ X) (g : G), g ≠ 1 → t ≫ σ.hom g = t → IsEmpty T) :
    Flat (σ.quotientπ V hVs hVa hVmem) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @Flat) (σ.quotientChart V hVs hVa)
    (σ.iSup_quotientChart_eq_top V hVs hVa) fun x => ?_
  rw [morphismRestrict_quotientπ σ V hVs hVa hVmem x,
    MorphismProperty.cancel_left_of_respectsIso (P := @Flat),
    MorphismProperty.cancel_right_of_respectsIso (P := @Flat),
    localQuotientπ_eq σ (hVs x) (hVa x),
    MorphismProperty.cancel_left_of_respectsIso (P := @Flat)]
  letI := σ.gammaMulSemiringAction (hVs x)
  have halg : IsFreeAlgebraAction G ℤ ↑Γ(X, V x) :=
    isFreeAlgebraAction_of_specSMul_free G ↑Γ(X, V x) ℤ
      (σ.specSMul_free_of_free V hVs hVa hfree x)
  haveI : SMulCommClass ℤ G ↑Γ(X, V x) := SMulCommClass.symm G ℤ ↑Γ(X, V x)
  haveI : Module.Finite (FixedPoints.subalgebra ℤ ↑Γ(X, V x) G) ↑Γ(X, V x) :=
    Module.Finite.of_isFreeAlgebraAction G ℤ _ halg
  haveI : Module.Projective (FixedPoints.subalgebra ℤ ↑Γ(X, V x) G) ↑Γ(X, V x) :=
    Module.Projective.of_isFreeAlgebraAction G ℤ _ halg
  haveI : Module.Flat (FixedPoints.subalgebra ℤ ↑Γ(X, V x) G) ↑Γ(X, V x) :=
    Module.Flat.of_projective
  rw [invariantsπ, AlgebraicGeometry.Flat.SpecMap_iff, CommRingCat.hom_ofHom,
    RingHom.flat_algebraMap_iff]
  infer_instance

include hVmem in
/-- For a FREE action, the base change of the quotient projection along ANY morphism is
an epimorphism — uniqueness of descent over an arbitrary base. -/
theorem epi_pullback_snd_quotientπ
    (hfree : ∀ {T : Scheme.{u}} (t : T ⟶ X) (g : G), g ≠ 1 → t ≫ σ.hom g = t → IsEmpty T)
    {W : Scheme.{u}} (j : W ⟶ σ.quotient V hVs hVa) :
    Epi (Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem) j) := by
  haveI : Flat (σ.quotientπ V hVs hVa hVmem) := σ.flat_quotientπ V hVs hVa hVmem hfree
  haveI : Surjective (σ.quotientπ V hVs hVa hVmem) :=
    ⟨σ.quotientπ_surjective V hVs hVa hVmem⟩
  haveI : Surjective (Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem) j) :=
    MorphismProperty.pullback_snd _ _ ‹Surjective (σ.quotientπ V hVs hVa hVmem)›
  exact Flat.epi_of_flat_of_surjective _

include hVmem in
/-- The comparison morphism between base changes of `quotientπ` (the `quotientπ`-level
`AffineQuotient.pullbackRes`). -/
private noncomputable def pullbackResQ {W' W'' : Scheme.{u}}
    (j'' : W'' ⟶ σ.quotient V hVs hVa) (w : W' ⟶ σ.quotient V hVs hVa)
    (u : W' ⟶ W'') (hw : w = u ≫ j'') :
    Limits.pullback (σ.quotientπ V hVs hVa hVmem) w ⟶
      Limits.pullback (σ.quotientπ V hVs hVa hVmem) j'' :=
  Limits.pullback.map _ _ _ _ (𝟙 _) u (𝟙 _) (by simp) (by rw [Category.comp_id, hw])

include hVmem in
@[reassoc]
private theorem pullbackResQ_fst {W' W'' : Scheme.{u}}
    (j'' : W'' ⟶ σ.quotient V hVs hVa) (w : W' ⟶ σ.quotient V hVs hVa)
    (u : W' ⟶ W'') (hw : w = u ≫ j'') :
    σ.pullbackResQ V hVs hVa hVmem j'' w u hw ≫
        Limits.pullback.fst (σ.quotientπ V hVs hVa hVmem) j'' =
      Limits.pullback.fst (σ.quotientπ V hVs hVa hVmem) w :=
  (Limits.pullback.lift_fst _ _ _).trans (Category.comp_id _)

include hVmem in
@[reassoc]
private theorem pullbackResQ_snd {W' W'' : Scheme.{u}}
    (j'' : W'' ⟶ σ.quotient V hVs hVa) (w : W' ⟶ σ.quotient V hVs hVa)
    (u : W' ⟶ W'') (hw : w = u ≫ j'') :
    σ.pullbackResQ V hVs hVa hVmem j'' w u hw ≫
        Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem) j'' =
      Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem) w ≫ u :=
  Limits.pullback.lift_snd _ _ _

include hVmem in
/-- The comparison morphisms intertwine the base-changed actions. -/
private theorem pullbackQuotientπSMul_pullbackResQ {W' W'' : Scheme.{u}}
    (j'' : W'' ⟶ σ.quotient V hVs hVa) (w : W' ⟶ σ.quotient V hVs hVa)
    (u : W' ⟶ W'') (hw : w = u ≫ j'') (g : G) :
    σ.pullbackQuotientπSMul V hVs hVa hVmem w g ≫
        σ.pullbackResQ V hVs hVa hVmem j'' w u hw =
      σ.pullbackResQ V hVs hVa hVmem j'' w u hw ≫
        σ.pullbackQuotientπSMul V hVs hVa hVmem j'' g := by
  refine Limits.pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, pullbackResQ_fst, pullbackResQ_fst_assoc,
      pullbackQuotientπSMul_fst]
  · simp only [Category.assoc, pullbackResQ_snd, pullbackQuotientπSMul_snd,
      pullbackQuotientπSMul_snd_assoc]

include hVmem in
/-- **The chart step of free base change**: if the base map factors through the `x`-th
chart of the quotient, invariant morphisms out of the base change descend. The chart is
`Spec Γ(X, V x)ᴳ`, over which `quotientπ` restricts to the local `invariantsπ` (the atlas
square `isPullback_quotientπ_quotientChart`), so this is exactly the free-action affine
engine `exists_invariantsπ_lift_baseChange_of_free` ([A711-BC] at ground `Γᴳ`) transported
through the pasted pullback. -/
private theorem exists_quotientπ_lift_baseChange_of_factors
    (hfree : ∀ {T : Scheme.{u}} (t : T ⟶ X) (g : G), g ≠ 1 → t ≫ σ.hom g = t → IsEmpty T)
    {WT Y : Scheme.{u}} (x : X) (wq : WT ⟶ σ.quotient V hVs hVa)
    (wc : WT ⟶ (σ.quotientChart V hVs hVa x : Scheme.{u}))
    (hw : wq = wc ≫ (σ.quotientChart V hVs hVa x).ι)
    (F : Limits.pullback (σ.quotientπ V hVs hVa hVmem) wq ⟶ Y)
    (hF : ∀ g : G, σ.pullbackQuotientπSMul V hVs hVa hVmem wq g ≫ F = F) :
    ∃ q : WT ⟶ Y, Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem) wq ≫ q = F := by
  classical
  letI := σ.gammaMulSemiringAction (hVs x)
  -- the base map into the local quotient `Spec Γ(X, V x)ᴳ`
  set jS : WT ⟶ σ.localQuotient (hVs x) :=
    wc ≫ (σ.quotientChartIso V hVs hVa x).inv with hjS
  -- the pasted pullback: `pullback (invariantsπ) jS` is the base change of `quotientπ`
  have sq1 : IsPullback ((hVa x).isoSpec.inv) (invariantsπ G ↑Γ(X, V x) ℤ)
      (σ.localQuotientπ (hVs x) (hVa x)) (𝟙 (σ.localQuotient (hVs x))) := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [Category.comp_id, localQuotientπ_eq σ (hVs x) (hVa x), Iso.inv_hom_id_assoc]
  have sq2 : IsPullback (𝟙 ((V x : Scheme.{u}))) (σ.localQuotientπ (hVs x) (hVa x))
      (σ.localQuotientπ (hVs x) (hVa x) ≫ (σ.quotientChartIso V hVs hVa x).hom)
      ((σ.quotientChartIso V hVs hVa x).hom) := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [Category.id_comp]
  have hpaste := ((IsPullback.of_hasPullback (invariantsπ G ↑Γ(X, V x) ℤ)
      jS).paste_horiz ((sq1.paste_horiz sq2).paste_horiz
        (σ.isPullback_quotientπ_quotientChart V hVs hVa hVmem x)))
  have htop : (((hVa x).isoSpec.inv ≫ 𝟙 (V x : Scheme.{u})) ≫ (V x).ι) =
      (hVa x).isoSpec.inv ≫ (V x).ι := by
    rw [Category.comp_id]
  have hbot : ((𝟙 (σ.localQuotient (hVs x)) ≫ (σ.quotientChartIso V hVs hVa x).hom) ≫
      (σ.quotientChart V hVs hVa x).ι) =
      (σ.quotientChartIso V hVs hVa x).hom ≫ (σ.quotientChart V hVs hVa x).ι := by
    rw [Category.id_comp]
  rw [htop, hbot] at hpaste
  have hbot2 : jS ≫ (σ.quotientChartIso V hVs hVa x).hom ≫
      (σ.quotientChart V hVs hVa x).ι = wq := by
    rw [hjS, Category.assoc, Iso.inv_hom_id_assoc, ← hw]
  rw [hbot2] at hpaste
  -- the comparison iso and its projections
  set E := hpaste.isoPullback with hE
  have hEfst : E.hom ≫ Limits.pullback.fst (σ.quotientπ V hVs hVa hVmem) wq =
      Limits.pullback.fst (invariantsπ G ↑Γ(X, V x) ℤ) jS ≫
        (hVa x).isoSpec.inv ≫ (V x).ι := by
    rw [hE]
    exact hpaste.isoPullback_hom_fst
  have hEsnd : E.hom ≫ Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem) wq =
      Limits.pullback.snd (invariantsπ G ↑Γ(X, V x) ℤ) jS := by
    rw [hE]
    exact hpaste.isoPullback_hom_snd
  -- the comparison intertwines the base-changed actions
  have hact : ∀ g : G, E.hom ≫ σ.pullbackQuotientπSMul V hVs hVa hVmem wq g =
      pullbackSpecSMul G ↑Γ(X, V x) ℤ jS g ≫ E.hom := by
    intro g
    refine Limits.pullback.hom_ext ?_ ?_
    · calc (E.hom ≫ σ.pullbackQuotientπSMul V hVs hVa hVmem wq g) ≫
            Limits.pullback.fst (σ.quotientπ V hVs hVa hVmem) wq
          = E.hom ≫ σ.pullbackQuotientπSMul V hVs hVa hVmem wq g ≫
              Limits.pullback.fst (σ.quotientπ V hVs hVa hVmem) wq :=
            Category.assoc _ _ _
        _ = E.hom ≫ Limits.pullback.fst (σ.quotientπ V hVs hVa hVmem) wq ≫ σ.hom g := by
            rw [pullbackQuotientπSMul_fst]
        _ = (E.hom ≫ Limits.pullback.fst (σ.quotientπ V hVs hVa hVmem) wq) ≫ σ.hom g :=
            (Category.assoc _ _ _).symm
        _ = (Limits.pullback.fst (invariantsπ G ↑Γ(X, V x) ℤ) jS ≫
              (hVa x).isoSpec.inv ≫ (V x).ι) ≫ σ.hom g := by rw [hEfst]
        _ = Limits.pullback.fst (invariantsπ G ↑Γ(X, V x) ℤ) jS ≫
              (hVa x).isoSpec.inv ≫ (V x).ι ≫ σ.hom g := by
            rw [Category.assoc, Category.assoc]
        _ = Limits.pullback.fst (invariantsπ G ↑Γ(X, V x) ℤ) jS ≫ (hVa x).isoSpec.inv ≫
              (σ.hom g).resLE (V x) (V x) ((hVs x).le_preimage g) ≫ (V x).ι := by
            rw [Scheme.Hom.resLE_comp_ι]
        _ = Limits.pullback.fst (invariantsπ G ↑Γ(X, V x) ℤ) jS ≫
              ((hVa x).isoSpec.inv ≫
                (σ.hom g).resLE (V x) (V x) ((hVs x).le_preimage g)) ≫ (V x).ι := by
            rw [Category.assoc]
        _ = Limits.pullback.fst (invariantsπ G ↑Γ(X, V x) ℤ) jS ≫
              (specSMul g ≫ (hVa x).isoSpec.inv) ≫ (V x).ι := by
            rw [specSMul_isoSpec_inv σ (hVs x) (hVa x) g]
        _ = (Limits.pullback.fst (invariantsπ G ↑Γ(X, V x) ℤ) jS ≫ specSMul g) ≫
              (hVa x).isoSpec.inv ≫ (V x).ι := by
            rw [Category.assoc, Category.assoc]
        _ = (pullbackSpecSMul G ↑Γ(X, V x) ℤ jS g ≫
              Limits.pullback.fst (invariantsπ G ↑Γ(X, V x) ℤ) jS) ≫
              (hVa x).isoSpec.inv ≫ (V x).ι := by
            rw [pullbackSpecSMul_fst]
        _ = pullbackSpecSMul G ↑Γ(X, V x) ℤ jS g ≫
              (E.hom ≫ Limits.pullback.fst (σ.quotientπ V hVs hVa hVmem) wq) := by
            rw [hEfst, Category.assoc]
        _ = (pullbackSpecSMul G ↑Γ(X, V x) ℤ jS g ≫ E.hom) ≫
              Limits.pullback.fst (σ.quotientπ V hVs hVa hVmem) wq :=
            (Category.assoc _ _ _).symm
    · calc (E.hom ≫ σ.pullbackQuotientπSMul V hVs hVa hVmem wq g) ≫
            Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem) wq
          = E.hom ≫ σ.pullbackQuotientπSMul V hVs hVa hVmem wq g ≫
              Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem) wq :=
            Category.assoc _ _ _
        _ = E.hom ≫ Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem) wq := by
            rw [pullbackQuotientπSMul_snd]
        _ = Limits.pullback.snd (invariantsπ G ↑Γ(X, V x) ℤ) jS := hEsnd
        _ = pullbackSpecSMul G ↑Γ(X, V x) ℤ jS g ≫
              Limits.pullback.snd (invariantsπ G ↑Γ(X, V x) ℤ) jS := by
            rw [pullbackSpecSMul_snd]
        _ = pullbackSpecSMul G ↑Γ(X, V x) ℤ jS g ≫
              (E.hom ≫ Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem) wq) := by
            rw [hEsnd]
        _ = (pullbackSpecSMul G ↑Γ(X, V x) ℤ jS g ≫ E.hom) ≫
              Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem) wq :=
            (Category.assoc _ _ _).symm
  -- transport the invariance and descend via the free-action affine engine
  have hFE : ∀ g : G, pullbackSpecSMul G ↑Γ(X, V x) ℤ jS g ≫ (E.hom ≫ F) = E.hom ≫ F := by
    intro g
    rw [← Category.assoc, ← hact g, Category.assoc, hF g]
  obtain ⟨q, hq⟩ := exists_invariantsπ_lift_baseChange_of_free G ↑Γ(X, V x) ℤ
    (σ.specSMul_free_of_free V hVs hVa hfree x) jS (E.hom ≫ F) hFE
  refine ⟨q, ?_⟩
  rw [← cancel_epi E.hom, ← Category.assoc, hEsnd]
  exact hq

/-- The pullback of the quotient-chart cover along a base map `j : W ⟶ X/G`: the pieces
are `j⁻¹(chart x)`, presented as pullbacks so the chart-factoring is definitional. -/
@[reducible]
private noncomputable def chartCover {W : Scheme.{u}} (j : W ⟶ σ.quotient V hVs hVa) :
    W.OpenCover where
  I₀ := X
  X x := Limits.pullback j (σ.quotientChart V hVs hVa x).ι
  f x := Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun w => ?_, fun x => inferInstance⟩
    have h1 : j w ∈ (⊤ : (σ.quotient V hVs hVa).Opens) := trivial
    rw [← σ.iSup_quotientChart_eq_top V hVs hVa] at h1
    obtain ⟨x, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp h1
    refine ⟨x, ?_⟩
    rw [IsOpenImmersion.range_pullbackFst]
    exact ⟨⟨j w, hx⟩, rfl⟩

private theorem chartCover_f {W : Scheme.{u}} (j : W ⟶ σ.quotient V hVs hVa) (x : X) :
    (σ.chartCover V hVs hVa j).f x =
      Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι := rfl

/-- **[GHB5a] Base change commutes with the quotient for a FREE action** (existence of
descent; KM 7.1.3(3c), the free case — condition (c)). For any base map `j : W ⟶ X/G`,
the base-changed projection `pullback.snd (quotientπ) j : pullback (quotientπ) j ⟶ W`
descends every morphism `F` invariant under the base-changed action.

The freeness hypothesis `hfree` is **essential** for arbitrary (non-flat) `j`: the
chart-local content is `(A ⊗_{R} C)ᴳ = Aᴳ ⊗_{R} C`, which holds *for every* base ring
`C` exactly when the action is free (KM A7.1.2 / [A711-BC]
`fixedPointsBaseChange_bijective_of_isFreeAlgebraAction`); the flatness route
(`exists_invariantsπ_lift_of_isOpenImmersion`, valid for open-immersion = localization
`j`) does not cover `j = pullback.fst f₀ g`, which is a base change of the arbitrary
`g : T ⟶ S` and hence not flat. Proof mirrors `exists_quotientπ_lift`'s glue over
`quotientGlueData`, with the per-chart descent supplied by the free-action affine
base-change engine (from [A711-BC]). Consumed by [GHB5]
`exists_quotient_baseChange_of_free` at `j = pullback.fst f₀ g`. -/
theorem exists_quotientπ_lift_baseChange {W Y : Scheme.{u}}
    (hfree : ∀ {T : Scheme.{u}} (t : T ⟶ X) (g : G), g ≠ 1 →
      t ≫ σ.hom g = t → IsEmpty T)
    (j : W ⟶ σ.quotient V hVs hVa)
    (F : Limits.pullback (σ.quotientπ V hVs hVa hVmem) j ⟶ Y)
    (hF : ∀ g : G, σ.pullbackQuotientπSMul V hVs hVa hVmem j g ≫ F = F) :
    ∃ q : W ⟶ Y, Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem) j ≫ q = F := by
  classical
  -- chart-wise descents of the restricted morphisms
  have hFx : ∀ (x : X) (g : G),
      σ.pullbackQuotientπSMul V hVs hVa hVmem
          (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j) g ≫
        (σ.pullbackResQ V hVs hVa hVmem j
          (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j)
          (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι) rfl ≫ F) =
      σ.pullbackResQ V hVs hVa hVmem j
        (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j)
        (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι) rfl ≫ F := by
    intro x g
    rw [← Category.assoc, pullbackQuotientπSMul_pullbackResQ, Category.assoc, hF g]
  choose qx hqx using fun x : X =>
    σ.exists_quotientπ_lift_baseChange_of_factors V hVs hVa hVmem hfree x
      (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j)
      (Limits.pullback.snd j (σ.quotientChart V hVs hVa x).ι)
      Limits.pullback.condition
      (σ.pullbackResQ V hVs hVa hVmem j
        (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j)
        (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι) rfl ≫ F)
      (hFx x)
  -- gluing compatibility on overlaps, cancelling the (epi) base-changed projection
  have hcompat : ∀ x z : X,
      Limits.pullback.fst ((σ.chartCover V hVs hVa j).f x)
          ((σ.chartCover V hVs hVa j).f z) ≫ qx x =
      Limits.pullback.snd ((σ.chartCover V hVs hVa j).f x)
          ((σ.chartCover V hVs hVa j).f z) ≫ qx z := by
    intro x z
    rw [chartCover_f, chartCover_f]
    have hbase : Limits.pullback.fst (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
          (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι) ≫
          Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j =
        Limits.pullback.snd (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
          (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι) ≫
          Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι ≫ j := by
      rw [← Category.assoc, ← Category.assoc, Limits.pullback.condition]
    have hσρ : σ.pullbackResQ V hVs hVa hVmem
          (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j)
          (Limits.pullback.fst (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
            (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι) ≫
            Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j)
          (Limits.pullback.fst (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
            (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι)) rfl ≫
          σ.pullbackResQ V hVs hVa hVmem j
            (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j)
            (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι) rfl =
        σ.pullbackResQ V hVs hVa hVmem
          (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι ≫ j)
          (Limits.pullback.fst (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
            (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι) ≫
            Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j)
          (Limits.pullback.snd (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
            (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι)) hbase ≫
          σ.pullbackResQ V hVs hVa hVmem j
            (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι ≫ j)
            (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι) rfl := by
      refine Limits.pullback.hom_ext ?_ ?_
      · simp only [Category.assoc, pullbackResQ_fst]
      · simp only [Category.assoc, pullbackResQ_snd, pullbackResQ_snd_assoc]
        rw [Limits.pullback.condition
          (f := Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
          (g := Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι)]
    haveI := σ.epi_pullback_snd_quotientπ V hVs hVa hVmem hfree
      (Limits.pullback.fst (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
        (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι) ≫
        Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j)
    refine (cancel_epi (Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem)
      (Limits.pullback.fst (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
        (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι) ≫
        Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j))).mp ?_
    calc Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem)
          (Limits.pullback.fst (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
            (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι) ≫
            Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j) ≫
          Limits.pullback.fst (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
            (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι) ≫ qx x
        = (Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem)
            (Limits.pullback.fst (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι) ≫
              Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j) ≫
            Limits.pullback.fst (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι)) ≫ qx x :=
          (Category.assoc _ _ _).symm
      _ = (σ.pullbackResQ V hVs hVa hVmem
            (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j)
            (Limits.pullback.fst (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι) ≫
              Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j)
            (Limits.pullback.fst (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι)) rfl ≫
            Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem)
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j)) ≫ qx x := by
          rw [pullbackResQ_snd]
      _ = σ.pullbackResQ V hVs hVa hVmem
            (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j)
            (Limits.pullback.fst (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι) ≫
              Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j)
            (Limits.pullback.fst (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι)) rfl ≫
            Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem)
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j) ≫ qx x :=
          Category.assoc _ _ _
      _ = σ.pullbackResQ V hVs hVa hVmem
            (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j)
            (Limits.pullback.fst (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι) ≫
              Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j)
            (Limits.pullback.fst (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι)) rfl ≫
            σ.pullbackResQ V hVs hVa hVmem j
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j)
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι) rfl ≫ F := by
          rw [hqx x]
      _ = (σ.pullbackResQ V hVs hVa hVmem
            (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j)
            (Limits.pullback.fst (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι) ≫
              Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j)
            (Limits.pullback.fst (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι)) rfl ≫
            σ.pullbackResQ V hVs hVa hVmem j
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j)
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι) rfl) ≫ F :=
          (Category.assoc _ _ _).symm
      _ = (σ.pullbackResQ V hVs hVa hVmem
            (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι ≫ j)
            (Limits.pullback.fst (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι) ≫
              Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j)
            (Limits.pullback.snd (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι)) hbase ≫
            σ.pullbackResQ V hVs hVa hVmem j
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι ≫ j)
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι) rfl) ≫ F := by
          rw [hσρ]
      _ = σ.pullbackResQ V hVs hVa hVmem
            (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι ≫ j)
            (Limits.pullback.fst (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι) ≫
              Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j)
            (Limits.pullback.snd (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι)) hbase ≫
            σ.pullbackResQ V hVs hVa hVmem j
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι ≫ j)
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι) rfl ≫ F :=
          Category.assoc _ _ _
      _ = σ.pullbackResQ V hVs hVa hVmem
            (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι ≫ j)
            (Limits.pullback.fst (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι) ≫
              Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j)
            (Limits.pullback.snd (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι)) hbase ≫
            Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem)
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι ≫ j) ≫ qx z := by
          rw [← hqx z]
      _ = (σ.pullbackResQ V hVs hVa hVmem
            (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι ≫ j)
            (Limits.pullback.fst (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι) ≫
              Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j)
            (Limits.pullback.snd (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι)) hbase ≫
            Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem)
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι ≫ j)) ≫ qx z :=
          (Category.assoc _ _ _).symm
      _ = (Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem)
            (Limits.pullback.fst (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι) ≫
              Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j) ≫
            Limits.pullback.snd (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι)) ≫ qx z := by
          rw [pullbackResQ_snd]
      _ = Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem)
            (Limits.pullback.fst (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι) ≫
              Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j) ≫
            Limits.pullback.snd (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
              (Limits.pullback.fst j (σ.quotientChart V hVs hVa z).ι) ≫ qx z :=
          Category.assoc _ _ _
  refine ⟨(σ.chartCover V hVs hVa j).glueMorphisms qx hcompat, ?_⟩
  -- verify the factorization on a cover of the base change
  refine Scheme.Cover.hom_ext (Scheme.Cover.mkOfCovers (J := X)
    (fun x => Limits.pullback (Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem) j)
      (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι))
    (fun x => Limits.pullback.fst (Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem) j)
      (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι))
    (fun e => by
      have h1 : j ((Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem) j) e) ∈
          (⊤ : (σ.quotient V hVs hVa).Opens) := trivial
      rw [← σ.iSup_quotientChart_eq_top V hVs hVa] at h1
      obtain ⟨x, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp h1
      have h2 : e ∈ Set.range ⇑(Limits.pullback.fst
          (Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem) j)
          (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)) := by
        rw [IsOpenImmersion.range_pullbackFst]
        show (Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem) j) e ∈
          Set.range ⇑(Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)
        rw [IsOpenImmersion.range_pullbackFst]
        exact ⟨⟨j ((Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem) j) e), hx⟩, rfl⟩
      obtain ⟨y', hy'⟩ := h2
      exact ⟨x, y', hy'⟩)
    (fun x => inferInstance)) _ _ fun x : X => ?_
  show Limits.pullback.fst (Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem) j)
      (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι) ≫
      Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem) j ≫
        (σ.chartCover V hVs hVa j).glueMorphisms qx hcompat =
    Limits.pullback.fst (Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem) j)
      (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι) ≫ F
  have hι := (σ.chartCover V hVs hVa j).ι_glueMorphisms qx hcompat x
  rw [chartCover_f] at hι
  rw [← Category.assoc,
    Limits.pullback.condition (f := Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem) j)
      (g := Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι),
    Category.assoc, hι]
  -- compare through the canonical map into the chart base change
  set θ : Limits.pullback (Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem) j)
      (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι) ⟶
      Limits.pullback (σ.quotientπ V hVs hVa hVmem)
        (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j) :=
    Limits.pullback.lift
      (Limits.pullback.fst (Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem) j)
        (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι) ≫
        Limits.pullback.fst (σ.quotientπ V hVs hVa hVmem) j)
      (Limits.pullback.snd (Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem) j)
        (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι))
      (by
        rw [Category.assoc,
          Limits.pullback.condition (f := σ.quotientπ V hVs hVa hVmem) (g := j),
          ← Category.assoc,
          Limits.pullback.condition
            (f := Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem) j)
            (g := Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι),
          Category.assoc])
      with hθ
  have hθsnd : θ ≫ Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem)
      (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j) =
      Limits.pullback.snd (Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem) j)
        (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι) := by
    rw [hθ]
    exact Limits.pullback.lift_snd _ _ _
  have hθρ : θ ≫ σ.pullbackResQ V hVs hVa hVmem j
      (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι ≫ j)
      (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι) rfl =
      Limits.pullback.fst (Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem) j)
        (Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι) := by
    refine Limits.pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullbackResQ_fst, hθ, Limits.pullback.lift_fst]
    · rw [Category.assoc, pullbackResQ_snd, ← Category.assoc, hθsnd,
        Limits.pullback.condition
          (f := Limits.pullback.snd (σ.quotientπ V hVs hVa hVmem) j)
          (g := Limits.pullback.fst j (σ.quotientChart V hVs hVa x).ι)]
  rw [← hθsnd, Category.assoc, hqx x, ← Category.assoc, hθρ]

/-- **The universal property of the quotient** (T-Q5d contract, part 4):
`quotientπ` is the categorical quotient of `X` by `G` — every invariant morphism
factors uniquely through it. -/
theorem existsUnique_quotientπ_lift {Y : Scheme.{u}} (F : X ⟶ Y)
    (hF : ∀ g : G, σ.hom g ≫ F = F) :
    ∃! q : σ.quotient V hVs hVa ⟶ Y, σ.quotientπ V hVs hVa hVmem ≫ q = F := by
  obtain ⟨q, hq⟩ := exists_quotientπ_lift σ V hVs hVa hVmem F hF
  exact ⟨q, hq, fun q' hq' =>
    quotientπ_hom_ext σ V hVs hVa hVmem q' q (hq'.trans hq.symm)⟩

end Glue

end OpenImmersion

end SchemeAction

end AlgebraicGeometry

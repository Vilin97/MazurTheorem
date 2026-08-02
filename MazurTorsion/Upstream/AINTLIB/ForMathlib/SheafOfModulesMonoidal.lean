/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Localization.Monoidal.Basic

/-!
# Towards the monoidal structure on sheaves of modules ([GAP1-W-MONO])

The AINTLIB ModularCurves GAP-1 development, route (b′) (board v10.64/v10.65): equip
`SheafOfModules` with a monoidal structure by localizing the monoidal category of
presheaves of modules at the class of morphisms inverted by sheafification, via
mathlib's `LocalizedMonoidal` machinery. The single load-bearing mathematical leaf is
tensor-stability of that class; everything else is registration plumbing.

* `PresheafOfModules.sheafificationW`: the inverted class.
* `sheafificationW_isLocalization`: the `IsLocalization` registration at `α = 𝟙`
  (reflective case), via `Adjunction.isLocalization`.
* `sheafificationW_iff_isLocallyBijective`: membership = locally injective + locally
  surjective on underlying presheaves of abelian groups (through mathlib's
  `WEqualsLocallyBijective` and the reflection of isomorphisms by `toSheaf`).
* `[GAP1-W-MONO]` (staged): tensor-stability. The locally-surjective half
  (`IsLocallySurjective.tensorHom`) is proven at the level of sections; the
  locally-injective half (`IsLocallyInjective.tensorHom`) is the stalkwise/filtered
  argument (no flatness — stalks of a locally bijective map are isomorphisms) and is
  a registered work-in-progress leaf.

Once the leaf closes, `LocalizedMonoidal (sheafification (𝟙 _)) (sheafificationW _) ε`
with `ε` the sheafified-unit counit iso hands `SheafOfModules` its monoidal structure
with monoidal sheafification — the GAP-1 kernel, tensor-closure of invertible sheaves,
and the Pic-group coherences (board v10.64).
-/

universe v v' u u'

open CategoryTheory MonoidalCategory

namespace PresheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [HasWeakSheafify J AddCommGrpCat.{v}]

/-- The class of morphisms of presheaves of modules inverted by the sheafification
functor: the localizing class for `SheafOfModules`. -/
def sheafificationW : MorphismProperty (PresheafOfModules.{v} R₀) :=
  (MorphismProperty.isomorphisms _).inverseImage (sheafification.{v} α)

lemma sheafificationW_iff {M N : PresheafOfModules.{v} R₀} (f : M ⟶ N) :
    sheafificationW.{v} α f ↔ IsIso ((sheafification.{v} α).map f) :=
  Iff.rfl

/-- Membership in the localizing class is local bijectivity of the underlying morphism
of presheaves of abelian groups: the sheafification of modules inverts exactly the
locally bijective maps. -/
lemma sheafificationW_iff_isLocallyBijective {M N : PresheafOfModules.{v} R₀}
    (f : M ⟶ N) :
    sheafificationW.{v} α f ↔
      Presheaf.IsLocallyInjective J ((toPresheaf R₀).map f) ∧
        Presheaf.IsLocallySurjective J ((toPresheaf R₀).map f) := by
  rw [sheafificationW_iff]
  constructor
  · intro h
    have h1 : IsIso ((SheafOfModules.toSheaf R).map ((sheafification.{v} α).map f)) :=
      inferInstance
    have h2 : IsIso ((presheafToSheaf J AddCommGrpCat).map ((toPresheaf R₀).map f)) := h1
    have h3 : J.W ((toPresheaf R₀).map f) := (J.W_iff _).mpr h2
    exact ⟨h3.isLocallyInjective, h3.isLocallySurjective⟩
  · rintro ⟨h1, h2⟩
    have h3 : J.W ((toPresheaf R₀).map f) := J.W_of_isLocallyBijective _
    have h4 : IsIso ((presheafToSheaf J AddCommGrpCat).map ((toPresheaf R₀).map f)) :=
      (J.W_iff _).mp h3
    have h5 : IsIso ((SheafOfModules.toSheaf R).map ((sheafification.{v} α).map f)) := h4
    exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf R)

section Reflective

variable (R' : Sheaf J RingCat.{u})

/-- At `α = 𝟙` the sheafification adjunction is reflective (`forget` is fully faithful
and `restrictScalars (𝟙 _)` is an equivalence), so the sheafification functor is a
localization at `sheafificationW`. -/
instance sheafificationW_isLocalization :
    (sheafification.{v} (𝟙 R'.obj)).IsLocalization (sheafificationW.{v} (𝟙 R'.obj)) := by
  have h : ((SheafOfModules.forget R' ⋙ restrictScalars (𝟙 R'.obj))).Full :=
    Functor.Full.comp _ _
  have h' : ((SheafOfModules.forget R' ⋙ restrictScalars (𝟙 R'.obj))).Faithful :=
    Functor.Faithful.comp _ _
  exact (sheafificationAdjunction (𝟙 R'.obj)).isLocalization

end Reflective

section Tensor

variable {S : Cᵒᵖ ⥤ CommRingCat.{u}}
  {M₁ M₂ N₁ N₂ : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)}

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
/-- The locally-surjective half of the [GAP1-W-MONO] tensor-stability leaf: the tensor
product of locally surjective morphisms of presheaves of modules is locally surjective.
Sections of the tensor presheaf are finite sums of simple tensors; each factor is
locally hit, and the finitely many image sieves intersect to a covering sieve. -/
lemma isLocallySurjective_tensorHom (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂)
    [Presheaf.IsLocallySurjective J ((toPresheaf _).map f)]
    [Presheaf.IsLocallySurjective J ((toPresheaf _).map g)] :
    Presheaf.IsLocallySurjective J ((toPresheaf _).map (f ⊗ₘ g)) := by
  constructor
  intro U t
  induction t using TensorProduct.induction_on with
  | zero =>
      refine J.superset_covering (fun V p _ => ⟨0, ?_⟩) (J.top_mem U)
      change (f ⊗ₘ g).app (Opposite.op V) 0 = (M₂ ⊗ N₂).map p.op 0
      erw [map_zero]
  | tmul m n =>
      refine J.superset_covering ?_ (J.intersection_covering
        (Presheaf.imageSieve_mem J ((toPresheaf _).map f) m)
        (Presheaf.imageSieve_mem J ((toPresheaf _).map g) n))
      rintro V p ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      refine ⟨a ⊗ₜ b, ?_⟩
      have ha' : f.app (Opposite.op V) a = M₂.map p.op m := ha
      have hb' : g.app (Opposite.op V) b = N₂.map p.op n := hb
      change (f ⊗ₘ g).app (Opposite.op V) (a ⊗ₜ b) = (M₂ ⊗ N₂).map p.op (m ⊗ₜ n)
      erw [Monoidal.tensorHom_app, ModuleCat.MonoidalCategory.tensorHom_tmul,
        Monoidal.tensorObj_map_tmul]
      rw [ha', hb']
      rfl
  | add t₁ t₂ h₁ h₂ =>
      refine J.superset_covering ?_ (J.intersection_covering h₁ h₂)
      rintro V p ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
      refine ⟨x₁ + x₂, ?_⟩
      have hx₁' : (f ⊗ₘ g).app (Opposite.op V) x₁ = (M₂ ⊗ N₂).map p.op t₁ := hx₁
      have hx₂' : (f ⊗ₘ g).app (Opposite.op V) x₂ = (M₂ ⊗ N₂).map p.op t₂ := hx₂
      change (f ⊗ₘ g).app (Opposite.op V) (x₁ + x₂) = (M₂ ⊗ N₂).map p.op (t₁ + t₂)
      erw [map_add, map_add]
      rw [hx₁', hx₂']
      rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
/-- **([W-MONO-inj])** Precomposition with the tensor of locally surjective morphisms
is injective on morphisms into a presheaf of modules whose underlying presheaf is a
sheaf: two maps out of the tensor agreeing after `f ⊗ₘ g` agree on simple tensors
locally, hence agree by separatedness. -/
theorem tensorHom_precomp_injective (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂)
    [Presheaf.IsLocallySurjective J ((toPresheaf _).map f)]
    [Presheaf.IsLocallySurjective J ((toPresheaf _).map g)]
    {P : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)}
    (hP : Presheaf.IsSheaf J P.presheaf) :
    Function.Injective (fun (ψ : M₂ ⊗ N₂ ⟶ P) => (f ⊗ₘ g) ≫ ψ) := by
  intro ψ₁ ψ₂ h
  refine hom_ext (fun U => ?_)
  ext t
  induction t using TensorProduct.induction_on with
  | zero => erw [map_zero, map_zero]
  | tmul m n =>
      have key : ∀ (ψ : M₂ ⊗ N₂ ⟶ P) {V : C} (p : V ⟶ U.unop)
          (a : M₁.obj (Opposite.op V)) (b : N₁.obj (Opposite.op V))
          (ha : f.app (Opposite.op V) a = M₂.map p.op m)
          (hb : g.app (Opposite.op V) b = N₂.map p.op n),
          P.map p.op (ψ.app U (m ⊗ₜ n)) =
            ((f ⊗ₘ g) ≫ ψ).app (Opposite.op V) (a ⊗ₜ b) := by
        intro ψ V p a b ha hb
        have hnat : ∀ x, P.map p.op (ψ.app U x) =
            ψ.app (Opposite.op V) ((M₂ ⊗ N₂).map p.op x) :=
          fun x => (CategoryTheory.congr_fun (ψ.naturality p.op) x).symm
        erw [hnat]
        have hres : (M₂ ⊗ N₂).map p.op (m ⊗ₜ n) =
            (f ⊗ₘ g).app (Opposite.op V) (a ⊗ₜ b) := by
          erw [Monoidal.tensorObj_map_tmul, Monoidal.tensorHom_app,
            ModuleCat.MonoidalCategory.tensorHom_tmul]
          rw [ha, hb]
          rfl
        rw [hres]
        rfl
      obtain ⟨U⟩ := U
      apply hP.isSeparated _ _ (J.intersection_covering
        (Presheaf.imageSieve_mem J ((toPresheaf _).map f) m)
        (Presheaf.imageSieve_mem J ((toPresheaf _).map g) n))
      rintro V p ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      have ha' : f.app (Opposite.op V) a = M₂.map p.op m := ha
      have hb' : g.app (Opposite.op V) b = N₂.map p.op n := hb
      exact (key ψ₁ p a b ha' hb').trans ((congrArg (fun φ => φ.app (Opposite.op V)
        (a ⊗ₜ b)) h).trans (key ψ₂ p a b ha' hb').symm)
  | add s t hs ht =>
      erw [map_add, map_add]
      rw [hs, ht]

end Tensor

section Glue

/- The gluing construction is stated over a small site (`C : Type u`, `Category.{u}`,
modules in `.{u}`) so that the Type-level amalgamation bridge
(`isSheaf_iff_isSheaf_forget`, which needs `forget` to land in `Type (max v₁ u₁)`)
applies — exactly the shape of GAP-1's consumer, the small Zariski site of a scheme. -/

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {S : Cᵒᵖ ⥤ CommRingCat.{u}}
  {M₁ M₂ N₁ N₂ : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)}
  (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂)
  [Presheaf.IsLocallyInjective J ((toPresheaf _).map f)]
  [Presheaf.IsLocallySurjective J ((toPresheaf _).map f)]
  [Presheaf.IsLocallyInjective J ((toPresheaf _).map g)]
  [Presheaf.IsLocallySurjective J ((toPresheaf _).map g)]
  {P : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)}
  (hP : Presheaf.IsSheaf J P.presheaf) (χ : M₁ ⊗ N₁ ⟶ P)

include hP in
omit [Presheaf.IsLocallySurjective J ((toPresheaf _).map f)]
  [Presheaf.IsLocallySurjective J ((toPresheaf _).map g)] in
/-- Any two preimage-pairs of the same sections give the same `χ`-value: locally the
pairs agree (local injectivity), so the values agree locally, so they agree
(separatedness). The workhorse of the [W-MONO-glue] construction. -/
private lemma chi_app_congr {V : C} (a a' : M₁.obj (Opposite.op V))
    (b b' : N₁.obj (Opposite.op V))
    (hfa : f.app (Opposite.op V) a = f.app (Opposite.op V) a')
    (hgb : g.app (Opposite.op V) b = g.app (Opposite.op V) b') :
    χ.app (Opposite.op V) (a ⊗ₜ b) = χ.app (Opposite.op V) (a' ⊗ₜ b') := by
  have hfa' : ((toPresheaf _).map f).app (Opposite.op V) a =
      ((toPresheaf _).map f).app (Opposite.op V) a' := hfa
  have hgb' : ((toPresheaf _).map g).app (Opposite.op V) b =
      ((toPresheaf _).map g).app (Opposite.op V) b' := hgb
  apply hP.isSeparated _ _ (J.intersection_covering
    (Presheaf.equalizerSieve_mem J ((toPresheaf _).map f) a a' hfa')
    (Presheaf.equalizerSieve_mem J ((toPresheaf _).map g) b b' hgb'))
  rintro W q ⟨hqa, hqb⟩
  have hnat : ∀ x : ((M₁ ⊗ N₁).obj (Opposite.op V) : Type u),
      P.presheaf.map q.op (χ.app (Opposite.op V) x) =
        χ.app (Opposite.op W) ((M₁ ⊗ N₁).map q.op x) :=
    fun x => (CategoryTheory.congr_fun (χ.naturality q.op) x).symm
  erw [hnat, hnat]
  congr 1
  erw [Monoidal.tensorObj_map_tmul, Monoidal.tensorObj_map_tmul]
  have hqa' : M₁.map q.op a = M₁.map q.op a' := hqa
  have hqb' : N₁.map q.op b = N₁.map q.op b' := hqb
  rw [hqa', hqb']

/-- The defining property of the glued pairing section at `(m, n)`: it restricts to
the `χ`-value of every local preimage-pair. -/
private def IsPairingSection {U : Cᵒᵖ} (m : M₂.obj U) (n : N₂.obj U)
    (s : P.obj U) : Prop :=
  ∀ ⦃V : C⦄ (p : V ⟶ U.unop) (a : M₁.obj (Opposite.op V)) (b : N₁.obj (Opposite.op V)),
    f.app (Opposite.op V) a = M₂.map p.op m → g.app (Opposite.op V) b = N₂.map p.op n →
    P.map p.op s = χ.app (Opposite.op V) (a ⊗ₜ b)

private lemma pom_map_comp (M : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat))
    {X : Cᵒᵖ} {V W : C} (q : W ⟶ V) (p : V ⟶ X.unop) (x : M.obj X) :
    M.map (q ≫ p).op x = M.map q.op (M.map p.op x) :=
  show M.presheaf.map (q ≫ p).op x = M.presheaf.map q.op (M.presheaf.map p.op x) by
    rw [op_comp, M.presheaf.map_comp]
    rfl

private lemma pom_napp_map {A B : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)}
    (φ : A ⟶ B) {V W : C} (q : W ⟶ V) (x : A.obj (Opposite.op V)) :
    φ.app (Opposite.op W) (A.map q.op x) = B.map q.op (φ.app (Opposite.op V) x) :=
  CategoryTheory.congr_fun (φ.naturality q.op) x

variable {f g} in
private lemma chi_value {V W : C} (q : W ⟶ V) (a : M₁.obj (Opposite.op V))
    (b : N₁.obj (Opposite.op V)) :
    P.presheaf.map q.op (χ.app (Opposite.op V) (a ⊗ₜ b)) =
      χ.app (Opposite.op W) (M₁.map q.op a ⊗ₜ N₁.map q.op b) := by
  refine ((CategoryTheory.congr_fun (χ.naturality q.op) (a ⊗ₜ b)).symm).trans ?_
  exact congrArg (χ.app (Opposite.op W)) (by erw [Monoidal.tensorObj_map_tmul]; rfl)

variable {f g} in
/-- Restricting a local preimage-pair of `(m, n)` over `p` along `q` gives a local
preimage-pair over `q ≫ p`: naturality of `f`, `g` moves the restriction across the
morphisms, then functoriality of the restriction maps recombines it. -/
private lemma isPreimagePair_restrict {X : Cᵒᵖ} {m : M₂.obj X} {n : N₂.obj X}
    {V W : C} (q : W ⟶ V) (p : V ⟶ X.unop)
    (a : M₁.obj (Opposite.op V)) (b : N₁.obj (Opposite.op V))
    (ha : f.app (Opposite.op V) a = M₂.map p.op m)
    (hb : g.app (Opposite.op V) b = N₂.map p.op n) :
    f.app (Opposite.op W) (M₁.map q.op a) = M₂.map (q ≫ p).op m ∧
      g.app (Opposite.op W) (N₁.map q.op b) = N₂.map (q ≫ p).op n :=
  ⟨by rw [pom_napp_map f q a, ha, ← pom_map_comp],
    by rw [pom_napp_map g q b, hb, ← pom_map_comp]⟩

variable {f g} in
include hP in
omit [Presheaf.IsLocallyInjective J ((toPresheaf _).map f)]
  [Presheaf.IsLocallyInjective J ((toPresheaf _).map g)] in
private lemma isPairingSection_unique {U : Cᵒᵖ} {m : M₂.obj U} {n : N₂.obj U}
    {s s' : P.obj U} (hs : IsPairingSection f g χ m n s)
    (hs' : IsPairingSection f g χ m n s') : s = s' := by
  apply hP.isSeparated _ _ (J.intersection_covering
    (Presheaf.imageSieve_mem J ((toPresheaf _).map f) m)
    (Presheaf.imageSieve_mem J ((toPresheaf _).map g) n))
  rintro V p ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  have ha' : f.app (Opposite.op V) a = M₂.map p.op m := ha
  have hb' : g.app (Opposite.op V) b = N₂.map p.op n := hb
  exact (hs p a b ha' hb').trans (hs' p a b ha' hb').symm

include hP in
/-- Existence and uniqueness of the glued pairing section: amalgamate the `χ`-values
of chosen local preimage-pairs over the intersection of the two image sieves
(compatibility and the defining property both reduce to `chi_app_congr`). -/
private lemma existsUnique_isPairingSection {U : Cᵒᵖ} (m : M₂.obj U) (n : N₂.obj U) :
    ∃! s : P.obj U, IsPairingSection f g χ m n s := by
  have hT : Presieve.IsSheaf J (P.presheaf ⋙ forget AddCommGrpCat) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((Presheaf.isSheaf_iff_isSheaf_forget J P.presheaf (forget _)).mp hP)
  have hSv : (Presheaf.imageSieve ((toPresheaf _).map f) m ⊓
      Presheaf.imageSieve ((toPresheaf _).map g) n) ∈ J U.unop :=
    J.intersection_covering
      (Presheaf.imageSieve_mem J ((toPresheaf _).map f) m)
      (Presheaf.imageSieve_mem J ((toPresheaf _).map g) n)
  set Sv := Presheaf.imageSieve ((toPresheaf _).map f) m ⊓
      Presheaf.imageSieve ((toPresheaf _).map g) n with hSvdef
  -- the choice family of χ-values
  set x : Presieve.FamilyOfElements (P.presheaf ⋙ forget AddCommGrpCat) Sv.arrows :=
    fun V p hp => χ.app (Opposite.op V) (hp.1.choose ⊗ₜ hp.2.choose) with hxdef
  have hchoice : ∀ {V : C} (p : V ⟶ U.unop) (hp : Sv.arrows p),
      f.app (Opposite.op V) hp.1.choose = M₂.map p.op m ∧
        g.app (Opposite.op V) hp.2.choose = N₂.map p.op n :=
    fun p hp => ⟨hp.1.choose_spec, hp.2.choose_spec⟩
  -- compatibility of the choice family
  have hx : x.Compatible := by
    intro V₁ V₂ W g₁ g₂ p₁ p₂ h₁ h₂ hcomm
    rw [hxdef]
    dsimp only
    erw [chi_value, chi_value]
    have hp₁ := hchoice p₁ h₁
    have hp₂ := hchoice p₂ h₂
    have hr₁ := isPreimagePair_restrict g₁ p₁ _ _ hp₁.1 hp₁.2
    have hr₂ := isPreimagePair_restrict g₂ p₂ _ _ hp₂.1 hp₂.2
    exact chi_app_congr f g hP χ _ _ _ _
      (hr₁.1.trans (by rw [hcomm]; exact hr₂.1.symm))
      (hr₁.2.trans (by rw [hcomm]; exact hr₂.2.symm))
  -- the amalgam is a pairing section
  have hamalg : IsPairingSection f g χ m n ((hT Sv hSv).amalgamate x hx) := by
    intro V p a b ha hb
    apply hP.isSeparated _ _ (J.pullback_stable p hSv)
    intro W q hq
    have hglue := (hT Sv hSv).valid_glue hx (q ≫ p) hq
    erw [(pom_map_comp P q p _).symm, hglue, hxdef]
    dsimp only
    erw [chi_value]
    have hc := hchoice (q ≫ p) hq
    have hr := isPreimagePair_restrict q p a b ha hb
    exact chi_app_congr f g hP χ _ _ _ _ (hc.1.trans hr.1.symm) (hc.2.trans hr.2.symm)
  exact ⟨(hT Sv hSv).amalgamate x hx, hamalg,
    fun s hs => isPairingSection_unique hP χ hs hamalg⟩

/-- The glued pairing section itself. -/
private noncomputable def pairingSection {U : Cᵒᵖ} (m : M₂.obj U) (n : N₂.obj U) :
    P.obj U :=
  (existsUnique_isPairingSection f g hP χ m n).exists.choose

private lemma pairingSection_spec {U : Cᵒᵖ} (m : M₂.obj U) (n : N₂.obj U) :
    IsPairingSection f g χ m n (pairingSection f g hP χ m n) :=
  (existsUnique_isPairingSection f g hP χ m n).exists.choose_spec

include hP in
private lemma pairingSection_add_left {U : Cᵒᵖ} (m m' : M₂.obj U) (n : N₂.obj U) :
    pairingSection f g hP χ (m + m') n =
      pairingSection f g hP χ m n + pairingSection f g hP χ m' n := by
  refine (isPairingSection_unique hP χ (pairingSection_spec f g hP χ (m + m') n) ?_)
  intro V p a b ha hb
  apply hP.isSeparated _ _ (J.intersection_covering
    (J.pullback_stable p (Presheaf.imageSieve_mem J ((toPresheaf _).map f) m))
    (J.pullback_stable p (Presheaf.imageSieve_mem J ((toPresheaf _).map f) m')))
  rintro W q ⟨hq₁, hq₂⟩
  obtain ⟨a₁, ha₁'⟩ : ∃ a₁ : ↑(M₁.obj (Opposite.op W)),
      f.app (Opposite.op W) a₁ = M₂.map (q ≫ p).op m := hq₁
  obtain ⟨a₂, ha₂'⟩ : ∃ a₂ : ↑(M₁.obj (Opposite.op W)),
      f.app (Opposite.op W) a₂ = M₂.map (q ≫ p).op m' := hq₂
  have hbW : g.app (Opposite.op W) (N₁.map q.op b) = N₂.map (q ≫ p).op n := by
    rw [pom_napp_map g q b, hb, ← pom_map_comp]
  have hL : P.presheaf.map q.op (P.map p.op (pairingSection f g hP χ m n +
      pairingSection f g hP χ m' n)) =
      χ.app (Opposite.op W) ((a₁ + a₂) ⊗ₜ N₁.map q.op b) := by
    change P.map q.op (P.map p.op (pairingSection f g hP χ m n +
      pairingSection f g hP χ m' n)) = _
    rw [← pom_map_comp]
    erw [map_add]
    rw [pairingSection_spec f g hP χ m n (q ≫ p) a₁ (N₁.map q.op b) ha₁' hbW,
      pairingSection_spec f g hP χ m' n (q ≫ p) a₂ (N₁.map q.op b) ha₂' hbW]
    exact ((χ.app (Opposite.op W)).hom.map_add _ _).symm.trans
      (congrArg (χ.app (Opposite.op W)) (TensorProduct.add_tmul a₁ a₂ _).symm)
  rw [hL, chi_value χ q a b]
  refine chi_app_congr f g hP χ _ _ _ _ ?_ rfl
  exact (map_add ((f.app (Opposite.op W)).hom) a₁ a₂).trans
    ((congrArg₂ (· + ·) ha₁' ha₂').trans
      ((map_add ((M₂.presheaf.map (q ≫ p).op).hom) m m').symm.trans
        ((pom_map_comp M₂ q p (m + m')).trans
          ((congrArg (M₂.map q.op) ha.symm).trans (pom_napp_map f q a).symm))))

include hP in
private lemma pairingSection_smul_left {U : Cᵒᵖ}
    (r : ↑((S ⋙ forget₂ CommRingCat RingCat).obj U)) (m : M₂.obj U) (n : N₂.obj U) :
    pairingSection f g hP χ (r • m) n = r • pairingSection f g hP χ m n := by
  refine (isPairingSection_unique hP χ (pairingSection_spec f g hP χ (r • m) n) ?_)
  intro V p a b ha hb
  apply hP.isSeparated _ _
    (J.pullback_stable p (Presheaf.imageSieve_mem J ((toPresheaf _).map f) m))
  intro W q hq₀
  obtain ⟨a₀, ha₀'⟩ : ∃ a₀ : ↑(M₁.obj (Opposite.op W)),
      f.app (Opposite.op W) a₀ = M₂.map (q ≫ p).op m := hq₀
  have hbW : g.app (Opposite.op W) (N₁.map q.op b) = N₂.map (q ≫ p).op n := by
    rw [pom_napp_map g q b, hb, ← pom_map_comp]
  set r' : ↑((S ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op W)) :=
    ((S ⋙ forget₂ CommRingCat RingCat).map (Opposite.op (q ≫ p))).hom r with hr'
  have hL : P.presheaf.map q.op (P.map p.op (r • pairingSection f g hP χ m n)) =
      χ.app (Opposite.op W) ((r' • a₀) ⊗ₜ N₁.map q.op b) := by
    change P.map q.op (P.map p.op (r • pairingSection f g hP χ m n)) = _
    rw [← pom_map_comp]
    erw [P.map_smul]
    rw [pairingSection_spec f g hP χ m n (q ≫ p) a₀ (N₁.map q.op b) ha₀' hbW]
    exact ((χ.app (Opposite.op W)).hom.map_smul r' _).symm.trans
      (congrArg (χ.app (Opposite.op W)) (TensorProduct.smul_tmul' r' a₀ _))
  rw [hL, chi_value χ q a b]
  refine chi_app_congr f g hP χ _ _ _ _ ?_ rfl
  exact (map_smul ((f.app (Opposite.op W)).hom) r' a₀).trans
    ((congrArg (r' • ·) ha₀').trans
      ((M₂.map_smul (q ≫ p).op r m).symm.trans
        ((pom_map_comp M₂ q p (r • m)).trans
          ((congrArg (M₂.map q.op) ha.symm).trans (pom_napp_map f q a).symm))))

include hP in
private lemma pairingSection_add_right {U : Cᵒᵖ} (m : M₂.obj U) (n n' : N₂.obj U) :
    pairingSection f g hP χ m (n + n') =
      pairingSection f g hP χ m n + pairingSection f g hP χ m n' := by
  refine (isPairingSection_unique hP χ (pairingSection_spec f g hP χ m (n + n')) ?_)
  intro V p a b ha hb
  apply hP.isSeparated _ _ (J.intersection_covering
    (J.pullback_stable p (Presheaf.imageSieve_mem J ((toPresheaf _).map g) n))
    (J.pullback_stable p (Presheaf.imageSieve_mem J ((toPresheaf _).map g) n')))
  rintro W q ⟨hq₁, hq₂⟩
  obtain ⟨b₁, hb₁'⟩ : ∃ b₁ : ↑(N₁.obj (Opposite.op W)),
      g.app (Opposite.op W) b₁ = N₂.map (q ≫ p).op n := hq₁
  obtain ⟨b₂, hb₂'⟩ : ∃ b₂ : ↑(N₁.obj (Opposite.op W)),
      g.app (Opposite.op W) b₂ = N₂.map (q ≫ p).op n' := hq₂
  have haW : f.app (Opposite.op W) (M₁.map q.op a) = M₂.map (q ≫ p).op m := by
    rw [pom_napp_map f q a, ha, ← pom_map_comp]
  have hL : P.presheaf.map q.op (P.map p.op (pairingSection f g hP χ m n +
      pairingSection f g hP χ m n')) =
      χ.app (Opposite.op W) (M₁.map q.op a ⊗ₜ (b₁ + b₂)) := by
    change P.map q.op (P.map p.op (pairingSection f g hP χ m n +
      pairingSection f g hP χ m n')) = _
    rw [← pom_map_comp]
    erw [map_add]
    rw [pairingSection_spec f g hP χ m n (q ≫ p) (M₁.map q.op a) b₁ haW hb₁',
      pairingSection_spec f g hP χ m n' (q ≫ p) (M₁.map q.op a) b₂ haW hb₂']
    exact ((χ.app (Opposite.op W)).hom.map_add _ _).symm.trans
      (congrArg (χ.app (Opposite.op W)) (TensorProduct.tmul_add _ b₁ b₂).symm)
  rw [hL, chi_value χ q a b]
  refine chi_app_congr f g hP χ _ _ _ _ rfl ?_
  exact (map_add ((g.app (Opposite.op W)).hom) b₁ b₂).trans
    ((congrArg₂ (· + ·) hb₁' hb₂').trans
      ((map_add ((N₂.presheaf.map (q ≫ p).op).hom) n n').symm.trans
        ((pom_map_comp N₂ q p (n + n')).trans
          ((congrArg (N₂.map q.op) hb.symm).trans (pom_napp_map g q b).symm))))

include hP in
private lemma pairingSection_smul_right {U : Cᵒᵖ}
    (r : ↑((S ⋙ forget₂ CommRingCat RingCat).obj U)) (m : M₂.obj U) (n : N₂.obj U) :
    pairingSection f g hP χ m (r • n) = r • pairingSection f g hP χ m n := by
  refine (isPairingSection_unique hP χ (pairingSection_spec f g hP χ m (r • n)) ?_)
  intro V p a b ha hb
  apply hP.isSeparated _ _
    (J.pullback_stable p (Presheaf.imageSieve_mem J ((toPresheaf _).map g) n))
  intro W q hq₀
  obtain ⟨b₀, hb₀'⟩ : ∃ b₀ : ↑(N₁.obj (Opposite.op W)),
      g.app (Opposite.op W) b₀ = N₂.map (q ≫ p).op n := hq₀
  have haW : f.app (Opposite.op W) (M₁.map q.op a) = M₂.map (q ≫ p).op m := by
    rw [pom_napp_map f q a, ha, ← pom_map_comp]
  set r' : ↑((S ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op W)) :=
    ((S ⋙ forget₂ CommRingCat RingCat).map (Opposite.op (q ≫ p))).hom r with hr'
  have hL : P.presheaf.map q.op (P.map p.op (r • pairingSection f g hP χ m n)) =
      χ.app (Opposite.op W) (M₁.map q.op a ⊗ₜ (r' • b₀)) := by
    change P.map q.op (P.map p.op (r • pairingSection f g hP χ m n)) = _
    rw [← pom_map_comp]
    erw [P.map_smul]
    rw [pairingSection_spec f g hP χ m n (q ≫ p) (M₁.map q.op a) b₀ haW hb₀']
    exact ((χ.app (Opposite.op W)).hom.map_smul r' _).symm.trans
      (congrArg (χ.app (Opposite.op W)) (TensorProduct.tmul_smul r' _ b₀).symm)
  rw [hL, chi_value χ q a b]
  refine chi_app_congr f g hP χ _ _ _ _ rfl ?_
  exact (map_smul ((g.app (Opposite.op W)).hom) r' b₀).trans
    ((congrArg (r' • ·) hb₀').trans
      ((N₂.map_smul (q ≫ p).op r n).symm.trans
        ((pom_map_comp N₂ q p (r • n)).trans
          ((congrArg (N₂.map q.op) hb.symm).trans (pom_napp_map g q b).symm))))

include hP in
private lemma pairingSection_map {U : Cᵒᵖ} {V : C} (p : V ⟶ U.unop)
    (m : M₂.obj U) (n : N₂.obj U) :
    P.map p.op (pairingSection f g hP χ m n) =
      pairingSection f g hP χ
        (show ↑(M₂.obj (Opposite.op V)) from M₂.map p.op m)
        (show ↑(N₂.obj (Opposite.op V)) from N₂.map p.op n) := by
  refine isPairingSection_unique hP χ ?_
    (pairingSection_spec f g hP χ
      (show ↑(M₂.obj (Opposite.op V)) from M₂.map p.op m)
      (show ↑(N₂.obj (Opposite.op V)) from N₂.map p.op n))
  intro W q a b ha hb
  rw [← pom_map_comp]
  exact pairingSection_spec f g hP χ m n (q ≫ p) a b
    (ha.trans (pom_map_comp M₂ q p m).symm) (hb.trans (pom_map_comp N₂ q p n).symm)

/-- The glued pairing, packaged as a bilinear map on sections. -/
private noncomputable def pairingLinear (U : Cᵒᵖ) :
    ↑(M₂.obj U) →ₗ[↑((S ⋙ forget₂ CommRingCat RingCat).obj U)]
      (↑(N₂.obj U) →ₗ[↑((S ⋙ forget₂ CommRingCat RingCat).obj U)] ↑(P.obj U)) where
  toFun m :=
    { toFun := pairingSection f g hP χ m
      map_add' := pairingSection_add_right f g hP χ m
      map_smul' := fun r n => pairingSection_smul_right f g hP χ r m n }
  map_add' m m' := LinearMap.ext (fun n => pairingSection_add_left f g hP χ m m' n)
  map_smul' r m := LinearMap.ext (fun n => pairingSection_smul_left f g hP χ r m n)

/-- The glued morphism out of the tensor product. -/
private noncomputable def gluedHom : M₂ ⊗ N₂ ⟶ P where
  app U := ModuleCat.ofHom (TensorProduct.lift (pairingLinear f g hP χ U))
  naturality {U V} p := by
    ext t
    change TensorProduct.lift (pairingLinear f g hP χ V) ((M₂ ⊗ N₂).map p t) =
      P.map p (TensorProduct.lift (pairingLinear f g hP χ U) t)
    induction t using TensorProduct.induction_on with
    | zero =>
        erw [map_zero, map_zero]
        rfl
    | tmul m n =>
        have h2 : (M₂ ⊗ N₂).map p (m ⊗ₜ n) =
            (show ↑(M₂.obj V) from M₂.map p m) ⊗ₜ
              (show ↑(N₂.obj V) from N₂.map p n) := by
          erw [Monoidal.tensorObj_map_tmul]
          rfl
        rw [h2]
        exact (pairingSection_map f g hP χ p.unop m n).symm
    | add t₁ t₂ h₁ h₂ =>
        erw [map_add, map_add]
        exact (congrArg₂ (· + ·) h₁ h₂).trans
          ((map_add ((P.presheaf.map p).hom)
            (TensorProduct.lift (pairingLinear f g hP χ U) t₁)
            (TensorProduct.lift (pairingLinear f g hP χ U) t₂)).symm.trans
              (congrArg (P.map p)
                (map_add (TensorProduct.lift (pairingLinear f g hP χ U)) t₁ t₂).symm))

include hP in
private lemma gluedHom_fac : (f ⊗ₘ g) ≫ gluedHom f g hP χ = χ := by
  refine hom_ext (fun U => ?_)
  ext t
  induction t using TensorProduct.induction_on with
  | zero => exact (map_zero _).trans (map_zero _).symm
  | tmul a b =>
      change TensorProduct.lift (pairingLinear f g hP χ U)
        ((f ⊗ₘ g).app U (a ⊗ₜ b)) = χ.app U (a ⊗ₜ b)
      have h1 : (f ⊗ₘ g).app U (a ⊗ₜ b) = f.app U a ⊗ₜ g.app U b := by
        erw [Monoidal.tensorHom_app, ModuleCat.MonoidalCategory.tensorHom_tmul]
      rw [h1]
      have h2 : TensorProduct.lift (pairingLinear f g hP χ U)
          (f.app U a ⊗ₜ g.app U b) =
            pairingSection f g hP χ (f.app U a) (g.app U b) := rfl
      rw [h2]
      have hida : f.app U a = M₂.map (𝟙 U.unop).op (f.app U a) :=
        ((CategoryTheory.congr_fun (M₂.presheaf.map_id U) (f.app U a)).trans rfl).symm
      have hidb : g.app U b = N₂.map (𝟙 U.unop).op (g.app U b) :=
        ((CategoryTheory.congr_fun (N₂.presheaf.map_id U) (g.app U b)).trans rfl).symm
      have h4 := pairingSection_spec f g hP χ (f.app U a) (g.app U b)
        (𝟙 U.unop) a b hida hidb
      refine Eq.trans ?_ h4
      exact ((CategoryTheory.congr_fun (P.presheaf.map_id U)
        (pairingSection f g hP χ (f.app U a) (g.app U b))).trans rfl).symm
  | add t₁ t₂ h₁ h₂ =>
      erw [map_add, map_add]
      rw [h₁, h₂]

include hP in
/-- **([W-MONO-glue])** Precomposition with the tensor of locally bijective morphisms
is surjective on morphisms into a presheaf of modules whose underlying presheaf is a
sheaf: every `χ` factors through the glued bilinear pairing. -/
theorem tensorHom_precomp_surjective :
    Function.Surjective (fun (ψ : M₂ ⊗ N₂ ⟶ P) => (f ⊗ₘ g) ≫ ψ) :=
  fun χ => ⟨gluedHom f g hP χ, gluedHom_fac f g hP χ⟩

end Glue

section Assembly

/- The assembly of the [GAP1-W-MONO] leaf: the two precomposition halves proven in the
`Glue`/`Tensor` sections give, via the sheafification adjunction and iso-detection by
coyoneda-bijectivity, that `sheafificationW` is closed under `⊗ₘ` — hence monoidal. The
site is the small one (`C : Type u`, `Category.{u}`) inherited from `Glue`, so the
precomposition lemmas apply. -/

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {S : Cᵒᵖ ⥤ CommRingCat.{u}} {R : Sheaf J RingCat.{u}}
  (α : (S ⋙ forget₂ CommRingCat RingCat) ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  {M₁ M₂ N₁ N₂ : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)}

/-- **([GAP1-W-MONO], the leaf)** The class of morphisms inverted by sheafification of
modules is closed under tensor product. Proof: `sheafificationW`-membership is local
bijectivity (the bridge), so `f`, `g` locally bijective make precomposition with
`f ⊗ₘ g` a bijection on morphisms into every sheaf-underlying target
(`tensorHom_precomp_injective`/`_surjective`); transporting that bijection across the
sheafification adjunction `homEquiv` (naturality-left) and detecting isomorphisms by
coyoneda-bijectivity shows `(sheafification α).map (f ⊗ₘ g)` is an isomorphism. No
flatness and no stalks — the topos-theoretic replacement for the pointwise argument. -/
theorem sheafificationW_tensorHom (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂)
    (hf : sheafificationW.{u} α f) (hg : sheafificationW.{u} α g) :
    sheafificationW.{u} α (f ⊗ₘ g) := by
  obtain ⟨hfi, hfs⟩ := (sheafificationW_iff_isLocallyBijective α f).mp hf
  obtain ⟨hgi, hgs⟩ := (sheafificationW_iff_isLocallyBijective α g).mp hg
  haveI := hfi; haveI := hfs; haveI := hgi; haveI := hgs
  rw [sheafificationW_iff]
  apply isIso_of_coyoneda_map_bijective
  intro Y
  have hP : Presheaf.IsSheaf J
      ((SheafOfModules.forget R ⋙ restrictScalars α).obj Y).presheaf := Y.isSheaf
  have hΨ : Function.Bijective (fun (ψ : M₂ ⊗ N₂ ⟶
      (SheafOfModules.forget R ⋙ restrictScalars α).obj Y) => (f ⊗ₘ g) ≫ ψ) :=
    ⟨tensorHom_precomp_injective f g hP, tensorHom_precomp_surjective f g hP⟩
  have hconj : (fun (x : (sheafification.{u} α).obj (M₂ ⊗ N₂) ⟶ Y) =>
      (sheafification.{u} α).map (f ⊗ₘ g) ≫ x) =
      ⇑((sheafificationAdjunction α).homEquiv (M₁ ⊗ N₁) Y).symm ∘
        (fun ψ => (f ⊗ₘ g) ≫ ψ) ∘
          ⇑((sheafificationAdjunction α).homEquiv (M₂ ⊗ N₂) Y) := by
    funext x
    simp only [Function.comp_apply, Equiv.eq_symm_apply]
    exact (sheafificationAdjunction α).homEquiv_naturality_left (f ⊗ₘ g) x
  rw [hconj]
  exact ((sheafificationAdjunction α).homEquiv (M₁ ⊗ N₁) Y).symm.bijective.comp
    (hΨ.comp ((sheafificationAdjunction α).homEquiv (M₂ ⊗ N₂) Y).bijective)

/-- **([GAP1-W-MONO], corollary — the original loc-injective claim)** The tensor product of
morphisms inverted by sheafification is locally injective on underlying presheaves. This was
the staged stalkwise leaf; it now follows *free* from `sheafificationW_tensorHom` through the
local-bijectivity bridge, with the sheafification datum `α` standing in for the stalks a
general site lacks: `f`, `g` locally bijective (i.e. `sheafificationW α`-members) ⟹
`sheafificationW α (f ⊗ₘ g)` ⟹ its underlying presheaf map is locally bijective, in
particular locally injective. (The bare statement over an arbitrary presheaf of commutative
rings, with only local-bijectivity instances and no `α`, is not closable — the sheafification
adjunction is the topos-theoretic replacement for a pointwise/stalkwise argument — so this
carries `α` and the `sheafificationW` hypotheses rather than the byte-identical staged
signature; obtain those hypotheses from local-bijectivity via
`sheafificationW_iff_isLocallyBijective`.) -/
lemma isLocallyInjective_tensorHom (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂)
    (hf : sheafificationW α f) (hg : sheafificationW α g) :
    Presheaf.IsLocallyInjective J ((toPresheaf _).map (f ⊗ₘ g)) :=
  ((sheafificationW_iff_isLocallyBijective α (f ⊗ₘ g)).mp
    (sheafificationW_tensorHom α f g hf hg)).1

instance sheafificationW_isMultiplicative : (sheafificationW.{u} α).IsMultiplicative :=
  inferInstanceAs
    ((MorphismProperty.isomorphisms _).inverseImage (sheafification.{u} α)).IsMultiplicative

/-- **([GAP1-W-MONO])** The localizing class `sheafificationW` is monoidal: multiplicative
(registration) and closed under `⊗ₘ` (`sheafificationW_tensorHom`). This is the sole
hypothesis, beyond the localization registration, that `LocalizedMonoidal` needs to hand
`SheafOfModules` its monoidal structure. -/
instance sheafificationW_isMonoidal : (sheafificationW.{u} α).IsMonoidal :=
  MorphismProperty.IsMonoidal.mk' _ fun f g hf hg => sheafificationW_tensorHom α f g hf hg

end Assembly

section Instantiation

/- The payoff: feeding the localization registration and the monoidal class into mathlib's
`LocalizedMonoidal` to obtain the monoidal category structure on sheaves of modules over a
sheaf of commutative rings. We take `α = 𝟙` (the reflective case, where
`sheafificationW_isLocalization` applies) and package the ring sheaf so that its underlying
presheaf is *syntactically* `S ⋙ forget₂`, keeping mathlib's monoidal instance on
`PresheafOfModules (S ⋙ forget₂ _ _)` in view. -/

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  (S : Cᵒᵖ ⥤ CommRingCat.{u})
  (hS : Presheaf.IsSheaf J (S ⋙ forget₂ CommRingCat RingCat))

/-- The reflective localization registration, specialised to the ring sheaf underlying a
sheaf of commutative rings (with `R'` spelled literally so type-class resolution matches it
directly, rather than having to invert the `.obj` projection). Delegates to
`sheafificationW_isLocalization`. -/
instance instSheafificationW_isLocalization_commRingSheaf :
    (sheafification.{u}
        (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj)).IsLocalization
      (sheafificationW.{u}
        (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj)) :=
  sheafificationW_isLocalization _

/-- The monoidality of the localizing class, specialised to the same ring sheaf (again with
`R'` spelled literally for direct resolution). Delegates to `sheafificationW_isMonoidal`
(this file's leaf). -/
instance instSheafificationW_isMonoidal_commRingSheaf :
    (sheafificationW.{u}
      (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj)).IsMonoidal :=
  sheafificationW_isMonoidal _

/-- **([GAP1-W-MONO] — the payoff)** The `LocalizedMonoidal` instantiation resolves: fed the
two registrations above (the reflective localization and the monoidality of the localizing
class — this file's leaf), mathlib's `LocalizedMonoidal` equips the localization of
presheaves of modules over a sheaf of commutative rings with a `MonoidalCategory` structure.
That localized category is definitionally `SheafOfModules ⟨S ⋙ forget₂ _ _, hS⟩` — so
sheaves of modules over a sheaf of commutative rings form a monoidal category,
monoidally under sheafification. This is the GAP-1 payoff; downstream consumers name the
localized category and read off the tensor product, unit, and Pic coherences. -/
theorem sheafOfModules_monoidalCategory_nonempty : Nonempty (MonoidalCategory
    (LocalizedMonoidal
      (sheafification.{u} (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj))
      (sheafificationW.{u} (𝟙 (⟨S ⋙ forget₂ CommRingCat RingCat, hS⟩ : Sheaf J RingCat.{u}).obj))
      (Iso.refl _))) :=
  ⟨inferInstance⟩

end Instantiation

end PresheafOfModules

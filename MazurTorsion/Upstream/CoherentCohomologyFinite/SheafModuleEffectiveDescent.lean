/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib

/-!
# Glue-datum descent for sheaves of modules over a scheme

Generic `AlgebraicGeometry.Scheme.Modules` glue-datum / descent layer:
`glue` (equalizer-of-pushforwards construction), `glueLift`, and the full
restriction isomorphism tower that makes the descent effective.

Blueprint: `blueprint/src/chapters/Picard_GlueDescent.tex`.
-/

universe u

open CategoryTheory Limits Opposite

/-! ## Gluing a sheaf of modules along a scheme glue datum

`Scheme.Modules.glue` descends a sheaf of modules from per-chart data plus a transition
cocycle over a `Scheme.GlueData`. Mathlib carries no turn-key module descent over a
scheme glue datum (confirmed), so this is an Archon-original construction.

Construction (blueprint `def:scheme_modules_glue`): the glued sheaf is built directly as a
categorical limit — an **equalizer of pushforwards** — rather than a hand-built presheaf of
compatible families. Concretely, `glue` forms the two parallel maps
`∏ᵢ (ιᵢ)_* Mᵢ ⇉ ∏_{i,j} (ιᵢ ≫ f_ij)_* (f_ij^* Mᵢ)` (one leg the adjunction unit composed
with the pushforward-composition comparison, the other transported across the inverse
transition `(g_ij)⁻¹`), and takes their equalizer inside `Scheme.Modules D.glued`. The
self-identity (C1) and triple-overlap multiplicativity (C2) hypotheses `_hC1`/`_hC2` on the
family `g` are NOT consumed in forming the equalizer object (the limit exists for any family
of transition maps); they are the descent conditions pinned down downstream when the
restriction isomorphisms are produced. The body below and the `_hC1`/`_hC2` signature are
complete (axiom-clean since iter-056). -/

namespace AlgebraicGeometry.Scheme.Modules

local instance schemeSheafPushforwardIsRightAdjointBridge
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (SheafOfModules.pushforward.{u}
      f.toRingCatSheafHom).IsRightAdjoint :=
  inferInstanceAs ((Scheme.Modules.pushforward f).IsRightAdjoint)

/-! ### Base-change transport of a transition isomorphism to a triple overlap

To state the triple-overlap multiplicativity (C2) of a module descent datum we must
transport each transition isomorphism `g_ij`, living on the overlap `V_ij`, to the common
triple overlap `V_ijk = V_ij ×_{U_i} V_ik`. The transport pulls `g_ij` back along a
projection `p : V_ijk ⟶ V_ij` and reassociates the iterated pullbacks via the pseudofunctor
comparison `Scheme.Modules.pullbackComp`. The three scheme-level `glueData_bridge_*`
identities below (consequences of `t_fac`, `pullback.condition` and `cocycle`) line up the
endpoints of the three transports so that the cocycle equation is well typed. -/

/-- **Base-change transport of a transition isomorphism along a morphism**
(`lem:modules_pullback_basechange_transport`). Given a transition isomorphism
`g : a^*Mᵢ ≅ b^*Mⱼ` over `V` and a morphism `p : W ⟶ V`, transport it to `W` as an
isomorphism `(p ≫ a)^*Mᵢ ≅ (p ≫ b)^*Mⱼ`, by pulling `g` back along `p` and reassociating
the iterated pullbacks through `Scheme.Modules.pullbackComp`.

Project-local: this is the pullback-pseudofunctor packaging that lets the three transition
isomorphisms attached to a triple of charts be compared on a single triple overlap; Mathlib
has no descent-of-modules-over-a-scheme-glue-datum API. -/
noncomputable def pullbackBaseChangeTransport {W V : Scheme.{u}} (p : W ⟶ V)
    {Yi Yj : Scheme.{u}} (a : V ⟶ Yi) (b : V ⟶ Yj)
    {Mi : Yi.Modules} {Mj : Yj.Modules}
    (g : (Scheme.Modules.pullback a).obj Mi ≅ (Scheme.Modules.pullback b).obj Mj) :
    (Scheme.Modules.pullback (p ≫ a)).obj Mi ≅ (Scheme.Modules.pullback (p ≫ b)).obj Mj :=
  (Scheme.Modules.pullbackComp p a).symm.app Mi ≪≫
    (Scheme.Modules.pullback p).mapIso g ≪≫
    (Scheme.Modules.pullbackComp p b).app Mj

/-- Triple-overlap bridge (source): on `V_ijk = V_ij ×_{U_i} V_ik` the two projections to
`V_ij` and `V_ik` followed by the overlap immersions `f_ij`, `f_ik` agree as morphisms to
`U_i`. This is the pullback condition; it identifies the sources of the `ij`- and
`ik`-transports. Project-local helper for the module cocycle (C2). -/
theorem glueData_bridge_src (D : Scheme.GlueData.{u}) (i j k : D.J) :
    pullback.fst (D.f i j) (D.f i k) ≫ D.f i j
      = pullback.snd (D.f i j) (D.f i k) ≫ D.f i k := pullback.condition

/-- Triple-overlap bridge (middle): the `ij`-transition's target leg
`p^{ij} ≫ (t_ij ≫ f_ji)` to `U_j` coincides with the `jk`-transition's source leg
`(t'_ijk ≫ p^{jk}) ≫ f_jk`. Follows from `t_fac` and the pullback condition; it identifies
the target of the `ij`-transport with the source of the `jk`-transport. Project-local helper
for the module cocycle (C2). -/
theorem glueData_bridge_mid (D : Scheme.GlueData.{u}) (i j k : D.J) :
    pullback.fst (D.f i j) (D.f i k) ≫ (D.t i j ≫ D.f j i)
      = (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i)) ≫ D.f j k := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, ← Category.assoc, D.t_fac i j k,
    Category.assoc]

/-- Triple-overlap bridge (target): the `jk`-transition's target leg
`(t'_ijk ≫ p^{jk}) ≫ (t_jk ≫ f_kj)` to `U_k` coincides with the `ik`-transition's target
leg `p^{ik} ≫ (t_ik ≫ f_ki)`. This is the heart of the cocycle, derived from `t_fac`, the
pullback condition, `t_inv` and `cocycle`; it identifies the target of the composite
`jk`-after-`ij` transport with the target of the `ik`-transport. Project-local helper for
the module cocycle (C2). -/
theorem glueData_bridge_tgt (D : Scheme.GlueData.{u}) (i j k : D.J) :
    (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i)) ≫ (D.t j k ≫ D.f k j)
      = pullback.snd (D.f i j) (D.f i k) ≫ (D.t i k ≫ D.f k i) := by
  have key : pullback.fst (D.f k i) (D.f k j) ≫ D.f k i
      = D.t' k i j ≫ pullback.snd (D.f i j) (D.f i k) ≫ D.t i k ≫ D.f k i := by
    rw [D.t_fac_assoc k i j, ← Category.assoc (D.t k i) (D.t i k), D.t_inv, Category.id_comp]
  rw [Category.assoc, ← D.t_fac_assoc j k i,
    ← @pullback.condition _ _ _ _ _ (D.f k i) (D.f k j) _, key, D.cocycle_assoc i j k]

/-- **Gluing a sheaf of modules along an open cover given by a scheme glue datum**
(`def:scheme_modules_glue`). From a glue datum `D`, per-chart sheaves of modules `M i`,
and transition isomorphisms `g i j` comparing the two charts' sheaves over the overlap
`V (i,j)` (after pullback), produces a glued sheaf of `O_{D.glued}`-modules.

Project-local: Mathlib has no module descent over a scheme glue datum. -/
noncomputable def glue (D : Scheme.GlueData)
    (M : ∀ i, (D.U i).Modules)
    (g : ∀ i j, (Scheme.Modules.pullback (D.f i j)).obj (M i) ≅
        (Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j))
    -- (C1) self-identity: over the diagonal overlap `V (i,i)` (where `t i i = 𝟙`) the
    -- transition isomorphism is the identity, i.e. the canonical isomorphism induced by
    -- `f i i = t i i ≫ f i i` (blueprint `def:scheme_modules_glue` (C1)).
    (_hC1 : ∀ i, g i i = eqToIso (congrArg (fun φ => (Scheme.Modules.pullback φ).obj (M i))
        (show D.f i i = D.t i i ≫ D.f i i by rw [D.t_id i, Category.id_comp])))
    -- (C2) triple-overlap multiplicativity: over each triple overlap
    -- `V_ijk = V_ij ×_{U_i} V_ik` the base-change transports
    -- (`pullbackBaseChangeTransport`) of the three transition isomorphisms `g_ij`, `g_jk`,
    -- `g_ik` satisfy `ĝ_jk ∘ ĝ_ij = ĝ_ik`. The three `glueData_bridge_*` identities, applied
    -- through `pullbackCongr`, line up the endpoints so the equation is well typed
    -- (blueprint `def:scheme_modules_glue` (C2), `lem:modules_pullback_basechange_transport`).
    (_hC2 : ∀ i j k,
        pullbackBaseChangeTransport (pullback.fst (D.f i j) (D.f i k))
            (D.f i j) (D.t i j ≫ D.f j i) (g i j) ≪≫
          (Scheme.Modules.pullbackCongr (glueData_bridge_mid D i j k)).app (M j) ≪≫
          pullbackBaseChangeTransport (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
            (D.f j k) (D.t j k ≫ D.f k j) (g j k) ≪≫
          (Scheme.Modules.pullbackCongr (glueData_bridge_tgt D i j k)).app (M k)
        = (Scheme.Modules.pullbackCongr (glueData_bridge_src D i j k)).app (M i) ≪≫
          pullbackBaseChangeTransport (pullback.snd (D.f i j) (D.f i k))
            (D.f i k) (D.t i k ≫ D.f k i) (g i k)) :
    D.glued.Modules :=
  -- **Effective descent as an equalizer of pushforwards.** The glued sheaf is the
  -- equalizer of the two canonical maps `∏ᵢ (ιᵢ)_* Mᵢ ⇉ ∏_{ij} (j_ij)_* (f_ij^* Mᵢ)`
  -- (`j_ij = f_ij ≫ ιᵢ : V_ij ↪ X`): the first map restricts the `i`-th chart section to
  -- `V_ij`, the second restricts the `j`-th and transports it across the transition `g_ij`,
  -- using the glue condition `(t_ij ≫ f_ji) ≫ ιⱼ = f_ij ≫ ιᵢ`. The cocycle hypotheses
  -- `_hC1`/`_hC2` are not needed to *construct* the object (they pin down the chart
  -- restriction isomorphisms `glueRestrictionIso`, built downstream). Pushforward preserves
  -- the sheaf condition and limits, so this equalizer of sheaves of modules is again a sheaf.
  let Qfun : D.J × D.J → D.glued.Modules := fun p =>
    (Scheme.Modules.pushforward (D.f p.1 p.2 ≫ D.ι p.1)).obj
      ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1))
  let P : D.glued.Modules := ∏ᶜ fun i => (Scheme.Modules.pushforward (D.ι i)).obj (M i)
  -- first leg: restrict the `p.1`-chart section to the overlap `V (p.1, p.2)`
  let aComp : ∀ p : D.J × D.J,
      (Scheme.Modules.pushforward (D.ι p.1)).obj (M p.1) ⟶ Qfun p := fun p =>
    (Scheme.Modules.pushforward (D.ι p.1)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (D.f p.1 p.2)).unit.app (M p.1)) ≫
      (Scheme.Modules.pushforwardComp (D.f p.1 p.2) (D.ι p.1)).hom.app
        ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1))
  -- second leg: restrict the `p.2`-chart section, transport it across `g`, and reindex
  -- the immersion via the glue condition
  let bComp : ∀ p : D.J × D.J,
      (Scheme.Modules.pushforward (D.ι p.2)).obj (M p.2) ⟶ Qfun p := fun p =>
    (Scheme.Modules.pushforward (D.ι p.2)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction
          (D.t p.1 p.2 ≫ D.f p.2 p.1)).unit.app (M p.2)) ≫
      (Scheme.Modules.pushforwardComp (D.t p.1 p.2 ≫ D.f p.2 p.1) (D.ι p.2)).hom.app
        ((Scheme.Modules.pullback (D.t p.1 p.2 ≫ D.f p.2 p.1)).obj (M p.2)) ≫
      (Scheme.Modules.pushforward
        ((D.t p.1 p.2 ≫ D.f p.2 p.1) ≫ D.ι p.2)).map (g p.1 p.2).inv ≫
      (Scheme.Modules.pushforwardCongr
        (show (D.t p.1 p.2 ≫ D.f p.2 p.1) ≫ D.ι p.2 = D.f p.1 p.2 ≫ D.ι p.1 by
          rw [Category.assoc]; exact D.glue_condition p.1 p.2)).hom.app
        ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1))
  let a : P ⟶ ∏ᶜ Qfun := Pi.lift fun p => Pi.π _ p.1 ≫ aComp p
  let b : P ⟶ ∏ᶜ Qfun := Pi.lift fun p => Pi.π _ p.2 ≫ bComp p
  equalizer a b

/-- **Lift into the glued sheaf** (`def:gr_modules_glueHom`-adjacent primitive): a family of
morphisms `k i : W ⟶ (ι_i)_* M_i` whose two overlap restrictions agree (the hypothesis
`hk`, stated against the two legs of the descent equalizer) lifts to a morphism
`W ⟶ glue D M g _ _`. This is `equalizer.lift` for the descent equalizer of pushforwards;
it is the vehicle by which the tautological quotient is assembled from the chart
quotients. Project-local. -/
noncomputable def glueLift (D : Scheme.GlueData)
    (M : ∀ i, (D.U i).Modules)
    (g : ∀ i j, (Scheme.Modules.pullback (D.f i j)).obj (M i) ≅
        (Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j))
    (_hC1 : ∀ i, g i i = eqToIso (congrArg (fun φ => (Scheme.Modules.pullback φ).obj (M i))
        (show D.f i i = D.t i i ≫ D.f i i by rw [D.t_id i, Category.id_comp])))
    (_hC2 : ∀ i j k,
        pullbackBaseChangeTransport (pullback.fst (D.f i j) (D.f i k))
            (D.f i j) (D.t i j ≫ D.f j i) (g i j) ≪≫
          (Scheme.Modules.pullbackCongr (glueData_bridge_mid D i j k)).app (M j) ≪≫
          pullbackBaseChangeTransport (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
            (D.f j k) (D.t j k ≫ D.f k j) (g j k) ≪≫
          (Scheme.Modules.pullbackCongr (glueData_bridge_tgt D i j k)).app (M k)
        = (Scheme.Modules.pullbackCongr (glueData_bridge_src D i j k)).app (M i) ≪≫
          pullbackBaseChangeTransport (pullback.snd (D.f i j) (D.f i k))
            (D.f i k) (D.t i k ≫ D.f k i) (g i k))
    {W : D.glued.Modules}
    (k : ∀ i, W ⟶ (Scheme.Modules.pushforward (D.ι i)).obj (M i))
    (hk : ∀ p : D.J × D.J,
      k p.1 ≫
          ((Scheme.Modules.pushforward (D.ι p.1)).map
            ((Scheme.Modules.pullbackPushforwardAdjunction (D.f p.1 p.2)).unit.app (M p.1)) ≫
          (Scheme.Modules.pushforwardComp (D.f p.1 p.2) (D.ι p.1)).hom.app
            ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1)))
        = k p.2 ≫
          ((Scheme.Modules.pushforward (D.ι p.2)).map
            ((Scheme.Modules.pullbackPushforwardAdjunction
              (D.t p.1 p.2 ≫ D.f p.2 p.1)).unit.app (M p.2)) ≫
          (Scheme.Modules.pushforwardComp (D.t p.1 p.2 ≫ D.f p.2 p.1) (D.ι p.2)).hom.app
            ((Scheme.Modules.pullback (D.t p.1 p.2 ≫ D.f p.2 p.1)).obj (M p.2)) ≫
          (Scheme.Modules.pushforward
            ((D.t p.1 p.2 ≫ D.f p.2 p.1) ≫ D.ι p.2)).map (g p.1 p.2).inv ≫
          (Scheme.Modules.pushforwardCongr
            (show (D.t p.1 p.2 ≫ D.f p.2 p.1) ≫ D.ι p.2 = D.f p.1 p.2 ≫ D.ι p.1 by
              rw [Category.assoc]; exact D.glue_condition p.1 p.2)).hom.app
            ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1)))) :
    W ⟶ glue D M g _hC1 _hC2 :=
  equalizer.lift (Pi.lift k) (by
    apply Pi.hom_ext
    intro p
    simp only [Category.assoc, Limits.Pi.lift_π, Limits.Pi.lift_π_assoc]
    exact hk p)

/-! ### Pullback of free sheaves along an arbitrary scheme morphism

The functor of points (`AlgebraicGeometry.Grassmannian.functor`) acts on morphisms by
pullback, and for that one needs `f^* (O^n) ≅ O^n` for an *arbitrary* scheme morphism
`f`. Mathlib's `SheafOfModules.pullbackObjFreeIso` supplies this only when the underlying
site functor `Opens.map f.base` is `Final`; the previous chapters discharged that `Final`
hypothesis only for open immersions and isomorphisms. The first lemma below removes the
restriction entirely: `Opens.map f.base` is `Final` for *every* scheme morphism, because
the structured-arrow category over any open `V` has a terminal object (the whole space
`⊤`). With that in hand, `pullbackFreeIso` and `pullback_isLocallyFreeOfRank` hold for all
morphisms. -/

/-- For an arbitrary scheme morphism `φ`, the site functor `Opens.map φ.base` is `Final`:
over any open `V` of the target the structured-arrow category `{U : V ≤ φ⁻¹ U}` has the
terminal object `U = ⊤`, hence is connected. This is the missing ingredient that makes
`SheafOfModules.pullbackObjUnitToUnit`/`pullbackObjFreeIso` applicable to *every* morphism,
not just to open immersions. Project-local. -/
lemma opensMap_final {T' T : Scheme.{u}} (φ : T' ⟶ T) :
    (TopologicalSpace.Opens.map φ.base).Final := by
  constructor
  intro V
  set top : StructuredArrow V (TopologicalSpace.Opens.map φ.base) :=
    StructuredArrow.mk (Y := (⊤ : T.Opens)) (homOfLE le_top)
  haveI : Nonempty (StructuredArrow V (TopologicalSpace.Opens.map φ.base)) := ⟨top⟩
  apply zigzag_isConnected
  intro s t
  have hs : s ⟶ top := StructuredArrow.homMk (homOfLE le_top) (Subsingleton.elim _ _)
  have ht : t ⟶ top := StructuredArrow.homMk (homOfLE le_top) (Subsingleton.elim _ _)
  exact Relation.ReflTransGen.trans
    (Relation.ReflTransGen.single (Or.inl ⟨hs⟩))
    (Relation.ReflTransGen.single (Or.inr ⟨ht⟩))

/-- **Pullback of a free sheaf of modules is free, for any scheme morphism**: for
`φ : T' ⟶ T` and an index type `I`, `φ^*(O_T^{⊕I}) ≅ O_{T'}^{⊕I}`. Built from
`SheafOfModules.pullbackObjFreeIso` once `opensMap_final` supplies the `Final` instance.
Project-local. -/
noncomputable def pullbackFreeIso {T' T : Scheme.{u}} (φ : T' ⟶ T) (I : Type u) :
    (Scheme.Modules.pullback φ).obj (SheafOfModules.free (R := T.ringCatSheaf) I)
      ≅ SheafOfModules.free (R := T'.ringCatSheaf) I := by
  haveI := opensMap_final φ
  exact SheafOfModules.pullbackObjFreeIso.{u} φ.toRingCatSheafHom I

/-- The free-pullback comparison is natural in the base morphism: equal morphisms give
`pullbackFreeIso`s related by the `eqToHom` transport of their (differing) sources.
Project-local — used for the bundle-transition self-identity. -/
lemma pullbackFreeIso_eqToHom {T' T : Scheme.{u}} {φ ψ : T' ⟶ T} (h : φ = ψ) (I : Type u) :
    eqToHom (congrArg
        (fun α => (Scheme.Modules.pullback α).obj (SheafOfModules.free (R := T.ringCatSheaf) I)) h)
        ≫ (pullbackFreeIso ψ I).hom
      = (pullbackFreeIso φ I).hom := by
  subst h
  exact Category.id_comp _

/-- Iso-level free-pullback cancellation: for equal base morphisms `φ = ψ`, the composite
`pullbackFreeIso φ ≪≫ (pullbackFreeIso ψ).symm` is the `eqToIso` transport between the
(differing) pullback sources. Proved generically (`φ`, `ψ` variables, `subst`), so applying
it never forces the kernel to whnf a concrete immersion — the leaner replacement for the
`.hom`-level cast chain in `bundleTransition_self`. Project-local. -/
lemma pullbackFreeIso_trans_symm_eqToIso {T' T : Scheme.{u}} {φ ψ : T' ⟶ T} (h : φ = ψ)
    (I : Type u) :
    pullbackFreeIso φ I ≪≫ (pullbackFreeIso ψ I).symm
      = eqToIso (congrArg
          (fun α => (Scheme.Modules.pullback α).obj (SheafOfModules.free (R := T.ringCatSheaf) I))
          h) := by
  subst h
  apply Iso.ext
  exact (pullbackFreeIso φ I).hom_inv_id

end AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry.Scheme.Modules

-- The first namespace block above is intentionally closed after the basic gluing
-- construction. Reinstall the universe-pinned adjoint instances for the coherence and
-- effective-descent developments below: `local instance`s do not cross a namespace end.
local instance schemeSheafPushforwardIsRightAdjointBridge_coherence
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (SheafOfModules.pushforward.{u}
      f.toRingCatSheafHom).IsRightAdjoint :=
  inferInstanceAs ((Scheme.Modules.pushforward f).IsRightAdjoint)

/-- **Unit coherence (`map_id` keystone, `lem:gr_pullbackObjUnitToUnit_id`).** The
Mathlib free-pullback comparison `SheafOfModules.pullbackObjUnitToUnit` at the identity
morphism agrees, on the unit sheaf, with the scheme-level pseudofunctor identity
`Scheme.Modules.pullbackId`. Project-local: bridges `pullbackObjFreeIso` to the
pseudofunctor `pullbackId`. -/
lemma pullbackObjUnitToUnit_id {T : Scheme.{u}} :
    SheafOfModules.pullbackObjUnitToUnit.{u} (Scheme.Hom.toRingCatSheafHom (𝟙 T))
      = (Scheme.Modules.pullbackId T).hom.app (SheafOfModules.unit T.ringCatSheaf) := by
  change ((SheafOfModules.pullbackPushforwardAdjunction.{u}
      (Scheme.Hom.toRingCatSheafHom (𝟙 T))).homEquiv _ _).symm
        (SheafOfModules.unitToPushforwardObjUnit.{u}
          (Scheme.Hom.toRingCatSheafHom (𝟙 T))) = _
  let e := (SheafOfModules.pullbackPushforwardAdjunction.{u}
      (Scheme.Hom.toRingCatSheafHom (𝟙 T))).homEquiv
        (SheafOfModules.unit T.ringCatSheaf) (SheafOfModules.unit T.ringCatSheaf)
  change e.symm _ = _
  refine (Equiv.symm_apply_eq e).2 ?_
  have he : e ((Scheme.Modules.pullbackId T).hom.app
        (SheafOfModules.unit T.ringCatSheaf)) =
      (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (Scheme.Hom.toRingCatSheafHom (𝟙 T))).unit.app
          (SheafOfModules.unit T.ringCatSheaf) ≫
        (SheafOfModules.pushforward.{u}
          (Scheme.Hom.toRingCatSheafHom (𝟙 T))).map
          ((Scheme.Modules.pullbackId T).hom.app
            (SheafOfModules.unit T.ringCatSheaf)) :=
    Adjunction.homEquiv_unit _ _ _ _
  refine Eq.trans ?_ he.symm
  have h := CategoryTheory.unit_conjugateEquiv Adjunction.id
    (SheafOfModules.pullbackPushforwardAdjunction.{u}
      (Scheme.Hom.toRingCatSheafHom (𝟙 T)))
    (Scheme.Modules.pullbackId T).hom (SheafOfModules.unit T.ringCatSheaf)
  simp only [Adjunction.id_unit, NatTrans.id_app, Functor.id_obj] at h
  rw [← h]
  -- term-mode `id_comp` (positional `rw [Category.id_comp]` hits the `T.Modules` instance diamond)
  refine Eq.trans ?_ (Category.id_comp _).symm
  -- the `conjugateEquiv` term sits in unfolded `SheafOfModules` form; bridge to the
  -- scheme-level pseudofunctor coherence by defeq, then it equals `(pushforwardId).inv`.
  have key : (CategoryTheory.conjugateEquiv Adjunction.id
        (SheafOfModules.pullbackPushforwardAdjunction.{u} (Scheme.Hom.toRingCatSheafHom (𝟙 T)))
        (Scheme.Modules.pullbackId T).hom)
      = (Scheme.Modules.pushforwardId T).inv :=
    Scheme.Modules.conjugateEquiv_pullbackId_hom T
  rw [key]
  ext Y
  -- both sides evaluate the unit section `1` through identity-like maps
  rfl

/-- **Free coherence (`map_id`).** `pullbackFreeIso (𝟙 T) I` agrees, on the free sheaf,
with the pseudofunctor identity `pullbackId`. Reduces to `pullbackObjUnitToUnit_id` by
coproduct extensionality (`free = ∐ unit`). Project-local. -/
lemma pullbackFreeIso_id {T : Scheme.{u}} (I : Type u) :
    (Scheme.Modules.pullbackFreeIso (𝟙 T) I).hom
      = (Scheme.Modules.pullbackId T).hom.app (SheafOfModules.free (R := T.ringCatSheaf) I) := by
  haveI := Scheme.Modules.opensMap_final (𝟙 T)
  -- Work in the scheme-level wrapper so the stored adjunction instance is shared with
  -- `pullbackId`; this also pins the module universe in colimit preservation.
  refine Cofan.IsColimit.hom_ext (isColimitCofanMkObjOfIsColimit
    (Scheme.Modules.pullback (𝟙 T)) _ _
    (SheafOfModules.isColimitFreeCofan (R := T.ringCatSheaf) I)) _ _ (fun i => ?_)
  simp only [cofan_mk_inj]
  -- Pure term-mode chain (positional `rw`/`simp` fail under the `SheafOfModules`/`X.Modules`
  -- instance diamond — they cannot match identical-printing terms with different implicit
  -- instance arguments; `exact`/`Eq.trans` unify up to defeq, which is what is needed here).
  -- LHS: free-pullback comparison.  Then transport the unit coherence through `· ≫ ιFree i`,
  -- and finally undo by naturality of `pullbackId.hom` (RHS).
  exact (SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom.{u}
        (Scheme.Hom.toRingCatSheafHom (𝟙 T)) i).trans
      ((congrArg (· ≫ SheafOfModules.ιFree (R := T.ringCatSheaf) i) pullbackObjUnitToUnit_id).trans
        ((Scheme.Modules.pullbackId T).hom.naturality
          (SheafOfModules.ιFree (R := T.ringCatSheaf) i)).symm)

/-- **Mate compatibility of `homEquiv`.** For adjunctions `adj₁ : L₁ ⊣ R₁`, `adj₂ : L₂ ⊣ R₂`
and a natural transformation `α : L₂ ⟶ L₁`, transposing `α.app c ≫ f` under `adj₂` equals
transposing `f` under `adj₁` post-composed with the conjugate transformation
(`CategoryTheory.conjugateEquiv adj₁ adj₂ α`) evaluated at `d`. Project-local; derived from
`CategoryTheory.unit_conjugateEquiv` + naturality of the conjugate transformation. -/
lemma homEquiv_conjugateEquiv_app {𝒞 𝒟 : Type*} [CategoryTheory.Category 𝒞]
    [CategoryTheory.Category 𝒟] {L₁ L₂ : 𝒞 ⥤ 𝒟} {R₁ R₂ : 𝒟 ⥤ 𝒞}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁) {c : 𝒞} {d : 𝒟}
    (f : L₁.obj c ⟶ d) :
    adj₂.homEquiv c d (α.app c ≫ f)
      = adj₁.homEquiv c d f ≫ (CategoryTheory.conjugateEquiv adj₁ adj₂ α).app d := by
  -- `rw` is unreliable at locating these right-associated sub-composites, so we assemble the
  -- proof entirely from term-mode whiskering equalities and chain them with `.trans`.
  have h1 := CategoryTheory.unit_conjugateEquiv adj₁ adj₂ α c
  -- the two `homEquiv_unit` expansions, with all implicits fixed by the stated types.
  have huA : adj₂.homEquiv c d (α.app c ≫ f)
      = adj₂.unit.app c ≫ R₂.map (α.app c ≫ f) :=
    Adjunction.homEquiv_unit adj₂ c d (α.app c ≫ f)
  have huB : adj₁.homEquiv c d f = adj₁.unit.app c ≫ R₁.map f :=
    Adjunction.homEquiv_unit adj₁ c d f
  -- LHS transpose, in left-bracketed shape.
  have e1 : adj₂.homEquiv c d (α.app c ≫ f)
      = (adj₂.unit.app c ≫ R₂.map (α.app c)) ≫ R₂.map f :=
    huA.trans <| (CategoryTheory.whisker_eq (adj₂.unit.app c) (R₂.map_comp (α.app c) f)).trans
      (Category.assoc _ _ _).symm
  -- RHS transpose, in the same left-bracketed shape.
  have e2 : adj₁.homEquiv c d f ≫ (CategoryTheory.conjugateEquiv adj₁ adj₂ α).app d
      = (adj₁.unit.app c ≫ (CategoryTheory.conjugateEquiv adj₁ adj₂ α).app (L₁.obj c))
          ≫ R₂.map f :=
    (CategoryTheory.eq_whisker huB
        ((CategoryTheory.conjugateEquiv adj₁ adj₂ α).app d)).trans <|
      (Category.assoc _ _ _).trans <|
        (CategoryTheory.whisker_eq (adj₁.unit.app c)
          ((CategoryTheory.conjugateEquiv adj₁ adj₂ α).naturality f)).trans
          (Category.assoc _ _ _).symm
  exact e1.trans ((CategoryTheory.eq_whisker h1.symm (R₂.map f)).trans e2.symm)

/-- **Unit coherence (`map_comp` keystone, `lem:gr_pullbackObjUnitToUnit_comp`).** The composite
analogue of `pullbackObjUnitToUnit_id`: the Mathlib free-pullback comparison at a composite
morphism `b ∘ a` factors through the pseudofunctor composition `pullbackComp`. Project-local.

Transposing both sides under the composite pullback-pushforward adjunction: the LHS collapses
by `homEquiv_conjugateEquiv_app` to `uTPU (b ≫ a) ≫ (conjugate of pullbackComp.hom)`, the
conjugate is `(pushforwardComp).inv` via `conjugateEquiv_pullbackComp_inv` + `conjugateEquiv_comm`,
and the RHS collapses by `homEquiv` naturality to `uTPU a ≫ pushforward a (uTPU b)`;
both reduce to the unit-section identity (`pushforwardComp_inv_app_app = 𝟙`). -/
lemma gr_pullbackObjUnitToUnit_comp {Tx Ty Tz : Scheme.{u}} (a : Ty ⟶ Tx) (b : Tz ⟶ Ty) :
    (Scheme.Modules.pullbackComp b a).hom.app (SheafOfModules.unit Tx.ringCatSheaf) ≫
        SheafOfModules.pullbackObjUnitToUnit.{u} (Scheme.Hom.toRingCatSheafHom (b ≫ a))
      = (Scheme.Modules.pullback b).map
          (SheafOfModules.pullbackObjUnitToUnit.{u} (Scheme.Hom.toRingCatSheafHom a)) ≫
        SheafOfModules.pullbackObjUnitToUnit.{u} (Scheme.Hom.toRingCatSheafHom b) := by
  -- Work with the Scheme-level adjunctions so `conjugateEquiv_pullbackComp_inv` lines up.
  apply ((Scheme.Modules.pullbackPushforwardAdjunction a).comp
      (Scheme.Modules.pullbackPushforwardAdjunction b)).homEquiv _ _ |>.injective
  -- abbreviations
  set adjA := Scheme.Modules.pullbackPushforwardAdjunction a
  set adjB := Scheme.Modules.pullbackPushforwardAdjunction b
  set adjBA := Scheme.Modules.pullbackPushforwardAdjunction (b ≫ a)
  -- LHS: collapse via the mate-compatibility helper (term-mode `.trans`, so `pullbackComp`
  -- stays OPAQUE and matching is up to defeq rather than syntactic `rw`).
  have hL := homEquiv_conjugateEquiv_app adjBA (adjA.comp adjB)
      (Scheme.Modules.pullbackComp b a).hom
      (f := SheafOfModules.pullbackObjUnitToUnit.{u} (Scheme.Hom.toRingCatSheafHom (b ≫ a)))
  -- transpose of `pullbackObjUnitToUnit` is `unitToPushforwardObjUnit` (used via defeq).
  have hL2 : adjBA.homEquiv _ _
        (SheafOfModules.pullbackObjUnitToUnit.{u} (Scheme.Hom.toRingCatSheafHom (b ≫ a)))
      = SheafOfModules.unitToPushforwardObjUnit.{u} (Scheme.Hom.toRingCatSheafHom (b ≫ a)) :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit.{u}
      (Scheme.Hom.toRingCatSheafHom (b ≫ a))
  have huA : adjA.homEquiv _ _
        (SheafOfModules.pullbackObjUnitToUnit.{u} (Scheme.Hom.toRingCatSheafHom a))
      = SheafOfModules.unitToPushforwardObjUnit.{u} (Scheme.Hom.toRingCatSheafHom a) :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit.{u}
      (Scheme.Hom.toRingCatSheafHom a)
  have huB : adjB.homEquiv _ _
        (SheafOfModules.pullbackObjUnitToUnit.{u} (Scheme.Hom.toRingCatSheafHom b))
      = SheafOfModules.unitToPushforwardObjUnit.{u} (Scheme.Hom.toRingCatSheafHom b) :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit.{u}
      (Scheme.Hom.toRingCatSheafHom b)
  -- the conjugate of `pullbackComp.hom` is `(pushforwardComp).inv`.
  have hcomm := CategoryTheory.conjugateEquiv_comm (adj₁ := adjA.comp adjB) (adj₂ := adjBA)
    (show (Scheme.Modules.pullbackComp b a).hom ≫ (Scheme.Modules.pullbackComp b a).inv = 𝟙 _
      from (Scheme.Modules.pullbackComp b a).hom_inv_id)
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at hcomm
  have hConj : CategoryTheory.conjugateEquiv adjBA (adjA.comp adjB)
        (Scheme.Modules.pullbackComp b a).hom
      = (Scheme.Modules.pushforwardComp b a).inv :=
    (CategoryTheory.Iso.hom_comp_eq_id _).mp hcomm
  -- RHS computation, term-mode (so the Scheme/SheafOfModules `pullback` defeq is bridged).
  have hR : (adjA.comp adjB).homEquiv _ _
        ((Scheme.Modules.pullback b).map
          (SheafOfModules.pullbackObjUnitToUnit.{u} (Scheme.Hom.toRingCatSheafHom a)) ≫
          SheafOfModules.pullbackObjUnitToUnit.{u} (Scheme.Hom.toRingCatSheafHom b))
      = SheafOfModules.unitToPushforwardObjUnit.{u} (Scheme.Hom.toRingCatSheafHom a) ≫
        (Scheme.Modules.pushforward a).map
          (SheafOfModules.unitToPushforwardObjUnit.{u} (Scheme.Hom.toRingCatSheafHom b)) := by
    rw [Adjunction.comp_homEquiv]
    change adjA.homEquiv _ _ (adjB.homEquiv _ _ (_ ≫ _)) = _
    have hInner : adjB.homEquiv _ _
          ((Scheme.Modules.pullback b).map
              (SheafOfModules.pullbackObjUnitToUnit.{u}
                (Scheme.Hom.toRingCatSheafHom a)) ≫
            SheafOfModules.pullbackObjUnitToUnit.{u}
              (Scheme.Hom.toRingCatSheafHom b))
        = SheafOfModules.pullbackObjUnitToUnit.{u}
              (Scheme.Hom.toRingCatSheafHom a) ≫
            SheafOfModules.unitToPushforwardObjUnit.{u}
              (Scheme.Hom.toRingCatSheafHom b) :=
      (Adjunction.homEquiv_naturality_left adjB _ _).trans
        (CategoryTheory.whisker_eq _ huB)
    have hOuter : adjA.homEquiv _ _
          (SheafOfModules.pullbackObjUnitToUnit.{u}
              (Scheme.Hom.toRingCatSheafHom a) ≫
            SheafOfModules.unitToPushforwardObjUnit.{u}
              (Scheme.Hom.toRingCatSheafHom b))
        = SheafOfModules.unitToPushforwardObjUnit.{u}
              (Scheme.Hom.toRingCatSheafHom a) ≫
            (Scheme.Modules.pushforward a).map
              (SheafOfModules.unitToPushforwardObjUnit.{u}
                (Scheme.Hom.toRingCatSheafHom b)) :=
      (Adjunction.homEquiv_naturality_right adjA _ _).trans
        (CategoryTheory.eq_whisker huA _)
    exact (congrArg (adjA.homEquiv _ _) hInner).trans hOuter
  -- the section-level identity: `(pushforwardComp).inv.app` is the identity on sections.
  have hMid : SheafOfModules.unitToPushforwardObjUnit.{u} (Scheme.Hom.toRingCatSheafHom (b ≫ a)) ≫
        (Scheme.Modules.pushforwardComp b a).inv.app (SheafOfModules.unit Tz.ringCatSheaf)
      = SheafOfModules.unitToPushforwardObjUnit.{u} (Scheme.Hom.toRingCatSheafHom a) ≫
        (Scheme.Modules.pushforward a).map
          (SheafOfModules.unitToPushforwardObjUnit.{u} (Scheme.Hom.toRingCatSheafHom b)) := by
    -- definitional: `unitToPushforwardObjUnit` sections are `φ.hom.app`,
    -- `pushforwardComp_inv_app_app = 𝟙`, and `(b ≫ a)⁻¹ U = b⁻¹(a⁻¹ U)`.
    rfl
  -- assemble in steps to avoid a single large `isDefEq` over the opaque `pullbackComp`.
  have e1 := hL.trans (congrArg
    (· ≫ (CategoryTheory.conjugateEquiv adjBA (adjA.comp adjB)
            (Scheme.Modules.pullbackComp b a).hom).app (SheafOfModules.unit Tz.ringCatSheaf)) hL2)
  have e2 := congrArg
    (SheafOfModules.unitToPushforwardObjUnit.{u} (Scheme.Hom.toRingCatSheafHom (b ≫ a)) ≫
      NatTrans.app · (SheafOfModules.unit Tz.ringCatSheaf)) hConj
  exact e1.trans (e2.trans (hMid.trans hR.symm))

/-- **Free coherence (`map_comp`).** Composite analogue of `pullbackFreeIso_id`: the
free-pullback isomorphism at a composite `b ∘ a` factors through the pseudofunctor composition
`pullbackComp`. Reduces, by coproduct extensionality (`free = ∐ unit`), to the unit coherence
`gr_pullbackObjUnitToUnit_comp`. Project-local. -/
lemma pullbackFreeIso_comp {Tx Ty Tz : Scheme.{u}} (a : Ty ⟶ Tx) (b : Tz ⟶ Ty) (I : Type u) :
    (Scheme.Modules.pullbackComp b a).hom.app (SheafOfModules.free (R := Tx.ringCatSheaf) I) ≫
        (pullbackFreeIso (b ≫ a) I).hom
      = (Scheme.Modules.pullback b).map (pullbackFreeIso a I).hom ≫
        (pullbackFreeIso b I).hom := by
  haveI := opensMap_final (b ≫ a)
  haveI := opensMap_final a
  haveI := opensMap_final b
  refine Cofan.IsColimit.hom_ext (isColimitCofanMkObjOfIsColimit
    (Scheme.Modules.pullback a ⋙ Scheme.Modules.pullback b) _ _
    (SheafOfModules.isColimitFreeCofan (R := Tx.ringCatSheaf) I)) _ _ (fun i => ?_)
  simp only [cofan_mk_inj]
  -- Pure term-mode (positional `rw`/`simp` fail under the `SheafOfModules`/`X.Modules` diamond).
  -- Both injections reduce, via `pullbackComp.hom` naturality and the free-cofan comparison
  -- `pullback_map_ιFree_comp_pullbackObjFreeIso_hom`, to `gr_pullbackObjUnitToUnit_comp` whiskered.
  -- the free-cofan comparison, restated in `pullbackFreeIso` form (defeq) so `congrArg` matches.
  -- each pullback changes the base ring sheaf: `Tx ↝ Ty ↝ Tz`.
  have key_ba : (Scheme.Modules.pullback (b ≫ a)).map
          (SheafOfModules.ιFree (R := Tx.ringCatSheaf) i) ≫
        (pullbackFreeIso (b ≫ a) I).hom
      = SheafOfModules.pullbackObjUnitToUnit.{u} (Scheme.Hom.toRingCatSheafHom (b ≫ a)) ≫
        SheafOfModules.ιFree (R := Tz.ringCatSheaf) i :=
    SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom.{u}
      (Scheme.Hom.toRingCatSheafHom (b ≫ a)) (I := I) i
  have key_a : (Scheme.Modules.pullback a).map (SheafOfModules.ιFree (R := Tx.ringCatSheaf) i) ≫
        (pullbackFreeIso a I).hom
      = SheafOfModules.pullbackObjUnitToUnit.{u} (Scheme.Hom.toRingCatSheafHom a) ≫
        SheafOfModules.ιFree (R := Ty.ringCatSheaf) i :=
    SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom.{u}
      (Scheme.Hom.toRingCatSheafHom a) (I := I) i
  have key_b : (Scheme.Modules.pullback b).map (SheafOfModules.ιFree (R := Ty.ringCatSheaf) i) ≫
        (pullbackFreeIso b I).hom
      = SheafOfModules.pullbackObjUnitToUnit.{u} (Scheme.Hom.toRingCatSheafHom b) ≫
        SheafOfModules.ιFree (R := Tz.ringCatSheaf) i :=
    SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom.{u}
      (Scheme.Hom.toRingCatSheafHom b) (I := I) i
  -- LHS: naturality of `pullbackComp.hom` + free-cofan comparison at `b ≫ a`.
  have hLHS :
      (Scheme.Modules.pullback a ⋙ Scheme.Modules.pullback b).map
            (SheafOfModules.ιFree (R := Tx.ringCatSheaf) i) ≫
        (Scheme.Modules.pullbackComp b a).hom.app (SheafOfModules.free (R := Tx.ringCatSheaf) I) ≫
          (pullbackFreeIso (b ≫ a) I).hom
      = ((Scheme.Modules.pullbackComp b a).hom.app (SheafOfModules.unit Tx.ringCatSheaf) ≫
          SheafOfModules.pullbackObjUnitToUnit.{u} (Scheme.Hom.toRingCatSheafHom (b ≫ a))) ≫
            (SheafOfModules.ιFree (R := Tz.ringCatSheaf) i) :=
    calc (Scheme.Modules.pullback a ⋙ Scheme.Modules.pullback b).map
            (SheafOfModules.ιFree (R := Tx.ringCatSheaf) i) ≫
          (Scheme.Modules.pullbackComp b a).hom.app (SheafOfModules.free (R := Tx.ringCatSheaf) I) ≫
            (pullbackFreeIso (b ≫ a) I).hom
        = ((Scheme.Modules.pullback a ⋙ Scheme.Modules.pullback b).map
              (SheafOfModules.ιFree (R := Tx.ringCatSheaf) i) ≫
            (Scheme.Modules.pullbackComp b a).hom.app
              (SheafOfModules.free (R := Tx.ringCatSheaf) I)) ≫
            (pullbackFreeIso (b ≫ a) I).hom := (Category.assoc _ _ _).symm
      _ = ((Scheme.Modules.pullbackComp b a).hom.app (SheafOfModules.unit Tx.ringCatSheaf) ≫
            (Scheme.Modules.pullback (b ≫ a)).map (SheafOfModules.ιFree (R := Tx.ringCatSheaf) i)) ≫
            (pullbackFreeIso (b ≫ a) I).hom :=
          congrArg (· ≫ (pullbackFreeIso (b ≫ a) I).hom)
            ((Scheme.Modules.pullbackComp b a).hom.naturality
              (SheafOfModules.ιFree (R := Tx.ringCatSheaf) i))
      _ = (Scheme.Modules.pullbackComp b a).hom.app (SheafOfModules.unit Tx.ringCatSheaf) ≫
            (Scheme.Modules.pullback (b ≫ a)).map (SheafOfModules.ιFree (R := Tx.ringCatSheaf) i) ≫
              (pullbackFreeIso (b ≫ a) I).hom := Category.assoc _ _ _
      _ = (Scheme.Modules.pullbackComp b a).hom.app (SheafOfModules.unit Tx.ringCatSheaf) ≫
            SheafOfModules.pullbackObjUnitToUnit.{u} (Scheme.Hom.toRingCatSheafHom (b ≫ a)) ≫
              (SheafOfModules.ιFree (R := Tz.ringCatSheaf) i) :=
          congrArg ((Scheme.Modules.pullbackComp b a).hom.app
            (SheafOfModules.unit Tx.ringCatSheaf) ≫ ·) key_ba
      _ = ((Scheme.Modules.pullbackComp b a).hom.app (SheafOfModules.unit Tx.ringCatSheaf) ≫
            SheafOfModules.pullbackObjUnitToUnit.{u} (Scheme.Hom.toRingCatSheafHom (b ≫ a))) ≫
              (SheafOfModules.ιFree (R := Tz.ringCatSheaf) i) := (Category.assoc _ _ _).symm
  -- RHS: split the composite functor, free-cofan comparison at `a` then at `b`.
  have hmid :
      (Scheme.Modules.pullback a ⋙ Scheme.Modules.pullback b).map
            (SheafOfModules.ιFree (R := Tx.ringCatSheaf) i) ≫
        (Scheme.Modules.pullback b).map (pullbackFreeIso a I).hom
      = (Scheme.Modules.pullback b).map
            (SheafOfModules.pullbackObjUnitToUnit.{u} (Scheme.Hom.toRingCatSheafHom a)) ≫
          (Scheme.Modules.pullback b).map (SheafOfModules.ιFree (R := Ty.ringCatSheaf) i) :=
    ((Scheme.Modules.pullback b).map_comp
        ((Scheme.Modules.pullback a).map (SheafOfModules.ιFree (R := Tx.ringCatSheaf) i))
        (pullbackFreeIso a I).hom).symm.trans
      ((congrArg (Scheme.Modules.pullback b).map key_a).trans
        ((Scheme.Modules.pullback b).map_comp
          (SheafOfModules.pullbackObjUnitToUnit.{u} (Scheme.Hom.toRingCatSheafHom a))
          (SheafOfModules.ιFree (R := Ty.ringCatSheaf) i)))
  have hRHS :
      (Scheme.Modules.pullback a ⋙ Scheme.Modules.pullback b).map
            (SheafOfModules.ιFree (R := Tx.ringCatSheaf) i) ≫
        (Scheme.Modules.pullback b).map (pullbackFreeIso a I).hom ≫ (pullbackFreeIso b I).hom
      = ((Scheme.Modules.pullback b).map
            (SheafOfModules.pullbackObjUnitToUnit.{u} (Scheme.Hom.toRingCatSheafHom a)) ≫
          SheafOfModules.pullbackObjUnitToUnit.{u} (Scheme.Hom.toRingCatSheafHom b)) ≫
            (SheafOfModules.ιFree (R := Tz.ringCatSheaf) i) := by
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ (pullbackFreeIso b I).hom) hmid).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((Scheme.Modules.pullback b).map
      (SheafOfModules.pullbackObjUnitToUnit.{u} (Scheme.Hom.toRingCatSheafHom a)) ≫ ·)
        key_b).trans ?_
    exact (Category.assoc _ _ _).symm
  exact hLHS.trans ((congrArg (· ≫ (SheafOfModules.ιFree (R := Tz.ringCatSheaf) i))
    (gr_pullbackObjUnitToUnit_comp a b)).trans hRHS.symm)

/-! ### Cast-collapse of `pullbackCongr` against the free-pullback comparisons

The three transports of the bundle cocycle are interleaved with `pullbackCongr` casts
(the `glueData_bridge_*` endpoint alignments). The next three lemmas collapse those casts
against the free-pullback comparisons `pullbackFreeIso`. Each is generic in the (equal)
base morphisms and proved by `subst`, so applying them never forces the kernel to whnf a
concrete immersion (the `pullbackFreeIso_trans_symm_eqToIso` discipline). -/

/-- Closed zig-zag: `Q_φ⁻¹ ≫ pullbackCongr(h).app ≫ Q_ψ = 𝟙` for equal base morphisms
`φ = ψ`. Project-local helper for the C2 endpoint alignment. -/
@[reassoc]
lemma pullbackFreeIso_inv_congr_hom {T' T : Scheme.{u}} {φ ψ : T' ⟶ T} (h : φ = ψ)
    (I : Type u) :
    (pullbackFreeIso φ I).inv ≫
        ((Scheme.Modules.pullbackCongr h).app
          (SheafOfModules.free (R := T.ringCatSheaf) I)).hom ≫
        (pullbackFreeIso ψ I).hom
      = 𝟙 _ := by
  subst h
  change
    (pullbackFreeIso φ I).inv ≫ 𝟙 _ ≫
        (pullbackFreeIso φ I).hom = 𝟙 _
  exact (CategoryTheory.whisker_eq _ (Category.id_comp _)).trans
    (pullbackFreeIso φ I).inv_hom_id

/-- Left absorption: `pullbackCongr(h).app ≫ Q_ψ = Q_φ` for equal base morphisms `φ = ψ`.
Project-local helper for the C2 endpoint alignment (source bridge). -/
@[reassoc]
lemma pullbackCongr_hom_app_free {T' T : Scheme.{u}} {φ ψ : T' ⟶ T} (h : φ = ψ)
    (I : Type u) :
    ((Scheme.Modules.pullbackCongr h).app
        (SheafOfModules.free (R := T.ringCatSheaf) I)).hom ≫
        (pullbackFreeIso ψ I).hom
      = (pullbackFreeIso φ I).hom := by
  subst h
  exact Category.id_comp _

/-- Right absorption: `Q_φ⁻¹ ≫ pullbackCongr(h).app = Q_ψ⁻¹` for equal base morphisms
`φ = ψ`. Project-local helper for the C2 endpoint alignment (target bridge). -/
@[reassoc]
lemma pullbackFreeIso_inv_congr {T' T : Scheme.{u}} {φ ψ : T' ⟶ T} (h : φ = ψ)
    (I : Type u) :
    (pullbackFreeIso φ I).inv ≫
        ((Scheme.Modules.pullbackCongr h).app
          (SheafOfModules.free (R := T.ringCatSheaf) I)).hom
      = (pullbackFreeIso ψ I).inv := by
  subst h
  exact Category.comp_id _

/-- Inverse-side absorption of the congruence cast against the free-pullback comparison:
`pullbackCongr(h).inv.app ≫ Q_φ = Q_ψ` for equal base morphisms `φ = ψ`. Generic-`subst`
companion of `pullbackCongr_hom_app_free`. Project-local helper for the tautological
quotient overlap. -/
@[reassoc]
lemma pullbackCongr_inv_app_free {T' T : Scheme.{u}} {φ ψ : T' ⟶ T} (h : φ = ψ)
    (I : Type u) :
    (Scheme.Modules.pullbackCongr h).inv.app
        (SheafOfModules.free (R := T.ringCatSheaf) I) ≫
        (pullbackFreeIso φ I).hom
      = (pullbackFreeIso ψ I).hom := by
  subst h
  exact Category.id_comp _

/-- Cancellation of the pseudofunctor-composition cast against the pulled-back source
comparison: `(pullbackComp b a).inv.app (free) ≫ (pullback b).map Q_a = Q_{b≫a} ≫ Q_b⁻¹`.
Direct consequence of the free coherence `pullbackFreeIso_comp`. Project-local helper for
the tautological quotient overlap. -/
@[reassoc]
lemma pullbackComp_inv_app_free_map {V U X : Scheme.{u}} (b : V ⟶ U) (a : U ⟶ X)
    (I : Type u) :
    (Scheme.Modules.pullbackComp b a).inv.app
        (SheafOfModules.free (R := X.ringCatSheaf) I) ≫
        (Scheme.Modules.pullback b).map (pullbackFreeIso a I).hom
      = (pullbackFreeIso (b ≫ a) I).hom ≫ (pullbackFreeIso b I).inv := by
  let Qb := pullbackFreeIso b I
  apply (Iso.cancel_iso_hom_right _ _ Qb).mp
  calc
    ((Scheme.Modules.pullbackComp b a).inv.app
          (SheafOfModules.free (R := X.ringCatSheaf) I) ≫
        (Scheme.Modules.pullback b).map (pullbackFreeIso a I).hom) ≫
        (pullbackFreeIso b I).hom =
      (Scheme.Modules.pullbackComp b a).inv.app
          (SheafOfModules.free (R := X.ringCatSheaf) I) ≫
        ((Scheme.Modules.pullback b).map (pullbackFreeIso a I).hom ≫
          (pullbackFreeIso b I).hom) :=
      Category.assoc _ _ _
    _ = (Scheme.Modules.pullbackComp b a).inv.app
          (SheafOfModules.free (R := X.ringCatSheaf) I) ≫
        ((Scheme.Modules.pullbackComp b a).hom.app
            (SheafOfModules.free (R := X.ringCatSheaf) I) ≫
          (pullbackFreeIso (b ≫ a) I).hom) :=
      CategoryTheory.whisker_eq _ (pullbackFreeIso_comp a b I).symm
    _ = ((Scheme.Modules.pullbackComp b a).inv.app
          (SheafOfModules.free (R := X.ringCatSheaf) I) ≫
        (Scheme.Modules.pullbackComp b a).hom.app
          (SheafOfModules.free (R := X.ringCatSheaf) I)) ≫
        (pullbackFreeIso (b ≫ a) I).hom :=
      (Category.assoc _ _ _).symm
    _ = 𝟙 _ ≫ (pullbackFreeIso (b ≫ a) I).hom :=
      CategoryTheory.eq_whisker
        (Iso.inv_hom_id_app (Scheme.Modules.pullbackComp b a)
          (SheafOfModules.free (R := X.ringCatSheaf) I)) _
    _ = (pullbackFreeIso (b ≫ a) I).hom := Category.id_comp _
    _ = (pullbackFreeIso (b ≫ a) I).hom ≫ 𝟙 _ :=
      (Category.comp_id _).symm
    _ = (pullbackFreeIso (b ≫ a) I).hom ≫
        ((pullbackFreeIso b I).inv ≫ (pullbackFreeIso b I).hom) :=
      CategoryTheory.whisker_eq _ (pullbackFreeIso b I).inv_hom_id.symm
    _ = ((pullbackFreeIso (b ≫ a) I).hom ≫
          (pullbackFreeIso b I).inv) ≫
        (pullbackFreeIso b I).hom :=
      (Category.assoc _ _ _).symm

/-! ### Adjunction transposition of the descent-equalizer legs

The overlap condition consumed by `glueLift` is an equation between composites of adjoint
transposes along the chart immersions. The next two lemmas transpose each leg back across
the pullback–pushforward adjunction of the *composite* overlap immersion, exposing the
pullback-level identity `g_{ij} ∘ f_ij^* u^i = (t_ij ≫ f_ji)^* u^j` that the matrix
computation closes. The first handles the unit/`pushforwardComp` factor pair, the second
the trailing `pushforwardCongr` reindexing cast. -/

/-- **Leg transpose** (`lem:gr_tautologicalQuotientComponent_transpose` engine): for
`b : V ⟶ U`, `a : U ⟶ X` and `c : a^* W ⟶ M`, the descent-equalizer leg
`homEquiv_a(c) ≫ (a_* unit_b) ≫ pushforwardComp` is the transpose along the composite
`b ≫ a` of the pullback of `c` to `V` (through the pseudofunctor comparison
`pullbackComp`). Combines `homEquiv_conjugateEquiv_app` with Mathlib's
`conjugateEquiv_pullbackComp_inv`. Project-local. -/
lemma homEquiv_comp_unit_pushforwardComp {V U X : Scheme.{u}} (b : V ⟶ U) (a : U ⟶ X)
    {W : X.Modules} {M : U.Modules} (c : (Scheme.Modules.pullback a).obj W ⟶ M) :
    (Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv W M c ≫
        ((Scheme.Modules.pushforward a).map
          ((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app M) ≫
        (Scheme.Modules.pushforwardComp b a).hom.app ((Scheme.Modules.pullback b).obj M))
      = (Scheme.Modules.pullbackPushforwardAdjunction (b ≫ a)).homEquiv W
          ((Scheme.Modules.pullback b).obj M)
          ((Scheme.Modules.pullbackComp b a).inv.app W ≫ (Scheme.Modules.pullback b).map c) := by
  -- inner transpose: `c ≫ unit_b` is the `b`-transpose of `(pullback b).map c`
  have h2 : (Scheme.Modules.pullbackPushforwardAdjunction b).homEquiv
        ((Scheme.Modules.pullback a).obj W) ((Scheme.Modules.pullback b).obj M)
        ((Scheme.Modules.pullback b).map c)
      = c ≫ (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app M := by
    rw [Adjunction.homEquiv_unit]
    exact ((Scheme.Modules.pullbackPushforwardAdjunction b).unit.naturality c).symm
  -- composite-adjunction transpose factors through the two single transposes
  have h3 : ((Scheme.Modules.pullbackPushforwardAdjunction a).comp
        (Scheme.Modules.pullbackPushforwardAdjunction b)).homEquiv W
        ((Scheme.Modules.pullback b).obj M) ((Scheme.Modules.pullback b).map c)
      = (Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv _ _
          ((Scheme.Modules.pullbackPushforwardAdjunction b).homEquiv _ _
            ((Scheme.Modules.pullback b).map c)) := by
    rw [Adjunction.comp_homEquiv]
    rfl
  -- mate compatibility: precomposing with `pullbackComp.inv` is postcomposition by the
  -- conjugate, which Mathlib identifies as `pushforwardComp.hom`
  have h4 := homEquiv_conjugateEquiv_app
      ((Scheme.Modules.pullbackPushforwardAdjunction a).comp
        (Scheme.Modules.pullbackPushforwardAdjunction b))
      (Scheme.Modules.pullbackPushforwardAdjunction (b ≫ a))
      (Scheme.Modules.pullbackComp b a).inv
      (f := (Scheme.Modules.pullback b).map c)
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h4
  rw [h4, h3, h2]
  -- regroup and fold the unit factor back into the transpose (term-mode: a positional
  -- `rw [homEquiv_naturality_right]` matches inside the wrong `homEquiv` argument)
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ (Scheme.Modules.pushforwardComp b a).hom.app
        ((Scheme.Modules.pullback b).obj M))
      (Adjunction.homEquiv_naturality_right _ _ _).symm)

/-- **Congruence-cast transpose**: postcomposing a transpose along `e` with the
`pushforwardCongr` cast of an equality `e = e'` is the transpose along `e'` of the
`pullbackCongr`-reindexed morphism. Generic `subst` lemma. Project-local. -/
lemma homEquiv_comp_pushforwardCongr {V X : Scheme.{u}} {e e' : V ⟶ X} (h : e = e')
    {W : X.Modules} {N : V.Modules} (y : (Scheme.Modules.pullback e).obj W ⟶ N) :
    (Scheme.Modules.pullbackPushforwardAdjunction e).homEquiv W N y ≫
        (Scheme.Modules.pushforwardCongr h).hom.app N
      = (Scheme.Modules.pullbackPushforwardAdjunction e').homEquiv W N
          ((Scheme.Modules.pullbackCongr h).inv.app W ≫ y) := by
  subst h
  have h1 : (Scheme.Modules.pushforwardCongr (rfl : e = e)).hom.app N = 𝟙 _ := by
    ext U
    simp
  have h2 : (Scheme.Modules.pullbackCongr (rfl : e = e)).inv.app W = 𝟙 _ := by
    simp [Scheme.Modules.pullbackCongr]
  rw [h1, h2, Category.comp_id, Category.id_comp]

/-- **Transposed form of the `glueLift` overlap condition**: the `(i,j)`-component of the
equalizing hypothesis consumed by `glueLift` holds iff the pullback-level identity
`f_ij^* (c i) = congr ∘ (t_ij ≫ f_ji)^* (c j) ∘ g_ij⁻¹` does (all comparisons through the
pseudofunctor casts). Both legs are transposed along the composite overlap immersion via
`homEquiv_comp_unit_pushforwardComp` / `homEquiv_comp_pushforwardCongr`, and the
hom-equivalence is injective. Project-local. -/
lemma glueLift_cond_iff (D : Scheme.GlueData.{u})
    (M : ∀ i, (D.U i).Modules)
    (g : ∀ i j, (Scheme.Modules.pullback (D.f i j)).obj (M i) ≅
        (Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j))
    {W : D.glued.Modules}
    (c : ∀ i, (Scheme.Modules.pullback (D.ι i)).obj W ⟶ M i) (i j : D.J) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (D.ι i)).homEquiv W (M i) (c i) ≫
        ((Scheme.Modules.pushforward (D.ι i)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (D.f i j)).unit.app (M i)) ≫
        (Scheme.Modules.pushforwardComp (D.f i j) (D.ι i)).hom.app
          ((Scheme.Modules.pullback (D.f i j)).obj (M i)))
      = (Scheme.Modules.pullbackPushforwardAdjunction (D.ι j)).homEquiv W (M j) (c j) ≫
        ((Scheme.Modules.pushforward (D.ι j)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction
            (D.t i j ≫ D.f j i)).unit.app (M j)) ≫
        (Scheme.Modules.pushforwardComp (D.t i j ≫ D.f j i) (D.ι j)).hom.app
          ((Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j)) ≫
        (Scheme.Modules.pushforward
          ((D.t i j ≫ D.f j i) ≫ D.ι j)).map (g i j).inv ≫
        (Scheme.Modules.pushforwardCongr
          (show (D.t i j ≫ D.f j i) ≫ D.ι j = D.f i j ≫ D.ι i by
            rw [Category.assoc]; exact D.glue_condition i j)).hom.app
          ((Scheme.Modules.pullback (D.f i j)).obj (M i))))
    ↔ ((Scheme.Modules.pullbackComp (D.f i j) (D.ι i)).inv.app W ≫
          (Scheme.Modules.pullback (D.f i j)).map (c i)
      = (Scheme.Modules.pullbackCongr
            (show (D.t i j ≫ D.f j i) ≫ D.ι j = D.f i j ≫ D.ι i by
              rw [Category.assoc]; exact D.glue_condition i j)).inv.app W ≫
          (Scheme.Modules.pullbackComp (D.t i j ≫ D.f j i) (D.ι j)).inv.app W ≫
          (Scheme.Modules.pullback (D.t i j ≫ D.f j i)).map (c j) ≫ (g i j).inv) := by
  -- transpose the left leg
  rw [homEquiv_comp_unit_pushforwardComp (D.f i j) (D.ι i) (c i)]
  -- transpose the right leg: regroup, fire the leg transpose, absorb `(g i j).inv`
  -- into the transpose, then fire the congruence-cast transpose
  have hR : (Scheme.Modules.pullbackPushforwardAdjunction (D.ι j)).homEquiv W (M j) (c j) ≫
        ((Scheme.Modules.pushforward (D.ι j)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction
            (D.t i j ≫ D.f j i)).unit.app (M j)) ≫
        (Scheme.Modules.pushforwardComp (D.t i j ≫ D.f j i) (D.ι j)).hom.app
          ((Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j)) ≫
        (Scheme.Modules.pushforward
          ((D.t i j ≫ D.f j i) ≫ D.ι j)).map (g i j).inv ≫
        (Scheme.Modules.pushforwardCongr
          (show (D.t i j ≫ D.f j i) ≫ D.ι j = D.f i j ≫ D.ι i by
            rw [Category.assoc]; exact D.glue_condition i j)).hom.app
          ((Scheme.Modules.pullback (D.f i j)).obj (M i)))
      = (Scheme.Modules.pullbackPushforwardAdjunction (D.f i j ≫ D.ι i)).homEquiv W
          ((Scheme.Modules.pullback (D.f i j)).obj (M i))
          ((Scheme.Modules.pullbackCongr
              (show (D.t i j ≫ D.f j i) ≫ D.ι j = D.f i j ≫ D.ι i by
                rw [Category.assoc]; exact D.glue_condition i j)).inv.app W ≫
            (((Scheme.Modules.pullbackComp (D.t i j ≫ D.f j i) (D.ι j)).inv.app W ≫
              (Scheme.Modules.pullback (D.t i j ≫ D.f j i)).map (c j)) ≫ (g i j).inv)) := by
    calc (Scheme.Modules.pullbackPushforwardAdjunction (D.ι j)).homEquiv W (M j) (c j) ≫
          ((Scheme.Modules.pushforward (D.ι j)).map
            ((Scheme.Modules.pullbackPushforwardAdjunction
              (D.t i j ≫ D.f j i)).unit.app (M j)) ≫
          (Scheme.Modules.pushforwardComp (D.t i j ≫ D.f j i) (D.ι j)).hom.app
            ((Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j)) ≫
          (Scheme.Modules.pushforward
            ((D.t i j ≫ D.f j i) ≫ D.ι j)).map (g i j).inv ≫
          (Scheme.Modules.pushforwardCongr
            (show (D.t i j ≫ D.f j i) ≫ D.ι j = D.f i j ≫ D.ι i by
              rw [Category.assoc]; exact D.glue_condition i j)).hom.app
            ((Scheme.Modules.pullback (D.f i j)).obj (M i)))
        = (((Scheme.Modules.pullbackPushforwardAdjunction (D.ι j)).homEquiv W (M j) (c j) ≫
            ((Scheme.Modules.pushforward (D.ι j)).map
              ((Scheme.Modules.pullbackPushforwardAdjunction
                (D.t i j ≫ D.f j i)).unit.app (M j)) ≫
            (Scheme.Modules.pushforwardComp (D.t i j ≫ D.f j i) (D.ι j)).hom.app
              ((Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j)))) ≫
          (Scheme.Modules.pushforward
            ((D.t i j ≫ D.f j i) ≫ D.ι j)).map (g i j).inv) ≫
          (Scheme.Modules.pushforwardCongr
            (show (D.t i j ≫ D.f j i) ≫ D.ι j = D.f i j ≫ D.ι i by
              rw [Category.assoc]; exact D.glue_condition i j)).hom.app
            ((Scheme.Modules.pullback (D.f i j)).obj (M i)) := by
          simp only [Category.assoc]
      _ = (((Scheme.Modules.pullbackPushforwardAdjunction
              ((D.t i j ≫ D.f j i) ≫ D.ι j)).homEquiv W
              ((Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j))
              ((Scheme.Modules.pullbackComp (D.t i j ≫ D.f j i) (D.ι j)).inv.app W ≫
                (Scheme.Modules.pullback (D.t i j ≫ D.f j i)).map (c j))) ≫
            (Scheme.Modules.pushforward
              ((D.t i j ≫ D.f j i) ≫ D.ι j)).map (g i j).inv) ≫
          (Scheme.Modules.pushforwardCongr
            (show (D.t i j ≫ D.f j i) ≫ D.ι j = D.f i j ≫ D.ι i by
              rw [Category.assoc]; exact D.glue_condition i j)).hom.app
            ((Scheme.Modules.pullback (D.f i j)).obj (M i)) :=
          congrArg (fun m => (m ≫ (Scheme.Modules.pushforward
              ((D.t i j ≫ D.f j i) ≫ D.ι j)).map (g i j).inv) ≫
            (Scheme.Modules.pushforwardCongr
              (show (D.t i j ≫ D.f j i) ≫ D.ι j = D.f i j ≫ D.ι i by
                rw [Category.assoc]; exact D.glue_condition i j)).hom.app
              ((Scheme.Modules.pullback (D.f i j)).obj (M i)))
            (homEquiv_comp_unit_pushforwardComp (D.t i j ≫ D.f j i) (D.ι j) (c j))
      _ = ((Scheme.Modules.pullbackPushforwardAdjunction
              ((D.t i j ≫ D.f j i) ≫ D.ι j)).homEquiv W
              ((Scheme.Modules.pullback (D.f i j)).obj (M i))
              ((((Scheme.Modules.pullbackComp (D.t i j ≫ D.f j i) (D.ι j)).inv.app W ≫
                (Scheme.Modules.pullback (D.t i j ≫ D.f j i)).map (c j))) ≫ (g i j).inv)) ≫
          (Scheme.Modules.pushforwardCongr
            (show (D.t i j ≫ D.f j i) ≫ D.ι j = D.f i j ≫ D.ι i by
              rw [Category.assoc]; exact D.glue_condition i j)).hom.app
            ((Scheme.Modules.pullback (D.f i j)).obj (M i)) :=
          congrArg (· ≫ (Scheme.Modules.pushforwardCongr
              (show (D.t i j ≫ D.f j i) ≫ D.ι j = D.f i j ≫ D.ι i by
                rw [Category.assoc]; exact D.glue_condition i j)).hom.app
              ((Scheme.Modules.pullback (D.f i j)).obj (M i)))
            (Adjunction.homEquiv_naturality_right _ _ _).symm
      _ = (Scheme.Modules.pullbackPushforwardAdjunction (D.f i j ≫ D.ι i)).homEquiv W
            ((Scheme.Modules.pullback (D.f i j)).obj (M i))
            ((Scheme.Modules.pullbackCongr
                (show (D.t i j ≫ D.f j i) ≫ D.ι j = D.f i j ≫ D.ι i by
                  rw [Category.assoc]; exact D.glue_condition i j)).inv.app W ≫
              (((Scheme.Modules.pullbackComp (D.t i j ≫ D.f j i) (D.ι j)).inv.app W ≫
                (Scheme.Modules.pullback (D.t i j ≫ D.f j i)).map (c j)) ≫ (g i j).inv)) :=
          homEquiv_comp_pushforwardCongr _ _
  rw [hR, Equiv.apply_eq_iff_eq]
  simp only [Category.assoc]

/-! ### Restriction of the glued sheaf to a chart (`def:gr_modules_glueRestrictionIso`)

The glued sheaf is the descent equalizer `eq(a, b) ⊆ ∏ᵢ (ιᵢ)_* Mᵢ`. This section
re-exposes the two legs of that equalizer as standalone declarations
(`glueLegA`/`glueLegB`), records that `glue` *is* their equalizer (`glueIsoEqualizer`,
definitional), and produces the canonical projection `glueProj i` of the glued sheaf
onto the `i`-th pushforward factor together with its compatibility with `glueLift`.
The adjoint transpose of `glueProj i` along the chart immersion `D.ι i` is the
*restriction morphism* `glueRestrictionHom i : ιᵢ^* (glue …) ⟶ M i`; effective descent
(consuming the cocycle hypotheses C1/C2) makes it an isomorphism — the restriction
isomorphism `glueRestrictionIso` of `def:gr_modules_glueRestrictionIso`. The
limit-preservation engine is `restrictFunctor`: pullback along an open immersion is
naturally isomorphic to a site-level pushforward, which is a right adjoint, hence
preserves the descent equalizer and the pushforward product. -/

/-- `restrictFunctor f` along an open immersion is a right adjoint: it is a site-level
pushforward of sheaves of modules, whose left adjoint (the site-level pullback) exists
by the presheaf-pullback + sheafification construction. Project-local instance. -/
instance restrictFunctor_isRightAdjoint {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (restrictFunctor f).IsRightAdjoint := by
  let α : X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf :=
    { app U := (f.appIso U.unop).inv }
  let φ : X.ringCatSheaf ⟶
      (f.opensFunctor.sheafPushforwardContinuous _ _ _).obj Y.ringCatSheaf :=
    ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩
  change (SheafOfModules.pushforward.{u} φ).IsRightAdjoint
  letI : (PresheafOfModules.pushforward.{u} φ.hom).IsRightAdjoint :=
    Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
      (PresheafOfModules.pullbackObjIsDefined_eq_top φ.hom)
  exact (SheafOfModules.PullbackConstruction.adjunction.{u} φ).isRightAdjoint

/-- `restrictFunctor f` along an open immersion preserves limits (it is a right
adjoint). Project-local. -/
noncomputable instance restrictFunctor_preservesLimits.{w, w'} {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] :
    PreservesLimitsOfSize.{w, w'} (restrictFunctor f) :=
  (Adjunction.ofIsRightAdjoint (restrictFunctor f)).rightAdjoint_preservesLimits

/-- **Pullback of sheaves of modules along an open immersion preserves limits**: it is
naturally isomorphic to `restrictFunctor f`, a site-level pushforward and right
adjoint. This is the engine that lets the chart restriction commute with the descent
equalizer. Project-local. -/
instance pullback_preservesLimits_of_isOpenImmersion.{w, w'} {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] :
    PreservesLimitsOfSize.{w, w'} (Scheme.Modules.pullback f) :=
  preservesLimits_of_natIso (restrictFunctorIsoPullback f)

section GlueRestriction

-- NOTE: `glue`/`glueLift` elaborated universe-monomorphic at `Scheme.GlueData.{0}`
-- (their universe was pinned during elaboration); the restriction layer follows suit.
variable (D : Scheme.GlueData.{0}) (M : ∀ i, (D.U i).Modules)

/-- The product of pushforwards `∏ᵢ (ιᵢ)_* Mᵢ` into which the glued sheaf embeds.
Project-local helper re-exposing the `P` of `glue`. -/
noncomputable def glueProd : D.glued.Modules :=
  ∏ᶜ fun i => (Scheme.Modules.pushforward (D.ι i)).obj (M i)

/-- The overlap product `∏_{(i,j)} (f_ij ≫ ιᵢ)_* (f_ij^* Mᵢ)` receiving the two descent
legs. Project-local helper re-exposing the `Qfun`-product of `glue`. -/
noncomputable def glueOverlapProd : D.glued.Modules :=
  ∏ᶜ fun p : D.J × D.J =>
    (Scheme.Modules.pushforward (D.f p.1 p.2 ≫ D.ι p.1)).obj
      ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1))

/-- First descent leg (`a` of `glue`): on the `(i,j)`-component, restrict the `i`-th
chart section to the overlap `V (i,j)` via the unit of the pullback–pushforward
adjunction along `f_ij` and the pushforward-composition comparison. Project-local. -/
noncomputable def glueLegA : glueProd D M ⟶ glueOverlapProd D M :=
  Pi.lift fun p => Pi.π _ p.1 ≫
    ((Scheme.Modules.pushforward (D.ι p.1)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (D.f p.1 p.2)).unit.app (M p.1)) ≫
      (Scheme.Modules.pushforwardComp (D.f p.1 p.2) (D.ι p.1)).hom.app
        ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1)))

/-- Second descent leg (`b` of `glue`): on the `(i,j)`-component, restrict the `j`-th
chart section, transport it across the transition isomorphism `g_ij`, and reindex the
immersion via the glue condition. Project-local. -/
noncomputable def glueLegB
    (g : ∀ i j, (Scheme.Modules.pullback (D.f i j)).obj (M i) ≅
        (Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j)) :
    glueProd D M ⟶ glueOverlapProd D M :=
  Pi.lift fun p => Pi.π _ p.2 ≫
    ((Scheme.Modules.pushforward (D.ι p.2)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction
          (D.t p.1 p.2 ≫ D.f p.2 p.1)).unit.app (M p.2)) ≫
      (Scheme.Modules.pushforwardComp (D.t p.1 p.2 ≫ D.f p.2 p.1) (D.ι p.2)).hom.app
        ((Scheme.Modules.pullback (D.t p.1 p.2 ≫ D.f p.2 p.1)).obj (M p.2)) ≫
      (Scheme.Modules.pushforward
        ((D.t p.1 p.2 ≫ D.f p.2 p.1) ≫ D.ι p.2)).map (g p.1 p.2).inv ≫
      (Scheme.Modules.pushforwardCongr
        (show (D.t p.1 p.2 ≫ D.f p.2 p.1) ≫ D.ι p.2 = D.f p.1 p.2 ≫ D.ι p.1 by
          rw [Category.assoc]; exact D.glue_condition p.1 p.2)).hom.app
        ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1)))

variable (g : ∀ i j, (Scheme.Modules.pullback (D.f i j)).obj (M i) ≅
      (Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j))
  (hC1 : ∀ i, g i i = eqToIso (congrArg (fun φ => (Scheme.Modules.pullback φ).obj (M i))
      (show D.f i i = D.t i i ≫ D.f i i by rw [D.t_id i, Category.id_comp])))
  (hC2 : ∀ i j k,
      pullbackBaseChangeTransport (pullback.fst (D.f i j) (D.f i k))
          (D.f i j) (D.t i j ≫ D.f j i) (g i j) ≪≫
        (Scheme.Modules.pullbackCongr (glueData_bridge_mid D i j k)).app (M j) ≪≫
        pullbackBaseChangeTransport (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
          (D.f j k) (D.t j k ≫ D.f k j) (g j k) ≪≫
        (Scheme.Modules.pullbackCongr (glueData_bridge_tgt D i j k)).app (M k)
      = (Scheme.Modules.pullbackCongr (glueData_bridge_src D i j k)).app (M i) ≪≫
        pullbackBaseChangeTransport (pullback.snd (D.f i j) (D.f i k))
          (D.f i k) (D.t i k ≫ D.f k i) (g i k))

/-- The glued sheaf *is* the equalizer of the two (re-exposed) descent legs. The
isomorphism is definitional (`Iso.refl`); it exists to let the equalizer API fire
syntactically on `glue`. Project-local. -/
noncomputable def glueIsoEqualizer :
    glue D M g hC1 hC2 ≅ equalizer (glueLegA D M) (glueLegB D M g) :=
  Iso.refl _

/-- Projection of the glued sheaf onto the `i`-th pushforward factor `(ιᵢ)_* Mᵢ`:
the equalizer inclusion followed by the product projection. Project-local. -/
noncomputable def glueProj (i : D.J) :
    glue D M g hC1 hC2 ⟶ (Scheme.Modules.pushforward (D.ι i)).obj (M i) :=
  (glueIsoEqualizer D M g hC1 hC2).hom ≫ equalizer.ι (glueLegA D M) (glueLegB D M g) ≫
    Pi.π _ i

/-- `glueLift` followed by the `i`-th projection recovers the `i`-th component of the
lifted family. Project-local. -/
@[reassoc]
lemma glueLift_glueProj {W : D.glued.Modules}
    (k : ∀ i, W ⟶ (Scheme.Modules.pushforward (D.ι i)).obj (M i))
    (hk : ∀ p : D.J × D.J,
      k p.1 ≫
          ((Scheme.Modules.pushforward (D.ι p.1)).map
            ((Scheme.Modules.pullbackPushforwardAdjunction (D.f p.1 p.2)).unit.app (M p.1)) ≫
          (Scheme.Modules.pushforwardComp (D.f p.1 p.2) (D.ι p.1)).hom.app
            ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1)))
        = k p.2 ≫
          ((Scheme.Modules.pushforward (D.ι p.2)).map
            ((Scheme.Modules.pullbackPushforwardAdjunction
              (D.t p.1 p.2 ≫ D.f p.2 p.1)).unit.app (M p.2)) ≫
          (Scheme.Modules.pushforwardComp (D.t p.1 p.2 ≫ D.f p.2 p.1) (D.ι p.2)).hom.app
            ((Scheme.Modules.pullback (D.t p.1 p.2 ≫ D.f p.2 p.1)).obj (M p.2)) ≫
          (Scheme.Modules.pushforward
            ((D.t p.1 p.2 ≫ D.f p.2 p.1) ≫ D.ι p.2)).map (g p.1 p.2).inv ≫
          (Scheme.Modules.pushforwardCongr
            (show (D.t p.1 p.2 ≫ D.f p.2 p.1) ≫ D.ι p.2 = D.f p.1 p.2 ≫ D.ι p.1 by
              rw [Category.assoc]; exact D.glue_condition p.1 p.2)).hom.app
            ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1)))) (i : D.J) :
    glueLift D M g hC1 hC2 k hk ≫ glueProj D M g hC1 hC2 i = k i := by
  dsimp only [glueLift, glueProj, glueIsoEqualizer, Iso.refl_hom]
  -- term-mode: the mixed-provenance comp nodes block positional `rw [Category.id_comp]`
  exact (congrArg (equalizer.lift (Pi.lift k) _ ≫ ·) (Category.id_comp _)).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ Pi.π _ i) (equalizer.lift_ι _ _)).trans (Limits.Pi.lift_π _ _)))

/-- **The restriction morphism of the glued sheaf** to the `i`-th chart: the adjoint
transpose, along the chart immersion `ιᵢ`, of the `i`-th projection `glueProj i`.
Effective descent (`isIso_glueRestrictionHom`) makes it an isomorphism. Project-local. -/
noncomputable def glueRestrictionHom (i : D.J) :
    (Scheme.Modules.pullback (D.ι i)).obj (glue D M g hC1 hC2) ⟶ M i :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (D.ι i)).homEquiv _ _).symm
    (glueProj D M g hC1 hC2 i)

/-- **The chart restriction of the glued sheaf is the equalizer of the restricted
descent legs**: the chart pullback preserves the descent equalizer
(`pullback_preservesLimits_of_isOpenImmersion`). First reduction step of
`isIso_glueRestrictionHom`. Project-local. -/
noncomputable def glueRestrictEqualizerIso (i : D.J) :
    (Scheme.Modules.pullback (D.ι i)).obj (glue D M g hC1 hC2)
      ≅ equalizer ((Scheme.Modules.pullback (D.ι i)).map (glueLegA D M))
          ((Scheme.Modules.pullback (D.ι i)).map (glueLegB D M g)) :=
  (Scheme.Modules.pullback (D.ι i)).mapIso (glueIsoEqualizer D M g hC1 hC2) ≪≫
    PreservesEqualizer.iso (Scheme.Modules.pullback (D.ι i)) _ _

/-- **The chart restriction of the pushforward product is the product of the
restrictions**: the chart pullback preserves the product
(`pullback_preservesLimits_of_isOpenImmersion`). Second reduction step of
`isIso_glueRestrictionHom`: the factors `ι_i^* ((ι_j)_* M_j)` are then identified with
`(f_ij)_* ((t_ij ≫ f_ji)^* M_j)` by the overlap base change of the cartesian chart
square (`glueData_preimage_image_eq`). Project-local. -/
noncomputable def glueRestrictProdIso (i : D.J) :
    (Scheme.Modules.pullback (D.ι i)).obj (glueProd D M)
      ≅ ∏ᶜ fun j => (Scheme.Modules.pullback (D.ι i)).obj
          ((Scheme.Modules.pushforward (D.ι j)).obj (M j)) :=
  PreservesProduct.iso (Scheme.Modules.pullback (D.ι i)) _

/-- **Chart restriction of a lifted morphism**: pulling a `glueLift` back to the `i`-th
chart and composing with the restriction morphism recovers the adjoint transpose of the
`i`-th component of the lifted family. This is `glueLift_glueProj` transposed along the
chart immersion; it is what identifies `ι_I^* (tautologicalQuotient)` with the chart
quotient downstream. Project-local. -/
lemma pullback_map_glueLift_glueRestrictionHom {W : D.glued.Modules}
    (k : ∀ i, W ⟶ (Scheme.Modules.pushforward (D.ι i)).obj (M i))
    (hk : ∀ p : D.J × D.J,
      k p.1 ≫
          ((Scheme.Modules.pushforward (D.ι p.1)).map
            ((Scheme.Modules.pullbackPushforwardAdjunction (D.f p.1 p.2)).unit.app (M p.1)) ≫
          (Scheme.Modules.pushforwardComp (D.f p.1 p.2) (D.ι p.1)).hom.app
            ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1)))
        = k p.2 ≫
          ((Scheme.Modules.pushforward (D.ι p.2)).map
            ((Scheme.Modules.pullbackPushforwardAdjunction
              (D.t p.1 p.2 ≫ D.f p.2 p.1)).unit.app (M p.2)) ≫
          (Scheme.Modules.pushforwardComp (D.t p.1 p.2 ≫ D.f p.2 p.1) (D.ι p.2)).hom.app
            ((Scheme.Modules.pullback (D.t p.1 p.2 ≫ D.f p.2 p.1)).obj (M p.2)) ≫
          (Scheme.Modules.pushforward
            ((D.t p.1 p.2 ≫ D.f p.2 p.1) ≫ D.ι p.2)).map (g p.1 p.2).inv ≫
          (Scheme.Modules.pushforwardCongr
            (show (D.t p.1 p.2 ≫ D.f p.2 p.1) ≫ D.ι p.2 = D.f p.1 p.2 ≫ D.ι p.1 by
              rw [Category.assoc]; exact D.glue_condition p.1 p.2)).hom.app
            ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1)))) (i : D.J) :
    (Scheme.Modules.pullback (D.ι i)).map (glueLift D M g hC1 hC2 k hk) ≫
        glueRestrictionHom D M g hC1 hC2 i
      = ((Scheme.Modules.pullbackPushforwardAdjunction (D.ι i)).homEquiv _ _).symm (k i) := by
  rw [glueRestrictionHom, ← Adjunction.homEquiv_naturality_left_symm,
    glueLift_glueProj]

end GlueRestriction

/-- **Overlap-square opens identity**: for an open `V` of the `i`-th chart of a scheme
glue datum, the preimage under `ι_j` of its image in the glued scheme coincides with
the image, under the `j`-side overlap immersion `t_ij ≫ f_ji`, of its preimage under
`f_ij`. This is the underlying-opens form of the cartesianness of the chart-overlap
square (`vPullbackCone`); it is the site-level input identifying the two composite
restriction functors of the overlap square. Project-local. -/
lemma glueData_preimage_image_eq (D : Scheme.GlueData.{0}) (i j : D.J)
    (V : (D.U i).Opens) :
    (D.ι j) ⁻¹ᵁ ((D.ι i) ''ᵁ V) = (D.t i j ≫ D.f j i) ''ᵁ ((D.f i j) ⁻¹ᵁ V) := by
  ext x
  constructor
  · intro hx
    -- a point of `U_j` mapping into `ι_i(V)` comes from the overlap via the glue relation
    obtain ⟨y, hyV, hyx⟩ := hx
    obtain ⟨w, hw1, hw2⟩ := (D.ι_eq_iff i j y x).mp hyx
    exact ⟨w, show (D.f i j) w ∈ V from (show (D.f i j) w = y from hw1) ▸ hyV, hw2⟩
  · rintro ⟨w, hwV, rfl⟩
    refine ⟨D.f i j w, hwV, ?_⟩
    -- `ι_i (f_ij w) = ι_j ((t_ij ≫ f_ji) w)`: the glue condition at the point `w`
    have h := congrArg (fun m : D.V (i, j) ⟶ D.glued => m w)
      ((D.glue_condition i j).symm.trans (Category.assoc _ _ _).symm)
    exact h

/-- **The two composite opens functors of the chart-overlap square are equal**: going
"into the glued scheme along `ι_i` and back down to `U_j`" is the same site functor as
"down to the overlap along `f_ij` and into `U_j` along `t_ij ≫ f_ji`". Object-level
content is `glueData_preimage_image_eq`; morphisms are proof-irrelevant in the opens
preorder. This is the site-level heart of the overlap base-change comparison
`ι_i^* ∘ (ι_j)_* ≅ (f_ij)_* ∘ (t_ij ≫ f_ji)^*` consumed by
`isIso_glueRestrictionHom`. Project-local. -/
lemma glueData_overlap_opensFunctor_eq (D : Scheme.GlueData.{0}) (i j : D.J) :
    (D.ι i).opensFunctor ⋙ TopologicalSpace.Opens.map (D.ι j).base
      = TopologicalSpace.Opens.map (D.f i j).base ⋙ (D.t i j ≫ D.f j i).opensFunctor :=
  CategoryTheory.Functor.ext (fun V => glueData_preimage_image_eq D i j V)
    (fun _ _ _ => Subsingleton.elim _ _)

/-- `appLE` transport along an equality of morphisms: for equal `f = g` the induced
section maps `Γ(B, U) ⟶ Γ(A, W)` agree (the open-inequality witnesses are
proof-irrelevant). Generic `subst` helper for the overlap structure-sheaf
compatibility. Project-local. -/
lemma appLE_congr_mor {A B : Scheme.{u}} {f g : A ⟶ B} (h : f = g) (U : B.Opens)
    (W : A.Opens) (e : W ≤ f ⁻¹ᵁ U) (e' : W ≤ g ⁻¹ᵁ U) :
    f.appLE U W e = g.appLE U W e' := by
  subst h; rfl

/-- **Structure-sheaf compatibility of the chart-overlap square**: the two composite
section maps `Γ(U_i, V) ⟶ Γ(U_j, (t_ij ≫ f_ji) '' (f_ij⁻¹ V))` of the overlap square —
"through the glued scheme" (via `(ι_i.appIso V)⁻¹`, `ι_j.app`, and the opens identity
`glueData_preimage_image_eq`) and "through the overlap" (via `f_ij.app` and
`((t_ij ≫ f_ji).appIso)⁻¹`) — coincide. Both sides are the `appLE` of the two (equal)
composites `(t_ij ≫ f_ji) ≫ ι_j = f_ij ≫ ι_i` of the square; this is the
`pushforwardCongr` coherence consumed by `glueOverlapBaseChangeIso`. Project-local. -/
lemma glueData_overlap_appIso_compat (D : Scheme.GlueData.{0}) (i j : D.J)
    (V : (D.U i).Opens) :
    ((D.ι i).appIso V).inv ≫ (D.ι j).app ((D.ι i) ''ᵁ V) ≫
        (D.U j).presheaf.map (eqToHom (glueData_preimage_image_eq D i j V).symm).op
      = (D.f i j).app V ≫ ((D.t i j ≫ D.f j i).appIso ((D.f i j) ⁻¹ᵁ V)).inv := by
  have hsq : (D.t i j ≫ D.f j i) ≫ D.ι j = D.f i j ≫ D.ι i := by
    rw [Category.assoc]; exact D.glue_condition i j
  rw [Iso.eq_comp_inv]
  simp only [Category.assoc]
  rw [Iso.inv_comp_eq]
  simp only [Scheme.Hom.appIso_hom', Scheme.Hom.app_eq_appLE,
    Scheme.Hom.appLE_map_assoc, Scheme.Hom.appLE_comp_appLE]
  exact appLE_congr_mor hsq _ _ _ _

/-- **Overlap base change of the chart square** (`β_ij`): restricting a pushforward
`(ι_j)_* N` to the chart `U_i` is the same as restricting `N` to the overlap `V_ij`
(along `t_ij ≫ f_ji`) and pushing forward along `f_ij`. All four functors are
site-level pushforwards; both composites are pushforwards along the SAME opens functor
(`glueData_overlap_opensFunctor_eq`), so the comparison is
`pushforwardComp ≪≫ pushforwardNatIso (eqToIso components) ≪≫ pushforwardCongr ≪≫
pushforwardComp.symm` — the `restrictFunctorComp` pattern of Mathlib. This is the
factor-wise identification of the restricted descent product consumed by
`isIso_glueRestrictionHom`. Project-local. -/
noncomputable def glueOverlapBaseChangeIso (D : Scheme.GlueData.{0}) (i j : D.J) :
    Scheme.Modules.pushforward (D.ι j) ⋙ restrictFunctor (D.ι i)
      ≅ restrictFunctor (D.t i j ≫ D.f j i) ⋙ Scheme.Modules.pushforward (D.f i j) :=
  haveI h₁ : Functor.IsContinuous
      ((D.ι i).opensFunctor ⋙ TopologicalSpace.Opens.map (D.ι j).base)
      (Opens.grothendieckTopology ↥(D.U i))
      (Opens.grothendieckTopology ↥(D.U j)) :=
    Functor.isContinuous_comp _ _ _
      (Opens.grothendieckTopology ↥(D.glued)) _
  haveI h₂ : Functor.IsContinuous
      (TopologicalSpace.Opens.map (D.f i j).base ⋙ (D.t i j ≫ D.f j i).opensFunctor)
      (Opens.grothendieckTopology ↥(D.U i))
      (Opens.grothendieckTopology ↥(D.U j)) :=
    Functor.isContinuous_comp _ _ _
      (Opens.grothendieckTopology ↥(D.V (i, j))) _
  SheafOfModules.pushforwardComp _ _ ≪≫
    SheafOfModules.pushforwardNatIso _
      (NatIso.ofComponents
        (fun V => eqToIso (glueData_preimage_image_eq D i j V).symm)
        (fun _ => Subsingleton.elim _ _)) ≪≫
    SheafOfModules.pushforwardCongr (by
      ext V x
      exact congr($(glueData_overlap_appIso_compat D i j (unop V)) x)) ≪≫
    (SheafOfModules.pushforwardComp _ _).symm

/-- **Joint faithfulness of the chart restrictions** (`lem:gr_modules_glue_unique`
core): two morphisms of sheaves of modules on the glued scheme that agree after
pullback to every chart agree. This is the separation half of the sheaf condition
over the chart cover `{ι_i}`: sections of the target sheaf are detected on the
chart-image opens `ι_i''(ι_i⁻¹ O)`, which cover any open `O` by the joint
surjectivity of the chart immersions. Engine for `tautologicalQuotient_epi`
(a morphism out of the glued sheaf is determined chart-locally). Project-local. -/
lemma pullback_map_jointly_faithful (D : Scheme.GlueData.{0}) {W W' : D.glued.Modules}
    {u v : W ⟶ W'}
    (h : ∀ i, (Scheme.Modules.pullback (D.ι i)).map u
        = (Scheme.Modules.pullback (D.ι i)).map v) :
    u = v := by
  -- transfer the hypothesis to the site-level restriction functor, whose sections
  -- are concrete (`Γ(restrict W, V) = Γ(W, ι_i''V)`)
  have hres : ∀ i, (restrictFunctor (D.ι i)).map u = (restrictFunctor (D.ι i)).map v := by
    intro i
    calc (restrictFunctor (D.ι i)).map u
        = (restrictFunctorIsoPullback (D.ι i)).hom.app W ≫
            (Scheme.Modules.pullback (D.ι i)).map u ≫
            (restrictFunctorIsoPullback (D.ι i)).inv.app W' :=
          (NatIso.naturality_2 (restrictFunctorIsoPullback (D.ι i)) u).symm
      _ = (restrictFunctorIsoPullback (D.ι i)).hom.app W ≫
            (Scheme.Modules.pullback (D.ι i)).map v ≫
            (restrictFunctorIsoPullback (D.ι i)).inv.app W' := by rw [h i]
      _ = (restrictFunctor (D.ι i)).map v :=
          NatIso.naturality_2 (restrictFunctorIsoPullback (D.ι i)) v
  ext O x
  -- sheaf separation of the target over the cover `{ι_i''(ι_i⁻¹ O)}` of `O`
  refine TopCat.Sheaf.eq_of_locally_eq'
    (⟨W'.presheaf, W'.isSheaf⟩ : TopCat.Sheaf Ab D.glued)
    (fun i => (D.ι i) ''ᵁ ((D.ι i) ⁻¹ᵁ O)) O
    (fun i => homOfLE ((D.ι i).image_preimage_le O)) ?_ _ _ ?_
  · intro pt hpt
    obtain ⟨i, y, rfl⟩ := D.ι_jointly_surjective pt
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, y, hpt, rfl⟩
  · intro i
    -- naturality moves the restriction inside `u.app`/`v.app`; the chart-image
    -- agreement is `hres i` evaluated on sections (defeq through `restrict_obj`)
    have hu := congr($(u.mapPresheaf.naturality
      (homOfLE ((D.ι i).image_preimage_le O)).op) x)
    have hv := congr($(v.mapPresheaf.naturality
      (homOfLE ((D.ι i).image_preimage_le O)).op) x)
    have hres_app := congr($(congrArg
      (fun (m : (restrictFunctor (D.ι i)).obj W ⟶ (restrictFunctor (D.ι i)).obj W') =>
        Scheme.Modules.Hom.app m ((D.ι i) ⁻¹ᵁ O)) (hres i))
      ((W.presheaf.map (homOfLE ((D.ι i).image_preimage_le O)).op) x))
    exact hu.symm.trans (hres_app.trans hv)

/-- **Sections of the overlap base change**: on sections over `V ⊆ U_i`, the inverse
of `β_ij` is the restriction map of `N` along the opens identity
`ι_j⁻¹(ι_i''V) = (t_ij ≫ f_ji)''(f_ij⁻¹V)` (`glueData_preimage_image_eq`). All four
factors of `β_ij` are site-level pushforwards whose components act identically or as
a single presheaf restriction. Project-local. -/
lemma glueOverlapBaseChangeIso_inv_app_app (D : Scheme.GlueData.{0}) (i j : D.J)
    (N : (D.U j).Modules) (V : (D.U i).Opens) :
    (((glueOverlapBaseChangeIso D i j).inv.app N).app V :
        Γ(N, (D.t i j ≫ D.f j i) ''ᵁ ((D.f i j) ⁻¹ᵁ V)) ⟶ Γ(N, (D.ι j) ⁻¹ᵁ ((D.ι i) ''ᵁ V)))
      = N.presheaf.map (eqToHom (glueData_preimage_image_eq D i j V)).op := by
  ext x
  rfl

/-- Hom-side companion of `glueOverlapBaseChangeIso_inv_app_app`. Project-local. -/
lemma glueOverlapBaseChangeIso_hom_app_app (D : Scheme.GlueData.{0}) (i j : D.J)
    (N : (D.U j).Modules) (V : (D.U i).Opens) :
    (((glueOverlapBaseChangeIso D i j).hom.app N).app V :
        Γ(N, (D.ι j) ⁻¹ᵁ ((D.ι i) ''ᵁ V)) ⟶ Γ(N, (D.t i j ≫ D.f j i) ''ᵁ ((D.f i j) ⁻¹ᵁ V)))
      = N.presheaf.map (eqToHom (glueData_preimage_image_eq D i j V).symm).op := by
  ext x
  rfl

/-! ### Triple-overlap base change

The `(p,q)`-component of the equalizing condition for the candidate inverse on the
chart `U_i` lives on the triple overlap `V_ipq := V_ip ×_{U_i} V_iq`. This block
mirrors the pair-level overlap base change (`glueData_preimage_image_eq` →
`glueOverlapBaseChangeIso`) for the square

  `V_ipq ──τ──→ V_pq`         `τ   := t'_ipq ≫ fst : V_ipq ⟶ V_pq`
  `  │q             │f_pq ≫ ι_p`
  `U_i ──ι_i──→ glued`,        `q   := fst ≫ f_ip  : V_ipq ⟶ U_i`

which commutes (`glueData_triple_square`) and is cartesian on underlying opens
(`glueData_preimage_image_eq₃`). -/

/-- Commutativity of the triple-overlap square: the triple overlap maps into the glued
scheme the same way through the chart `U_i` (via `q = fst ≫ f_ip`) and through the
pair overlap `V_pq` (via the cocycle transport `τ = t'_ipq ≫ fst` and `f_pq ≫ ι_p`).
Consequence of `glueData_bridge_mid` and the glue condition. Project-local. -/
theorem glueData_triple_square (D : Scheme.GlueData.{0}) (i p q : D.J) :
    (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i)) ≫ (D.f p q ≫ D.ι p)
      = (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p) ≫ D.ι i := by
  rw [← Category.assoc, ← glueData_bridge_mid D i p q]
  simp only [Category.assoc]
  rw [D.glue_condition i p]

/-- **Triple-overlap opens identity**: for an open `V` of the chart `U_i`, the preimage
under `f_pq ≫ ι_p : V_pq ⟶ X` of its image in the glued scheme is the image, under the
cocycle transport `τ = t'_ipq ≫ fst`, of its preimage under `q = fst ≫ f_ip`. The
underlying-opens cartesianness of the triple-overlap square; triple analogue of
`glueData_preimage_image_eq` (via `ι_eq_iff` at the pairs `(i,p)` and `(i,q)`, the
point-range of `pullback.fst`, and injectivity of the open immersion `f_pq`).
Project-local. -/
lemma glueData_preimage_image_eq₃ (D : Scheme.GlueData.{0}) (i p q : D.J)
    (V : (D.U i).Opens) :
    (D.f p q ≫ D.ι p) ⁻¹ᵁ ((D.ι i) ''ᵁ V)
      = (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i)) ''ᵁ
          ((pullback.fst (D.f i p) (D.f i q) ≫ D.f i p) ⁻¹ᵁ V) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hyV, hyx⟩ := hx
    -- `y` is glued to `f_pq x` through the overlap `V_ip` …
    obtain ⟨w₁, hw₁, hw₁'⟩ := (D.ι_eq_iff i p y ((D.f p q) x)).mp hyx
    -- … and to `(t_pq ≫ f_qp) x` through `V_iq` (via the glue condition at `(p,q)`)
    have hgl : (D.ι i) y = (D.ι q) ((D.t p q ≫ D.f q p) x) :=
      hyx.trans (congrArg (fun m : D.V (p, q) ⟶ D.glued => m x)
        ((Category.assoc _ _ _).trans (D.glue_condition p q))).symm
    obtain ⟨w₂, hw₂, _⟩ := (D.ι_eq_iff i q y ((D.t p q ≫ D.f q p) x)).mp hgl
    -- hence `w₁` lifts to the triple overlap `V_ipq`
    have hw₁_range : w₁ ∈ Set.range (pullback.fst (D.f i p) (D.f i q)) := by
      rw [IsOpenImmersion.range_pullbackFst (D.f i q) (D.f i p)]
      exact ⟨w₂, hw₂.trans hw₁.symm⟩
    obtain ⟨w, hw⟩ := hw₁_range
    refine ⟨w, ?_, ?_⟩
    · -- the lift lies over `V`
      change (D.f i p) ((pullback.fst (D.f i p) (D.f i q)) w) ∈ V
      rw [hw, hw₁]; exact hyV
    · -- and transports to `x`: compare under the injective open immersion `f_pq`
      apply (D.f p q).isOpenEmbedding.injective
      exact (congrArg (fun m : Limits.pullback (D.f i p) (D.f i q) ⟶ D.U p => m w)
          (glueData_bridge_mid D i p q)).symm.trans
        ((congrArg (D.t i p ≫ D.f p i) hw).trans hw₁')
  · rintro ⟨w, hwV, rfl⟩
    refine ⟨(pullback.fst (D.f i p) (D.f i q) ≫ D.f i p) w, hwV, ?_⟩
    exact congrArg (fun m : Limits.pullback (D.f i p) (D.f i q) ⟶ D.glued => m w)
      (glueData_triple_square D i p q).symm

/-- **The two composite opens functors of the triple-overlap square are equal**: going
"into the glued scheme along `ι_i` and back down to `V_pq`" is the same site functor
as "down to the triple overlap along `q = fst ≫ f_ip` and across along
`τ = t'_ipq ≫ fst`". Object-level content is `glueData_preimage_image_eq₃`; morphisms
are proof-irrelevant in the opens preorder. Triple analogue of
`glueData_overlap_opensFunctor_eq`. Project-local. -/
lemma glueData_triple_opensFunctor_eq (D : Scheme.GlueData.{0}) (i p q : D.J) :
    (D.ι i).opensFunctor ⋙ TopologicalSpace.Opens.map (D.f p q ≫ D.ι p).base
      = TopologicalSpace.Opens.map (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p).base ⋙
          (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i)).opensFunctor :=
  CategoryTheory.Functor.ext (fun V => glueData_preimage_image_eq₃ D i p q V)
    (fun _ _ _ => Subsingleton.elim _ _)

/-- **Structure-sheaf compatibility of the triple-overlap square**: the two composite
section maps `Γ(U_i, V) ⟶ Γ(V_pq, τ ''ᵁ (q ⁻¹ᵁ V))` — "through the glued scheme" and
"through the triple overlap" — coincide. Both are the `appLE` of the two (equal)
composites of the square (`glueData_triple_square`); triple analogue of
`glueData_overlap_appIso_compat`. Project-local. -/
lemma glueData_triple_appIso_compat (D : Scheme.GlueData.{0}) (i p q : D.J)
    (V : (D.U i).Opens) :
    ((D.ι i).appIso V).inv ≫ (D.f p q ≫ D.ι p).app ((D.ι i) ''ᵁ V) ≫
        (D.V (p, q)).presheaf.map
          (eqToHom (glueData_preimage_image_eq₃ D i p q V).symm).op
      = (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p).app V ≫
        ((D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i)).appIso
          ((pullback.fst (D.f i p) (D.f i q) ≫ D.f i p) ⁻¹ᵁ V)).inv := by
  rw [Iso.eq_comp_inv]
  simp only [Category.assoc]
  rw [Iso.inv_comp_eq]
  simp only [Scheme.Hom.appIso_hom', Scheme.Hom.app_eq_appLE,
    Scheme.Hom.appLE_map_assoc, Scheme.Hom.appLE_comp_appLE]
  exact appLE_congr_mor (glueData_triple_square D i p q) _ _ _ _

/-- **Triple-overlap base change** (`β_ipq`): restricting a pushforward
`(f_pq ≫ ι_p)_* N` (of a sheaf on the pair overlap `V_pq`) to the chart `U_i` is the
same as restricting `N` to the triple overlap `V_ipq` along `τ = t'_ipq ≫ fst` and
pushing forward along `q = fst ≫ f_ip`. Same four-factor recipe as
`glueOverlapBaseChangeIso` over the opens identity `glueData_preimage_image_eq₃`.
Project-local. -/
noncomputable def glueTripleBaseChangeIso (D : Scheme.GlueData.{0}) (i p q : D.J) :
    Scheme.Modules.pushforward (D.f p q ≫ D.ι p) ⋙ restrictFunctor (D.ι i)
      ≅ restrictFunctor (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i)) ⋙
        Scheme.Modules.pushforward (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p) :=
  haveI h₁ : Functor.IsContinuous
      ((D.ι i).opensFunctor ⋙ TopologicalSpace.Opens.map (D.f p q ≫ D.ι p).base)
      (Opens.grothendieckTopology ↥(D.U i))
      (Opens.grothendieckTopology ↥(D.V (p, q))) :=
    Functor.isContinuous_comp _ _ _
      (Opens.grothendieckTopology ↥(D.glued)) _
  haveI h₂ : Functor.IsContinuous
      (TopologicalSpace.Opens.map (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p).base ⋙
        (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i)).opensFunctor)
      (Opens.grothendieckTopology ↥(D.U i))
      (Opens.grothendieckTopology ↥(D.V (p, q))) :=
    Functor.isContinuous_comp _ _ _
      (Opens.grothendieckTopology ↥(Limits.pullback (D.f i p) (D.f i q))) _
  SheafOfModules.pushforwardComp _ _ ≪≫
    SheafOfModules.pushforwardNatIso _
      (NatIso.ofComponents
        (fun V => eqToIso (glueData_preimage_image_eq₃ D i p q V).symm)
        (fun _ => Subsingleton.elim _ _)) ≪≫
    SheafOfModules.pushforwardCongr (by
      ext V x
      exact congr($(glueData_triple_appIso_compat D i p q (unop V)) x)) ≪≫
    (SheafOfModules.pushforwardComp _ _).symm

/-- Sections of the triple-overlap base change, inverse side: on sections over
`V ⊆ U_i`, the inverse of `β_ipq` is the restriction map of `N` along the opens
identity `glueData_preimage_image_eq₃`. Project-local. -/
lemma glueTripleBaseChangeIso_inv_app_app (D : Scheme.GlueData.{0}) (i p q : D.J)
    (N : (D.V (p, q)).Modules) (V : (D.U i).Opens) :
    (((glueTripleBaseChangeIso D i p q).inv.app N).app V :
        Γ(N, (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i)) ''ᵁ
            ((pullback.fst (D.f i p) (D.f i q) ≫ D.f i p) ⁻¹ᵁ V))
          ⟶ Γ(N, (D.f p q ≫ D.ι p) ⁻¹ᵁ ((D.ι i) ''ᵁ V)))
      = N.presheaf.map (eqToHom (glueData_preimage_image_eq₃ D i p q V)).op := by
  ext x
  rfl

/-- Hom-side companion of `glueTripleBaseChangeIso_inv_app_app`. Project-local. -/
lemma glueTripleBaseChangeIso_hom_app_app (D : Scheme.GlueData.{0}) (i p q : D.J)
    (N : (D.V (p, q)).Modules) (V : (D.U i).Opens) :
    (((glueTripleBaseChangeIso D i p q).hom.app N).app V :
        Γ(N, (D.f p q ≫ D.ι p) ⁻¹ᵁ ((D.ι i) ''ᵁ V))
          ⟶ Γ(N, (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i)) ''ᵁ
            ((pullback.fst (D.f i p) (D.f i q) ≫ D.f i p) ⁻¹ᵁ V)))
      = N.presheaf.map (eqToHom (glueData_preimage_image_eq₃ D i p q V).symm).op := by
  ext x
  rfl

/-! ### Bridges between the geometric and the site-level adjunction

`Scheme.Modules.pullbackPushforwardAdjunction f` (the geometric adjunction, with the
sheafification-built pullback) and `restrictAdjunction f` (the site-level adjunction
along an open immersion, with concrete unit/counit) share the right adjoint
`pushforward f`; `restrictFunctorIsoPullback f` is their `leftAdjointUniq`. The next
lemmas transport units, counits and congruence casts across that identification —
they are the vehicle by which the descent obligations are reduced to section-level
computations. -/

/-- **Unit comparison**: the geometric adjunction unit is the (concrete) site-level
unit followed by the pushforward of the `leftAdjointUniq` comparison. Project-local. -/
@[reassoc]
lemma restrictAdjunction_unit_app_iso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (N : Y.Modules) :
    (restrictAdjunction f).unit.app N ≫
        (Scheme.Modules.pushforward f).map ((restrictFunctorIsoPullback f).hom.app N)
      = (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ _

/-- **Counit comparison**: the `leftAdjointUniq` comparison followed by the geometric
counit is the (concrete) site-level counit. Project-local. -/
@[reassoc]
lemma restrictFunctorIsoPullback_hom_app_counit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (N : X.Modules) :
    (restrictFunctorIsoPullback f).hom.app ((Scheme.Modules.pushforward f).obj N) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app N
      = (restrictAdjunction f).counit.app N :=
  Adjunction.leftAdjointUniq_hom_app_counit _ _ _

/-- The congruence cast of equal morphisms at the pullback-functor level, evaluated at
an object, is the `eqToHom` of the object-level equality. Generic `subst` lemma.
Project-local. -/
lemma pullbackCongr_hom_app_eqToHom {X Y : Scheme.{u}} {φ ψ : X ⟶ Y} (h : φ = ψ)
    (N : Y.Modules) :
    (Scheme.Modules.pullbackCongr h).hom.app N
      = eqToHom (congrArg (fun α => (Scheme.Modules.pullback α).obj N) h) := by
  subst h
  simp [Scheme.Modules.pullbackCongr]

/-- The site-level congruence cast at `rfl` is the identity. Project-local. -/
lemma restrictFunctorCongr_rfl_hom_app {X Y : Scheme.{u}} (φ : X ⟶ Y) [IsOpenImmersion φ]
    (N : Y.Modules) :
    (restrictFunctorCongr (rfl : φ = φ)).hom.app N = 𝟙 _ := by
  ext U x
  rw [restrictFunctorCongr_hom_app_app]
  -- `eqToHom` of a self-equality is definitionally the identity (proof irrelevance)
  exact congr($(N.presheaf.map_id _) x)

/-- **Congruence compatibility of the `leftAdjointUniq` comparison**: for equal open
immersions `φ = ψ` the comparison intertwines the pullback-level and the site-level
congruence casts. Generic `subst` lemma. Project-local. -/
@[reassoc]
lemma restrictFunctorIsoPullback_congr {X Y : Scheme.{u}} {φ ψ : X ⟶ Y} (h : φ = ψ)
    [IsOpenImmersion φ] [IsOpenImmersion ψ] (N : Y.Modules) :
    (restrictFunctorIsoPullback φ).hom.app N ≫ (Scheme.Modules.pullbackCongr h).hom.app N
      = (restrictFunctorCongr h).hom.app N ≫ (restrictFunctorIsoPullback ψ).hom.app N := by
  subst h
  rw [pullbackCongr_hom_app_eqToHom, restrictFunctorCongr_rfl_hom_app, eqToHom_refl,
    Category.comp_id, Category.id_comp]

/-! ### Triple-overlap base change in pullback form, and its transpose -/

/-- **Object-level triple-overlap base change in pullback form**: the `β_ipq` of
`glueTripleBaseChangeIso`, evaluated at a sheaf `N` on the pair overlap `V_pq` and
conjugated through `restrictFunctorIsoPullback` on both sides. Triple analogue of
`glueOverlapFactorIso`. Project-local. -/
noncomputable def glueTripleFactorIso (D : Scheme.GlueData.{0}) (i p q : D.J)
    (N : (D.V (p, q)).Modules) :
    (Scheme.Modules.pullback (D.ι i)).obj
        ((Scheme.Modules.pushforward (D.f p q ≫ D.ι p)).obj N)
      ≅ (Scheme.Modules.pushforward (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p)).obj
          ((Scheme.Modules.pullback
            (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).obj N) :=
  (restrictFunctorIsoPullback (D.ι i)).symm.app
      ((Scheme.Modules.pushforward (D.f p q ≫ D.ι p)).obj N) ≪≫
    (glueTripleBaseChangeIso D i p q).app N ≪≫
    (Scheme.Modules.pushforward (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p)).mapIso
      ((restrictFunctorIsoPullback (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).app N)

/-- **Transpose of the triple-overlap base change** (triple mate core): the adjoint
transpose along `ι_i` of the pullback-form triple base change is the canonical
four-functor comparison of the triple square — the unit along `τ = t'_ipq ≫ fst`
pushed forward along `f_pq ≫ ι_p`, regrouped by `pushforwardComp`, re-indexed by
`pushforwardCongr` along `glueData_triple_square`, and ungrouped by
`pushforwardComp⁻¹`. Cocycle-free site-level content; triple analogue of
`glueOverlapFactor_transpose` (same proof). Project-local. -/
lemma glueTripleFactor_transpose (D : Scheme.GlueData.{0}) (i p q : D.J)
    (N : (D.V (p, q)).Modules) :
    (Scheme.Modules.pushforward (D.f p q ≫ D.ι p)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction
          (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).unit.app N) ≫
      (Scheme.Modules.pushforwardComp (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))
        (D.f p q ≫ D.ι p)).hom.app
        ((Scheme.Modules.pullback
          (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).obj N) ≫
      (Scheme.Modules.pushforwardCongr (glueData_triple_square D i p q)).hom.app
        ((Scheme.Modules.pullback
          (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).obj N) ≫
      (Scheme.Modules.pushforwardComp (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p)
        (D.ι i)).inv.app
        ((Scheme.Modules.pullback
          (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).obj N)
    = (Scheme.Modules.pullbackPushforwardAdjunction (D.ι i)).homEquiv
        ((Scheme.Modules.pushforward (D.f p q ≫ D.ι p)).obj N)
        ((Scheme.Modules.pushforward (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p)).obj
          ((Scheme.Modules.pullback
            (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).obj N))
        ((glueTripleFactorIso D i p q N).hom) := by
  have hglue := glueData_triple_square D i p q
  -- RHS: expand the transpose in unit form; the `leftAdjointUniq` conjugation of the
  -- chart comparison cancels against the unit bridge, leaving the site-level `β_ipq`
  have hRHS : (Scheme.Modules.pullbackPushforwardAdjunction (D.ι i)).homEquiv
        ((Scheme.Modules.pushforward (D.f p q ≫ D.ι p)).obj N)
        ((Scheme.Modules.pushforward (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p)).obj
          ((Scheme.Modules.pullback
            (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).obj N))
        ((glueTripleFactorIso D i p q N).hom)
      = (restrictAdjunction (D.ι i)).unit.app
          ((Scheme.Modules.pushforward (D.f p q ≫ D.ι p)).obj N) ≫
        (Scheme.Modules.pushforward (D.ι i)).map
          ((glueTripleBaseChangeIso D i p q).hom.app N) ≫
        (Scheme.Modules.pushforward (D.ι i)).map
          ((Scheme.Modules.pushforward
            (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p)).map
            ((restrictFunctorIsoPullback
              (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).hom.app N)) := by
    refine (Adjunction.homEquiv_unit _ _ _ _).trans ?_
    refine Eq.trans (eq_whisker
      (restrictAdjunction_unit_app_iso (D.ι i)
        ((Scheme.Modules.pushforward (D.f p q ≫ D.ι p)).obj N)).symm _) ?_
    refine (Category.assoc _ _ _).trans (whisker_eq _ ?_)
    refine ((Scheme.Modules.pushforward (D.ι i)).map_comp _ _).symm.trans ?_
    refine Eq.trans (congrArg (Scheme.Modules.pushforward (D.ι i)).map ?_)
      ((Scheme.Modules.pushforward (D.ι i)).map_comp _ _)
    exact Iso.hom_inv_id_app_assoc (restrictFunctorIsoPullback (D.ι i)) _ _
  rw [hRHS]
  -- LHS: bridge the geometric unit at `τ` to the site-level unit; the emerging
  -- `restrictFunctorIsoPullback` factor migrates across the three casts by naturality
  have h_a : (Scheme.Modules.pushforward (D.f p q ≫ D.ι p)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction
          (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).unit.app N)
      = (Scheme.Modules.pushforward (D.f p q ≫ D.ι p)).map
          ((restrictAdjunction
            (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).unit.app N) ≫
        (Scheme.Modules.pushforward (D.f p q ≫ D.ι p)).map
          ((Scheme.Modules.pushforward
            (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).map
            ((restrictFunctorIsoPullback
              (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).hom.app N)) :=
    (congrArg (Scheme.Modules.pushforward (D.f p q ≫ D.ι p)).map
        (restrictAdjunction_unit_app_iso
          (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i)) N).symm).trans
      ((Scheme.Modules.pushforward (D.f p q ≫ D.ι p)).map_comp _ _)
  have n₁ := (Scheme.Modules.pushforwardComp
      (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i)) (D.f p q ≫ D.ι p)).hom.naturality
    ((restrictFunctorIsoPullback
      (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).hom.app N)
  have n₂ := (Scheme.Modules.pushforwardCongr hglue).hom.naturality
    ((restrictFunctorIsoPullback
      (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).hom.app N)
  have n₃ := (Scheme.Modules.pushforwardComp
      (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p) (D.ι i)).inv.naturality
    ((restrictFunctorIsoPullback
      (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).hom.app N)
  -- the site-level core: all four factors are concrete on sections; both sides are a
  -- single presheaf restriction along the triple opens identity
  have hcore : (Scheme.Modules.pushforward (D.f p q ≫ D.ι p)).map
        ((restrictAdjunction
          (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).unit.app N) ≫
      (Scheme.Modules.pushforwardComp (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))
        (D.f p q ≫ D.ι p)).hom.app
        ((restrictFunctor (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).obj N) ≫
      (Scheme.Modules.pushforwardCongr hglue).hom.app
        ((restrictFunctor (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).obj N) ≫
      (Scheme.Modules.pushforwardComp (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p)
        (D.ι i)).inv.app
        ((restrictFunctor (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).obj N)
      = (restrictAdjunction (D.ι i)).unit.app
          ((Scheme.Modules.pushforward (D.f p q ≫ D.ι p)).obj N) ≫
        (Scheme.Modules.pushforward (D.ι i)).map
          ((glueTripleBaseChangeIso D i p q).hom.app N) := by
    ext O x
    have htot : N.presheaf.map
          (homOfLE ((D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i)).image_preimage_le
            ((D.f p q ≫ D.ι p) ⁻¹ᵁ O))).op ≫
        N.presheaf.map
          ((D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i)).opensFunctor.map
            (eqToHom (show ((pullback.fst (D.f i p) (D.f i q) ≫ D.f i p) ≫ D.ι i) ⁻¹ᵁ O
                = ((D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i)) ≫
                    (D.f p q ≫ D.ι p)) ⁻¹ᵁ O by
              rw [hglue]))).op
        = N.presheaf.map ((TopologicalSpace.Opens.map (D.f p q ≫ D.ι p).base).map
            (homOfLE ((D.ι i).image_preimage_le O))).op ≫
          N.presheaf.map
            (eqToHom (glueData_preimage_image_eq₃ D i p q ((D.ι i) ⁻¹ᵁ O)).symm).op := by
      erw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg N.presheaf.map (Subsingleton.elim _ _)
    exact congr($(htot) x)
  -- restate `h_a` with the composite-functor map (defeq) so `n₁` fires syntactically
  have h_a' : (Scheme.Modules.pushforward (D.f p q ≫ D.ι p)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction
          (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).unit.app N)
      = (Scheme.Modules.pushforward (D.f p q ≫ D.ι p)).map
          ((restrictAdjunction
            (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).unit.app N) ≫
        (Scheme.Modules.pushforward (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i)) ⋙
          Scheme.Modules.pushforward (D.f p q ≫ D.ι p)).map
          ((restrictFunctorIsoPullback
            (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).hom.app N) := h_a
  rw [h_a']
  -- inner chain: migrate the comparison factor through the three casts (`n₁`–`n₃`)
  have hmove : (Scheme.Modules.pushforward
        (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i)) ⋙
        Scheme.Modules.pushforward (D.f p q ≫ D.ι p)).map
        ((restrictFunctorIsoPullback
          (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).hom.app N) ≫
      (Scheme.Modules.pushforwardComp (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))
        (D.f p q ≫ D.ι p)).hom.app
        ((Scheme.Modules.pullback
          (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).obj N) ≫
      (Scheme.Modules.pushforwardCongr hglue).hom.app
        ((Scheme.Modules.pullback
          (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).obj N) ≫
      (Scheme.Modules.pushforwardComp (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p)
        (D.ι i)).inv.app
        ((Scheme.Modules.pullback
          (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).obj N)
      = (Scheme.Modules.pushforwardComp (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))
          (D.f p q ≫ D.ι p)).hom.app
          ((restrictFunctor (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).obj N) ≫
        (Scheme.Modules.pushforwardCongr hglue).hom.app
          ((restrictFunctor (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).obj N) ≫
        (Scheme.Modules.pushforwardComp (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p)
          (D.ι i)).inv.app
          ((restrictFunctor (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).obj N) ≫
        (Scheme.Modules.pushforward (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p) ⋙
          Scheme.Modules.pushforward (D.ι i)).map
          ((restrictFunctorIsoPullback
            (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).hom.app N) :=
    (Category.assoc _ _ _).symm.trans ((eq_whisker n₁ _).trans
      ((Category.assoc _ _ _).trans (whisker_eq _
        ((Category.assoc _ _ _).symm.trans ((eq_whisker n₂ _).trans
          ((Category.assoc _ _ _).trans (whisker_eq _ n₃)))))))
  refine (Category.assoc _ _ _).trans ((whisker_eq _ hmove).trans ?_)
  refine ((whisker_eq _ ((whisker_eq _ (Category.assoc _ _ _).symm).trans
    (Category.assoc _ _ _).symm)).trans ?_)
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (eq_whisker hcore _).trans ?_
  exact Category.assoc _ _ _

/-- **Mate recognition for the triple-overlap square**: for any `W` on the glued
scheme and `m : W ⟶ (f_pq ≫ ι_p)_* N`, transposing `m` along `f_pq ≫ ι_p`, pulling
back to the triple overlap along `τ = t'_ipq ≫ fst`, and re-indexing through the
pullback-pseudofunctor casts of the triple square equals the transpose along
`q = fst ≫ f_ip` of `ι_i^* m` composed with the triple base change in pullback form
(`glueTripleFactorIso`). Triple analogue of `glueOverlapFactor_mate` (same proof,
reducing to the mate core `glueTripleFactor_transpose`). Project-local. -/
lemma glueTripleFactor_mate (D : Scheme.GlueData.{0}) (i p q : D.J)
    (N : (D.V (p, q)).Modules) {W : D.glued.Modules}
    (m : W ⟶ (Scheme.Modules.pushforward (D.f p q ≫ D.ι p)).obj N) :
    (Scheme.Modules.pullbackComp (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p)
        (D.ι i)).hom.app W ≫
      (Scheme.Modules.pullbackCongr (glueData_triple_square D i p q)).inv.app W ≫
      (Scheme.Modules.pullbackComp (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))
        (D.f p q ≫ D.ι p)).inv.app W ≫
      (Scheme.Modules.pullback (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).map
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (D.f p q ≫ D.ι p)).homEquiv W N).symm m)
    = ((Scheme.Modules.pullbackPushforwardAdjunction
          (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p)).homEquiv
          ((Scheme.Modules.pullback (D.ι i)).obj W)
          ((Scheme.Modules.pullback
            (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).obj N)).symm
        ((Scheme.Modules.pullback (D.ι i)).map m ≫
          (glueTripleFactorIso D i p q N).hom) := by
  have hglue := glueData_triple_square D i p q
  apply ((Scheme.Modules.pullbackPushforwardAdjunction
    (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p)).homEquiv
    ((Scheme.Modules.pullback (D.ι i)).obj W)
    ((Scheme.Modules.pullback
      (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).obj N)).injective
  refine Eq.trans ?_ (Equiv.apply_symm_apply _ _).symm
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (D.ι i)).homEquiv _ _).injective
  -- right-hand side: peel `m` off by naturality of the transpose
  have hR : (Scheme.Modules.pullbackPushforwardAdjunction (D.ι i)).homEquiv _ _
        ((Scheme.Modules.pullback (D.ι i)).map m ≫ (glueTripleFactorIso D i p q N).hom)
      = m ≫ (Scheme.Modules.pullbackPushforwardAdjunction (D.ι i)).homEquiv _ _
          ((glueTripleFactorIso D i p q N).hom) :=
    Adjunction.homEquiv_naturality_left _ _ _
  -- the conjugate of `pullbackComp.hom` is `pushforwardComp.inv`
  have hcomm := CategoryTheory.conjugateEquiv_comm
    (adj₁ := (Scheme.Modules.pullbackPushforwardAdjunction (D.ι i)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction
        (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p)))
    (adj₂ := Scheme.Modules.pullbackPushforwardAdjunction
      ((pullback.fst (D.f i p) (D.f i q) ≫ D.f i p) ≫ D.ι i))
    (show (Scheme.Modules.pullbackComp (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p)
        (D.ι i)).hom ≫
        (Scheme.Modules.pullbackComp (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p)
          (D.ι i)).inv = 𝟙 _
      from (Scheme.Modules.pullbackComp (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p)
        (D.ι i)).hom_inv_id)
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at hcomm
  have hConj : CategoryTheory.conjugateEquiv
        (Scheme.Modules.pullbackPushforwardAdjunction
          ((pullback.fst (D.f i p) (D.f i q) ≫ D.f i p) ≫ D.ι i))
        ((Scheme.Modules.pullbackPushforwardAdjunction (D.ι i)).comp
          (Scheme.Modules.pullbackPushforwardAdjunction
            (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p)))
        (Scheme.Modules.pullbackComp (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p)
          (D.ι i)).hom
      = (Scheme.Modules.pushforwardComp (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p)
          (D.ι i)).inv :=
    (CategoryTheory.Iso.hom_comp_eq_id _).mp hcomm
  -- transpose of the inner chain along `τ ≫ (f_pq ≫ ι_p)`: fold the unit pair
  have h1 : (Scheme.Modules.pullbackPushforwardAdjunction
        ((D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i)) ≫
          (D.f p q ≫ D.ι p))).homEquiv W
        ((Scheme.Modules.pullback
          (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).obj N)
        ((Scheme.Modules.pullbackComp (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))
          (D.f p q ≫ D.ι p)).inv.app W ≫
          (Scheme.Modules.pullback
            (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).map
            (((Scheme.Modules.pullbackPushforwardAdjunction
              (D.f p q ≫ D.ι p)).homEquiv W N).symm m))
      = m ≫ ((Scheme.Modules.pushforward (D.f p q ≫ D.ι p)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction
            (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).unit.app N) ≫
        (Scheme.Modules.pushforwardComp (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))
          (D.f p q ≫ D.ι p)).hom.app
          ((Scheme.Modules.pullback
            (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).obj N)) := by
    have h := homEquiv_comp_unit_pushforwardComp
      (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i)) (D.f p q ≫ D.ι p)
      (((Scheme.Modules.pullbackPushforwardAdjunction
        (D.f p q ≫ D.ι p)).homEquiv W N).symm m)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  -- re-index along the triple square
  have h2 := homEquiv_comp_pushforwardCongr hglue
    (W := W)
    (y := (Scheme.Modules.pullbackComp (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))
        (D.f p q ≫ D.ι p)).inv.app W ≫
      (Scheme.Modules.pullback (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).map
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (D.f p q ≫ D.ι p)).homEquiv W N).symm m))
  -- the double transpose of the full cast chain
  have hstar := homEquiv_conjugateEquiv_app
    (Scheme.Modules.pullbackPushforwardAdjunction
      ((pullback.fst (D.f i p) (D.f i q) ≫ D.f i p) ≫ D.ι i))
    ((Scheme.Modules.pullbackPushforwardAdjunction (D.ι i)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction
        (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p)))
    (Scheme.Modules.pullbackComp (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p)
      (D.ι i)).hom
    (f := (Scheme.Modules.pullbackCongr hglue).inv.app W ≫
      (Scheme.Modules.pullbackComp (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))
        (D.f p q ≫ D.ι p)).inv.app W ≫
      (Scheme.Modules.pullback (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).map
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (D.f p q ≫ D.ι p)).homEquiv W N).symm m))
  rw [hConj] at hstar
  -- assemble: LHS double transpose = m ≫ (four-functor comparison) = m ≫ transpose β₃
  refine Eq.trans ?_ hR.symm
  refine Eq.trans (?_ : _ = ((Scheme.Modules.pullbackPushforwardAdjunction
      ((pullback.fst (D.f i p) (D.f i q) ≫ D.f i p) ≫ D.ι i)).homEquiv W _
      ((Scheme.Modules.pullbackCongr hglue).inv.app W ≫
        (Scheme.Modules.pullbackComp (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))
          (D.f p q ≫ D.ι p)).inv.app W ≫
        (Scheme.Modules.pullback (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).map
          (((Scheme.Modules.pullbackPushforwardAdjunction
            (D.f p q ≫ D.ι p)).homEquiv W N).symm m)) ≫
      (Scheme.Modules.pushforwardComp (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p)
        (D.ι i)).inv.app
        ((Scheme.Modules.pullback
          (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).obj N))) ?_
  · -- the composite-adjunction transpose computes the nested transposes
    refine Eq.trans ?_ hstar
    rw [Adjunction.comp_homEquiv]
    rfl
  · -- substitute `h2`, then `h1`, regroup, and finish with the mate core
    rw [← h2]
    exact (eq_whisker (eq_whisker h1 _) _).trans
      ((eq_whisker (Category.assoc _ _ _) _).trans
        ((Category.assoc _ _ _).trans (whisker_eq m
          ((eq_whisker (Category.assoc _ _ _) _).trans
            ((Category.assoc _ _ _).trans ((whisker_eq _ (Category.assoc _ _ _)).trans
              (glueTripleFactor_transpose D i p q N)))))))

/-- **Transpose of the first descent-leg factor** along the composite overlap
immersion `f_pq ≫ ι_p`: the `aComp`-factor of `glueLegA` (unit along `f_pq` +
`pushforwardComp`) transposes to the pseudofunctor cast followed by the pullback of
the geometric counit. Instance of `homEquiv_comp_unit_pushforwardComp` at the counit
(whose transpose is the identity, by the right triangle). Project-local. -/
lemma glueLegA_component_transpose (D : Scheme.GlueData.{0}) (p q : D.J)
    (Mp : (D.U p).Modules) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (D.f p q ≫ D.ι p)).homEquiv
        ((Scheme.Modules.pushforward (D.ι p)).obj Mp)
        ((Scheme.Modules.pullback (D.f p q)).obj Mp)).symm
        ((Scheme.Modules.pushforward (D.ι p)).map
            ((Scheme.Modules.pullbackPushforwardAdjunction (D.f p q)).unit.app Mp) ≫
          (Scheme.Modules.pushforwardComp (D.f p q) (D.ι p)).hom.app
            ((Scheme.Modules.pullback (D.f p q)).obj Mp))
      = (Scheme.Modules.pullbackComp (D.f p q) (D.ι p)).inv.app
          ((Scheme.Modules.pushforward (D.ι p)).obj Mp) ≫
        (Scheme.Modules.pullback (D.f p q)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (D.ι p)).counit.app Mp) := by
  rw [Equiv.symm_apply_eq]
  have hε : (Scheme.Modules.pullbackPushforwardAdjunction (D.ι p)).homEquiv
        ((Scheme.Modules.pushforward (D.ι p)).obj Mp) Mp
        ((Scheme.Modules.pullbackPushforwardAdjunction (D.ι p)).counit.app Mp)
      = 𝟙 ((Scheme.Modules.pushforward (D.ι p)).obj Mp) :=
    (Adjunction.homEquiv_unit _ _ _ _).trans
      ((Scheme.Modules.pullbackPushforwardAdjunction (D.ι p)).right_triangle_components
        Mp)
  have h := homEquiv_comp_unit_pushforwardComp (D.f p q) (D.ι p)
    ((Scheme.Modules.pullbackPushforwardAdjunction (D.ι p)).counit.app Mp)
  -- `rw [hε] at h` cannot match (the counit codomain carries a `𝟭`-wrapper); term-mode
  exact (Category.id_comp _).symm.trans ((eq_whisker hε _).symm.trans h)

/-! ### Pseudofunctor cast coherence for the conjugated cocycle

The remaining content of the descent obligation (`glueChartComponent_leg_compat`) is a
comparison of two regroupings of iterated pullbacks: the route through the glued scheme
(the triple-square casts) against the route through the chart overlaps (the pair-square
casts whiskered by the triple-overlap projections). This comparison is *pure cast
coherence*: it involves only the pseudofunctor comparisons `pullbackComp` and the
congruence casts `pullbackCongr` — no units, counits, or transition isomorphisms. The
block below derives it (`pullback_cast_compat`) from the Mathlib associativity
2-cocycle `Scheme.Modules.pseudofunctor_associativity` specialised to objects, plus a
handful of generic `subst`-style `pullbackComp`/`pullbackCongr` compatibilities. -/

section CastCoherence

/-- Generic 4-factor rearrangement: solve an iso-chain equation for its last factor.
Project-local helper for the solved forms of the associativity cocycle. -/
private lemma comp4_solve_last {𝒞 : Type*} [Category 𝒞] {a b c d e : 𝒞}
    (A : a ≅ b) (B : b ≅ c) (Cc : c ≅ d) {D : d ⟶ e} {E : a ⟶ e}
    (hE : A.hom ≫ B.hom ≫ Cc.hom ≫ D = E) :
    D = Cc.inv ≫ B.inv ≫ A.inv ≫ E := by
  rw [← hE]; simp

/-- Generic 4-factor rearrangement: solve an iso-chain equation for its middle pair.
Project-local. -/
private lemma comp4_solve_mid {𝒞 : Type*} [Category 𝒞] {a b c d e : 𝒞}
    (A : a ≅ b) {B : b ⟶ c} {Cc : c ⟶ d} (D : d ≅ e) {E : a ⟶ e}
    (hE : A.hom ≫ B ≫ Cc ≫ D.hom = E) :
    B ≫ Cc = A.inv ≫ E ≫ D.inv := by
  rw [← hE]; simp

/-- Generic 4-factor rearrangement: solve an iso-chain equation for its front pair.
Project-local. -/
private lemma comp4_solve_front {𝒞 : Type*} [Category 𝒞] {a b c d e : 𝒞}
    {A : a ⟶ b} {B : b ⟶ c} (Cc : c ≅ d) (D : d ≅ e) {E : a ⟶ e}
    (hE : A ≫ B ≫ Cc.hom ≫ D.hom = E) :
    A ≫ B = E ≫ D.inv ≫ Cc.inv := by
  rw [← hE]; simp

/-- `pullbackCongr` evaluated at an object, inverse side: the `eqToHom` of the
object-level equality. Generic `subst` companion of `pullbackCongr_hom_app_eqToHom`.
Project-local. -/
lemma pullbackCongr_inv_app_eqToHom {T' T : Scheme.{u}} {φ ψ : T' ⟶ T} (h : φ = ψ)
    (N : T.Modules) :
    (Scheme.Modules.pullbackCongr h).inv.app N
      = eqToHom (congrArg (fun α => (Scheme.Modules.pullback α).obj N) h.symm) := by
  subst h
  simp [Scheme.Modules.pullbackCongr]

/-- The pseudofunctor associativity 2-cocycle of module pullback, at an object: the
two regroupings of a triple composite of pullbacks differ by the congruence cast along
`Category.assoc`. Object-level form of `Scheme.Modules.pseudofunctor_associativity`.
Project-local. -/
lemma pullbackComp_assoc_app {X' Y' Z' T' : Scheme.{u}} (f : X' ⟶ Y') (g : Y' ⟶ Z')
    (h : Z' ⟶ T') (M : T'.Modules) :
    (Scheme.Modules.pullbackComp f (g ≫ h)).inv.app M ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app M) ≫
        (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M) ≫
        (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M
      = (Scheme.Modules.pullbackCongr (Category.assoc f g h).symm).hom.app M := by
  have e := congrArg (fun α => α.app M)
    (Scheme.Modules.pseudofunctor_associativity (f := f) (g := g) (h := h))
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, eqToHom_app] at e
  rw [pullbackCongr_hom_app_eqToHom]
  exact e

/-- Solved form of the associativity cocycle at a composite first leg: the regrouping
comparison `((f ≫ g) ≫ h)^*` factors through the two inner comparisons and the
associativity cast. Project-local. -/
@[reassoc]
lemma pullbackComp_comp_fst_hom_app {X' Y' Z' T' : Scheme.{u}} (f : X' ⟶ Y')
    (g : Y' ⟶ Z') (h : Z' ⟶ T') (M : T'.Modules) :
    (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M
      = (Scheme.Modules.pullbackComp f g).inv.app ((Scheme.Modules.pullback h).obj M) ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M) ≫
        (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M ≫
        (Scheme.Modules.pullbackCongr (Category.assoc f g h).symm).hom.app M :=
  comp4_solve_last ((Scheme.Modules.pullbackComp f (g ≫ h)).app M).symm
    ((Scheme.Modules.pullback f).mapIso ((Scheme.Modules.pullbackComp g h).app M)).symm
    ((Scheme.Modules.pullbackComp f g).app ((Scheme.Modules.pullback h).obj M))
    (pullbackComp_assoc_app f g h M)

/-- Solved form of the associativity cocycle for the middle pair: pulling back the
inner regrouping inverse and regrouping the outer pair equals the comparison at the
composite second leg, the associativity cast, and the ungrouping at the composite
first leg. Project-local. -/
@[reassoc]
lemma pullback_map_inv_comp_hom_app {X' Y' Z' T' : Scheme.{u}} (f : X' ⟶ Y')
    (g : Y' ⟶ Z') (h : Z' ⟶ T') (M : T'.Modules) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app M) ≫
        (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M)
      = (Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M ≫
        (Scheme.Modules.pullbackCongr (Category.assoc f g h).symm).hom.app M ≫
        (Scheme.Modules.pullbackComp (f ≫ g) h).inv.app M :=
  ((comp4_solve_mid ((Scheme.Modules.pullbackComp f (g ≫ h)).app M).symm
    ((Scheme.Modules.pullbackComp (f ≫ g) h).app M)
    (pullbackComp_assoc_app f g h M)).trans (Category.assoc _ _ _).symm).trans
    (Category.assoc _ _ _)

/-- Solved form of the associativity cocycle for the front pair: ungrouping at the
composite second leg followed by the pulled-back inner ungrouping equals the
associativity cast, the ungrouping at the composite first leg, and the outer
ungrouping. Project-local. -/
@[reassoc]
lemma pullbackComp_inv_comp_map_inv_app {X' Y' Z' T' : Scheme.{u}} (f : X' ⟶ Y')
    (g : Y' ⟶ Z') (h : Z' ⟶ T') (M : T'.Modules) :
    (Scheme.Modules.pullbackComp f (g ≫ h)).inv.app M ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app M)
      = (Scheme.Modules.pullbackCongr (Category.assoc f g h).symm).hom.app M ≫
        (Scheme.Modules.pullbackComp (f ≫ g) h).inv.app M ≫
        (Scheme.Modules.pullbackComp f g).inv.app ((Scheme.Modules.pullback h).obj M) :=
  comp4_solve_front
    ((Scheme.Modules.pullbackComp f g).app ((Scheme.Modules.pullback h).obj M))
    ((Scheme.Modules.pullbackComp (f ≫ g) h).app M)
    (pullbackComp_assoc_app f g h M)

/-- Congruence compatibility of `pullbackComp` in its second argument (hom side).
Generic `subst` lemma. Project-local. -/
@[reassoc]
lemma pullback_map_congr_inv_comp_hom_app {X' Y' Z' : Scheme.{u}} (f : X' ⟶ Y')
    {x y : Y' ⟶ Z'} (h : x = y) (W : Z'.Modules) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackCongr h).inv.app W) ≫
        (Scheme.Modules.pullbackComp f x).hom.app W
      = (Scheme.Modules.pullbackComp f y).hom.app W ≫
        (Scheme.Modules.pullbackCongr
          (show f ≫ x = f ≫ y from by rw [h])).inv.app W := by
  subst h
  simp [Scheme.Modules.pullbackCongr]

/-- Congruence compatibility of `pullbackComp` in its second argument (inv side).
Generic `subst` lemma. Project-local. -/
@[reassoc]
lemma pullbackComp_inv_comp_map_congr_inv_app {X' Y' Z' : Scheme.{u}} (f : X' ⟶ Y')
    {x y : Y' ⟶ Z'} (h : x = y) (W : Z'.Modules) :
    (Scheme.Modules.pullbackComp f y).inv.app W ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackCongr h).inv.app W)
      = (Scheme.Modules.pullbackCongr
          (show f ≫ x = f ≫ y from by rw [h])).inv.app W ≫
        (Scheme.Modules.pullbackComp f x).inv.app W := by
  subst h
  simp [Scheme.Modules.pullbackCongr]
@[reassoc]
lemma pullbackComp_inv_comp_congr_hom_app {X' Y' Z' : Scheme.{u}} {x y : X' ⟶ Y'}
    (h : x = y) (κ : Y' ⟶ Z') (W : Z'.Modules) :
    (Scheme.Modules.pullbackComp x κ).inv.app W ≫
        (Scheme.Modules.pullbackCongr h).hom.app ((Scheme.Modules.pullback κ).obj W)
      = (Scheme.Modules.pullbackCongr
          (show x ≫ κ = y ≫ κ from by rw [h])).hom.app W ≫
        (Scheme.Modules.pullbackComp y κ).inv.app W := by
  subst h
  simp [Scheme.Modules.pullbackCongr]
lemma pullbackComp_hom_app_congr_fst {X' Y' Z' : Scheme.{u}} {x y : X' ⟶ Y'}
    (h : x = y) (κ : Y' ⟶ Z') (W : Z'.Modules) :
    (Scheme.Modules.pullbackComp x κ).hom.app W
      = (Scheme.Modules.pullbackCongr h).hom.app ((Scheme.Modules.pullback κ).obj W) ≫
        (Scheme.Modules.pullbackComp y κ).hom.app W ≫
        (Scheme.Modules.pullbackCongr
          (show y ≫ κ = x ≫ κ from by rw [h])).hom.app W := by
  subst h
  simp [Scheme.Modules.pullbackCongr]

/-- Generic 5-factor pipeline rearrangement: substitute a middle-pair regrouping, a
front-pair exchange and a back-pair exchange in one move. Stated in an abstract
category (where `rw` matching is reliable) and applied to the concrete pullback chain
by unification — the lever for the `X.Modules` instance diamond. Project-local. -/
private lemma comp5_rearrange {𝒞 : Type*} [Category 𝒞]
    {x₀ x₁ x₂ x₃ x₄ x₅ y₁ y₂ z₁ w : 𝒞}
    {d₃ : x₀ ⟶ x₁} {d₄ : x₁ ⟶ x₂} {d₅ : x₂ ⟶ x₃} {d₆ : x₃ ⟶ x₄} {d₇ : x₄ ⟶ x₅}
    {B : x₁ ⟶ y₁} {cC : y₁ ⟶ y₂} {e : y₂ ⟶ x₃} {A : x₀ ⟶ z₁} {cD : z₁ ⟶ y₁}
    {cE : y₂ ⟶ w} {f : w ⟶ x₄}
    (h45 : d₄ ≫ d₅ = B ≫ cC ≫ e) (h3 : d₃ ≫ B = A ≫ cD) (h6 : e ≫ d₆ = cE ≫ f) :
    d₃ ≫ d₄ ≫ d₅ ≫ d₆ ≫ d₇ = A ≫ cD ≫ cC ≫ cE ≫ f ≫ d₇ := by
  rw [reassoc_of% h45, reassoc_of% h6, ← Category.assoc d₃ B, h3, Category.assoc]

-- `backward.isDefEq.respectTransparency false`: the `pullbackComp` solved-forms unfold to the
-- `⋙`-composite object form (`pullback ι ⋙ pullback a`), which is only defeq (not syntactic) to
-- `(pullback a).obj ((pullback ι).obj W)`; without this the v4.31 `instances`-transparency wall
-- reports the target "not type-correct" and blocks the congruence-slide `rw`s.
/-- **Cast compatibility of the triple-overlap and pair-overlap regroupings** (the
coherence core of the conjugated cocycle): given a pair square `t ≫ κ = a ≫ ι`, a
middle bridge `u ≫ t = τ ≫ b` and the induced triple square
`τ ≫ (b ≫ κ) = (u ≫ a) ≫ ι`, the cast chain through the triple square equals the
pair-square cast chain pulled back along `u`, re-bracketed through the pseudofunctor
associativity. Pure cast coherence — no units, counits, or transition isomorphisms.
Project-local. -/
lemma pullback_cast_compat {P A' B' C' E' X' : Scheme.{u}}
    (u : P ⟶ A') (a : A' ⟶ C') (ι : C' ⟶ X') (t : A' ⟶ E') (κ : E' ⟶ X')
    (τ : P ⟶ B') (b : B' ⟶ E')
    (hpair : t ≫ κ = a ≫ ι) (hmid : u ≫ t = τ ≫ b)
    (htriple : τ ≫ (b ≫ κ) = (u ≫ a) ≫ ι) (W : X'.Modules) :
    (Scheme.Modules.pullbackComp (u ≫ a) ι).hom.app W ≫
        (Scheme.Modules.pullbackCongr htriple).inv.app W ≫
        (Scheme.Modules.pullbackComp τ (b ≫ κ)).inv.app W ≫
        (Scheme.Modules.pullback τ).map ((Scheme.Modules.pullbackComp b κ).inv.app W)
      = (Scheme.Modules.pullbackComp u a).inv.app ((Scheme.Modules.pullback ι).obj W) ≫
        (Scheme.Modules.pullback u).map ((Scheme.Modules.pullbackComp a ι).hom.app W) ≫
        (Scheme.Modules.pullback u).map ((Scheme.Modules.pullbackCongr hpair).inv.app W) ≫
        (Scheme.Modules.pullback u).map ((Scheme.Modules.pullbackComp t κ).inv.app W) ≫
        (Scheme.Modules.pullbackComp u t).hom.app ((Scheme.Modules.pullback κ).obj W) ≫
        (Scheme.Modules.pullbackCongr hmid).hom.app ((Scheme.Modules.pullback κ).obj W) ≫
        (Scheme.Modules.pullbackComp τ b).inv.app ((Scheme.Modules.pullback κ).obj W) := by
  -- Both routes reduce, via the associativity solved-forms, to `(common) ≫ eqToHom ≫ pair`.
  -- Phase 1 (keep the `pullbackCongr` casts as casts, use the `_assoc` reassociated forms so
  -- they fire mid-chain, `simp` re-flattens associativity between them): expand the `(u≫a)^*ι`-
  -- hom (fst solved form); fold `(pb u)`-map∘hom (R4≫R5) into `u^*(t≫κ)`; slide the `hpair`
  -- congruence through it to turn `u^*(t≫κ)` into `u^*(a≫ι)`; slide the `hmid` congruence
  -- through `(u≫t)^*κ`-inv into `(τ≫b)^*κ`-inv; expand the trailing `τ^*(b≫κ)`-inv (L3≫L4) into
  -- the matching `(τ≫b)^*κ`-inv ∘ `τ^*b`-inv pair.
  simp only [pullbackComp_comp_fst_hom_app, pullback_map_inv_comp_hom_app_assoc,
    pullback_map_congr_inv_comp_hom_app_assoc, pullbackComp_inv_comp_congr_hom_app_assoc,
    pullbackComp_inv_comp_map_inv_app, Category.assoc]
  -- Phase 2: the remaining chains of `pullbackCongr` casts are `eqToHom`s between the same
  -- endpoints, so they collapse (via the `_assoc` fold, since they sit mid-chain) by `eqToHom`
  -- uniqueness.
  simp only [pullbackCongr_hom_app_eqToHom, pullbackCongr_inv_app_eqToHom,
    eqToHom_trans_assoc]
private lemma map_fold₅ {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (F : 𝒞 ⥤ 𝒟)
    {x₀ x₁ x₂ x₃ x₄ x₅ : 𝒞} {a : x₀ ⟶ x₁} {k₁ : x₁ ⟶ x₂} {k₂ : x₂ ⟶ x₃} {k₃ : x₃ ⟶ x₄}
    {k₄ : x₄ ⟶ x₅} {z : x₀ ⟶ x₅} (h : a ≫ k₁ ≫ k₂ ≫ k₃ ≫ k₄ = z) :
    F.map a ≫ F.map k₁ ≫ F.map k₂ ≫ F.map k₃ ≫ F.map k₄ = F.map z := by
  rw [← F.map_comp, ← F.map_comp, ← F.map_comp, ← F.map_comp, h]

/-- **Generic left-side assembly for the conjugated cocycle**: substitute the cast
coherence (`hcast`), migrate the counit decoration `Y` through the three trailing
comparisons by the naturality squares `nY1`–`nY3`, peel the chart component off the
front by `nX`, and fold the chart-level collapse `hfold`. Pure rebracketing in an
abstract category, applied to the concrete pullback chain by unification.
Project-local. -/
private lemma side_collapse_left {𝒞 : Type*} [Category 𝒞]
    {x₀ x₁ y₁ y₂ y₃ y₄ y₅ a₁ a₂ a₃ a₄ a₅ a₆ b₁ m₁ m₂ m₃ : 𝒞}
    {X : x₀ ⟶ x₁} {c₁ : x₁ ⟶ y₁} {c₂ : y₁ ⟶ y₂} {c₃ : y₂ ⟶ y₃} {w : y₃ ⟶ y₅}
    {c₄ : y₃ ⟶ y₄} {Y : y₄ ⟶ y₅}
    {F1 : x₁ ⟶ a₁} {F2 : a₁ ⟶ a₂} {F3 : a₂ ⟶ a₃} {F4 : a₃ ⟶ a₄} {F5 : a₄ ⟶ a₅}
    {F6 : a₅ ⟶ a₆} {F7 : a₆ ⟶ y₄}
    {F1' : x₀ ⟶ b₁} {X' : b₁ ⟶ a₁}
    {Y₁ : a₆ ⟶ m₁} {F7' : m₁ ⟶ y₅} {Y₂ : a₅ ⟶ m₂} {F6' : m₂ ⟶ m₁}
    {Y₃ : a₄ ⟶ m₃} {F5' : m₃ ⟶ m₂} {Z : b₁ ⟶ m₃}
    (hw : w = c₄ ≫ Y)
    (hcast : c₁ ≫ c₂ ≫ c₃ ≫ c₄ = F1 ≫ F2 ≫ F3 ≫ F4 ≫ F5 ≫ F6 ≫ F7)
    (nX : X ≫ F1 = F1' ≫ X')
    (nY1 : F7 ≫ Y = Y₁ ≫ F7')
    (nY2 : F6 ≫ Y₁ = Y₂ ≫ F6')
    (nY3 : F5 ≫ Y₂ = Y₃ ≫ F5')
    (hfold : X' ≫ F2 ≫ F3 ≫ F4 ≫ Y₃ = Z) :
    X ≫ c₁ ≫ c₂ ≫ c₃ ≫ w = F1' ≫ Z ≫ F5' ≫ F6' ≫ F7' := by
  rw [hw]
  calc X ≫ c₁ ≫ c₂ ≫ c₃ ≫ c₄ ≫ Y
      = X ≫ (c₁ ≫ c₂ ≫ c₃ ≫ c₄) ≫ Y := by simp only [Category.assoc]
    _ = X ≫ (F1 ≫ F2 ≫ F3 ≫ F4 ≫ F5 ≫ F6 ≫ F7) ≫ Y := by rw [hcast]
    _ = X ≫ F1 ≫ F2 ≫ F3 ≫ F4 ≫ F5 ≫ F6 ≫ F7 ≫ Y := by simp only [Category.assoc]
    _ = F1' ≫ X' ≫ F2 ≫ F3 ≫ F4 ≫ F5 ≫ F6 ≫ Y₁ ≫ F7' := by
        rw [reassoc_of% nX, nY1]
    _ = F1' ≫ X' ≫ F2 ≫ F3 ≫ F4 ≫ F5 ≫ Y₂ ≫ F6' ≫ F7' := by rw [reassoc_of% nY2]
    _ = F1' ≫ X' ≫ F2 ≫ F3 ≫ F4 ≫ Y₃ ≫ F5' ≫ F6' ≫ F7' := by rw [reassoc_of% nY3]
    _ = F1' ≫ (X' ≫ F2 ≫ F3 ≫ F4 ≫ Y₃) ≫ F5' ≫ F6' ≫ F7' := by
        simp only [Category.assoc]
    _ = F1' ≫ Z ≫ F5' ≫ F6' ≫ F7' := by rw [hfold]

/-- **Generic right-side assembly for the conjugated cocycle**: like
`side_collapse_left`, with three extra moves — the front comparison splits off a
source-bridge congruence (`hc₁`), the pair congruence inside the last factor commutes
out (`hex`), the three middle congruences merge (`hstack`) — and a trailing transition
factor `d₄` riding along. Pure rebracketing in an abstract category. Project-local. -/
private lemma side_collapse_right {𝒞 : Type*} [Category 𝒞]
    {x₀ x₁ s₁ s₂ y₁ y₂ y₃ z₁ z₂ z₃ y₆ e₁ a₁ a₂ a₃ a₄ a₅ a₆ b₀ b₁ m₁ m₂ m₃ : 𝒞}
    {X : x₀ ⟶ x₁} {c₁ : x₁ ⟶ y₁} {c₂ : y₁ ⟶ y₂} {c₃ : y₂ ⟶ y₃} {w : y₃ ⟶ y₆}
    {d₁ : y₃ ⟶ z₁} {d₂ : z₁ ⟶ z₂} {d₃ : z₂ ⟶ z₃} {d₄ : z₃ ⟶ y₆}
    {Cs : x₁ ⟶ s₁} {c₁' : s₁ ⟶ s₂} {ce₁ : s₂ ⟶ y₁} {ce₂ : y₂ ⟶ e₁} {c₃' : e₁ ⟶ z₁}
    {ctq : s₂ ⟶ e₁}
    {G1 : s₁ ⟶ a₁} {G2 : a₁ ⟶ a₂} {G3 : a₂ ⟶ a₃} {G4 : a₃ ⟶ a₄} {G5 : a₄ ⟶ a₅}
    {G6 : a₅ ⟶ a₆} {G7 : a₆ ⟶ z₂}
    {Cs' : x₀ ⟶ b₀} {X₁ : b₀ ⟶ s₁} {G1' : b₀ ⟶ b₁} {X₂ : b₁ ⟶ a₁}
    {Y₁ : a₆ ⟶ m₁} {G7' : m₁ ⟶ z₃} {Y₂ : a₅ ⟶ m₂} {G6' : m₂ ⟶ m₁}
    {Y₃ : a₄ ⟶ m₃} {G5' : m₃ ⟶ m₂} {Z : b₁ ⟶ m₃}
    (hw : w = d₁ ≫ d₂ ≫ d₃ ≫ d₄)
    (hc₁ : c₁ = Cs ≫ c₁' ≫ ce₁)
    (hex : c₃ ≫ d₁ = ce₂ ≫ c₃')
    (hstack : ∀ {Z'} (zc : e₁ ⟶ Z'), ce₁ ≫ c₂ ≫ ce₂ ≫ zc = ctq ≫ zc)
    (hcast : c₁' ≫ ctq ≫ c₃' ≫ d₂ = G1 ≫ G2 ≫ G3 ≫ G4 ≫ G5 ≫ G6 ≫ G7)
    (nXpre : X ≫ Cs = Cs' ≫ X₁)
    (nX : X₁ ≫ G1 = G1' ≫ X₂)
    (nY1 : G7 ≫ d₃ = Y₁ ≫ G7')
    (nY2 : G6 ≫ Y₁ = Y₂ ≫ G6')
    (nY3 : G5 ≫ Y₂ = Y₃ ≫ G5')
    (hfold : X₂ ≫ G2 ≫ G3 ≫ G4 ≫ Y₃ = Z) :
    X ≫ c₁ ≫ c₂ ≫ c₃ ≫ w = Cs' ≫ G1' ≫ Z ≫ G5' ≫ G6' ≫ G7' ≫ d₄ := by
  rw [hw, hc₁]
  calc X ≫ (Cs ≫ c₁' ≫ ce₁) ≫ c₂ ≫ c₃ ≫ d₁ ≫ d₂ ≫ d₃ ≫ d₄
      = X ≫ Cs ≫ c₁' ≫ ce₁ ≫ c₂ ≫ (c₃ ≫ d₁) ≫ d₂ ≫ d₃ ≫ d₄ := by
        simp only [Category.assoc]
    _ = X ≫ Cs ≫ c₁' ≫ ce₁ ≫ c₂ ≫ (ce₂ ≫ c₃') ≫ d₂ ≫ d₃ ≫ d₄ := by rw [hex]
    _ = Cs' ≫ X₁ ≫ c₁' ≫ ce₁ ≫ c₂ ≫ ce₂ ≫ c₃' ≫ d₂ ≫ d₃ ≫ d₄ := by
        rw [reassoc_of% nXpre]; simp only [Category.assoc]
    _ = Cs' ≫ X₁ ≫ c₁' ≫ ctq ≫ c₃' ≫ d₂ ≫ d₃ ≫ d₄ := by rw [hstack]
    _ = Cs' ≫ X₁ ≫ (c₁' ≫ ctq ≫ c₃' ≫ d₂) ≫ d₃ ≫ d₄ := by simp only [Category.assoc]
    _ = Cs' ≫ X₁ ≫ (G1 ≫ G2 ≫ G3 ≫ G4 ≫ G5 ≫ G6 ≫ G7) ≫ d₃ ≫ d₄ := by rw [hcast]
    _ = Cs' ≫ X₁ ≫ G1 ≫ G2 ≫ G3 ≫ G4 ≫ G5 ≫ G6 ≫ G7 ≫ d₃ ≫ d₄ := by
        simp only [Category.assoc]
    _ = Cs' ≫ G1' ≫ X₂ ≫ G2 ≫ G3 ≫ G4 ≫ G5 ≫ G6 ≫ Y₁ ≫ G7' ≫ d₄ := by
        rw [reassoc_of% nX, reassoc_of% nY1]
    _ = Cs' ≫ G1' ≫ X₂ ≫ G2 ≫ G3 ≫ G4 ≫ G5 ≫ Y₂ ≫ G6' ≫ G7' ≫ d₄ := by
        rw [reassoc_of% nY2]
    _ = Cs' ≫ G1' ≫ X₂ ≫ G2 ≫ G3 ≫ G4 ≫ Y₃ ≫ G5' ≫ G6' ≫ G7' ≫ d₄ := by
        rw [reassoc_of% nY3]
    _ = Cs' ≫ G1' ≫ (X₂ ≫ G2 ≫ G3 ≫ G4 ≫ Y₃) ≫ G5' ≫ G6' ≫ G7' ≫ d₄ := by
        simp only [Category.assoc]
    _ = Cs' ≫ G1' ≫ Z ≫ G5' ≫ G6' ≫ G7' ≫ d₄ := by rw [hfold]

/-- **Generic final cancellation for the conjugated cocycle**: from the (flattened)
cocycle equation `h` whose left side carries three extra invertible factors
`a ≫ b ≫ c`, solve for the five-factor prefix against the right side decorated with
the three inverses. Pure rebracketing in an abstract category. Project-local. -/
private lemma final_cancel {𝒞 : Type*} [Category 𝒞]
    {x₀ l₁ l₂ l₃ l₄ l₅ e₁ e₂ e₃ r₁ r₂ r₃ : 𝒞}
    {L₁ : x₀ ⟶ l₁} {L₂ : l₁ ⟶ l₂} {L₃ : l₂ ⟶ l₃} {L₄ : l₃ ⟶ l₄} {L₅ : l₄ ⟶ l₅}
    {a : l₅ ⟶ e₁} {b : e₁ ⟶ e₂} {c : e₂ ⟶ e₃}
    {R₁ : x₀ ⟶ r₁} {R₂ : r₁ ⟶ r₂} {R₃ : r₂ ⟶ r₃} {R₄ : r₃ ⟶ e₃}
    {c' : e₃ ⟶ e₂} {b' : e₂ ⟶ e₁} {a' : e₁ ⟶ l₅}
    (h : L₁ ≫ L₂ ≫ L₃ ≫ L₄ ≫ L₅ ≫ a ≫ b ≫ c = R₁ ≫ R₂ ≫ R₃ ≫ R₄)
    (hcc : c ≫ c' = 𝟙 e₂) (hbb : b ≫ b' = 𝟙 e₁) (haa : a ≫ a' = 𝟙 l₅) :
    L₁ ≫ L₂ ≫ L₃ ≫ L₄ ≫ L₅ = R₁ ≫ R₂ ≫ R₃ ≫ R₄ ≫ c' ≫ b' ≫ a' := by
  rw [← reassoc_of% h, reassoc_of% hcc, reassoc_of% hbb, haa, Category.comp_id]

end CastCoherence

/-! ### The candidate inverse of the chart restriction morphism

The inverse `σ_i : M i ⟶ ι_i^* (glue …)` is assembled as an equalizer lift: the chart
pullback preserves the descent equalizer (`glueRestrictEqualizerIso`) and the
pushforward product (`glueRestrictProdIso`), so a map into `ι_i^* (glue …)` is a
family of maps into the factors `ι_i^* ((ι_j)_* M_j)` equalizing the restricted legs.
The `j`-th component (`glueChartComponent`) transports a section of `M i` to the
overlap: the unit along `f_ij`, the transition isomorphism `g_ij`, then the inverse of
the overlap base change `β_ij` (`glueOverlapBaseChangeIso`, in pullback form
`glueOverlapFactorIso`). The three named obligations consuming the cocycle hypotheses
are `glueChartFamily_equalizes` (C2 transported), `glueChartComponent_self_counit`
(C1 + the counit triangle), and `glueRestrictionHom_glueChartComponent` (the
pair-`(i,j)` equalizer condition transposed). -/

section GlueRestrictionInverse

variable (D : Scheme.GlueData.{0}) (M : ∀ i, (D.U i).Modules)

/-- **Object-level overlap base change in pullback form**: the `β_ij` of
`glueOverlapBaseChangeIso`, evaluated at `M j` and conjugated through
`restrictFunctorIsoPullback` on both sides, identifying
`ι_i^* ((ι_j)_* M_j) ≅ (f_ij)_* ((t_ij ≫ f_ji)^* M_j)` with the geometric pullback
functors. Project-local. -/
noncomputable def glueOverlapFactorIso (i j : D.J) :
    (Scheme.Modules.pullback (D.ι i)).obj ((Scheme.Modules.pushforward (D.ι j)).obj (M j))
      ≅ (Scheme.Modules.pushforward (D.f i j)).obj
          ((Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j)) :=
  (restrictFunctorIsoPullback (D.ι i)).symm.app
      ((Scheme.Modules.pushforward (D.ι j)).obj (M j)) ≪≫
    (glueOverlapBaseChangeIso D i j).app (M j) ≪≫
    (Scheme.Modules.pushforward (D.f i j)).mapIso
      ((restrictFunctorIsoPullback (D.t i j ≫ D.f j i)).app (M j))

variable (g : ∀ i j, (Scheme.Modules.pullback (D.f i j)).obj (M i) ≅
      (Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j))

/-- **The `j`-th component of the candidate inverse** `σ_i`: transport a section of
`M i` to the overlap `V_ij` (the unit of the pullback–pushforward adjunction along
`f_ij`), across the transition isomorphism `g_ij`, and back up through the inverse of
the overlap base change `β_ij`. Project-local. -/
noncomputable def glueChartComponent (i j : D.J) :
    M i ⟶ (Scheme.Modules.pullback (D.ι i)).obj
      ((Scheme.Modules.pushforward (D.ι j)).obj (M j)) :=
  (Scheme.Modules.pullbackPushforwardAdjunction (D.f i j)).unit.app (M i) ≫
    (Scheme.Modules.pushforward (D.f i j)).map (g i j).hom ≫
    (glueOverlapFactorIso D M i j).inv

/-- **The candidate-inverse family into the restricted pushforward product**: the
`glueChartComponent`s assembled through the product-preservation comparison
`glueRestrictProdIso`. Project-local. -/
noncomputable def glueChartFamily (i : D.J) :
    M i ⟶ (Scheme.Modules.pullback (D.ι i)).obj (glueProd D M) :=
  Pi.lift (glueChartComponent D M g i) ≫ (glueRestrictProdIso D M i).inv

/-- **Transpose of the second descent-leg factor** along the composite overlap
immersion `f_pq ≫ ι_p`: the `bComp`-factor of `glueLegB` (unit along `t_pq ≫ f_qp`,
`pushforwardComp`, pushforward of `g_pq⁻¹`, `pushforwardCongr`) transposes to the
pseudofunctor casts, the pullback of the geometric counit, and `g_pq⁻¹`. Companion of
`glueLegA_component_transpose`, via `homEquiv_comp_pushforwardCongr` and the
transpose naturality in the right argument. Project-local. -/
lemma glueLegB_component_transpose (p q : D.J) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (D.f p q ≫ D.ι p)).homEquiv
        ((Scheme.Modules.pushforward (D.ι q)).obj (M q))
        ((Scheme.Modules.pullback (D.f p q)).obj (M p))).symm
        ((Scheme.Modules.pushforward (D.ι q)).map
            ((Scheme.Modules.pullbackPushforwardAdjunction
              (D.t p q ≫ D.f q p)).unit.app (M q)) ≫
          (Scheme.Modules.pushforwardComp (D.t p q ≫ D.f q p) (D.ι q)).hom.app
            ((Scheme.Modules.pullback (D.t p q ≫ D.f q p)).obj (M q)) ≫
          (Scheme.Modules.pushforward
            ((D.t p q ≫ D.f q p) ≫ D.ι q)).map (g p q).inv ≫
          (Scheme.Modules.pushforwardCongr
            (show (D.t p q ≫ D.f q p) ≫ D.ι q = D.f p q ≫ D.ι p by
              rw [Category.assoc]; exact D.glue_condition p q)).hom.app
            ((Scheme.Modules.pullback (D.f p q)).obj (M p)))
      = (Scheme.Modules.pullbackCongr
            (show (D.t p q ≫ D.f q p) ≫ D.ι q = D.f p q ≫ D.ι p by
              rw [Category.assoc]; exact D.glue_condition p q)).inv.app
          ((Scheme.Modules.pushforward (D.ι q)).obj (M q)) ≫
        (Scheme.Modules.pullbackComp (D.t p q ≫ D.f q p) (D.ι q)).inv.app
          ((Scheme.Modules.pushforward (D.ι q)).obj (M q)) ≫
        ((Scheme.Modules.pullback (D.t p q ≫ D.f q p)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (D.ι q)).counit.app (M q)) ≫
          (g p q).inv) := by
  rw [Equiv.symm_apply_eq]
  have hpq : (D.t p q ≫ D.f q p) ≫ D.ι q = D.f p q ≫ D.ι p := by
    rw [Category.assoc]; exact D.glue_condition p q
  -- transpose of the unit pair at `(t_pq ≫ f_qp, ι_q)`: the counit trick of
  -- `glueLegA_component_transpose`
  have hε : (Scheme.Modules.pullbackPushforwardAdjunction (D.ι q)).homEquiv
        ((Scheme.Modules.pushforward (D.ι q)).obj (M q)) (M q)
        ((Scheme.Modules.pullbackPushforwardAdjunction (D.ι q)).counit.app (M q))
      = 𝟙 ((Scheme.Modules.pushforward (D.ι q)).obj (M q)) :=
    (Adjunction.homEquiv_unit _ _ _ _).trans
      ((Scheme.Modules.pullbackPushforwardAdjunction (D.ι q)).right_triangle_components
        (M q))
  have h1 := homEquiv_comp_unit_pushforwardComp (D.t p q ≫ D.f q p) (D.ι q)
    ((Scheme.Modules.pullbackPushforwardAdjunction (D.ι q)).counit.app (M q))
  -- `rw [hε] at h1` cannot match (the counit codomain carries a `𝟭`-wrapper); term-mode
  replace h1 := (Category.id_comp _).symm.trans ((eq_whisker hε _).symm.trans h1)
  -- re-index along the glue condition
  have h2 := homEquiv_comp_pushforwardCongr hpq
    (W := (Scheme.Modules.pushforward (D.ι q)).obj (M q))
    (y := (Scheme.Modules.pullbackComp (D.t p q ≫ D.f q p) (D.ι q)).inv.app
        ((Scheme.Modules.pushforward (D.ι q)).obj (M q)) ≫
      ((Scheme.Modules.pullback (D.t p q ≫ D.f q p)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (D.ι q)).counit.app (M q)) ≫
        (g p q).inv))
  -- absorb `g⁻¹` into the transpose and fold the unit pair
  have hy : (Scheme.Modules.pullbackPushforwardAdjunction
        ((D.t p q ≫ D.f q p) ≫ D.ι q)).homEquiv
        ((Scheme.Modules.pushforward (D.ι q)).obj (M q))
        ((Scheme.Modules.pullback (D.f p q)).obj (M p))
        ((Scheme.Modules.pullbackComp (D.t p q ≫ D.f q p) (D.ι q)).inv.app
            ((Scheme.Modules.pushforward (D.ι q)).obj (M q)) ≫
          ((Scheme.Modules.pullback (D.t p q ≫ D.f q p)).map
            ((Scheme.Modules.pullbackPushforwardAdjunction (D.ι q)).counit.app (M q)) ≫
            (g p q).inv))
      = ((Scheme.Modules.pushforward (D.ι q)).map
            ((Scheme.Modules.pullbackPushforwardAdjunction
              (D.t p q ≫ D.f q p)).unit.app (M q)) ≫
          (Scheme.Modules.pushforwardComp (D.t p q ≫ D.f q p) (D.ι q)).hom.app
            ((Scheme.Modules.pullback (D.t p q ≫ D.f q p)).obj (M q))) ≫
        (Scheme.Modules.pushforward ((D.t p q ≫ D.f q p) ≫ D.ι q)).map (g p q).inv :=
    (congrArg ((Scheme.Modules.pullbackPushforwardAdjunction
        ((D.t p q ≫ D.f q p) ≫ D.ι q)).homEquiv _ _)
        (Category.assoc _ _ _).symm).trans
      ((Adjunction.homEquiv_naturality_right _ _ _).trans (eq_whisker h1.symm _))
  refine Eq.trans ?_ h2
  refine Eq.trans (((Category.assoc _ _ _).trans (Category.assoc _ _ _)).symm) ?_
  exact eq_whisker hy.symm _

/-- **Transpose of the overlap base change** (mate core): the adjoint transpose along
`ι_i` of the pullback-form overlap base change `(glueOverlapFactorIso D M i j).hom` is
the canonical four-functor comparison of the glue square — the unit along
`t_ij ≫ f_ji` pushed forward along `ι_j`, regrouped by `pushforwardComp`, re-indexed
by `pushforwardCongr` along the glue condition, and ungrouped by `pushforwardComp⁻¹`.
Cocycle-free: this is pure site-level content (every factor is concrete on sections
after the unit/counit bridges). Project-local. -/
lemma glueOverlapFactor_transpose (i j : D.J) :
    (Scheme.Modules.pushforward (D.ι j)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (D.t i j ≫ D.f j i)).unit.app
          (M j)) ≫
      (Scheme.Modules.pushforwardComp (D.t i j ≫ D.f j i) (D.ι j)).hom.app
        ((Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j)) ≫
      (Scheme.Modules.pushforwardCongr
          (show (D.t i j ≫ D.f j i) ≫ D.ι j = D.f i j ≫ D.ι i by
            rw [Category.assoc]; exact D.glue_condition i j)).hom.app
        ((Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j)) ≫
      (Scheme.Modules.pushforwardComp (D.f i j) (D.ι i)).inv.app
        ((Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j))
    = (Scheme.Modules.pullbackPushforwardAdjunction (D.ι i)).homEquiv
        ((Scheme.Modules.pushforward (D.ι j)).obj (M j))
        ((Scheme.Modules.pushforward (D.f i j)).obj
          ((Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j)))
        ((glueOverlapFactorIso D M i j).hom) := by
  have hglue : (D.t i j ≫ D.f j i) ≫ D.ι j = D.f i j ≫ D.ι i := by
    rw [Category.assoc]; exact D.glue_condition i j
  -- RHS: expand the transpose in unit form; the `leftAdjointUniq` conjugation of the
  -- chart comparison cancels against the unit bridge, leaving the site-level `β`
  have hRHS : (Scheme.Modules.pullbackPushforwardAdjunction (D.ι i)).homEquiv
        ((Scheme.Modules.pushforward (D.ι j)).obj (M j))
        ((Scheme.Modules.pushforward (D.f i j)).obj
          ((Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j)))
        ((glueOverlapFactorIso D M i j).hom)
      = (restrictAdjunction (D.ι i)).unit.app
          ((Scheme.Modules.pushforward (D.ι j)).obj (M j)) ≫
        (Scheme.Modules.pushforward (D.ι i)).map
          ((glueOverlapBaseChangeIso D i j).hom.app (M j)) ≫
        (Scheme.Modules.pushforward (D.ι i)).map
          ((Scheme.Modules.pushforward (D.f i j)).map
            ((restrictFunctorIsoPullback (D.t i j ≫ D.f j i)).hom.app (M j))) := by
    refine (Adjunction.homEquiv_unit _ _ _ _).trans ?_
    refine Eq.trans (eq_whisker
      (restrictAdjunction_unit_app_iso (D.ι i)
        ((Scheme.Modules.pushforward (D.ι j)).obj (M j))).symm _) ?_
    refine (Category.assoc _ _ _).trans (whisker_eq _ ?_)
    refine ((Scheme.Modules.pushforward (D.ι i)).map_comp _ _).symm.trans ?_
    refine Eq.trans (congrArg (Scheme.Modules.pushforward (D.ι i)).map ?_)
      ((Scheme.Modules.pushforward (D.ι i)).map_comp _ _)
    exact Iso.hom_inv_id_app_assoc (restrictFunctorIsoPullback (D.ι i)) _ _
  rw [hRHS]
  -- LHS: bridge the geometric unit at `t_ij ≫ f_ji` to the site-level unit; the
  -- emerging `restrictFunctorIsoPullback` factor migrates across the three casts by
  -- naturality (`n₁`–`n₃`), matching the tail of the right-hand side
  have h_a : (Scheme.Modules.pushforward (D.ι j)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (D.t i j ≫ D.f j i)).unit.app
          (M j))
      = (Scheme.Modules.pushforward (D.ι j)).map
          ((restrictAdjunction (D.t i j ≫ D.f j i)).unit.app (M j)) ≫
        (Scheme.Modules.pushforward (D.ι j)).map
          ((Scheme.Modules.pushforward (D.t i j ≫ D.f j i)).map
            ((restrictFunctorIsoPullback (D.t i j ≫ D.f j i)).hom.app (M j))) :=
    (congrArg (Scheme.Modules.pushforward (D.ι j)).map
        (restrictAdjunction_unit_app_iso (D.t i j ≫ D.f j i) (M j)).symm).trans
      ((Scheme.Modules.pushforward (D.ι j)).map_comp _ _)
  have n₁ := (Scheme.Modules.pushforwardComp (D.t i j ≫ D.f j i) (D.ι j)).hom.naturality
    ((restrictFunctorIsoPullback (D.t i j ≫ D.f j i)).hom.app (M j))
  have n₂ := (Scheme.Modules.pushforwardCongr hglue).hom.naturality
    ((restrictFunctorIsoPullback (D.t i j ≫ D.f j i)).hom.app (M j))
  have n₃ := (Scheme.Modules.pushforwardComp (D.f i j) (D.ι i)).inv.naturality
    ((restrictFunctorIsoPullback (D.t i j ≫ D.f j i)).hom.app (M j))
  -- the site-level core: all four factors are concrete on sections; both sides are a
  -- single presheaf restriction along the overlap opens identity
  -- (`glueData_preimage_image_eq`), folded by proof irrelevance as in the closing step
  -- of `glueChartComponent_self_counit`.
  have hcore : (Scheme.Modules.pushforward (D.ι j)).map
        ((restrictAdjunction (D.t i j ≫ D.f j i)).unit.app (M j)) ≫
      (Scheme.Modules.pushforwardComp (D.t i j ≫ D.f j i) (D.ι j)).hom.app
        ((restrictFunctor (D.t i j ≫ D.f j i)).obj (M j)) ≫
      (Scheme.Modules.pushforwardCongr hglue).hom.app
        ((restrictFunctor (D.t i j ≫ D.f j i)).obj (M j)) ≫
      (Scheme.Modules.pushforwardComp (D.f i j) (D.ι i)).inv.app
        ((restrictFunctor (D.t i j ≫ D.f j i)).obj (M j))
      = (restrictAdjunction (D.ι i)).unit.app
          ((Scheme.Modules.pushforward (D.ι j)).obj (M j)) ≫
        (Scheme.Modules.pushforward (D.ι i)).map
          ((glueOverlapBaseChangeIso D i j).hom.app (M j)) := by
    ext O x
    -- every factor is a presheaf restriction of `M j` (the two `pushforwardComp`
    -- factors are identities); fold each side to a single restriction and use
    -- proof irrelevance of the opens morphisms
    have htot : (M j).presheaf.map
          (homOfLE ((D.t i j ≫ D.f j i).image_preimage_le ((D.ι j) ⁻¹ᵁ O))).op ≫
        (M j).presheaf.map ((D.t i j ≫ D.f j i).opensFunctor.map
          (eqToHom (show (D.f i j ≫ D.ι i) ⁻¹ᵁ O = ((D.t i j ≫ D.f j i) ≫ D.ι j) ⁻¹ᵁ O by
            rw [hglue]))).op
        = (M j).presheaf.map ((TopologicalSpace.Opens.map (D.ι j).base).map
            (homOfLE ((D.ι i).image_preimage_le O))).op ≫
          (M j).presheaf.map
            (eqToHom (glueData_preimage_image_eq D i j ((D.ι i) ⁻¹ᵁ O)).symm).op := by
      erw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (M j).presheaf.map (Subsingleton.elim _ _)
    exact congr($(htot) x)
  -- restate `h_a` with the composite-functor map (defeq) so `n₁` fires syntactically
  have h_a' : (Scheme.Modules.pushforward (D.ι j)).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (D.t i j ≫ D.f j i)).unit.app
          (M j))
      = (Scheme.Modules.pushforward (D.ι j)).map
          ((restrictAdjunction (D.t i j ≫ D.f j i)).unit.app (M j)) ≫
        (Scheme.Modules.pushforward (D.t i j ≫ D.f j i) ⋙
          Scheme.Modules.pushforward (D.ι j)).map
          ((restrictFunctorIsoPullback (D.t i j ≫ D.f j i)).hom.app (M j)) := h_a
  rw [h_a']
  -- inner chain: migrate the comparison factor through the three casts (`n₁`–`n₃`);
  -- pure term-mode (positional `simp [Category.assoc]` cannot match the comp nodes
  -- under the `X.Modules` instance diamond)
  have hmove : (Scheme.Modules.pushforward (D.t i j ≫ D.f j i) ⋙
        Scheme.Modules.pushforward (D.ι j)).map
        ((restrictFunctorIsoPullback (D.t i j ≫ D.f j i)).hom.app (M j)) ≫
      (Scheme.Modules.pushforwardComp (D.t i j ≫ D.f j i) (D.ι j)).hom.app
        ((Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j)) ≫
      (Scheme.Modules.pushforwardCongr hglue).hom.app
        ((Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j)) ≫
      (Scheme.Modules.pushforwardComp (D.f i j) (D.ι i)).inv.app
        ((Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j))
      = (Scheme.Modules.pushforwardComp (D.t i j ≫ D.f j i) (D.ι j)).hom.app
          ((restrictFunctor (D.t i j ≫ D.f j i)).obj (M j)) ≫
        (Scheme.Modules.pushforwardCongr hglue).hom.app
          ((restrictFunctor (D.t i j ≫ D.f j i)).obj (M j)) ≫
        (Scheme.Modules.pushforwardComp (D.f i j) (D.ι i)).inv.app
          ((restrictFunctor (D.t i j ≫ D.f j i)).obj (M j)) ≫
        (Scheme.Modules.pushforward (D.f i j) ⋙
          Scheme.Modules.pushforward (D.ι i)).map
          ((restrictFunctorIsoPullback (D.t i j ≫ D.f j i)).hom.app (M j)) :=
    (Category.assoc _ _ _).symm.trans ((eq_whisker n₁ _).trans
      ((Category.assoc _ _ _).trans (whisker_eq _
        ((Category.assoc _ _ _).symm.trans ((eq_whisker n₂ _).trans
          ((Category.assoc _ _ _).trans (whisker_eq _ n₃)))))))
  refine (Category.assoc _ _ _).trans ((whisker_eq _ hmove).trans ?_)
  refine ((whisker_eq _ ((whisker_eq _ (Category.assoc _ _ _).symm).trans
    (Category.assoc _ _ _).symm)).trans ?_)
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (eq_whisker hcore _).trans ?_
  exact Category.assoc _ _ _

/-- **Mate recognition for the chart-overlap square**: for any `W` on the glued scheme
and `m : W ⟶ (ι_j)_* (M j)`, transposing `m` along `ι_j`, pulling back to the overlap
along `t_ij ≫ f_ji`, and re-indexing through the pullback-pseudofunctor casts of the
glue square equals the transpose along `f_ij` of `ι_i^* m` composed with the overlap
base change in pullback form (`glueOverlapFactorIso`). Universal four-functor
compatibility; reduces by the conjugate calculus to the `m`-free mate core
`glueOverlapFactor_transpose`. Project-local. -/
lemma glueOverlapFactor_mate (i j : D.J) {W : D.glued.Modules}
    (m : W ⟶ (Scheme.Modules.pushforward (D.ι j)).obj (M j)) :
    (Scheme.Modules.pullbackComp (D.f i j) (D.ι i)).hom.app W ≫
      (Scheme.Modules.pullbackCongr
        (show (D.t i j ≫ D.f j i) ≫ D.ι j = D.f i j ≫ D.ι i by
          rw [Category.assoc]; exact D.glue_condition i j)).inv.app W ≫
      (Scheme.Modules.pullbackComp (D.t i j ≫ D.f j i) (D.ι j)).inv.app W ≫
      (Scheme.Modules.pullback (D.t i j ≫ D.f j i)).map
        (((Scheme.Modules.pullbackPushforwardAdjunction (D.ι j)).homEquiv W (M j)).symm m)
    = ((Scheme.Modules.pullbackPushforwardAdjunction (D.f i j)).homEquiv
          ((Scheme.Modules.pullback (D.ι i)).obj W)
          ((Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j))).symm
        ((Scheme.Modules.pullback (D.ι i)).map m ≫ (glueOverlapFactorIso D M i j).hom) := by
  have hglue : (D.t i j ≫ D.f j i) ≫ D.ι j = D.f i j ≫ D.ι i := by
    rw [Category.assoc]; exact D.glue_condition i j
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (D.f i j)).homEquiv
    ((Scheme.Modules.pullback (D.ι i)).obj W)
    ((Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j))).injective
  refine Eq.trans ?_ (Equiv.apply_symm_apply _ _).symm
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (D.ι i)).homEquiv _ _).injective
  -- right-hand side: peel `m` off by naturality of the transpose
  have hR : (Scheme.Modules.pullbackPushforwardAdjunction (D.ι i)).homEquiv _ _
        ((Scheme.Modules.pullback (D.ι i)).map m ≫ (glueOverlapFactorIso D M i j).hom)
      = m ≫ (Scheme.Modules.pullbackPushforwardAdjunction (D.ι i)).homEquiv _ _
          ((glueOverlapFactorIso D M i j).hom) :=
    Adjunction.homEquiv_naturality_left _ _ _
  -- the conjugate of `pullbackComp.hom` is `pushforwardComp.inv`
  have hcomm := CategoryTheory.conjugateEquiv_comm
    (adj₁ := (Scheme.Modules.pullbackPushforwardAdjunction (D.ι i)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (D.f i j)))
    (adj₂ := Scheme.Modules.pullbackPushforwardAdjunction (D.f i j ≫ D.ι i))
    (show (Scheme.Modules.pullbackComp (D.f i j) (D.ι i)).hom ≫
        (Scheme.Modules.pullbackComp (D.f i j) (D.ι i)).inv = 𝟙 _
      from (Scheme.Modules.pullbackComp (D.f i j) (D.ι i)).hom_inv_id)
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at hcomm
  have hConj : CategoryTheory.conjugateEquiv
        (Scheme.Modules.pullbackPushforwardAdjunction (D.f i j ≫ D.ι i))
        ((Scheme.Modules.pullbackPushforwardAdjunction (D.ι i)).comp
          (Scheme.Modules.pullbackPushforwardAdjunction (D.f i j)))
        (Scheme.Modules.pullbackComp (D.f i j) (D.ι i)).hom
      = (Scheme.Modules.pushforwardComp (D.f i j) (D.ι i)).inv :=
    (CategoryTheory.Iso.hom_comp_eq_id _).mp hcomm
  -- transpose of the inner chain along `(t_ij ≫ f_ji) ≫ ι_j`: fold the unit pair
  have h1 : (Scheme.Modules.pullbackPushforwardAdjunction
        ((D.t i j ≫ D.f j i) ≫ D.ι j)).homEquiv W
        ((Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j))
        ((Scheme.Modules.pullbackComp (D.t i j ≫ D.f j i) (D.ι j)).inv.app W ≫
          (Scheme.Modules.pullback (D.t i j ≫ D.f j i)).map
            (((Scheme.Modules.pullbackPushforwardAdjunction (D.ι j)).homEquiv
              W (M j)).symm m))
      = m ≫ ((Scheme.Modules.pushforward (D.ι j)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction
            (D.t i j ≫ D.f j i)).unit.app (M j)) ≫
        (Scheme.Modules.pushforwardComp (D.t i j ≫ D.f j i) (D.ι j)).hom.app
          ((Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j))) := by
    have h := homEquiv_comp_unit_pushforwardComp (D.t i j ≫ D.f j i) (D.ι j)
      (((Scheme.Modules.pullbackPushforwardAdjunction (D.ι j)).homEquiv W (M j)).symm m)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  -- re-index along the glue condition
  have h2 := homEquiv_comp_pushforwardCongr hglue
    (W := W)
    (y := (Scheme.Modules.pullbackComp (D.t i j ≫ D.f j i) (D.ι j)).inv.app W ≫
      (Scheme.Modules.pullback (D.t i j ≫ D.f j i)).map
        (((Scheme.Modules.pullbackPushforwardAdjunction (D.ι j)).homEquiv W (M j)).symm m))
  -- the double transpose of the full cast chain
  have hstar := homEquiv_conjugateEquiv_app
    (Scheme.Modules.pullbackPushforwardAdjunction (D.f i j ≫ D.ι i))
    ((Scheme.Modules.pullbackPushforwardAdjunction (D.ι i)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (D.f i j)))
    (Scheme.Modules.pullbackComp (D.f i j) (D.ι i)).hom
    (f := (Scheme.Modules.pullbackCongr hglue).inv.app W ≫
      (Scheme.Modules.pullbackComp (D.t i j ≫ D.f j i) (D.ι j)).inv.app W ≫
      (Scheme.Modules.pullback (D.t i j ≫ D.f j i)).map
        (((Scheme.Modules.pullbackPushforwardAdjunction (D.ι j)).homEquiv W (M j)).symm m))
  rw [hConj] at hstar
  -- assemble: LHS double transpose = m ≫ (four-functor comparison) = m ≫ transpose β = RHS
  refine Eq.trans ?_ hR.symm
  refine Eq.trans (?_ : _ = ((Scheme.Modules.pullbackPushforwardAdjunction
      (D.f i j ≫ D.ι i)).homEquiv W _
      ((Scheme.Modules.pullbackCongr hglue).inv.app W ≫
        (Scheme.Modules.pullbackComp (D.t i j ≫ D.f j i) (D.ι j)).inv.app W ≫
        (Scheme.Modules.pullback (D.t i j ≫ D.f j i)).map
          (((Scheme.Modules.pullbackPushforwardAdjunction (D.ι j)).homEquiv
            W (M j)).symm m)) ≫
      (Scheme.Modules.pushforwardComp (D.f i j) (D.ι i)).inv.app
        ((Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j)))) ?_
  · -- the composite-adjunction transpose computes the nested transposes
    refine Eq.trans ?_ hstar
    rw [Adjunction.comp_homEquiv]
    rfl
  · -- substitute `h2`, then `h1`, regroup, and finish with the mate core
    rw [← h2]
    exact (eq_whisker (eq_whisker h1 _) _).trans
      ((eq_whisker (Category.assoc _ _ _) _).trans
        ((Category.assoc _ _ _).trans (whisker_eq m
          ((eq_whisker (Category.assoc _ _ _) _).trans
            ((Category.assoc _ _ _).trans ((whisker_eq _ (Category.assoc _ _ _)).trans
              (glueOverlapFactor_transpose D M i j)))))))

/-- **Pair-overlap collapse of the chart component** (the triangle step of the
conjugated cocycle): the chart pullback `f_ij^*` of the `j`-th candidate-inverse
component, fed through the pair cast chain of the glue square and the pulled-back
counit at `ι_j`, collapses to the transition isomorphism `g_ij`. The mate
`glueOverlapFactor_mate` at the identity identifies the cast chain with the transpose
of `γ_ij`, which cancels `γ_ij⁻¹` inside the component; the remaining unit/counit pair
at `f_ij` cancels by the left triangle identity. Project-local. -/
lemma glueChartComponent_overlap_collapse (i j : D.J) :
    (Scheme.Modules.pullback (D.f i j)).map (glueChartComponent D M g i j) ≫
        (Scheme.Modules.pullbackComp (D.f i j) (D.ι i)).hom.app
          ((Scheme.Modules.pushforward (D.ι j)).obj (M j)) ≫
        (Scheme.Modules.pullbackCongr
          (show (D.t i j ≫ D.f j i) ≫ D.ι j = D.f i j ≫ D.ι i by
            rw [Category.assoc]; exact D.glue_condition i j)).inv.app
          ((Scheme.Modules.pushforward (D.ι j)).obj (M j)) ≫
        (Scheme.Modules.pullbackComp (D.t i j ≫ D.f j i) (D.ι j)).inv.app
          ((Scheme.Modules.pushforward (D.ι j)).obj (M j)) ≫
        (Scheme.Modules.pullback (D.t i j ≫ D.f j i)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (D.ι j)).counit.app (M j))
      = (g i j).hom := by
  -- transpose of the identity is the counit
  have hid : ((Scheme.Modules.pullbackPushforwardAdjunction (D.ι j)).homEquiv
        ((Scheme.Modules.pushforward (D.ι j)).obj (M j)) (M j)).symm
        (𝟙 ((Scheme.Modules.pushforward (D.ι j)).obj (M j)))
      = (Scheme.Modules.pullbackPushforwardAdjunction (D.ι j)).counit.app (M j) :=
    (Adjunction.homEquiv_counit _ _ _ _).trans
      ((eq_whisker ((Scheme.Modules.pullback (D.ι j)).map_id _) _).trans
        (Category.id_comp _))
  -- the mate at the identity: the pair cast chain is the transpose of `γ_ij`
  have hmate := glueOverlapFactor_mate D M i j
    (m := 𝟙 ((Scheme.Modules.pushforward (D.ι j)).obj (M j)))
  -- absorb the pulled-back identity in front of `γ_ij`
  have hγ : (Scheme.Modules.pullback (D.ι i)).map
        (𝟙 ((Scheme.Modules.pushforward (D.ι j)).obj (M j))) ≫
        (glueOverlapFactorIso D M i j).hom
      = (glueOverlapFactorIso D M i j).hom :=
    (eq_whisker ((Scheme.Modules.pullback (D.ι i)).map_id _) _).trans (Category.id_comp _)
  -- the transpose of `γ_ij` in counit form
  have hγt : ((Scheme.Modules.pullbackPushforwardAdjunction (D.f i j)).homEquiv
        ((Scheme.Modules.pullback (D.ι i)).obj
          ((Scheme.Modules.pushforward (D.ι j)).obj (M j)))
        ((Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j))).symm
        ((glueOverlapFactorIso D M i j).hom)
      = (Scheme.Modules.pullback (D.f i j)).map ((glueOverlapFactorIso D M i j).hom) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction (D.f i j)).counit.app
          ((Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j)) :=
    Adjunction.homEquiv_counit _ _ _ _
  -- the cast chain with the counit decoration equals `f_ij^*(γ_ij) ≫ ε_{f_ij}`
  have hchain := ((whisker_eq
      ((Scheme.Modules.pullbackComp (D.f i j) (D.ι i)).hom.app
        ((Scheme.Modules.pushforward (D.ι j)).obj (M j)))
      (whisker_eq _ (whisker_eq _ (congrArg
        (Scheme.Modules.pullback (D.t i j ≫ D.f j i)).map hid.symm)))).trans
    hmate).trans
    ((congrArg ((Scheme.Modules.pullbackPushforwardAdjunction (D.f i j)).homEquiv _ _).symm
      hγ).trans hγt)
  -- the component composed with `γ_ij` is the bare unit/transition pair
  have hsγ : glueChartComponent D M g i j ≫ (glueOverlapFactorIso D M i j).hom
      = (Scheme.Modules.pullbackPushforwardAdjunction (D.f i j)).unit.app (M i) ≫
        (Scheme.Modules.pushforward (D.f i j)).map (g i j).hom := by
    dsimp only [glueChartComponent]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  -- gather `f_ij^*`, cancel `γ`, and finish with counit naturality + the left triangle
  have hAB : (Scheme.Modules.pullback (D.f i j)).map (glueChartComponent D M g i j) ≫
        (Scheme.Modules.pullback (D.f i j)).map ((glueOverlapFactorIso D M i j).hom)
      = (Scheme.Modules.pullback (D.f i j)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (D.f i j)).unit.app (M i)) ≫
        (Scheme.Modules.pullback (D.f i j)).map
          ((Scheme.Modules.pushforward (D.f i j)).map (g i j).hom) :=
    (((Scheme.Modules.pullback (D.f i j)).map_comp _ _).symm.trans
      (congrArg (Scheme.Modules.pullback (D.f i j)).map hsγ)).trans
      ((Scheme.Modules.pullback (D.f i j)).map_comp _ _)
  refine (whisker_eq _ hchain).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (eq_whisker hAB _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (whisker_eq _
    ((Scheme.Modules.pullbackPushforwardAdjunction (D.f i j)).counit.naturality
      (g i j).hom)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact (eq_whisker
      ((Scheme.Modules.pullbackPushforwardAdjunction (D.f i j)).left_triangle_components
        (M i)) _).trans
    (Category.id_comp _)

variable (hC1 : ∀ i, g i i = eqToIso (congrArg (fun φ => (Scheme.Modules.pullback φ).obj (M i))
      (show D.f i i = D.t i i ≫ D.f i i by rw [D.t_id i, Category.id_comp])))
  (hC2 : ∀ i j k,
      pullbackBaseChangeTransport (pullback.fst (D.f i j) (D.f i k))
          (D.f i j) (D.t i j ≫ D.f j i) (g i j) ≪≫
        (Scheme.Modules.pullbackCongr (glueData_bridge_mid D i j k)).app (M j) ≪≫
        pullbackBaseChangeTransport (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
          (D.f j k) (D.t j k ≫ D.f k j) (g j k) ≪≫
        (Scheme.Modules.pullbackCongr (glueData_bridge_tgt D i j k)).app (M k)
      = (Scheme.Modules.pullbackCongr (glueData_bridge_src D i j k)).app (M i) ≪≫
        pullbackBaseChangeTransport (pullback.snd (D.f i j) (D.f i k))
          (D.f i k) (D.t i k ≫ D.f k i) (g i k))

/-- The candidate-inverse family followed by the restricted `j`-th product projection
recovers the `j`-th component: the product-preservation comparison cancels against the
lift. Project-local. -/
@[reassoc]
lemma glueChartFamily_pullback_map_π (i j : D.J) :
    glueChartFamily D M g i ≫ (Scheme.Modules.pullback (D.ι i)).map
        (Pi.π (fun k => (Scheme.Modules.pushforward (D.ι k)).obj (M k)) j)
      = glueChartComponent D M g i j := by
  have hπ : (glueRestrictProdIso D M i).hom ≫ Pi.π _ j
      = (Scheme.Modules.pullback (D.ι i)).map
          (Pi.π (fun k => (Scheme.Modules.pushforward (D.ι k)).obj (M k)) j) :=
    piComparison_comp_π _ _ _
  rw [glueChartFamily, Category.assoc]
  -- cancel the preservation comparison term-mode (positional `rw [← hπ]` cannot match
  -- the comp node under the `X.Modules` instance diamond)
  exact (whisker_eq _ ((whisker_eq _ hπ.symm).trans (Iso.inv_hom_id_assoc _ _))).trans
    (Limits.Pi.lift_π _ _)

/-- **Left collapse of the conjugated cocycle** (the `(i,p)`-side): the chart pullback
of the `p`-th component, fed through the triple cast chain and the pulled-back counit,
collapses to the `(i,p)` base-change transport followed by the middle-bridge cast and
the ungrouping at `(τ, f_pq)`. Cast coherence (`pullback_cast_compat`) + counit
migration (naturality) + the pair collapse `glueChartComponent_overlap_collapse`,
assembled by the abstract-category rearrangement `side_collapse_left`. Project-local. -/
private lemma glueChart_legCompat_left (i p q : D.J) :
    (Scheme.Modules.pullback (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p)).map
        (glueChartComponent D M g i p) ≫
      (Scheme.Modules.pullbackComp (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p)
        (D.ι i)).hom.app ((Scheme.Modules.pushforward (D.ι p)).obj (M p)) ≫
      (Scheme.Modules.pullbackCongr (glueData_triple_square D i p q)).inv.app
        ((Scheme.Modules.pushforward (D.ι p)).obj (M p)) ≫
      (Scheme.Modules.pullbackComp (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))
        (D.f p q ≫ D.ι p)).inv.app ((Scheme.Modules.pushforward (D.ι p)).obj (M p)) ≫
      (Scheme.Modules.pullback (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).map
        ((Scheme.Modules.pullbackComp (D.f p q) (D.ι p)).inv.app
            ((Scheme.Modules.pushforward (D.ι p)).obj (M p)) ≫
          (Scheme.Modules.pullback (D.f p q)).map
            ((Scheme.Modules.pullbackPushforwardAdjunction (D.ι p)).counit.app (M p)))
      = (Scheme.Modules.pullbackComp (pullback.fst (D.f i p) (D.f i q))
            (D.f i p)).inv.app (M i) ≫
        (Scheme.Modules.pullback (pullback.fst (D.f i p) (D.f i q))).map (g i p).hom ≫
        (Scheme.Modules.pullbackComp (pullback.fst (D.f i p) (D.f i q))
          (D.t i p ≫ D.f p i)).hom.app (M p) ≫
        (Scheme.Modules.pullbackCongr (glueData_bridge_mid D i p q)).hom.app (M p) ≫
        (Scheme.Modules.pullbackComp (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))
          (D.f p q)).inv.app (M p) := by
  have hpairp : (D.t i p ≫ D.f p i) ≫ D.ι p = D.f i p ≫ D.ι i := by
    rw [Category.assoc]; exact D.glue_condition i p
  exact side_collapse_left
    ((Scheme.Modules.pullback
      (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).map_comp _ _)
    (pullback_cast_compat (pullback.fst (D.f i p) (D.f i q)) (D.f i p) (D.ι i)
      (D.t i p ≫ D.f p i) (D.ι p) (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))
      (D.f p q) hpairp (glueData_bridge_mid D i p q) (glueData_triple_square D i p q)
      ((Scheme.Modules.pushforward (D.ι p)).obj (M p)))
    ((Scheme.Modules.pullbackComp (pullback.fst (D.f i p) (D.f i q))
      (D.f i p)).inv.naturality (glueChartComponent D M g i p))
    (((Scheme.Modules.pullbackComp (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))
      (D.f p q)).inv.naturality
      ((Scheme.Modules.pullbackPushforwardAdjunction (D.ι p)).counit.app (M p))).symm)
    (((Scheme.Modules.pullbackCongr (glueData_bridge_mid D i p q)).hom.naturality
      ((Scheme.Modules.pullbackPushforwardAdjunction (D.ι p)).counit.app (M p))).symm)
    (((Scheme.Modules.pullbackComp (pullback.fst (D.f i p) (D.f i q))
      (D.t i p ≫ D.f p i)).hom.naturality
      ((Scheme.Modules.pullbackPushforwardAdjunction (D.ι p)).counit.app (M p))).symm)
    (map_fold₅ (Scheme.Modules.pullback (pullback.fst (D.f i p) (D.f i q)))
      (glueChartComponent_overlap_collapse D M g i p))

/-- **Right collapse of the conjugated cocycle** (the `(i,q)`-side, with `g_pq⁻¹`
riding along): the chart pullback of the `q`-th component through the triple cast
chain, the leg-B decorations and `g_pq⁻¹` collapses to the source-bridge cast, the
`(i,q)` base-change transport, the (inverted) target-bridge cast, the ungrouping at
`(τ, t_pq ≫ f_qp)`, and `τ^*(g_pq⁻¹)`. Same assembly as the left side plus the
source-bridge re-indexing, the pair-congruence exchange, and the congruence-stack
merge (`side_collapse_right`). Project-local. -/
private lemma glueChart_legCompat_right (i p q : D.J) :
    (Scheme.Modules.pullback (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p)).map
        (glueChartComponent D M g i q) ≫
      (Scheme.Modules.pullbackComp (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p)
        (D.ι i)).hom.app ((Scheme.Modules.pushforward (D.ι q)).obj (M q)) ≫
      (Scheme.Modules.pullbackCongr (glueData_triple_square D i p q)).inv.app
        ((Scheme.Modules.pushforward (D.ι q)).obj (M q)) ≫
      (Scheme.Modules.pullbackComp (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))
        (D.f p q ≫ D.ι p)).inv.app ((Scheme.Modules.pushforward (D.ι q)).obj (M q)) ≫
      (Scheme.Modules.pullback (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).map
        ((Scheme.Modules.pullbackCongr
            (show (D.t p q ≫ D.f q p) ≫ D.ι q = D.f p q ≫ D.ι p by
              rw [Category.assoc]; exact D.glue_condition p q)).inv.app
            ((Scheme.Modules.pushforward (D.ι q)).obj (M q)) ≫
          (Scheme.Modules.pullbackComp (D.t p q ≫ D.f q p) (D.ι q)).inv.app
            ((Scheme.Modules.pushforward (D.ι q)).obj (M q)) ≫
          (Scheme.Modules.pullback (D.t p q ≫ D.f q p)).map
            ((Scheme.Modules.pullbackPushforwardAdjunction (D.ι q)).counit.app (M q)) ≫
          (g p q).inv)
      = (Scheme.Modules.pullbackCongr (glueData_bridge_src D i p q)).hom.app (M i) ≫
        (Scheme.Modules.pullbackComp (pullback.snd (D.f i p) (D.f i q))
          (D.f i q)).inv.app (M i) ≫
        (Scheme.Modules.pullback (pullback.snd (D.f i p) (D.f i q))).map (g i q).hom ≫
        (Scheme.Modules.pullbackComp (pullback.snd (D.f i p) (D.f i q))
          (D.t i q ≫ D.f q i)).hom.app (M q) ≫
        (Scheme.Modules.pullbackCongr (glueData_bridge_tgt D i p q).symm).hom.app (M q) ≫
        (Scheme.Modules.pullbackComp (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))
          (D.t p q ≫ D.f q p)).inv.app (M q) ≫
        (Scheme.Modules.pullback
          (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).map (g p q).inv := by
  have hpairq : (D.t i q ≫ D.f q i) ≫ D.ι q = D.f i q ≫ D.ι i := by
    rw [Category.assoc]; exact D.glue_condition i q
  have hpq : (D.t p q ≫ D.f q p) ≫ D.ι q = D.f p q ≫ D.ι p := by
    rw [Category.assoc]; exact D.glue_condition p q
  have htq : (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i)) ≫
        ((D.t p q ≫ D.f q p) ≫ D.ι q)
      = (pullback.snd (D.f i p) (D.f i q) ≫ D.f i q) ≫ D.ι i := by
    rw [hpq, glueData_triple_square D i p q, glueData_bridge_src D i p q]
  -- the three middle congruence casts merge into the q-side triple cast
  have hstackQ : ∀ {W' : (Limits.pullback (D.f i p) (D.f i q)).Modules}
      (zc : (Scheme.Modules.pullback ((D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i)) ≫
          ((D.t p q ≫ D.f q p) ≫ D.ι q))).obj
        ((Scheme.Modules.pushforward (D.ι q)).obj (M q)) ⟶ W'),
      (Scheme.Modules.pullbackCongr
          (show (pullback.snd (D.f i p) (D.f i q) ≫ D.f i q) ≫ D.ι i
              = (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p) ≫ D.ι i by
            rw [glueData_bridge_src D i p q])).hom.app
        ((Scheme.Modules.pushforward (D.ι q)).obj (M q)) ≫
      (Scheme.Modules.pullbackCongr (glueData_triple_square D i p q)).inv.app
        ((Scheme.Modules.pushforward (D.ι q)).obj (M q)) ≫
      (Scheme.Modules.pullbackCongr
          (show (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i)) ≫
              ((D.t p q ≫ D.f q p) ≫ D.ι q)
              = (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i)) ≫ (D.f p q ≫ D.ι p) by
            rw [hpq])).inv.app
        ((Scheme.Modules.pushforward (D.ι q)).obj (M q)) ≫ zc
      = (Scheme.Modules.pullbackCongr htq).inv.app
          ((Scheme.Modules.pushforward (D.ι q)).obj (M q)) ≫ zc := by
    intro W' zc
    simp only [pullbackCongr_hom_app_eqToHom, pullbackCongr_inv_app_eqToHom,
      eqToHom_trans_assoc]
  exact side_collapse_right
    (((Scheme.Modules.pullback
        (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).map_comp _ _).trans
      (whisker_eq _ (((Scheme.Modules.pullback
          (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).map_comp _ _).trans
        (whisker_eq _ ((Scheme.Modules.pullback
          (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).map_comp _ _)))))
    (pullbackComp_hom_app_congr_fst (glueData_bridge_src D i p q) (D.ι i)
      ((Scheme.Modules.pushforward (D.ι q)).obj (M q)))
    (pullbackComp_inv_comp_map_congr_inv_app
      (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i)) hpq
      ((Scheme.Modules.pushforward (D.ι q)).obj (M q)))
    hstackQ
    (pullback_cast_compat (pullback.snd (D.f i p) (D.f i q)) (D.f i q) (D.ι i)
      (D.t i q ≫ D.f q i) (D.ι q) (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))
      (D.t p q ≫ D.f q p) hpairq (glueData_bridge_tgt D i p q).symm htq
      ((Scheme.Modules.pushforward (D.ι q)).obj (M q)))
    ((Scheme.Modules.pullbackCongr (glueData_bridge_src D i p q)).hom.naturality
      (glueChartComponent D M g i q))
    ((Scheme.Modules.pullbackComp (pullback.snd (D.f i p) (D.f i q))
      (D.f i q)).inv.naturality (glueChartComponent D M g i q))
    (((Scheme.Modules.pullbackComp (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))
      (D.t p q ≫ D.f q p)).inv.naturality
      ((Scheme.Modules.pullbackPushforwardAdjunction (D.ι q)).counit.app (M q))).symm)
    (((Scheme.Modules.pullbackCongr (glueData_bridge_tgt D i p q).symm).hom.naturality
      ((Scheme.Modules.pullbackPushforwardAdjunction (D.ι q)).counit.app (M q))).symm)
    (((Scheme.Modules.pullbackComp (pullback.snd (D.f i p) (D.f i q))
      (D.t i q ≫ D.f q i)).hom.naturality
      ((Scheme.Modules.pullbackPushforwardAdjunction (D.ι q)).counit.app (M q))).symm)
    (map_fold₅ (Scheme.Modules.pullback (pullback.snd (D.f i p) (D.f i q)))
      (glueChartComponent_overlap_collapse D M g i q))

include hC2 in
/-- **Pair component of the equalizing condition** (the `(p,q)`-component of
`glueChartFamily_equalizes`, C2 transported): the `p`-th candidate-inverse component
followed by the restricted first descent-leg factor equals the `q`-th component
followed by the restricted second descent-leg factor. This is where the triple-overlap
multiplicativity (C2) at the triple `(i,p,q)` is consumed, transposed along the
triple-overlap immersion `q_pq : V_ipq ⟶ U_i`; the degenerate pairs (`p = i` or
`q = i`) instead invoke the self-identity (C1). Project-local. -/
lemma glueChartComponent_leg_compat (i p q : D.J) :
    glueChartComponent D M g i p ≫ (Scheme.Modules.pullback (D.ι i)).map
        ((Scheme.Modules.pushforward (D.ι p)).map
            ((Scheme.Modules.pullbackPushforwardAdjunction (D.f p q)).unit.app (M p)) ≫
          (Scheme.Modules.pushforwardComp (D.f p q) (D.ι p)).hom.app
            ((Scheme.Modules.pullback (D.f p q)).obj (M p)))
      = glueChartComponent D M g i q ≫ (Scheme.Modules.pullback (D.ι i)).map
          ((Scheme.Modules.pushforward (D.ι q)).map
              ((Scheme.Modules.pullbackPushforwardAdjunction
                (D.t p q ≫ D.f q p)).unit.app (M q)) ≫
            (Scheme.Modules.pushforwardComp (D.t p q ≫ D.f q p) (D.ι q)).hom.app
              ((Scheme.Modules.pullback (D.t p q ≫ D.f q p)).obj (M q)) ≫
            (Scheme.Modules.pushforward
              ((D.t p q ≫ D.f q p) ≫ D.ι q)).map (g p q).inv ≫
            (Scheme.Modules.pushforwardCongr
              (show (D.t p q ≫ D.f q p) ≫ D.ι q = D.f p q ≫ D.ι p by
                rw [Category.assoc]; exact D.glue_condition p q)).hom.app
              ((Scheme.Modules.pullback (D.f p q)).obj (M p))) := by
  -- REDUCTION (blueprint items (1)–(2), DONE): cancel the triple factor iso
  -- `glueTripleFactorIso` (blueprint's triple `β`, built on the opens identity
  -- `glueData_preimage_image_eq₃`), transpose along the triple-overlap immersion
  -- `q = fst ≫ f_ip` (the transposes are injective), fire the triple mate
  -- `glueTripleFactor_mate` on both sides, and substitute the leg transposes
  -- `glueLegA_component_transpose` / `glueLegB_component_transpose`.
  refine (Iso.cancel_iso_hom_right _ _
    (glueTripleFactorIso D i p q ((Scheme.Modules.pullback (D.f p q)).obj (M p)))).mp ?_
  apply ((Scheme.Modules.pullbackPushforwardAdjunction
    (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p)).homEquiv _ _).symm.injective
  -- LHS: associate, peel the component, fire the mate, substitute the leg-A transpose
  refine Eq.trans (congrArg ((Scheme.Modules.pullbackPushforwardAdjunction
      (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p)).homEquiv _ _).symm
    (Category.assoc _ _ _)) ?_
  refine Eq.trans (Adjunction.homEquiv_naturality_left_symm _ _ _) ?_
  refine Eq.trans (whisker_eq _ ((glueTripleFactor_mate D i p q _ _).symm.trans
    (whisker_eq _ (whisker_eq _ (whisker_eq _
      (congrArg (Scheme.Modules.pullback
          (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).map
        (glueLegA_component_transpose D p q (M p)))))))) ?_
  -- RHS: the same three steps with the leg-B transpose
  refine Eq.trans ?_ ((congrArg ((Scheme.Modules.pullbackPushforwardAdjunction
      (pullback.fst (D.f i p) (D.f i q) ≫ D.f i p)).homEquiv _ _).symm
    (Category.assoc _ _ _)).trans
    ((Adjunction.homEquiv_naturality_left_symm _ _ _).trans
      (whisker_eq _ ((glueTripleFactor_mate D i p q _ _).symm.trans
        (whisker_eq _ (whisker_eq _ (whisker_eq _
          (congrArg (Scheme.Modules.pullback
              (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).map
            (glueLegB_component_transpose D M g p q))))))))).symm
  -- REMAINING CORE (blueprint item (3)): the fully transposed component equation over
  -- the triple overlap `V_ipq`. Each side collapses, by the cast coherence
  -- `pullback_cast_compat`, the counit-migration naturality squares, and the
  -- chart-level collapse `glueChartComponent_overlap_collapse` (the pair mate at the
  -- identity + the triangle identity), to a `pullbackBaseChangeTransport` chain
  -- (`glueChart_legCompat_left`/`_right`); the two chains agree by the cocycle
  -- multiplicativity `hC2 i p q` whose endpoints the `glueData_bridge_src/mid/tgt`
  -- casts align on the nose (`final_cancel`). No case split on the degenerate pairs
  -- (`p = i` / `q = i`) is needed: (C2) holds for all triples.
  have hC2h := congrArg (fun e => e.hom) (hC2 i p q)
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom,
    pullbackBaseChangeTransport, Category.assoc] at hC2h
  -- cancellation data for the three extra invertible factors
  have hcc : (Scheme.Modules.pullbackCongr (glueData_bridge_tgt D i p q)).hom.app (M q) ≫
      (Scheme.Modules.pullbackCongr (glueData_bridge_tgt D i p q).symm).hom.app (M q)
      = 𝟙 _ := by
    simp only [pullbackCongr_hom_app_eqToHom, eqToHom_trans, eqToHom_refl]
  have hbb : (Scheme.Modules.pullbackComp
        (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))
        (D.t p q ≫ D.f q p)).hom.app (M q) ≫
      (Scheme.Modules.pullbackComp (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))
        (D.t p q ≫ D.f q p)).inv.app (M q) = 𝟙 _ :=
    Iso.hom_inv_id_app _ _
  have haa : (Scheme.Modules.pullback
        (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).map (g p q).hom ≫
      (Scheme.Modules.pullback
        (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).map (g p q).inv = 𝟙 _ :=
    ((Scheme.Modules.pullback
        (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).map_comp _ _).symm.trans
      ((congrArg (Scheme.Modules.pullback
          (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).map (g p q).hom_inv_id).trans
        ((Scheme.Modules.pullback
          (D.t' i p q ≫ pullback.fst (D.f p q) (D.f p i))).map_id _))
  exact (glueChart_legCompat_left D M g i p q).trans
    ((final_cancel hC2h hcc hbb haa).trans
      (glueChart_legCompat_right D M g i p q).symm)

include hC2 in
/-- **The candidate-inverse family equalizes the restricted descent legs**
(C2 transported): the `(p,q)`-component of the equalizing condition is the
triple-overlap multiplicativity (C2) at the triple `(i,p,q)`, transported through the
overlap base changes `β`. Obligation 1 of `isIso_glueRestrictionHom`. Project-local. -/
lemma glueChartFamily_equalizes (i : D.J) :
    glueChartFamily D M g i ≫ (Scheme.Modules.pullback (D.ι i)).map (glueLegA D M)
      = glueChartFamily D M g i ≫ (Scheme.Modules.pullback (D.ι i)).map (glueLegB D M g) := by
  -- componentwise detection through the preserved overlap product (the same
  -- `piComparison` discipline as `glueRestrict_proj_compat`/`glueRestrict_hom_ext`);
  -- `refine`-style (`rw [← Iso.cancel_iso_hom_right …]` cannot match the `Eq` node:
  -- `glueOverlapProd` is only defeq to the `∏ᶜ` the comparison is stated at)
  refine (Iso.cancel_iso_hom_right _ _
    (PreservesProduct.iso (Scheme.Modules.pullback (D.ι i)) fun p : D.J × D.J =>
      (Scheme.Modules.pushforward (D.f p.1 p.2 ≫ D.ι p.1)).obj
        ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1)))).mp
    (Limits.Pi.hom_ext _ _ fun p => ?_)
  have hπ : (PreservesProduct.iso (Scheme.Modules.pullback (D.ι i)) fun p : D.J × D.J =>
        (Scheme.Modules.pushforward (D.f p.1 p.2 ≫ D.ι p.1)).obj
          ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1))).hom ≫ Pi.π _ p
      = (Scheme.Modules.pullback (D.ι i)).map (Pi.π _ p) := piComparison_comp_π _ _ _
  -- fold each leg against the projection (`Pi.lift_π` at the glued level), splitting
  -- off the `p.1`-/`p.2`-th chart projection (term-mode `map_comp` under the diamond)
  have hA : (Scheme.Modules.pullback (D.ι i)).map (glueLegA D M) ≫
        (Scheme.Modules.pullback (D.ι i)).map (Pi.π _ p)
      = (Scheme.Modules.pullback (D.ι i)).map
          (Pi.π (fun k => (Scheme.Modules.pushforward (D.ι k)).obj (M k)) p.1) ≫
        (Scheme.Modules.pullback (D.ι i)).map
          ((Scheme.Modules.pushforward (D.ι p.1)).map
              ((Scheme.Modules.pullbackPushforwardAdjunction (D.f p.1 p.2)).unit.app
                (M p.1)) ≫
            (Scheme.Modules.pushforwardComp (D.f p.1 p.2) (D.ι p.1)).hom.app
              ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1))) :=
    ((Scheme.Modules.pullback (D.ι i)).map_comp _ _).symm.trans
      ((congrArg (Scheme.Modules.pullback (D.ι i)).map (Limits.Pi.lift_π _ _)).trans
        ((Scheme.Modules.pullback (D.ι i)).map_comp _ _))
  have hB : (Scheme.Modules.pullback (D.ι i)).map (glueLegB D M g) ≫
        (Scheme.Modules.pullback (D.ι i)).map (Pi.π _ p)
      = (Scheme.Modules.pullback (D.ι i)).map
          (Pi.π (fun k => (Scheme.Modules.pushforward (D.ι k)).obj (M k)) p.2) ≫
        (Scheme.Modules.pullback (D.ι i)).map
          ((Scheme.Modules.pushforward (D.ι p.2)).map
              ((Scheme.Modules.pullbackPushforwardAdjunction
                (D.t p.1 p.2 ≫ D.f p.2 p.1)).unit.app (M p.2)) ≫
            (Scheme.Modules.pushforwardComp (D.t p.1 p.2 ≫ D.f p.2 p.1) (D.ι p.2)).hom.app
              ((Scheme.Modules.pullback (D.t p.1 p.2 ≫ D.f p.2 p.1)).obj (M p.2)) ≫
            (Scheme.Modules.pushforward
              ((D.t p.1 p.2 ≫ D.f p.2 p.1) ≫ D.ι p.2)).map (g p.1 p.2).inv ≫
            (Scheme.Modules.pushforwardCongr
              (show (D.t p.1 p.2 ≫ D.f p.2 p.1) ≫ D.ι p.2 = D.f p.1 p.2 ≫ D.ι p.1 by
                rw [Category.assoc]; exact D.glue_condition p.1 p.2)).hom.app
              ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1))) :=
    ((Scheme.Modules.pullback (D.ι i)).map_comp _ _).symm.trans
      ((congrArg (Scheme.Modules.pullback (D.ι i)).map (Limits.Pi.lift_π _ _)).trans
        ((Scheme.Modules.pullback (D.ι i)).map_comp _ _))
  -- pure-unification assembly: comparison-cancel, leg fold, family projection,
  -- component obligation, and back up the `B`-side
  exact (Category.assoc _ _ _).trans ((whisker_eq _ hπ).trans ((Category.assoc _ _ _).trans
    ((whisker_eq _ hA).trans ((Category.assoc _ _ _).symm.trans
      ((eq_whisker (glueChartFamily_pullback_map_π D M g i p.1) _).trans
        ((glueChartComponent_leg_compat D M g hC2 i p.1 p.2).trans
          ((eq_whisker (glueChartFamily_pullback_map_π D M g i p.2) _).symm.trans
            ((Category.assoc _ _ _).trans ((whisker_eq _ hB).symm.trans
              ((Category.assoc _ _ _).symm.trans ((whisker_eq _ hπ.symm).trans
                (Category.assoc _ _ _).symm)))))))))))

/-- **The candidate inverse** `σ_i : M i ⟶ ι_i^* (glue …)`: the equalizer lift of
`glueChartFamily` through the limit-preservation comparison
`glueRestrictEqualizerIso`. Project-local. -/
noncomputable def glueRestrictionInv (i : D.J) :
    M i ⟶ (Scheme.Modules.pullback (D.ι i)).obj (glue D M g hC1 hC2) :=
  equalizer.lift (glueChartFamily D M g i) (glueChartFamily_equalizes D M g hC2 i) ≫
    (glueRestrictEqualizerIso D M g hC1 hC2 i).inv

/-- **Comparison compatibility**: through the equalizer- and product-preservation
comparisons, the restricted equalizer inclusion followed by the `j`-th product
projection is the chart pullback of `glueProj j`. Pure limit-API bookkeeping shared by
the lift computation and the joint-detection lemma. Project-local. -/
@[reassoc]
lemma glueRestrict_proj_compat (i j : D.J) :
    (glueRestrictEqualizerIso D M g hC1 hC2 i).hom ≫
        equalizer.ι ((Scheme.Modules.pullback (D.ι i)).map (glueLegA D M))
          ((Scheme.Modules.pullback (D.ι i)).map (glueLegB D M g)) ≫
        (glueRestrictProdIso D M i).hom ≫ Pi.π _ j
      = (Scheme.Modules.pullback (D.ι i)).map (glueProj D M g hC1 hC2 j) := by
  have hπ : (glueRestrictProdIso D M i).hom ≫ Pi.π _ j
      = (Scheme.Modules.pullback (D.ι i)).map (Pi.π _ j) :=
    piComparison_comp_π _ _ _
  have hι : (glueRestrictEqualizerIso D M g hC1 hC2 i).hom ≫
        equalizer.ι ((Scheme.Modules.pullback (D.ι i)).map (glueLegA D M))
          ((Scheme.Modules.pullback (D.ι i)).map (glueLegB D M g))
      = (Scheme.Modules.pullback (D.ι i)).map (𝟙 (glue D M g hC1 hC2)) ≫
        (Scheme.Modules.pullback (D.ι i)).map
          (equalizer.ι (glueLegA D M) (glueLegB D M g)) :=
    (Category.assoc _ _ _).trans
      (congrArg ((Scheme.Modules.pullback (D.ι i)).map (𝟙 _) ≫ ·)
        (equalizerComparison_comp_π _ _ _))
  rw [reassoc_of% hι, hπ]
  -- term-mode `map_comp` folding (positional `rw [← Functor.map_comp]` fails to match
  -- under the `X.Modules` instance diamond)
  exact (congrArg ((Scheme.Modules.pullback (D.ι i)).map (𝟙 _) ≫ ·)
      ((Scheme.Modules.pullback (D.ι i)).map_comp _ _).symm).trans
    ((Scheme.Modules.pullback (D.ι i)).map_comp _ _).symm

/-- The candidate inverse followed by the restricted `j`-th projection recovers the
`j`-th component of the family: the equalizer/product preservation comparisons cancel
against the lift. Project-local. -/
@[reassoc]
lemma glueRestrictionInv_pullback_map_glueProj (i j : D.J) :
    glueRestrictionInv D M g hC1 hC2 i ≫
        (Scheme.Modules.pullback (D.ι i)).map (glueProj D M g hC1 hC2 j)
      = glueChartComponent D M g i j := by
  rw [glueRestrictionInv, Category.assoc,
    ← glueRestrict_proj_compat D M g hC1 hC2 i j, Iso.inv_hom_id_assoc,
    equalizer.lift_ι_assoc, glueChartFamily, Category.assoc, Iso.inv_hom_id_assoc]
  exact Limits.Pi.lift_π _ _

/-- **Joint detection of morphisms into the restricted glued sheaf**: two morphisms
into `ι_i^* (glue …)` agreeing after every restricted projection
`ι_i^* (glueProj j)` agree. The restricted equalizer inclusion is a monomorphism and
the restricted product projections are jointly monic through the preservation
comparisons. Project-local. -/
lemma glueRestrict_hom_ext {i : D.J} {Z : (D.U i).Modules}
    {u v : Z ⟶ (Scheme.Modules.pullback (D.ι i)).obj (glue D M g hC1 hC2)}
    (h : ∀ j, u ≫ (Scheme.Modules.pullback (D.ι i)).map (glueProj D M g hC1 hC2 j)
        = v ≫ (Scheme.Modules.pullback (D.ι i)).map (glueProj D M g hC1 hC2 j)) :
    u = v := by
  rw [← Iso.cancel_iso_hom_right u v (glueRestrictEqualizerIso D M g hC1 hC2 i)]
  apply equalizer.hom_ext
  simp only [Category.assoc]
  rw [← Iso.cancel_iso_hom_right _ _ (glueRestrictProdIso D M i)]
  apply Limits.Pi.hom_ext
  intro j
  simp only [Category.assoc]
  rw [glueRestrict_proj_compat D M g hC1 hC2 i j]
  exact h j

include hC1 in
/-- **Triangle (C1 + counit): the self-component collapses to the identity**. The
`(i,i)`-component of the candidate inverse, transposed back along the chart immersion
(the counit), is the identity of `M i`: the transition `g_ii` is the canonical cast
(C1), `f_ii` is an isomorphism, and the unit/counit cancel by the triangle identity.
Obligation 2 of `isIso_glueRestrictionHom`. Project-local. -/
lemma glueChartComponent_self_counit (i : D.J) :
    glueChartComponent D M g i i ≫
        (Scheme.Modules.pullbackPushforwardAdjunction (D.ι i)).counit.app (M i)
      = 𝟙 (M i) := by
  have h_f : D.f i i = D.t i i ≫ D.f i i := by rw [D.t_id i, Category.id_comp]
  -- collapse the transition (C1) against the geometric/site-level comparison casts:
  -- the middle three pullback-level factors are one site-level congruence cast
  have hC : (restrictFunctorIsoPullback (D.f i i)).hom.app (M i) ≫
        (g i i).hom ≫
        (restrictFunctorIsoPullback (D.t i i ≫ D.f i i)).inv.app (M i)
      = (restrictFunctorCongr h_f).hom.app (M i) := by
    have hg : (g i i).hom = (Scheme.Modules.pullbackCongr h_f).hom.app (M i) := by
      rw [hC1 i, pullbackCongr_hom_app_eqToHom h_f (M i)]
      rfl
    rw [hg, restrictFunctorIsoPullback_congr_assoc h_f (M i), Iso.hom_inv_id_app,
      Category.comp_id]
  have hmid : (Scheme.Modules.pushforward (D.f i i)).map
        ((restrictFunctorIsoPullback (D.f i i)).hom.app (M i)) ≫
      (Scheme.Modules.pushforward (D.f i i)).map ((g i i).hom) ≫
      (Scheme.Modules.pushforward (D.f i i)).map
        ((restrictFunctorIsoPullback (D.t i i ≫ D.f i i)).inv.app (M i))
      = (Scheme.Modules.pushforward (D.f i i)).map
        ((restrictFunctorCongr h_f).hom.app (M i)) :=
    (congrArg ((Scheme.Modules.pushforward (D.f i i)).map
          ((restrictFunctorIsoPullback (D.f i i)).hom.app (M i)) ≫ ·)
        ((Scheme.Modules.pushforward (D.f i i)).map_comp _ _).symm).trans
      ((((Scheme.Modules.pushforward (D.f i i)).map_comp _ _).symm).trans
        (congrArg (Scheme.Modules.pushforward (D.f i i)).map
          ((Category.assoc _ _ _).symm.trans (by rw [← Category.assoc] at hC; exact hC))))
  -- unfold the component and the factor isomorphism, regroup, and substitute the
  -- three bridges (unit, C1-cast, counit)
  dsimp only [glueChartComponent, glueOverlapFactorIso, Iso.trans_inv, Functor.mapIso_inv,
    Iso.app_inv, Iso.symm_inv]
  simp only [Category.assoc]
  -- `erw` (defeq matching) — plain `rw` cannot match the comp nodes under the
  -- `X.Modules` instance diamond
  erw [← restrictAdjunction_unit_app_iso_assoc (D.f i i) (M i)]
  -- pure-unification calc (positional `rw` cannot match across comp-node provenances)
  calc (restrictAdjunction (D.f i i)).unit.app (M i) ≫
        (Scheme.Modules.pushforward (D.f i i)).map
          ((restrictFunctorIsoPullback (D.f i i)).hom.app (M i)) ≫
        (Scheme.Modules.pushforward (D.f i i)).map (g i i).hom ≫
        (Scheme.Modules.pushforward (D.f i i)).map
          ((restrictFunctorIsoPullback (D.t i i ≫ D.f i i)).inv.app (M i)) ≫
        (glueOverlapBaseChangeIso D i i).inv.app (M i) ≫
        (restrictFunctorIsoPullback (D.ι i)).hom.app
          ((Scheme.Modules.pushforward (D.ι i)).obj (M i)) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction (D.ι i)).counit.app (M i)
      = (restrictAdjunction (D.f i i)).unit.app (M i) ≫
        ((Scheme.Modules.pushforward (D.f i i)).map
            ((restrictFunctorIsoPullback (D.f i i)).hom.app (M i)) ≫
          (Scheme.Modules.pushforward (D.f i i)).map (g i i).hom ≫
          (Scheme.Modules.pushforward (D.f i i)).map
            ((restrictFunctorIsoPullback (D.t i i ≫ D.f i i)).inv.app (M i))) ≫
        (glueOverlapBaseChangeIso D i i).inv.app (M i) ≫
        (restrictFunctorIsoPullback (D.ι i)).hom.app
          ((Scheme.Modules.pushforward (D.ι i)).obj (M i)) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction (D.ι i)).counit.app (M i) := by
        simp only [Category.assoc]
    _ = (restrictAdjunction (D.f i i)).unit.app (M i) ≫
        (Scheme.Modules.pushforward (D.f i i)).map
          ((restrictFunctorCongr h_f).hom.app (M i)) ≫
        (glueOverlapBaseChangeIso D i i).inv.app (M i) ≫
        (restrictFunctorIsoPullback (D.ι i)).hom.app
          ((Scheme.Modules.pushforward (D.ι i)).obj (M i)) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction (D.ι i)).counit.app (M i) :=
        whisker_eq _ (eq_whisker hmid _)
    _ = (restrictAdjunction (D.f i i)).unit.app (M i) ≫
        (Scheme.Modules.pushforward (D.f i i)).map
          ((restrictFunctorCongr h_f).hom.app (M i)) ≫
        (glueOverlapBaseChangeIso D i i).inv.app (M i) ≫
        (restrictAdjunction (D.ι i)).counit.app (M i) :=
        whisker_eq _ (whisker_eq _ (whisker_eq _
          (restrictFunctorIsoPullback_hom_app_counit (D.ι i) (M i))))
    _ = 𝟙 (M i) := by
        -- section-level: the remaining composite is a cycle of presheaf restrictions
        ext V x
        have htot : (M i).presheaf.map
              (homOfLE ((D.f i i).image_preimage_le V)).op ≫
            (M i).presheaf.map (eqToHom (show (D.t i i ≫ D.f i i) ''ᵁ ((D.f i i) ⁻¹ᵁ V)
                = (D.f i i) ''ᵁ ((D.f i i) ⁻¹ᵁ V) from
              TopologicalSpace.Opens.ext (by
                change (D.t i i ≫ D.f i i).base '' _ = (D.f i i).base '' _
                rw [← h_f]))).op ≫
            (M i).presheaf.map (eqToHom (glueData_preimage_image_eq D i i V)).op ≫
            (M i).presheaf.map (eqToHom ((D.ι i).preimage_image_eq V).symm).op
            = 𝟙 _ := by
          erw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
          exact (congrArg (M i).presheaf.map (Subsingleton.elim _ (𝟙 (op V)))).trans
            ((M i).presheaf.map_id _)
        exact congr($(htot) x)


/-- **The overlap compatibility of the restriction morphisms**: the `(i,j)`-component
of the descent-equalizer condition, transposed to the pullback level through
`glueLift_cond_iff` — over the overlap, `r_i` and `r_j` differ exactly by the
transition isomorphism `g_ij` (through the pseudofunctor casts). Project-local. -/
lemma glueRestriction_overlap_compat (i j : D.J) :
    (Scheme.Modules.pullbackComp (D.f i j) (D.ι i)).inv.app (glue D M g hC1 hC2) ≫
        (Scheme.Modules.pullback (D.f i j)).map (glueRestrictionHom D M g hC1 hC2 i)
      = (Scheme.Modules.pullbackCongr
            (show (D.t i j ≫ D.f j i) ≫ D.ι j = D.f i j ≫ D.ι i by
              rw [Category.assoc]; exact D.glue_condition i j)).inv.app
          (glue D M g hC1 hC2) ≫
        (Scheme.Modules.pullbackComp (D.t i j ≫ D.f j i) (D.ι j)).inv.app
          (glue D M g hC1 hC2) ≫
        (Scheme.Modules.pullback (D.t i j ≫ D.f j i)).map
          (glueRestrictionHom D M g hC1 hC2 j) ≫ (g i j).inv := by
  refine (glueLift_cond_iff D M g
    (fun k => glueRestrictionHom D M g hC1 hC2 k) i j).mp ?_
  have hfold : ∀ k, (Scheme.Modules.pullbackPushforwardAdjunction (D.ι k)).homEquiv
        (glue D M g hC1 hC2) (M k) (glueRestrictionHom D M g hC1 hC2 k)
      = glueProj D M g hC1 hC2 k := fun k => Equiv.apply_symm_apply _ _
  rw [hfold i, hfold j]
  -- the `(i,j)`-component of the equalizer condition of the glued sheaf, extracted by
  -- a pure-unification calc (`glueProj k ≡ 𝟙 ≫ equalizer.ι ≫ π_k` definitionally, and
  -- the legs are `Pi.lift`s, so `Pi.lift_π` folds the components)
  refine Eq.trans ?_ (((eq_whisker (Category.id_comp
    (equalizer.ι (glueLegA D M) (glueLegB D M g) ≫
      Pi.π (fun k => (Scheme.Modules.pushforward (D.ι k)).obj (M k)) j)) _).trans
    (Category.assoc _ _ _)).symm)
  refine (((eq_whisker (Category.id_comp _) _).trans (Category.assoc _ _ _)).trans
    ((whisker_eq _ (Limits.Pi.lift_π (fun p : D.J × D.J =>
        Pi.π (fun k => (Scheme.Modules.pushforward (D.ι k)).obj (M k)) p.1 ≫
          ((Scheme.Modules.pushforward (D.ι p.1)).map
            ((Scheme.Modules.pullbackPushforwardAdjunction (D.f p.1 p.2)).unit.app
              (M p.1)) ≫
          (Scheme.Modules.pushforwardComp (D.f p.1 p.2) (D.ι p.1)).hom.app
            ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1)))) (i, j)).symm).trans
      (Category.assoc _ _ _).symm)).trans ?_
  refine (eq_whisker (equalizer.condition _ _) _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact whisker_eq _ (Limits.Pi.lift_π _ _)

/-- **The restriction morphism followed by a component of the candidate inverse is the
restricted projection** (the pair-`(i,j)` equalizer condition transposed along the
chart immersion). Obligation 3 of `isIso_glueRestrictionHom`. Project-local. -/
lemma glueRestrictionHom_glueChartComponent (i j : D.J) :
    glueRestrictionHom D M g hC1 hC2 i ≫ glueChartComponent D M g i j
      = (Scheme.Modules.pullback (D.ι i)).map (glueProj D M g hC1 hC2 j) := by
  -- the overlap pullback of `r_i`, transported across `g_ij`, is the mate transpose
  -- of the restricted `j`-th projection
  have hZ : (Scheme.Modules.pullback (D.f i j)).map (glueRestrictionHom D M g hC1 hC2 i) ≫
        (g i j).hom
      = ((Scheme.Modules.pullbackPushforwardAdjunction (D.f i j)).homEquiv
            ((Scheme.Modules.pullback (D.ι i)).obj (glue D M g hC1 hC2))
            ((Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j))).symm
          ((Scheme.Modules.pullback (D.ι i)).map (glueProj D M g hC1 hC2 j) ≫
            (glueOverlapFactorIso D M i j).hom) := by
    have hc := glueRestriction_overlap_compat D M g hC1 hC2 i j
    have hm := glueOverlapFactor_mate D M i j (glueProj D M g hC1 hC2 j)
    -- unfold the iso-conjugation of `hc`:
    -- `pb(f).map r_i = pbComp.hom.app ≫ pbCongr.inv.app ≫ pbComp'.inv.app ≫ pb(tf).map r_j ≫ g⁻¹`
    have hL : (Scheme.Modules.pullback (D.f i j)).map
          (glueRestrictionHom D M g hC1 hC2 i)
        = (Scheme.Modules.pullbackComp (D.f i j) (D.ι i)).hom.app (glue D M g hC1 hC2) ≫
          (Scheme.Modules.pullbackCongr
              (show (D.t i j ≫ D.f j i) ≫ D.ι j = D.f i j ≫ D.ι i by
                rw [Category.assoc]; exact D.glue_condition i j)).inv.app
            (glue D M g hC1 hC2) ≫
          (Scheme.Modules.pullbackComp (D.t i j ≫ D.f j i) (D.ι j)).inv.app
            (glue D M g hC1 hC2) ≫
          (Scheme.Modules.pullback (D.t i j ≫ D.f j i)).map
            (glueRestrictionHom D M g hC1 hC2 j) ≫ (g i j).inv := by
      exact (Iso.inv_comp_eq ((Scheme.Modules.pullbackComp (D.f i j) (D.ι i)).app
        (glue D M g hC1 hC2))).mp hc
    rw [hL]
    -- generic cancel shape, proved abstractly (simp works on fresh variables; it
    -- cannot match the diamond-laden concrete comp nodes)
    have hcancel : ∀ {P Q R S T U : (D.V (i, j)).Modules}
        (x₁ : P ⟶ Q) (x₂ : Q ⟶ R) (x₃ : R ⟶ S) (x₄ : S ⟶ T) (e : U ≅ T),
        (x₁ ≫ x₂ ≫ x₃ ≫ x₄ ≫ e.inv) ≫ e.hom = x₁ ≫ x₂ ≫ x₃ ≫ x₄ := by
      intros; simp
    exact (hcancel _ _ _ _ _).trans hm
  -- the unit naturality square at `r_i`
  have hnat : glueRestrictionHom D M g hC1 hC2 i ≫
      (Scheme.Modules.pullbackPushforwardAdjunction (D.f i j)).unit.app (M i)
      = (Scheme.Modules.pullbackPushforwardAdjunction (D.f i j)).unit.app
          ((Scheme.Modules.pullback (D.ι i)).obj (glue D M g hC1 hC2)) ≫
        (Scheme.Modules.pushforward (D.f i j)).map
          ((Scheme.Modules.pullback (D.f i j)).map
            (glueRestrictionHom D M g hC1 hC2 i)) :=
    (Scheme.Modules.pullbackPushforwardAdjunction (D.f i j)).unit.naturality _
  -- the folded transpose equals the restricted projection through the factor iso
  have hY : (Scheme.Modules.pullbackPushforwardAdjunction (D.f i j)).unit.app
        ((Scheme.Modules.pullback (D.ι i)).obj (glue D M g hC1 hC2)) ≫
      (Scheme.Modules.pushforward (D.f i j)).map
        ((Scheme.Modules.pullback (D.f i j)).map
          (glueRestrictionHom D M g hC1 hC2 i) ≫ (g i j).hom)
      = (Scheme.Modules.pullback (D.ι i)).map (glueProj D M g hC1 hC2 j) ≫
        (glueOverlapFactorIso D M i j).hom := by
    refine (whisker_eq _ (congrArg
      (fun m => (Scheme.Modules.pushforward (D.f i j)).map m) hZ)).trans ?_
    exact (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  -- pure-unification assembly (regroup, naturality, fold, `hY`, cancel the iso)
  exact (Category.assoc _ _ _).symm.trans ((eq_whisker hnat _).trans
    ((Category.assoc _ _ _).trans ((whisker_eq _ ((Category.assoc _ _ _).symm)).trans
      ((whisker_eq _ (eq_whisker
          ((Scheme.Modules.pushforward (D.f i j)).map_comp _ _).symm _)).trans
        ((Category.assoc _ _ _).symm.trans ((eq_whisker hY _).trans
          ((Category.assoc _ _ _).trans ((whisker_eq _
              (glueOverlapFactorIso D M i j).hom_inv_id).trans
            (Category.comp_id _)))))))))

end GlueRestrictionInverse

/-- **Effective descent: the chart restriction morphism of the glued sheaf is an
isomorphism** (`def:gr_modules_glueRestrictionIso`). This is where the cocycle
hypotheses (C1)/(C2) are consumed.

PROOF ROUTE (scoped iter-066, partially built): the chart pullback `ι_i^*` preserves
limits (`pullback_preservesLimits_of_isOpenImmersion` — it is isomorphic to the
site-level pushforward `restrictFunctor`), so `ι_i^* (glue …)` is the equalizer of the
restricted legs `ι_i^* (glueLegA)`, `ι_i^* (glueLegB)` and the restricted product
embeds into `∏_j ι_i^* ((ι_j)_* M_j)`. The candidate inverse `M i ⟶ ι_i^* (glue …)`
is the equalizer lift of the family whose `j`-component transports a section of `M i`
to the overlap: `unit_{f_ij} ≫ (f_ij)_* (g_ij-conjugate) ≫ β_ij⁻¹`, where
`β_ij : ι_i^* ((ι_j)_* M_j) ≅ (f_ij)_* ((t_ij ≫ f_ji)^* M_j)` is the open-cover base
change of the cartesian overlap square (site-level: both composites are pushforwards
along the SAME opens functor, by `glueData_preimage_image_eq`). The equalizing
condition of that family is (C2) in transported form; the two triangle identities
reduce to (C1) and the counit triangle. Remaining work: construct `β_ij` (via
`restrictFunctor` + `SheafOfModules.pushforwardComp`/`pushforwardCongr` +
`glueData_preimage_image_eq`) and verify the three conditions. -/
theorem isIso_glueRestrictionHom (D : Scheme.GlueData.{0}) (M : ∀ i, (D.U i).Modules)
    (g : ∀ i j, (Scheme.Modules.pullback (D.f i j)).obj (M i) ≅
        (Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j))
    (hC1 : ∀ i, g i i = eqToIso (congrArg (fun φ => (Scheme.Modules.pullback φ).obj (M i))
        (show D.f i i = D.t i i ≫ D.f i i by rw [D.t_id i, Category.id_comp])))
    (hC2 : ∀ i j k,
        pullbackBaseChangeTransport (pullback.fst (D.f i j) (D.f i k))
            (D.f i j) (D.t i j ≫ D.f j i) (g i j) ≪≫
          (Scheme.Modules.pullbackCongr (glueData_bridge_mid D i j k)).app (M j) ≪≫
          pullbackBaseChangeTransport (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
            (D.f j k) (D.t j k ≫ D.f k j) (g j k) ≪≫
          (Scheme.Modules.pullbackCongr (glueData_bridge_tgt D i j k)).app (M k)
        = (Scheme.Modules.pullbackCongr (glueData_bridge_src D i j k)).app (M i) ≪≫
          pullbackBaseChangeTransport (pullback.snd (D.f i j) (D.f i k))
            (D.f i k) (D.t i k ≫ D.f k i) (g i k)) (i : D.J) :
    IsIso (glueRestrictionHom D M g hC1 hC2 i) := by
  -- the restriction morphism in unit–counit form
  have hr : glueRestrictionHom D M g hC1 hC2 i
      = (Scheme.Modules.pullback (D.ι i)).map (glueProj D M g hC1 hC2 i) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction (D.ι i)).counit.app (M i) :=
    Adjunction.homEquiv_counit _ _ _ _
  refine ⟨glueRestrictionInv D M g hC1 hC2 i, ?_, ?_⟩
  · -- `r_i ≫ σ_i = 𝟙`: joint detection by the restricted projections; the `j`-th
    -- component is the transposed pair-`(i,j)` equalizer condition (obligation 3)
    apply glueRestrict_hom_ext D M g hC1 hC2
    intro j
    rw [Category.assoc, glueRestrictionInv_pullback_map_glueProj,
      glueRestrictionHom_glueChartComponent]
    exact (Category.id_comp _).symm
  · -- `σ_i ≫ r_i = 𝟙`: the self-component collapses by (C1) + the counit triangle
    -- (obligation 2)
    -- term-mode regrouping (mixed-provenance comp nodes block positional `rw`)
    exact (whisker_eq _ hr).trans ((Category.assoc _ _ _).symm.trans
      ((eq_whisker (glueRestrictionInv_pullback_map_glueProj D M g hC1 hC2 i i) _).trans
        (glueChartComponent_self_counit D M g hC1 i)))

/-- **The restriction isomorphism of the glued sheaf**
(`def:gr_modules_glueRestrictionIso`): the canonical identification
`ι_i^* (glue D M g …) ≅ M i` of the chart restriction of the glued sheaf with the
`i`-th input sheaf, with underlying morphism the adjoint transpose of the `i`-th
descent-equalizer projection. Project-local. -/
noncomputable def glueRestrictionIso (D : Scheme.GlueData.{0}) (M : ∀ i, (D.U i).Modules)
    (g : ∀ i j, (Scheme.Modules.pullback (D.f i j)).obj (M i) ≅
        (Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j))
    (hC1 : ∀ i, g i i = eqToIso (congrArg (fun φ => (Scheme.Modules.pullback φ).obj (M i))
        (show D.f i i = D.t i i ≫ D.f i i by rw [D.t_id i, Category.id_comp])))
    (hC2 : ∀ i j k,
        pullbackBaseChangeTransport (pullback.fst (D.f i j) (D.f i k))
            (D.f i j) (D.t i j ≫ D.f j i) (g i j) ≪≫
          (Scheme.Modules.pullbackCongr (glueData_bridge_mid D i j k)).app (M j) ≪≫
          pullbackBaseChangeTransport (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
            (D.f j k) (D.t j k ≫ D.f k j) (g j k) ≪≫
          (Scheme.Modules.pullbackCongr (glueData_bridge_tgt D i j k)).app (M k)
        = (Scheme.Modules.pullbackCongr (glueData_bridge_src D i j k)).app (M i) ≪≫
          pullbackBaseChangeTransport (pullback.snd (D.f i j) (D.f i k))
            (D.f i k) (D.t i k ≫ D.f k i) (g i k)) (i : D.J) :
    (Scheme.Modules.pullback (D.ι i)).obj (glue D M g hC1 hC2) ≅ M i :=
  haveI := isIso_glueRestrictionHom D M g hC1 hC2 i
  asIso (glueRestrictionHom D M g hC1 hC2 i)

end AlgebraicGeometry.Scheme.Modules

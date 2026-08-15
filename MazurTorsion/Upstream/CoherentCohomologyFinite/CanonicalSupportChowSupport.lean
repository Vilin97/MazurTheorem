/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.CanonicalSupportChowCoherence

/-!
# Support adaptation of the canonical Chow open

The model module on the canonical support thickening has nonzero stalk
at every point.  Consequently, unless it is zero, the dense common open
of its Chow modification contains a point in its closed stalk support.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology
namespace CanonicalSupportThickening

variable {X : Scheme.{0}} {F : X.Modules}
  [F.IsFiniteType] [F.IsQuasicoherent]

/--
Every point of the canonical support thickening lies in the stalk
support of its model module.
-/
theorem modelModule_stalkSupport_eq_univ
    (A : CanonicalSupportThickening F) :
    Scheme.Modules.stalkSupport A.modelModule = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true]
  have hyClosed :
      A.inclusion x ∈ Scheme.Modules.closedStalkSupport F := by
    change
      A.inclusion x ∈
        (Scheme.Modules.closedStalkSupport F : Set X)
    rw [← A.range_inclusion]
    exact ⟨x, rfl⟩
  have hy :
      A.inclusion x ∈ Scheme.Modules.stalkSupport F := by
    rw [← Scheme.Modules.coe_closedStalkSupport_eq_stalkSupport F]
    exact hyClosed
  intro hx
  apply hy
  let e :=
    (Scheme.Modules.underlyingStalkFunctor
      (A.inclusion x)).mapIso A.comparisonIso
  apply e.isZero_iff.mpr
  let α :=
    TopCat.Presheaf.stalkPushforward
      AddCommGrpCat A.inclusion.base
        A.modelModule.sheaf.presheaf x
  letI : IsIso α :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      AddCommGrpCat
      A.inclusion_isClosedImmersion.isClosedEmbedding.isInducing
      A.modelModule.sheaf.presheaf x
  have hx' :
      IsZero (A.modelModule.sheaf.presheaf.stalk x) :=
    hx
  have hpush :
      IsZero
        (((TopCat.Presheaf.pushforward
            AddCommGrpCat A.inclusion.base).obj
          A.modelModule.sheaf.presheaf).stalk
            (A.inclusion x)) :=
    IsZero.of_iso hx' (asIso α)
  exact hpush

/-- The closed stalk support of the model module is the whole support
thickening. -/
theorem modelModule_closedStalkSupport_eq_top
    (A : CanonicalSupportThickening F) :
    Scheme.Modules.closedStalkSupport A.modelModule = ⊤ := by
  apply Closeds.ext
  change
    closure (Scheme.Modules.stalkSupport A.modelModule) =
      Set.univ
  rw [A.modelModule_stalkSupport_eq_univ, closure_univ]

variable {k : Type} [Field k]
  {f : X ⟶ Spec (CommRingCat.of k)} [IsProper f]

/--
The canonical common open is adapted to the support module: either the
module is zero, or that open contains a point of its closed stalk support.
-/
theorem sourceZeroOrSupportPoint_chowCommonOpen
    (A : CanonicalSupportThickening F) :
    let P := A.chowModification (k := k) (f := f)
    letI : IsOpenImmersion P.toOriginalOpen :=
      P.isOpenImmersion_toOriginalOpen
    IsZero A.modelModule ∨
      ∃ x : P.toOriginalOpen.opensRange,
        P.toOriginalOpen.opensRange.ι x ∈
          Scheme.Modules.closedStalkSupport A.modelModule := by
  dsimp only
  let P := A.chowModification (k := k) (f := f)
  letI : IsOpenImmersion P.toOriginalOpen :=
    P.isOpenImmersion_toOriginalOpen
  by_cases hzero : IsZero A.modelModule
  · exact Or.inl hzero
  right
  have htop_ne_bot :
      (⊤ : Closeds A.supportScheme) ≠ ⊥ := by
    intro htop
    apply hzero
    apply
      (Scheme.Modules.isZero_iff_closedStalkSupport_eq_bot
        A.modelModule).mpr
    rw [A.modelModule_closedStalkSupport_eq_top]
    exact htop
  have hnonempty : Nonempty A.supportScheme := by
    by_contra h
    letI : IsEmpty A.supportScheme :=
      not_nonempty_iff.mp h
    apply htop_ne_bot
    apply Closeds.ext
    ext x
    exact isEmptyElim x
  letI : Nonempty A.supportScheme := hnonempty
  have hrange :
      Set.Nonempty (Set.range P.toOriginalOpen) :=
    P.dense_toOriginalOpen.nonempty
  obtain ⟨_, x, rfl⟩ := hrange
  let x' : P.toOriginalOpen.opensRange :=
    ⟨P.toOriginalOpen x, ⟨x, rfl⟩⟩
  refine ⟨x', ?_⟩
  rw [A.modelModule_closedStalkSupport_eq_top]
  trivial

end CanonicalSupportThickening
end MazurTorsion.AlgebraicGeometry.CoherentCohomology

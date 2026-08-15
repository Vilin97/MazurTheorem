/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FinitePushforwardCoherence
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreVanishingCohomology
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveSerreTwistEquivalence
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemePushforwardCohomology

/-!
# Closed-immersion transfer of projective Serre vanishing

This file isolates the geometric comparison needed to transfer the
projective-space theorem to a closed subscheme.  Once relative scalar
twisting commutes with closed-immersion pushforward, the transfer of
eventual higher-cohomology vanishing is formal.
-/


open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

noncomputable local instance relativeSerreSheafHAddCommGroup
    {Z : TopCat.{0}}
    (G : TopCat.Sheaf AddCommGrpCat.{0} Z) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H G n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

/-- The functorial compatibility required between the scalar twist on a
closed subscheme and the ambient projective scalar twist. -/
def ClosedImmersionTwistPushforwardCompatible
    (R : Type) [CommRing R] (d : ℕ)
    {Y : Scheme.{0}} (i : Y ⟶ scheme R d) : Prop :=
  ∀ n : ℕ,
    Nonempty
      ((relativeProjectiveSerreTwistEquivalence
          R d i (n : ℤ)).functor ⋙
          Scheme.Modules.pushforward i ≅
        Scheme.Modules.pushforward i ⋙
          positiveScalarTwistFunctor R d n)

/-- Objectwise pushforward comparison supplied by the functorial
closed-immersion compatibility. -/
noncomputable def closedImmersionTwistPushforwardObjectIso
    (R : Type) [CommRing R] (d : ℕ)
    {Y : Scheme.{0}} (i : Y ⟶ scheme R d)
    (hcompat :
      ClosedImmersionTwistPushforwardCompatible
        R d i)
    (M : Y.Modules) (n : ℕ) :
    (Scheme.Modules.pushforward i).obj
        ((relativeProjectiveSerreTwistEquivalence
          R d i (n : ℤ)).functor.obj M) ≅
      (positiveScalarTwistFunctor R d n).obj
        ((Scheme.Modules.pushforward i).obj M) :=
  Classical.choice (hcompat n) |>.app M

/-- Relative Serre vanishing follows from the natural pushforward
comparison with the ambient projective scalar twist. -/
theorem eventually_relativeProjectiveSerreTwist_sheafH_subsingleton
    (R : Type) [CommRing R] [Module.Flat ℤ R]
    [IsNoetherianRing R]
    (d : ℕ)
    {Y : Scheme.{0}} (i : Y ⟶ scheme R d)
    [IsClosedImmersion i]
    (hcompat :
      ClosedImmersionTwistPushforwardCompatible
        R d i)
    (M : Y.Modules)
    [M.IsFiniteType] [M.IsQuasicoherent] :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      ∀ q : ℕ, 0 < q →
        Subsingleton
          (((relativeProjectiveSerreTwistEquivalence
            R d i (n : ℤ)).functor.obj M).sheaf.H q) := by
  let N := (Scheme.Modules.pushforward i).obj M
  letI : IsLocallyNoetherian (scheme R d) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (toSpec R d)
  letI : N.IsFiniteType :=
    Scheme.Modules.isFiniteType_pushforward_closedImmersion
      i M
  letI : N.IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_pushforward_affineHom
      i M
  obtain ⟨b, hb⟩ :=
    _root_.MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.eventually_positiveScalarTwist_sheafH_subsingleton
      R d N
  refine ⟨b, fun n hn q hq => ?_⟩
  let T :=
    (relativeProjectiveSerreTwistEquivalence
      R d i (n : ℤ)).functor.obj M
  let ePush :
      AddCommGrpCat.of (T.sheaf.H q) ≅
        AddCommGrpCat.of
          (((Scheme.Modules.pushforward i).obj T).sheaf.H q) :=
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.closedImmersionPushforwardHIso
      i T q
  let eTwist :=
    closedImmersionTwistPushforwardObjectIso
      R d i hcompat M n
  let eSheaf :=
    (Scheme.Modules.toUnderlyingSheaf
      (scheme R d)).mapIso eTwist
  let E :
      T.sheaf.H q ≃+
        ((positiveScalarTwistFunctor
          R d n).obj N).sheaf.H q :=
    ePush.addCommGroupIsoToAddEquiv.trans
      (_root_.MazurTorsion.AlgebraicGeometry.CoherentCohomology.ExtAdjunction.postcompIsoAddEquiv
        eSheaf q)
  have hTarget :=
    hb n hn q hq
  exact
    ⟨fun x y =>
      E.injective
        (hTarget.elim (E x) (E y))⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace.SerreTwist

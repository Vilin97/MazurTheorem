/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveSerreTwistInteger
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAffineQuasicoherent
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverEpimorphism

/-!
# Detecting epimorphisms on the standard projective cover

The standard coordinate charts jointly detect morphisms of module sheaves.
In particular, a morphism which is an epimorphism after pullback to every
standard chart is an epimorphism globally.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

variable (k : Type) [CommRing k] (d : ℕ)

/-- Pullback to the standard coordinate charts is jointly faithful on
morphisms of module sheaves. -/
theorem standardChartPullback_jointly_faithful
    {M N : (scheme k d).Modules} {f g : M ⟶ N}
    (h : ∀ i,
      (Scheme.Modules.pullback ((SerreTwist.cover k d).f i)).map f =
        (Scheme.Modules.pullback
          ((SerreTwist.cover k d).f i)).map g) :
    f = g := by
  letI :
      (Scheme.Modules.restrictFunctor
        (SerreTwist.cover k d).fromGlued).IsEquivalence :=
    inferInstanceAs
      ((Scheme.Modules.restrictFunctor
        (asIso
          (SerreTwist.cover k d).fromGlued).hom).IsEquivalence)
  letI :
      (Scheme.Modules.pullback
        (SerreTwist.cover k d).fromGlued).IsEquivalence :=
    Functor.isEquivalence_of_iso
      (Scheme.Modules.restrictFunctorIsoPullback
        (SerreTwist.cover k d).fromGlued)
  apply
    (Scheme.Modules.pullback
      (SerreTwist.cover k d).fromGlued).map_injective
  apply
    Scheme.Modules.pullback_map_jointly_faithful
      (SerreTwist.glueData k d)
  intro i
  change Fin (d + 1) at i
  let A :=
    Scheme.Modules.pullbackComp
      ((SerreTwist.glueData k d).ι i)
      (SerreTwist.cover k d).fromGlued
  apply (cancel_mono (A.hom.app N)).1
  change
    (Scheme.Modules.pullback
          (SerreTwist.cover k d).fromGlued ⋙
        Scheme.Modules.pullback
          ((SerreTwist.glueData k d).ι i)).map f ≫
        A.hom.app N =
      (Scheme.Modules.pullback
          (SerreTwist.cover k d).fromGlued ⋙
        Scheme.Modules.pullback
          ((SerreTwist.glueData k d).ι i)).map g ≫
        A.hom.app N
  rw [A.hom.naturality f, A.hom.naturality g]
  apply congrArg (fun q => A.hom.app M ≫ q)
  let B :=
    Scheme.Modules.pullbackCongr
      ((SerreTwist.cover k d).ι_fromGlued i)
  apply (cancel_mono (B.hom.app N)).1
  rw [B.hom.naturality f, B.hom.naturality g]
  exact congrArg (fun q => B.hom.app M ≫ q) (h i)

/-- A morphism of module sheaves on projective space is an epimorphism if
its pullback to every standard chart is an epimorphism. -/
theorem epi_of_standardChartPullback_epi
    {M N : (scheme k d).Modules} (f : M ⟶ N)
    (hf : ∀ i,
      Epi
        ((Scheme.Modules.pullback
          ((SerreTwist.cover k d).f i)).map f)) :
    Epi f := by
  constructor
  intro Z g h e
  apply standardChartPullback_jointly_faithful k d
  intro i
  letI :
      Epi
        ((Scheme.Modules.pullback
          ((SerreTwist.cover k d).f i)).map f) :=
    hf i
  apply
    (cancel_epi
      ((Scheme.Modules.pullback
        ((SerreTwist.cover k d).f i)).map f)).1
  simpa only [Functor.map_comp] using
    congrArg
      (fun q =>
        (Scheme.Modules.pullback
          ((SerreTwist.cover k d).f i)).map q) e

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

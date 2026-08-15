/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineFiniteSections
import MazurTorsion.Upstream.CoherentCohomologyFinite.QuasicoherentKernel
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finite affine sections of a quasicoherent kernel

On a Noetherian spectrum, global sections are left exact.  The global
sections of a kernel therefore inject into the finite module of global
sections of its source.
-/


universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}}

/--
The global sections of the kernel of a morphism between finite-type
quasicoherent modules on a Noetherian spectrum form a finite module.
-/
theorem finiteTopSections_kernel
    [IsNoetherianRing (R : Type u)]
    {M N : (Spec R).Modules} (f : M ⟶ N)
    [M.IsFiniteType] [N.IsFiniteType]
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Module.Finite R Γ(kernel f, ⊤) := by
  letI : (kernel f).IsQuasicoherent :=
    isQuasicoherent_kernel_coherentCohomology f
  letI : Module.Finite R (moduleSpecΓFunctor.obj M) :=
    finite_top_sections_of_isFiniteType_isQuasicoherent M
  letI : _root_.IsNoetherian R (moduleSpecΓFunctor.obj M) :=
    isNoetherian_of_isNoetherianRing_of_finite R
      (moduleSpecΓFunctor.obj M)
  letI :
      (moduleSpecΓFunctor (R := R)).IsRightAdjoint :=
    (tilde.adjunction (R := R)).isRightAdjoint
  let g :=
    moduleSpecΓFunctor.map (kernel.ι f)
  have hg : Function.Injective g.hom := by
    haveI : Mono (kernel.ι f) :=
      equalizer.ι_mono
    haveI : Mono g :=
      Functor.map_mono
        (moduleSpecΓFunctor (R := R))
        (kernel.ι f)
    exact
      (ModuleCat.mono_iff_injective g).mp inferInstance
  exact
    Module.Finite.of_injective g.hom hg

end AlgebraicGeometry.Scheme.Modules

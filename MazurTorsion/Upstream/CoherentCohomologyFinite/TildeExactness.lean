/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.TildeStalkExactness
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Exactness of the affine tilde functor

The functor `M ↦ M̃` from modules over `R` to modules on `Spec R`
preserves monomorphisms because localization is injective on an
injective map and monomorphisms of sheaves can be checked stalkwise.
Since tilde is a left adjoint, it also preserves cokernels.  The
standard abelian-category criterion then gives preservation of finite
limits.
-/


universe u

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}}

/--
An injective map of modules induces an injective map on sections of the
associated sheaves over every open.
-/
theorem tildeMap_app_injective {M N : ModuleCat R}
    (f : M ⟶ N) (hf : Function.Injective f.hom)
    (U : (Spec (.of R)).Opens) :
    Function.Injective ((tilde.map f).app U) := by
  let F : TopCat.Sheaf Ab (Spec (.of R)) :=
    ⟨(tilde M).presheaf, Scheme.Modules.isSheaf (tilde M)⟩
  apply TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective
    (F := F)
    ((Scheme.Modules.toPresheaf (Spec (.of R))).map
      (tilde.map f))
    U
  intro x hx
  exact tildeStalkMapₗ_injective f hf x

/-- The affine tilde functor preserves monomorphisms. -/
noncomputable instance tildeFunctor_preservesMonomorphisms :
    (tilde.functor R).PreservesMonomorphisms where
  preserves f hf := by
    apply
      (Scheme.Modules.toPresheaf (Spec (.of R))).mono_of_mono_map
    apply
      (NatTrans.mono_iff_mono_app
        ((Scheme.Modules.toPresheaf (Spec (.of R))).map
          ((tilde.functor R).map f))).mpr
    intro U
    apply ConcreteCategory.mono_of_injective
    apply tildeMap_app_injective f
    · exact (ModuleCat.mono_iff_injective f).mp hf

/-- The affine tilde functor preserves finite limits. -/
noncomputable instance tildeFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (tilde.functor R) := by
  haveI : (tilde.functor R).PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels
      (tilde.functor R)
  exact
    (tilde.functor R).preservesFiniteLimits_of_preservesHomology

end AlgebraicGeometry

/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Restriction of scalars along a surjection

An additive map between modules over the target of a surjective ring
homomorphism is linear over the target as soon as it is linear over the
source.  Consequently restriction of scalars is fully faithful.
-/

open CategoryTheory

universe v u₁ u₂

namespace ModuleCat

variable {R : Type u₁} {S : Type u₂} [Ring R] [Ring S]

/--
Restriction of scalars along a surjective ring homomorphism is fully
faithful.
-/
noncomputable def restrictScalarsFullyFaithfulOfSurjective
    (f : R →+* S) (hf : Function.Surjective f) :
    (restrictScalars.{v} f).FullyFaithful where
  preimage {M N} g :=
    ModuleCat.ofHom
      { toFun := g
        map_add' := g.hom.map_add
        map_smul' := by
          intro s m
          obtain ⟨r, rfl⟩ := hf s
          exact g.hom.map_smul r m }
  map_preimage _ := rfl
  preimage_map _ := rfl

end ModuleCat

namespace ModuleCat

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S]

/--
The extension--restriction counit is an isomorphism for a surjective
homomorphism.
-/
theorem isIso_extendRestrictScalars_counit_app_of_surjective
    (f : R →+* S) (hf : Function.Surjective f)
    (N : ModuleCat.{max u₂ v} S) :
    IsIso ((extendRestrictScalarsAdj f).counit.app N) := by
  letI : (restrictScalars.{max u₂ v} f).Full :=
    (restrictScalarsFullyFaithfulOfSurjective f hf).full
  infer_instance

end ModuleCat

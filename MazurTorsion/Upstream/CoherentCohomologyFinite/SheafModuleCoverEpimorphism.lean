/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleEffectiveDescent

/-!
# Detecting module epimorphisms on a glued open cover

Morphisms of module sheaves on a glued scheme are detected after pullback to
the gluing charts.  Consequently, a morphism which is an epimorphism on every
chart is already an epimorphism globally.
-/

open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- A morphism on a glued scheme is an epimorphism if all of its chart
pullbacks are epimorphisms. -/
theorem epi_of_pullback_epi (D : Scheme.GlueData.{0})
    {M N : D.glued.Modules} (f : M ⟶ N)
    (hf : ∀ i, Epi ((pullback (D.ι i)).map f)) :
    Epi f := by
  constructor
  intro Z g h e
  apply pullback_map_jointly_faithful D
  intro i
  letI : Epi ((pullback (D.ι i)).map f) := hf i
  apply (cancel_epi ((pullback (D.ι i)).map f)).1
  simpa only [Functor.map_comp] using
    congrArg (fun q => (pullback (D.ι i)).map q) e

/-- Dually, a morphism on a glued scheme is a monomorphism if all of its
chart pullbacks are monomorphisms. -/
theorem mono_of_pullback_mono (D : Scheme.GlueData.{0})
    {M N : D.glued.Modules} (f : M ⟶ N)
    (hf : ∀ i, Mono ((pullback (D.ι i)).map f)) :
    Mono f := by
  constructor
  intro Z g h e
  apply pullback_map_jointly_faithful D
  intro i
  letI : Mono ((pullback (D.ι i)).map f) := hf i
  apply (cancel_mono ((pullback (D.ι i)).map f)).1
  simpa only [Functor.map_comp] using
    congrArg (fun q => (pullback (D.ι i)).map q) e

/-- A morphism which is an isomorphism on every gluing chart is an
isomorphism globally. -/
theorem isIso_of_pullback_isIso (D : Scheme.GlueData.{0})
    {M N : D.glued.Modules} (f : M ⟶ N)
    (hf : ∀ i, IsIso ((pullback (D.ι i)).map f)) :
    IsIso f := by
  letI : Mono f :=
    mono_of_pullback_mono D f
      (fun i => @IsIso.mono_of_iso _ _ _ _
        ((pullback (D.ι i)).map f) (hf i))
  letI : Epi f :=
    epi_of_pullback_epi D f
      (fun i => @IsIso.epi_of_iso _ _ _ _
        ((pullback (D.ι i)).map f) (hf i))
  exact isIso_of_mono_of_epi f

end AlgebraicGeometry.Scheme.Modules

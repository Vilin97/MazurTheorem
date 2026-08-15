/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.AffineFiniteSections
import MazurTorsion.Upstream.CoherentCohomologyFinite.SemilinearFiniteTransport
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAffineQuasicoherent
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAffineTildeCounit
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafFiniteTypeRestriction

/-!
# Finite sections on affine open subschemes

Global sections on the open subscheme attached to `U` are naturally
identified with sections over `U`.  Because the coefficient rings are
isomorphic rather than definitionally equal, finite generation is
transported through the resulting semilinear additive equivalence.
-/


open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/--
Finite generation of sections of a restricted module transports to
sections over the image open of an arbitrary open immersion.
-/
theorem finiteSections_image_of_finiteRestrictSections
    (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (U : X.Opens)
    (hfin :
      Module.Finite Γ(X, U)
        Γ(M.restrict f, U)) :
    Module.Finite Γ(Y, f ''ᵁ U)
      Γ(M, f ''ᵁ U) := by
  let σ :
      (Γ(Y, f ''ᵁ U) : Type u) →+*
        Γ(X, U) :=
    (f.appIso U).hom.hom
  have hσ : Function.Surjective σ := by
    intro r
    refine
      ⟨(f.appIso U).inv.hom r, ?_⟩
    simp [σ]
  let e :
      (Γ(M, f ''ᵁ U) : Type u) ≃+
        Γ(M.restrict f, U) :=
    (M.restrictAppIso f U).symm.addCommGroupIsoToAddEquiv
  refine
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.Module.Finite.of_surjectiveSemilinearAddEquiv
      σ hσ e ?_ hfin
  intro r x
  change
    (M.restrictAppIso f U).inv.hom
        ((M.smul r).hom x) =
      ((M.restrict f).smul
        ((f.appIso U).hom.hom r)).hom
          ((M.restrictAppIso f U).inv.hom x)
  exact
    congr($(smul_restrictAppIso_inv f M U r) x)

/--
Finite generation of sections over an image open transports back to
the corresponding sections of a restricted module.
-/
theorem finiteRestrictSections_of_finiteImageSections
    (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (U : X.Opens)
    (hfin :
      Module.Finite Γ(Y, f ''ᵁ U)
        Γ(M, f ''ᵁ U)) :
    Module.Finite Γ(X, U)
      Γ(M.restrict f, U) := by
  let σ :
      (Γ(X, U) : Type u) →+*
        Γ(Y, f ''ᵁ U) :=
    (f.appIso U).inv.hom
  have hσ : Function.Surjective σ := by
    intro r
    refine
      ⟨(f.appIso U).hom.hom r, ?_⟩
    simp [σ]
  let e :
      (Γ(M.restrict f, U) : Type u) ≃+
        Γ(M, f ''ᵁ U) :=
    (M.restrictAppIso f U).addCommGroupIsoToAddEquiv
  refine
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.Module.Finite.of_surjectiveSemilinearAddEquiv
      σ hσ e ?_ hfin
  intro r x
  change
    (M.restrictAppIso f U).hom.hom
        (((M.restrict f).smul r).hom x) =
      (M.smul ((f.appIso U).inv.hom r)).hom
        ((M.restrictAppIso f U).hom.hom x)
  exact
    congr($(smul_restrictAppIso_hom f M U r) x)

/--
Global sections of a finite-type quasicoherent module on an affine
scheme form a finite module.
-/
theorem finiteTopSections_of_affineScheme
    [IsAffine X] (M : X.Modules)
    [M.IsFiniteType] [M.IsQuasicoherent] :
    Module.Finite Γ(X, ⊤) Γ(M, ⊤) := by
  let N : (Spec Γ(X, ⊤)).Modules :=
    M.restrict X.isoSpec.inv
  haveI : N.IsFiniteType := inferInstance
  haveI : N.IsQuasicoherent := inferInstance
  have h :=
    finite_top_sections_of_isFiniteType_isQuasicoherent N
  have hNatural :
      Module.Finite
        Γ(Spec Γ(X, ⊤), ⊤) Γ(N, ⊤) := by
    let σ :
        (Γ(Spec Γ(X, ⊤), ⊤) : Type u) →+*
          Γ(X, ⊤) :=
      (Scheme.ΓSpecIso Γ(X, ⊤)).hom.hom
    have hσ : Function.Surjective σ := by
      intro r
      refine
        ⟨(Scheme.ΓSpecIso Γ(X, ⊤)).inv.hom r,
          ?_⟩
      simp [σ]
    let e :
        (Γ(N, ⊤) : Type u) ≃+
          Γ(N, ⊤) :=
      AddEquiv.refl _
    refine
      MazurTorsion.AlgebraicGeometry.CoherentCohomology.Module.Finite.of_surjectiveSemilinearAddEquiv
        σ hσ e ?_ h
    intro r x
    change
      r • x =
        (Scheme.ΓSpecIso Γ(X, ⊤)).hom.hom r • x
    rw [Scheme.Modules.smul_Spec_def]
    have hmap :
        (Spec Γ(X, ⊤)).presheaf.map
          (Opens.leTop
            (⊤ : (Spec Γ(X, ⊤)).Opens)).op =
          𝟙 _ := by
      rw [show
        Opens.leTop
            (⊤ : (Spec Γ(X, ⊤)).Opens) =
          𝟙 (⊤ : (Spec Γ(X, ⊤)).Opens) from rfl]
      exact (Spec Γ(X, ⊤)).presheaf.map_id _
    rw [hmap]
    have hcancel :
        (Scheme.ΓSpecIso Γ(X, ⊤)).inv.hom
            ((Scheme.ΓSpecIso Γ(X, ⊤)).hom.hom r) =
          r := by
      have h0 :=
        (Scheme.ΓSpecIso Γ(X, ⊤)).hom_inv_id
      have h1 :=
        congrArg
          (fun φ :
              Γ(Spec Γ(X, ⊤), ⊤) ⟶
                Γ(Spec Γ(X, ⊤), ⊤) =>
            φ.hom r) h0
      simpa only [CommRingCat.hom_comp,
        RingHom.comp_apply, CommRingCat.hom_id,
        RingHom.id_apply] using h1
    simp only [ConcreteCategory.id_apply, hcancel]
  have hImage :=
    finiteSections_image_of_finiteRestrictSections
      X.isoSpec.inv M
        (⊤ : (Spec Γ(X, ⊤)).Opens)
        hNatural
  have himage :
      X.isoSpec.inv ''ᵁ
          (⊤ : (Spec Γ(X, ⊤)).Opens) =
        (⊤ : X.Opens) := by
    rw [X.isoSpec.inv.image_top_eq_opensRange,
      X.isoSpec.inv.opensRange_of_isIso]
  rw [← himage]
  exact hImage

/--
Finite generation of top sections after restriction to an open subscheme
implies finite generation of sections over the original open.
-/
theorem finiteSections_of_finiteRestrictTopSections
    (M : X.Modules) (U : X.Opens)
    (hfin :
      Module.Finite Γ(U, ⊤)
        Γ(M.restrict U.ι, ⊤)) :
    Module.Finite Γ(X, U) Γ(M, U) := by
  have hImage :=
    finiteSections_image_of_finiteRestrictSections
      U.ι M (⊤ : (↑U : Scheme.{u}).Opens) hfin
  have himage :
      U.ι ''ᵁ
          (⊤ : (↑U : Scheme.{u}).Opens) = U := by
    rw [U.ι.image_top_eq_opensRange,
      Scheme.Opens.opensRange_ι]
  rw [← himage]
  exact hImage

/--
Sections of a finite-type quasicoherent module over an affine open are
finite over the corresponding ring of functions.
-/
theorem finiteSections_of_isAffineOpen
    (M : X.Modules) [M.IsFiniteType]
    [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) :
    Module.Finite Γ(X, U) Γ(M, U) := by
  letI : IsAffine (↑U : Scheme.{u}) := hU
  apply
    finiteSections_of_finiteRestrictTopSections
      M U
  exact finiteTopSections_of_affineScheme
    (M.restrict U.ι)

end AlgebraicGeometry.Scheme.Modules

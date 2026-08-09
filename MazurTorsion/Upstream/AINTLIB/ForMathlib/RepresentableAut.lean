/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Ticket T-Q6d.
-/
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Endomorphism

/-!
# Transport of endomorphisms and automorphisms along representability

For a representable presheaf `F : Cᵒᵖ ⥤ Type v` with representation
`r : F.RepresentableBy Y`, natural endomorphisms of `F` transport to endomorphisms
of `Y` (`RepresentableBy.transportHom`), monoidally
(`transportHom_id`/`transportHom_comp`), hence group actions on `F` transport to
group actions on the representing object (`RepresentableBy.autMulHom : Aut F →* Aut Y`).

This is the Yoneda step of Katz–Mazur 4.7 ("Let `G` operate upon `𝕸(𝒫,δ)` through
its action on `δ`", KM p. 112); it is stated for arbitrary categories.

The characterizing property is `homEquiv_comp_transportHom`:
`r.homEquiv (v ≫ r.transportHom η) = η.app _ (r.homEquiv v)`.
-/

universe v v₁ u₁

open CategoryTheory Opposite

namespace CategoryTheory.Functor.RepresentableBy

variable {C : Type u₁} [Category.{v₁} C] {F : Cᵒᵖ ⥤ Type v} {Y : C}

/-- Transport a natural endomorphism of `F` to an endomorphism of a representing
object: the image of the universal element under `η`, reflected through the
representing bijection. -/
noncomputable def transportHom (r : F.RepresentableBy Y) (η : F ⟶ F) : Y ⟶ Y :=
  r.homEquiv.symm (η.app (op Y) (r.homEquiv (𝟙 Y)))

/-- The characterizing property of `transportHom`: postcomposition with the
transported endomorphism realizes `η` under the representing bijections. -/
theorem homEquiv_comp_transportHom (r : F.RepresentableBy Y) (η : F ⟶ F)
    {X : C} (v : X ⟶ Y) :
    r.homEquiv (v ≫ r.transportHom η) = η.app (op X) (r.homEquiv v) := by
  rw [r.homEquiv_comp, transportHom, Equiv.apply_symm_apply,
    show r.homEquiv v = F.map v.op (r.homEquiv (𝟙 Y)) from by
      conv_lhs => rw [← Category.comp_id v]
      exact r.homEquiv_comp v (𝟙 Y)]
  exact (NatTrans.naturality_apply η v.op _).symm

@[simp]
theorem transportHom_id (r : F.RepresentableBy Y) :
    r.transportHom (𝟙 F) = 𝟙 Y := by
  apply r.homEquiv.injective
  have h := r.homEquiv_comp_transportHom (𝟙 F) (𝟙 Y)
  rw [Category.id_comp] at h
  rw [h]
  rfl

theorem transportHom_comp (r : F.RepresentableBy Y) (η θ : F ⟶ F) :
    r.transportHom (η ≫ θ) = r.transportHom η ≫ r.transportHom θ := by
  apply r.homEquiv.injective
  calc r.homEquiv (r.transportHom (η ≫ θ))
      = (η ≫ θ).app (op Y) (r.homEquiv (𝟙 Y)) := by
        have h := r.homEquiv_comp_transportHom (η ≫ θ) (𝟙 Y)
        rwa [Category.id_comp] at h
    _ = θ.app (op Y) (η.app (op Y) (r.homEquiv (𝟙 Y))) := rfl
    _ = θ.app (op Y) (r.homEquiv (r.transportHom η)) := by
        rw [transportHom, Equiv.apply_symm_apply]
    _ = r.homEquiv (r.transportHom η ≫ r.transportHom θ) :=
        (r.homEquiv_comp_transportHom θ _).symm

/-- **Automorphisms of a representable presheaf transport to automorphisms of the
representing object**, as a group homomorphism. This is the Yoneda step of
KM 4.7's "Let `G` operate upon `𝕸(𝒫,δ)` through its action on `δ`": a group
action `G →* Aut F` composes with this to give `G →* Aut Y`. -/
noncomputable def autMulHom (r : F.RepresentableBy Y) : Aut F →* Aut Y where
  toFun e :=
    { hom := r.transportHom e.hom
      inv := r.transportHom e.inv
      hom_inv_id := by
        rw [← r.transportHom_comp, e.hom_inv_id, r.transportHom_id]
      inv_hom_id := by
        rw [← r.transportHom_comp, e.inv_hom_id, r.transportHom_id] }
  map_one' := by
    ext
    exact r.transportHom_id
  map_mul' e₁ e₂ := by
    ext
    exact r.transportHom_comp e₂.hom e₁.hom

@[simp]
theorem autMulHom_apply_hom (r : F.RepresentableBy Y) (e : Aut F) :
    (r.autMulHom e).hom = r.transportHom e.hom := rfl

end CategoryTheory.Functor.RepresentableBy

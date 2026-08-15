/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteProjectiveProducts

/-!
# Maps into finite products of projective models

`FiniteProjectiveProducts` constructs projective iterated fiber
products.  This file carries along a compatible map from one fixed
scheme while forming those products.  The result is a projective model
over `Spec k` together with the diagonal map into all factors.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

namespace StandardProjectiveModel

variable {k : Type u} [CommRing k]

/-- A morphism from `T` to a projective model, compatible with fixed
structural map `t : T ⟶ Spec k`. -/
structure MapFrom
    (P : StandardProjectiveModel k)
    {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of k)) where
  hom : T ⟶ P.carrier
  overBase : hom ≫ P.toSpec = t

namespace MapFrom

variable {T : Scheme.{u}}
variable {t : T ⟶ Spec (CommRingCat.of k)}

/-- Combine two compatible maps by the universal property of the fiber
product. -/
def fiberProduct
    (hsegre : StandardSegreEmbeddings k)
    {P Q : StandardProjectiveModel k}
    (p : P.MapFrom t) (q : Q.MapFrom t) :
    (P.fiberProduct hsegre Q).MapFrom t where
  hom :=
    pullback.lift p.hom q.hom
      (p.overBase.trans q.overBase.symm)
  overBase := by
    change
      pullback.lift p.hom q.hom
          (p.overBase.trans q.overBase.symm) ≫
        pullback.fst P.toSpec Q.toSpec ≫ P.toSpec =
          t
    rw [pullback.lift_fst_assoc, p.overBase]

end MapFrom

/-- A projective model equipped with a compatible map from `T`. -/
abbrev ModelWithMapFrom
    (k : Type u) [CommRing k]
    {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of k)) :=
  Σ P : StandardProjectiveModel k, P.MapFrom t

/-- Iteratively combine a head projective model with a list of further
projective models, carrying the map from `T` throughout. -/
def iteratedFiberProductWithMap
    (hsegre : StandardSegreEmbeddings k)
    {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of k)} :
    ModelWithMapFrom k t →
      List (ModelWithMapFrom k t) →
        ModelWithMapFrom k t
  | P, [] => P
  | ⟨P, p⟩, ⟨Q, q⟩ :: tail =>
      iteratedFiberProductWithMap hsegre
        ⟨P.fiberProduct hsegre Q,
          p.fiberProduct hsegre q⟩
        tail

/-- A chosen nonempty finite family of compatible maps has a diagonal
map into a projective iterated fiber product. -/
def finiteFiberProductWithMap
    (hsegre : StandardSegreEmbeddings k)
    {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of k)}
    {ι : Type u} [Fintype ι] [Nonempty ι]
    (P : ι → StandardProjectiveModel k)
    (p : ∀ i, (P i).MapFrom t) :
    ModelWithMapFrom k t := by
  classical
  let i₀ : ι := Classical.choice inferInstance
  exact
    iteratedFiberProductWithMap hsegre
      ⟨P i₀, p i₀⟩
      (((Finset.univ.erase i₀).toList).map
        (fun i => ⟨P i, p i⟩))

/-- The model underlying the finite diagonal construction is
projective over the coefficient ring. -/
theorem finiteFiberProductWithMap_projective
    (hsegre : StandardSegreEmbeddings k)
    {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of k)}
    {ι : Type u} [Fintype ι] [Nonempty ι]
    (P : ι → StandardProjectiveModel k)
    (p : ∀ i, (P i).MapFrom t) :
    IsProjectiveFactorization
      (finiteFiberProductWithMap hsegre P p).1.toSpec :=
  (finiteFiberProductWithMap hsegre P p).1.projective

end StandardProjectiveModel

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

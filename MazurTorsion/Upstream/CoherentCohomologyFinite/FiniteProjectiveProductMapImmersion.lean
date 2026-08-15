/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteProjectiveProductMaps

/-!
# Immersions into finite products of projective models

The finite-product construction used in Chow's lemma carries a map from
one fixed source.  If its first component is an immersion, then the
induced map to every successive fiber product is an immersion as well:
composition with the first projection recovers that component.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

namespace StandardProjectiveModel

variable {k : Type u} [CommRing k]
variable {T : Scheme.{u}}
variable {t : T ⟶ Spec (CommRingCat.of k)}

namespace MapFrom

/-- The diagonal map to a binary fiber product is an immersion whenever
its first component is. -/
theorem isImmersion_fiberProduct_of_left
    (hsegre : StandardSegreEmbeddings k)
    {P Q : StandardProjectiveModel k}
    (p : P.MapFrom t) (q : Q.MapFrom t)
    (hp : IsImmersion p.hom) :
    IsImmersion (p.fiberProduct hsegre q).hom := by
  letI :
      IsImmersion
        ((p.fiberProduct hsegre q).hom ≫
          pullback.fst P.toSpec Q.toSpec) := by
    change
      IsImmersion
        (pullback.lift p.hom q.hom
            (p.overBase.trans q.overBase.symm) ≫
          pullback.fst P.toSpec Q.toSpec)
    rw [pullback.lift_fst]
    exact hp
  exact
    IsImmersion.of_comp
      (p.fiberProduct hsegre q).hom
      (pullback.fst P.toSpec Q.toSpec)

end MapFrom

/-- Iterating fiber products preserves immersion of the distinguished
map from the source. -/
theorem isImmersion_iteratedFiberProductWithMap
    (hsegre : StandardSegreEmbeddings k)
    (P : ModelWithMapFrom k t)
    (tail : List (ModelWithMapFrom k t))
    (hP : IsImmersion P.2.hom) :
    IsImmersion
      (iteratedFiberProductWithMap hsegre P tail).2.hom := by
  induction tail generalizing P with
  | nil =>
      exact hP
  | cons Q tail ih =>
      apply ih
      exact
        MapFrom.isImmersion_fiberProduct_of_left
          hsegre P.2 Q.2 hP

/-- A finite diagonal map is an immersion if each of its component
maps is an immersion. -/
theorem isImmersion_finiteFiberProductWithMap
    (hsegre : StandardSegreEmbeddings k)
    {ι : Type u} [Fintype ι] [Nonempty ι]
    (P : ι → StandardProjectiveModel k)
    (p : ∀ i, (P i).MapFrom t)
    (hp : ∀ i, IsImmersion (p i).hom) :
    IsImmersion
      (finiteFiberProductWithMap hsegre P p).2.hom := by
  classical
  let i₀ : ι := Classical.choice inferInstance
  exact
    isImmersion_iteratedFiberProductWithMap
      hsegre ⟨P i₀, p i₀⟩
      (((Finset.univ.erase i₀).toList).map
        (fun i => ⟨P i, p i⟩))
      (hp i₀)

end StandardProjectiveModel

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

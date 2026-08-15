/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.FiniteProjectiveProductMaps

/-!
# Projections from the chosen finite projective product

The iterated fiber-product construction used in Chow's lemma originally
retained only its diagonal map from the common source.  This file records
the equally important projections back to every labeled factor.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

namespace StandardProjectiveModel

variable {k : Type u} [CommRing k]
variable {T : Scheme.{u}}
variable {t : T ⟶ Spec (CommRingCat.of k)}

/-- A projection between projective models equipped with maps from the
same source, compatible both with the base and with those source maps. -/
structure ModelWithMapProjection
    (A B : ModelWithMapFrom k t) where
  hom : A.1.carrier ⟶ B.1.carrier
  overBase : hom ≫ B.1.toSpec = A.1.toSpec
  from_hom : A.2.hom ≫ hom = B.2.hom

namespace ModelWithMapProjection

/-- Identity projection. -/
def refl (A : ModelWithMapFrom k t) :
    ModelWithMapProjection A A where
  hom := 𝟙 _
  overBase := Category.id_comp _
  from_hom := Category.comp_id _

/-- Compose compatible projections. -/
def comp
    {A B C : ModelWithMapFrom k t}
    (e : ModelWithMapProjection A B)
    (q : ModelWithMapProjection B C) :
    ModelWithMapProjection A C where
  hom := e.hom ≫ q.hom
  overBase := by
    rw [Category.assoc, q.overBase, e.overBase]
  from_hom := by
    rw [← Category.assoc, e.from_hom, q.from_hom]

end ModelWithMapProjection

namespace MapFrom

/-- First projection from a binary fiber product with its diagonal
source map. -/
def fiberProductFstProjection
    (hsegre : StandardSegreEmbeddings k)
    {P Q : StandardProjectiveModel k}
    (p : P.MapFrom t) (q : Q.MapFrom t) :
    ModelWithMapProjection
      ⟨P.fiberProduct hsegre Q,
        p.fiberProduct hsegre q⟩
      ⟨P, p⟩ where
  hom := pullback.fst P.toSpec Q.toSpec
  overBase := rfl
  from_hom := pullback.lift_fst _ _ _

/-- Second projection from a binary fiber product with its diagonal
source map. -/
def fiberProductSndProjection
    (hsegre : StandardSegreEmbeddings k)
    {P Q : StandardProjectiveModel k}
    (p : P.MapFrom t) (q : Q.MapFrom t) :
    ModelWithMapProjection
      ⟨P.fiberProduct hsegre Q,
        p.fiberProduct hsegre q⟩
      ⟨Q, q⟩ where
  hom := pullback.snd P.toSpec Q.toSpec
  overBase := pullback.condition.symm
  from_hom := pullback.lift_snd _ _ _

end MapFrom

/-- The chosen iterated product always projects back to its head
factor. -/
def iteratedFiberProductWithMapHeadProjection
    (hsegre : StandardSegreEmbeddings k)
    (A : ModelWithMapFrom k t) :
    (tail : List (ModelWithMapFrom k t)) →
      ModelWithMapProjection
        (iteratedFiberProductWithMap hsegre A tail)
        A
  | [] => ModelWithMapProjection.refl A
  | B :: tail =>
      (iteratedFiberProductWithMapHeadProjection
        hsegre
        ⟨A.1.fiberProduct hsegre B.1,
          A.2.fiberProduct hsegre B.2⟩
        tail).comp
          (MapFrom.fiberProductFstProjection
            hsegre A.2 B.2)

/-- Every factor occurring in the list has a compatible projection from
the chosen iterated fiber product. -/
theorem nonempty_iteratedFiberProductWithMapProjection_of_mem
    (hsegre : StandardSegreEmbeddings k)
    (A B : ModelWithMapFrom k t)
    (tail : List (ModelWithMapFrom k t))
    (hB : B ∈ A :: tail) :
    Nonempty
      (ModelWithMapProjection
        (iteratedFiberProductWithMap hsegre A tail)
        B) := by
  classical
  induction tail generalizing A B with
  | nil =>
      simp only [List.mem_singleton] at hB
      subst B
      exact
        ⟨iteratedFiberProductWithMapHeadProjection
          hsegre A []⟩
  | cons C tail ih =>
      simp only [List.mem_cons] at hB
      rcases hB with hBA | hBC | hBtail
      · subst B
        exact
          ⟨iteratedFiberProductWithMapHeadProjection
            hsegre A (C :: tail)⟩
      · subst B
        let AC : ModelWithMapFrom k t :=
          ⟨A.1.fiberProduct hsegre C.1,
            A.2.fiberProduct hsegre C.2⟩
        exact
          ⟨(iteratedFiberProductWithMapHeadProjection
              hsegre AC tail).comp
            (MapFrom.fiberProductSndProjection
              hsegre A.2 C.2)⟩
      · exact
          ih
            ⟨A.1.fiberProduct hsegre C.1,
              A.2.fiberProduct hsegre C.2⟩
            B (List.mem_cons_of_mem _ hBtail)

/-- The chosen finite product has a compatible projection to every
labeled factor. -/
theorem nonempty_finiteFiberProductWithMapProjection
    (hsegre : StandardSegreEmbeddings k)
    {ι : Type u} [Fintype ι] [Nonempty ι]
    (P : ι → StandardProjectiveModel k)
    (p : ∀ i, (P i).MapFrom t)
    (i : ι) :
    Nonempty
      (ModelWithMapProjection
        (finiteFiberProductWithMap hsegre P p)
        ⟨P i, p i⟩) := by
  classical
  let i₀ : ι := Classical.choice inferInstance
  apply
    nonempty_iteratedFiberProductWithMapProjection_of_mem
      hsegre ⟨P i₀, p i₀⟩ ⟨P i, p i⟩
      (((Finset.univ.erase i₀).toList).map
        (fun j => ⟨P j, p j⟩))
  by_cases hi : i = i₀
  · subst i
    exact List.mem_cons_self
  · right
    apply List.mem_map.mpr
    refine ⟨i, ?_, rfl⟩
    simp [hi]

/-- A chosen compatible projection from the finite product to a labeled
factor. -/
def finiteFiberProductWithMapProjection
    (hsegre : StandardSegreEmbeddings k)
    {ι : Type u} [Fintype ι] [Nonempty ι]
    (P : ι → StandardProjectiveModel k)
    (p : ∀ i, (P i).MapFrom t)
    (i : ι) :
    ModelWithMapProjection
      (finiteFiberProductWithMap hsegre P p)
      ⟨P i, p i⟩ :=
  Classical.choice
    (nonempty_finiteFiberProductWithMapProjection
      hsegre P p i)

end StandardProjectiveModel

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveFactorization

/-!
# Products of projective factorizations before the Segre embedding

The fiber product of two schemes with closed embeddings into projective
space embeds as a closed subscheme of the corresponding product of
projective spaces.  This entire "biprojective" layer is available at the
exact Mathlib pin.

The conversion from a product of projective spaces to one projective
space is isolated as `StandardSegreEmbeddings`.  No scheme-level Segre
embedding is present in Mathlib, LeanPool, or TauCeti at this pin.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-- The product of two standard projective spaces over `Spec k`. -/
abbrev binaryProjectiveScheme
    (k : Type u) [CommRing k] (m n : ℕ) :
    Scheme.{u} :=
  pullback (toSpec k m) (toSpec k n)

/-- The structural morphism of a binary product of projective spaces. -/
def binaryProjectiveToSpec
    (k : Type u) [CommRing k] (m n : ℕ) :
    binaryProjectiveScheme k m n ⟶
      Spec (CommRingCat.of k) :=
  pullback.fst (toSpec k m) (toSpec k n) ≫
    toSpec k m

@[reassoc]
lemma binaryProjective_projection_condition
    (k : Type u) [CommRing k] (m n : ℕ) :
    pullback.snd (toSpec k m) (toSpec k n) ≫
        toSpec k n =
      binaryProjectiveToSpec k m n := by
  exact pullback.condition.symm

instance isProper_binaryProjectiveToSpec
    (k : Type u) [CommRing k] (m n : ℕ) :
    IsProper (binaryProjectiveToSpec k m n) := by
  dsimp only [binaryProjectiveToSpec]
  infer_instance

/-- A factorization through a closed subscheme of a product of two
standard projective spaces. -/
def IsBiprojectiveFactorization
    {X : Scheme.{u}} {k : Type u} [CommRing k]
    (f : X ⟶ Spec (CommRingCat.of k)) : Prop :=
  ∃ (m n : ℕ)
    (i : X ⟶ binaryProjectiveScheme k m n),
    IsClosedImmersion i ∧
      i ≫ binaryProjectiveToSpec k m n = f

namespace IsBiprojectiveFactorization

/-- A biprojective factorization is proper, independently of any Segre
embedding. -/
theorem isProper
    {X : Scheme.{u}} {k : Type u} [CommRing k]
    {f : X ⟶ Spec (CommRingCat.of k)}
    (h : IsBiprojectiveFactorization f) :
    IsProper f := by
  obtain ⟨m, n, i, hi, hif⟩ := h
  letI : IsClosedImmersion i := hi
  rw [← hif]
  infer_instance

end IsBiprojectiveFactorization

/-- The map on fiber products induced by two compatible projective
embeddings. -/
def projectiveFiberProductMap
    {k : Type u} [CommRing k]
    {X Y : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)}
    {g : Y ⟶ Spec (CommRingCat.of k)}
    {m n : ℕ}
    (i : X ⟶ scheme k m)
    (j : Y ⟶ scheme k n)
    (hi : i ≫ toSpec k m = f)
    (hj : j ≫ toSpec k n = g) :
    pullback f g ⟶ binaryProjectiveScheme k m n :=
  pullback.map f g (toSpec k m) (toSpec k n)
    i j (𝟙 _) (by simpa using hi.symm) (by simpa using hj.symm)

@[reassoc (attr := simp)]
lemma projectiveFiberProductMap_fst
    {k : Type u} [CommRing k]
    {X Y : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)}
    {g : Y ⟶ Spec (CommRingCat.of k)}
    {m n : ℕ}
    (i : X ⟶ scheme k m)
    (j : Y ⟶ scheme k n)
    (hi : i ≫ toSpec k m = f)
    (hj : j ≫ toSpec k n = g) :
    projectiveFiberProductMap i j hi hj ≫
      pullback.fst (toSpec k m) (toSpec k n) =
      pullback.fst f g ≫ i := by
  dsimp only [projectiveFiberProductMap, pullback.map]
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma projectiveFiberProductMap_snd
    {k : Type u} [CommRing k]
    {X Y : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)}
    {g : Y ⟶ Spec (CommRingCat.of k)}
    {m n : ℕ}
    (i : X ⟶ scheme k m)
    (j : Y ⟶ scheme k n)
    (hi : i ≫ toSpec k m = f)
    (hj : j ≫ toSpec k n = g) :
    projectiveFiberProductMap i j hi hj ≫
      pullback.snd (toSpec k m) (toSpec k n) =
      pullback.snd f g ≫ j := by
  dsimp only [projectiveFiberProductMap, pullback.map]
  exact pullback.lift_snd _ _ _

/-- Products of closed projective embeddings remain closed before the
Segre step. -/
theorem isClosedImmersion_projectiveFiberProductMap
    {k : Type u} [CommRing k]
    {X Y : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)}
    {g : Y ⟶ Spec (CommRingCat.of k)}
    {m n : ℕ}
    (i : X ⟶ scheme k m)
    (j : Y ⟶ scheme k n)
    (hi : i ≫ toSpec k m = f)
    (hj : j ≫ toSpec k n = g)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    IsClosedImmersion
      (projectiveFiberProductMap i j hi hj) := by
  letI hmul : MorphismProperty.IsMultiplicative
      (@IsClosedImmersion : MorphismProperty Scheme.{u}) :=
    inferInstance
  letI : MorphismProperty.IsStableUnderComposition
      (@IsClosedImmersion : MorphismProperty Scheme.{u}) :=
    hmul.toIsStableUnderComposition
  exact
    MorphismProperty.pullbackMap
      (P := @IsClosedImmersion)
      (by infer_instance)
      (by infer_instance)
      (by simpa using hi.symm)
      (by simpa using hj.symm)

/-- The fiber product of two projective factorizations has a canonical
biprojective factorization. -/
theorem isBiprojectiveFactorization_fiberProduct
    {k : Type u} [CommRing k]
    {X Y : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)}
    {g : Y ⟶ Spec (CommRingCat.of k)}
    (hf : IsProjectiveFactorization f)
    (hg : IsProjectiveFactorization g) :
    IsBiprojectiveFactorization
      (pullback.fst f g ≫ f) := by
  obtain ⟨m, i, hi, hif⟩ := hf
  obtain ⟨n, j, hj, hjg⟩ := hg
  letI : IsClosedImmersion i := hi
  letI : IsClosedImmersion j := hj
  let productMap :=
    projectiveFiberProductMap i j hif hjg
  have hproductMap :
      IsClosedImmersion productMap :=
    isClosedImmersion_projectiveFiberProductMap
      i j hif hjg
  refine ⟨m, n, productMap, hproductMap, ?_⟩
  rw [binaryProjectiveToSpec, ← Category.assoc,
    projectiveFiberProductMap_fst i j hif hjg,
    Category.assoc, hif]

/-- A scheme-level Segre interface: every product of two standard
projective spaces admits a closed embedding into one standard projective
space over the same base. -/
def StandardSegreEmbeddings
    (k : Type u) [CommRing k] : Prop :=
  ∀ (m n : ℕ),
    ∃ (d : ℕ)
      (segre :
        binaryProjectiveScheme k m n ⟶ scheme k d),
      IsClosedImmersion segre ∧
      segre ≫ toSpec k d =
        binaryProjectiveToSpec k m n

/-- A scheme-level Segre embedding converts every biprojective
factorization into an ordinary projective factorization. -/
theorem isProjectiveFactorization_of_isBiprojective
    {k : Type u} [CommRing k]
    (hsegre : StandardSegreEmbeddings k)
    {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)}
    (h : IsBiprojectiveFactorization f) :
    IsProjectiveFactorization f := by
  obtain ⟨m, n, i, hi, hif⟩ := h
  obtain ⟨d, segre, hsegreClosed, hsegreBase⟩ :=
    hsegre m n
  letI : IsClosedImmersion i := hi
  letI : IsClosedImmersion segre := hsegreClosed
  exact
    ⟨d, i ≫ segre, inferInstance, by
      rw [Category.assoc, hsegreBase, hif]⟩

/-- Subject only to the scheme-level Segre interface, projective
factorizations are closed under fiber products over `Spec k`. -/
theorem isProjectiveFactorization_fiberProduct
    {k : Type u} [CommRing k]
    (hsegre : StandardSegreEmbeddings k)
    {X Y : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of k)}
    {g : Y ⟶ Spec (CommRingCat.of k)}
    (hf : IsProjectiveFactorization f)
    (hg : IsProjectiveFactorization g) :
    IsProjectiveFactorization
      (pullback.fst f g ≫ f) :=
  isProjectiveFactorization_of_isBiprojective
    hsegre
    (isBiprojectiveFactorization_fiberProduct hf hg)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI Codex
-/

import MazurTorsion.ModularCurve.XZeroRelativeGammaZeroFunctor
import Mathlib.CategoryTheory.Yoneda

/-!
# Coarse moduli interface for locally constant `Gamma_0(N)` families

This module states the precise geometric boundary after construction of the
locally constant `Gamma_0(N)` moduli functor.  A `CoarseModuliSpace` consists
of a scheme, a natural classifying map from family isomorphism classes to its
functor of points, bijectivity on algebraically closed field-valued points,
and the universal factorization property for maps to schemes.

The functor of points is expressed with `uliftYoneda`, since morphisms between
`Scheme.{u}` objects live one universe below the isomorphism-class functor.
The interface therefore records actual morphisms `T ⟶ X`, not a
presentation-level point shadow.  Naturality proves that classification
commutes with arbitrary base change, and the universal property proves that
two coarse moduli schemes are canonically isomorphic.

This is deliberately not a representability claim.  The isomorphism-class
functor has objects with automorphisms, so a coarse space need not represent
it on arbitrary bases.  No instance of `CoarseModuliSpace` is constructed in
this module, and the locally constant locus still omits generalized cyclic
subgroups in characteristics dividing `N`.  The named downstream consumer is
`MazurTorsion.XZeroFortyNine.coarseModuliPointOfOrderFortyNineTorsion`.
-/

noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace MazurTorsion.ModularCurve.XZeroModuli
namespace LocallyConstantGammaZeroFamily

universe u

variable {N : ℕ} [NeZero N]

/-- The scheme-valued-point functor, lifted to the object universe of
`Scheme.{u}`.  Its value at `T` is `ULift (T ⟶ X)`. -/
abbrev SchemePointFunctor (X : Scheme.{u}) :
    Scheme.{u}ᵒᵖ ⥤ Type (u + 1) :=
  uliftYoneda.{u + 1}.obj X

/-- A coarse moduli space for the locally constant `Gamma_0(N)` moduli
functor.

Besides classification of geometric points, `desc`, `fac`, and `uniq` say
that the classifying transformation is initial among natural transformations
from the moduli functor to functors represented by schemes.  They do not say
that the classifying transformation is an isomorphism. -/
structure CoarseModuliSpace (N : ℕ) [NeZero N] where
  /-- The underlying coarse moduli scheme. -/
  scheme : Scheme.{u}
  /-- The natural classifying morphism to the scheme's functor of points. -/
  classifying :
    locallyConstantGammaZeroModuliFunctor N ⟶ SchemePointFunctor scheme
  /-- Classification is bijective on points over algebraically closed
  fields, within the locally constant locus. -/
  geometric_bijective : ∀ (K : Type u) [Field K] [IsAlgClosed K],
    Function.Bijective (fun x :
      (locallyConstantGammaZeroModuliFunctor N).obj
        (Opposite.op (Spec (.of K))) =>
      (classifying.app (Opposite.op (Spec (.of K))) x).down)
  /-- The morphism induced by a natural invariant with values in a scheme. -/
  desc : ∀ (Y : Scheme.{u}),
    (locallyConstantGammaZeroModuliFunctor N ⟶ SchemePointFunctor Y) →
      (scheme ⟶ Y)
  /-- Every scheme-valued natural invariant factors through the coarse
  classifying transformation. -/
  fac : ∀ (Y : Scheme.{u})
    (α : locallyConstantGammaZeroModuliFunctor N ⟶ SchemePointFunctor Y),
    α = classifying ≫ uliftYoneda.map (desc Y α)
  /-- The factorization through the coarse scheme is unique. -/
  uniq : ∀ (Y : Scheme.{u})
    (α : locallyConstantGammaZeroModuliFunctor N ⟶ SchemePointFunctor Y)
    (f : scheme ⟶ Y),
    α = classifying ≫ uliftYoneda.map f → f = desc Y α

namespace CoarseModuliSpace

variable (M : CoarseModuliSpace.{u} N)

/-- The actual morphism to the coarse moduli scheme classified by a relative
locally constant `Gamma_0(N)` family. -/
def point {T : Scheme.{u}}
    (x : (locallyConstantGammaZeroModuliFunctor N).obj (Opposite.op T)) :
    T ⟶ M.scheme :=
  (M.classifying.app (Opposite.op T) x).down

/-- On algebraically closed fields, `point` is a bijection from family
isomorphism classes to geometric points of the coarse scheme. -/
theorem geometricPoint_bijective (K : Type u) [Field K] [IsAlgClosed K] :
    Function.Bijective (M.point (T := Spec (.of K))) :=
  M.geometric_bijective K

/-- Formation of the coarse classifying point commutes with arbitrary base
change. -/
@[simp]
theorem point_baseChange {S T : Scheme.{u}} (f : T ⟶ S)
    (x : (locallyConstantGammaZeroModuliFunctor N).obj (Opposite.op S)) :
    M.point ((locallyConstantGammaZeroModuliFunctor N).map f.op x) =
      f ≫ M.point x := by
  have h := M.classifying.naturality f.op
  exact congrArg (fun q => (q x).down) h

/-- The canonical morphism from one coarse moduli scheme to another. -/
def map (M M' : CoarseModuliSpace.{u} N) : M.scheme ⟶ M'.scheme :=
  M.desc M'.scheme M'.classifying

/-- The canonical morphism intertwines the two classifying
transformations. -/
theorem map_spec (M M' : CoarseModuliSpace.{u} N) :
    M'.classifying = M.classifying ≫ uliftYoneda.map (map M M') :=
  M.fac M'.scheme M'.classifying

/-- The canonical endomorphism of a coarse moduli scheme is the identity. -/
theorem map_self (M : CoarseModuliSpace.{u} N) : map M M = 𝟙 M.scheme := by
  symm
  apply M.uniq M.scheme M.classifying
  simp

/-- Canonical maps between coarse moduli schemes compose canonically. -/
theorem map_comp (M M' M'' : CoarseModuliSpace.{u} N) :
    map M M' ≫ map M' M'' = map M M'' := by
  apply M.uniq M''.scheme M''.classifying
  rw [map_spec M' M'', map_spec M M']
  simp only [Category.assoc, ← Functor.map_comp]

/-- Any two coarse moduli schemes for the same locally constant functor are
canonically isomorphic. -/
noncomputable def uniqueIso (M M' : CoarseModuliSpace.{u} N) :
    M.scheme ≅ M'.scheme where
  hom := map M M'
  inv := map M' M
  hom_inv_id := by rw [map_comp, map_self]
  inv_hom_id := by rw [map_comp, map_self]

/-- The canonical isomorphism intertwines the classifying
transformations. -/
theorem uniqueIso_hom_spec (M M' : CoarseModuliSpace.{u} N) :
    M'.classifying =
      M.classifying ≫ uliftYoneda.map (uniqueIso M M').hom :=
  map_spec M M'

/-- A morphism compatible with both classifying transformations is the
canonical coarse-moduli isomorphism. -/
theorem hom_eq_uniqueIso_hom (M M' : CoarseModuliSpace.{u} N)
    (f : M.scheme ⟶ M'.scheme)
    (hf : M'.classifying = M.classifying ≫ uliftYoneda.map f) :
    f = (uniqueIso M M').hom :=
  M.uniq M'.scheme M'.classifying f hf

end CoarseModuliSpace
end LocallyConstantGammaZeroFamily
end MazurTorsion.ModularCurve.XZeroModuli

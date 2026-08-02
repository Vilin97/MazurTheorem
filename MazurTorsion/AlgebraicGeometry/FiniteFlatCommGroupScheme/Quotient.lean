/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.GroupTheory.Coset.Card
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.Constant

/-!
# Quotients of constant finite-flat commutative group schemes

For a finite commutative group `G` and a subgroup `N`, the quotient `G/N` is again finite
commutative.  Applying the explicit function-Hopf-algebra construction gives a genuine
finite-flat quotient group scheme.  The quotient morphism and its factorization property are
constructed from `QuotientGroup.mk'` and `QuotientGroup.lift`; faithfulness of function-ring
pullback over a nonzero base proves uniqueness among morphisms induced from group homomorphisms.

This concrete construction is intentionally separate from the still-larger theorem that an
arbitrary finite-flat closed subgroup quotient is representable as an fppf sheaf quotient.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry
namespace FiniteFlatCommGroupScheme

universe u

noncomputable local instance quotientFintype
    {G : Type u} [Group G] [Finite G] (N : Subgroup G) : Fintype (G ⧸ N) :=
  Fintype.ofFinite (G ⧸ N)

/-- The finite-free affine quotient of a constant group by a subgroup. -/
abbrev constantQuotientAffine (R : Type u) [CommRing R]
    {G : Type u} [CommGroup G] [Fintype G] (N : Subgroup G) :
    AffineFiniteFreeCommGroupScheme R :=
  (constant R (G ⧸ N))

/-- The geometric constant finite-flat quotient `G/N`. -/
abbrev constantQuotient (R : Type u) [CommRing R]
    {G : Type u} [CommGroup G] [Fintype G] (N : Subgroup G) :
    FiniteFlatCommGroupScheme (Spec (.of R)) :=
  constantScheme R (G ⧸ N)

/-- The affine quotient morphism induced by `G → G/N`. -/
def constantQuotientMapAffine (R : Type u) [CommRing R]
    {G : Type u} [CommGroup G] [Fintype G] (N : Subgroup G) :
    (constant R G) ⟶ constantQuotientAffine R N :=
  constantMapAffine R (QuotientGroup.mk' N)

/-- The geometric quotient morphism induced by `G → G/N`. -/
def constantQuotientMap (R : Type u) [CommRing R]
    {G : Type u} [CommGroup G] [Fintype G] (N : Subgroup G) :
    constantScheme R G ⟶ constantQuotient R N :=
  constantMap R (QuotientGroup.mk' N)

/-- A homomorphism killing `N` descends to a morphism out of the constant quotient. -/
def constantQuotientLiftAffine (R : Type u) [CommRing R]
    {G K : Type u} [CommGroup G] [Fintype G] [CommGroup K] [Fintype K]
    (N : Subgroup G) (f : G →* K) (hf : N ≤ f.ker) :
    constantQuotientAffine R N ⟶ constant R K :=
  constantMapAffine R (QuotientGroup.lift N f hf)

/-- The descended affine morphism factors the original constant-group morphism. -/
theorem constantQuotientMapAffine_comp_lift (R : Type u) [CommRing R]
    {G K : Type u} [CommGroup G] [Fintype G] [CommGroup K] [Fintype K]
    (N : Subgroup G) (f : G →* K) (hf : N ≤ f.ker) :
    constantQuotientMapAffine R N ≫ constantQuotientLiftAffine R N f hf =
      constantMapAffine R f := by
  change constantMapAffine R (QuotientGroup.mk' N) ≫
      constantMapAffine R (QuotientGroup.lift N f hf) = constantMapAffine R f
  rw [← constantMapAffine_comp]
  rw [QuotientGroup.lift_comp_mk']

/-- Universal factorization and uniqueness for constant quotient morphisms.  The maps quantified
here are the actual scheme morphisms induced by the displayed group homomorphisms. -/
theorem existsUnique_constantQuotientLiftAffine
    (R : Type u) [CommRing R] [Nontrivial R]
    {G K : Type u} [CommGroup G] [Fintype G] [CommGroup K] [Fintype K]
    (N : Subgroup G) (f : G →* K) (hf : N ≤ f.ker) :
    ∃! q : G ⧸ N →* K,
      constantQuotientMapAffine R N ≫ constantMapAffine R q = constantMapAffine R f := by
  refine ⟨QuotientGroup.lift N f hf, constantQuotientMapAffine_comp_lift R N f hf, ?_⟩
  intro q hq
  apply QuotientGroup.monoidHom_ext
  have hcomp : q.comp (QuotientGroup.mk' N) = f := by
    apply constantMapAffine_injective R
    rw [constantMapAffine_comp]
    exact hq
  rw [hcomp, QuotientGroup.lift_comp_mk']

/-- The quotient morphism sends the distinguished point `g` to its coset. -/
@[simp]
theorem mapPoint_constantQuotientMap (R : Type u) [CommRing R]
    {G : Type u} [CommGroup G] [Fintype G] (N : Subgroup G) (g : G) :
    mapPoint (constantQuotientMap R N) (AffineCommGroupScheme.testObject (R := R) R)
        (constantGeometricPoint R G g) =
      constantGeometricPoint R (G ⧸ N) (QuotientGroup.mk' N g) :=
  mapPoint_constantMap_constantPoint R (QuotientGroup.mk' N) g

/-- The quotient has the expected finite-free order. -/
@[simp]
theorem constantQuotient_order (R : Type u) [CommRing R] [Nontrivial R]
    {G : Type u} [CommGroup G] [Fintype G] (N : Subgroup G) :
    (constantQuotientAffine R N).order = Fintype.card (G ⧸ N) :=
  constant_order R (G ⧸ N)

/-- Geometric base change of a constant quotient agrees with scalar extension of its explicit
function Hopf algebra. -/
noncomputable def constantQuotientRealizeBaseChangeIso
    {R K : Type u} [CommRing R] [CommRing K] [Algebra R K]
    {G : Type u} [CommGroup G] [Fintype G] (N : Subgroup G) :
    (baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj
        (constantQuotient R N) ≅
      ((constantQuotientAffine R N).baseChange (K := K)).realize :=
  constantRealizeBaseChangeIso (R := R) (K := K) (G ⧸ N)

end FiniteFlatCommGroupScheme
end AlgebraicGeometry

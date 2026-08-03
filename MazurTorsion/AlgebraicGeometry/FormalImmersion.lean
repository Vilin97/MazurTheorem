/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FormalCompletion
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Ideal.Cotangent

/-!
# The cotangent boundary for formal immersions

For a morphism of schemes `f : X ⟶ Y` and a point `x : X`, the local-ring map
`O_{Y, f(x)} ⟶ O_{X, x}` induces a canonical map

`m_{Y, f(x)} / m_{Y, f(x)}² ⟶ m_{X, x} / m_{X, x}²`.

This file packages that map both as a `ℤ`-linear map and as the canonical semilinear map over
the induced homomorphism of residue fields.  The integer-linear version is convenient for
functoriality because the residue fields at the two points need not be definitionally equal.

Surjectivity of this cotangent map is recorded as
`Scheme.Hom.IsCotangentSurjectiveAt`.  Because cotangent surjectivity alone does not control a
residue-field extension, `Scheme.Hom.IsCotangentCriterionAt` adds invertibility of the induced
residue-field map.  The actual completed-local-ring predicate is
`AlgebraicGeometry.IsFormalImmersionAt`; it remains distinct from these first-order conditions until
the locally Noetherian converse criterion required by `MT-X0-INTEGRAL` is proved.

The generic theorem `isCotangentSurjectiveAt_of_degreeOne` isolates the degree-one linear-algebra
step: when the residue-field map is an isomorphism, a nonzero canonical semilinear map onto a
one-dimensional cotangent space is surjective.  `FormalImmersionIdentity` provides a separate
concrete normalization consumer.
-/

namespace AlgebraicGeometry

universe u

open CategoryTheory

/-- A nonzero semilinear map onto a one-dimensional vector space is surjective when its
homomorphism of scalars is surjective. -/
theorem surjective_semilinear_of_nonzero_of_finrank_eq_one
    {K L V W : Type*} [DivisionRing K] [DivisionRing L]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module L W]
    {σ : K →+* L} (hσ : Function.Surjective σ)
    (hfinrank : Module.finrank L W = 1)
    {d : V →ₛₗ[σ] W} (hnonzero : d ≠ 0) :
    Function.Surjective d := by
  obtain ⟨z, hz⟩ := DFunLike.ne_iff.mp hnonzero
  intro y
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero' (d z) hz).mp hfinrank y
  obtain ⟨a, rfl⟩ := hσ c
  exact ⟨a • z, by simpa using hc⟩

namespace Scheme

/-- The cotangent space of a scheme stalk. -/
abbrev StalkCotangent (Z : Scheme.{u}) (z : Z) : Type u :=
  IsLocalRing.CotangentSpace (Z.presheaf.stalk z)

namespace Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)

/-- The cotangent space of the target stalk at the image of `x`.

This is the source of the cotangent map induced by `f`; the reversal is the usual contravariance
of local rings. -/
abbrev targetStalkCotangent : Type u := StalkCotangent Y (f x)

/-- The cotangent space of the source stalk at `x`.

This is the target of the cotangent map induced by `f`. -/
abbrev sourceStalkCotangent : Type u := StalkCotangent X x

/-- The canonical map on stalk cotangent spaces, restricted to the common scalar ring `ℤ`.

The local-hom property of a scheme morphism identifies the preimage of the source maximal ideal
with the target maximal ideal, which is precisely the hypothesis needed by
`Ideal.mapCotangent`. -/
noncomputable def cotangentMapAtInt :
    targetStalkCotangent f x →ₗ[ℤ] sourceStalkCotangent x :=
  Ideal.mapCotangent
    (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)))
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (f.stalkMap x).hom.toIntAlgHom
    (by
      change IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)) ≤
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).comap (f.stalkMap x).hom
      rw [IsLocalRing.maximalIdeal_comap])

/-- On a class represented by an element of the target maximal ideal, the cotangent map is
represented by its image under the stalk map. -/
@[simp]
theorem cotangentMapAtInt_toCotangent
    (a : IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))) :
    cotangentMapAtInt f x
        (Ideal.toCotangent (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))) a) =
      Ideal.toCotangent (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        ⟨(f.stalkMap x).hom a,
          map_nonunit (f.stalkMap x).hom a a.property⟩ :=
  rfl

/-- The canonical cotangent map, semilinear over the induced residue-field homomorphism.

Unlike an arbitrary common-field linearization, this declaration remembers exactly how the
target residue field acts on the source cotangent space. -/
noncomputable def cotangentMapAtResidue :
    targetStalkCotangent f x →ₛₗ[IsLocalRing.ResidueField.map (f.stalkMap x).hom]
      sourceStalkCotangent x where
  toFun := cotangentMapAtInt f x
  map_add' := (cotangentMapAtInt f x).map_add
  map_smul' := by
    intro c z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨b, rfl⟩ :=
      Ideal.toCotangent_surjective
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))) z
    change Ideal.toCotangent (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) _ =
      Ideal.toCotangent (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) _
    congr 1
    apply Subtype.ext
    exact (f.stalkMap x).hom.map_mul a b

/-- Forgetting residue-field semilinearity recovers the integer-linear cotangent map. -/
@[simp]
theorem cotangentMapAtResidue_apply (z : targetStalkCotangent f x) :
    cotangentMapAtResidue f x z = cotangentMapAtInt f x z :=
  rfl

/-- Cotangent maps are contravariantly functorial under composition of scheme morphisms. -/
theorem cotangentMapAtInt_comp
    {Z : Scheme.{u}} (g : Y ⟶ Z) :
    cotangentMapAtInt (f ≫ g) x =
      (cotangentMapAtInt f x).comp (cotangentMapAtInt g (f x)) := by
  apply LinearMap.ext
  intro z
  obtain ⟨a, rfl⟩ :=
    Ideal.toCotangent_surjective
      (IsLocalRing.maximalIdeal (Z.presheaf.stalk (g (f x)))) z
  apply congrArg (Ideal.toCotangent
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)))
  apply Subtype.ext
  let a' : Z.presheaf.stalk ((f ≫ g) x) :=
    (Scheme.Hom.comp_apply f g x).symm ▸ (a : Z.presheaf.stalk (g (f x)))
  have hmap := DFunLike.congr_fun
    (CommRingCat.hom_ext_iff.mp (Scheme.Hom.stalkMap_comp f g x)) a'
  change ((f ≫ g).stalkMap x).hom a' =
    ((f.stalkMap x).hom.comp (g.stalkMap (f x)).hom) a'
  exact hmap

/-- The checked cotangent-space criterion at a scheme point.

This deliberately does not assert surjectivity of completed local rings. -/
def IsCotangentSurjectiveAt : Prop :=
  Function.Surjective (cotangentMapAtInt f x)

/-- The two first-order conditions used by the cotangent criterion for a formal immersion:
the residue-field map is an isomorphism and the canonical cotangent map is surjective.

This remains distinct from `IsFormalImmersionAt`: proving the equivalence with a surjective map
on completed local rings still requires the appropriate finiteness and Noetherian hypotheses. -/
def IsCotangentCriterionAt : Prop :=
  IsIso (f.residueFieldMap x) ∧ IsCotangentSurjectiveAt f x

/-- Cotangent surjectivity is stable under composition. -/
theorem IsCotangentSurjectiveAt.comp
    {Z : Scheme.{u}} {g : Y ⟶ Z}
    (hf : IsCotangentSurjectiveAt f x)
    (hg : IsCotangentSurjectiveAt g (f x)) :
    IsCotangentSurjectiveAt (f ≫ g) x := by
  rw [IsCotangentSurjectiveAt]
  intro z
  obtain ⟨y, hy⟩ := hf z
  obtain ⟨w, hw⟩ := hg y
  let hT : StalkCotangent Z ((f ≫ g) x) = StalkCotangent Z (g (f x)) :=
    congrArg (StalkCotangent Z) (Scheme.Hom.comp_apply f g x)
  let w' : targetStalkCotangent (f ≫ g) x :=
    Eq.mpr hT w
  have hwtransport : Eq.mp hT w' = w := by
    cases hT
    rfl
  refine ⟨w', ?_⟩
  calc
    cotangentMapAtInt (f ≫ g) x w' =
        ((cotangentMapAtInt f x).comp (cotangentMapAtInt g (f x))) w' :=
      LinearMap.congr_fun (cotangentMapAtInt_comp f x g) w'
    _ = z := by
      change cotangentMapAtInt f x
        (cotangentMapAtInt g (f x) (Eq.mp hT w')) = z
      rw [hwtransport, hw, hy]

/-- The residue-field and cotangent conditions are stable under composition.

This is the factorization interface needed for the composite from a modular curve through its
Jacobian to an optimal quotient. -/
theorem IsCotangentCriterionAt.comp
    {Z : Scheme.{u}} {g : Y ⟶ Z}
    (hf : IsCotangentCriterionAt f x)
    (hg : IsCotangentCriterionAt g (f x)) :
    IsCotangentCriterionAt (f ≫ g) x := by
  refine ⟨?_, IsCotangentSurjectiveAt.comp (f := f) (x := x) hf.2 hg.2⟩
  rw [Scheme.residueFieldMap_comp]
  exact IsIso.comp_isIso' hg.1 hf.1

/-- A surjective map on local rings is surjective on cotangent spaces.

This is the basic closed-immersion consumer of the stalk-cotangent interface.  The proof uses the
local-hom property to ensure that a lift of an element of the source maximal ideal lies in the
target maximal ideal. -/
theorem isCotangentSurjectiveAt_of_surjective_stalkMap
    (hstalk : Function.Surjective (f.stalkMap x).hom) :
    IsCotangentSurjectiveAt f x := by
  intro z
  obtain ⟨b, rfl⟩ :=
    Ideal.toCotangent_surjective
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) z
  obtain ⟨a, ha⟩ := hstalk b
  have ha_mem : a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)) := by
    rw [← IsLocalRing.maximalIdeal_comap (f.stalkMap x).hom]
    simpa only [Ideal.mem_comap, ha] using b.property
  refine ⟨Ideal.toCotangent (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)))
    ⟨a, ha_mem⟩, ?_⟩
  rw [cotangentMapAtInt_toCotangent]
  congr 1
  exact Subtype.ext ha

/-- A nonzero canonical residue-field-semilinear map onto a one-dimensional source-curve
cotangent space proves the cotangent-surjectivity half of the criterion. -/
theorem isCotangentSurjectiveAt_of_degreeOne
    (hresidue : IsIso (f.residueFieldMap x))
    (hfinrank :
      Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk x))
        (sourceStalkCotangent x) = 1)
    (hnonzero : cotangentMapAtResidue f x ≠ 0) :
    IsCotangentSurjectiveAt f x := by
  letI := hresidue
  have hsurjective : Function.Surjective
      (IsLocalRing.ResidueField.map (f.stalkMap x).hom) := by
    intro y
    obtain ⟨z, hz⟩ :=
      (ConcreteCategory.bijective_of_isIso (f.residueFieldMap x)).2 y
    exact ⟨z, hz⟩
  exact surjective_semilinear_of_nonzero_of_finrank_eq_one
    hsurjective hfinrank hnonzero

/-- The residue-field-honest degree-one criterion proves both first-order conditions. -/
theorem isCotangentCriterionAt_of_degreeOne
    (hresidue : IsIso (f.residueFieldMap x))
    (hfinrank :
      Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk x))
        (sourceStalkCotangent x) = 1)
    (hnonzero : cotangentMapAtResidue f x ≠ 0) :
    IsCotangentCriterionAt f x :=
  ⟨hresidue,
    isCotangentSurjectiveAt_of_degreeOne f x hresidue hfinrank hnonzero⟩

end Hom

end Scheme

end AlgebraicGeometry

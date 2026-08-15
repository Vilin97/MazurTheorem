/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.GroupTheory.GroupAction.Defs

/-!
# Symmetric quotients of split finite schemes

For a group acting on a set `I`, the invariant subring of the product ring
`I → R` consists precisely of the functions on the orbit set.  Specializing
to permutations of the positions of a tuple of sheet labels gives the affine
component decomposition of a symmetric power of a split finite scheme.

For every component, the multiplicities of its sheets sum to the degree of
the symmetric power.  The named downstream consumer is the split étale
monic-root chart in `PointedIncidenceDescent`: on a component, its universal
divisor is the product of the affine-line root families with these
multiplicities.
-/

noncomputable section

universe u v w

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.Jacobian.SplitFiniteSymmetricQuotient

variable (G : Type u) [Group G] (I : Type v) [MulAction G I]
variable (R : Type w) [CommRing R]

/-- The action on a product ring induced by the action on its factors. -/
@[instance_reducible]
noncomputable def orbitFunctionAction : MulSemiringAction G (I → R) where
  smul g f i := f (g⁻¹ • i)
  one_smul f := by
    funext i
    change f (1⁻¹ • i) = f i
    rw [inv_one, one_smul]
  mul_smul g h f := by
    funext i
    change f ((g * h)⁻¹ • i) = f (h⁻¹ • g⁻¹ • i)
    rw [mul_inv_rev, mul_smul]
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

/-- Permuting the factors of a product ring commutes with its scalar
algebra structure. -/
theorem orbitFunctionSMulCommClass :
    letI := orbitFunctionAction G I R
    SMulCommClass G R (I → R) := by
  letI := orbitFunctionAction G I R
  constructor
  intro g r f
  rfl

/-- An invariant product-ring function has the same value at points in the
same orbit. -/
theorem fixed_eq_of_orbitRel
    (f : I → R)
    (hf : letI := orbitFunctionAction G I R
      ∀ g : G, g • f = f)
    {i j : I} (hij : MulAction.orbitRel G I i j) : f i = f j := by
  letI := orbitFunctionAction G I R
  rcases hij with ⟨g, rfl⟩
  have h := congrFun (hf g) (g • j)
  change f (g⁻¹ • g • j) = f (g • j) at h
  rw [inv_smul_smul] at h
  exact h.symm

/-- Invariant functions on a product ring are exactly functions on the
orbit set of its factors. -/
noncomputable def fixedPointsEquivOrbitFunctions :
    letI := orbitFunctionAction G I R
    letI := orbitFunctionSMulCommClass G I R
    FixedPoints.subalgebra R (I → R) G ≃ₐ[R]
      (MulAction.orbitRel.Quotient G I → R) := by
  letI := orbitFunctionAction G I R
  letI := orbitFunctionSMulCommClass G I R
  let Q := MulAction.orbitRel.Quotient G I
  let q : I → Q := fun i ↦ Quotient.mk'' i
  refine
    { toFun := fun f z ↦ f.1 z.out
      invFun := fun a ↦ ⟨fun i ↦ a (q i), ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_
      map_mul' := ?_
      commutes' := ?_ }
  · intro g
    funext i
    change a (q (g⁻¹ • i)) = a (q i)
    congr 1
    apply Quotient.sound'
    exact MulAction.mem_orbit i (g⁻¹)
  · intro f
    apply Subtype.ext
    funext i
    change f.1 (q i).out = f.1 i
    apply fixed_eq_of_orbitRel G I R f.1 f.2
    exact Quotient.exact ((q i).out_eq.trans rfl)
  · intro a
    funext z
    change a (q z.out) = a z
    rw [show q z.out = z from Quotient.out_eq' z]
  · intro f h
    rfl
  · intro f h
    rfl
  · intro r
    rfl

/-- Permutations act on tuples by reindexing their positions. -/
@[instance_reducible]
noncomputable def tuplePermutationAction (d : ℕ) (A : Type v) :
    MulAction (Equiv.Perm (Fin d)) (Fin d → A) where
  smul g a i := a (g⁻¹ i)
  one_smul a := by
    funext i
    change a (((1 : Equiv.Perm (Fin d))⁻¹) i) = a i
    simp
  mul_smul g h a := by
    funext i
    change a ((g * h)⁻¹ i) = a (h⁻¹ (g⁻¹ i))
    rw [mul_inv_rev]
    rfl

/-- Components of the degree-`d` symmetric power of `m` split sheets. -/
noncomputable abbrev splitComponentIndex (d m : ℕ) := by
  letI := tuplePermutationAction d (Fin m)
  exact MulAction.orbitRel.Quotient
    (Equiv.Perm (Fin d)) (Fin d → Fin m)

/-- The invariant component ring of the split ordered power is a product
indexed by unordered tuples of sheet labels. -/
noncomputable def splitTupleFixedPointsEquivComponents (d m : ℕ) :
    letI := tuplePermutationAction d (Fin m)
    letI := orbitFunctionAction (Equiv.Perm (Fin d)) (Fin d → Fin m) R
    letI := orbitFunctionSMulCommClass
      (Equiv.Perm (Fin d)) (Fin d → Fin m) R
    FixedPoints.subalgebra R ((Fin d → Fin m) → R)
        (Equiv.Perm (Fin d)) ≃ₐ[R]
      (splitComponentIndex d m → R) := by
  letI := tuplePermutationAction d (Fin m)
  exact fixedPointsEquivOrbitFunctions
    (Equiv.Perm (Fin d)) (Fin d → Fin m) R

/-- The affine invariant quotient of a split ordered power is the spectrum
of the product ring indexed by its tuple orbits. -/
noncomputable def splitInvariantSchemeIsoComponents (d m : ℕ) :
    letI := tuplePermutationAction d (Fin m)
    letI := orbitFunctionAction (Equiv.Perm (Fin d)) (Fin d → Fin m) R
    letI := orbitFunctionSMulCommClass
      (Equiv.Perm (Fin d)) (Fin d → Fin m) R
    Spec (.of (FixedPoints.subalgebra R ((Fin d → Fin m) → R)
        (Equiv.Perm (Fin d)))) ≅
      Spec (.of (splitComponentIndex d m → R)) := by
  letI := tuplePermutationAction d (Fin m)
  letI := orbitFunctionAction (Equiv.Perm (Fin d)) (Fin d → Fin m) R
  letI := orbitFunctionSMulCommClass
    (Equiv.Perm (Fin d)) (Fin d → Fin m) R
  exact Scheme.Spec.mapIso
    (splitTupleFixedPointsEquivComponents R d m).symm.toRingEquiv.toCommRingCatIso.op

/-- The product-ring spectrum is the finite coproduct of one copy of the
base for every tuple orbit. -/
noncomputable def splitComponentsCoproductIso (d m : ℕ) :
    (∐ fun _ : ULift.{w} (splitComponentIndex d m) ↦ Spec (.of R)) ≅
      Spec (.of (splitComponentIndex d m → R)) := by
  letI : Finite (ULift.{w} (splitComponentIndex d m)) := by infer_instance
  letI : IsIso (sigmaSpec
      (fun _ : ULift.{w} (splitComponentIndex d m) ↦ CommRingCat.of R)) :=
    AlgebraicGeometry.instIsIsoSchemeSigmaSpecOfFinite _
  let e : (splitComponentIndex d m → R) ≃ₐ[R]
      (ULift.{w} (splitComponentIndex d m) → R) :=
    AlgEquiv.piCongrLeft' R
      (fun _ : splitComponentIndex d m ↦ R) Equiv.ulift.symm
  exact asIso (sigmaSpec
      (fun _ : ULift.{w} (splitComponentIndex d m) ↦ CommRingCat.of R)) ≪≫
    Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op

/-- Scheme-level component decomposition of the invariant quotient of the
split ordered power. -/
noncomputable def splitInvariantSchemeIsoCoproduct (d m : ℕ) :
    letI := tuplePermutationAction d (Fin m)
    letI := orbitFunctionAction (Equiv.Perm (Fin d)) (Fin d → Fin m) R
    letI := orbitFunctionSMulCommClass
      (Equiv.Perm (Fin d)) (Fin d → Fin m) R
    Spec (.of (FixedPoints.subalgebra R ((Fin d → Fin m) → R)
      (Equiv.Perm (Fin d)))) ≅
      (∐ fun _ : ULift.{w} (splitComponentIndex d m) ↦ Spec (.of R)) := by
  letI := tuplePermutationAction d (Fin m)
  letI := orbitFunctionAction (Equiv.Perm (Fin d)) (Fin d → Fin m) R
  letI := orbitFunctionSMulCommClass
    (Equiv.Perm (Fin d)) (Fin d → Fin m) R
  exact splitInvariantSchemeIsoComponents R d m ≪≫
    (splitComponentsCoproductIso R d m).symm

/-- The multiplicity of one split sheet in a symmetric-power component. -/
noncomputable def sheetMultiplicity (d m : ℕ)
    (c : splitComponentIndex d m) (j : Fin m) : ℕ :=
  Fintype.card { i : Fin d // c.out i = j }

/-- The sheet multiplicities of every component sum to the degree. -/
theorem sum_sheetMultiplicity (d m : ℕ) (c : splitComponentIndex d m) :
    ∑ j : Fin m, sheetMultiplicity d m c j = d := by
  classical
  calc
    ∑ j : Fin m, sheetMultiplicity d m c j = Fintype.card (Fin d) := by
      simp only [sheetMultiplicity, Fintype.card_subtype]
      exact (Finset.card_eq_sum_card_fiberwise
        (s := Finset.univ) (t := Finset.univ)
        (f := c.out) (by simp)).symm
    _ = d := Fintype.card_fin d

/-- Indices for all roots on one split component, grouped by their sheet. -/
noncomputable abbrev componentRootIndex (d m : ℕ)
    (c : splitComponentIndex d m) :=
  Σ j : Fin m, Fin (sheetMultiplicity d m c j)

/-- The total number of root indices on every split component is the
symmetric-power degree. -/
theorem card_componentRootIndex (d m : ℕ) (c : splitComponentIndex d m) :
    Fintype.card (componentRootIndex d m c) = d := by
  rw [Fintype.card_sigma]
  simpa using sum_sheetMultiplicity d m c

/-- A finite product of free root algebras on one component has total
module rank equal to the symmetric-power degree. -/
theorem finrank_pi_eq_degree
    (B : Type w) [CommRing B] [Nontrivial B]
    (d m : ℕ) (c : splitComponentIndex d m)
    (M : Fin m → Type v)
    [∀ j, AddCommMonoid (M j)] [∀ j, Module B (M j)]
    [∀ j, Module.Free B (M j)] [∀ j, Module.Finite B (M j)]
    (hM : ∀ j, Module.finrank B (M j) = sheetMultiplicity d m c j) :
    Module.finrank B (∀ j, M j) = d := by
  rw [Module.finrank_pi_fintype]
  simp_rw [hM]
  exact sum_sheetMultiplicity d m c

end MazurTorsion.AlgebraicGeometry.Jacobian.SplitFiniteSymmetricQuotient

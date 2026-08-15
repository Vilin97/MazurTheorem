/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.Jacobian.CoordinateCoefficientInvariants
import MazurTorsion.AlgebraicGeometry.Jacobian.AffineLineSymmetricPower
import Mathlib.Algebra.Category.Ring.Basic

/-!
# Iterated blockwise symmetric invariants

For a finite list of block sizes, recursively view the joint polynomial ring
as polynomials in the first block with coefficients in the polynomial ring of
the remaining blocks.  The corresponding product of symmetric groups acts by
coordinate permutations in the first block and by the recursive action on
coefficients.  Iterating the one-block fundamental theorem identifies the
fixed ring with a polynomial ring of the same block shape, now interpreted as
elementary-symmetric coefficient variables.

The named downstream consumer is `SplitSymmetricQuotientChart`, which
transports this iterated presentation to the sigma type of sheet fibers.
-/

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.Jacobian.IteratedBlockInvariants

open CoordinateCoefficientInvariants
open AffineLineSymmetricPower

variable (R : Type u) [CommRing R]

/-- Iterated polynomial ring, bundled so the recursive coefficient ring carries
its commutative-ring structure while the next polynomial type is formed. -/
@[reducible]
noncomputable def blockRing : List ℕ → CommRingCat
  | [] => CommRingCat.of R
  | n :: ns => CommRingCat.of (MvPolynomial (Fin n) (blockRing ns))

/-- Underlying type of the iterated block polynomial ring. -/
noncomputable abbrev blockPolynomial (ns : List ℕ) := blockRing R ns

/-- Joint variable type corresponding to the nested block presentation. -/
@[reducible]
def blockIndex : List ℕ → Type
  | [] => PEmpty
  | n :: ns => Fin n ⊕ blockIndex ns

noncomputable instance blockPolynomialAlgebra (ns : List ℕ) :
    Algebra R (blockPolynomial R ns) := by
  induction ns with
  | nil =>
      change Algebra R R
      exact Algebra.id R
  | cons n ns ih =>
      letI : Algebra R (blockPolynomial R ns) := ih
      change Algebra R (MvPolynomial (Fin n) (blockPolynomial R ns))
      infer_instance

/-- Iterated and joint presentations of a block polynomial ring are
canonically algebra-equivalent. -/
noncomputable def blockPolynomialAlgEquivJoint :
    (ns : List ℕ) →
      blockPolynomial R ns ≃ₐ[R] MvPolynomial (blockIndex ns) R
  | [] => (MvPolynomial.isEmptyAlgEquiv R PEmpty).symm
  | n :: ns =>
      (MvPolynomial.mapAlgEquiv (Fin n)
        (blockPolynomialAlgEquivJoint ns)).trans
      (MvPolynomial.sumAlgEquiv R (Fin n) (blockIndex ns)).symm

/-- Product of the symmetric groups of all variable blocks. -/
def blockPermutationGroup : List ℕ → Type
  | [] => PUnit
  | n :: ns => Equiv.Perm (Fin n) × blockPermutationGroup ns

instance blockPermutationGroupGroup (ns : List ℕ) :
    Group (blockPermutationGroup ns) := by
  induction ns with
  | nil => exact inferInstanceAs (Group PUnit)
  | cons n ns ih =>
      letI : Group (blockPermutationGroup ns) := ih
      exact inferInstanceAs (Group
        (Equiv.Perm (Fin n) × blockPermutationGroup ns))

/-- The permutation of the joint variable type induced by a recursive block
permutation. -/
def blockIndexPermutationHom :
    (ns : List ℕ) → blockPermutationGroup ns →* Equiv.Perm (blockIndex ns)
  | [] =>
      { toFun := fun _ ↦ 1
        map_one' := rfl
        map_mul' := fun _ _ ↦ rfl }
  | n :: ns =>
      { toFun := fun g ↦ Equiv.sumCongr g.1 (blockIndexPermutationHom ns g.2)
        map_one' := by
          ext i
          cases i with
          | inl i => rfl
          | inr i =>
              change Sum.inr ((blockIndexPermutationHom ns) 1 i) = Sum.inr i
              rw [map_one]
              rfl
        map_mul' := by
          intro g h
          ext i
          cases i with
          | inl i => rfl
          | inr i =>
              change Sum.inr ((blockIndexPermutationHom ns) (g.2 * h.2) i) =
                Sum.inr ((blockIndexPermutationHom ns) g.2
                  ((blockIndexPermutationHom ns) h.2 i))
              rw [map_mul]
              rfl }

/-- Recursive block permutations act on the joint polynomial presentation by
renaming the corresponding joint variables. -/
@[instance_reducible]
noncomputable def jointBlockPermutationAction (ns : List ℕ) :
    MulSemiringAction (blockPermutationGroup ns)
      (MvPolynomial (blockIndex ns) R) := by
  letI := coordinatePermutationAction R (blockIndex ns)
  exact MulSemiringAction.compHom (MvPolynomial (blockIndex ns) R)
    (blockIndexPermutationHom ns)

/-- The joint block-permutation action fixes the coefficient ring. -/
theorem jointBlockPermutationSMulCommClass (ns : List ℕ) :
    letI := jointBlockPermutationAction R ns
    SMulCommClass (blockPermutationGroup ns) R
      (MvPolynomial (blockIndex ns) R) := by
  letI := jointBlockPermutationAction R ns
  constructor
  intro g r p
  change MvPolynomial.rename (blockIndexPermutationHom ns g) (r • p) =
    r • MvPolynomial.rename (blockIndexPermutationHom ns g) p
  simp [Algebra.smul_def]

/-- Combining outer-variable and coefficient-variable permutations in an
iterated polynomial ring is the same as renaming the sum of the two variable
types in its joint presentation. -/
theorem sumAlgEquiv_symm_rename_map
    {S T : Type*} (h : Equiv.Perm S) (g : Equiv.Perm T)
    (p : MvPolynomial S (MvPolynomial T R)) :
    (MvPolynomial.sumAlgEquiv R S T).symm
        (MvPolynomial.rename h (MvPolynomial.map
          (MvPolynomial.rename g).toRingHom p)) =
      MvPolynomial.rename (Equiv.sumCongr h g)
        ((MvPolynomial.sumAlgEquiv R S T).symm p) := by
  induction p using MvPolynomial.induction_on with
  | C q =>
      simp only [MvPolynomial.map_C, MvPolynomial.rename_C]
      induction q using MvPolynomial.induction_on with
      | C r => simp
      | add p q hp hq => simp only [map_add, hp, hq]
      | mul_X p i hp =>
          simpa using congrArg
            (fun z ↦ z * MvPolynomial.X (Sum.inr (g i))) hp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
      simpa using congrArg
        (fun z ↦ z * MvPolynomial.X (Sum.inl (h i))) hp

/-- Under the inverse sum presentation, polynomials in the outer variables
are renamed into the left summand. -/
theorem sumAlgEquiv_symm_map_algebraMap
    {S T : Type*} (p : MvPolynomial S R) :
    (MvPolynomial.sumAlgEquiv R S T).symm
        (MvPolynomial.map (algebraMap R (MvPolynomial T R)) p) =
      MvPolynomial.rename Sum.inl p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, MvPolynomial.map_X,
      MvPolynomial.rename_X, hp,
      MvPolynomial.sumAlgEquiv_symm_X]

/-- Under the inverse sum presentation, a polynomial coefficient is renamed
into the right summand. -/
theorem sumAlgEquiv_symm_C
    {S T : Type*} (p : MvPolynomial T R) :
    (MvPolynomial.sumAlgEquiv R S T).symm (MvPolynomial.C p) =
      MvPolynomial.rename Sum.inr p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul,
      MvPolynomial.rename_X, hp,
      MvPolynomial.sumAlgEquiv_symm_C_X]

@[simp]
theorem blockPolynomialAlgEquivJoint_symm_X_inl
    (n : ℕ) (ns : List ℕ) (i : Fin n) :
    (blockPolynomialAlgEquivJoint R (n :: ns)).symm
        (MvPolynomial.X (Sum.inl i)) = MvPolynomial.X i := by
  simp [blockPolynomialAlgEquivJoint]

@[simp]
theorem blockPolynomialAlgEquivJoint_symm_X_inr
    (n : ℕ) (ns : List ℕ) (i : blockIndex ns) :
    (blockPolynomialAlgEquivJoint R (n :: ns)).symm
        (MvPolynomial.X (Sum.inr i)) =
      MvPolynomial.C ((blockPolynomialAlgEquivJoint R ns).symm
        (MvPolynomial.X i)) := by
  simp [blockPolynomialAlgEquivJoint]

theorem blockPolynomialAlgEquivJoint_esymm
    (n : ℕ) (ns : List ℕ) (q : ℕ) :
    blockPolynomialAlgEquivJoint R (n :: ns)
        (MvPolynomial.esymm (Fin n) (blockPolynomial R ns) q) =
      MvPolynomial.rename Sum.inl (MvPolynomial.esymm (Fin n) R q) := by
  rw [blockPolynomialAlgEquivJoint, AlgEquiv.trans_apply,
    MvPolynomial.mapAlgEquiv_apply, MvPolynomial.map_esymm]
  rw [← MvPolynomial.map_esymm (σ := Fin n) (f :=
    algebraMap R (MvPolynomial (blockIndex ns) R))]
  exact sumAlgEquiv_symm_map_algebraMap R
    (MvPolynomial.esymm (Fin n) R q)

theorem blockPolynomialAlgEquivJoint_C
    (n : ℕ) (ns : List ℕ) (p : blockPolynomial R ns) :
    blockPolynomialAlgEquivJoint R (n :: ns) (MvPolynomial.C p) =
      MvPolynomial.rename Sum.inr (blockPolynomialAlgEquivJoint R ns p) := by
  rw [blockPolynomialAlgEquivJoint, AlgEquiv.trans_apply,
    MvPolynomial.mapAlgEquiv_apply, MvPolynomial.map_C]
  exact sumAlgEquiv_symm_C R (blockPolynomialAlgEquivJoint R ns p)

/-- Recursive block-permutation action on the iterated polynomial ring. -/
@[instance_reducible]
noncomputable def blockPermutationAction :
    (ns : List ℕ) →
      MulSemiringAction (blockPermutationGroup ns) (blockPolynomial R ns)
  | [] =>
      { smul := fun _ r ↦ r
        one_smul := fun _ ↦ rfl
        mul_smul := fun _ _ _ ↦ rfl
        smul_zero := fun _ ↦ rfl
        smul_add := fun _ _ _ ↦ rfl
        smul_one := fun _ ↦ rfl
        smul_mul := fun _ _ _ ↦ rfl }
  | n :: ns => by
      letI : MulSemiringAction (blockPermutationGroup ns)
          (blockPolynomial R ns) := blockPermutationAction ns
      change MulSemiringAction
        (Equiv.Perm (Fin n) × blockPermutationGroup ns)
        (MvPolynomial (Fin n) (blockPolynomial R ns))
      exact coordinateCoefficientAction
        (blockPermutationGroup ns) (blockPolynomial R ns) (Fin n)

/-- The recursive block action fixes the ground ring. -/
theorem blockPermutationSMulCommClass :
    (ns : List ℕ) →
    letI := blockPermutationAction R ns
    SMulCommClass (blockPermutationGroup ns) R (blockPolynomial R ns)
  | [] => by
      letI := blockPermutationAction R []
      constructor
      intro _ r x
      rfl
  | n :: ns => by
      letI : MulSemiringAction (blockPermutationGroup ns)
          (blockPolynomial R ns) := blockPermutationAction R ns
      letI : SMulCommClass (blockPermutationGroup ns) R
          (blockPolynomial R ns) := blockPermutationSMulCommClass ns
      letI : MulSemiringAction
          (Equiv.Perm (Fin n) × blockPermutationGroup ns)
          (MvPolynomial (Fin n) (blockPolynomial R ns)) :=
        coordinateCoefficientAction
          (blockPermutationGroup ns) (blockPolynomial R ns) (Fin n)
      change SMulCommClass
        (Equiv.Perm (Fin n) × blockPermutationGroup ns) R
        (MvPolynomial (Fin n) (blockPolynomial R ns))
      exact coordinateCoefficientSMulCommClass
        (blockPermutationGroup ns) R (blockPolynomial R ns) (Fin n)

/-- Mapping coefficients through an equivariant ring homomorphism commutes
with the corresponding coefficientwise actions on multivariable
polynomials. -/
theorem map_map_of_equivariant
    {A B : Type*} [CommRing A] [CommRing B]
    (e : A →+* B) (f : A →+* A) (g : B →+* B)
    (he : ∀ a, e (f a) = g (e a))
    {S : Type*} (p : MvPolynomial S A) :
    MvPolynomial.map e (MvPolynomial.map f p) =
      MvPolynomial.map g (MvPolynomial.map e p) := by
  rw [MvPolynomial.map_map, MvPolynomial.map_map]
  apply congrArg (fun h : A →+* B ↦ MvPolynomial.map h p)
  ext a
  exact he a

/-- The canonical equivalence from the recursive to the joint polynomial
presentation intertwines the recursive product action with joint variable
renaming. -/
theorem blockPolynomialAlgEquivJoint_equivariant :
    (ns : List ℕ) → ∀ (g : blockPermutationGroup ns)
      (p : blockPolynomial R ns),
      letI := blockPermutationAction R ns
      letI := jointBlockPermutationAction R ns
      blockPolynomialAlgEquivJoint R ns (g • p) =
        g • blockPolynomialAlgEquivJoint R ns p
  | [], g, p => by
      change PUnit at g
      letI := blockPermutationAction R []
      letI := jointBlockPermutationAction R []
      change blockPolynomialAlgEquivJoint R [] p =
        MvPolynomial.rename (blockIndexPermutationHom [] g)
          (blockPolynomialAlgEquivJoint R [] p)
      cases g
      change blockPolynomialAlgEquivJoint R [] p =
        MvPolynomial.rename (Equiv.refl (blockIndex []))
          (blockPolynomialAlgEquivJoint R [] p)
      simp
  | n :: ns, g, p => by
      change Equiv.Perm (Fin n) × blockPermutationGroup ns at g
      change MvPolynomial (Fin n) (blockPolynomial R ns) at p
      letI : MulSemiringAction (blockPermutationGroup ns)
          (blockPolynomial R ns) := blockPermutationAction R ns
      letI : MulSemiringAction (blockPermutationGroup (n :: ns))
          (blockPolynomial R (n :: ns)) := blockPermutationAction R (n :: ns)
      letI : MulSemiringAction (blockPermutationGroup ns)
          (MvPolynomial (blockIndex ns) R) := jointBlockPermutationAction R ns
      letI : MulSemiringAction (blockPermutationGroup (n :: ns))
          (MvPolynomial (blockIndex (n :: ns)) R) :=
        jointBlockPermutationAction R (n :: ns)
      change (MvPolynomial.sumAlgEquiv R (Fin n) (blockIndex ns)).symm
          (MvPolynomial.map (blockPolynomialAlgEquivJoint R ns).toRingHom
            (MvPolynomial.rename g.1
              (MvPolynomial.map
                (MulSemiringAction.toRingHom (blockPermutationGroup ns)
                  (blockPolynomial R ns) g.2) p))) =
        MvPolynomial.rename
          (Equiv.sumCongr g.1 (blockIndexPermutationHom ns g.2))
          ((MvPolynomial.sumAlgEquiv R (Fin n) (blockIndex ns)).symm
            (MvPolynomial.map (blockPolynomialAlgEquivJoint R ns).toRingHom p))
      rw [MvPolynomial.map_rename]
      rw [map_map_of_equivariant
        (blockPolynomialAlgEquivJoint R ns).toRingHom
        (MulSemiringAction.toRingHom (blockPermutationGroup ns)
          (blockPolynomial R ns) g.2)
        (MvPolynomial.rename (blockIndexPermutationHom ns g.2)).toRingHom
        (fun a ↦ blockPolynomialAlgEquivJoint_equivariant ns g.2 a)]
      exact sumAlgEquiv_symm_rename_map R g.1
        (blockIndexPermutationHom ns g.2)
        (MvPolynomial.map (blockPolynomialAlgEquivJoint R ns).toRingHom p)

/-- Fixed subring of the iterated block-permutation action. -/
noncomputable abbrev blockFixedSubalgebra (ns : List ℕ) :
    Subalgebra R (blockPolynomial R ns) := by
  letI : MulSemiringAction (blockPermutationGroup ns)
      (blockPolynomial R ns) := blockPermutationAction R ns
  letI : SMulCommClass (blockPermutationGroup ns) R
      (blockPolynomial R ns) := blockPermutationSMulCommClass R ns
  exact FixedPoints.subalgebra R (blockPolynomial R ns)
    (blockPermutationGroup ns)

/-- Equivariance transports the fixed subring of the recursive presentation
to the fixed subring for blockwise renaming in the joint presentation. -/
noncomputable def blockFixedAlgEquivJoint (ns : List ℕ) :
    letI := blockPermutationAction R ns
    letI := blockPermutationSMulCommClass R ns
    letI := jointBlockPermutationAction R ns
    letI := jointBlockPermutationSMulCommClass R ns
    blockFixedSubalgebra R ns ≃ₐ[R]
      FixedPoints.subalgebra R (MvPolynomial (blockIndex ns) R)
        (blockPermutationGroup ns) := by
  letI := blockPermutationAction R ns
  letI := blockPermutationSMulCommClass R ns
  letI := jointBlockPermutationAction R ns
  letI := jointBlockPermutationSMulCommClass R ns
  let e := blockPolynomialAlgEquivJoint R ns
  let F := FixedPoints.subalgebra R (MvPolynomial (blockIndex ns) R)
    (blockPermutationGroup ns)
  let forward : blockFixedSubalgebra R ns →ₐ[R] F :=
    { toFun := fun p ↦ ⟨e p.1, fun g ↦ by
          rw [← blockPolynomialAlgEquivJoint_equivariant R ns g p.1]
          exact congrArg e (p.2 g)⟩
      map_one' := by apply Subtype.ext; exact e.map_one
      map_mul' := fun p q ↦ by apply Subtype.ext; exact e.map_mul p.1 q.1
      map_zero' := by apply Subtype.ext; exact e.map_zero
      map_add' := fun p q ↦ by apply Subtype.ext; exact e.map_add p.1 q.1
      commutes' := fun r ↦ by apply Subtype.ext; exact e.commutes r }
  let backward : F →ₐ[R] blockFixedSubalgebra R ns :=
    { toFun := fun p ↦ ⟨e.symm p.1, fun g ↦ by
          apply e.injective
          rw [blockPolynomialAlgEquivJoint_equivariant R ns]
          rw [e.apply_symm_apply]
          exact p.2 g⟩
      map_one' := by apply Subtype.ext; exact e.symm.map_one
      map_mul' := fun p q ↦ by apply Subtype.ext; exact e.symm.map_mul p.1 q.1
      map_zero' := by apply Subtype.ext; exact e.symm.map_zero
      map_add' := fun p q ↦ by apply Subtype.ext; exact e.symm.map_add p.1 q.1
      commutes' := fun r ↦ by apply Subtype.ext; exact e.symm.commutes r }
  apply AlgEquiv.ofAlgHom forward backward
  · apply DFunLike.ext _ _
    intro p
    apply Subtype.ext
    exact e.apply_symm_apply p.1
  · apply DFunLike.ext _ _
    intro p
    apply Subtype.ext
    exact e.symm_apply_apply p.1

/-- Recursive coefficient map into the blockwise fixed ring.  Keeping this
map explicit makes its values on generators available without unfolding
equivalences between definitionally equal fixed-point presentations. -/
noncomputable def blockInvariantAlgHom :
    (ns : List ℕ) →
      letI := blockPermutationAction R ns
      letI := blockPermutationSMulCommClass R ns
      blockPolynomial R ns →ₐ[R]
        FixedPoints.subalgebra R (blockPolynomial R ns)
          (blockPermutationGroup ns)
  | [] => by
      letI := blockPermutationAction R []
      letI := blockPermutationSMulCommClass R []
      exact
        { toFun := fun r ↦ ⟨r, fun _ ↦ rfl⟩
          map_one' := rfl
          map_mul' := fun _ _ ↦ rfl
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl
          commutes' := fun _ ↦ rfl }
  | n :: ns => by
      letI : MulSemiringAction (blockPermutationGroup ns)
          (blockPolynomial R ns) := blockPermutationAction R ns
      letI : SMulCommClass (blockPermutationGroup ns) R
          (blockPolynomial R ns) := blockPermutationSMulCommClass R ns
      letI : MulSemiringAction (blockPermutationGroup (n :: ns))
          (blockPolynomial R (n :: ns)) := blockPermutationAction R (n :: ns)
      letI : SMulCommClass (blockPermutationGroup (n :: ns)) R
          (blockPolynomial R (n :: ns)) := blockPermutationSMulCommClass R (n :: ns)
      let h := (coefficientCoordinateAlgHom
        (blockPermutationGroup ns) R (blockPolynomial R ns)
        (Fin n) n (Fintype.card_fin n)).comp
          (MvPolynomial.mapAlgHom (blockInvariantAlgHom ns))
      refine ((Subalgebra.val _).comp h).codRestrict _ ?_
      intro p g
      exact (h p).2 g.1 g.2

@[simp]
theorem blockInvariantAlgHom_cons_apply_val (n : ℕ) (ns : List ℕ)
    :
    letI := blockPermutationAction R ns
    letI := blockPermutationSMulCommClass R ns
    ∀ p : blockPolynomial R (n :: ns),
      ((blockInvariantAlgHom R (n :: ns)) p).1 =
        ((coefficientCoordinateAlgHom
          (blockPermutationGroup ns) R (blockPolynomial R ns)
          (Fin n) n (Fintype.card_fin n))
            (MvPolynomial.map (σ := Fin n)
              (blockInvariantAlgHom R ns).toRingHom p)).1 := by
  letI := blockPermutationAction R ns
  letI := blockPermutationSMulCommClass R ns
  intro p
  rfl

/-- The explicit recursive block invariant map is bijective. -/
theorem blockInvariantAlgHom_bijective :
    (ns : List ℕ) →
      letI := blockPermutationAction R ns
      letI := blockPermutationSMulCommClass R ns
      Function.Bijective (blockInvariantAlgHom R ns)
  | [] => by
      letI := blockPermutationAction R []
      letI := blockPermutationSMulCommClass R []
      constructor
      · intro p q hpq
        exact congrArg Subtype.val hpq
      · intro p
        exact ⟨p.1, Subtype.ext rfl⟩
  | n :: ns => by
      letI : MulSemiringAction (blockPermutationGroup ns)
          (blockPolynomial R ns) := blockPermutationAction R ns
      letI : SMulCommClass (blockPermutationGroup ns) R
          (blockPolynomial R ns) := blockPermutationSMulCommClass R ns
      letI : MulSemiringAction (blockPermutationGroup (n :: ns))
          (blockPolynomial R (n :: ns)) := blockPermutationAction R (n :: ns)
      letI : SMulCommClass (blockPermutationGroup (n :: ns)) R
          (blockPolynomial R (n :: ns)) := blockPermutationSMulCommClass R (n :: ns)
      let h := coefficientCoordinateAlgHom
        (blockPermutationGroup ns) R (blockPolynomial R ns)
        (Fin n) n (Fintype.card_fin n)
      have hrec := blockInvariantAlgHom_bijective ns
      have hmap_injective : Function.Injective
          (MvPolynomial.map (σ := Fin n)
            (blockInvariantAlgHom R ns).toRingHom) :=
        MvPolynomial.map_injective (σ := Fin n)
          (blockInvariantAlgHom R ns).toRingHom hrec.1
      have hmap_surjective : Function.Surjective
          (MvPolynomial.map (σ := Fin n)
            (blockInvariantAlgHom R ns).toRingHom) :=
        MvPolynomial.map_surjective (σ := Fin n)
          (blockInvariantAlgHom R ns).toRingHom hrec.2
      have hh := coefficientCoordinateAlgHom_bijective
        (blockPermutationGroup ns) R (blockPolynomial R ns)
        (Fin n) n (Fintype.card_fin n)
      constructor
      · intro p q hpq
        have hpqval := congrArg Subtype.val hpq
        change (h (MvPolynomial.map (σ := Fin n)
            (blockInvariantAlgHom R ns).toRingHom p)).1 =
          (h (MvPolynomial.map (σ := Fin n)
            (blockInvariantAlgHom R ns).toRingHom q)).1 at hpqval
        exact hmap_injective (hh.1 (Subtype.ext hpqval))
      · intro p
        let pc : coordinateCoefficientFixedSubalgebra
            (blockPermutationGroup ns) R (blockPolynomial R ns) (Fin n) :=
          ⟨p.1, fun a g ↦ p.2 (a, g)⟩
        obtain ⟨q, hq⟩ := hh.2 pc
        obtain ⟨r, hr⟩ := hmap_surjective q
        refine ⟨r, ?_⟩
        apply Subtype.ext
        change (h (MvPolynomial.map (σ := Fin n)
          (blockInvariantAlgHom R ns).toRingHom r)).1 = p.1
        rw [hr]
        exact congrArg Subtype.val hq

/-- The fixed ring of a finite product of blockwise symmetric groups is freely
generated by the elementary-symmetric coefficient variables in every block. -/
noncomputable def blockInvariantAlgEquiv (ns : List ℕ) :
    letI := blockPermutationAction R ns
    letI := blockPermutationSMulCommClass R ns
    blockPolynomial R ns ≃ₐ[R]
      FixedPoints.subalgebra R (blockPolynomial R ns)
        (blockPermutationGroup ns) :=
  AlgEquiv.ofBijective (blockInvariantAlgHom R ns)
    (blockInvariantAlgHom_bijective R ns)

@[simp]
theorem blockInvariantAlgEquiv_apply (ns : List ℕ)
    (p : blockPolynomial R ns) :
    (blockInvariantAlgEquiv R ns) p = (blockInvariantAlgHom R ns) p := by
  rw [blockInvariantAlgEquiv, AlgEquiv.ofBijective_apply]

/-- In one recursive invariant step, an outer coefficient generator becomes
the elementary-symmetric polynomial in the corresponding root block. -/
theorem blockInvariantAlgEquiv_X (n : ℕ) (ns : List ℕ) (i : Fin n) :
    ((blockInvariantAlgEquiv R (n :: ns)) (MvPolynomial.X i)).1 =
      MvPolynomial.esymm (Fin n) (blockPolynomial R ns) (i + 1) := by
  letI : MulSemiringAction (blockPermutationGroup ns)
      (blockPolynomial R ns) := blockPermutationAction R ns
  letI : SMulCommClass (blockPermutationGroup ns) R
      (blockPolynomial R ns) := blockPermutationSMulCommClass R ns
  rw [blockInvariantAlgEquiv_apply,
    blockInvariantAlgHom_cons_apply_val]
  rw [coefficientCoordinateAlgHom_apply_val]
  simp only [AlgHom.toRingHom_eq_coe, MvPolynomial.map_X,
    MvPolynomial.esymmAlgEquiv_apply, MvPolynomial.esymmAlgHom_apply,
    MvPolynomial.aeval_X]
  rw [MvPolynomial.map_esymm]

/-- In one recursive invariant step, a coefficient invariant is included as
a polynomial constant. -/
theorem blockInvariantAlgEquiv_C (n : ℕ) (ns : List ℕ)
    (p : blockPolynomial R ns) :
    ((blockInvariantAlgEquiv R (n :: ns)) (MvPolynomial.C p)).1 =
      MvPolynomial.C ((blockInvariantAlgEquiv R ns) p).1 := by
  letI : MulSemiringAction (blockPermutationGroup ns)
      (blockPolynomial R ns) := blockPermutationAction R ns
  letI : SMulCommClass (blockPermutationGroup ns) R
      (blockPolynomial R ns) := blockPermutationSMulCommClass R ns
  rw [blockInvariantAlgEquiv_apply,
    blockInvariantAlgHom_cons_apply_val]
  rw [coefficientCoordinateAlgHom_apply_val]
  simp [MvPolynomial.esymmAlgEquiv, MvPolynomial.esymmAlgHom,
    blockInvariantAlgEquiv]

/-- Joint-presentation form of the blockwise fundamental theorem: the fixed
ring for a finite recursive product of symmetric groups is itself a
polynomial ring with one elementary-symmetric coordinate block for every
root-variable block. -/
noncomputable def jointBlockInvariantAlgEquiv (ns : List ℕ) :
    letI := jointBlockPermutationAction R ns
    letI := jointBlockPermutationSMulCommClass R ns
    MvPolynomial (blockIndex ns) R ≃ₐ[R]
      FixedPoints.subalgebra R (MvPolynomial (blockIndex ns) R)
        (blockPermutationGroup ns) := by
  letI := blockPermutationAction R ns
  letI := blockPermutationSMulCommClass R ns
  letI := jointBlockPermutationAction R ns
  letI := jointBlockPermutationSMulCommClass R ns
  exact (blockPolynomialAlgEquivJoint R ns).symm.trans
    ((blockInvariantAlgEquiv R ns).trans (blockFixedAlgEquivJoint R ns))

/-- The elementary-symmetric polynomial belonging to the block and degree
encoded by one recursive coefficient variable. -/
noncomputable def blockElementarySymmetric :
    (ns : List ℕ) → blockIndex ns → MvPolynomial (blockIndex ns) R
  | [], i => PEmpty.elim i
  | n :: _ns, Sum.inl i =>
      MvPolynomial.rename Sum.inl
        (MvPolynomial.esymm (Fin n) R (i + 1))
  | _n :: ns, Sum.inr i =>
      MvPolynomial.rename Sum.inr (blockElementarySymmetric ns i)

/-- The recursively constructed invariant equivalence has the expected
elementary-symmetric value on every coefficient generator. -/
theorem jointBlockInvariantAlgEquiv_X :
    (ns : List ℕ) → (i : blockIndex ns) →
    letI := jointBlockPermutationAction R ns
    letI := jointBlockPermutationSMulCommClass R ns
    ((jointBlockInvariantAlgEquiv R ns) (MvPolynomial.X i)).1 =
      blockElementarySymmetric R ns i
  | [], i => PEmpty.elim i
  | n :: ns, Sum.inl i => by
      letI : MulSemiringAction (blockPermutationGroup ns)
          (blockPolynomial R ns) := blockPermutationAction R ns
      letI : SMulCommClass (blockPermutationGroup ns) R
          (blockPolynomial R ns) := blockPermutationSMulCommClass R ns
      letI : MulSemiringAction (blockPermutationGroup (n :: ns))
          (blockPolynomial R (n :: ns)) := blockPermutationAction R (n :: ns)
      letI : SMulCommClass (blockPermutationGroup (n :: ns)) R
          (blockPolynomial R (n :: ns)) := blockPermutationSMulCommClass R (n :: ns)
      letI := jointBlockPermutationAction R (n :: ns)
      letI := jointBlockPermutationSMulCommClass R (n :: ns)
      change blockPolynomialAlgEquivJoint R (n :: ns)
          (((blockInvariantAlgEquiv R (n :: ns))
            ((blockPolynomialAlgEquivJoint R (n :: ns)).symm
              (MvPolynomial.X (Sum.inl i)))).1) = _
      rw [blockPolynomialAlgEquivJoint_symm_X_inl,
        blockInvariantAlgEquiv_X, blockPolynomialAlgEquivJoint_esymm]
      rfl
  | n :: ns, Sum.inr i => by
      letI : MulSemiringAction (blockPermutationGroup ns)
          (blockPolynomial R ns) := blockPermutationAction R ns
      letI : SMulCommClass (blockPermutationGroup ns) R
          (blockPolynomial R ns) := blockPermutationSMulCommClass R ns
      letI : MulSemiringAction (blockPermutationGroup (n :: ns))
          (blockPolynomial R (n :: ns)) := blockPermutationAction R (n :: ns)
      letI : SMulCommClass (blockPermutationGroup (n :: ns)) R
          (blockPolynomial R (n :: ns)) := blockPermutationSMulCommClass R (n :: ns)
      letI := jointBlockPermutationAction R (n :: ns)
      letI := jointBlockPermutationSMulCommClass R (n :: ns)
      change blockPolynomialAlgEquivJoint R (n :: ns)
          (((blockInvariantAlgEquiv R (n :: ns))
            ((blockPolynomialAlgEquivJoint R (n :: ns)).symm
              (MvPolynomial.X (Sum.inr i)))).1) = _
      rw [blockPolynomialAlgEquivJoint_symm_X_inr,
        blockInvariantAlgEquiv_C, blockPolynomialAlgEquivJoint_C]
      change MvPolynomial.rename Sum.inr
          (((jointBlockInvariantAlgEquiv R ns)
            (MvPolynomial.X i)).1) =
        MvPolynomial.rename Sum.inr (blockElementarySymmetric R ns i)
      rw [jointBlockInvariantAlgEquiv_X ns i]

/-- The affine quotient chart attached to the joint block action. -/
noncomputable abbrev jointBlockInvariantScheme (ns : List ℕ) := by
  letI := jointBlockPermutationAction R ns
  letI := jointBlockPermutationSMulCommClass R ns
  exact _root_.AlgebraicGeometry.Spec (.of
    (FixedPoints.subalgebra R (MvPolynomial (blockIndex ns) R)
      (blockPermutationGroup ns)))

/-- Scheme form of the blockwise fundamental theorem: the joint invariant
quotient is affine space in the elementary-symmetric block coordinates. -/
noncomputable def jointBlockInvariantSchemeIso (ns : List ℕ) :
    jointBlockInvariantScheme R ns ≅
      _root_.AlgebraicGeometry.Spec
        (.of (MvPolynomial (blockIndex ns) R)) := by
  letI := jointBlockPermutationAction R ns
  letI := jointBlockPermutationSMulCommClass R ns
  exact _root_.AlgebraicGeometry.Scheme.Spec.mapIso
    (jointBlockInvariantAlgEquiv R ns).toRingEquiv.toCommRingCatIso.op

end MazurTorsion.AlgebraicGeometry.Jacobian.IteratedBlockInvariants

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Forbidden additive-group embeddings

This file packages the recurring negative input in Mazur's torsion classification: a specified
finite abelian group does not embed in the rational points of an elliptic curve. The definition is
pure group theory, and the transport lemmas keep later arithmetic files independent of a particular
presentation of either group.
-/

@[expose] public section

namespace MazurTorsion

/-- There is no injective additive homomorphism from `A` to `G`. -/
def ForbidsEmbedding (A G : Type*) [AddCommGroup A] [AddCommGroup G] : Prop :=
  ∀ f : A →+ G, ¬ Function.Injective f

namespace ForbidsEmbedding

variable {A B G H : Type*}
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup G] [AddCommGroup H]

/-- If `A` embeds in `B` and `A` cannot embed in `G`, then `B` cannot embed in `G`. -/
theorem of_injective_source (h : ForbidsEmbedding A G) (f : A →+ B)
    (hf : Function.Injective f) : ForbidsEmbedding B G := by
  intro g hg
  exact h (g.comp f) (hg.comp hf)

/-- If `G` embeds in `H` and `A` cannot embed in `H`, then `A` cannot embed in `G`. -/
theorem of_injective_target (h : ForbidsEmbedding A H) (f : G →+ H)
    (hf : Function.Injective f) : ForbidsEmbedding A G := by
  intro g hg
  exact h (f.comp g) (hf.comp hg)

/-- Transport the forbidden source along an additive equivalence. -/
theorem addEquiv_source (e : A ≃+ B) :
    ForbidsEmbedding A G ↔ ForbidsEmbedding B G := by
  constructor
  · intro h
    exact h.of_injective_source e.toAddMonoidHom e.injective
  · intro h
    exact h.of_injective_source e.symm.toAddMonoidHom e.symm.injective

/-- Transport the target along an additive equivalence. -/
theorem addEquiv_target (e : G ≃+ H) :
    ForbidsEmbedding A G ↔ ForbidsEmbedding A H := by
  constructor
  · intro h
    exact h.of_injective_target e.symm.toAddMonoidHom e.symm.injective
  · intro h
    exact h.of_injective_target e.toAddMonoidHom e.injective

/-- A forbidden embedding into a group is also forbidden into any additive subgroup. -/
theorem subgroup_target (h : ForbidsEmbedding A G) (K : AddSubgroup G) :
    ForbidsEmbedding A K :=
  h.of_injective_target K.subtype K.subtype_injective

/-- A forbidden embedding rules out an additive equivalence. -/
theorem not_nonempty_addEquiv (h : ForbidsEmbedding A G) :
    ¬ Nonempty (A ≃+ G) := by
  rintro ⟨e⟩
  exact h e.toAddMonoidHom e.injective

end ForbidsEmbedding

end MazurTorsion

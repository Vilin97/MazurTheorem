/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.CommGroupSchemeFppfQuotient

/-!
# The quotient boundary as an injection

For an ambient fppf quotient presentation `K → G → Q`, the connecting homomorphism

`Q(S) → H¹_fppf(S, K)`

vanishes exactly on the image of `G(S)`.  It therefore descends to an injection

`Q(S) / image(G(S)) → H¹_fppf(S, K)`.

The checked exactness at the next term identifies its image with the actual kernel of
`H¹_fppf(S, K) → H¹_fppf(S, G)`.  Thus the descended boundary is canonically equivalent to
that kernel.  This is the geometric Kummer injection; identifying its source with a particular
Mordell--Weil quotient remains a separate arithmetic input.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.CommGroupScheme

universe u

variable {S : Scheme.{u}}

namespace FppfQuotientPresentation

variable {K G : CommGroupScheme S} {i : K ⟶ G}

/-- The image of source base points in the base points of the quotient scheme. -/
def basePointProjectRange (_D : FppfQuotientPresentation i) :
    Subgroup (BasePoint _D.quotient) :=
  (mapPoint _D.project (baseObject S)).range

/-- Quotient-scheme base points modulo those represented by source base points. -/
abbrev BoundarySourceQuotient (D : FppfQuotientPresentation i) :=
  BasePoint D.quotient ⧸ D.basePointProjectRange

private theorem basePointProjectRange_le_boundaryHom_ker
    (D : FppfQuotientPresentation i) :
    D.basePointProjectRange ≤ D.boundaryHom.ker := by
  rintro _ ⟨x, rfl⟩
  exact MonoidHom.mem_ker.mpr (D.boundaryHom_project x)

/-- Low-degree exactness at quotient base points identifies the subgroup killed by the
boundary with the image of source base points. -/
theorem basePointProjectRange_eq_boundaryHom_ker
    (D : FppfQuotientPresentation i) :
    D.basePointProjectRange = D.boundaryHom.ker := by
  apply le_antisymm
  · exact D.basePointProjectRange_le_boundaryHom_ker
  · intro q hq
    obtain ⟨x, hx⟩ := D.locallyLiftable.exists_source_of_boundaryHom_eq_one q
      (MonoidHom.mem_ker.mp hq)
    exact ⟨x, hx⟩

/-- The connecting homomorphism descended through quotient-scheme base points modulo the
image of source base points. -/
def boundaryQuotientHom (D : FppfQuotientPresentation i) :
    D.BoundarySourceQuotient →* K.FppfHOne.{u} :=
  QuotientGroup.lift D.basePointProjectRange D.boundaryHom
    D.basePointProjectRange_le_boundaryHom_ker

@[simp]
theorem boundaryQuotientHom_mk (D : FppfQuotientPresentation i)
    (q : BasePoint D.quotient) :
    D.boundaryQuotientHom (QuotientGroup.mk' D.basePointProjectRange q) =
      D.boundaryHom q :=
  QuotientGroup.lift_mk' _ _ _

/-- The descended quotient boundary is injective. -/
theorem boundaryQuotientHom_injective (D : FppfQuotientPresentation i) :
    Function.Injective D.boundaryQuotientHom := by
  change Function.Injective
    (QuotientGroup.lift D.basePointProjectRange D.boundaryHom
      D.basePointProjectRange_le_boundaryHom_ker)
  exact (QuotientGroup.injective_lift_iff
    (N := D.basePointProjectRange) D.boundaryHom
      D.basePointProjectRange_le_boundaryHom_ker).2
        D.basePointProjectRange_eq_boundaryHom_ker

/-- The descended boundary, with codomain restricted to the actual kernel of extension from
kernel-valued fppf `H¹` to source-valued fppf `H¹`. -/
def boundaryQuotientKernelHom (D : FppfQuotientPresentation i) :
    D.BoundarySourceQuotient →* (fppfHOneMap i).ker :=
  D.boundaryQuotientHom.codRestrict (fppfHOneMap i).ker fun q ↦ by
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective D.basePointProjectRange q
    exact D.locallyLiftable.fppfHOneMap_boundaryHom q

@[simp]
theorem boundaryQuotientKernelHom_mk (D : FppfQuotientPresentation i)
    (q : BasePoint D.quotient) :
    D.boundaryQuotientKernelHom
        (QuotientGroup.mk' D.basePointProjectRange q) =
      ⟨D.boundaryHom q, D.locallyLiftable.fppfHOneMap_boundaryHom q⟩ := by
  rfl

/-- The descended boundary identifies the quotient of target base points by source base
points with the actual kernel of extension in fppf `H¹`. -/
def boundaryQuotientKernelMulEquiv (D : FppfQuotientPresentation i) :
    D.BoundarySourceQuotient ≃* (fppfHOneMap i).ker := by
  apply MulEquiv.ofBijective D.boundaryQuotientKernelHom
  constructor
  · intro x y hxy
    apply D.boundaryQuotientHom_injective
    exact congrArg Subtype.val hxy
  · rintro ⟨z, hz⟩
    obtain ⟨q, hq⟩ :=
      D.locallyLiftable.exists_boundary_of_fppfHOneMap_eq_one z
        (MonoidHom.mem_ker.mp hz)
    refine ⟨QuotientGroup.mk' D.basePointProjectRange q, ?_⟩
    apply Subtype.ext
    change D.boundaryQuotientHom
        (QuotientGroup.mk' D.basePointProjectRange q) = z
    rw [D.boundaryQuotientHom_mk]
    exact hq

end FppfQuotientPresentation

end AlgebraicGeometry.CommGroupScheme

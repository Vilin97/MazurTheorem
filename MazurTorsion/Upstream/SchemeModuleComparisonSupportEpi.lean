/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleComparisonSupport

/-!
# Cokernel support of an open-local epimorphism

This file weakens the isomorphism hypothesis in the retained comparison-
support boundary on the cokernel side.  If a module morphism becomes an
epimorphism after restriction to an open subscheme, its image cokernel
vanishes there.  A coherent residual whose ambient support contains that of
the target consequently has strictly smaller closed stalk support.

The named downstream consumer is
`hZeroCanonical_finiteDimensional_of_fullSupportSource_of_epi_restrict` in
`ProperCurveFiniteSupportCech`.  No assertion about the kernel is made: its
degree-zero cohomology is deliberately replaced by pointed-curve `H¹`
finiteness in that consumer.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {U X : Scheme.{u}}

/-- The cokernel residual in the kernel-image-cokernel factorization
vanishes wherever the original morphism restricts to an epimorphism. -/
theorem isZero_restrict_cokernel_image_ι_of_epi_map
    (j : U ⟶ X) [IsOpenImmersion j]
    {M N : X.Modules} (f : M ⟶ N)
    [Epi ((restrictFunctor j).map f)] :
    IsZero
      ((cokernel (Abelian.image.ι f)).restrict j) := by
  let F := restrictFunctor j
  letI : PreservesColimitsOfSize.{u, u} F := by
    dsimp [F]
    infer_instance
  have hfac :
      F.map (Abelian.factorThruImage f) ≫
          F.map (Abelian.image.ι f) =
        F.map f := by
    rw [← F.map_comp, Abelian.image.fac]
  letI : Epi (F.map (Abelian.image.ι f)) :=
    epi_of_epi_fac hfac
  have hzero :
      IsZero (cokernel (F.map (Abelian.image.ι f))) :=
    isZero_cokernel_of_epi _
  change IsZero (F.obj (cokernel (Abelian.image.ι f)))
  exact hzero.of_iso
    (PreservesCokernel.iso F (Abelian.image.ι f))

/-- On a preirreducible scheme, a coherent source which surjects onto a
full-support coherent target over a nonempty open also has full support.

The proof is stalkwise: the epimorphism prevents a target stalk on the open
from being nonzero when the corresponding source stalk vanishes.  Thus the
source support contains the open immersion's range, which is dense by
preirreducibility, and coherence makes that support closed.  The named
downstream consumer is
`hZeroCanonical_finiteDimensional_of_fullSupportTarget_lattice_of_epi_restrict`
in `ProperCurveFiniteSupportCech`. -/
theorem closedStalkSupport_eq_top_of_epi_restrict
    (j : U ⟶ X) [IsOpenImmersion j] [Nonempty U]
    [PreirreducibleSpace X]
    {M N : X.Modules} [M.IsFiniteType] [M.IsQuasicoherent]
    [N.IsFiniteType] [N.IsQuasicoherent]
    (f : M ⟶ N) [Epi ((restrictFunctor j).map f)]
    (hN : closedStalkSupport N = ⊤) :
    closedStalkSupport M = ⊤ := by
  have hRange : Set.range j ⊆ stalkSupport M := by
    rintro _ ⟨y, rfl⟩
    intro hMy
    let Fy := underlyingStalkFunctor y
    let eM := (restrictStalkNatIso j y).app M
    let eN := (restrictStalkNatIso j y).app N
    have hMres : IsZero (Fy.obj (M.restrict j)) :=
      eM.isZero_iff.mpr hMy
    haveI : Epi (Fy.map ((restrictFunctor j).map f)) := by
      dsimp [Fy]
      infer_instance
    have hNres : IsZero (Fy.obj (N.restrict j)) :=
      IsZero.of_epi (Fy.map ((restrictFunctor j).map f)) hMres
    have hNy : IsZero ((underlyingStalkFunctor (j y)).obj N) :=
      eN.isZero_iff.mp hNres
    have hyN : j y ∈ stalkSupport N := by
      rw [← coe_closedStalkSupport_eq_stalkSupport N, hN]
      trivial
    exact hyN hNy
  apply Closeds.ext
  change closure (stalkSupport M) = Set.univ
  apply dense_iff_closure_eq.mp
  exact Dense.mono hRange
    (j.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty j))

/-- The cokernel residual has strictly smaller support when the comparison
is epic on an open meeting the source support and the target support is
contained in the source support. -/
theorem closedStalkSupport_cokernel_image_ι_lt_of_epi_map
    (j : U ⟶ X) [IsOpenImmersion j]
    {M N : X.Modules} (f : M ⟶ N)
    [Epi ((restrictFunctor j).map f)]
    [(cokernel (Abelian.image.ι f)).IsFiniteType]
    [(cokernel (Abelian.image.ι f)).IsQuasicoherent]
    (hNM : closedStalkSupport N ≤ closedStalkSupport M)
    (x : U) (hxM : j x ∈ closedStalkSupport M) :
    closedStalkSupport
        (cokernel (Abelian.image.ι f)) <
      closedStalkSupport M := by
  apply closedStalkSupport_lt_of_le_of_isZero_restrict
    j (cokernel (Abelian.image.ι f)) M
  · exact
      (closedStalkSupport_le_of_epi
        (cokernel.π (Abelian.image.ι f))).trans hNM
  · exact
      isZero_restrict_cokernel_image_ι_of_epi_map j f
  · exact hxM

end AlgebraicGeometry.Scheme.Modules

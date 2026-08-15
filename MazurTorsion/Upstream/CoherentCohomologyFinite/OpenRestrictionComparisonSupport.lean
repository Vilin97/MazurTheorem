/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.OpenRestrictionSupportDrop
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafRestrictionExactness

/-!
# Support of the residuals of an open-local isomorphism

Suppose a morphism of scheme modules becomes an isomorphism after
restriction to an open subscheme.  Exactness of open restriction implies
that its kernel and cokernel vanish there.  The same is therefore true for
the kernel--image--cokernel residuals used by support codévissage.

Combining this with `OpenRestrictionSupportDrop` gives strict support
decrease from one explicit support point in the open subscheme.  For the
cokernel residual we keep the necessary support-containment hypothesis
visible: an open-local isomorphism alone does not control extra support of
the target outside the open.
-/


open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {U X : Scheme.{u}}

/--
The kernel of a morphism vanishes on an open subscheme on which the
morphism is an isomorphism.
-/
theorem isZero_restrict_kernel_of_isIso_map
    (j : U ⟶ X) [IsOpenImmersion j]
    {M N : X.Modules} (f : M ⟶ N)
    [IsIso ((restrictFunctor j).map f)] :
    IsZero ((kernel f).restrict j) := by
  let F := restrictFunctor j
  letI : PreservesFiniteLimits F :=
    restrictFunctor_preservesFiniteLimits j
  have hzero : IsZero (kernel (F.map f)) :=
    isZero_kernel_of_mono _
  change IsZero (F.obj (kernel f))
  exact hzero.of_iso (PreservesKernel.iso F f)

/--
The cokernel of a morphism vanishes on an open subscheme on which the
morphism is an isomorphism.
-/
theorem isZero_restrict_cokernel_of_isIso_map
    (j : U ⟶ X) [IsOpenImmersion j]
    {M N : X.Modules} (f : M ⟶ N)
    [IsIso ((restrictFunctor j).map f)] :
    IsZero ((cokernel f).restrict j) := by
  let F := restrictFunctor j
  letI : PreservesColimitsOfSize.{u, u} F :=
    restrictPreservesColimits j
  have hzero : IsZero (cokernel (F.map f)) :=
    isZero_cokernel_of_epi _
  change IsZero (F.obj (cokernel f))
  exact hzero.of_iso (PreservesCokernel.iso F f)

/--
The kernel residual used in kernel--image--cokernel codévissage vanishes
where the original comparison is an isomorphism.
-/
theorem isZero_restrict_kernel_factorThruImage_of_isIso_map
    (j : U ⟶ X) [IsOpenImmersion j]
    {M N : X.Modules} (f : M ⟶ N)
    [IsIso ((restrictFunctor j).map f)] :
    IsZero
      ((kernel (Abelian.factorThruImage f)).restrict j) := by
  let F := restrictFunctor j
  letI : PreservesFiniteLimits F :=
    restrictFunctor_preservesFiniteLimits j
  have hfac :
      F.map (Abelian.factorThruImage f) ≫
          F.map (Abelian.image.ι f) =
        F.map f := by
    rw [← F.map_comp, Abelian.image.fac]
  letI : Mono (F.map (Abelian.factorThruImage f)) :=
    mono_of_mono_fac hfac
  have hzero :
      IsZero (kernel (F.map (Abelian.factorThruImage f))) :=
    isZero_kernel_of_mono _
  change IsZero (F.obj (kernel (Abelian.factorThruImage f)))
  exact hzero.of_iso
    (PreservesKernel.iso F (Abelian.factorThruImage f))

/--
The cokernel residual used in kernel--image--cokernel codévissage
vanishes where the original comparison is an isomorphism.
-/
theorem isZero_restrict_cokernel_image_ι_of_isIso_map
    (j : U ⟶ X) [IsOpenImmersion j]
    {M N : X.Modules} (f : M ⟶ N)
    [IsIso ((restrictFunctor j).map f)] :
    IsZero
      ((cokernel (Abelian.image.ι f)).restrict j) := by
  let F := restrictFunctor j
  letI : PreservesColimitsOfSize.{u, u} F :=
    restrictPreservesColimits j
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

/--
The kernel residual of an open-local isomorphism has strictly smaller
closed support once the chosen open contains a support point of the
source.
-/
theorem closedStalkSupport_kernel_factorThruImage_lt
    (j : U ⟶ X) [IsOpenImmersion j]
    {M N : X.Modules} (f : M ⟶ N)
    [IsIso ((restrictFunctor j).map f)]
    [(kernel (Abelian.factorThruImage f)).IsFiniteType]
    [(kernel (Abelian.factorThruImage f)).IsQuasicoherent]
    (x : U) (hxM : j x ∈ closedStalkSupport M) :
    closedStalkSupport
        (kernel (Abelian.factorThruImage f)) <
      closedStalkSupport M := by
  apply closedStalkSupport_lt_of_le_of_isZero_restrict
    j (kernel (Abelian.factorThruImage f)) M
  · exact closedStalkSupport_le_of_mono
      (kernel.ι (Abelian.factorThruImage f))
  · exact
      isZero_restrict_kernel_factorThruImage_of_isIso_map
        j f
  · exact hxM

/--
The cokernel residual of an open-local isomorphism has strictly smaller
closed support, provided the target has no support outside the source.
-/
theorem closedStalkSupport_cokernel_image_ι_lt
    (j : U ⟶ X) [IsOpenImmersion j]
    {M N : X.Modules} (f : M ⟶ N)
    [IsIso ((restrictFunctor j).map f)]
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
      isZero_restrict_cokernel_image_ι_of_isIso_map
        j f
  · exact hxM

/--
Both residual supports drop under the hypotheses used in modification
codévissage.
-/
theorem comparisonResidual_closedStalkSupport_lt
    (j : U ⟶ X) [IsOpenImmersion j]
    {M N : X.Modules} (f : M ⟶ N)
    [IsIso ((restrictFunctor j).map f)]
    [(kernel (Abelian.factorThruImage f)).IsFiniteType]
    [(kernel (Abelian.factorThruImage f)).IsQuasicoherent]
    [(cokernel (Abelian.image.ι f)).IsFiniteType]
    [(cokernel (Abelian.image.ι f)).IsQuasicoherent]
    (hNM : closedStalkSupport N ≤ closedStalkSupport M)
    (x : U) (hxM : j x ∈ closedStalkSupport M) :
    closedStalkSupport
          (kernel (Abelian.factorThruImage f)) <
        closedStalkSupport M ∧
      closedStalkSupport
          (cokernel (Abelian.image.ι f)) <
        closedStalkSupport M :=
  ⟨closedStalkSupport_kernel_factorThruImage_lt
      j f x hxM,
    closedStalkSupport_cokernel_image_ι_lt
      j f hNM x hxM⟩

end AlgebraicGeometry.Scheme.Modules

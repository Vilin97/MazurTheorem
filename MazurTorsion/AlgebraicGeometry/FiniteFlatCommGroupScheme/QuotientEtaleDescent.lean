/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import MazurTorsion.AlgebraicGeometry.FiniteFlatCommGroupScheme.QuotientKernelPairTorsor

/-!
# Etale descent for finite-flat fppf quotient presentations

For an actual finite-flat fppf quotient presentation `K → G → Q`, the represented
kernel-pair torsor law identifies the pullback of `G → Q` along itself with
`K ×_S G → G`.  If `K → S` is etale, this latter projection is etale by base change.
Etaleness then descends along the finite, faithfully flat quotient projection, proving that
`G → Q` is etale.  Consequently an actual fppf extension of two etale finite-flat group
schemes is etale.

The quotient presentation, its scheme-theoretic kernel, and the kernel-pair torsor isomorphism
are all geometric data already constructed in the imported modules.  No connected--etale,
Oort--Tate, or Raynaud classification law is assumed or inferred here.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.FiniteFlatCommGroupScheme

universe u

namespace FppfQuotientPresentation

variable {S : Scheme.{u}} {G : FiniteFlatCommGroupScheme S}

/-- An actual fppf quotient by an etale finite-flat geometric kernel is an etale morphism.

After pulling the quotient projection back along itself, the kernel-pair torsor isomorphism
turns the second projection into `K ×_S G → G`, which is the base change of `K → S`.
The quotient projection is finite, flat, and surjective, so fpqc descent of etaleness applies. -/
theorem project_etale_of_kernel_etale
    (D : FppfQuotientPresentation G)
    (hKernel : Etale D.kernelPresentation.kernel.structureMap) :
    Etale (hom D.project) := by
  letI : MorphismProperty.RespectsIso
      (@Etale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  haveI : MorphismProperty.DescendsAlong
      (@Etale : MorphismProperty Scheme.{u})
      ((@Surjective : MorphismProperty Scheme.{u}) ⊓
        (@Flat : MorphismProperty Scheme.{u}) ⊓
        (@QuasiCompact : MorphismProperty Scheme.{u})) :=
    HasRingHomProperty.descendsAlong_flat
      RingHom.Etale.codescendsAlong_faithfullyFlat
  have hKernelProduct : Etale
      (prod.snd : D.KernelProduct ⟶ G.obj.X).left := by
    exact MorphismProperty.of_isPullback
      (P := (@Etale : MorphismProperty Scheme.{u}))
      (Over.isPullback_of_binaryFan_isLimit _ (limit.isLimit _)) hKernel
  let e := (Over.forget S).mapIso D.kernelProductIsoKernelPair
  have hKernelPair : Etale
      (pullback.snd D.projectOverHom D.projectOverHom).left := by
    refine (MorphismProperty.cancel_left_of_respectsIso
      (@Etale : MorphismProperty Scheme.{u}) e.hom
      (pullback.snd D.projectOverHom D.projectOverHom).left).mp ?_
    change Etale (D.kernelProductIsoKernelPair.hom.left ≫
      (pullback.snd D.projectOverHom D.projectOverHom).left)
    simpa only [← Over.comp_left, D.kernelProductIsoKernelPair_hom_snd] using hKernelProduct
  have hPullback : IsPullback
      (pullback.fst D.projectOverHom D.projectOverHom).left
      (pullback.snd D.projectOverHom D.projectOverHom).left
      (hom D.project) (hom D.project) := by
    exact (IsPullback.of_hasPullback D.projectOverHom D.projectOverHom).map
      (Over.forget S)
  haveI : IsFinite (hom D.project) := D.project_isFinite
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := (@Etale : MorphismProperty Scheme.{u}))
    (Q := ((@Surjective : MorphismProperty Scheme.{u}) ⊓
      (@Flat : MorphismProperty Scheme.{u}) ⊓
      (@QuasiCompact : MorphismProperty Scheme.{u})))
    hPullback.flip
    ⟨⟨D.project_surjective, D.project_flat⟩, inferInstance⟩
    hKernelPair

/-- An actual fppf extension of two etale finite-flat commutative group schemes is etale. -/
theorem middle_etale_of_kernel_quotient_etale
    (D : FppfQuotientPresentation G)
    (hKernel : Etale D.kernelPresentation.kernel.structureMap)
    (hQuotient : Etale D.quotient.structureMap) :
    Etale G.structureMap := by
  letI : Etale (hom D.project) := D.project_etale_of_kernel_etale hKernel
  letI : Etale D.quotient.structureMap := hQuotient
  rw [← hom_comp_structureMap D.project]
  infer_instance

end FppfQuotientPresentation

end AlgebraicGeometry.FiniteFlatCommGroupScheme

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Upstream.SchemeModuleBaseChangeCech
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Cover-independent low-degree base change over fields

This file removes the affine-cover parameter from the checked degree-zero and degree-one
cohomology base-change comparison.  On a compact separated scheme it uses the finite subcover of
Mathlib's canonical affine cover.  Properness over a field supplies compactness and absolute
separatedness, so downstream proper-curve consumers need not choose a cover.

The design boundary remains low-degree base change between spectra of fields.  No general
proper-flat base-change theorem or semicontinuity statement is asserted.  The named downstream
consumer is `properCurveFieldExtensionLowDegreeBaseChange`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.Modules

namespace MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

/-- The canonical finite affine subcover removes all cover data from low-degree field-extension
base change on a compact separated scheme. -/
noncomputable def compactFieldExtensionLowDegreeBaseChange
    {P X : Scheme.{u}} (K L : Type u) [Field K] [Field L]
    [CompactSpace X] [X.IsSeparated]
    (fst : P ⟶ X) (snd : P ⟶ Spec (.of L))
    (f : X ⟶ Spec (.of K)) (g : Spec (.of L) ⟶ Spec (.of K))
    (h : IsPullback fst snd f g)
    (M : X.Modules) [M.IsQuasicoherent] :
    let N := (Scheme.Modules.pullback fst).obj M
    letI := baseSectionsHZeroModule f M
    letI := baseSectionsHZeroModule snd N
    let sourceZero := ModuleCat.of Γ(Spec (.of K), ⊤) (H M 0)
    let targetZero := ModuleCat.of Γ(Spec (.of L), ⊤) (H N 0)
    letI := baseSectionsHOneModule f M
    letI := baseSectionsHOneModule snd N
    let sourceOne := ModuleCat.of Γ(Spec (.of K), ⊤) (H M 1)
    let targetOne := ModuleCat.of Γ(Spec (.of L), ⊤) (H N 1)
    LowDegreeBaseChangeData g.appTop.hom
      sourceZero sourceOne targetZero targetOne := by
  let cover := X.affineCover.finiteSubcover
  let U : cover.I₀ → X.Opens := fun i ↦ (cover.f i).opensRange
  have hU : ∀ i, IsAffineOpen (U i) := fun i ↦
    isAffineOpen_opensRange (cover.f i)
  have hUcover : IsOpenCover U := cover.isOpenCover_opensRange
  exact fieldExtensionLowDegreeBaseChange
    K L fst snd f g h M U hU hUcover

/-- Properness over a field supplies the compactness and absolute separatedness needed by the
canonical finite-affine-cover construction. -/
noncomputable def properFieldExtensionLowDegreeBaseChange
    {P X : Scheme.{u}} (K L : Type u) [Field K] [Field L]
    (fst : P ⟶ X) (snd : P ⟶ Spec (.of L))
    (f : X ⟶ Spec (.of K)) [IsProper f]
    (g : Spec (.of L) ⟶ Spec (.of K))
    (h : IsPullback fst snd f g)
    (M : X.Modules) [M.IsQuasicoherent] :
    let N := (Scheme.Modules.pullback fst).obj M
    letI := baseSectionsHZeroModule f M
    letI := baseSectionsHZeroModule snd N
    let sourceZero := ModuleCat.of Γ(Spec (.of K), ⊤) (H M 0)
    let targetZero := ModuleCat.of Γ(Spec (.of L), ⊤) (H N 0)
    letI := baseSectionsHOneModule f M
    letI := baseSectionsHOneModule snd N
    let sourceOne := ModuleCat.of Γ(Spec (.of K), ⊤) (H M 1)
    let targetOne := ModuleCat.of Γ(Spec (.of L), ⊤) (H N 1)
    LowDegreeBaseChangeData g.appTop.hom
      sourceZero sourceOne targetZero targetOne := by
  letI : QuasiCompact f := inferInstance
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  letI : X.IsSeparated := by
    constructor
    rw [← terminal.comp_from f]
    infer_instance
  exact compactFieldExtensionLowDegreeBaseChange K L fst snd f g h M

/-- Cover-independent low-degree field-extension base change for a coherent module on a smooth
proper integral curve.  The curve hypotheses expose the exact interface consumed by the
proper-curve cohomology package; the comparison itself only needs properness and
quasicoherence. -/
noncomputable def properCurveFieldExtensionLowDegreeBaseChange
    {P X : Scheme.{u}} (K L : Type u) [Field K] [Field L]
    [IsIntegral X]
    (fst : P ⟶ X) (snd : P ⟶ Spec (.of L))
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (g : Spec (.of L) ⟶ Spec (.of K))
    (h : IsPullback fst snd f g)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    let N := (Scheme.Modules.pullback fst).obj M
    letI := baseSectionsHZeroModule f M
    letI := baseSectionsHZeroModule snd N
    let sourceZero := ModuleCat.of Γ(Spec (.of K), ⊤) (H M 0)
    let targetZero := ModuleCat.of Γ(Spec (.of L), ⊤) (H N 0)
    letI := baseSectionsHOneModule f M
    letI := baseSectionsHOneModule snd N
    let sourceOne := ModuleCat.of Γ(Spec (.of K), ⊤) (H M 1)
    let targetOne := ModuleCat.of Γ(Spec (.of L), ⊤) (H N 1)
    LowDegreeBaseChangeData g.appTop.hom
      sourceZero sourceOne targetZero targetOne :=
  properFieldExtensionLowDegreeBaseChange K L fst snd f g h M

end MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

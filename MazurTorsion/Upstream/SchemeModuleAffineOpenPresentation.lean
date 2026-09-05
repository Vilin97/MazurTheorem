/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.Upstream.SchemeModulePullbackCoherent

/-!
# Coherent presentations from an affine open

This file develops the affine-open presentation boundary for coherent
scheme modules.  On a separated scheme, an affine open immersion is affine;
consequently restriction to that open followed by pushforward remains
quasicoherent.  Finite generators on the affine open can then be transposed
globally and pulled back against the adjunction unit.

The named downstream consumer of `isAffineHom_ι_of_isAffineOpen` is the
open-local coherent presentation constructed later in this file.  Its
proper-curve consumer is `ProperCurveFiniteSupportCech`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open _root_.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {Y X : Scheme.{u}}

/-- The inclusion of an affine open in a separated scheme is affine. -/
theorem isAffineHom_ι_of_isAffineOpen [X.IsSeparated]
    (U : X.Opens) (hU : IsAffineOpen U) : IsAffineHom U.ι := by
  rw [isAffineHom_iff]
  intro V hV
  rw [← U.ι.isAffineOpen_iff_of_isOpenImmersion,
    U.ι.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact hU.inf hV

/-- Finite type for sheaves of modules is invariant under isomorphism. -/
theorem isFiniteType_of_iso
    {M N : X.Modules} (e : M ≅ N) [M.IsFiniteType] : N.IsFiniteType := by
  obtain ⟨q, hq⟩ :=
    SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  let qN : N.LocalGeneratorsData :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators := fun i ↦
        SheafOfModules.GeneratingSections.equivOfIso
          ((SheafOfModules.overFunctor X.ringCatSheaf (q.X i)).mapIso e)
          (q.generators i) }
  have hqN : qN.IsFiniteType := by
    constructor
    intro i
    letI : (q.generators i).IsFiniteType := hq.isFiniteType i
    dsimp [qN]
    constructor
    change Finite (q.generators i).I
    infer_instance
  refine { exists_localGeneratorsData := ?_ }
  exact ⟨qN, hqN⟩

/-- A coproduct indexed by a finite type of finite-type quasicoherent
modules is of finite type. -/
theorem isFiniteType_finite_coproduct
    {ι : Type} [Finite ι] (M : ι → X.Modules)
    (hqc : ∀ i, (M i).IsQuasicoherent)
    (hft : ∀ i, (M i).IsFiniteType) :
    (∐ M).IsFiniteType := by
  letI := Fintype.ofFinite ι
  let ε : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let N : Fin (Fintype.card ι) → X.Modules := M ∘ ε
  have hN : (∐ N).IsFiniteType :=
    isFiniteType_fin_coproduct N (fun i ↦ hqc (ε i))
      (fun i ↦ hft (ε i))
  letI : (∐ N).IsFiniteType := hN
  exact isFiniteType_of_iso (Sigma.reindex ε M)

/-- A binary biproduct of quasicoherent modules is quasicoherent. -/
theorem isQuasicoherent_biprod
    (M N : X.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (M ⊞ N).IsQuasicoherent := by
  let D : WalkingPair → X.Modules :=
    fun i ↦ (pair M N).obj ⟨i⟩
  have hD : ∀ i, (D i).IsQuasicoherent := by
    rintro (_ | _)
    · exact inferInstanceAs M.IsQuasicoherent
    · exact inferInstanceAs N.IsQuasicoherent
  have hSigma : (∐ D).IsQuasicoherent :=
    isQuasicoherent_coproduct D hD
  have hCoprod : (M ⨿ N).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (Sigma.isoColimit (pair M N)) hSigma
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (biprod.isoCoprod M N).symm hCoprod

/-- A binary biproduct of finite-type quasicoherent modules is of finite
type. -/
theorem isFiniteType_biprod
    (M N : X.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]
    [M.IsFiniteType] [N.IsFiniteType] : (M ⊞ N).IsFiniteType := by
  let D : WalkingPair → X.Modules :=
    fun i ↦ (pair M N).obj ⟨i⟩
  have hDqc : ∀ i, (D i).IsQuasicoherent := by
    rintro (_ | _)
    · exact inferInstanceAs M.IsQuasicoherent
    · exact inferInstanceAs N.IsQuasicoherent
  have hDft : ∀ i, (D i).IsFiniteType := by
    rintro (_ | _)
    · exact inferInstanceAs M.IsFiniteType
    · exact inferInstanceAs N.IsFiniteType
  have hSigma : (∐ D).IsFiniteType :=
    isFiniteType_finite_coproduct D hDqc hDft
  letI : (∐ D).IsFiniteType := hSigma
  have hCoprod : (M ⨿ N).IsFiniteType :=
    isFiniteType_of_iso (Sigma.isoColimit (pair M N))
  letI : (M ⨿ N).IsFiniteType := hCoprod
  exact isFiniteType_of_iso (biprod.isoCoprod M N).symm

/-- A pullback of quasicoherent modules in the ambient module category is
quasicoherent. -/
theorem isQuasicoherent_pullback
    {A M P : X.Modules} [A.IsQuasicoherent] [M.IsQuasicoherent]
    [P.IsQuasicoherent] (φ : A ⟶ P) (η : M ⟶ P) :
    (Limits.pullback φ η).IsQuasicoherent := by
  let B := A ⊞ M
  let a : B ⟶ P := biprod.desc φ (-η)
  letI : B.IsQuasicoherent := isQuasicoherent_biprod A M
  have hK : (kernel a).IsQuasicoherent := isQuasicoherent_kernel a
  let e : Limits.pullback φ η ≅ kernel a :=
    IsLimit.conePointUniqueUpToIso
      (_root_.CategoryTheory.Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct φ η)
      (limit.isLimit (parallelPair a 0))
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    e.symm hK

/-- On a locally Noetherian scheme, a pullback of two finite-type
quasicoherent modules over a quasicoherent target is of finite type. -/
theorem isFiniteType_pullback
    [IsLocallyNoetherian X]
    {A M P : X.Modules} [A.IsQuasicoherent] [M.IsQuasicoherent]
    [P.IsQuasicoherent] [A.IsFiniteType] [M.IsFiniteType]
    (φ : A ⟶ P) (η : M ⟶ P) :
    (Limits.pullback φ η).IsFiniteType := by
  let B := A ⊞ M
  let a : B ⟶ P := biprod.desc φ (-η)
  letI : B.IsQuasicoherent := isQuasicoherent_biprod A M
  letI : B.IsFiniteType := isFiniteType_biprod A M
  have hK : (kernel a).IsFiniteType := isFiniteType_kernel a
  letI : (kernel a).IsFiniteType := hK
  let e : kernel a ≅ Limits.pullback φ η :=
    (IsLimit.conePointUniqueUpToIso
      (_root_.CategoryTheory.Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct φ η)
      (limit.isLimit (parallelPair a 0))).symm
  exact isFiniteType_of_iso e

/-- Pulling back an adjoint transpose against the adjunction unit produces
an epimorphism after restriction whenever the original local map is epic.

This is the categorical core of the affine-open presentation: restriction
preserves the pullback, and in the restricted pullback the first leg is epic
because composing it with the adjunction counit recovers the given local
epimorphism. -/
theorem epi_restrict_pullback_snd_adjointTranspose
    (j : Y ⟶ X) [IsOpenImmersion j]
    (A M : X.Modules)
    (q : (restrictFunctor j).obj A ⟶ (restrictFunctor j).obj M)
    [Epi q] :
    Epi ((restrictFunctor j).map
      (pullback.snd
        ((restrictAdjunction j).homEquiv A
          ((restrictFunctor j).obj M) q)
        ((restrictAdjunction j).unit.app M))) := by
  let F := restrictFunctor j
  let adj := restrictAdjunction j
  let φ := adj.homEquiv A (F.obj M) q
  let η := adj.unit.app M
  letI : PreservesLimits F := restrictFunctor_preservesLimits j
  have hφ : F.map φ ≫ adj.counit.app (F.obj M) = q := by
    exact (adj.homEquiv A (F.obj M)).symm_apply_apply q
  letI : Epi (F.map φ) := by
    rw [← epi_comp_iff_of_isIso
      (F.map φ) (adj.counit.app (F.obj M)), hφ]
    infer_instance
  change Epi (F.map (pullback.snd φ η))
  rw [← PreservesPullback.iso_hom_snd F φ η]
  infer_instance

/-- In an adjunction-unit pullback, the projection to the global source is
monic after restriction. -/
theorem mono_restrict_pullback_fst_adjointTranspose
    (j : Y ⟶ X) [IsOpenImmersion j]
    (A M : X.Modules)
    (q : (restrictFunctor j).obj A ⟶ (restrictFunctor j).obj M) :
    Mono ((restrictFunctor j).map
      (pullback.fst
        ((restrictAdjunction j).homEquiv A
          ((restrictFunctor j).obj M) q)
        ((restrictAdjunction j).unit.app M))) := by
  let F := restrictFunctor j
  let adj := restrictAdjunction j
  let φ := adj.homEquiv A (F.obj M) q
  let η := adj.unit.app M
  letI : PreservesLimits F := restrictFunctor_preservesLimits j
  have hη : F.map η ≫ adj.counit.app (F.obj M) = 𝟙 (F.obj M) :=
    adj.left_triangle_components M
  letI : Mono (F.map η) := mono_of_mono_fac hη
  change Mono (F.map (pullback.fst φ η))
  rw [← PreservesPullback.iso_hom_fst F φ η]
  infer_instance

/-- In the same adjunction-unit pullback, the projection to the global
source has kernel vanishing after restriction.  The restricted unit is
monic by the left triangle identity, so its pullback projection is monic;
restriction preserving kernels then gives the claim. -/
theorem isZero_restrict_kernel_pullback_fst_adjointTranspose
    (j : Y ⟶ X) [IsOpenImmersion j]
    (A M : X.Modules)
    (q : (restrictFunctor j).obj A ⟶ (restrictFunctor j).obj M) :
    IsZero ((kernel
      (pullback.fst
        ((restrictAdjunction j).homEquiv A
          ((restrictFunctor j).obj M) q)
        ((restrictAdjunction j).unit.app M))).restrict j) := by
  let F := restrictFunctor j
  let adj := restrictAdjunction j
  let φ := adj.homEquiv A (F.obj M) q
  let η := adj.unit.app M
  letI : PreservesLimits F := restrictFunctor_preservesLimits j
  letI : Mono (F.map (pullback.fst φ η)) :=
    mono_restrict_pullback_fst_adjointTranspose j A M q
  have hzero : IsZero (kernel (F.map (pullback.fst φ η))) :=
    isZero_kernel_of_mono _
  change IsZero (F.obj (kernel (pullback.fst φ η)))
  exact hzero.of_iso (PreservesKernel.iso F (pullback.fst φ η))

/-- If a module morphism becomes monic after restriction, then the kernel
of its coimage-to-image map vanishes after restriction as well. -/
theorem isZero_restrict_kernel_factorThruImage_of_mono_map
    (j : Y ⟶ X) [IsOpenImmersion j]
    {M N : X.Modules} (f : M ⟶ N)
    [Mono ((restrictFunctor j).map f)] :
    IsZero ((kernel (Abelian.factorThruImage f)).restrict j) := by
  let F := restrictFunctor j
  letI : PreservesLimits F := restrictFunctor_preservesLimits j
  have hfac :
      F.map (Abelian.factorThruImage f) ≫
          F.map (Abelian.image.ι f) = F.map f := by
    rw [← F.map_comp, Abelian.image.fac]
  letI : Mono (F.map (Abelian.factorThruImage f)) :=
    mono_of_mono_fac hfac
  have hzero :
      IsZero (kernel (F.map (Abelian.factorThruImage f))) :=
    isZero_kernel_of_mono _
  change IsZero (F.obj (kernel (Abelian.factorThruImage f)))
  exact hzero.of_iso
    (PreservesKernel.iso F (Abelian.factorThruImage f))

/-- A finite free sheaf is of finite type. -/
theorem free_isFiniteType (X : Scheme.{u}) (I : Type u) [Finite I] :
    (SheafOfModules.free I (R := X.ringCatSheaf)).IsFiniteType := by
  let G := SheafOfModules.free.generatingSections
    (R := X.ringCatSheaf) I
  letI : G.IsFiniteType := by
    constructor
    change Finite I
    infer_instance
  have hGlocal : G.localGeneratorsData.IsFiniteType := by
    constructor
    intro i
    constructor
    change Finite I
    infer_instance
  exact
    { exists_localGeneratorsData :=
        ⟨G.localGeneratorsData, hGlocal⟩ }

/-- A coherent presentation obtained from generators on an affine open.
The source maps globally to a finite free sheaf and to the original module;
after restriction, the first map is monic and the second is epic. -/
structure AffineOpenPresentation (M : X.Modules) (U : X.Opens) where
  I : Type u
  finite_I : Finite I
  source : X.Modules
  source_isFiniteType : source.IsFiniteType
  source_isQuasicoherent : source.IsQuasicoherent
  toFree : source ⟶ SheafOfModules.free I (R := X.ringCatSheaf)
  toModule : source ⟶ M
  mono_restrict_toFree : Mono ((restrictFunctor U.ι).map toFree)
  epi_restrict_toModule : Epi ((restrictFunctor U.ι).map toModule)

/-- Finite generators on an affine open of a separated locally Noetherian
scheme produce an open-local coherent presentation.  The construction takes
the adjoint transpose of the local finite-free epimorphism and pulls it back
against the restriction--pushforward unit. -/
theorem exists_affineOpenPresentation
    [X.IsSeparated] [IsLocallyNoetherian X]
    (M : X.Modules) [M.IsFiniteType] [M.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) :
    Nonempty (AffineOpenPresentation M U) := by
  let UA : X.affineOpens := ⟨U, hU⟩
  obtain ⟨G, hG⟩ :=
    exists_generatingSections_restrict_of_isFiniteType_of_isAffineOpen M UA
  letI : G.IsFiniteType := hG
  letI : Finite G.I :=
    SheafOfModules.GeneratingSections.IsFiniteType.finite
  let F := restrictFunctor U.ι
  letI : PreservesColimitsOfSize.{u, u} F := by
    dsimp [F]
    infer_instance
  let hDiscrete : PreservesColimitsOfShape.{u, u} (Discrete G.I) F :=
    (restrictAdjunction U.ι).leftAdjoint_preservesColimits.preservesColimitsOfShape
  let A : X.Modules := SheafOfModules.free G.I
  let eFree := @SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _
    F G.I hDiscrete (restrictUnitIso U.ι).symm
  let q : F.obj A ⟶ F.obj M :=
    eFree.inv ≫ G.π
  letI : Epi G.π := G.epi
  letI : Epi q := by
    exact epi_comp' (inferInstance : Epi eFree.inv) G.epi
  let adj := restrictAdjunction U.ι
  let φ := adj.homEquiv A (F.obj M) q
  let η := adj.unit.app M
  let E := Limits.pullback φ η
  let e : E ⟶ A := pullback.fst φ η
  let g : E ⟶ M := pullback.snd φ η
  letI : IsAffineHom U.ι := isAffineHom_ι_of_isAffineOpen U hU
  let P := (pushforward U.ι).obj (F.obj M)
  letI : (F.obj M).IsQuasicoherent := by
    dsimp [F]
    infer_instance
  letI : P.IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom U.ι
  letI : A.IsQuasicoherent := by
    dsimp [A]
    infer_instance
  letI : A.IsFiniteType := by
    dsimp [A]
    exact free_isFiniteType X G.I
  letI : E.IsQuasicoherent := by
    dsimp [E, φ, η, P, adj]
    exact isQuasicoherent_pullback _ _
  letI : E.IsFiniteType := by
    dsimp [E, φ, η, P, adj]
    exact isFiniteType_pullback _ _
  exact ⟨
    { I := G.I
      finite_I := inferInstance
      source := E
      source_isFiniteType := inferInstance
      source_isQuasicoherent := inferInstance
      toFree := e
      toModule := g
      mono_restrict_toFree := by
        dsimp [e, E, φ, η, adj]
        exact mono_restrict_pullback_fst_adjointTranspose U.ι A M q
      epi_restrict_toModule := by
        dsimp [g, E, φ, η, adj]
        exact epi_restrict_pullback_snd_adjointTranspose U.ι A M q }⟩

end AlgebraicGeometry.Scheme.Modules

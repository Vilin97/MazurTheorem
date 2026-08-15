/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.Rationalization
import MazurTorsion.Upstream.LeanPool.GrothendieckVanishing.ClosedImmersionCohomology
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Scheme-module pushforward and topological cohomology

The underlying abelian sheaf of the scheme-theoretic module pushforward is
the ordinary direct image along the underlying continuous map.  This file
records that comparison explicitly, as preparation for the closed-immersion
reduction.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Abelian Limits Opposite
  TensorProduct

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

namespace TopCat

noncomputable local instance schemePushforwardCohomologyAddCommGroup
    {Z : TopCat.{u}}
    (G : Z.Sheaf AddCommGrpCat.{u}) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H G n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

/-- An open set contained in the complement of the range of an embedding
has empty inverse image. -/
lemma opensMap_eq_bot_of_le_compl_range
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : Topology.IsClosedEmbedding f)
    {U : Opens Y}
    (hU : U ≤ ⟨(Set.range f)ᶜ, hf.isClosed_range.isOpen_compl⟩) :
    (Opens.map f).obj U = ⊥ := by
  apply Opens.ext
  change f ⁻¹' (U : Set Y) = (⊥ : Opens X)
  have hdisj : Disjoint (U : Set Y) (Set.range f) :=
    Set.disjoint_left.mpr fun y hyU hyf => hU hyU hyf
  simpa using Set.preimage_eq_empty hdisj

/-- The stalk of a direct image along a closed embedding vanishes away
from the image. -/
theorem pushforward_stalk_eq_zero_of_not_mem_range
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : Topology.IsClosedEmbedding f)
    {G : X.Presheaf AddCommGrpCat.{u}} (hG : G.IsSheaf)
    {y : Y} (hy : y ∉ Set.range f)
    (a : (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).obj
      ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).obj G)) :
    a = 0 := by
  let Gsh : X.Sheaf AddCommGrpCat.{u} := ⟨G, hG⟩
  let F' := (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).obj G
  obtain ⟨U, hyU, sU, rfl⟩ := F'.exists_germ_eq a
  let W : Opens Y :=
    U ⊓ ⟨(Set.range f)ᶜ, hf.isClosed_range.isOpen_compl⟩
  have hW_map : (Opens.map f).obj W = ⊥ :=
    opensMap_eq_bot_of_le_compl_range hf inf_le_right
  haveI : Subsingleton (F'.obj (op W)) :=
    AddCommGrpCat.subsingleton_of_isZero (by
      change IsZero (G.obj (op ((Opens.map f).obj W)))
      rw [hW_map]
      exact Gsh.isTerminalOfEmpty.isZero)
  rw [← TopCat.Presheaf.germ_res_apply F'
    (homOfLE (show W ≤ U from inf_le_left)) y ⟨hyU, hy⟩ sU]
  rw [Subsingleton.eq_zero
    (ConcreteCategory.hom
      (F'.map (homOfLE (show W ≤ U from inf_le_left)).op) sU)]
  exact map_zero _

/-- Direct image along a closed embedding sends a locally-surjective map
of sheaves to an epimorphism. -/
theorem epi_pushforward_map_of_isClosedEmbedding
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : Topology.IsClosedEmbedding f)
    {F G : X.Presheaf AddCommGrpCat.{u}}
    (hF : F.IsSheaf) (hG : G.IsSheaf)
    (α : F ⟶ G)
    (hα : TopCat.Presheaf.IsLocallySurjective α) :
    Epi ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map
      (show (⟨F, hF⟩ : X.Sheaf AddCommGrpCat.{u}) ⟶
        (⟨G, hG⟩ : X.Sheaf AddCommGrpCat.{u}) from
          ObjectProperty.homMk α)) := by
  let αsh : (⟨F, hF⟩ : X.Sheaf AddCommGrpCat.{u}) ⟶
      (⟨G, hG⟩ : X.Sheaf AddCommGrpCat.{u}) :=
    ObjectProperty.homMk α
  letI : Balanced (Sheaf (Opens.grothendieckTopology Y)
      AddCommGrpCat.{u}) :=
    balanced_of_strongEpiCategory
  change Epi ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map αsh)
  rw [← TopCat.Sheaf.isLocallySurjective_iff_epi
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map αsh)]
  rw [TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks]
  intro y
  by_cases hy : y ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hy
    haveI hEpiF :
        Epi ((TopCat.Presheaf.stalkFunctor
          AddCommGrpCat.{u} x).map α) :=
      (AddCommGrpCat.epi_iff_surjective _).mpr
        (((TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
          (T := α)).mp hα) x)
    have hnat :
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map
            ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map α) ≫
          TopCat.Presheaf.stalkPushforward
            AddCommGrpCat.{u} f G x =
        TopCat.Presheaf.stalkPushforward
            AddCommGrpCat.{u} f F x ≫
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map α := by
      apply TopCat.Presheaf.stalk_hom_ext
      intro U hU
      erw [← Category.assoc]
      rw [TopCat.Presheaf.stalkFunctor_map_germ U (f x) hU
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map α)]
      erw [Category.assoc]
      erw [TopCat.Presheaf.stalkPushforward_germ]
      erw [TopCat.Presheaf.stalkPushforward_germ_assoc]
      erw [TopCat.Presheaf.stalkFunctor_map_germ]
      rfl
    apply (AddCommGrpCat.epi_iff_surjective _).mp
    change Epi
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map
        ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map α))
    haveI : IsIso
        (TopCat.Presheaf.stalkPushforward
          AddCommGrpCat.{u} f F x) :=
      TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
        AddCommGrpCat.{u} hf.isInducing F x
    haveI : IsIso
        (TopCat.Presheaf.stalkPushforward
          AddCommGrpCat.{u} f G x) :=
      TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
        AddCommGrpCat.{u} hf.isInducing G x
    have hcomp :
        Epi (TopCat.Presheaf.stalkPushforward
          AddCommGrpCat.{u} f F x ≫
            (TopCat.Presheaf.stalkFunctor
              AddCommGrpCat.{u} x).map α) :=
      @epi_comp _ _ _ _ _
        (TopCat.Presheaf.stalkPushforward
          AddCommGrpCat.{u} f F x)
        inferInstance
        ((TopCat.Presheaf.stalkFunctor
          AddCommGrpCat.{u} x).map α)
        hEpiF
    have hcomp' :
        Epi ((TopCat.Presheaf.stalkFunctor
          AddCommGrpCat.{u} (f x)).map
            ((TopCat.Presheaf.pushforward
              AddCommGrpCat.{u} f).map α) ≫
          TopCat.Presheaf.stalkPushforward
            AddCommGrpCat.{u} f G x) := by
      rw [hnat]
      exact hcomp
    exact (epi_comp_iff_of_isIso _
      (TopCat.Presheaf.stalkPushforward
        AddCommGrpCat.{u} f G x)).mp hcomp'
  · intro b
    rw [pushforward_stalk_eq_zero_of_not_mem_range hf hG hy b]
    exact ⟨0, AddMonoidHom.map_zero _⟩

/-- Direct image along a closed embedding preserves epimorphisms. -/
theorem pushforwardPreservesEpimorphismsOfIsClosedEmbedding
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : Topology.IsClosedEmbedding f) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).PreservesEpimorphisms where
  preserves {F G} α hα := by
    letI : Epi α := hα
    letI : Balanced (Sheaf (Opens.grothendieckTopology Y)
        AddCommGrpCat.{u}) :=
      balanced_of_strongEpiCategory
    have hαloc : TopCat.Presheaf.IsLocallySurjective α.hom :=
      (TopCat.Sheaf.isLocallySurjective_iff_epi α).mpr inferInstance
    change Epi ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map
      (ObjectProperty.homMk α.hom))
    exact epi_pushforward_map_of_isClosedEmbedding
      hf F.property G.property α.hom hαloc

/-- Direct image along a closed embedding preserves short exact
sequences. -/
theorem pushforward_shortExact_of_isClosedEmbedding
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : Topology.IsClosedEmbedding f)
    {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
    (hS : S.ShortExact) :
    (S.map (TopCat.Sheaf.pushforward
      AddCommGrpCat.{u} f)).ShortExact := by
  let F := TopCat.Sheaf.pushforward AddCommGrpCat.{u} f
  letI : F.PreservesEpimorphisms :=
    pushforwardPreservesEpimorphismsOfIsClosedEmbedding hf
  haveI := hS.mono_f
  haveI := hS.epi_g
  haveI : Mono (F.map S.f) := inferInstance
  haveI : Epi (F.map S.g) := inferInstance
  exact ShortComplex.ShortExact.mk'
    (hS.exact.map_of_mono_of_preservesKernel _
      hS.mono_f inferInstance) ‹_› ‹_›

/-- Direct image along a closed embedding preserves sheaf cohomology in
every degree. -/
noncomputable def pushforwardHIsoOfIsClosedEmbedding
    {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : Topology.IsClosedEmbedding f)
    (G : X.Sheaf AddCommGrpCat.{u})
    (n : ℕ) :
    AddCommGrpCat.of (Sheaf.H G n) ≅
      AddCommGrpCat.of
        (Sheaf.H
          ((TopCat.Sheaf.pushforward
            AddCommGrpCat.{u} f).obj G) n) := by
  induction n generalizing G with
  | zero =>
      change (sheafCohomologyFunctor X 0).obj G ≅
        (sheafCohomologyFunctor Y 0).obj
          ((TopCat.Sheaf.pushforward
            AddCommGrpCat.{u} f).obj G)
      simpa [Opens.map_top] using
        (sheafH0NatIsoSections (X := X)).app G ≪≫
          ((sheafH0NatIsoSections (X := Y)).app
            ((TopCat.Sheaf.pushforward
              AddCommGrpCat.{u} f).obj G)).symm
  | succ k ih =>
      classical
      let ip : InjectivePresentation G :=
        Classical.choice (EnoughInjectives.presentation G)
      let S := ip.shortComplex
      let hInjective : Injective S.X₂ := by
        change Injective ip.J
        exact ip.injective
      letI : Injective S.X₂ := hInjective
      let SY := S.map
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f)
      have hSEY : SY.ShortExact :=
        pushforward_shortExact_of_isClosedEmbedding
          hf ip.shortExact_shortComplex
      have hFlasqueSY₂ : IsFlasqueSheaf SY.X₂ :=
        fun j => by
          change Epi
            (S.X₂.obj.map ((Opens.map f).op.map j.op))
          exact (isFlasque_of_injective S.X₂)
            ((Opens.map f).map j)
      have hSE : S.ShortExact := by
        simpa [S] using ip.shortExact_shortComplex
      have hSrcSub (r : ℕ) :
          Subsingleton (Sheaf.H S.X₂ (r + 1)) :=
        @sheafH_subsingleton_of_injective
          (Opens X) _ (Opens.grothendieckTopology X)
          _ _ S.X₂ hInjective r
      have hTgtSub (r : ℕ) :
          Subsingleton (Sheaf.H SY.X₂ (r + 1)) :=
        sheafH_subsingleton_of_flasque
          Y SY.X₂ hFlasqueSY₂ r
      change (sheafCohomologyFunctor X (k + 1)).obj G ≅
        (sheafCohomologyFunctor Y (k + 1)).obj SY.X₁
      cases k with
      | zero =>
          simpa [S, SY] using
            (show cokernel (SY.g.hom.app (op ⊤)) ≅
                (sheafCohomologyFunctor X 1).obj G from by
              change cokernel (S.g.hom.app (op ⊤)) ≅
                (sheafCohomologyFunctor X 1).obj S.X₁
              exact
                sheafH1CokernelIsoOfSubsingletonMiddle
                  hSE (hSrcSub 0)).symm ≪≫
              sheafH1CokernelIsoOfSubsingletonMiddle
                hSEY (hTgtSub 0)
      | succ m =>
          simpa [S, SY] using
            (sheafHSuccIsoOfSubsingletonMiddle hSE
              (m + 1) (hSrcSub m)
              (hSrcSub (m + 1))).symm ≪≫
              ih S.X₃ ≪≫
                sheafHSuccIsoOfSubsingletonMiddle hSEY
                  (m + 1) (hTgtSub m)
                  (hTgtSub (m + 1))

end TopCat

end MazurTorsion.AlgebraicGeometry.CoherentCohomology

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

variable {X Y : Scheme.{0}} (i : X ⟶ Y) (M : X.Modules)

noncomputable local instance schemeCohomologyAddCommGroup
    {Z : TopCat.{0}}
    (G : Z.Sheaf AddCommGrpCat.{0}) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H G n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

/-- Forgetting scalars commutes definitionally with direct image. -/
lemma pushforward_sheaf_eq :
    ((Scheme.Modules.pushforward i).obj M).sheaf =
      (TopCat.Sheaf.pushforward AddCommGrpCat.{0} i.base).obj M.sheaf :=
  rfl

/-- Cohomology of a module sheaf is unchanged by pushforward along a
closed immersion of schemes. -/
noncomputable def closedImmersionPushforwardHIso
    (i : X ⟶ Y) [_root_.AlgebraicGeometry.IsClosedImmersion i]
    (M : X.Modules) (n : ℕ) :
    AddCommGrpCat.of (M.sheaf.H n) ≅
      AddCommGrpCat.of
        (((Scheme.Modules.pushforward i).obj M).sheaf.H n) := by
  exact
    MazurTorsion.AlgebraicGeometry.CoherentCohomology.TopCat.pushforwardHIsoOfIsClosedEmbedding
      i.isClosedEmbedding M.sheaf n

/-- The induced linear equivalence after rationalization. -/
noncomputable def closedImmersionRationalizedCohomologyLinearEquiv
    (i : X ⟶ Y) [_root_.AlgebraicGeometry.IsClosedImmersion i]
    (M : X.Modules) (n : ℕ) :
    ℚ ⊗[ℤ] M.sheaf.H n ≃ₗ[ℚ]
      ℚ ⊗[ℤ]
        ((Scheme.Modules.pushforward i).obj M).sheaf.H n :=
  rationalizationMapAddEquiv
    (closedImmersionPushforwardHIso i M n).addCommGroupIsoToAddEquiv

/-- Rationalized finite-dimensional cohomology is invariant under
scheme-theoretic closed-immersion pushforward. -/
theorem closedImmersion_rationalizedCohomology_finite_iff
    (i : X ⟶ Y) [_root_.AlgebraicGeometry.IsClosedImmersion i]
    (M : X.Modules) (n : ℕ) :
    Module.Finite ℚ (ℚ ⊗[ℤ] M.sheaf.H n) ↔
      Module.Finite ℚ
        (ℚ ⊗[ℤ]
          ((Scheme.Modules.pushforward i).obj M).sheaf.H n) :=
  rationalization_finite_congr
    (closedImmersionPushforwardHIso i M n).addCommGroupIsoToAddEquiv

end MazurTorsion.AlgebraicGeometry.CoherentCohomology

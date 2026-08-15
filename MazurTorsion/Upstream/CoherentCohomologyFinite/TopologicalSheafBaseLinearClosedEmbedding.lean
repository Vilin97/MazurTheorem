/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemePushforwardCohomology
import MazurTorsion.Upstream.CoherentCohomologyFinite.TopologicalSheafBaseLinearPullback
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Base-linear direct image along a closed embedding

Direct image of sheaves is always left exact.  For a closed embedding it
also preserves epimorphisms, hence is exact.  This file proves that
statement for sheaves of modules over a fixed coefficient ring.
-/


open CategoryTheory Limits TopologicalSpace

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.TopCat

variable {R : Type u} [CommRing R]
variable {X Y : TopCat.{u}}

/-- Away from the image of a closed embedding, the stalk of a
base-linear direct image is zero. -/
theorem baseLinearPushforward_stalk_eq_zero_of_not_mem_range
    {f : X ⟶ Y}
    (hf : Topology.IsClosedEmbedding f)
    {G : X.Presheaf (ModuleCat.{u} R)}
    (hG : G.IsSheaf)
    {y : Y} (hy : y ∉ Set.range f)
    (a : (TopCat.Presheaf.stalkFunctor
      (ModuleCat.{u} R) y).obj
        ((TopCat.Presheaf.pushforward
          (ModuleCat.{u} R) f).obj G)) :
    a = 0 := by
  let Gsh : X.Sheaf (ModuleCat.{u} R) := ⟨G, hG⟩
  let F' :=
    (TopCat.Presheaf.pushforward
      (ModuleCat.{u} R) f).obj G
  obtain ⟨U, hyU, sU, rfl⟩ :=
    F'.exists_germ_eq a
  let W : Opens Y :=
    U ⊓
      ⟨(Set.range f)ᶜ,
        hf.isClosed_range.isOpen_compl⟩
  have hW_map :
      (Opens.map f).obj W = ⊥ :=
    opensMap_eq_bot_of_le_compl_range
      hf inf_le_right
  haveI : Subsingleton (F'.obj (Opposite.op W)) :=
    ModuleCat.subsingleton_of_isZero (by
      change IsZero
        (G.obj
          (Opposite.op ((Opens.map f).obj W)))
      rw [hW_map]
      exact Gsh.isTerminalOfEmpty.isZero)
  rw [← TopCat.Presheaf.germ_res_apply F'
    (homOfLE
      (show W ≤ U from inf_le_left))
    y ⟨hyU, hy⟩ sU]
  rw [Subsingleton.eq_zero
    (ConcreteCategory.hom
      (F'.map
        (homOfLE
          (show W ≤ U from inf_le_left)).op)
      sU)]
  exact map_zero _

/-- Direct image along a closed embedding sends a locally surjective
map of base-linear sheaves to an epimorphism. -/
theorem epi_baseLinearPushforward_map_of_isClosedEmbedding
    {f : X ⟶ Y}
    (hf : Topology.IsClosedEmbedding f)
    {F G : X.Presheaf (ModuleCat.{u} R)}
    (hF : F.IsSheaf) (hG : G.IsSheaf)
    (α : F ⟶ G)
    (hα : TopCat.Presheaf.IsLocallySurjective α) :
    Epi
      ((TopCat.Sheaf.pushforward
        (ModuleCat.{u} R) f).map
        (show
          (⟨F, hF⟩ :
            X.Sheaf (ModuleCat.{u} R)) ⟶
          (⟨G, hG⟩ :
            X.Sheaf (ModuleCat.{u} R))
          from ObjectProperty.homMk α)) := by
  let αsh :
      (⟨F, hF⟩ :
        X.Sheaf (ModuleCat.{u} R)) ⟶
      (⟨G, hG⟩ :
        X.Sheaf (ModuleCat.{u} R)) :=
    ObjectProperty.homMk α
  letI :
      Balanced
        (Sheaf (Opens.grothendieckTopology Y)
          (ModuleCat.{u} R)) :=
    balanced_of_strongEpiCategory
  change Epi
    ((TopCat.Sheaf.pushforward
      (ModuleCat.{u} R) f).map αsh)
  rw [← TopCat.Sheaf.isLocallySurjective_iff_epi
    ((TopCat.Sheaf.pushforward
      (ModuleCat.{u} R) f).map αsh)]
  rw [TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks]
  intro y
  by_cases hy : y ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hy
    haveI hEpiF :
        Epi
          ((TopCat.Presheaf.stalkFunctor
            (ModuleCat.{u} R) x).map α) :=
      (ModuleCat.epi_iff_surjective _).mpr
        (((TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
          (T := α)).mp hα) x)
    have hnat :
        (TopCat.Presheaf.stalkFunctor
          (ModuleCat.{u} R) (f x)).map
            ((TopCat.Presheaf.pushforward
              (ModuleCat.{u} R) f).map α) ≫
          TopCat.Presheaf.stalkPushforward
            (ModuleCat.{u} R) f G x =
        TopCat.Presheaf.stalkPushforward
            (ModuleCat.{u} R) f F x ≫
          (TopCat.Presheaf.stalkFunctor
            (ModuleCat.{u} R) x).map α :=
      Presheaf.stalkPushforward_naturality
        f α x
    apply
      (ModuleCat.epi_iff_surjective _).mp
    change Epi
      ((TopCat.Presheaf.stalkFunctor
        (ModuleCat.{u} R) (f x)).map
        ((TopCat.Presheaf.pushforward
          (ModuleCat.{u} R) f).map α))
    haveI :
        IsIso
          (TopCat.Presheaf.stalkPushforward
            (ModuleCat.{u} R) f F x) :=
      TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
        (ModuleCat.{u} R) hf.isInducing F x
    haveI :
        IsIso
          (TopCat.Presheaf.stalkPushforward
            (ModuleCat.{u} R) f G x) :=
      TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
        (ModuleCat.{u} R) hf.isInducing G x
    have hcomp :
        Epi
          (TopCat.Presheaf.stalkPushforward
              (ModuleCat.{u} R) f F x ≫
            (TopCat.Presheaf.stalkFunctor
              (ModuleCat.{u} R) x).map α) :=
      @epi_comp _ _ _ _ _
        (TopCat.Presheaf.stalkPushforward
          (ModuleCat.{u} R) f F x)
        inferInstance
        ((TopCat.Presheaf.stalkFunctor
          (ModuleCat.{u} R) x).map α)
        hEpiF
    have hcomp' :
        Epi
          ((TopCat.Presheaf.stalkFunctor
            (ModuleCat.{u} R) (f x)).map
              ((TopCat.Presheaf.pushforward
                (ModuleCat.{u} R) f).map α) ≫
            TopCat.Presheaf.stalkPushforward
              (ModuleCat.{u} R) f G x) := by
      rw [hnat]
      exact hcomp
    exact
      (epi_comp_iff_of_isIso _
        (TopCat.Presheaf.stalkPushforward
          (ModuleCat.{u} R) f G x)).mp hcomp'
  · intro b
    rw [baseLinearPushforward_stalk_eq_zero_of_not_mem_range
      hf hG hy b]
    exact ⟨0, LinearMap.map_zero _⟩

/-- Direct image along a closed embedding preserves epimorphisms for
sheaves of modules over a fixed ring. -/
theorem baseLinearPushforward_preservesEpimorphisms
    {f : X ⟶ Y}
    (hf : Topology.IsClosedEmbedding f) :
    (TopCat.Sheaf.pushforward
      (ModuleCat.{u} R) f).PreservesEpimorphisms where
  preserves {F G} α hα := by
    letI : Epi α := hα
    letI :
        Balanced
          (Sheaf (Opens.grothendieckTopology Y)
            (ModuleCat.{u} R)) :=
      balanced_of_strongEpiCategory
    have hαloc :
        TopCat.Presheaf.IsLocallySurjective α.hom :=
      (TopCat.Sheaf.isLocallySurjective_iff_epi α).mpr
        inferInstance
    change Epi
      ((TopCat.Sheaf.pushforward
        (ModuleCat.{u} R) f).map
        (ObjectProperty.homMk α.hom))
    exact
      epi_baseLinearPushforward_map_of_isClosedEmbedding
        hf F.property G.property α.hom hαloc

/-- Base-linear direct image along a closed embedding is exact. -/
theorem baseLinearPushforward_preservesFiniteColimits
    {f : X ⟶ Y}
    (hf : Topology.IsClosedEmbedding f) :
    PreservesFiniteColimits
      (TopCat.Sheaf.pushforward
        (ModuleCat.{u} R) f) := by
  let P :=
    TopCat.Sheaf.pushforward
      (ModuleCat.{u} R) f
  letI : P.PreservesEpimorphisms :=
    baseLinearPushforward_preservesEpimorphisms
      (R := R) hf
  letI : PreservesFiniteLimits P := inferInstance
  letI : P.Additive :=
    P.additive_of_preserves_binary_products
  letI : P.PreservesHomology := by
    apply
      Functor.preservesHomology_of_preservesEpis_and_kernels
  exact
    Functor.preservesFiniteColimits_of_preservesHomology P

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.TopCat

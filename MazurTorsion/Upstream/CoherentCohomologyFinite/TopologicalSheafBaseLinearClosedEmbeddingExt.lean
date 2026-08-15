/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ExtLinearAdjunction
import MazurTorsion.Upstream.CoherentCohomologyFinite.ExtLinearFiniteBiproduct
import MazurTorsion.Upstream.CoherentCohomologyFinite.TopologicalSheafBaseLinearCategory
import MazurTorsion.Upstream.CoherentCohomologyFinite.TopologicalSheafBaseLinearExt

/-!
# Constant-source Ext across a closed embedding

For sheaves of modules over a fixed coefficient ring, direct image
along a closed embedding is exact.  The pullback/direct-image
adjunction therefore identifies Ext from the constant rank-one sheaf
on the source with Ext from the constant rank-one sheaf on the target.
-/


open CategoryTheory Limits TopologicalSpace

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.TopCat

variable {R : Type u} [CommRing R]
variable {X Y : TopCat.{u}}

noncomputable local instance closedEmbeddingExtAddCommGroup
    {Z : TopCat.{u}} (B : Z.Sheaf (ModuleCat.{u} R)) (n : ℕ) :
    AddCommGroup (Abelian.Ext
      ((constantSheaf (Opens.grothendieckTopology Z) (ModuleCat.{u} R)).obj
        (ModuleCat.of R R)) B n) := by
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

noncomputable local instance closedEmbeddingExtModule
    {Z : TopCat.{u}} (B : Z.Sheaf (ModuleCat.{u} R)) (n : ℕ) :
    Module R (Abelian.Ext
      ((constantSheaf (Opens.grothendieckTopology Z) (ModuleCat.{u} R)).obj
        (ModuleCat.of R R)) B n) := by
  exact CategoryTheory.Abelian.Ext.instModule

noncomputable local instance closedEmbeddingPullbackExtAddCommGroup
    {Z W : TopCat.{u}} (f : Z ⟶ W)
    (B : Z.Sheaf (ModuleCat.{u} R)) (n : ℕ) :
    AddCommGroup (Abelian.Ext
      ((TopCat.Sheaf.pullback (ModuleCat.{u} R) f).obj
        ((constantSheaf (Opens.grothendieckTopology W) (ModuleCat.{u} R)).obj
          (ModuleCat.of R R))) B n) := by
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

noncomputable local instance closedEmbeddingPullbackExtModule
    {Z W : TopCat.{u}} (f : Z ⟶ W)
    (B : Z.Sheaf (ModuleCat.{u} R)) (n : ℕ) :
    Module R (Abelian.Ext
      ((TopCat.Sheaf.pullback (ModuleCat.{u} R) f).obj
        ((constantSheaf (Opens.grothendieckTopology W) (ModuleCat.{u} R)).obj
          (ModuleCat.of R R))) B n) := by
  exact CategoryTheory.Abelian.Ext.instModule

/-- The constant rank-one sheaf of `R`-modules on a topological
space. -/
abbrev constantRankOneSheaf
    (X : TopCat.{u}) :
    X.Sheaf (ModuleCat.{u} R) :=
  (constantSheaf
    (Opens.grothendieckTopology X)
    (ModuleCat.{u} R)).obj
      (ModuleCat.of R R)

/-- Ext from the constant rank-one sheaf is unchanged by exact direct
image along a closed embedding. -/
noncomputable def closedEmbeddingConstantExtLinearEquiv
    (f : X ⟶ Y)
    (hf : Topology.IsClosedEmbedding f)
    (F : X.Sheaf (ModuleCat.{u} R))
    (n : ℕ) :
    Abelian.Ext
        (constantRankOneSheaf (R := R) X)
        F n ≃ₗ[R]
      Abelian.Ext
        (constantRankOneSheaf (R := R) Y)
        ((TopCat.Sheaf.pushforward
          (ModuleCat.{u} R) f).obj F) n := by
  letI : AddCommGroup (Abelian.Ext
      (constantRankOneSheaf (R := R) X) F n) :=
    CategoryTheory.Abelian.Ext.instAddCommGroup
  letI : Module R (Abelian.Ext
      (constantRankOneSheaf (R := R) X) F n) :=
    CategoryTheory.Abelian.Ext.instModule
  letI : AddCommGroup (Abelian.Ext
      (constantRankOneSheaf (R := R) Y)
      ((TopCat.Sheaf.pushforward (ModuleCat.{u} R) f).obj F) n) :=
    CategoryTheory.Abelian.Ext.instAddCommGroup
  letI : Module R (Abelian.Ext
      (constantRankOneSheaf (R := R) Y)
      ((TopCat.Sheaf.pushforward (ModuleCat.{u} R) f).obj F) n) :=
    CategoryTheory.Abelian.Ext.instModule
  let pulledConstant :=
    (TopCat.Sheaf.pullback (ModuleCat.{u} R) f).obj
      (constantRankOneSheaf (R := R) Y)
  letI : AddCommGroup (Abelian.Ext pulledConstant F n) :=
    CategoryTheory.Abelian.Ext.instAddCommGroup
  letI : Module R (Abelian.Ext pulledConstant F n) :=
    CategoryTheory.Abelian.Ext.instModule
  let L :=
    TopCat.Sheaf.pullback
      (ModuleCat.{u} R) f
  let U :=
    TopCat.Sheaf.pushforward
      (ModuleCat.{u} R) f
  letI : PreservesFiniteColimits U :=
    baseLinearPushforward_preservesFiniteColimits
      (R := R) hf
  letI : U.Additive :=
    U.additive_of_preserves_binary_products
  exact
    (ExtAdjunction.precompIsoLinearEquiv
      (R := R)
      (C := X.Sheaf (ModuleCat.{u} R))
      (constantRankOnePullbackIso
        (R := R) f) n).trans
      (ExtAdjunction.extLinearEquiv
        (R := R)
        (C := Y.Sheaf (ModuleCat.{u} R))
        (D := X.Sheaf (ModuleCat.{u} R))
        L U
        (TopCat.Sheaf.pullbackPushforwardAdjunction
          (ModuleCat.{u} R) f)
        (constantRankOneSheaf (R := R) Y)
        F n)

/-- Finite generation of constant-source Ext is equivalent before and
after exact direct image along a closed embedding. -/
theorem closedEmbeddingConstantExt_finite_iff
    (f : X ⟶ Y)
    (hf : Topology.IsClosedEmbedding f)
    (F : X.Sheaf (ModuleCat.{u} R))
    (n : ℕ) :
    Module.Finite R
        (Abelian.Ext
          (constantRankOneSheaf (R := R) X)
          F n) ↔
      Module.Finite R
        (Abelian.Ext
          (constantRankOneSheaf (R := R) Y)
          ((TopCat.Sheaf.pushforward
            (ModuleCat.{u} R) f).obj F) n) := by
  let e :=
    closedEmbeddingConstantExtLinearEquiv
      (R := R) f hf F n
  constructor
  · intro h
    letI := h
    exact Module.Finite.equiv e
  · intro h
    letI := h
    exact Module.Finite.equiv e.symm

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.TopCat

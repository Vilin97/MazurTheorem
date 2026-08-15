/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeModuleScalarBaseChange
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentCocycle
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafModuleCoverDescentNaturality

/-!
# Scalar-twisted canonical cover descent

A family of units on pairwise overlaps modifies the canonical descent
transition of a global module sheaf.  If those units are one on diagonal
overlaps and satisfy the usual pulled-back triple-overlap cocycle, the
modified transitions again satisfy the two descent axioms.
-/


open CategoryTheory Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable (D : Scheme.GlueData.{u})

/-- Pull an `ij` overlap unit to the `ijk` triple overlap through its first
projection. -/
def coverUnitPullback₁₂
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ) (i j k : D.J) :
    Γ(Limits.pullback (D.f i j) (D.f i k), ⊤)ˣ :=
  pullbackGlobalUnit
    (pullback.fst (D.f i j) (D.f i k)) (a i j)

/-- Pull a `jk` overlap unit to the `ijk` triple overlap, using the
glue-datum comparison from that triple overlap to `V(j,k)`. -/
def coverUnitPullback₂₃
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ) (i j k : D.J) :
    Γ(Limits.pullback (D.f i j) (D.f i k), ⊤)ˣ :=
  pullbackGlobalUnit
    (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
    (a j k)

/-- Pull an `ik` overlap unit to the `ijk` triple overlap through its second
projection. -/
def coverUnitPullback₁₃
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ) (i j k : D.J) :
    Γ(Limits.pullback (D.f i j) (D.f i k), ⊤)ˣ :=
  pullbackGlobalUnit
    (pullback.snd (D.f i j) (D.f i k)) (a i k)

/-- The scalar cocycle equation on every triple overlap. -/
def CoverUnitCocycleCondition
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ) : Prop :=
  ∀ i j k,
    coverUnitPullback₁₂ D a i j k *
        coverUnitPullback₂₃ D a i j k =
      coverUnitPullback₁₃ D a i j k

/-- The canonical overlap transition followed by multiplication by the
chosen overlap unit on its target. -/
def scalarTwistedCoverTransition
    (W : D.glued.Modules)
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (i j : D.J) :
    (pullback (D.f i j)).obj (coverRestriction D W i) ≅
      (pullback (D.t i j ≫ D.f j i)).obj
        (coverRestriction D W j) :=
  coverRestrictionTransition D W i j ≪≫
    scalarIso
      ((pullback (D.t i j ≫ D.f j i)).obj
        (coverRestriction D W j))
      (a i j)

/-- A scalar-twisted transition is the identity on a diagonal overlap when
the corresponding unit is one. -/
theorem scalarTwistedCoverTransition_self
    (W : D.glued.Modules)
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (hself : ∀ i, a i i = 1) (i : D.J) :
    scalarTwistedCoverTransition D W a i i =
      eqToIso (congrArg
        (fun φ => (pullback φ).obj (coverRestriction D W i))
        (show D.f i i = D.t i i ≫ D.f i i by
          rw [D.t_id i, Category.id_comp])) := by
  rw [scalarTwistedCoverTransition, hself i, scalarIso_one,
    Iso.trans_refl, coverRestrictionTransition_self]

/-- Every global module morphism is compatible with the scalar-twisted
canonical transitions. -/
theorem scalarTwistedCoverTransition_naturality
    {W Z : D.glued.Modules} (φ : W ⟶ Z)
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (i j : D.J) :
    (pullback (D.f i j)).map
        ((pullback (D.ι i)).map φ) ≫
      (scalarTwistedCoverTransition D Z a i j).hom =
      (scalarTwistedCoverTransition D W a i j).hom ≫
      (pullback (D.t i j ≫ D.f j i)).map
        ((pullback (D.ι j)).map φ) := by
  let q :=
    (pullback (D.t i j ≫ D.f j i)).map
      ((pullback (D.ι j)).map φ)
  have hcanonical :=
    coverRestrictionTransition_naturality D φ i j
  have hscalar :=
    scalarEndomorphism_naturality q (a i j).val
  change
    (pullback (D.f i j)).map
          ((pullback (D.ι i)).map φ) ≫
        (coverRestrictionTransition D Z i j).hom ≫
        scalarEndomorphism _ (a i j).val =
      (coverRestrictionTransition D W i j).hom ≫
        scalarEndomorphism _ (a i j).val ≫ q
  rw [← Category.assoc, hcanonical, Category.assoc, ← hscalar]

/-- Scalar-twisted canonical transitions satisfy the triple-overlap
descent cocycle whenever the overlap units do. -/
theorem scalarTwistedCoverTransition_cocycle
    (W : D.glued.Modules)
    (a : ∀ i j, Γ(D.V (i, j), ⊤)ˣ)
    (hcocycle : CoverUnitCocycleCondition D a)
    (i j k : D.J) :
    pullbackBaseChangeTransport
        (pullback.fst (D.f i j) (D.f i k))
        (D.f i j) (D.t i j ≫ D.f j i)
        (scalarTwistedCoverTransition D W a i j) ≪≫
      (pullbackCongr (glueData_bridge_mid D i j k)).app
        (coverRestriction D W j) ≪≫
      pullbackBaseChangeTransport
        (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
        (D.f j k) (D.t j k ≫ D.f k j)
        (scalarTwistedCoverTransition D W a j k) ≪≫
      (pullbackCongr (glueData_bridge_tgt D i j k)).app
        (coverRestriction D W k)
    =
      (pullbackCongr (glueData_bridge_src D i j k)).app
          (coverRestriction D W i) ≪≫
        pullbackBaseChangeTransport
          (pullback.snd (D.f i j) (D.f i k))
          (D.f i k) (D.t i k ≫ D.f k i)
          (scalarTwistedCoverTransition D W a i k) := by
  have hcanonical :=
    coverRestrictionTransition_cocycle D W i j k
  have hunit :
      coverUnitPullback₁₂ D a i j k *
          coverUnitPullback₂₃ D a i j k =
        coverUnitPullback₁₃ D a i j k :=
    hcocycle i j k
  have hchain :=
    scalarIso_twisted_chain
      (pullbackBaseChangeTransport
        (pullback.fst (D.f i j) (D.f i k))
        (D.f i j) (D.t i j ≫ D.f j i)
        (coverRestrictionTransition D W i j))
      ((pullbackCongr (glueData_bridge_mid D i j k)).app
        (coverRestriction D W j))
      (pullbackBaseChangeTransport
        (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
        (D.f j k) (D.t j k ≫ D.f k j)
        (coverRestrictionTransition D W j k))
      ((pullbackCongr (glueData_bridge_tgt D i j k)).app
        (coverRestriction D W k))
      (coverUnitPullback₁₂ D a i j k)
      (coverUnitPullback₂₃ D a i j k)
  unfold scalarTwistedCoverTransition
  rw [pullbackBaseChangeTransport_trans_scalarIso,
    pullbackBaseChangeTransport_trans_scalarIso,
    pullbackBaseChangeTransport_trans_scalarIso]
  change
    (pullbackBaseChangeTransport
          (pullback.fst (D.f i j) (D.f i k))
          (D.f i j) (D.t i j ≫ D.f j i)
          (coverRestrictionTransition D W i j) ≪≫
        scalarIso _
          (coverUnitPullback₁₂ D a i j k)) ≪≫
      (pullbackCongr (glueData_bridge_mid D i j k)).app
          (coverRestriction D W j) ≪≫
      (pullbackBaseChangeTransport
          (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
          (D.f j k) (D.t j k ≫ D.f k j)
          (coverRestrictionTransition D W j k) ≪≫
        scalarIso _
          (coverUnitPullback₂₃ D a i j k)) ≪≫
      (pullbackCongr (glueData_bridge_tgt D i j k)).app
          (coverRestriction D W k) =
    (pullbackCongr (glueData_bridge_src D i j k)).app
          (coverRestriction D W i) ≪≫
      (pullbackBaseChangeTransport
          (pullback.snd (D.f i j) (D.f i k))
          (D.f i k) (D.t i k ≫ D.f k i)
          (coverRestrictionTransition D W i k) ≪≫
        scalarIso _
          (coverUnitPullback₁₃ D a i j k))
  calc
    (pullbackBaseChangeTransport
            (pullback.fst (D.f i j) (D.f i k))
            (D.f i j) (D.t i j ≫ D.f j i)
            (coverRestrictionTransition D W i j) ≪≫
          scalarIso _
            (coverUnitPullback₁₂ D a i j k)) ≪≫
        (pullbackCongr (glueData_bridge_mid D i j k)).app
            (coverRestriction D W j) ≪≫
        (pullbackBaseChangeTransport
            (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
            (D.f j k) (D.t j k ≫ D.f k j)
            (coverRestrictionTransition D W j k) ≪≫
          scalarIso _
            (coverUnitPullback₂₃ D a i j k)) ≪≫
        (pullbackCongr (glueData_bridge_tgt D i j k)).app
            (coverRestriction D W k) =
      (pullbackBaseChangeTransport
            (pullback.fst (D.f i j) (D.f i k))
            (D.f i j) (D.t i j ≫ D.f j i)
            (coverRestrictionTransition D W i j) ≪≫
        (pullbackCongr (glueData_bridge_mid D i j k)).app
            (coverRestriction D W j) ≪≫
        pullbackBaseChangeTransport
            (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
            (D.f j k) (D.t j k ≫ D.f k j)
            (coverRestrictionTransition D W j k) ≪≫
        (pullbackCongr (glueData_bridge_tgt D i j k)).app
            (coverRestriction D W k)) ≪≫
          scalarIso _
            (coverUnitPullback₁₂ D a i j k *
              coverUnitPullback₂₃ D a i j k) := by
        simpa only [Iso.trans_assoc] using hchain
    _ =
      ((pullbackCongr (glueData_bridge_src D i j k)).app
            (coverRestriction D W i) ≪≫
        pullbackBaseChangeTransport
            (pullback.snd (D.f i j) (D.f i k))
            (D.f i k) (D.t i k ≫ D.f k i)
            (coverRestrictionTransition D W i k)) ≪≫
          scalarIso _
            (coverUnitPullback₁₂ D a i j k *
              coverUnitPullback₂₃ D a i j k) := by
        exact congrArg
          (fun e =>
            e ≪≫ scalarIso _
              (coverUnitPullback₁₂ D a i j k *
                coverUnitPullback₂₃ D a i j k))
          hcanonical
    _ =
      ((pullbackCongr (glueData_bridge_src D i j k)).app
            (coverRestriction D W i) ≪≫
        pullbackBaseChangeTransport
            (pullback.snd (D.f i j) (D.f i k))
            (D.f i k) (D.t i k ≫ D.f k i)
            (coverRestrictionTransition D W i k)) ≪≫
          scalarIso _
            (coverUnitPullback₁₃ D a i j k) := by
        rw [hunit]
    _ =
      (pullbackCongr (glueData_bridge_src D i j k)).app
            (coverRestriction D W i) ≪≫
        (pullbackBaseChangeTransport
            (pullback.snd (D.f i j) (D.f i k))
            (D.f i k) (D.t i k ≫ D.f k i)
            (coverRestrictionTransition D W i k) ≪≫
          scalarIso _
            (coverUnitPullback₁₃ D a i j k)) := by
        exact Iso.trans_assoc _ _ _

end AlgebraicGeometry.Scheme.Modules

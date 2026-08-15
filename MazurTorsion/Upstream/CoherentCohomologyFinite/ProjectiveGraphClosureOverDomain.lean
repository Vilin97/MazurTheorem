/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ClosedImmersionOpenFactor
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveGraphClosure
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemeTheoreticImageOpenRestriction

/-!
# A projective graph closure over its domain of definition

The relative graph of `U ⟶ X` and `U ⟶ ℙⁿ` factors as its closed graph
over `U`, followed by the open base change induced by `U ⟶ X`.
Therefore the graph is closed after restricting the relative projective
space to this open.  Scheme-theoretic image then commutes with that open
restriction, identifying the graph closure with the original domain
there.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-- The closed graph into projective space relative to its own
domain. -/
def relativeProjectiveGraphClosedFactor
    {k : Type u} [CommRing k] {U : Scheme.{u}}
    {d : ℕ} (p : U ⟶ scheme k d) :
    U ⟶ pullback (p ≫ toSpec k d) (toSpec k d) :=
  pullback.lift (𝟙 U) p (Category.id_comp _)

instance
    {k : Type u} [CommRing k] {U : Scheme.{u}}
    {d : ℕ} (p : U ⟶ scheme k d) :
    IsClosedImmersion
      (relativeProjectiveGraphClosedFactor p) := by
  change IsClosedImmersion
    (pullback.lift (𝟙 U) p
      (Category.id_comp (p ≫ toSpec k d)) :
      U ⟶ pullback (p ≫ toSpec k d) (toSpec k d))
  infer_instance

/-- The open base-change map from projective space relative to `U` to
projective space relative to `X`. -/
def relativeProjectiveGraphOpenFactor
    {k : Type u} [CommRing k] {U X : Scheme.{u}}
    (s : X ⟶ Spec (CommRingCat.of k)) {d : ℕ}
    (u : U ⟶ X) (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d) :
    pullback (p ≫ toSpec k d) (toSpec k d) ⟶
      relativeScheme s d :=
  pullback.map
    (p ≫ toSpec k d) (toSpec k d)
    s (toSpec k d)
    u (𝟙 _) (𝟙 _)
    ((Category.comp_id _).trans h.symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)

instance isOpenImmersion_relativeProjectiveGraphOpenFactor
    {k : Type u} [CommRing k] {U X : Scheme.{u}}
    (s : X ⟶ Spec (CommRingCat.of k)) {d : ℕ}
    (u : U ⟶ X) [IsOpenImmersion u]
    (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d) :
    IsOpenImmersion
      (relativeProjectiveGraphOpenFactor s u p h) := by
  exact
    MorphismProperty.pullbackMap
      (P := @IsOpenImmersion)
      (inferInstance : IsOpenImmersion u)
      (inferInstance : IsOpenImmersion (𝟙 (scheme k d)))
      h.symm
      (Category.id_comp _).symm

/-- The relative graph is the closed graph over `U`, followed by the
open base-change map to the relative projective space over `X`. -/
theorem relativeProjectiveGraph_factor
    {k : Type u} [CommRing k] {U X : Scheme.{u}}
    (s : X ⟶ Spec (CommRingCat.of k)) {d : ℕ}
    (u : U ⟶ X) (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d) :
    relativeProjectiveGraph s d u p h =
      relativeProjectiveGraphClosedFactor p ≫
        relativeProjectiveGraphOpenFactor s u p h := by
  apply pullback.hom_ext
  · rw [Category.assoc]
    simp [relativeProjectiveGraph,
      relativeProjectiveGraphClosedFactor,
      relativeProjectiveGraphOpenFactor, pullback.map,
      pullback.lift_fst, pullback.lift_fst_assoc]
  · rw [Category.assoc]
    simp [relativeProjectiveGraph,
      relativeProjectiveGraphClosedFactor,
      relativeProjectiveGraphOpenFactor, pullback.map,
      pullback.lift_snd]

/-- On the open base-change locus, the relative graph is a closed
immersion. -/
theorem isClosedImmersion_relativeProjectiveGraph_restrict_domain
    {k : Type u} [CommRing k] {U X : Scheme.{u}}
    (s : X ⟶ Spec (CommRingCat.of k)) {d : ℕ}
    (u : U ⟶ X) [IsOpenImmersion u]
    (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d) :
    IsClosedImmersion
      (relativeProjectiveGraph s d u p h ∣_
        (relativeProjectiveGraphOpenFactor s u p h).opensRange) := by
  letI :
      IsOpenImmersion
        (relativeProjectiveGraphOpenFactor s u p h) :=
    isOpenImmersion_relativeProjectiveGraphOpenFactor s u p h
  exact
    isClosedImmersion_morphismRestrict_opensRange_of_factor
      (relativeProjectiveGraph s d u p h)
      (relativeProjectiveGraphClosedFactor p)
      (relativeProjectiveGraphOpenFactor s u p h)
      (relativeProjectiveGraph_factor s u p h)

/-- The relative graph has full preimage of the open base-change
locus. -/
theorem relativeProjectiveGraph_preimage_openFactor_opensRange
    {k : Type u} [CommRing k] {U X : Scheme.{u}}
    (s : X ⟶ Spec (CommRingCat.of k)) {d : ℕ}
    (u : U ⟶ X) [IsOpenImmersion u]
    (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d) :
    relativeProjectiveGraph s d u p h ⁻¹ᵁ
        (relativeProjectiveGraphOpenFactor s u p h).opensRange =
      ⊤ := by
  letI :
      IsOpenImmersion
        (relativeProjectiveGraphOpenFactor s u p h) :=
    isOpenImmersion_relativeProjectiveGraphOpenFactor s u p h
  rw [relativeProjectiveGraph_factor,
    Scheme.Hom.comp_preimage,
    Scheme.Hom.preimage_opensRange]
  simp

/-- Pulling the scheme-theoretic graph closure back to the open
base-change locus recovers the original graph domain. -/
def domainIsoPullbackProjectiveGraphClosure
    {k : Type u} [CommRing k] {U X : Scheme.{u}}
    (s : X ⟶ Spec (CommRingCat.of k)) {d : ℕ}
    (u : U ⟶ X) [IsOpenImmersion u] [QuasiCompact u]
    (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d) :
    U ≅
      pullback
        (relativeProjectiveGraphOpenFactor s u p h).opensRange.ι
        (projectiveGraphClosureι s d u p h) := by
  let graph :=
    relativeProjectiveGraph s d u p h
  let targetOpen :=
    (relativeProjectiveGraphOpenFactor s u p h).opensRange
  letI :
      IsOpenImmersion
        (relativeProjectiveGraphOpenFactor s u p h) :=
    isOpenImmersion_relativeProjectiveGraphOpenFactor s u p h
  letI : QuasiCompact graph :=
    quasiCompact_relativeProjectiveGraph s d u p h
  letI :
      IsClosedImmersion (graph ∣_ targetOpen) :=
    isClosedImmersion_relativeProjectiveGraph_restrict_domain
      s u p h
  exact
    U.topIso.symm ≪≫
      U.isoOfEq
        (relativeProjectiveGraph_preimage_openFactor_opensRange
          s u p h).symm ≪≫
      SchemeTheoreticImage.sourceMorphismRestrictIsoPullbackImage
        graph targetOpen

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

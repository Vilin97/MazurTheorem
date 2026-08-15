/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ImmersionClosure
import MazurTorsion.Upstream.CoherentCohomologyFinite.RelativeProjectiveSpace

/-!
# Closures of graphs in relative projective space

Given an immersion `U ⟶ S` and a compatible map from `U` to projective
space, its graph in relative projective space is again an immersion.  If
the original immersion is quasi-compact, the scheme-theoretic image of
the graph contains `U` as a dense open and is projective (hence proper)
over `S`.
-/

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

/-- The graph of two compatible morphisms into a base scheme and
projective space. -/
def relativeProjectiveGraph
    {k : Type u} [CommRing k] {U S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ)
    (u : U ⟶ S) (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d) :
    U ⟶ relativeScheme s d :=
  pullback.lift u p h

@[reassoc (attr := simp)]
lemma relativeProjectiveGraph_toBase
    {k : Type u} [CommRing k] {U S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ)
    (u : U ⟶ S) (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d) :
    relativeProjectiveGraph s d u p h ≫ relativeToBase s d = u :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma relativeProjectiveGraph_toProjective
    {k : Type u} [CommRing k] {U S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ)
    (u : U ⟶ S) (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d) :
    relativeProjectiveGraph s d u p h ≫
        relativeToProjective s d = p :=
  pullback.lift_snd _ _ _

/-- If the map to the base is an immersion, then so is its relative
projective graph. -/
theorem isImmersion_relativeProjectiveGraph
    {k : Type u} [CommRing k] {U S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ)
    (u : U ⟶ S) (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d)
    [IsImmersion u] :
    IsImmersion (relativeProjectiveGraph s d u p h) := by
  haveI :
      IsImmersion
        (relativeProjectiveGraph s d u p h ≫
          relativeToBase s d) := by
    rw [relativeProjectiveGraph_toBase]
    infer_instance
  exact
    IsImmersion.of_comp
      (relativeProjectiveGraph s d u p h)
      (relativeToBase s d)

/-- Quasi-compactness of the map to the base implies
quasi-compactness of its relative projective graph. -/
theorem quasiCompact_relativeProjectiveGraph
    {k : Type u} [CommRing k] {U S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ)
    (u : U ⟶ S) (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d)
    [QuasiCompact u] :
    QuasiCompact (relativeProjectiveGraph s d u p h) := by
  haveI :
      QuasiCompact
        (relativeProjectiveGraph s d u p h ≫
          relativeToBase s d) := by
    rw [relativeProjectiveGraph_toBase]
    infer_instance
  exact
    QuasiCompact.of_comp
      (relativeProjectiveGraph s d u p h)
      (relativeToBase s d)

/-- The scheme-theoretic closure of a relative projective graph. -/
abbrev projectiveGraphClosure
    {k : Type u} [CommRing k] {U S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ)
    (u : U ⟶ S) (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d) :
    Scheme.{u} :=
  (relativeProjectiveGraph s d u p h).image

/-- The canonical map from the graph domain into its closure. -/
noncomputable
abbrev toProjectiveGraphClosure
    {k : Type u} [CommRing k] {U S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ)
    (u : U ⟶ S) (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d) :
    U ⟶ projectiveGraphClosure s d u p h :=
  (relativeProjectiveGraph s d u p h).toImage

/-- The closed immersion of the graph closure into relative projective
space. -/
abbrev projectiveGraphClosureι
    {k : Type u} [CommRing k] {U S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ)
    (u : U ⟶ S) (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d) :
    projectiveGraphClosure s d u p h ⟶ relativeScheme s d :=
  (relativeProjectiveGraph s d u p h).imageι

/-- The first projection from the graph closure to the base scheme. -/
def projectiveGraphClosureToBase
    {k : Type u} [CommRing k] {U S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ)
    (u : U ⟶ S) (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d) :
    projectiveGraphClosure s d u p h ⟶ S :=
  projectiveGraphClosureι s d u p h ≫ relativeToBase s d

/-- The second projection from the graph closure to projective space. -/
def projectiveGraphClosureToProjective
    {k : Type u} [CommRing k] {U S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ)
    (u : U ⟶ S) (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d) :
    projectiveGraphClosure s d u p h ⟶ scheme k d :=
  projectiveGraphClosureι s d u p h ≫
    relativeToProjective s d

/-- The graph domain is open in its closure. -/
theorem isOpenImmersion_toProjectiveGraphClosure
    {k : Type u} [CommRing k] {U S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ)
    (u : U ⟶ S) (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d)
    [IsImmersion u] [QuasiCompact u] :
    IsOpenImmersion (toProjectiveGraphClosure s d u p h) := by
  letI : IsImmersion (relativeProjectiveGraph s d u p h) :=
    isImmersion_relativeProjectiveGraph s d u p h
  letI : QuasiCompact (relativeProjectiveGraph s d u p h) :=
    quasiCompact_relativeProjectiveGraph s d u p h
  infer_instance

/-- The graph domain is dense in its scheme-theoretic closure. -/
theorem denseRange_toProjectiveGraphClosure
    {k : Type u} [CommRing k] {U S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ)
    (u : U ⟶ S) (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d)
    [QuasiCompact u] :
    Dense
      (Set.range
        (toProjectiveGraphClosure s d u p h).base) := by
  letI : QuasiCompact (relativeProjectiveGraph s d u p h) :=
    quasiCompact_relativeProjectiveGraph s d u p h
  simpa [DenseRange] using
    (relativeProjectiveGraph s d u p h).toImage.denseRange

/-- The graph closure is a closed subscheme of relative projective
space. -/
theorem isClosedImmersion_projectiveGraphClosureι
    {k : Type u} [CommRing k] {U S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ)
    (u : U ⟶ S) (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d) :
    IsClosedImmersion (projectiveGraphClosureι s d u p h) :=
  inferInstance

/-- The dense-open map followed by the closed embedding recovers the
relative projective graph. -/
@[reassoc]
lemma toProjectiveGraphClosure_projectiveGraphClosureι
    {k : Type u} [CommRing k] {U S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ)
    (u : U ⟶ S) (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d) :
    toProjectiveGraphClosure s d u p h ≫
        projectiveGraphClosureι s d u p h =
      relativeProjectiveGraph s d u p h :=
  (relativeProjectiveGraph s d u p h).toImage_imageι

/-- The graph closure is projective relative to the base scheme. -/
theorem isRelativeProjectiveFactorization_projectiveGraphClosureToBase
    {k : Type u} [CommRing k] {U S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ)
    (u : U ⟶ S) (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d) :
    IsRelativeProjectiveFactorization s
      (projectiveGraphClosureToBase s d u p h) :=
  ⟨d, projectiveGraphClosureι s d u p h,
    inferInstance, rfl⟩

/-- In particular, the first projection from the graph closure is
proper. -/
theorem isProper_projectiveGraphClosureToBase
    {k : Type u} [CommRing k] {U S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ)
    (u : U ⟶ S) (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d) :
    IsProper (projectiveGraphClosureToBase s d u p h) :=
  (isRelativeProjectiveFactorization_projectiveGraphClosureToBase
    s d u p h).isProper

/-- On the dense open, the first projection is the original map to the
base scheme. -/
@[reassoc]
lemma toProjectiveGraphClosure_toBase
    {k : Type u} [CommRing k] {U S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ)
    (u : U ⟶ S) (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d) :
    toProjectiveGraphClosure s d u p h ≫
        projectiveGraphClosureToBase s d u p h = u := by
  rw [projectiveGraphClosureToBase, ← Category.assoc,
    toProjectiveGraphClosure_projectiveGraphClosureι,
    relativeProjectiveGraph_toBase]

/-- On the dense open, the second projection is the original map to
projective space. -/
@[reassoc]
lemma toProjectiveGraphClosure_toProjective
    {k : Type u} [CommRing k] {U S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ)
    (u : U ⟶ S) (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d) :
    toProjectiveGraphClosure s d u p h ≫
        projectiveGraphClosureToProjective s d u p h = p := by
  rw [projectiveGraphClosureToProjective, ← Category.assoc,
    toProjectiveGraphClosure_projectiveGraphClosureι,
    relativeProjectiveGraph_toProjective]

/-- The two projections from the graph closure remain compatible over
`Spec k`. -/
@[reassoc]
lemma projectiveGraphClosure_projection_condition
    {k : Type u} [CommRing k] {U S : Scheme.{u}}
    (s : S ⟶ Spec (CommRingCat.of k)) (d : ℕ)
    (u : U ⟶ S) (p : U ⟶ scheme k d)
    (h : u ≫ s = p ≫ toSpec k d) :
    projectiveGraphClosureToBase s d u p h ≫ s =
      projectiveGraphClosureToProjective s d u p h ≫
        toSpec k d := by
  simp only [projectiveGraphClosureToBase,
    projectiveGraphClosureToProjective, Category.assoc]
  rw [relative_projection_condition]

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

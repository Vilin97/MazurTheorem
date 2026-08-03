/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.CurveDivisorPicardDescent

/-!
# Rational normalization of descended divisor line bundles

This file isolates the rational-section compatibility needed at the exact principal boundary
of `CurveDivisorPicardDescent`. A global trivialization already makes a divisor principal on
each affine chart, but the resulting chart generators must come from one rational function.

`CompatibleChartPrincipalGenerators` records the concrete local data: a function-field unit on
every chart, the equality between its principal divisor and the restricted divisor, and equality
of the units whenever the charts overlap. Since an integral scheme is irreducible and every
coordinate chart is nonempty, every pair of charts has nonempty intersection. Thus compatible
chart generators determine one global rational function. Conversely, one global rational
function gives a constant compatible family. The two formulations are therefore proved
equivalent; this file does not assert that the compatible family exists for an arbitrary divisor
cocycle.

Together with coherent principal cocycles and reflection of the trivial descent object, this
rational compatibility constructs both fields of `GlobalPrincipalBoundary`. A final checked
consumer constructs the full divisor/Picard dictionary from the resulting boundary.
-/

namespace MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

universe u v

open CategoryTheory MonoidalCategory
open TopologicalSpace
open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.WeilDivisor

namespace DivisorCocycleSystem.ExplicitInverse

/-- Rational generators for the restrictions of one divisor, normalized to agree in the common
function field on every nonempty chart overlap. Equality in `X.functionField` is the concrete
form of equality of rational sections after restriction to a nonempty open of an integral
scheme. -/
structure CompatibleChartPrincipalGenerators
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (D : WeilDivisor (CodimensionOnePoint X)) where
  /-- The rational generator on each affine chart. -/
  generator : I → Additive X.functionFieldˣ
  /-- The generator has the prescribed divisor on its chart. -/
  restrictDivisor_eq (i : I) :
    restrictDivisor X (U i) D =
      ((h i).ambientOrderSystem X (U i) (hU i)).principalDivisor (generator i)
  /-- The rational generators agree whenever their charts have nonempty intersection. -/
  compatible (i j : I) :
    ((U i : Set X) ∩ (U j : Set X)).Nonempty → generator i = generator j

/-- On an integral scheme, any two nonempty open charts have nonempty intersection. This is the
irreducibility input that turns overlap compatibility into equality of all chart generators. -/
theorem chartIntersection_nonempty
    (X : Scheme.{u}) [IsIntegral X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (i j : I) : ((U i : Set X) ∩ (U j : Set X)).Nonempty := by
  have hi : (U i : Set X).Nonempty := by
    obtain ⟨x⟩ := hnonempty i
    exact ⟨x.1, x.2⟩
  have hj : (U j : Set X).Nonempty := by
    obtain ⟨x⟩ := hnonempty j
    exact ⟨x.1, x.2⟩
  exact nonempty_preirreducible_inter (U i).isOpen (U j).isOpen hi hj

namespace CompatibleChartPrincipalGenerators

/-- A compatible family of chart generators on an integral covered scheme is induced by one
global rational function. No connectedness hypothesis on the cover nerve is needed: every pair
of nonempty opens in an integral scheme intersects. -/
theorem exists_globalGenerator
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    {D : WeilDivisor (CodimensionOnePoint X)}
    (r : CompatibleChartPrincipalGenerators X U hnonempty hU h D) :
    ∃ g : Additive X.functionFieldˣ, ∀ i,
      restrictDivisor X (U i) D =
        ((h i).ambientOrderSystem X (U i) (hU i)).principalDivisor g := by
  obtain ⟨i₀, -⟩ := hcover.exists_mem (genericPoint X)
  refine ⟨r.generator i₀, fun i ↦ ?_⟩
  rw [r.restrictDivisor_eq i,
    r.compatible i i₀ (chartIntersection_nonempty X U hnonempty i i₀)]

end CompatibleChartPrincipalGenerators

/-- Every globally trivial descended divisor bundle has a compatible family of concrete
chartwise rational generators. Local existence follows from affine Dedekind principal detection;
agreement on overlaps is the genuine rational-normalization condition retained here. -/
def TrivialDescendedLineBundleHasCompatibleChartPrincipalGenerators
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C) : Prop :=
  ∀ D, Nonempty
      ((descendedLineBundle X U hnonempty hcover hU h C heffective D).obj ≅
        (InvertibleSheaf.trivial X).obj) →
    Nonempty (CompatibleChartPrincipalGenerators X U hnonempty hU h D)

/-- A global trivialization supplies an individual rational generator on each chart
unconditionally. The only additional content in
`TrivialDescendedLineBundleHasCompatibleChartPrincipalGenerators` is choosing these generators
compatibly on overlaps. -/
theorem exists_chartPrincipalGenerator_of_descendedLineBundle_iso_trivial
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (D : WeilDivisor (CodimensionOnePoint X))
    (htrivial : Nonempty
      ((descendedLineBundle X U hnonempty hcover hU h C heffective D).obj ≅
        (InvertibleSheaf.trivial X).obj))
    (i : I) :
    ∃ g : Additive X.functionFieldˣ,
      restrictDivisor X (U i) D =
        ((h i).ambientOrderSystem X (U i) (hU i)).principalDivisor g :=
  by
    obtain ⟨g, hg⟩ :=
      ((h i).ambientOrderSystem X (U i) (hU i)).mem_principalSubgroup.mp
        (restrictDivisor_mem_principal_of_descendedLineBundle_iso_trivial
          X U hnonempty hcover hU h C heffective D htrivial i)
    exact ⟨g, hg.symm⟩

/-- Compatible chartwise rational generators construct the single global principal witness
required by the exact divisor kernel. -/
theorem globalPrincipalWitness_of_compatibleChartPrincipalGenerators
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hcompatible : TrivialDescendedLineBundleHasCompatibleChartPrincipalGenerators
      X U hnonempty hcover hU h C heffective) :
    TrivialDescendedLineBundleHasGlobalPrincipalWitness
      X U hnonempty hcover hU h C heffective := by
  intro D htrivial
  obtain ⟨r⟩ := hcompatible D htrivial
  exact r.exists_globalGenerator X U hnonempty hcover hU h

/-- One global rational witness gives the constant compatible family of chart generators. -/
theorem compatibleChartPrincipalGenerators_of_globalPrincipalWitness
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hwitness : TrivialDescendedLineBundleHasGlobalPrincipalWitness
      X U hnonempty hcover hU h C heffective) :
    TrivialDescendedLineBundleHasCompatibleChartPrincipalGenerators
      X U hnonempty hcover hU h C heffective := by
  intro D htrivial
  obtain ⟨g, hg⟩ := hwitness D htrivial
  exact ⟨
    { generator := fun _ ↦ g
      restrictDivisor_eq := hg
      compatible := fun _ _ _ ↦ rfl }⟩

/-- The overlap-compatible chart formulation is exactly the prior global-witness formulation,
not a strengthened replacement for the unresolved geometry. -/
theorem compatibleChartPrincipalGenerators_iff_globalPrincipalWitness
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C) :
    TrivialDescendedLineBundleHasCompatibleChartPrincipalGenerators
        X U hnonempty hcover hU h C heffective ↔
      TrivialDescendedLineBundleHasGlobalPrincipalWitness
        X U hnonempty hcover hU h C heffective :=
  ⟨globalPrincipalWitness_of_compatibleChartPrincipalGenerators
      X U hnonempty hcover hU h C heffective,
    compatibleChartPrincipalGenerators_of_globalPrincipalWitness
      X U hnonempty hcover hU h C heffective⟩

/-- Compatible chart generators supply the reverse field of the global principal boundary. -/
theorem trivialLineBundleDetectsPrincipal_of_compatibleChartPrincipalGenerators
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (hord : S.ord = SchemeWeilDivisor.orderAt)
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hcompatible : TrivialDescendedLineBundleHasCompatibleChartPrincipalGenerators
      X U hnonempty hcover hU h C heffective) :
    TrivialLineBundleDetectsPrincipal X U hnonempty hcover hU h S C heffective :=
  trivialLineBundleDetectsPrincipal_of_globalPrincipalWitness
    X U hnonempty hcover hU h S hord C heffective
    (globalPrincipalWitness_of_compatibleChartPrincipalGenerators
      X U hnonempty hcover hU h C heffective hcompatible)

namespace GlobalPrincipalBoundary

/-- Coherent principal cocycles construct the forward boundary, while compatible rational
generators extracted from a trivial descended bundle construct the reverse boundary. This is the
direct constructor from the two standard geometric compatibilities. -/
theorem of_compatibleChartPrincipalGenerators
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (hord : S.ord = SchemeWeilDivisor.orderAt)
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hreflect : LineBundleDescent.ModuleDescentReflectsTrivialityFor
      (coordinateCover U hcover hU))
    (hprincipal : PrincipalCocycleSystemTrivial X U hnonempty hcover hU h S C)
    (hcompatible : TrivialDescendedLineBundleHasCompatibleChartPrincipalGenerators
      X U hnonempty hcover hU h C heffective) :
    GlobalPrincipalBoundary X U hnonempty hcover hU h S C heffective :=
  of_principalCocycleSystem X U hnonempty hcover hU h S C heffective
    hreflect hprincipal
    (trivialLineBundleDetectsPrincipal_of_compatibleChartPrincipalGenerators
      X U hnonempty hcover hU h S hord C heffective hcompatible)

end GlobalPrincipalBoundary

/-- The full divisor/Picard dictionary consumes overlap-compatible rational generators through
the global principal boundary. Surjectivity and the tensor-inverse comparison remain the honest
separate global inputs required by `DivisorPicard.Dictionary`. -/
noncomputable def dictionaryOfCompatibleChartPrincipalGenerators
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    {I : Type v} (U : I → X.Opens) (hnonempty : ∀ i, Nonempty (U i))
    (hcover : IsOpenCover U) (hU : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, AffineChart.DedekindOrderCompatibility X (U i) (hU i))
    (S : OrderSystem (CodimensionOnePoint X) (Additive X.functionFieldˣ))
    (hord : S.ord = SchemeWeilDivisor.orderAt)
    (C : DivisorCocycleSystem X U hnonempty hcover hU h)
    (heffective : EffectiveDivisorCocycleSystem X U hnonempty hcover hU h C)
    (hadd : DescendedTensorAdditive X U hnonempty hcover hU h C heffective)
    (hreflect : LineBundleDescent.ModuleDescentReflectsTrivialityFor
      (coordinateCover U hcover hU))
    (hprincipal : PrincipalCocycleSystemTrivial X U hnonempty hcover hU h S C)
    (hcompatible : TrivialDescendedLineBundleHasCompatibleChartPrincipalGenerators
      X U hnonempty hcover hU h C heffective)
    (hX : TensorInverseComparison X)
    (hsurjective : Function.Surjective
      (divisorToPicOfGlobalPrincipalBoundary
        X U hnonempty hcover hU h S C heffective hadd
          (GlobalPrincipalBoundary.of_compatibleChartPrincipalGenerators
            X U hnonempty hcover hU h S hord C heffective
              hreflect hprincipal hcompatible))) :
    DivisorPicard.Dictionary S X :=
  dictionaryOfGlobalPrincipalBoundary X U hnonempty hcover hU h S C heffective hadd
    (GlobalPrincipalBoundary.of_compatibleChartPrincipalGenerators
      X U hnonempty hcover hU h S hord C heffective hreflect hprincipal hcompatible)
    hX hsurjective

end DivisorCocycleSystem.ExplicitInverse

end MazurTorsion.AlgebraicGeometry.CurveDivisorDescent

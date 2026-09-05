/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, Codex
-/

import MazurTorsion.AlgebraicGeometry.SmoothCurveRationalSection
import MazurTorsion.Upstream.CurveCohomologyGrothendieckVanishing
import MazurTorsion.Upstream.ProjectiveLineCechHOneFinite
import MazurTorsion.Upstream.SchemeModuleCohomologyConnectingLinear
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.ProductFormula.Finite

/-!
# Degree-one coherent cohomology from a non-global rational function

On a smooth proper integral curve, Tau Ceti constructs a finite morphism to
the projective line from every rational function which is not represented by
a global section.  Combining that construction with the checked two-chart
cohomology calculation on `P¹` makes genuine sheaf `H¹` finite-dimensional.

At a supplied codimension-one point, a uniformizer of the discrete valuation
stalk gives a rational function with order `-1`.  This manufactures the
required non-global function without Riemann--Roch, so the proper-cohomology
argument does not depend circularly on the next roadmap node.
A rational section supplies such a point through its checked non-genericity,
giving the pointed-curve facade needed at modular cusps.
-/

noncomputable section

open CategoryTheory
open _root_.AlgebraicGeometry
open TauCeti.AlgebraicGeometry
open TauCeti.AlgebraicGeometry.SchemeWeilDivisor

namespace MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

universe u

local instance {X : Scheme.{u}} [IsIntegral X] : Nonempty (⊤ : X.Opens) :=
  ⟨⟨genericPoint X, trivial⟩⟩

/-- The canonical ground-field action on genuine `H⁰`, obtained by
restricting the global-functions action along the actual structure morphism.
Like the canonical action in every degree, this remains an opt-in structure. -/
@[instance_reducible]
noncomputable def hZeroCanonicalFieldModule
    (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (.of K)) (M : X.Modules) :
    Module K (H M 0) := by
  letI : Module Γ(X, ⊤) (H M 0) :=
    globalSectionsCohomologyModule M 0
  exact Module.compHom (H M 0)
    (f.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)

/-- The canonical field action on genuine `H⁰` identifies linearly with
global sections carrying the same structure-map action.  This is the
degree-zero interface for proper-curve and future Riemann--Roch consumers. -/
noncomputable def hZeroCanonicalFieldLinearEquivGlobalSections
    (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (.of K)) (M : X.Modules) :
    letI := hZeroCanonicalFieldModule K X f M
    letI : Module K Γ(M, ⊤) := Module.compHom Γ(M, ⊤)
      (f.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)
    H M 0 ≃ₗ[K] Γ(M, ⊤) := by
  letI : Module Γ(X, ⊤) (H M 0) :=
    globalSectionsCohomologyModule M 0
  letI := hZeroCanonicalFieldModule K X f M
  letI : Module K Γ(M, ⊤) := Module.compHom Γ(M, ⊤)
    (f.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)
  refine
    { hZeroCanonicalLinearEquivGlobalSections M with
      map_smul' := ?_ }
  intro r x
  exact (hZeroCanonicalLinearEquivGlobalSections M).map_smul
    (f.appTop.hom ((Scheme.ΓSpecIso (.of K)).inv.hom r)) x

/-- The canonical ground-field action on genuine `H¹`, obtained by
restricting the global-functions action along the actual structure morphism.
It uses neither an affine cover nor a finite map to projective space. -/
@[instance_reducible]
noncomputable def hOneCanonicalFieldModule
    (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (.of K)) (M : X.Modules) :
    Module K (H M 1) := by
  letI : Module Γ(X, ⊤) (H M 1) :=
    globalSectionsCohomologyModule M 1
  exact Module.compHom (H M 1)
    (f.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)

/-- A morphism of coefficient modules induces a ground-field-linear map on
genuine `H¹` for the canonical actions coming from the structure morphism.
This is the field-linear functoriality needed by subsequent curve
cohomology exact sequences. -/
noncomputable def hOneCanonicalFieldLinearMap
    (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (.of K)) {M N : X.Modules} (g : M ⟶ N) :
    letI := hOneCanonicalFieldModule K X f M
    letI := hOneCanonicalFieldModule K X f N
    H M 1 →ₗ[K] H N 1 := by
  letI : Module Γ(X, ⊤) (H M 1) :=
    globalSectionsCohomologyModule M 1
  letI : Module Γ(X, ⊤) (H N 1) :=
    globalSectionsCohomologyModule N 1
  letI := hOneCanonicalFieldModule K X f M
  letI := hOneCanonicalFieldModule K X f N
  refine
    { toFun := (zariskiFunctor X 1).map g
      map_add' := ((zariskiFunctor X 1).map g).hom.map_add
      map_smul' := ?_ }
  intro r x
  exact (cohomologyLinearMap 1 g).map_smul
    (f.appTop.hom ((Scheme.ΓSpecIso (.of K)).inv.hom r)) x

/-- The canonical field-linear `H¹` map has the same underlying function as
the genuine Ext-based cohomology functor. -/
theorem hOneCanonicalFieldLinearMap_apply
    (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (.of K)) {M N : X.Modules} (g : M ⟶ N)
    (x : H M 1) :
    letI := hOneCanonicalFieldModule K X f M
    letI := hOneCanonicalFieldModule K X f N
    hOneCanonicalFieldLinearMap K X f g x =
      (zariskiFunctor X 1).map g x := by
  rfl

/-- The degree-zero-to-degree-one connecting homomorphism of a short exact
sequence is linear over the ground field for the canonical actions induced by
the structure morphism.  This is the field-level consumer of
`cohomologyConnectingLinearMap` used by proper-curve exact sequences. -/
noncomputable def hZeroHOneCanonicalFieldConnectingLinearMap
    (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (.of K)) {S : ShortComplex X.Modules}
    (hS : S.ShortExact) :
    letI := hZeroCanonicalFieldModule K X f S.X₃
    letI := hOneCanonicalFieldModule K X f S.X₁
    H S.X₃ 0 →ₗ[K] H S.X₁ 1 := by
  letI : Module Γ(X, ⊤) (H S.X₃ 0) :=
    globalSectionsCohomologyModule S.X₃ 0
  letI : Module Γ(X, ⊤) (H S.X₁ 1) :=
    globalSectionsCohomologyModule S.X₁ 1
  letI := hZeroCanonicalFieldModule K X f S.X₃
  letI := hOneCanonicalFieldModule K X f S.X₁
  refine
    { toFun := cohomologyConnectingLinearMap hS 0 1 rfl
      map_add' := (cohomologyConnectingLinearMap hS 0 1 rfl).map_add
      map_smul' := ?_ }
  intro r x
  exact (cohomologyConnectingLinearMap hS 0 1 rfl).map_smul
    (f.appTop.hom ((Scheme.ΓSpecIso (.of K)).inv.hom r)) x

/-- The field-linear connecting map has the same underlying function as the
Ext connecting homomorphism. -/
theorem hZeroHOneCanonicalFieldConnectingLinearMap_apply
    (K : Type u) [Field K] (X : Scheme.{u})
    (f : X ⟶ Spec (.of K)) {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (x : H S.X₃ 0) :
    letI := hZeroCanonicalFieldModule K X f S.X₃
    letI := hOneCanonicalFieldModule K X f S.X₁
    hZeroHOneCanonicalFieldConnectingLinearMap K X f hS x =
      cohomologyConnectingHom hS 0 1 rfl x := by
  rfl

/-- A non-global rational function on a smooth proper integral curve gives a
finite morphism to `P¹`.  This wrapper derives the Noetherian hypothesis from
properness and smooth relative dimension one, rather than asking downstream
cohomology consumers to supply it separately. -/
theorem rationalFunctionMorphism_isFinite_of_nonGlobal
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (g : Additive X.functionFieldˣ)
    (hg : ¬ ∃ a : Γ(X, ⊤),
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
        X.germToFunctionField ⊤ a) :
    IsFinite (rationalFunctionMorphism K X f g) := by
  letI : IsNoetherian X :=
    isNoetherian_of_proper_smoothRelativeDimension_one K X f
  exact isFinite_rationalFunctionMorphism_of_nonGlobal K X f g hg

private theorem exists_nonGlobalRationalFunction_of_codimensionOnePoint
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    [IsLocallyNoetherian X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (x : CodimensionOnePoint X) :
    ∃ g : Additive X.functionFieldˣ,
      orderAt x g = -1 ∧
        ¬ ∃ a : Γ(X, ⊤),
          ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
            X.germToFunctionField ⊤ a := by
  let A := X.presheaf.stalk x.1
  let F := X.functionField
  letI : IsDiscreteValuationRing A :=
    isDiscreteValuationRing_stalk_of_smoothRelativeDimension_one K X f x
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hπmap : algebraMap A F π ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective A F).ne hπ.ne_zero
  let u : Fˣ := Units.mk0 (algebraMap A F π) hπmap
  let g : Additive Fˣ := -Additive.ofMul u
  have huOrder : orderAt x (Additive.ofMul u) = 1 := by
    rw [orderAt_eq_ord_stalk_of_eq_algebraMap x hπ.ne_zero]
    · have hOrder : Ring.ord A π = 1 := Ring.ord_of_irreducible hπ
      rw [hOrder]
      norm_num
    · rfl
  refine ⟨g, ?_, ?_⟩
  · simp only [g, map_neg, huOrder]
  rintro ⟨a, ha⟩
  let aₓ : A := X.presheaf.germ ⊤ x.1 trivial a
  have haₓ : algebraMap A F aₓ = ((u⁻¹ : Fˣ) : F) := by
    rw [show algebraMap A F aₓ = X.germToFunctionField ⊤ a by
      exact Scheme.algebraMap_germ_eq_germToFunctionField
        (X := X) (U := ⊤) (x := x.1) trivial a]
    simpa only [g, toMul_neg, toMul_ofMul] using ha.symm
  have hprodF : algebraMap A F (π * aₓ) = 1 := by
    rw [map_mul, haₓ]
    change (u : F) * ((u⁻¹ : Fˣ) : F) = 1
    exact u.val_inv
  have hprodA : π * aₓ = 1 := by
    apply IsFractionRing.injective A F
    simpa using hprodF
  exact hπ.not_isUnit (isUnit_iff_exists_inv.mpr ⟨aₓ, hprodA⟩)

/-- A chosen non-global rational function with a pole at the
supplied codimension-one point.  The choice of a uniformizer stays private;
the public API exposes only the resulting rational function and its
non-globality theorem. -/
noncomputable def nonGlobalRationalFunctionAt
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (x : CodimensionOnePoint X) : Additive X.functionFieldˣ :=
  letI : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  Classical.choose
    (exists_nonGlobalRationalFunction_of_codimensionOnePoint K X f x)

/-- The chosen rational function has a simple pole at the supplied
codimension-one point. -/
theorem nonGlobalRationalFunctionAt_orderAt
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (x : CodimensionOnePoint X) :
    letI : Smooth f := SmoothOfRelativeDimension.smooth 1 f
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    orderAt x (nonGlobalRationalFunctionAt K X f x) = -1 := by
  letI : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact (Classical.choose_spec
    (exists_nonGlobalRationalFunction_of_codimensionOnePoint K X f x)).1

/-- The chosen rational function attached to a codimension-one point is not
represented by a global section. -/
theorem nonGlobalRationalFunctionAt_not_global
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (x : CodimensionOnePoint X) :
    ¬ ∃ a : Γ(X, ⊤),
      ((Additive.toMul (nonGlobalRationalFunctionAt K X f x) :
          X.functionFieldˣ) : X.functionField) =
        X.germToFunctionField ⊤ a := by
  letI : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact (Classical.choose_spec
    (exists_nonGlobalRationalFunction_of_codimensionOnePoint K X f x)).2

/-- The rational function selected at a codimension-one point gives an actual
finite morphism from the proper curve to `P¹`. -/
theorem rationalFunctionMorphismAt_isFinite
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (x : CodimensionOnePoint X) :
    IsFinite (rationalFunctionMorphism K X f
      (nonGlobalRationalFunctionAt K X f x)) :=
  rationalFunctionMorphism_isFinite_of_nonGlobal K X f
    (nonGlobalRationalFunctionAt K X f x)
    (nonGlobalRationalFunctionAt_not_global K X f x)

/-- The ground-field action on genuine `H¹` obtained from the finite
projective-line morphism attached to a non-global rational function. -/
@[instance_reducible]
noncomputable def genuineSheafHOneFieldModuleOfNonGlobalRationalFunction
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (g : Additive X.functionFieldˣ)
    (hg : ¬ ∃ a : Γ(X, ⊤),
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
        X.germToFunctionField ⊤ a)
    (M : X.Modules) [M.IsQuasicoherent] :
    Module K (GenuineSheafHOne M) := by
  letI : IsFinite (rationalFunctionMorphism K X f g) :=
    rationalFunctionMorphism_isFinite_of_nonGlobal K X f g hg
  exact
    ProjectiveLineCohomology.genuineSheafHOneFieldModuleOfFiniteToProjectiveLine
      K (rationalFunctionMorphism K X f g) M

/-- Genuine degree-one sheaf cohomology of a coherent module on a smooth
proper integral curve is finite-dimensional once a non-global rational
function is supplied.  The rational function is used to construct the actual
finite map to `P¹`; no abstract finiteness premise is left to the caller. -/
theorem genuineSheafHOne_finiteDimensional_of_nonGlobalRationalFunction
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (g : Additive X.functionFieldˣ)
    (hg : ¬ ∃ a : Γ(X, ⊤),
      ((Additive.toMul g : X.functionFieldˣ) : X.functionField) =
        X.germToFunctionField ⊤ a)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    letI := genuineSheafHOneFieldModuleOfNonGlobalRationalFunction
      K X f g hg M
    FiniteDimensional K (GenuineSheafHOne M) := by
  letI : IsFinite (rationalFunctionMorphism K X f g) :=
    rationalFunctionMorphism_isFinite_of_nonGlobal K X f g hg
  exact
    ProjectiveLineCohomology.genuineSheafHOne_finiteDimensional_of_finite_to_projectiveLine
      K (rationalFunctionMorphism K X f g) M

/-- The ground-field action on genuine `H¹` obtained from the chosen
non-global rational function at a supplied codimension-one point. -/
@[instance_reducible]
noncomputable def genuineSheafHOneFieldModuleOfCodimensionOnePoint
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (x : CodimensionOnePoint X) (M : X.Modules) [M.IsQuasicoherent] :
    Module K (GenuineSheafHOne M) := by
  letI : IsFinite (rationalFunctionMorphism K X f
      (nonGlobalRationalFunctionAt K X f x)) :=
    rationalFunctionMorphismAt_isFinite K X f x
  exact
    ProjectiveLineCohomology.genuineSheafHOneFieldModuleOfFiniteToProjectiveLine
      K (rationalFunctionMorphism K X f
        (nonGlobalRationalFunctionAt K X f x)) M

/-- Genuine `H¹` of a coherent module on a smooth proper integral curve is
finite-dimensional as soon as a codimension-one point is supplied.  The
point produces a non-global rational function and hence an actual finite map
to `P¹`; callers do not provide either the function or a finiteness premise. -/
theorem genuineSheafHOne_finiteDimensional_of_codimensionOnePoint
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (x : CodimensionOnePoint X) (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] :
    letI := genuineSheafHOneFieldModuleOfCodimensionOnePoint K X f x M
    FiniteDimensional K (GenuineSheafHOne M) := by
  letI : IsFinite (rationalFunctionMorphism K X f
      (nonGlobalRationalFunctionAt K X f x)) :=
    rationalFunctionMorphismAt_isFinite K X f x
  exact
    ProjectiveLineCohomology.genuineSheafHOne_finiteDimensional_of_finite_to_projectiveLine
      K (rationalFunctionMorphism K X f
        (nonGlobalRationalFunctionAt K X f x)) M

/-- The image of a rational section is a codimension-one point of a smooth
relative curve.  Non-genericity is the checked section/closed-immersion
theorem; smooth relative dimension one then computes its coheight. -/
noncomputable def codimensionOnePointOfRationalSection
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
    (s : SmoothCurveRationalSection K X f) : CodimensionOnePoint X :=
  ⟨s.hom (IsLocalRing.closedPoint K),
    coheight_eq_one_of_ne_genericPoint_of_smoothRelativeDimension_one
      K X f _ s.ne_generic⟩

/-- The field action on genuine `H¹` selected by a rational section of a
smooth proper integral curve. -/
@[instance_reducible]
noncomputable def genuineSheafHOneFieldModuleOfRationalSection
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (s : SmoothCurveRationalSection K X f)
    (M : X.Modules) [M.IsQuasicoherent] :
    Module K (GenuineSheafHOne M) :=
  genuineSheafHOneFieldModuleOfCodimensionOnePoint K X f
    (codimensionOnePointOfRationalSection K X f s) M

/-- A rational section supplies the codimension-one point needed to prove
finite-dimensionality of genuine coherent `H¹`.  This is the cusp-shaped
consumer used by pointed modular curves. -/
theorem genuineSheafHOne_finiteDimensional_of_rationalSection
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (s : SmoothCurveRationalSection K X f)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    letI := genuineSheafHOneFieldModuleOfRationalSection K X f s M
    FiniteDimensional K (GenuineSheafHOne M) := by
  exact genuineSheafHOne_finiteDimensional_of_codimensionOnePoint K X f
    (codimensionOnePointOfRationalSection K X f s) M

/-- A rational section makes genuine `H¹` finite over the global functions
of the base for the canonical action induced by the structure morphism.
This is the base-linear input used by ordered Cech consumers. -/
theorem genuineSheafHOneCanonicalBase_finite_of_rationalSection
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (s : SmoothCurveRationalSection K X f)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    letI := baseSectionsHOneModule f M
    Module.Finite Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens))
      (H M 1) := by
  let x := codimensionOnePointOfRationalSection K X f s
  let g := nonGlobalRationalFunctionAt K X f x
  let φ := rationalFunctionMorphism K X f g
  letI : IsFinite φ := rationalFunctionMorphismAt_isFinite K X f x
  rw [← rationalFunctionMorphism_comp_structureMap K X f g]
  exact
    ProjectiveLineCohomology.genuineSheafHOne_finite_canonical_of_finite_to_projectiveLine
      K φ M

/-- A rational section makes genuine `H¹` finite-dimensional for the
canonical field action induced by the structure morphism. -/
theorem genuineSheafHOneCanonical_finiteDimensional_of_rationalSection
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (s : SmoothCurveRationalSection K X f)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    letI := hOneCanonicalFieldModule K X f M
    FiniteDimensional K (H M 1) := by
  let R := Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens))
  letI : Algebra K R := (Scheme.ΓSpecIso (.of K)).inv.hom.toAlgebra
  letI : Module R (H M 1) := baseSectionsHOneModule f M
  letI : Module.Finite R (H M 1) :=
    genuineSheafHOneCanonicalBase_finite_of_rationalSection K X f s M
  letI := hOneCanonicalFieldModule K X f M
  letI : IsScalarTower K R (H M 1) :=
    IsScalarTower.of_compHom K R (H M 1)
  have hR : RingHom.Finite (algebraMap K R) := by
    change RingHom.Finite (Scheme.ΓSpecIso (.of K)).inv.hom
    exact (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv.finite
  letI : Module.Finite K R := RingHom.finite_algebraMap.mp hR
  exact Module.Finite.trans R (H M 1)

/-- For a pointed smooth proper integral curve, the image of every canonical
degree-zero-to-degree-one connecting map is finite-dimensional.  This named
proper-curve consumer combines linearity of the actual connecting map with
the checked finite-dimensionality of its coherent `H¹` target. -/
theorem hZeroHOneCanonicalFieldConnecting_range_finiteDimensional_of_rationalSection
    (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [IsProper f] [SmoothOfRelativeDimension 1 f]
    (s : SmoothCurveRationalSection K X f)
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₁.IsFiniteType] :
    letI := hZeroCanonicalFieldModule K X f S.X₃
    letI := hOneCanonicalFieldModule K X f S.X₁
    FiniteDimensional K
      (LinearMap.range
        (hZeroHOneCanonicalFieldConnectingLinearMap K X f hS)) := by
  letI := hZeroCanonicalFieldModule K X f S.X₃
  letI := hOneCanonicalFieldModule K X f S.X₁
  letI : FiniteDimensional K (H S.X₁ 1) :=
    genuineSheafHOneCanonical_finiteDimensional_of_rationalSection
      K X f s S.X₁
  infer_instance

end MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

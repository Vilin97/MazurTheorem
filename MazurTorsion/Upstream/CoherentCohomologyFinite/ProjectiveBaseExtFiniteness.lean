/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.BaseRingModuleSheafFunctor
import MazurTorsion.Upstream.CoherentCohomologyFinite.CoherentKernel
import MazurTorsion.Upstream.CoherentCohomologyFinite.ExtLinearFiniteBiproduct
import MazurTorsion.Upstream.CoherentCohomologyFinite.FlatBaseAcyclicCoverCechLinearComparison
import MazurTorsion.Upstream.CoherentCohomologyFinite.NoetherianLinearExtDevissage
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveBaseTwistGeneration
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveStandardCoverModuleExt

/-!
# Coherent Ext-finiteness on projective space over a base ring

Over a Noetherian coefficient ring flat over `ℤ`, the standard-cover
calculation gives finite constant-source Ext for every integer Serre
twist and a uniform cohomological bound.  Corrected chart generators
present every coherent module by a finite sum of those twists.

The exact base-linear module-sheaf functor transports these presentations
to the category where Ext is coefficient-linear.  Noetherian descending
dévissage then proves finite generation for every coherent module.
-/


open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

open MazurTorsion.AlgebraicGeometry.CoherentCohomology.BaseRing
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FiniteSubsetFreeSheaf
open MazurTorsion.AlgebraicGeometry.CoherentCohomology.FlatBaseAcyclicCoverCechComparison
open SerreTwist

variable {R : Type} [CommRing R] [Module.Flat ℤ R]
  [IsNoetherianRing R]
variable {d : ℕ}

local instance projectiveSpaceOverBaseForCoherentExt :
    (scheme R d).Over (Spec (CommRingCat.of R)) :=
  ⟨toSpec R d⟩

/-- A base-linear sheaf which comes from a coherent scheme module. -/
def IsBaseCoherentModuleSheaf
    (F :
      Sheaf (Opens.grothendieckTopology (scheme R d))
        (ModuleCat R)) : Prop :=
  ∃ M : (scheme R d).Modules,
    CoherentModule M ∧
      Nonempty (F ≅ moduleSheaf (k := R) M)

/-- A base-linear sheaf which comes from a finite sum of integer Serre
twists. -/
def IsBaseFiniteIntegerTwistSumSheaf
    (F :
      Sheaf (Opens.grothendieckTopology (scheme R d))
        (ModuleCat R)) : Prop :=
  ∃ E : (scheme R d).Modules,
    IsBaseFiniteIntegerTwistSum R d E ∧
      Nonempty (F ≅ moduleSheaf (k := R) E)

/-- Constant-source Ext of the base-linear sheaf attached to a finite
sum of twists is finite. -/
theorem moduleSheafExt_finite_of_isBaseFiniteIntegerTwistSum
    (hcoord :
      ∀ m : ℤ, BaseStandardCoverCoordinatesNatural R d m)
    (E : (scheme R d).Modules)
    (hE : IsBaseFiniteIntegerTwistSum R d E)
    (n : ℕ) :
    Module.Finite R
      (Abelian.Ext
        (constantRankOneSheaf (R := R) (scheme R d))
        (moduleSheaf (k := R) E) n) := by
  obtain ⟨ι, hι, degree, ⟨e⟩⟩ := hE
  letI : Fintype ι := hι
  let F :=
    moduleSheafFunctor (k := R) (X := scheme R d)
  have htwist :
      ∀ i : ι,
        Module.Finite R
          (Abelian.Ext
            (constantRankOneSheaf (R := R) (scheme R d))
            (F.obj (OInt R d (degree i))) n) := by
    intro i
    exact
      integerTwistConstantBaseExt_finite
        R d (degree i) (hcoord (degree i)) n
  have hsum :
      Module.Finite R
        (Abelian.Ext
          (constantRankOneSheaf (R := R) (scheme R d))
          (F.obj (finiteIntegerSum R d degree)) n) := by
    change
      Module.Finite R
        (Abelian.Ext
          (constantRankOneSheaf (R := R) (scheme R d))
          (F.obj (∐ fun i => OInt R d (degree i))) n)
    exact
      extFinite_obj_finiteCoproduct
        (R := R) F
        (constantRankOneSheaf (R := R) (scheme R d))
        (fun i => OInt R d (degree i)) n htwist
  letI :
      Module.Finite R
        (Abelian.Ext
          (constantRankOneSheaf (R := R) (scheme R d))
          (F.obj (finiteIntegerSum R d degree)) n) :=
    hsum
  exact
    extFinite_congr_right (F.mapIso e) n

/-- Every coherent base-linear module sheaf on projective space has
finite constant-source Ext, assuming the two isolated coordinate
compatibilities used by the twist calculation and twisted-free
generation. -/
theorem coherentModuleSheafExt_finite_of_coordinate_seams
    (d : ℕ)
    (hchart :
      ∀ m : ℤ, BaseStandardCoverCoordinatesNatural R d m)
    (hcoordinate :
      ∀ N : ℕ,
        IntegerOverChartCoordinateTransition R d N)
    (M : (scheme R d).Modules)
    [M.IsFiniteType] [M.IsQuasicoherent]
    (n : ℕ) :
    letI :
        (scheme R d).Over (Spec (CommRingCat.of R)) :=
      ⟨toSpec R d⟩
    Module.Finite R
      (Abelian.Ext
        (constantRankOneSheaf (R := R) (scheme R d))
        (moduleSheaf (k := R) M) n) := by
  letI :
      (scheme R d).Over (Spec (CommRingCat.of R)) :=
    ⟨toSpec R d⟩
  letI : IsLocallyNoetherian (scheme R d) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (toSpec R d)
  let X₀ :=
    constantRankOneSheaf (R := R) (scheme R d)
  let P :=
    IsBaseCoherentModuleSheaf
      (R := R) (d := d)
  let Good :=
    IsBaseFiniteIntegerTwistSumSheaf
      (R := R) (d := d)
  apply
    noetherianLinearExtFinite_of_bounded_quotient_presentations
      X₀ P Good d
  · intro Y hY q hq
    obtain ⟨Y₀, hY₀, ⟨eY⟩⟩ := hY
    letI : Y₀.IsQuasicoherent := hY₀.2
    let e :
        Abelian.Ext X₀ Y q ≃ₗ[R]
          Abelian.Ext X₀
            (moduleSheaf (k := R) Y₀) q :=
      ExtAdjunction.postcompIsoLinearEquiv
        (R := R) (X := X₀) eY q
    letI :
        Subsingleton
          (Abelian.Ext X₀
            (moduleSheaf (k := R) Y₀) q) :=
      constantBaseExt_subsingleton_of_dimension_lt
        Y₀ q hq
    exact
      ⟨fun x y =>
        e.injective
          (Subsingleton.elim (e x) (e y))⟩
  · intro Y hY
    obtain ⟨Y₀, hY₀, ⟨eY⟩⟩ := hY
    letI : Y₀.IsFiniteType := hY₀.1
    letI : Y₀.IsQuasicoherent := hY₀.2
    obtain ⟨E, e, hepi, hEcoherent, hEtwist⟩ :=
      exists_baseFiniteIntegerTwistSum_epi
        R d hcoordinate Y₀
    letI : E.IsFiniteType := hEcoherent.1
    letI : E.IsQuasicoherent := hEcoherent.2
    letI : Epi e := hepi
    let g :
        moduleSheaf (k := R) E ⟶ Y :=
      moduleSheafMap (k := R) e ≫ eY.inv
    haveI : Epi (moduleSheafMap (k := R) e) :=
      moduleSheafMap_epi e
    haveI : Epi g := by
      dsimp only [g]
      infer_instance
    have hkernel :
        CoherentModule (kernel e) :=
      Scheme.Modules.kernel_isFiniteType_and_isQuasicoherent e
    let kernelIso :
        kernel g ≅ moduleSheaf (k := R) (kernel e) :=
      kernel.mapIso
          (f := g)
          (moduleSheafMap (k := R) e)
          (Iso.refl _) eY
          (by simp [g]) ≪≫
        (moduleSheafKernelIso (k := R) e).symm
    exact
      ⟨moduleSheaf (k := R) E, g, inferInstance,
        ⟨E, hEtwist, ⟨Iso.refl _⟩⟩,
        ⟨kernel e, hkernel, ⟨kernelIso⟩⟩⟩
  · intro E hE q
    obtain ⟨E₀, hE₀, ⟨eE⟩⟩ := hE
    letI :
        Module.Finite R
          (Abelian.Ext X₀
            (moduleSheaf (k := R) E₀) q) :=
      moduleSheafExt_finite_of_isBaseFiniteIntegerTwistSum
        hchart E₀ hE₀ q
    exact extFinite_congr_right eE q
  · exact
      ⟨M, ⟨inferInstance, inferInstance⟩,
        ⟨Iso.refl _⟩⟩

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveSpace

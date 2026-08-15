/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ProjectiveLaurentCechComplex

/-!
# Categorical homology of the Laurent Čech complex

This file compares Mathlib's categorical homology object for the Laurent
Čech cochain complex with the explicit kernel modulo image used in the
finiteness calculation.  The comparison is valid over an arbitrary
commutative coefficient ring.
-/

open CategoryTheory


namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

universe v

variable {ι R : Type*} [Fintype ι] [LinearOrder ι]

attribute [local instance 2000] laurentCechCyclesAddCommGroup

/-- The explicit positive Laurent cohomology quotient carries the
additive group inherited from the explicitly chosen cycle group. -/
noncomputable local instance laurentCechPositiveAddCommGroup
    [CommRing R] (d : ℤ) (q : ℕ) :
    AddCommGroup
      ((differential
          (ι := ι) (R := R) d (q + 1)).ker ⧸
        laurentCechBoundaries (ι := ι) R d q) := by
  letI :
      AddCommGroup
        (differential
          (ι := ι) (R := R) d (q + 1)).ker :=
    laurentCechCyclesAddCommGroup
      (ι := ι) (R := R) d (q + 1)
  infer_instance

/-- The explicit positive Laurent cohomology quotient carries its
quotient-module structure over the coefficient ring. -/
noncomputable local instance laurentCechPositiveModule
    [CommRing R] (d : ℤ) (q : ℕ) :
    Module R
      ((differential
          (ι := ι) (R := R) d (q + 1)).ker ⧸
        laurentCechBoundaries (ι := ι) R d q) := by
  letI :
      AddCommGroup
        (differential
          (ι := ι) (R := R) d (q + 1)).ker :=
    laurentCechCyclesAddCommGroup
      (ι := ι) (R := R) d (q + 1)
  infer_instance

/-- Transport a supplied finiteness witness across a linear
equivalence, without relying on instance search for the source
finiteness proof. -/
theorem moduleFiniteOfLinearEquiv
    {S M N : Type*} [Semiring S]
    [AddCommMonoid M] [Module S M]
    [AddCommMonoid N] [Module S N]
    (hM : Module.Finite S M) (e : M ≃ₗ[S] N) :
    Module.Finite S N := by
  letI : Module.Finite S M := hM
  exact Module.Finite.equiv e

/-- The range of a map corestricted to cycles is its original range,
viewed inside the cycle submodule. -/
lemma range_codRestrict_eq_comap_range
    [CommRing R]
    {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (h : g.comp f = 0) :
    LinearMap.range
        (f.codRestrict g.ker
          (fun x => by
            have hx := DFunLike.congr_fun h x
            simpa [LinearMap.comp_apply] using hx)) =
      Submodule.comap g.ker.subtype f.range := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext
    exact hy

/--
Transport an explicit kernel-modulo-image quotient across equal
differentials.  Keeping this dependent transport separate prevents
kernel subtype equalities from leaking into concrete complex proofs.
-/
noncomputable def homologyQuotientLinearEquivOfEq
    [CommRing R]
    {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (toCycles : A →ₗ[R] g.ker)
    (toCycles_val : ∀ x, (toCycles x : B) = f x)
    (f' : A →ₗ[R] B) (g' : B →ₗ[R] C)
    (hf : f = f') (hg : g = g') :
    (g.ker ⧸ LinearMap.range toCycles) ≃ₗ[R]
      (g'.ker ⧸ Submodule.comap g'.ker.subtype f'.range) := by
  subst f'
  subst g'
  apply Submodule.quotEquivOfEq
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, (toCycles_val y).symm⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext
    exact (toCycles_val y).trans hy

/-- Identify Mathlib's explicit homology data for a short complex with a
kernel-modulo-image quotient presented by equal linear maps. -/
noncomputable def shortComplexHomologyLinearEquivOfEq
    [CommRing R]
    (S : ShortComplex (ModuleCat.{v} R))
    (f' : S.X₁ →ₗ[R] S.X₂) (g' : S.X₂ →ₗ[R] S.X₃)
    (hf : S.f.hom = f') (hg : S.g.hom = g') :
    S.moduleCatLeftHomologyData.H ≃ₗ[R]
      (g'.ker ⧸ Submodule.comap g'.ker.subtype f'.range) := by
  change
    (S.g.hom.ker ⧸ LinearMap.range S.moduleCatToCycles) ≃ₗ[R]
      (g'.ker ⧸ Submodule.comap g'.ker.subtype f'.range)
  exact homologyQuotientLinearEquivOfEq
    S.f.hom S.g.hom S.moduleCatToCycles (fun _ => rfl)
    f' g' hf hg

/--
Transport an explicit homology quotient to a specified boundary
submodule.  The extra submodule parameter is useful when the target
boundary has a stable mathematical name: it prevents later proofs from
having to normalize a large defining expression merely to recognize the
quotient.
-/
noncomputable def homologyQuotientLinearEquivOfEqSubmodule
    [CommRing R]
    {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (toCycles : A →ₗ[R] g.ker)
    (toCycles_val : ∀ x, (toCycles x : B) = f x)
    (f' : A →ₗ[R] B) (g' : B →ₗ[R] C)
    (hf : f = f') (hg : g = g')
    (P : Submodule R g'.ker)
    (hP :
      P = Submodule.comap g'.ker.subtype f'.range) :
    (g.ker ⧸ LinearMap.range toCycles) ≃ₗ[R]
      (g'.ker ⧸ P) :=
  LinearEquiv.trans
    (homologyQuotientLinearEquivOfEq
      f g toCycles toCycles_val f' g' hf hg)
    (Submodule.quotEquivOfEq
      (Submodule.comap g'.ker.subtype f'.range) P hP.symm)

/--
The short-complex homology comparison with a named target boundary
submodule.
-/
noncomputable def shortComplexHomologyLinearEquivOfEqSubmodule
    [CommRing R]
    (S : ShortComplex (ModuleCat.{v} R))
    (f' : S.X₁ →ₗ[R] S.X₂) (g' : S.X₂ →ₗ[R] S.X₃)
    (hf : S.f.hom = f') (hg : S.g.hom = g')
    (P : Submodule R g'.ker)
    (hP :
      P = Submodule.comap g'.ker.subtype f'.range) :
    S.moduleCatLeftHomologyData.H ≃ₗ[R]
      (g'.ker ⧸ P) := by
  change
    (S.g.hom.ker ⧸ LinearMap.range S.moduleCatToCycles) ≃ₗ[R]
      (g'.ker ⧸ P)
  exact homologyQuotientLinearEquivOfEqSubmodule
    S.f.hom S.g.hom S.moduleCatToCycles (fun _ => rfl)
    f' g' hf hg P hP

/--
Finiteness of a named kernel-modulo-boundary quotient implies
finiteness of the corresponding short-complex homology object.
-/
theorem shortComplexHomologyFiniteOfEqSubmodule
    [CommRing R]
    (S : ShortComplex (ModuleCat.{v} R))
    (f' : S.X₁ →ₗ[R] S.X₂) (g' : S.X₂ →ₗ[R] S.X₃)
    (hf : S.f.hom = f') (hg : S.g.hom = g')
    (P : Submodule R g'.ker)
    (hP :
      P = Submodule.comap g'.ker.subtype f'.range)
    (hfinite : Module.Finite R (g'.ker ⧸ P)) :
    Module.Finite R S.moduleCatLeftHomologyData.H := by
  letI : Module.Finite R (g'.ker ⧸ P) := hfinite
  exact Module.Finite.equiv
    (shortComplexHomologyLinearEquivOfEqSubmodule
      S f' g' hf hg P hP).symm

/-- The three-term short complex centered in Laurent Čech degree `q + 1`. -/
noncomputable def laurentCechShortComplex
    [CommRing R] (d : ℤ) (q : ℕ) :
    ShortComplex (ModuleCat R) :=
  (laurentCechComplex (ι := ι) (R := R) d).sc'
    q (q + 1) ((q + 1) + 1)

@[simp]
lemma laurentCechShortComplex_f
    [CommRing R] (d : ℤ) (q : ℕ) :
    (laurentCechShortComplex (ι := ι) (R := R) d q).f.hom =
      differential (ι := ι) (R := R) d q := by
  dsimp only [laurentCechShortComplex, HomologicalComplex.sc',
    HomologicalComplex.shortComplexFunctor'_obj_f]
  exact congrArg ModuleCat.Hom.hom
    (laurentCechComplex_d (ι := ι) (R := R) d q)

@[simp]
lemma laurentCechShortComplex_g
    [CommRing R] (d : ℤ) (q : ℕ) :
    (laurentCechShortComplex (ι := ι) (R := R) d q).g.hom =
      differential (ι := ι) (R := R) d (q + 1) := by
  dsimp only [laurentCechShortComplex, HomologicalComplex.sc',
    HomologicalComplex.shortComplexFunctor'_obj_g]
  exact congrArg ModuleCat.Hom.hom
    (laurentCechComplex_d (ι := ι) (R := R) d (q + 1))

/-- Categorical homology is isomorphic to the explicit homology object
of the centered Laurent Čech short complex. -/
noncomputable def laurentCechHomologyShortComplexIso
    [CommRing R] (d : ℤ) (q : ℕ) :
    (laurentCechComplex (ι := ι) (R := R) d).homology (q + 1) ≅
      (laurentCechShortComplex (ι := ι) (R := R) d q).moduleCatLeftHomologyData.H :=
  (laurentCechComplex (ι := ι) (R := R) d).homologyIsoSc'
      q (q + 1) ((q + 1) + 1) (by simp) (by simp) ≪≫
    (laurentCechShortComplex (ι := ι) (R := R) d q).moduleCatHomologyIso

noncomputable def laurentCechHomologyShortComplexLinearEquiv
    [CommRing R] (d : ℤ) (q : ℕ) :
    (laurentCechComplex (ι := ι) (R := R) d).homology (q + 1) ≃ₗ[R]
      (laurentCechShortComplex (ι := ι) (R := R) d q).moduleCatLeftHomologyData.H :=
  (laurentCechHomologyShortComplexIso
    (ι := ι) (R := R) d q).toLinearEquiv

/-- The short-complex homology object is the explicit positive-degree
Laurent Čech kernel modulo image. -/
noncomputable def laurentCechShortComplexPositiveLinearEquiv
    [CommRing R] (d : ℤ) (q : ℕ) :=
  shortComplexHomologyLinearEquivOfEq
    (laurentCechShortComplex (ι := ι) (R := R) d q)
    (differential (ι := ι) (R := R) d q)
    (differential (ι := ι) (R := R) d (q + 1))
    (laurentCechShortComplex_f (ι := ι) (R := R) d q)
    (laurentCechShortComplex_g (ι := ι) (R := R) d q)

/-- The defining Laurent boundary submodule is the image-comap boundary
appearing in the short-complex homology presentation. -/
theorem laurentCechBoundaries_eq_comap
    [CommRing R] (d : ℤ) (q : ℕ) :
    laurentCechBoundaries (ι := ι) R d q =
      Submodule.comap
        (differential
          (ι := ι) (R := R) d (q + 1)).ker.subtype
        (differential (ι := ι) (R := R) d q).range :=
  rfl

/--
The short-complex homology object compared directly with the quotient by
the named Laurent boundary submodule.
-/
noncomputable def laurentCechShortComplexPositiveNamedLinearEquiv
    [CommRing R] (d : ℤ) (q : ℕ) := by
  letI :
      AddCommGroup
        (differential
          (ι := ι) (R := R) d (q + 1)).ker :=
    laurentCechCyclesAddCommGroup
      (ι := ι) (R := R) d (q + 1)
  exact shortComplexHomologyLinearEquivOfEqSubmodule
    (laurentCechShortComplex (ι := ι) (R := R) d q)
    (differential (ι := ι) (R := R) d q)
    (differential (ι := ι) (R := R) d (q + 1))
    (laurentCechShortComplex_f (ι := ι) (R := R) d q)
    (laurentCechShortComplex_g (ι := ι) (R := R) d q)
    (laurentCechBoundaries (ι := ι) R d q)
    (laurentCechBoundaries_eq_comap
      (ι := ι) (R := R) d q)

/--
Positive categorical Laurent Čech homology compared directly with the
quotient by the named Laurent boundary submodule.
-/
noncomputable def laurentCechPositiveNamedHomologyLinearEquiv
    [CommRing R] (d : ℤ) (q : ℕ) :
    (laurentCechComplex (ι := ι) (R := R) d).homology (q + 1) ≃ₗ[R]
      ((differential (ι := ι) (R := R) d (q + 1)).ker ⧸
        laurentCechBoundaries (ι := ι) R d q) := by
  letI :
      AddCommGroup
        (differential
          (ι := ι) (R := R) d (q + 1)).ker :=
    laurentCechCyclesAddCommGroup
      (ι := ι) (R := R) d (q + 1)
  letI :
      AddCommGroup
        ((differential
          (ι := ι) (R := R) d (q + 1)).ker ⧸
            laurentCechBoundaries (ι := ι) R d q) :=
    inferInstance
  letI :
      Module R
        ((differential
          (ι := ι) (R := R) d (q + 1)).ker ⧸
            laurentCechBoundaries (ι := ι) R d q) :=
    inferInstance
  exact LinearEquiv.trans
    (σ₁₂ := RingHom.id R) (σ₂₁ := RingHom.id R)
    (σ₂₃ := RingHom.id R) (σ₃₂ := RingHom.id R)
    (σ₁₃ := RingHom.id R) (σ₃₁ := RingHom.id R)
    (re₁₂ := RingHomInvPair.ids) (re₂₁ := RingHomInvPair.ids)
    (re₂₃ := RingHomInvPair.ids) (re₃₂ := RingHomInvPair.ids)
    (laurentCechHomologyShortComplexLinearEquiv
      (ι := ι) (R := R) d q)
    (laurentCechShortComplexPositiveNamedLinearEquiv
      (ι := ι) (R := R) d q)

/--
The same comparison with a lifted source.  Besides making universe
transport explicit, the lift gives the source module a single canonical
set of inherited additive and scalar instances.
-/
noncomputable def laurentCechPositiveNamedHomologyULiftLinearEquiv
    [CommRing R] (d : ℤ) (q : ℕ) :
    ULift
        ((differential (ι := ι) (R := R) d (q + 1)).ker ⧸
          laurentCechBoundaries (ι := ι) R d q) ≃ₗ[R]
      (laurentCechComplex (ι := ι) (R := R) d).homology (q + 1) := by
  letI :
      AddCommGroup
        (differential
          (ι := ι) (R := R) d (q + 1)).ker :=
    laurentCechCyclesAddCommGroup
      (ι := ι) (R := R) d (q + 1)
  letI :
      AddCommGroup
        ((differential
          (ι := ι) (R := R) d (q + 1)).ker ⧸
            laurentCechBoundaries (ι := ι) R d q) :=
    inferInstance
  letI :
      Module R
        ((differential
          (ι := ι) (R := R) d (q + 1)).ker ⧸
            laurentCechBoundaries (ι := ι) R d q) :=
    inferInstance
  exact LinearEquiv.trans
    (σ₁₂ := RingHom.id R) (σ₂₁ := RingHom.id R)
    (σ₂₃ := RingHom.id R) (σ₃₂ := RingHom.id R)
    (σ₁₃ := RingHom.id R) (σ₃₁ := RingHom.id R)
    (re₁₂ := RingHomInvPair.ids) (re₂₁ := RingHomInvPair.ids)
    (re₂₃ := RingHomInvPair.ids) (re₃₂ := RingHomInvPair.ids)
    ULift.moduleEquiv.{_, _, 0}
    (laurentCechPositiveNamedHomologyLinearEquiv
      (ι := ι) (R := R) d q).symm

/--
Categorical Laurent Čech homology in degree `q + 1` is linearly
equivalent to `LaurentCechPositiveCohomology R d q`.

The inferred target is displayed as the defining kernel quotient; it is
definitionally the named positive cohomology type.
-/
noncomputable def laurentCechPositiveHomologyLinearEquiv
    [CommRing R] (d : ℤ) (q : ℕ) :=
  LinearEquiv.trans
    (σ₁₂ := RingHom.id R) (σ₂₁ := RingHom.id R)
    (σ₂₃ := RingHom.id R) (σ₃₂ := RingHom.id R)
    (σ₁₃ := RingHom.id R) (σ₃₁ := RingHom.id R)
    (re₁₂ := RingHomInvPair.ids) (re₂₁ := RingHomInvPair.ids)
    (re₂₃ := RingHomInvPair.ids) (re₃₂ := RingHomInvPair.ids)
    (laurentCechHomologyShortComplexLinearEquiv
      (ι := ι) (R := R) d q)
    (laurentCechShortComplexPositiveLinearEquiv
      (ι := ι) (R := R) d q)

/-- Equal linear maps have linearly equivalent kernels. -/
noncomputable def kernelLinearEquivOfEq
    [CommRing R]
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module R A] [Module R B]
    (f g : A →ₗ[R] B) (h : f = g) :
    f.ker ≃ₗ[R] g.ker := by
  subst g
  exact LinearEquiv.refl R f.ker

/--
Categorical Laurent Čech homology in degree zero is linearly equivalent
to `LaurentCechCycles R d 0`.
-/
noncomputable def laurentCechDegreeZeroHomologyLinearEquiv
    [CommRing R] (d : ℤ) := by
  let K := laurentCechComplex (ι := ι) (R := R) d
  let S := K.sc' 0 0 1
  let e :
      K.homology 0 ≃ₗ[R] S.moduleCatLeftHomologyData.K :=
    (K.isoHomologyπ₀.symm ≪≫
      K.cyclesIsoSc' 0 0 1 (by simp) (by simp) ≪≫
      S.moduleCatCyclesIso).toLinearEquiv
  have hg :
      S.g.hom = differential (ι := ι) (R := R) d 0 := by
    dsimp only [S, K, HomologicalComplex.sc',
      HomologicalComplex.shortComplexFunctor'_obj_g]
    exact congrArg ModuleCat.Hom.hom
      (laurentCechComplex_d (ι := ι) (R := R) d 0)
  exact LinearEquiv.trans
    (σ₁₂ := RingHom.id R) (σ₂₁ := RingHom.id R)
    (σ₂₃ := RingHom.id R) (σ₃₂ := RingHom.id R)
    (σ₁₃ := RingHom.id R) (σ₃₁ := RingHom.id R)
    (re₁₂ := RingHomInvPair.ids) (re₂₁ := RingHomInvPair.ids)
    (re₂₃ := RingHomInvPair.ids) (re₃₂ := RingHomInvPair.ids)
    e (kernelLinearEquivOfEq S.g.hom
      (differential (ι := ι) (R := R) d 0) hg)

end MazurTorsion.AlgebraicGeometry.CoherentCohomology.ProjectiveLaurentCech

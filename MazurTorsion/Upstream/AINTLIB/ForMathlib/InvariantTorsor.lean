/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Ticket T-Q2 (statements) +
T-Q2-A711 / [A711-BC] / [A711-DESC] / [FP-B] (proofs). Fully proved as of 2026-07-08:
the last gap ([A711-FP]) was closed by `FinitePresentationOfFinite.lean`.
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.InvariantBaseChange
import MazurTorsion.Upstream.AINTLIB.ForMathlib.FinitePresentationOfFinite
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Finiteness.Nakayama

/-!
# Free actions and the étale-torsor theorem

This file proves Katz–Mazur A7.1.1/A7.1.2 for a finite group `G` acting on an
`R`-algebra `A`. Its main constructions and results are:

* `IsFreeAlgebraAction`, the pointwise freeness predicate;
* `MulSemiringAction.torsorMul`, the comparison `A ⊗[Aᴳ] A → (G → A)`;
* finiteness, projectivity, étaleness, and bijectivity of `torsorMul` for free actions;
* base-change invariance of fixed points for free actions.

The proofs use Chase–Harrison–Rosenberg Galois coordinates and trace averaging.
The finite-presentation input is `Algebra.FinitePresentation.of_finite_of_projective`.
See Katz–Mazur, Appendix A7; SGA III, Exposé V, Theorem 4.1; and
Demazure–Gabriel, III §2, 6.1.
-/

universe u v

open TensorProduct

variable (G : Type*) [Group G]
variable (R : Type v) (A : Type u)
variable [CommRing R] [CommRing A] [Algebra R A]
variable [MulSemiringAction G A] [SMulCommClass G R A] [SMulCommClass R G A]

/-- **KM A7.1.1's freeness condition**: `G` acts freely on the `R`-algebra `A` if for
every nonzero `R`-algebra `R'` no `g ≠ 1` fixes an `R`-algebra point
`A →ₐ[R] R'`. (Verbatim: "for any non-zero R-algebra R', and any element g ≠ id of
G, g operates without fixed points on the set Hom_{R-alg}(A, R')".) -/
def IsFreeAlgebraAction : Prop :=
  ∀ g : G, g ≠ 1 → ∀ (R' : Type u) [CommRing R'] [Algebra R R'] [Nontrivial R']
    (φ : A →ₐ[R] R'), ∃ a : A, φ (g • a) ≠ φ a

variable {G R A} in
omit [SMulCommClass R G A] in
/-- **Freeness descends to the invariant ground ring.** If `G` acts freely on the
`R`-algebra `A`, then it acts freely on `A` viewed as an `Aᴳ`-algebra: every
`Aᴳ`-algebra is an `R`-algebra (via `R → Aᴳ`) and every `Aᴳ`-algebra hom out of `A` is
an `R`-algebra hom, so the ground-`R` freeness applies verbatim. This lets
`fixedPointsBaseChange_bijective_of_isFreeAlgebraAction` ([A711-BC]) be invoked at
ground `Aᴳ`, giving `(A ⊗_{Aᴳ} C)ᴳ = C` for every `Aᴳ`-algebra `C` — the affine
base-change engine of KM 7.1.3(3c) (GHB5a-i). -/
theorem IsFreeAlgebraAction.of_fixedPoints_ground
    [SMulCommClass G ↥(FixedPoints.subalgebra R A G) A]
    [SMulCommClass ↥(FixedPoints.subalgebra R A G) G A]
    [IsScalarTower R ↥(FixedPoints.subalgebra R A G) A]
    (hfree : IsFreeAlgebraAction G R A) :
    IsFreeAlgebraAction G ↥(FixedPoints.subalgebra R A G) A := by
  intro g hg R' _ _ _ φ
  letI : Algebra R R' :=
    ((algebraMap (↥(FixedPoints.subalgebra R A G)) R').comp
      (algebraMap R ↥(FixedPoints.subalgebra R A G))).toAlgebra
  haveI : IsScalarTower R ↥(FixedPoints.subalgebra R A G) R' :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨a, ha⟩ := hfree g hg R' (φ.restrictScalars R)
  exact ⟨a, ha⟩

variable {G R A} in
/-- Elements of the fixed subalgebra commute with the `G`-action — the reversed order of
mathlib's `SMulCommClass G (FixedPoints.subalgebra A B' G) B'` instance. Together they let
`IsFreeAlgebraAction.of_fixedPoints_ground` and the `A ⊗[Aᴳ] C` base-change action fire
without manual instance plumbing. -/
instance : SMulCommClass ↥(FixedPoints.subalgebra R A G) G A :=
  SMulCommClass.symm G ↥(FixedPoints.subalgebra R A G) A

variable {G R A} in
/-- The fixed subalgebra's action on a base change of `A` (through the left factor, by
multiplication) commutes with the `G`-action — the subtype-`SMul` sibling of
`MulSemiringAction`'s `SMulCommClass G R (A ⊗[R] R')` instance. This is the instance
`FixedPoints.subalgebra` elaborates against when the GROUND ring of the tensor is itself
`Aᴳ` (as in `(A ⊗[Aᴳ] C)ᴳ`, the affine base-change engine of the free quotient): there
the `Aᴳ`-`SMul` is the subalgebra-subtype action `s • z = (s : A) • z`, not the
module-structure action, and the generic instance does not unify. -/
instance (C : Type u) [CommRing C] [Algebra ↥(FixedPoints.subalgebra R A G) C] :
    SMulCommClass G ↥(FixedPoints.subalgebra R A G)
      (A ⊗[↥(FixedPoints.subalgebra R A G)] C) where
  smul_comm g s z := by
    change g • ((s : A) • z) = (s : A) • (g • z)
    induction z with
    | zero => simp
    | add z₁ z₂ h₁ h₂ => simp only [smul_add, h₁, h₂]
    | tmul a r =>
      simp only [TensorProduct.smul_tmul']
      congr 1
      rw [smul_eq_mul, smul_eq_mul, smul_mul', s.2 g]

omit [SMulCommClass G R A] [SMulCommClass R G A] in
/-- **(T-Q2-A711, step 1 — the Chase–Harrison–Rosenberg bridge; PROVEN)** KM's freeness
condition implies the pointwise CHR condition: at every prime `𝔭` of `A` and every `g ≠ 1`
there is `a : A` with `g • a - a ∉ 𝔭`.

Take KM's `R' := A ⧸ 𝔭` (nonzero because `𝔭` is prime) and `φ :=` the quotient map. This is
the hypothesis under which the classical Galois theory of commutative rings
(Chase–Harrison–Rosenberg, Auslander–Goldman) proves `A ⊗_{Aᴳ} A ≅ ∏_G A` and étaleness —
i.e. the route by which `torsorMul_bijective_of_isFreeAlgebraAction` and
`Algebra.Etale.of_isFreeAlgebraAction` below will be discharged, KM's own reference being
[SGA III, Exp. V, Thm 4.1] (not in `refs/`). -/
theorem chr_of_isFreeAlgebraAction (hfree : IsFreeAlgebraAction G R A)
    (p : Ideal A) [hp : p.IsPrime] (g : G) (hg : g ≠ 1) :
    ∃ a : A, g • a - a ∉ p := by
  haveI : Nontrivial (A ⧸ p) := Ideal.Quotient.nontrivial_iff.mpr hp.ne_top
  obtain ⟨a, ha⟩ := hfree g hg (A ⧸ p) (Ideal.Quotient.mkₐ R p)
  refine ⟨a, fun hmem => ha ?_⟩
  have h0 : (Ideal.Quotient.mkₐ R p) (g • a - a) = 0 := by
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hmem
  rw [map_sub, sub_eq_zero] at h0
  exact h0

omit [SMulCommClass G R A] [SMulCommClass R G A] in
/-- **(T-Q2-A711, step 2)** For `g ≠ 1` the ideal generated by the "displacements"
`g • a - a` is the unit ideal: otherwise it lies in a maximal ideal, contradicting
`chr_of_isFreeAlgebraAction` there. -/
theorem span_displacement_eq_top (hfree : IsFreeAlgebraAction G R A) (g : G) (hg : g ≠ 1) :
    Ideal.span (Set.range fun a : A => g • a - a) = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  haveI : m.IsPrime := hm.isPrime
  obtain ⟨a, ha⟩ := chr_of_isFreeAlgebraAction G R A hfree m g hg
  exact ha (hle (Ideal.subset_span ⟨a, rfl⟩))

namespace MulSemiringAction

/-- The torsor-multiplication comparison map `A ⊗[Aᴳ] A → (G → A)`,
`x ⊗ y ↦ (x · (g • y))_g` (KM A7.1.1: "the natural map A ⊗_{A^G} A → ∏_{g∈G} A,
x⊗y ↦ (⋯, x⊗g(y), ⋯)"). Its bijectivity is the `G`-torsor condition for
`Aᴳ → A`. -/
noncomputable def torsorMul :
    A ⊗[FixedPoints.subalgebra R A G] A →ₐ[FixedPoints.subalgebra R A G] (G → A) :=
  Algebra.TensorProduct.lift
    (Pi.constAlgHom (FixedPoints.subalgebra R A G) G A)
    (AlgHom.pi fun g => MulSemiringAction.toAlgHom (FixedPoints.subalgebra R A G) A g)
    (fun _ _ => Commute.all _ _)

omit [SMulCommClass R G A] in
@[simp]
theorem torsorMul_tmul (x y : A) (g : G) :
    torsorMul G R A (x ⊗ₜ y) g = x * g • y := rfl

end MulSemiringAction

variable [Finite G]

section GaloisCoordinates

variable [Fintype G] [DecidableEq G]

omit [SMulCommClass R G A] [Finite G] [Fintype G] [DecidableEq G] in
/-- For each `g ≠ 1`, there is a tensor whose image under `torsorMul` is zero at `1`
and one at `g`. -/
theorem exists_torsorMul_eq_zero_one (hfree : IsFreeAlgebraAction G R A) (g : G) (hg : g ≠ 1) :
    ∃ w : A ⊗[FixedPoints.subalgebra R A G] A,
      MulSemiringAction.torsorMul G R A w 1 = 0 ∧
      MulSemiringAction.torsorMul G R A w g = 1 := by
  have h1 : (1 : A) ∈ Ideal.span (Set.range fun a : A => g • a - a) := by
    rw [span_displacement_eq_top G R A hfree g hg]; trivial
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at h1
  obtain ⟨c, hc⟩ := h1
  refine ⟨c.sum fun a ca => (ca ⊗ₜ[FixedPoints.subalgebra R A G] a
      - (ca * a) ⊗ₜ[FixedPoints.subalgebra R A G] (1 : A)), ?_, ?_⟩
  · rw [Finsupp.sum, map_sum]
    simp only [Finset.sum_apply, map_sub, Pi.sub_apply, MulSemiringAction.torsorMul_tmul,
      one_smul, mul_one]
    simp only [sub_self, Finset.sum_const_zero]
  · rw [Finsupp.sum, map_sum]
    simp only [Finset.sum_apply, map_sub, Pi.sub_apply, MulSemiringAction.torsorMul_tmul,
      smul_one, mul_one]
    rw [← hc, Finsupp.sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_eq_mul, mul_sub]

omit [SMulCommClass R G A] [Fintype G] in
/-- A free finite-group action admits Galois coordinates: a finite family `(aᵢ, bᵢ)`
with `∑ᵢ aᵢ * (g • bᵢ) = if g = 1 then 1 else 0` for every `g`. -/
theorem exists_galoisCoords (hfree : IsFreeAlgebraAction G R A) :
    ∃ S : Finset (A × A), ∀ g : G,
      (∑ p ∈ S, p.1 * (g • p.2)) = if g = 1 then 1 else 0 := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  choose w hw1 hwg using fun (g : G) (hg : g ≠ 1) => exists_torsorMul_eq_zero_one G R A hfree g hg
  set e : A ⊗[FixedPoints.subalgebra R A G] A :=
    ∏ h ∈ (Finset.univ.erase (1 : G)).attach,
      (1 - w h.1 (Finset.ne_of_mem_erase h.2)) with he
  have hev : ∀ g : G, MulSemiringAction.torsorMul G R A e g = if g = 1 then 1 else 0 := by
    intro g
    have hprod : MulSemiringAction.torsorMul G R A e g
        = ∏ h ∈ (Finset.univ.erase (1 : G)).attach,
            (1 - MulSemiringAction.torsorMul G R A (w h.1 (Finset.ne_of_mem_erase h.2)) g) := by
      rw [he, map_prod]
      simp only [map_sub, map_one, Finset.prod_apply, Pi.sub_apply, Pi.one_apply]
    rw [hprod]
    by_cases hg : g = 1
    · subst hg
      refine (Finset.prod_eq_one fun h _ => ?_).trans (by simp only [if_pos])
      rw [hw1 h.1 (Finset.ne_of_mem_erase h.2), sub_zero]
    · rw [if_neg hg]
      refine Finset.prod_eq_zero (i := ⟨g, Finset.mem_erase.mpr ⟨hg, Finset.mem_univ g⟩⟩)
        (Finset.mem_attach _ _) ?_
      rw [hwg g hg, sub_self]
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset e
  refine ⟨S, fun g => ?_⟩
  have hg := hev g
  rw [hS, map_sum] at hg
  simpa only [Finset.sum_apply, MulSemiringAction.torsorMul_tmul] using hg

end GaloisCoordinates

/-- The `G`-trace `a ↦ ∑_g g • a`, valued in the invariants. -/
def traceInvariants [Fintype G] (a : A) : FixedPoints.subalgebra R A G :=
  ⟨∑ g : G, g • a, by
    intro h
    change h • (∑ g : G, g • a) = ∑ g : G, g • a
    rw [Finset.smul_sum]
    have hre : ∀ g : G, h • (g • a) = (h * g) • a := fun g => (mul_smul h g a).symm
    simp only [hre]
    exact Fintype.sum_bijective (h * ·) (Group.mulLeft_bijective h) _ _ (fun _ => rfl)⟩

omit [SMulCommClass R G A] [Finite G] in
/-- Galois coordinates satisfy the trace dual-basis identity
`∑ᵢ aᵢ * tr(bᵢ * x) = x`. -/
theorem galoisCoords_dual [Fintype G] [DecidableEq G] {S : Finset (A × A)}
    (hS : ∀ g : G, (∑ p ∈ S, p.1 * (g • p.2)) = if g = 1 then 1 else 0) (x : A) :
    (∑ p ∈ S, p.1 * (traceInvariants G R A (p.2 * x) : A)) = x := by
  classical
  have hexp : ∀ p : A × A, (traceInvariants G R A (p.2 * x) : A) = ∑ g : G, g • (p.2 * x) :=
    fun _ => rfl
  simp only [hexp, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm : ∀ g : G, (∑ p ∈ S, p.1 * (g • (p.2 * x)))
      = (∑ p ∈ S, p.1 * (g • p.2)) * (g • x) := by
    intro g
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [smul_mul', mul_assoc]
  simp only [hterm, hS]
  rw [Finset.sum_eq_single (1 : G)]
  · simp only [if_pos, one_smul, one_mul]
  · intro g _ hg; rw [if_neg hg, zero_mul]
  · intro hc; exact absurd (Finset.mem_univ (1 : G)) hc

omit [SMulCommClass R G A] in
/-- For a free finite-group action, `A` is finite as a module over its invariants. -/
theorem Module.Finite.of_isFreeAlgebraAction (hfree : IsFreeAlgebraAction G R A) :
    Module.Finite (FixedPoints.subalgebra R A G) A := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  obtain ⟨S, hS⟩ := exists_galoisCoords G R A hfree
  refine ⟨⟨S.image Prod.fst, ?_⟩⟩
  rw [eq_top_iff]
  intro x _
  rw [← galoisCoords_dual G R A hS x]
  refine Submodule.sum_mem _ fun p hp => ?_
  have hsm : p.1 * (traceInvariants G R A (p.2 * x) : A)
      = (traceInvariants G R A (p.2 * x)) • p.1 := by
    change _ = (traceInvariants G R A (p.2 * x) : A) * p.1
    ring
  rw [hsm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.mpr
    (Finset.mem_image.mpr ⟨p, hp, rfl⟩)))

/-- The `G`-trace as an `Aᴳ`-linear map `A → Aᴳ` (the bundled form of `traceInvariants`). -/
noncomputable def traceLinear [Fintype G] :
    A →ₗ[FixedPoints.subalgebra R A G] FixedPoints.subalgebra R A G where
  toFun a := traceInvariants G R A a
  map_add' a b := by
    ext
    change (∑ g : G, g • (a + b)) = (∑ g : G, g • a) + ∑ g : G, g • b
    simp only [smul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    ext
    change (∑ g : G, g • ((c : A) * a)) = (c : A) * ∑ g : G, g • a
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [smul_mul', c.2 g]

omit [SMulCommClass R G A] in
/-- For a free finite-group action, `A` is projective as a module over its invariants. -/
theorem Module.Projective.of_isFreeAlgebraAction (hfree : IsFreeAlgebraAction G R A) :
    Module.Projective (FixedPoints.subalgebra R A G) A := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  obtain ⟨S, hS⟩ := exists_galoisCoords G R A hfree
  rw [Module.projective_def']
  refine ⟨∑ p ∈ S, (Finsupp.lsingle p.1).comp
      (traceLinear G R A ∘ₗ (LinearMap.mulLeft (FixedPoints.subalgebra R A G) p.2)), ?_⟩
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_apply,
    LinearMap.coe_sum, Finset.sum_apply, map_sum, Finsupp.lsingle_apply,
    Finsupp.linearCombination_single, id_eq, LinearMap.mulLeft_apply]
  refine Eq.trans ?_ (galoisCoords_dual G R A hS x)
  refine Finset.sum_congr rfl fun p _ => ?_
  change (traceInvariants G R A (p.2 * x) : A) * p.1
      = p.1 * (traceInvariants G R A (p.2 * x) : A)
  ring

omit [SMulCommClass R G A] in
/-- For a free finite-group action, the trace onto the invariants is surjective. -/
theorem exists_traceInvariants_eq_one [Fintype G] (hfree : IsFreeAlgebraAction G R A) :
    ∃ c : A, traceLinear G R A c = 1 := by
  classical
  haveI : Module.Finite (FixedPoints.subalgebra R A G) A :=
    Module.Finite.of_isFreeAlgebraAction G R A hfree
  obtain ⟨S, hS⟩ := exists_galoisCoords G R A hfree
  have h1 : (1 : FixedPoints.subalgebra R A G) ∈ LinearMap.range (traceLinear G R A) := by
    by_contra hnot
    have hne : (LinearMap.range (traceLinear G R A) :
        Submodule (FixedPoints.subalgebra R A G) (FixedPoints.subalgebra R A G)) ≠ ⊤ := by
      intro hc; exact hnot (hc ▸ Submodule.mem_top)
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (LinearMap.range (traceLinear G R A)) hne
    have hsub : (⊤ : Submodule (FixedPoints.subalgebra R A G) A)
        ≤ m • (⊤ : Submodule (FixedPoints.subalgebra R A G) A) := by
      intro x _
      have hx : (∑ p ∈ S, (traceLinear G R A (p.2 * x)) • p.1) = x := by
        refine Eq.trans ?_ (galoisCoords_dual G R A hS x)
        refine Finset.sum_congr rfl fun p _ => ?_
        change (traceInvariants G R A (p.2 * x) : A) * p.1
            = p.1 * (traceInvariants G R A (p.2 * x) : A)
        ring
      rw [← hx]
      refine Submodule.sum_mem _ fun p _ => ?_
      exact Submodule.smul_mem_smul (hle ⟨p.2 * x, rfl⟩) Submodule.mem_top
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
      m ⊤ Module.Finite.fg_top hsub
    have hzero : (r : A) = 0 := by
      have hone := hr0 1 Submodule.mem_top
      change (r : A) * 1 = 0 at hone
      simpa only [mul_one] using hone
    have hr' : r = 0 := Subtype.ext hzero
    rw [hr', zero_sub] at hr
    exact hm.ne_top (Ideal.eq_top_of_isUnit_mem m (by simpa only [zero_sub] using hr)
      isUnit_one.neg)
  obtain ⟨c, hc⟩ := h1
  exact ⟨c, hc⟩

omit [SMulCommClass R G A] in
/-- Additive Hilbert 90 for a free action: every additive `1`-cocycle is a coboundary. -/
theorem exists_sub_smul_eq_of_isCocycle (hfree : IsFreeAlgebraAction G R A)
    (a : G → A) (hcocycle : ∀ g h : G, a (g * h) = a g + g • a h) :
    ∃ d : A, ∀ g : G, a g = d - g • d := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨c, hc⟩ := exists_traceInvariants_eq_one G R A hfree
  have hc' : (∑ g : G, g • c) = 1 := congrArg Subtype.val hc
  refine ⟨∑ h : G, a h * (h • c), fun g => ?_⟩
  have hgd : g • (∑ h : G, a h * (h • c)) = (∑ h : G, a h * (h • c)) - a g := by
    rw [Finset.smul_sum]
    have hterm : ∀ h : G, g • (a h * (h • c)) = (a (g * h) - a g) * ((g * h) • c) := by
      intro h
      rw [smul_mul', ← mul_smul, hcocycle g h]
      ring_nf
    simp only [hterm, sub_mul]
    rw [Finset.sum_sub_distrib]
    congr 1
    · exact Fintype.sum_bijective (g * ·) (Group.mulLeft_bijective g) _ _ (fun _ => rfl)
    · rw [← Finset.mul_sum]
      have hre : (∑ h : G, (g * h) • c) = ∑ h : G, h • c :=
        Fintype.sum_bijective (g * ·) (Group.mulLeft_bijective g) _ _ (fun _ => rfl)
      rw [hre, hc', mul_one]
  rw [hgd]
  ring

/-! ### Galois descent of twisted modules

For a `1`-cocycle `w : G → Aˣ`, the twisted invariants form an `Aᴳ`-submodule of `A`.
Galois coordinates show that this module is finite projective and becomes free of rank one
after base change to `A`. -/

omit [Finite G] in
/-- Cocycle bookkeeping: `h • w(g)⁻¹ = w(hg)⁻¹ · w(h)`. -/
theorem smul_cocycle_inv (w : G → Aˣ)
    (hw : ∀ g h : G, ((w (g * h) : A)) = (w g : A) * g • (w h : A)) (g h : G) :
    h • (((w g)⁻¹ : Aˣ) : A) = (((w (h * g))⁻¹ : Aˣ) : A) * (w h : A) := by
  have hmul : (h • (((w g)⁻¹ : Aˣ) : A)) * (w (h * g) : A) = (w h : A) := by
    rw [hw h g, ← mul_assoc]
    rw [show (h • (((w g)⁻¹ : Aˣ) : A)) * (w h : A)
        = (w h : A) * (h • (((w g)⁻¹ : Aˣ) : A)) by ring]
    rw [mul_assoc, ← smul_mul' h]
    rw [show ((((w g)⁻¹ : Aˣ) : A) * (w g : A)) = 1 from (w g).inv_mul]
    rw [smul_one, mul_one]
  have hc := congrArg (fun z => z * ((((w (h * g))⁻¹ : Aˣ)) : A)) hmul
  simp only [mul_assoc] at hc
  rw [(w (h * g)).mul_inv, mul_one] at hc
  rw [hc]; ring

/-- The `w`-twisted invariants, an `Aᴳ`-submodule of `A`. -/
def twistedInvariants (w : G → Aˣ) : Submodule (FixedPoints.subalgebra R A G) A where
  carrier := {a : A | ∀ g : G, g • a = (w g : A) * a}
  zero_mem' := by intro g; simp only [smul_zero, mul_zero]
  add_mem' := by
    intro a b ha hb g
    rw [smul_add, ha g, hb g, mul_add]
  smul_mem' := by
    intro b a ha g
    change g • ((b : A) * a) = (w g : A) * ((b : A) * a)
    rw [smul_mul', b.2 g, ha g]
    ring

omit [SMulCommClass R G A] [Finite G] in
/-- The twisted average `ρ(x) = ∑_g w(g)⁻¹ · (g • x)` lands in the twisted invariants. -/
theorem twistedAvg_mem [Fintype G] (w : G → Aˣ)
    (hw : ∀ g h : G, ((w (g * h) : A)) = (w g : A) * g • (w h : A)) (x : A) :
    (∑ g : G, (((w g)⁻¹ : Aˣ) : A) * g • x) ∈ twistedInvariants G R A w := by
  intro h
  rw [Finset.smul_sum, show (w h : A) * (∑ g : G, (((w g)⁻¹ : Aˣ) : A) * g • x)
      = ∑ g : G, (w h : A) * ((((w g)⁻¹ : Aˣ) : A) * g • x) from Finset.mul_sum ..]
  have hterm : ∀ g : G, h • ((((w g)⁻¹ : Aˣ) : A) * g • x)
      = (w h : A) * ((((w (h * g))⁻¹ : Aˣ) : A) * (h * g) • x) := by
    intro g
    rw [smul_mul', smul_cocycle_inv (G := G) (A := A) w hw g h, ← mul_smul]
    ring
  simp only [hterm]
  exact Fintype.sum_bijective (h * ·) (Group.mulLeft_bijective h)
    (fun g => (w h : A) * ((((w (h * g))⁻¹ : Aˣ) : A) * (h * g) • x))
    (fun k => (w h : A) * ((((w k)⁻¹ : Aˣ) : A) * k • x)) (fun _ => rfl)

/-- The twisted average as an `Aᴳ`-linear map `A → M_w`. -/
noncomputable def twistedAvg [Fintype G] (w : G → Aˣ)
    (hw : ∀ g h : G, ((w (g * h) : A)) = (w g : A) * g • (w h : A)) :
    A →ₗ[FixedPoints.subalgebra R A G] twistedInvariants G R A w where
  toFun x := ⟨∑ g : G, (((w g)⁻¹ : Aˣ) : A) * g • x, twistedAvg_mem G R A w hw x⟩
  map_add' x y := by
    ext
    change (∑ g : G, (((w g)⁻¹ : Aˣ) : A) * g • (x + y))
      = (∑ g : G, (((w g)⁻¹ : Aˣ) : A) * g • x) +
        ∑ g : G, (((w g)⁻¹ : Aˣ) : A) * g • y
    simp only [smul_add, mul_add, Finset.sum_add_distrib]
  map_smul' b x := by
    ext
    change (∑ g : G, (((w g)⁻¹ : Aˣ) : A) * g • ((b : A) * x))
      = (b : A) * ∑ g : G, (((w g)⁻¹ : Aˣ) : A) * g • x
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [smul_mul', b.2 g]
    ring

omit [SMulCommClass R G A] [Finite G] in
/-- If `tr(c) = 1`, the twisted average retracts `A` onto the twisted invariants along
`m ↦ c * m`. -/
theorem twistedAvg_smul_eq [Fintype G] (w : G → Aˣ)
    (hw : ∀ g h : G, ((w (g * h) : A)) = (w g : A) * g • (w h : A))
    (c : A) (hc : (∑ g : G, g • c) = 1) (m : twistedInvariants G R A w) :
    twistedAvg G R A w hw (c * (m : A)) = m := by
  ext
  change (∑ g : G, (((w g)⁻¹ : Aˣ) : A) * g • (c * (m : A))) = (m : A)
  have hterm : ∀ g : G, (((w g)⁻¹ : Aˣ) : A) * g • (c * (m : A)) = (g • c) * (m : A) := by
    intro g
    rw [smul_mul', m.2 g]
    rw [show (((w g)⁻¹ : Aˣ) : A) * ((g • c) * ((w g : A) * (m : A)))
        = (g • c) * ((((w g)⁻¹ : Aˣ) : A) * (w g : A)) * (m : A) by ring,
      (w g).inv_mul, mul_one]
  simp only [hterm, ← Finset.sum_mul, hc, one_mul]

omit [SMulCommClass R G A] in
/-- **(A711-DESC)** The twisted invariants are a finite `Aᴳ`-module (a quotient of `A`). -/
theorem twistedInvariants_finite (hfree : IsFreeAlgebraAction G R A)
    (w : G → Aˣ) (hw : ∀ g h : G, ((w (g * h) : A)) = (w g : A) * g • (w h : A)) :
    Module.Finite (FixedPoints.subalgebra R A G) (twistedInvariants G R A w) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  haveI : Module.Finite (FixedPoints.subalgebra R A G) A :=
    Module.Finite.of_isFreeAlgebraAction G R A hfree
  obtain ⟨c, hc⟩ := exists_traceInvariants_eq_one G R A hfree
  have hc' : (∑ g : G, g • c) = 1 := congrArg Subtype.val hc
  refine Module.Finite.of_surjective (twistedAvg G R A w hw) fun m => ?_
  exact ⟨c * (m : A), twistedAvg_smul_eq G R A w hw c hc' m⟩

/-- A pointwise formulation of `Module.Projective.of_split`. -/
theorem Module.Projective.of_retract {B : Type u} [CommRing B] {A' M' : Type u}
    [AddCommGroup A'] [Module B A'] [AddCommGroup M'] [Module B M'] [Module.Projective B A']
    (j : M' →ₗ[B] A') (ρ : A' →ₗ[B] M') (h : ∀ m, ρ (j m) = m) :
    Module.Projective B M' := by
  apply Module.Projective.of_split j ρ
  ext m
  exact h m

omit [SMulCommClass R G A] in
/-- The twisted invariants are projective as a module over `Aᴳ`. -/
theorem twistedInvariants_projective (hfree : IsFreeAlgebraAction G R A)
    (w : G → Aˣ) (hw : ∀ g h : G, ((w (g * h) : A)) = (w g : A) * g • (w h : A)) :
    Module.Projective (FixedPoints.subalgebra R A G) (twistedInvariants G R A w) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  haveI : Module.Projective (FixedPoints.subalgebra R A G) A :=
    Module.Projective.of_isFreeAlgebraAction G R A hfree
  obtain ⟨c, hc⟩ := exists_traceInvariants_eq_one G R A hfree
  have hc' : (∑ g : G, g • c) = 1 := congrArg Subtype.val hc
  refine Module.Projective.of_retract
    ((LinearMap.mulLeft (FixedPoints.subalgebra R A G) c).comp
      (twistedInvariants G R A w).subtype)
    (twistedAvg G R A w hw) fun m => ?_
  change twistedAvg G R A w hw (c * (m : A)) = m
  exact twistedAvg_smul_eq G R A w hw c hc' m

omit [Finite G] in
/-- A `1`-cocycle is normalised: `w(1) = 1`. -/
theorem cocycle_one (w : G → Aˣ)
    (hw : ∀ g h : G, ((w (g * h) : A)) = (w g : A) * g • (w h : A)) : ((w 1 : A)) = 1 := by
  have h := hw 1 1
  rw [mul_one, one_smul] at h
  have h2 := congrArg (fun z => (((w 1)⁻¹ : Aˣ) : A) * z) h
  simp only [← mul_assoc, (w 1).inv_mul, one_mul] at h2
  exact h2.symm

/-- The multiplication map `A ⊗_{Aᴳ} M_w → A`, `a ⊗ m ↦ a · m`. -/
noncomputable def twistedMul (w : G → Aˣ) :
    A ⊗[FixedPoints.subalgebra R A G] (twistedInvariants G R A w)
      →ₗ[FixedPoints.subalgebra R A G] A :=
  TensorProduct.lift ((LinearMap.mul (FixedPoints.subalgebra R A G) A).compl₂
    (twistedInvariants G R A w).subtype)

omit [SMulCommClass R G A] [Finite G] in
@[simp]
theorem twistedMul_tmul (w : G → Aˣ) (a : A) (m : twistedInvariants G R A w) :
    twistedMul G R A w (a ⊗ₜ[FixedPoints.subalgebra R A G] m) = a * (m : A) := rfl

omit [SMulCommClass R G A] in
/-- Galois descent for rank-one modules: multiplication
`A ⊗[Aᴳ] twistedInvariants G R A w → A` is bijective. -/
theorem twistedMul_bijective (hfree : IsFreeAlgebraAction G R A)
    (w : G → Aˣ) (hw : ∀ g h : G, ((w (g * h) : A)) = (w g : A) * g • (w h : A)) :
    Function.Bijective (twistedMul G R A w) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨S, hS⟩ := exists_galoisCoords G R A hfree
  set inv : A → A ⊗[FixedPoints.subalgebra R A G] (twistedInvariants G R A w) :=
    fun x => ∑ p ∈ S, p.1 ⊗ₜ[FixedPoints.subalgebra R A G] (twistedAvg G R A w hw (p.2 * x))
    with hinv
  have hright : ∀ x : A, twistedMul G R A w (inv x) = x := by
    intro x
    rw [hinv, map_sum]
    have hterm : ∀ p : A × A, twistedMul G R A w
        (p.1 ⊗ₜ[FixedPoints.subalgebra R A G] (twistedAvg G R A w hw (p.2 * x)))
          = ∑ g : G, (((w g)⁻¹ : Aˣ) : A) * (p.1 * (g • p.2) * (g • x)) := by
      intro p
      rw [twistedMul_tmul]
      change p.1 * (∑ g : G, (((w g)⁻¹ : Aˣ) : A) * g • (p.2 * x)) = _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [smul_mul']
      ring
    simp only [hterm]
    rw [Finset.sum_comm]
    have hg : ∀ g : G, (∑ p ∈ S, (((w g)⁻¹ : Aˣ) : A) * (p.1 * (g • p.2) * (g • x)))
        = (((w g)⁻¹ : Aˣ) : A) * ((if g = 1 then (1 : A) else 0) * (g • x)) := by
      intro g
      rw [← hS g, Finset.sum_mul, Finset.mul_sum]
    simp only [hg]
    rw [Finset.sum_eq_single (1 : G)]
    · have hw1 : w 1 = 1 := Units.ext (cocycle_one (G := G) (A := A) w hw)
      rw [if_pos rfl, one_mul, one_smul, hw1]
      simp only [inv_one, Units.val_one, one_mul]
    · intro g _ hg1; rw [if_neg hg1, zero_mul, mul_zero]
    · intro hc; exact absurd (Finset.mem_univ (1 : G)) hc
  have hadd : ∀ x y : A, inv (x + y) = inv x + inv y := by
    intro x y
    rw [hinv, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← TensorProduct.tmul_add]
    congr 1
    rw [mul_add, map_add]
  have hleft : ∀ z : A ⊗[FixedPoints.subalgebra R A G] (twistedInvariants G R A w),
      inv (twistedMul G R A w z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [hinv, map_zero, mul_zero, tmul_zero, Finset.sum_const_zero]
    | add z₁ z₂ h₁ h₂ => rw [map_add, hadd, h₁, h₂]
    | tmul a m =>
      rw [twistedMul_tmul, hinv]
      have hrho : ∀ p : A × A, twistedAvg G R A w hw (p.2 * (a * (m : A)))
          = (traceInvariants G R A (p.2 * a)) • m := by
        intro p
        ext
        change (∑ g : G, (((w g)⁻¹ : Aˣ) : A) * g • (p.2 * (a * (m : A))))
            = (traceInvariants G R A (p.2 * a) : A) * (m : A)
        have hterm : ∀ g : G, (((w g)⁻¹ : Aˣ) : A) * g • (p.2 * (a * (m : A)))
            = (g • (p.2 * a)) * (m : A) := by
          intro g
          rw [smul_mul', smul_mul', m.2 g]
          rw [show (((w g)⁻¹ : Aˣ) : A) *
              ((g • p.2) * ((g • a) * ((w g : A) * (m : A)))) =
              ((g • p.2) * (g • a)) * ((((w g)⁻¹ : Aˣ) : A) * (w g : A)) *
                (m : A) by ring,
            (w g).inv_mul, mul_one]
          rw [smul_mul']
        simp only [hterm, ← Finset.sum_mul]
        rfl
      simp only [hrho]
      have hmove : ∀ p : A × A,
          p.1 ⊗ₜ[FixedPoints.subalgebra R A G]
              ((traceInvariants G R A (p.2 * a)) • m)
            = ((traceInvariants G R A (p.2 * a) : A) * p.1)
                ⊗ₜ[FixedPoints.subalgebra R A G] m := by
        intro p
        rw [TensorProduct.tmul_smul]
        rfl
      simp only [hmove]
      rw [← TensorProduct.sum_tmul]
      congr 1
      show (∑ p ∈ S, (traceInvariants G R A (p.2 * a) : A) * p.1) = a
      refine Eq.trans ?_ (galoisCoords_dual G R A hS a)
      refine Finset.sum_congr rfl fun p _ => ?_
      ring
  exact ⟨Function.LeftInverse.injective hleft, fun x => ⟨inv x, hright x⟩⟩

omit [SMulCommClass R G A] in
/-- If `Aᴳ` is local, every multiplicative `1`-cocycle is a coboundary represented by a
unit of `A`. -/
theorem exists_unit_smul_eq_of_isLocalRing [Nontrivial A]
    [IsLocalRing (FixedPoints.subalgebra R A G)] (hfree : IsFreeAlgebraAction G R A)
    (w : G → Aˣ) (hw : ∀ g h : G, ((w (g * h) : A)) = (w g : A) * g • (w h : A)) :
    ∃ d : Aˣ, ∀ g : G, g • (d : A) = (w g : A) * (d : A) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  haveI hfin : Module.Finite (FixedPoints.subalgebra R A G) (twistedInvariants G R A w) :=
    twistedInvariants_finite G R A hfree w hw
  haveI hproj : Module.Projective (FixedPoints.subalgebra R A G) (twistedInvariants G R A w) :=
    twistedInvariants_projective G R A hfree w hw
  haveI : Module.Flat (FixedPoints.subalgebra R A G) (twistedInvariants G R A w) :=
    Module.Flat.of_projective
  haveI : Module.Free (FixedPoints.subalgebra R A G) (twistedInvariants G R A w) :=
    Module.free_of_flat_of_isLocalRing
  set b := Module.Free.chooseBasis (FixedPoints.subalgebra R A G) (twistedInvariants G R A w)
    with hb
  set ι := Module.Free.ChooseBasisIndex (FixedPoints.subalgebra R A G)
    (twistedInvariants G R A w) with hι
  set bA := b.baseChange A with hbA
  have hbij := twistedMul_bijective G R A hfree w hw
  have hbne : ∀ i : ι, ((b i : A)) ≠ 0 := by
    intro i hzero
    have : b i = 0 := Subtype.ext hzero
    exact (b.ne_zero i) this
  have hsub : Subsingleton ι := by
    refine ⟨fun i j => ?_⟩
    by_contra hij
    set x : A ⊗[FixedPoints.subalgebra R A G] (twistedInvariants G R A w) :=
      ((b j : A)) ⊗ₜ[FixedPoints.subalgebra R A G] (b i)
        - ((b i : A)) ⊗ₜ[FixedPoints.subalgebra R A G] (b j) with hx
    have hx0 : x = 0 := by
      refine hbij.1 ?_
      rw [hx, map_sub, twistedMul_tmul, twistedMul_tmul, map_zero]
      ring
    have hxrepr : x = ((b j : A)) • bA i - ((b i : A)) • bA j := by
      rw [hx, hbA, Module.Basis.baseChange_apply, Module.Basis.baseChange_apply]
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul,
        mul_one, mul_one]
    have hcoef := congrArg (fun z => bA.repr z i) hx0
    rw [hxrepr] at hcoef
    simp only [map_sub, map_smul, Finsupp.coe_sub, Finsupp.coe_smul, Pi.sub_apply,
      Pi.smul_apply, Module.Basis.repr_self, smul_eq_mul, map_zero, Finsupp.coe_zero,
      Pi.zero_apply, Finsupp.single_apply] at hcoef
    have hcoef2 : ((b j : A)) = 0 := by
      simpa only [if_pos, mul_one, if_neg (Ne.symm hij), mul_zero, sub_zero] using hcoef
    exact hbne j hcoef2
  have hne : Nonempty ι := by
    by_contra hempty
    rw [not_nonempty_iff] at hempty
    obtain ⟨z, hz⟩ := hbij.2 (1 : A)
    have hz0 : z = 0 := by
      conv_lhs => rw [← bA.sum_repr z]
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
    rw [hz0, map_zero] at hz
    exact one_ne_zero hz.symm
  haveI : Unique ι := uniqueOfSubsingleton (Classical.choice hne)
  set d : A := (b default : A) with hd
  obtain ⟨z, hz⟩ := hbij.2 (1 : A)
  have hzrepr : z = (bA.repr z default) • bA default := by
    conv_lhs => rw [← bA.sum_repr z]
    rw [Finset.sum_eq_single (default : ι)]
    · intro i _ hi; exact absurd (Subsingleton.elim i default) hi
    · intro hc; exact absurd (Finset.mem_univ (default : ι)) hc
  have hzt : z = (bA.repr z default) ⊗ₜ[FixedPoints.subalgebra R A G] (b default) := by
    conv_lhs => rw [hzrepr]
    rw [hbA, Module.Basis.baseChange_apply, TensorProduct.smul_tmul']
    congr 1
    rw [smul_eq_mul, mul_one]
  rw [hzt, twistedMul_tmul] at hz
  refine ⟨Units.mkOfMulEqOne d (bA.repr z default) (by rw [mul_comm]; exact hz), fun g => ?_⟩
  change g • d = (w g : A) * d
  exact (b default).2 g

/-- The candidate inverse of `torsorMul`, built from Galois coordinates `S`:
`x ↦ ∑ᵢ aᵢ ⊗ (∑_g g⁻¹ • (x g · bᵢ))`. -/
noncomputable def galoisInv [Fintype G] (S : Finset (A × A)) (x : G → A) :
    A ⊗[FixedPoints.subalgebra R A G] A :=
  ∑ p ∈ S, p.1 ⊗ₜ[FixedPoints.subalgebra R A G] (∑ g : G, g⁻¹ • (x g * p.2))

omit [SMulCommClass R G A] [Finite G] in
/-- The pure-tensor case of the left-inverse identity for `galoisInv`: on `u ⊗ₜ v` the
Galois-coordinate inverse recovers the tensor (the trace/averaging collapse). Extracted so
`torsorMul_injective`'s induction stays short. -/
theorem galoisInv_torsorMul_tmul [Fintype G] [DecidableEq G] (S : Finset (A × A))
    (hS : ∀ g : G, (∑ p ∈ S, p.1 * (g • p.2)) = if g = 1 then 1 else 0) (u v : A) :
    galoisInv G R A S (MulSemiringAction.torsorMul G R A
        (u ⊗ₜ[FixedPoints.subalgebra R A G] v)) = u ⊗ₜ[FixedPoints.subalgebra R A G] v := by
  rw [galoisInv]
  have hterm : ∀ p : A × A,
      (∑ g : G, g⁻¹ • ((MulSemiringAction.torsorMul G R A
          (u ⊗ₜ[FixedPoints.subalgebra R A G] v) : G → A) g * p.2))
        = (traceInvariants G R A (u * p.2) : A) * v := by
    intro p
    have hinner : ∀ g : G, g⁻¹ • ((MulSemiringAction.torsorMul G R A
        (u ⊗ₜ[FixedPoints.subalgebra R A G] v) : G → A) g * p.2)
          = (g⁻¹ • (u * p.2)) * v := by
      intro g
      rw [MulSemiringAction.torsorMul_tmul,
        show u * g • v * p.2 = (u * p.2) * (g • v) by ring, smul_mul', smul_smul,
        inv_mul_cancel, one_smul]
    simp only [hinner, ← Finset.sum_mul]
    congr 1
    change (∑ g : G, g⁻¹ • (u * p.2)) = ∑ g : G, g • (u * p.2)
    exact Fintype.sum_bijective (·⁻¹) (Equiv.inv G).bijective _ _ (fun _ => rfl)
  simp only [hterm]
  have hmove : ∀ p : A × A,
      p.1 ⊗ₜ[FixedPoints.subalgebra R A G] ((traceInvariants G R A (u * p.2) : A) * v)
        = ((traceInvariants G R A (u * p.2) : A) * p.1)
            ⊗ₜ[FixedPoints.subalgebra R A G] v := by
    intro p
    change p.1 ⊗ₜ[FixedPoints.subalgebra R A G]
        ((traceInvariants G R A (u * p.2)) • v) = _
    rw [TensorProduct.tmul_smul]
    rfl
  simp only [hmove]
  rw [← TensorProduct.sum_tmul]
  congr 1
  change (∑ p ∈ S, (∑ g : G, g • (u * p.2)) * p.1) = u
  have hswap : (∑ p ∈ S, (∑ g : G, g • (u * p.2)) * p.1)
      = ∑ g : G, (g • u) * (∑ p ∈ S, p.1 * (g • p.2)) := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [smul_mul']
    ring
  rw [hswap, Finset.sum_eq_single (1 : G)]
  · rw [hS (1 : G)]
    simp only [if_pos, one_smul, mul_one]
  · intro g _ hg; rw [hS g, if_neg hg, mul_zero]
  · intro hc; exact absurd (Finset.mem_univ (1 : G)) hc

omit [SMulCommClass R G A] in
/-- Surjectivity half of `torsorMul_bijective_of_isFreeAlgebraAction`: `galoisInv S` is a
right inverse of `torsorMul` (Galois coordinates from `exists_galoisCoords`). -/
theorem torsorMul_surjective (hfree : IsFreeAlgebraAction G R A) :
    Function.Surjective (MulSemiringAction.torsorMul G R A) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  obtain ⟨S, hS⟩ := exists_galoisCoords G R A hfree
  have hright : ∀ x : G → A,
      MulSemiringAction.torsorMul G R A (galoisInv G R A S x) = x := by
    intro x
    funext h
    rw [galoisInv, map_sum]
    simp only [Finset.sum_apply, MulSemiringAction.torsorMul_tmul, Finset.smul_sum,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    have hterm : ∀ g : G, (∑ p ∈ S, p.1 * (h • g⁻¹ • (x g * p.2)))
        = ((h * g⁻¹) • x g) * (if (h * g⁻¹) = 1 then 1 else 0) := by
      intro g
      rw [← hS (h * g⁻¹), Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← mul_smul, smul_mul']
      ring
    simp only [hterm]
    rw [Finset.sum_eq_single h]
    · simp only [mul_inv_cancel, one_smul, if_pos, mul_one]
    · intro g _ hgh
      have hne : h * g⁻¹ ≠ 1 := fun hc => hgh (mul_inv_eq_one.mp hc).symm
      simp only [hne, if_false, mul_zero]
    · intro hc
      exact absurd (Finset.mem_univ h) hc
  exact fun x => ⟨galoisInv G R A S x, hright x⟩

omit [SMulCommClass R G A] in
/-- Injectivity half of `torsorMul_bijective_of_isFreeAlgebraAction`: `galoisInv S` is a
left inverse of `torsorMul` (additive, checked on pure tensors via
`galoisInv_torsorMul_tmul`). -/
theorem torsorMul_injective (hfree : IsFreeAlgebraAction G R A) :
    Function.Injective (MulSemiringAction.torsorMul G R A) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  obtain ⟨S, hS⟩ := exists_galoisCoords G R A hfree
  have hadd : ∀ x y : G → A, galoisInv G R A S (x + y)
      = galoisInv G R A S x + galoisInv G R A S y := by
    intro x y
    rw [galoisInv, galoisInv, galoisInv, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← TensorProduct.tmul_add, ← Finset.sum_add_distrib]
    refine congrArg _ (Finset.sum_congr rfl fun g _ => ?_)
    rw [Pi.add_apply, add_mul, smul_add]
  have hleft : ∀ y : A ⊗[FixedPoints.subalgebra R A G] A,
      galoisInv G R A S (MulSemiringAction.torsorMul G R A y) = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero =>
      simp only [galoisInv, map_zero, Pi.zero_apply, zero_mul, smul_zero,
        Finset.sum_const_zero, tmul_zero]
    | add y₁ y₂ h₁ h₂ => rw [map_add, hadd, h₁, h₂]
    | tmul u v => exact galoisInv_torsorMul_tmul G R A S hS u v
  exact Function.LeftInverse.injective hleft

omit [SMulCommClass R G A] in
/-- **(T-Q2-A711, step 5 — KM A7.1.1, torsor part; PROVEN)** For a free action of a finite
group the multiplication comparison `A ⊗[Aᴳ] A ≅ ∏_G A` is bijective — `Spec A` is a
`G`-torsor over `Spec Aᴳ`.

This is SGA III Exp. V Thm 4.1 (iv), *"`X₁ ⟶ X₀ ×_Y X₀` est un isomorphisme"*, obtained by
the Chase–Harrison–Rosenberg route. The Galois coordinates of `exists_galoisCoords` give
an explicit two-sided inverse `galoisInv`, so neither SGA's semi-local reduction, its
Lemme 4.2, nor its faithfully-flat residue-field enlargement is needed. None of the three
has a mathlib substrate (there is no `IsSemilocalRing`), and no finiteness of `A` over
`Aᴳ` is used either.

`galoisInv ∘ torsorMul = id` is where the trace enters: on a pure tensor `u ⊗ v` the inner
sum is `tr(u · bᵢ) · v` with `tr(u · bᵢ)` invariant, so it crosses the tensor to give
`(∑ᵢ tr(u · bᵢ) · aᵢ) ⊗ v = u ⊗ v` by the coordinate identity again. -/
theorem torsorMul_bijective_of_isFreeAlgebraAction
    (hfree : IsFreeAlgebraAction G R A) :
    Function.Bijective (MulSemiringAction.torsorMul G R A) :=
  ⟨torsorMul_injective G R A hfree, torsorMul_surjective G R A hfree⟩

/-- **(A711-BC = KM A7.1.2; PROVEN)** Free actions satisfy base change for rings of
invariants — `∗(A, G, R, R')` for every `R'`: `Aᴳ ⊗_R R' ≅ (A ⊗_R R')ᴳ`.

KM's route (extend scalars of the étale torsor, then use trivializability) is bypassed:
**averaging with a trace-one element suffices**. Injectivity comes from the `Aᴳ`-linear
retraction `s(x) = tr(c·x)` of `Aᴳ ↪ A` (`exists_traceInvariants_eq_one`); surjectivity from
the identity `φ(ψ(z)) = ∑_g g • ((c ⊗ 1) · z)`, whose right-hand side collapses to `z` when
`z` is `G`-invariant. -/
theorem fixedPointsBaseChange_bijective_of_isFreeAlgebraAction
    (hfree : IsFreeAlgebraAction G R A)
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    Function.Bijective
      (fixedPointsBaseChange (G := G) (R := R) (A := A) (R' := R')) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  obtain ⟨c, hc⟩ := exists_traceInvariants_eq_one G R A hfree
  have hc' : (∑ g : G, g • c) = 1 := congrArg Subtype.val hc
  set s : A →ₗ[FixedPoints.subalgebra R A G] FixedPoints.subalgebra R A G :=
    (traceLinear G R A).comp (LinearMap.mulLeft (FixedPoints.subalgebra R A G) c) with hs
  have hs_apply : ∀ x : A, (s x : A) = ∑ g : G, g • (c * x) := fun _ => rfl
  have hs_left : ∀ b : FixedPoints.subalgebra R A G, s (b : A) = b := by
    intro b
    ext
    rw [hs_apply]
    have hterm : ∀ g : G, g • (c * (b : A)) = (g • c) * (b : A) := by
      intro g; rw [smul_mul', b.2 g]
    simp only [hterm, ← Finset.sum_mul, hc', one_mul]
  set ψ : A ⊗[R] R' →ₗ[R] (FixedPoints.subalgebra R A G) ⊗[R] R' :=
    TensorProduct.map (s.restrictScalars R) LinearMap.id with hψ
  set φ : (FixedPoints.subalgebra R A G) ⊗[R] R' →ₐ[R] A ⊗[R] R' :=
    Algebra.TensorProduct.map (FixedPoints.subalgebra R A G).val (AlgHom.id R R') with hφ
  have hcoe : ∀ x, (fixedPointsBaseChange (G := G) (R := R) (A := A) (R' := R') x :
      A ⊗[R] R') = φ x := fun _ => rfl
  have hΘ : ∀ z : A ⊗[R] R', φ (ψ z) = ∑ g : G, g • ((c ⊗ₜ[R] (1 : R')) * z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [hψ, map_zero, mul_zero, smul_zero, Finset.sum_const_zero]
    | add z₁ z₂ h₁ h₂ =>
      rw [map_add, map_add, h₁, h₂, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun g _ => by rw [mul_add, smul_add]
    | tmul a r =>
      rw [hψ, TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.restrictScalars_apply, hφ]
      change ((s a : A) ⊗ₜ[R] r) = _
      rw [hs_apply, TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        MulSemiringAction.smul_tmul_baseChange g (c * a) r]
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · have hleft : ∀ z : (FixedPoints.subalgebra R A G) ⊗[R] R', ψ (φ z) = z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add z₁ z₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
      | tmul b r =>
        rw [hφ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hψ]
        change ψ ((b : A) ⊗ₜ[R] r) = _
        rw [hψ, TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.restrictScalars_apply,
          hs_left b]
    have h0 : φ x = φ y := by
      have hval := congrArg Subtype.val hxy
      simpa only [hcoe] using hval
    have h1 := congrArg ψ h0
    rwa [hleft, hleft] at h1
  · refine ⟨ψ (y : A ⊗[R] R'), ?_⟩
    refine Subtype.ext ?_
    rw [hcoe, hΘ]
    have hterm : ∀ g : G, g • ((c ⊗ₜ[R] (1 : R')) * (y : A ⊗[R] R'))
        = ((g • c) ⊗ₜ[R] (1 : R')) * (y : A ⊗[R] R') := by
      intro g
      rw [smul_mul', y.2 g, MulSemiringAction.smul_tmul_baseChange g c (1 : R')]
    simp only [hterm, ← Finset.sum_mul, ← TensorProduct.sum_tmul, hc']
    rw [show ((1 : A) ⊗ₜ[R] (1 : R')) = 1 from (Algebra.TensorProduct.one_def).symm, one_mul]

variable {G R A} in
/-- The inclusion of the base ring into the invariants of a base change: for an algebra `C`
over the invariants `Aᴳ`, the map `c ↦ 1 ⊗ c` lands in the `G`-fixed points of `A ⊗_{Aᴳ} C`
(the action being through the left factor). For free actions it is a bijection
(`bijective_includeRightFixedPoints` below) — KM 7.1.3(3c)'s affine base-change engine. -/
noncomputable def includeRightFixedPoints (C : Type u) [CommRing C]
    [Algebra ↥(FixedPoints.subalgebra R A G) C] :
    C →ₐ[↥(FixedPoints.subalgebra R A G)]
      ↥(FixedPoints.subalgebra ↥(FixedPoints.subalgebra R A G)
        (A ⊗[↥(FixedPoints.subalgebra R A G)] C) G) :=
  AlgHom.codRestrict Algebra.TensorProduct.includeRight
    (FixedPoints.subalgebra ↥(FixedPoints.subalgebra R A G)
      (A ⊗[↥(FixedPoints.subalgebra R A G)] C) G) fun c g => by
    change g • ((1 : A) ⊗ₜ[↥(FixedPoints.subalgebra R A G)] c) =
      (1 : A) ⊗ₜ[↥(FixedPoints.subalgebra R A G)] c
    rw [MulSemiringAction.smul_tmul_baseChange, smul_one]

variable {G R A} in
omit [SMulCommClass R G A] [Finite G] in
@[simp]
theorem includeRightFixedPoints_coe (C : Type u) [CommRing C]
    [Algebra ↥(FixedPoints.subalgebra R A G) C] (c : C) :
    (includeRightFixedPoints (G := G) (R := R) (A := A) C c :
      A ⊗[↥(FixedPoints.subalgebra R A G)] C) =
      (1 : A) ⊗ₜ[↥(FixedPoints.subalgebra R A G)] c := rfl

variable {G R A} in
omit [SMulCommClass R G A] in
/-- **The affine base-change engine of the free quotient (GHB5a-i, algebra half; KM
7.1.3(3c))**: for a free action of a finite group `G` and ANY algebra `C` over the
invariants `Aᴳ`, base change along `Aᴳ → C` has invariants exactly `C`:
`c ↦ 1 ⊗ c : C ≅ (A ⊗_{Aᴳ} C)ᴳ`.

This is [A711-BC] `fixedPointsBaseChange_bijective_of_isFreeAlgebraAction` re-grounded at
`Aᴳ` (`IsFreeAlgebraAction.of_fixedPoints_ground`), where `FixedPoints.subalgebra Aᴳ A G`
is `Aᴳ` itself and `Aᴳ ⊗_{Aᴳ} C ≅ C`. Note there is NO flatness/openness hypothesis on
`C` — this is exactly what fails for non-free actions and what powers arbitrary-base
descent of the affine quotient (`exists_invariantsπ_lift_baseChange_of_free`). -/
theorem bijective_includeRightFixedPoints (hfree : IsFreeAlgebraAction G R A)
    (C : Type u) [CommRing C] [Algebra ↥(FixedPoints.subalgebra R A G) C] :
    Function.Bijective (includeRightFixedPoints (G := G) (R := R) (A := A) C) := by
  classical
  -- [A711-BC] at ground `Aᴳ`, via the ground-switch of freeness
  have hbc := fixedPointsBaseChange_bijective_of_isFreeAlgebraAction G
    ↥(FixedPoints.subalgebra R A G) A hfree.of_fixedPoints_ground C
  -- the ground-switch identification `Aᴳ ≃ₐ[Aᴳ] FixedPoints.subalgebra Aᴳ A G`
  have hij : Function.Bijective (Algebra.ofId ↥(FixedPoints.subalgebra R A G)
      ↥(FixedPoints.subalgebra ↥(FixedPoints.subalgebra R A G) A G)) := by
    constructor
    · intro x y hxy
      exact Subtype.ext (congrArg Subtype.val hxy)
    · rintro ⟨z, hz⟩
      exact ⟨⟨z, hz⟩, Subtype.ext rfl⟩
  -- the composite `C ≅ Aᴳ ⊗ C ≅ (Fixᴳ Aᴳ) ⊗ C → (A ⊗ C)ᴳ` is elementwise `c ↦ 1 ⊗ c`
  have hfun : ∀ c : C, includeRightFixedPoints (G := G) (R := R) (A := A) C c =
      fixedPointsBaseChange (G := G) (R := ↥(FixedPoints.subalgebra R A G)) (A := A)
        (R' := C)
        (Algebra.TensorProduct.congr (AlgEquiv.ofBijective _ hij) AlgEquiv.refl
          ((Algebra.TensorProduct.lid ↥(FixedPoints.subalgebra R A G) C).symm c)) := by
    intro c
    refine Subtype.ext ?_
    rw [Algebra.TensorProduct.lid_symm_apply]
    simp only [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
      fixedPointsBaseChange_tmul, includeRightFixedPoints_coe, map_one,
      OneMemClass.coe_one]
    rfl
  have hcomp : ⇑(includeRightFixedPoints (G := G) (R := R) (A := A) C) =
      ⇑(fixedPointsBaseChange (G := G) (R := ↥(FixedPoints.subalgebra R A G)) (A := A)
        (R' := C)) ∘
      ⇑(Algebra.TensorProduct.congr (AlgEquiv.ofBijective _ hij) AlgEquiv.refl) ∘
      ⇑(Algebra.TensorProduct.lid ↥(FixedPoints.subalgebra R A G) C).symm :=
    funext hfun
  rw [hcomp]
  exact hbc.comp ((Algebra.TensorProduct.congr (AlgEquiv.ofBijective _ hij)
    AlgEquiv.refl).bijective.comp
      (Algebra.TensorProduct.lid ↥(FixedPoints.subalgebra R A G) C).symm.bijective)

omit [SMulCommClass R G A] in
/-- **(T-Q2-A711, step 7 — the separability idempotent, in its classical form)** For a free
action of a finite group there is `e ∈ A ⊗_{Aᴳ} A` with `mult(e) = 1` and
`(1 ⊗ x − x ⊗ 1) · e = 0` for every `x` — i.e. `A` is a *separable* `Aᴳ`-algebra.

`e := ∑ᵢ aᵢ ⊗ bᵢ` is the element already built in `exists_galoisCoords`. Both properties
are read off through `torsorMul`: its `1`-component is the multiplication map, and the
annihilation identity holds because `torsorMul` is an injective ring homomorphism
(`torsorMul_bijective_of_isFreeAlgebraAction`) sending `(1 ⊗ x − x ⊗ 1) · e` to
`g ↦ (g • x − x) · δ_{g,1} = 0`. -/
theorem exists_separabilityIdempotent (hfree : IsFreeAlgebraAction G R A) :
    ∃ e : A ⊗[FixedPoints.subalgebra R A G] A,
      (Algebra.TensorProduct.lmul' (FixedPoints.subalgebra R A G) (S := A)) e = 1 ∧
      ∀ x : A, ((1 : A) ⊗ₜ[FixedPoints.subalgebra R A G] x
        - x ⊗ₜ[FixedPoints.subalgebra R A G] (1 : A)) * e = 0 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  obtain ⟨S, hS⟩ := exists_galoisCoords G R A hfree
  refine ⟨∑ p ∈ S, p.1 ⊗ₜ[FixedPoints.subalgebra R A G] p.2, ?_, ?_⟩
  · rw [map_sum]
    simpa only [Algebra.TensorProduct.lmul'_apply_tmul, one_smul, if_pos] using hS 1
  · intro x
    refine (torsorMul_bijective_of_isFreeAlgebraAction G R A hfree).1 ?_
    rw [map_zero, map_mul, map_sub, map_sum]
    funext g
    simp only [Pi.mul_apply, Pi.sub_apply, Finset.sum_apply, Pi.zero_apply,
      MulSemiringAction.torsorMul_tmul, one_mul, smul_one, mul_one]
    rw [hS g]
    by_cases hg : g = 1
    · subst hg
      simp only [one_smul, sub_self, if_pos, mul_one]
    · rw [if_neg hg, mul_zero]

omit [SMulCommClass R G A] in
/-- **(T-Q2-A711, step 8 — KM A7.1.1, unramifiedness; PROVEN)** For a free action of a
finite group, `A` is formally unramified over `Aᴳ`.

`Ω[A⁄Aᴳ] = I/I²` with `I = ker(A ⊗ A → A)`. For every `x`, the element
`v = 1 ⊗ x − x ⊗ 1` lies in `I`, and `1 − e ∈ I` as well (`mult(e) = 1`); the separability
identity `v · e = 0` gives `v = v · (1 − e) ∈ I·I = I²`, so `D x = 0`. Since the image of
`D` spans `Ω`, it vanishes. -/
theorem Algebra.FormallyUnramified.of_isFreeAlgebraAction (hfree : IsFreeAlgebraAction G R A) :
    Algebra.FormallyUnramified (FixedPoints.subalgebra R A G) A := by
  obtain ⟨e, hmul, hann⟩ := exists_separabilityIdempotent G R A hfree
  let B := FixedPoints.subalgebra R A G
  have hD : ∀ x : A, KaehlerDifferential.D B A x = 0 := by
    intro x
    have hmem : (1 : A) ⊗ₜ[B] x - x ⊗ₜ[B] (1 : A) ∈ KaehlerDifferential.ideal B A :=
      KaehlerDifferential.one_smul_sub_smul_one_mem_ideal B x
    have h1e : (1 : A ⊗[B] A) - e ∈ KaehlerDifferential.ideal B A := by
      change _ ∈ RingHom.ker _
      rw [RingHom.mem_ker, map_sub, hmul, map_one, sub_self]
    have hfac : ((1 : A) ⊗ₜ[B] x - x ⊗ₜ[B] (1 : A)) =
        ((1 : A) ⊗ₜ[B] x - x ⊗ₜ[B] (1 : A)) * ((1 : A ⊗[B] A) - e) := by
      rw [mul_sub, mul_one, hann x, sub_zero]
    have hsq : ((1 : A) ⊗ₜ[B] x - x ⊗ₜ[B] (1 : A)) ∈
        (KaehlerDifferential.ideal B A) ^ 2 := by
      rw [pow_two, hfac]
      exact Ideal.mul_mem_mul hmem h1e
    change (KaehlerDifferential.ideal B A).toCotangent ⟨_, hmem⟩ = 0
    rw [Ideal.toCotangent_eq_zero]
    exact hsq
  have htop : (⊤ : Submodule A (Ω[A⁄B])) = ⊥ := by
    rw [← KaehlerDifferential.span_range_derivation, Submodule.span_eq_bot]
    rintro _ ⟨x, rfl⟩
    exact hD x
  refine ⟨?_⟩
  constructor
  intro a b
  have ha : a ∈ (⊥ : Submodule A (Ω[A⁄B])) := htop ▸ Submodule.mem_top
  have hb : b ∈ (⊥ : Submodule A (Ω[A⁄B])) := htop ▸ Submodule.mem_top
  rw [Submodule.mem_bot] at ha hb
  rw [ha, hb]

omit [SMulCommClass R G A] in
/-- **(T-Q2-A711, step 10 — KM A7.1.1, étaleness over a noetherian invariant ring; PROVEN)**
For a free action of a finite group with `Aᴳ` noetherian, `A` is étale over `Aᴳ`.

All three inputs of mathlib's `Algebra.Etale.of_formallyUnramified_of_flat`
(Stacks 08WD (3)⟹(1)) are now in hand:
* `FormallyUnramified` — `Algebra.FormallyUnramified.of_isFreeAlgebraAction` (separability
  idempotent, no hypotheses);
* `Module.Flat` — from `Module.Projective.of_isFreeAlgebraAction` (dual basis), again with
  no hypotheses;
* `Algebra.FinitePresentation` — the *only* place noetherianity is used: `Module.Finite`
  gives `Algebra.FiniteType`, and over a noetherian base finite type = finite presentation
  (`Algebra.FinitePresentation.of_finiteType`).

The `[IsNoetherianRing …]` hypothesis is a **drop-in scaffold** (the T-E4a-noeth precedent,
owner-authorized 2026-07-08): every consumer in the `Y(N)` pipeline has noetherian invariant
rings. Removing it is exactly the tracked gap **[A711-FP]** — algebra-level finite
presentation of a module-finite projective algebra over a non-noetherian base (Stacks
00QQ/05GH), which is what KM means by *"in the absence of noetherian hypotheses, this is
rather delicate."* Note **[A711-SM] dissolved**: mathlib derives `Smooth` from
unramified + flat + finitely presented, so "separable ⟹ formally smooth" is never needed.

**[A711-FP] DISCHARGED 2026-07-08 (fable-FP, [FP-B])** — the general-base theorem
`Algebra.Etale.of_isFreeAlgebraAction` below supersedes this noetherian scaffold (kept as
the historical record of the T-E4a-noeth precedent). -/
theorem Algebra.Etale.of_isFreeAlgebraAction_of_isNoetherianRing
    [IsNoetherianRing (FixedPoints.subalgebra R A G)] (hfree : IsFreeAlgebraAction G R A) :
    Algebra.Etale (FixedPoints.subalgebra R A G) A := by
  haveI : Module.Finite (FixedPoints.subalgebra R A G) A :=
    Module.Finite.of_isFreeAlgebraAction G R A hfree
  haveI : Module.Projective (FixedPoints.subalgebra R A G) A :=
    Module.Projective.of_isFreeAlgebraAction G R A hfree
  haveI : Module.Flat (FixedPoints.subalgebra R A G) A := Module.Flat.of_projective
  haveI : Algebra.FiniteType (FixedPoints.subalgebra R A G) A := inferInstance
  haveI : Algebra.FinitePresentation (FixedPoints.subalgebra R A G) A :=
    (Algebra.FinitePresentation.of_finiteType).mp inferInstance
  haveI : Algebra.FormallyUnramified (FixedPoints.subalgebra R A G) A :=
    Algebra.FormallyUnramified.of_isFreeAlgebraAction G R A hfree
  exact Algebra.Etale.of_formallyUnramified_of_flat

omit [SMulCommClass R G A] in
/-- **(T-Q2-A711, step 10′ — KM A7.1.1, étaleness part, GENERAL base; [FP-B], PROVEN)**
For a free action of a finite group, `A` is étale over the invariants — over an
**arbitrary** invariant ring: this is exactly the clause KM defers to SGA III Exp. V
Thm 4.1 with the warning *"in the absence of noetherian hypotheses, this is rather
delicate."*

Assembly = Stacks 08WD (3)⟹(1) via mathlib's `Algebra.Etale.of_formallyUnramified_of_flat`,
identical to the noetherian twin above except in one line: `Algebra.FinitePresentation`
comes from **[A711-FP]** `Algebra.FinitePresentation.of_finite_of_projective`
(`ForMathlib/FinitePresentationOfFinite.lean`: finite projective ⟹ module-finitely-presented
(Stacks 00NX) ⟹ algebra-finitely-presented (EGA IV₁ 1.4.7)) applied to the proven
f.g.-projectivity of `A` over `Aᴳ`. Noetherianity is used nowhere. -/
theorem Algebra.Etale.of_isFreeAlgebraAction (hfree : IsFreeAlgebraAction G R A) :
    Algebra.Etale (FixedPoints.subalgebra R A G) A := by
  haveI : Module.Finite (FixedPoints.subalgebra R A G) A :=
    Module.Finite.of_isFreeAlgebraAction G R A hfree
  haveI : Module.Projective (FixedPoints.subalgebra R A G) A :=
    Module.Projective.of_isFreeAlgebraAction G R A hfree
  haveI : Module.Flat (FixedPoints.subalgebra R A G) A := Module.Flat.of_projective
  haveI : Algebra.FinitePresentation (FixedPoints.subalgebra R A G) A :=
    Algebra.FinitePresentation.of_finite_of_projective _ _
  haveI : Algebra.FormallyUnramified (FixedPoints.subalgebra R A G) A :=
    Algebra.FormallyUnramified.of_isFreeAlgebraAction G R A hfree
  exact Algebra.Etale.of_formallyUnramified_of_flat

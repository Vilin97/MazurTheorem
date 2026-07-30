/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
Source: MichaelStollBayreuth/EllipticCurves at commit 3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f.
Exact-pin changes are documented in PORTING.md.
-/
module

public import Mathlib

@[expose] public section

/-!
# Material for Mathlib

This file collects the general-purpose results developed for `EllipticCurves.WeakMordellWeil`
that have nothing to do with elliptic curves and look like candidates for Mathlib.

* `MonoidHom.ofMapMulMulEqOne`: build a `MonoidHom` from `f 1 = 1` and
  `a * b * c = 1 → f a * f b * f c = 1`.
* `Valuation.map_eval_eq_of_one_lt` and `Valuation.le_one_of_root_monic`: dominance of the
  leading term of a monic polynomial with integral coefficients, and integrality of its roots.
  `Valuation.eq_one_of_mul_eq_one`: a factor of a unit is a unit, provided both factors are
  integral.
* `IsDedekindDomain.HeightOneSpectrum.finite_setOf_valuation_ne_one`,
  `.below` (the prime lying below a prime of an integral extension), `.primesAbove` and its
  finiteness `.primesAbove_finite`,
  `IsDedekindDomain.selmerGroupAbove`, `.valuationOfNeZero_eq_iff`,
  `.dvd_toAdd_valuationOfNeZero` and
  `.valuationOfNeZeroMod_mk_eq_one_iff`, which turns the Selmer condition into a
  divisibility of valuations; `Set.integer_mono` and `Set.unit_mono`, monotonicity of the
  `S`-integers and `S`-units in `S`. (`Mathlib.RingTheory.DedekindDomain.SelmerGroup` has a
  `TODO` about the `Multiplicative`/`Additive` defeq abuse in `valuationOfNeZeroMod`
  and provides no API for it.)
* `Units.modPow`, the group of `n`-th power classes of units, which
  `Mathlib.RingTheory.DedekindDomain.SelmerGroup` has only as a local notation, together
  with `map`, `congr` and `piEquiv`.
* Division with remainder by a monic polynomial: `Polynomial.Monic.divByMonic_mul_add`,
  `.modByMonic_mul_add`, `modByMonic_mem_degreeLT`, `divByMonic_mem_degreeLT`.
* `isIntegralClosure_int_integralClosure`, `NumberField.finite_classGroup_integralClosure` and
  `NumberField.fg_units_integralClosure`: the class number theorem and the finite generation of
  the unit group for the integral closure of `𝓞 K` in a finite extension of a number field `K`;
  `NumberField.subsingleton_classGroup_integralClosure` and
  `NumberField.finrank_additive_units_integralClosure` transport triviality of the class
  group and the unit rank from `𝓞 L`.
* `AdjoinRoot.discr_powerBasis_eq_discr`, `NumberField.exists_eq_discr_mul_sq`,
  `RingOfIntegers.isPrincipalIdealRing_of_finrank_eq_three_of_abs_discr_le` and
  `RingOfIntegers.finrank_additive_units_of_discr_neg`/`_pos`: the discriminant of the power
  basis of `K[X]/(f)` is `f.discr`; the field discriminant is any integral power-basis
  discriminant divided by a square; a cubic field with `|discr| ≤ 49` has trivial class group
  (Minkowski bound), and the sign of its discriminant determines the unit rank (Dirichlet).
* `AdjoinRoot.norm_mk_eq_resultant`: for monic `g`, the norm of `AdjoinRoot.mk g p` is the
  resultant of `g` and `p`. This links `Polynomial.resultant` to `Algebra.norm`.
* `AdjoinRoot.equivPiFactors`: for nonzero squarefree `f`, `K[X]/(f)` is the product of the
  fields `K[X]/(p)` over the monic irreducible factors `p` of `f`, and the induced
  `AdjoinRoot.modPowEquivPiFactors` on `n`-th power classes of units.
* `Polynomial.discr_X_sub_C_mul`: splitting off a linear factor multiplies the discriminant
  by the square of the evaluation, `((X - C x) * g).discr = g.discr * g.eval x ^ 2`.
* `Matrix.det_blockDiagonal'`, `LinearMap.det_pi'`, `Algebra.norm_prod`, `Algebra.norm_pi`:
  determinants and norms on (dependent) products decompose as products; together with
  `AdjoinRoot.norm_eq_prod_norm_projFactor`, the norm on `K[X]/(f)` as the product of the
  norms on the field factors.
* General helpers extracted from the rank example: `Squarefree.map` (transport along a
  `MulEquiv`), `Polynomial.Monic.irreducible_map_fraction_map_of_irreducible_map`
  (irreducibility over the fraction field via reduction modulo a prime),
  `Polynomial.Factors.coe_eq`, `AdjoinRoot.isIntegralElem_root_of_map`,
  `AdjoinRoot.finrank_eq_natDegree`, and the `IsPrincipalIdealRing (𝓞 ℚ)` instance.
-/

section Group

variable {G H : Type*} [Group G] [Group H]

/-- A map `f` between groups with `f 1 = 1` that sends triples with product `1` to triples
with product `1` is a homomorphism. Useful when a map is naturally defined via a symmetric
ternary relation, like collinearity on a cubic curve. -/
@[to_additive /-- A map `f` between additive groups with `f 0 = 0` that sends triples with
sum `0` to triples with sum `0` is a homomorphism. Useful when a map is naturally defined via
a symmetric ternary relation, like collinearity on a cubic curve. -/]
def MonoidHom.ofMapMulMulEqOne {f : G → H} (hf₁ : f 1 = 1)
    (hf : ∀ a b c, a * b * c = 1 → f a * f b * f c = 1) :
    G →* H :=
  .ofMapMulInv f fun x y ↦ by
    have (x : G) : f x⁻¹ = (f x)⁻¹ := by
      rw [← mul_eq_one_iff_eq_inv', ← mul_one (_ * _)]
      nth_rewrite 1 [← hf₁]
      exact hf _ _ _ <| by group
    rw [eq_mul_inv_iff_mul_eq, eq_comm, ← inv_mul_eq_one, ← mul_assoc, ← this]
    exact hf _ _ _ <| by group

@[to_additive (attr := simp)]
lemma MonoidHom.coe_ofMapMulMulEqOne {f : G → H} (hf₁ : f 1 = 1)
    (hf : ∀ a b c, a * b * c = 1 → f a * f b * f c = 1) :
    ⇑(ofMapMulMulEqOne hf₁ hf) = f :=
  rfl

/-- The preimage of a finite subgroup under an injective group homomorphism is finite. -/
@[to_additive]
lemma Subgroup.finite_comap_of_injective {f : G →* H} (hf : Function.Injective f)
    (S : Subgroup H) [Finite S] : Finite (S.comap f) :=
  .of_injective (fun x ↦ (⟨f x, x.2⟩ : S)) fun _ _ h ↦
    Subtype.ext <| hf <| congrArg Subtype.val h

/-- A product of finitely many finite subgroups is finite. -/
@[to_additive]
instance Subgroup.instFinitePi {ι : Type*} [Finite ι] {G : ι → Type*} [(i : ι) → Group (G i)]
    {S : (i : ι) → Subgroup (G i)} [(i : ι) → Finite (S i)] :
    Finite (Subgroup.pi Set.univ S) :=
  .of_injective (fun x i ↦ (⟨x.1 i, x.2 i (Set.mem_univ i)⟩ : S i)) fun _ _ h ↦
    Subtype.ext <| funext fun i ↦ congrArg Subtype.val (congrFun h i)

end Group

section Units

variable {α : Type*} [Monoid α]

@[to_additive]
lemma IsUnit.exists_pow_eq_unit_iff {a : α} (h : IsUnit a) (n : ℕ) :
    (∃ x, x ^ n = h.unit) ↔ ∃ x, x ^ n = a := by
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨x, ?_⟩, fun ⟨x, hx⟩ ↦ ?_⟩
  · simpa using congrArg Units.val hx
  · cases n with
    | zero => exact ⟨1, Units.ext (by simpa using hx)⟩
    | succ _ => exact ⟨(isUnit_pow_succ_iff.mp (hx ▸ h)).unit, Units.ext hx⟩

/-- A multiplicative equivalence preserves squarefreeness. -/
theorem Squarefree.map {β : Type*} [Monoid β] (e : α ≃* β) {r : α} (h : Squarefree r) :
    Squarefree (e r) := by
  intro x ⟨c, hc⟩
  have hd : e.symm x * e.symm x ∣ r :=
    ⟨e.symm c, by simpa [mul_assoc] using congrArg e.symm hc⟩
  simpa using (h _ hd).map e

end Units

section modPow

/-- Algebraic closedness transfers along a ring isomorphism. This is
`IsAlgClosed.of_ringEquiv` without its restriction of both fields to a common universe
(needed e.g. to transfer `IsAlgClosed ℂ` to a completion of a number field `F : Type*` at a
complex place). -/
lemma IsAlgClosed.of_ringEquiv' {k K : Type*} [Field k] [Field K] [IsAlgClosed k]
    (e : k ≃+* K) : IsAlgClosed K := by
  refine IsAlgClosed.of_exists_root _ fun p _ hpi ↦ ?_
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (p.map (e.symm : K →+* k))
    (by rw [Polynomial.degree_map]; exact (Polynomial.degree_pos_of_irreducible hpi).ne')
  refine ⟨e z, (map_eq_zero_iff (e.symm : K →+* k) e.symm.injective).mp ?_⟩
  rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map,
    show (e.symm : K →+* k) (e z) = z from e.symm_apply_apply z]
  exact hz

/-- The group of `n`-th power classes of units of `α`. This is the group underlying the
Selmer groups of `Mathlib.RingTheory.DedekindDomain.SelmerGroup`, where it only exists
as a local notation. -/
abbrev Units.modPow (α : Type*) [CommMonoid α] (n : ℕ) : Type _ :=
  αˣ ⧸ (powMonoidHom n : αˣ →* αˣ).range

/-- A multiplicative equivalence of commutative groups induces one on the quotients by the
subgroups of `n`-th powers. -/
def QuotientGroup.congrRangePowMonoidHom {G H : Type*} [CommGroup G] [CommGroup H]
    (e : G ≃* H) (n : ℕ) :
    G ⧸ (powMonoidHom n : G →* G).range ≃* H ⧸ (powMonoidHom n : H →* H).range :=
  QuotientGroup.congr _ _ e <| by
    ext x
    simp only [Subgroup.mem_map, MonoidHom.mem_range, powMonoidHom_apply]
    refine ⟨?_, ?_⟩
    · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
      exact ⟨e u, by simp⟩
    · rintro ⟨u, rfl⟩
      exact ⟨e.symm u ^ n, ⟨_, rfl⟩, by simp⟩

namespace Units.modPow

variable {α β : Type*} [CommMonoid α] [CommMonoid β] {a b c : α}

open QuotientGroup

lemma unit_eq_one_iff (ha : IsUnit a) (n : ℕ) :
    (ha.unit : Units.modPow α n) = 1 ↔ ∃ z, z ^ n = a := by
  simp [IsUnit.exists_pow_eq_unit_iff]

lemma unit_mul_unit_mul_unit_eq_one_iff (ha : IsUnit a) (hb : IsUnit b) (hc : IsUnit c) (n : ℕ) :
    (ha.unit : Units.modPow α n) * hb.unit * hc.unit = 1 ↔ ∃ z, z ^ n = a * b * c := by
  simp only [← mk_mul, ← IsUnit.unit_mul]
  exact unit_eq_one_iff ((ha.mul hb).mul hc) n

lemma mk_eq_one_iff {u : αˣ} (n : ℕ) :
    (QuotientGroup.mk u : Units.modPow α n) = 1 ↔ ∃ w : αˣ, w ^ n = u := by
  simp

lemma mk_eq_mk_iff {u v : αˣ} (n : ℕ) :
    (QuotientGroup.mk u : Units.modPow α n) = QuotientGroup.mk v ↔ ∃ w : αˣ, v = u * w ^ n := by
  simp only [QuotientGroup.eq, MonoidHom.mem_range, powMonoidHom_apply]
  exact ⟨fun ⟨w, hw⟩ ↦ ⟨w, by rw [hw]; group⟩, fun ⟨w, hw⟩ ↦ ⟨w, by rw [hw]; group⟩⟩

/-- The class of a unit is trivial in `Units.modPow α 2` exactly when the unit is a square
in `α`. -/
lemma mk_eq_one_iff_isSquare {u : αˣ} :
    (QuotientGroup.mk u : Units.modPow α 2) = 1 ↔ IsSquare (u : α) := by
  rw [mk_eq_one_iff]
  refine ⟨fun ⟨w, hw⟩ ↦ ⟨w, by rw [← hw]; push_cast [sq]; rfl⟩, fun ⟨s, hs⟩ ↦ ?_⟩
  have hsu : IsUnit s := isUnit_of_mul_isUnit_left (hs ▸ u.isUnit)
  exact ⟨hsu.unit, Units.ext (by rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, sq, ← hs])⟩

@[simp]
lemma pow_eq_one {n : ℕ} (m : Units.modPow α n) : m ^ n = 1 := by
  obtain ⟨u, rfl⟩ := mk'_surjective _ m
  rw [mk'_apply, ← mk_pow]
  exact (mk_eq_one_iff n).mpr ⟨u, rfl⟩

/-- If every unit of `α` is an `n`-th power, then the group of `n`-th power classes of units
is trivial. -/
lemma subsingleton_of_forall_exists_pow {n : ℕ} (h : ∀ u : αˣ, ∃ w : αˣ, w ^ n = u) :
    Subsingleton (Units.modPow α n) := by
  refine ⟨fun a b ↦ ?_⟩
  induction a using QuotientGroup.induction_on with
  | H u =>
    induction b using QuotientGroup.induction_on with
    | H w => rw [(mk_eq_one_iff n).mpr (h u), (mk_eq_one_iff n).mpr (h w)]

/-- Over an algebraically closed field, the group of `n`-th power classes of units is trivial
(for `n ≠ 0`). -/
lemma subsingleton_of_isAlgClosed (K : Type*) [Field K] [IsAlgClosed K] {n : ℕ} (hn : n ≠ 0) :
    Subsingleton (Units.modPow K n) := by
  refine subsingleton_of_forall_exists_pow fun u ↦ ?_
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : K) (Nat.pos_of_ne_zero hn)
  have hz0 : z ≠ 0 := fun h0 ↦ u.ne_zero (by rw [← hz, h0, zero_pow hn])
  exact ⟨Units.mk0 z hz0, Units.ext (by simp [hz])⟩

/-- A monoid homomorphism `α →* β` induces a homomorphism on `n`-th power classes of units. -/
def map (φ : α →* β) (n : ℕ) : Units.modPow α n →* Units.modPow β n :=
  QuotientGroup.map _ _ (Units.map φ) <| by
    rintro _ ⟨u, rfl⟩
    exact ⟨Units.map φ u, by simp [powMonoidHom]⟩

@[simp]
lemma map_mk (φ : α →* β) (n : ℕ) (u : αˣ) :
    map φ n (QuotientGroup.mk u) = QuotientGroup.mk (Units.map φ u) :=
  rfl

@[simp]
lemma map_id (n : ℕ) : map (MonoidHom.id α) n = MonoidHom.id (Units.modPow α n) := by
  ext
  simp

lemma map_comp {γ : Type*} [CommMonoid γ] (ψ : β →* γ) (φ : α →* β) (n : ℕ) :
    (map ψ n).comp (map φ n) = map (ψ.comp φ) n := by
  ext
  simp

@[simp]
lemma map_unit (φ : α →* β) (n : ℕ) (ha : IsUnit a) :
    map φ n (ha.unit : Units.modPow α n) = ((ha.map φ).unit : Units.modPow β n) := by
  rw [map, ← mk'_apply, map_mk']
  exact congrArg _ (Units.ext rfl)

/-- A multiplicative equivalence `α ≃* β` induces one on `n`-th power classes of units. -/
def congr (e : α ≃* β) (n : ℕ) : Units.modPow α n ≃* Units.modPow β n :=
  congrRangePowMonoidHom (Units.mapEquiv e) n

/-- The group of `n`-th power classes of units of a domain that is integral over an algebraically
closed field is trivial (for `n ≠ 0`) — the algebra map is then bijective, so this extends
`Units.modPow.subsingleton_of_isAlgClosed`; e.g., it applies to the residue fields `L[X]/(p)` of
an étale algebra over an algebraically closed field. -/
lemma subsingleton_of_isAlgClosed_of_isIntegral (k K : Type*) [Field k] [IsAlgClosed k]
    [CommRing K] [IsDomain K] [Algebra k K] [Algebra.IsIntegral k K] {n : ℕ} (hn : n ≠ 0) :
    Subsingleton (Units.modPow K n) :=
  have : Subsingleton (Units.modPow k n) := subsingleton_of_isAlgClosed k hn
  (congr (RingEquiv.ofBijective (algebraMap k K)
    IsAlgClosed.algebraMap_bijective_of_isIntegral).toMulEquiv n).symm.toEquiv.subsingleton

/-- The map on `n`-th power classes of units induced by a bijective homomorphism is
bijective. -/
lemma bijective_map {φ : α →* β} (hφ : Function.Bijective φ) (n : ℕ) :
    Function.Bijective (map φ n) := by
  have h : ⇑(map φ n) = ⇑(congr (MulEquiv.ofBijective φ hφ) n) := by
    ext m
    induction m using QuotientGroup.induction_on with
    | H u => rfl
  rw [h]
  exact (congr (MulEquiv.ofBijective φ hφ) n).bijective

/-- Taking `n`-th power classes of units commutes with products. -/
noncomputable def piEquiv {ι : Type*} (α : ι → Type*) [(i : ι) → CommMonoid (α i)] (n : ℕ) :
    Units.modPow ((i : ι) → α i) n ≃* ((i : ι) → Units.modPow (α i) n) :=
  (congrRangePowMonoidHom MulEquiv.piUnits n).trans <|
    mulEquivPiModRangePowMonoidHom (fun i ↦ (α i)ˣ) n

@[simp]
lemma piEquiv_mk {ι : Type*} (α : ι → Type*) [(i : ι) → CommMonoid (α i)] (n : ℕ)
    (u : ((i : ι) → α i)ˣ) (i : ι) :
    piEquiv α n (QuotientGroup.mk u) i = QuotientGroup.mk (MulEquiv.piUnits u i) := by
  simp [piEquiv, congrRangePowMonoidHom, mulEquivPiModRangePowMonoidHom_apply]

end Units.modPow

end modPow

section Ideal

/-- An ideal contraction is nonzero as soon as its further contraction along an injective ring
homomorphism is nonzero. -/
lemma Ideal.comap_ne_bot_of_comap_comap_ne_bot {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] {ρ : R →+* S} {φ : S →+* T} (hρ : Function.Injective ρ) {I : Ideal T}
    (h : (I.comap φ).comap ρ ≠ ⊥) : I.comap φ ≠ ⊥ := fun h0 ↦
  h (by rw [h0, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot ρ).mp hρ])

end Ideal

section LinearAlgebra

/-- A "diagonal" family of vectors — supported at the family index with nonzero value there —
is linearly independent. -/
lemma linearIndependent_of_diagonal {ι A : Type*} [CommRing A] [NoZeroDivisors A]
    {u : ι → ι → A} (hd : ∀ i, u i i ≠ 0) (ho : ∀ i j, j ≠ i → u i j = 0) :
    LinearIndependent A u := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h := congrFun hg i
  rw [Finset.sum_apply, Pi.zero_apply,
    Finset.sum_eq_single i
      (fun j _ hji ↦ by rw [Pi.smul_apply, ho j i (fun hc ↦ hji (hc ▸ rfl)), smul_zero])
      (fun hni ↦ absurd hi hni),
    Pi.smul_apply, smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_right (hd i)

/-- The determinant of a block diagonal matrix with (possibly) non-uniform block sizes is the
product of the determinants of the blocks. Dependent version of `Matrix.det_blockDiagonal`. -/
theorem Matrix.det_blockDiagonal' {ι : Type*} [Fintype ι] [DecidableEq ι] {η : ι → Type*}
    [(i : ι) → Fintype (η i)] [(i : ι) → DecidableEq (η i)] {R : Type*} [CommRing R]
    (M : (i : ι) → Matrix (η i) (η i) R) :
    (Matrix.blockDiagonal' M).det = ∏ i, (M i).det := by
  let : LinearOrder ι := LinearOrder.lift' _ (Fintype.equivFin ι).injective
  have hbt : (blockDiagonal' M).BlockTriangular Sigma.fst := by
    intro x y h
    obtain ⟨k, i⟩ := x
    obtain ⟨k', j⟩ := y
    exact blockDiagonal'_apply_ne _ _ _ h.ne'
  rw [hbt.det_fintype]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  let e : {x : Σ i, η i // x.fst = k} ≃ η k :=
    { toFun := fun x ↦ x.2 ▸ x.1.2
      invFun := fun j ↦ ⟨⟨k, j⟩, rfl⟩
      left_inv := fun ⟨⟨k', j⟩, h⟩ ↦ by subst h; rfl
      right_inv := fun j ↦ rfl }
  rw [← Matrix.det_reindex_self e]
  congr 1
  ext j j'
  simp [e, Matrix.toSquareBlock_def]

/-- The determinant of a component-wise endomorphism of a finite product of finite free modules
is the product of the determinants of the components. Dependent version of `LinearMap.det_pi`. -/
theorem LinearMap.det_pi' {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {S : ι → Type*}
    [(i : ι) → AddCommGroup (S i)] [(i : ι) → Module R (S i)]
    [(i : ι) → Module.Free R (S i)] [(i : ι) → Module.Finite R (S i)]
    (f : (i : ι) → S i →ₗ[R] S i) :
    (LinearMap.pi fun i ↦ (f i).comp (LinearMap.proj i)).det = ∏ i, (f i).det := by
  classical
  let b (i : ι) := Module.Free.chooseBasis R (S i)
  rw [← LinearMap.det_toMatrix (Pi.basis b)]
  have h : LinearMap.toMatrix (Pi.basis b) (Pi.basis b)
        (LinearMap.pi fun i ↦ (f i).comp (LinearMap.proj i))
      = Matrix.blockDiagonal' fun i ↦ LinearMap.toMatrix (b i) (b i) (f i) := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    rcases eq_or_ne i₁ j₁ with rfl | hne
    · simp [LinearMap.toMatrix_apply']
    · simp [LinearMap.toMatrix_apply', Matrix.blockDiagonal'_apply_ne _ _ _ hne,
        Pi.single_eq_of_ne hne]
  rw [h, Matrix.det_blockDiagonal']
  simp [LinearMap.det_toMatrix]

end LinearAlgebra

section Valuation

open Polynomial

variable {L Γ : Type*} [CommRing L] [LinearOrderedCommGroupWithZero Γ] (ν : Valuation L Γ)
  {t a b : L}

lemma Valuation.map_natCast_le_one {R : Type*} [Ring R] (ν : Valuation R Γ) (n : ℕ) :
    ν (n : R) ≤ 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ]
    exact (ν.map_add _ _).trans (max_le ih ν.map_one.le)

/-- If a product of two integral elements is a unit, then each factor is a unit. -/
lemma Valuation.eq_one_of_mul_eq_one (ha : ν a ≤ 1) (hb : ν b ≤ 1) (hab : ν (a * b) = 1) :
    ν a = 1 := by
  refine le_antisymm ha ?_
  calc (1 : Γ) = ν a * ν b := by rw [← map_mul, hab]
    _ ≤ ν a * 1 := by gcongr
    _ = ν a := mul_one _

/-- If `p` is monic with coefficients that are integral for the valuation `ν` and `1 < ν t`,
then the value of `p` at `t` is dominated by the leading term: `ν (p.eval t) = ν t ^ p.natDegree`.
In particular, `p.eval t ≠ 0`. -/
lemma Valuation.map_eval_eq_of_one_lt {p : L[X]} (hp : p.Monic)
    (hcoeff : ∀ i < p.natDegree, ν (p.coeff i) ≤ 1) (ht : 1 < ν t) :
    ν (p.eval t) = ν t ^ p.natDegree := by
  set n := p.natDegree with hn
  have h0 : ν t ≠ 0 := (zero_lt_one.trans ht).ne'
  have heval : p.eval t = (∑ i ∈ Finset.range n, p.coeff i * t ^ i) + t ^ n := by
    rw [eval_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, one_mul]
  have hlt : ν (∑ i ∈ Finset.range n, p.coeff i * t ^ i) < ν (t ^ n) := by
    rw [map_pow]
    refine ν.map_sum_lt (pow_ne_zero n h0) fun i hi ↦ ?_
    rw [Finset.mem_range] at hi
    calc ν (p.coeff i * t ^ i) ≤ 1 * ν t ^ i := by
          rw [map_mul, map_pow]; gcongr; exact hcoeff i hi
      _ = ν t ^ i := one_mul _
      _ < ν t ^ n := pow_lt_pow_right₀ ht hi
  rw [heval, ν.map_add_eq_of_lt_right hlt, map_pow]

/-- A root of a monic polynomial of positive degree with coefficients that are integral for the
valuation `ν` is itself integral. (This is a concrete form of the fact that valuation rings are
integrally closed.) -/
lemma Valuation.le_one_of_root_monic {p : L[X]} (hp : p.Monic)
    (hcoeff : ∀ i < p.natDegree, ν (p.coeff i) ≤ 1) (hdeg : p.natDegree ≠ 0)
    (heq : p.eval t = 0) :
    ν t ≤ 1 := by
  by_contra! hlt
  have h := ν.map_eval_eq_of_one_lt hp hcoeff hlt
  rw [heq, map_zero] at h
  exact (zero_lt_one.trans hlt).ne' (pow_eq_zero_iff hdeg |>.mp h.symm)

end Valuation

section DedekindDomain

open IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- A nonzero element of the fraction field of a Dedekind domain has trivial valuation at all
but finitely many primes. -/
lemma IsDedekindDomain.HeightOneSpectrum.finite_setOf_valuation_ne_one {x : K} (hx : x ≠ 0) :
    {v : HeightOneSpectrum R | v.valuation K x ≠ 1}.Finite := by
  refine ((Support.finite R x).union (Support.finite R x⁻¹)).subset fun v hv ↦ ?_
  rcases lt_or_gt_of_ne hv with h | h
  · refine .inr ?_
    rw [Support, Set.mem_setOf_eq, map_inv₀,
      one_lt_inv₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx))]
    exact h
  · exact .inl h

lemma Set.integer_mono {S T : Set (HeightOneSpectrum R)} (hST : S ⊆ T) :
    S.integer K ≤ T.integer K :=
  fun _ hx v hv ↦ hx v fun hvS ↦ hv (hST hvS)

lemma Set.unit_mono {S T : Set (HeightOneSpectrum R)} (hST : S ⊆ T) : S.unit K ≤ T.unit K :=
  fun _ hx v hv ↦ hx v fun hvS ↦ hv (hST hvS)

/-- Ideal-level divisibility characterization of `Associates.count`: the multiplicity of `v` in
`J` is at least `k` iff `v ^ k` divides `J`. -/
lemma IsDedekindDomain.HeightOneSpectrum.le_count_iff_le {A : Type*} [CommRing A]
    [IsDedekindDomain A] (v : HeightOneSpectrum A) {J : Ideal A} (hJ : J ≠ ⊥) (k : ℕ) :
    k ≤ (Associates.mk v.asIdeal).count (Associates.mk J).factors ↔ J ≤ v.asIdeal ^ k := by
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ) v.associates_irreducible,
    ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le]

/-- Divisibility characterization of `Associates.count` for a height one prime: the `v`-adic
valuation of `x` is at least `k` iff `x ∈ v ^ k`. -/
lemma IsDedekindDomain.HeightOneSpectrum.le_count_iff {A : Type*} [CommRing A]
    [IsDedekindDomain A] (v : HeightOneSpectrum A) {x : A} (hx : x ≠ 0) (k : ℕ) :
    k ≤ Associates.count (Associates.mk v.asIdeal) (Associates.mk (Ideal.span {x})).factors ↔
      x ∈ v.asIdeal ^ k := by
  rw [v.le_count_iff_le (fun h ↦ hx (Ideal.span_singleton_eq_bot.mp h)) k,
    Ideal.span_singleton_le_iff_mem]

/-- The `Multiplicative ℤ`-valued valuation of a unit is determined by the `ℤᵐ⁰`-valued one. -/
lemma IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq_iff (v : HeightOneSpectrum R)
    (u : Kˣ) (m : Multiplicative ℤ) :
    v.valuationOfNeZero u = m ↔ v.valuation K (u : K) = (m : WithZero (Multiplicative ℤ)) := by
  rw [← WithZero.coe_inj, valuationOfNeZero_eq]

/-- If the valuation of a unit `u` is the `n`-th power of the valuation of a unit `z`, then the
`v`-adic order of `u` is divisible by `n`. -/
lemma IsDedekindDomain.HeightOneSpectrum.dvd_toAdd_valuationOfNeZero (v : HeightOneSpectrum R)
    {n : ℕ} {u z : Kˣ} (h : v.valuation K (u : K) = v.valuation K (z : K) ^ n) :
    (n : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero u) := by
  have hu : v.valuationOfNeZero u = v.valuationOfNeZero z ^ n := by
    rw [valuationOfNeZero_eq_iff]
    push_cast
    rw [valuationOfNeZero_eq, h]
  exact ⟨Multiplicative.toAdd (v.valuationOfNeZero z), by rw [hu]; simp [toAdd_pow]⟩

/-- The class of a unit `u` in `Units.modPow K n` has trivial image under the `v`-adic valuation
mod `n` exactly when the `v`-adic valuation of `u` is divisible by `n`. -/
lemma IsDedekindDomain.HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff
    (v : HeightOneSpectrum R) (n : ℕ) (u : Kˣ) :
    v.valuationOfNeZeroMod n (QuotientGroup.mk u) = 1 ↔
      (n : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero u) := by
  rw [valuationOfNeZeroMod, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, EmbeddingLike.map_eq_one_iff]
  refine (QuotientGroup.eq_one_iff _).trans ?_
  rw [Multiplicative.mem_toSubgroup, AddSubgroup.mem_zmultiples_iff]
  exact ⟨fun ⟨k, hk⟩ ↦ ⟨k, by rw [← hk]; ring⟩, fun ⟨k, hk⟩ ↦ ⟨k, by rw [hk]; ring⟩⟩

/-- If a power of the prime `v` is generated by `π`, then `π` is a `w`-adic unit at every prime
`w ≠ v`. -/
lemma IsDedekindDomain.HeightOneSpectrum.valuation_algebraMap_eq_one_of_pow_eq_span
    {v w : HeightOneSpectrum R} (hne : w ≠ v) {n : ℕ} {π : R}
    (h : v.asIdeal ^ n = Ideal.span {π}) :
    w.valuation K (algebraMap R K π) = 1 := by
  refine w.valuation_eq_one_iff_notMem.mpr fun hmem ↦ hne (HeightOneSpectrum.ext ?_).symm
  refine v.isMaximal.eq_of_le w.isPrime.ne_top (Ideal.IsPrime.le_of_pow_le (n := n) ?_)
  rwa [h, Ideal.span_le, Set.singleton_subset_iff]

open WithZero in
/-- The valuation of an element of `R` not lying in `v ^ 2` is at least `exp (-1)`: it can
vanish at `v` at most to first order. -/
lemma IsDedekindDomain.HeightOneSpectrum.exp_neg_one_le_valuation_algebraMap
    {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
    [IsFractionRing R K] (v : HeightOneSpectrum R) {r : R} (hr : r ∉ v.asIdeal ^ 2) :
    exp (-1 : ℤ) ≤ v.valuation K (algebraMap R K r) := by
  rw [valuation_of_algebraMap]
  have h2 : ¬ v.intValuation r ≤ exp (-((2 : ℕ) : ℤ)) := fun hc ↦
    hr ((intValuation_le_pow_iff_mem v r 2).mp hc)
  rw [intValuation_le_exp_iff_le_emultiplicity, not_le] at h2
  rw [show (-1 : ℤ) = -((1 : ℕ) : ℤ) by norm_num,
    exp_le_intValuation_iff_emultiplicity_le]
  exact Order.le_of_lt_succ (by exact_mod_cast h2)

/-- In a principal ideal domain, a squarefree element lies in no square of a maximal ideal. -/
lemma IsDedekindDomain.HeightOneSpectrum.notMem_pow_two_of_squarefree
    {R : Type*} [CommRing R] [IsPrincipalIdealRing R] (v : HeightOneSpectrum R) {r : R}
    (hr : Squarefree r) : r ∉ v.asIdeal ^ 2 := by
  obtain ⟨p, hp⟩ := IsPrincipalIdealRing.principal v.asIdeal
  intro hmem
  rw [hp, Ideal.submodule_span_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
  have hunit : IsUnit p := hr p (by rwa [← sq])
  exact v.isPrime.ne_top <| by
    rw [hp, Ideal.submodule_span_eq, Ideal.span_singleton_eq_top]
    exact hunit

variable (R) (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra R B]

/-- The primes of `B` lying above a set `S` of primes of `R`. -/
def IsDedekindDomain.HeightOneSpectrum.primesAbove (S : Set (HeightOneSpectrum R)) :
    Set (HeightOneSpectrum B) :=
  {w | ∃ v ∈ S, v.asIdeal = w.asIdeal.under R}

-- The `IsDedekindDomain` instances are needed to *state* this (they are parameters of
-- `HeightOneSpectrum`), but are erased from the proof term (`nolint unusedArguments`),
-- which makes the linter fire spuriously.
omit [IsDedekindDomain R] [IsDedekindDomain B] in
lemma IsDedekindDomain.HeightOneSpectrum.primesAbove_mono {S T : Set (HeightOneSpectrum R)}
    (hST : S ⊆ T) : primesAbove R B S ⊆ primesAbove R B T :=
  fun _ ⟨v, hv, hva⟩ ↦ ⟨v, hST hv, hva⟩

-- as for `primesAbove_mono`, the `IsDedekindDomain` instances are needed for the statement
omit [IsDedekindDomain R] [IsDedekindDomain B] in
@[simp]
lemma IsDedekindDomain.HeightOneSpectrum.primesAbove_empty :
    primesAbove R B (∅ : Set (HeightOneSpectrum R)) = ∅ := by
  ext w
  simp [primesAbove]

/-- The prime of `R` lying below a prime `w` of an integral extension `B`. -/
def IsDedekindDomain.HeightOneSpectrum.below [Algebra.IsIntegral R B] (w : HeightOneSpectrum B) :
    HeightOneSpectrum R where
  asIdeal := w.asIdeal.under R
  isPrime := Ideal.IsPrime.under R w.asIdeal
  ne_bot := Ideal.IsIntegral.comap_ne_bot R w.ne_bot

@[simp]
lemma IsDedekindDomain.HeightOneSpectrum.below_asIdeal [Algebra.IsIntegral R B]
    (w : HeightOneSpectrum B) :
    (w.below R).asIdeal = w.asIdeal.under R :=
  rfl

instance IsDedekindDomain.HeightOneSpectrum.instLiesOverBelow [Algebra.IsIntegral R B]
    (w : HeightOneSpectrum B) :
    w.asIdeal.LiesOver (w.below R).asIdeal :=
  Ideal.over_under ..

lemma IsDedekindDomain.HeightOneSpectrum.mem_primesAbove_iff [Algebra.IsIntegral R B]
    (S : Set (HeightOneSpectrum R)) (w : HeightOneSpectrum B) :
    w ∈ primesAbove R B S ↔ w.below R ∈ S := by
  refine ⟨fun ⟨v, hv, hva⟩ ↦ ?_, fun hw ↦ ⟨w.below R, hw, rfl⟩⟩
  rwa [show w.below R = v from HeightOneSpectrum.ext hva.symm]

/-- Only finitely many primes of `B` lie above a finite set of primes of `R`: each fiber
injects into `Ideal.primesOver`, which is finite for a Dedekind extension. -/
lemma IsDedekindDomain.HeightOneSpectrum.primesAbove_finite [Algebra.IsIntegral R B]
    [Module.IsTorsionFree R B] {S : Set (HeightOneSpectrum R)} (hS : S.Finite) :
    (primesAbove R B S).Finite := by
  have hsub : primesAbove R B S ⊆
      ⋃ v ∈ S, {w : HeightOneSpectrum B | w.asIdeal ∈ v.asIdeal.primesOver B} :=
    fun w ⟨v, hv, hva⟩ ↦ Set.mem_biUnion hv ⟨w.isPrime, ⟨hva⟩⟩
  refine (hS.biUnion fun v _ ↦ ?_).subset hsub
  have := v.isMaximal
  exact (IsDedekindDomain.primesOver_finite v.asIdeal B).preimage
    (fun a _ b _ hab ↦ HeightOneSpectrum.ext hab)

/-- The `S`-Selmer group of `L`, where `B` is a Dedekind domain with fraction field `L` and `S`
is a set of primes of `R`: the classes of `Lˣ` modulo `n`-th powers whose valuation is divisible
by `n` at every prime of `B` not lying above `S`. -/
def IsDedekindDomain.selmerGroupAbove (L : Type*) [Field L] [Algebra B L] [IsFractionRing B L]
    (S : Set (HeightOneSpectrum R)) (n : ℕ) : Subgroup (Units.modPow L n) :=
  selmerGroup (R := B) (K := L) (S := HeightOneSpectrum.primesAbove R B S) (n := n)

omit [IsDedekindDomain R] in
lemma IsDedekindDomain.mem_selmerGroupAbove_iff (L : Type*) [Field L] [Algebra B L]
    [IsFractionRing B L] (S : Set (HeightOneSpectrum R)) (n : ℕ) (x : Units.modPow L n) :
    x ∈ selmerGroupAbove R B L S n ↔
      ∀ w ∉ HeightOneSpectrum.primesAbove R B S, w.valuationOfNeZeroMod n x = 1 :=
  Iff.rfl

-- as for `mem_selmerGroupAbove_iff`, the instances are needed for the statement only
omit [IsDedekindDomain R] in
lemma IsDedekindDomain.selmerGroupAbove_empty (L : Type*) [Field L] [Algebra B L]
    [IsFractionRing B L] (n : ℕ) :
    selmerGroupAbove R B L (∅ : Set (HeightOneSpectrum R)) n =
      selmerGroup (R := B) (K := L) (S := (∅ : Set (HeightOneSpectrum B))) (n := n) := by
  rw [selmerGroupAbove, HeightOneSpectrum.primesAbove_empty]

namespace IsDiscreteValuationRing

variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

@[simp]
lemma asIdeal_maximalIdeal : (maximalIdeal A).asIdeal = IsLocalRing.maximalIdeal A := rfl

variable {A}

/-- The maximal ideal is the only height-one prime of a discrete valuation ring. -/
lemma _root_.IsDedekindDomain.HeightOneSpectrum.eq_maximalIdeal (P : HeightOneSpectrum A) :
    P = maximalIdeal A :=
  HeightOneSpectrum.ext (IsLocalRing.eq_maximalIdeal P.isMaximal)

end IsDiscreteValuationRing

namespace IsDedekindDomain.HeightOneSpectrum

variable {B C : Type*} [CommRing B] [IsDedekindDomain B] [CommRing C] [IsDedekindDomain C]

/-- The height-one prime of `B` obtained by contracting a height-one prime along a ring
homomorphism `ψ : B →+* C`, given that the contraction is nonzero. -/
def comapOfNeBot (ψ : B →+* C) (w : HeightOneSpectrum C) (hne : w.asIdeal.comap ψ ≠ ⊥) :
    HeightOneSpectrum B where
  asIdeal := w.asIdeal.comap ψ
  isPrime := w.isPrime.comap ψ
  ne_bot := hne

-- the `IsDedekindDomain` instances are needed to state this, but the proof (`rfl`) erases them
omit [IsDedekindDomain B] [IsDedekindDomain C] in
@[simp]
lemma comapOfNeBot_asIdeal (ψ : B →+* C) (w : HeightOneSpectrum C)
    (hne : w.asIdeal.comap ψ ≠ ⊥) :
    (comapOfNeBot ψ w hne).asIdeal = w.asIdeal.comap ψ :=
  rfl

variable {L N : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
  [Field N] [Algebra C N] [IsFractionRing C N]

/-- The `w`-adic valuation of `φ u` is the valuation of `u` at the contracted prime, raised
to a fixed positive power (the ramification index), for an embedding `φ` of fraction fields
compatible with an embedding `ψ` of Dedekind domains. -/
theorem exists_valuationOfNeZero_map_eq (φ : L →+* N) (ψ : B →+* C)
    (hcomp : (algebraMap C N).comp ψ = φ.comp (algebraMap B L))
    (w : HeightOneSpectrum C) (hne : w.asIdeal.comap ψ ≠ ⊥) :
    ∃ e : ℕ, ∀ u : Lˣ, w.valuationOfNeZero (Units.map (φ : L →* N) u) =
      (comapOfNeBot ψ w hne).valuationOfNeZero u ^ e := by
  let _ : Algebra B C := ψ.toAlgebra
  let _ : Algebra L N := φ.toAlgebra
  let _ : Algebra B N := (φ.comp (algebraMap B L)).toAlgebra
  have hψ : Function.Injective ψ := by
    have h : Function.Injective ((algebraMap C N).comp ψ) := by
      rw [hcomp]
      exact φ.injective.comp (IsFractionRing.injective B L)
    exact fun x y hxy ↦ h (by simp only [RingHom.comp_apply, hxy])
  have ht1 : IsScalarTower B L N := .of_algebraMap_eq' rfl
  have ht2 : IsScalarTower B C N := .of_algebraMap_eq fun x ↦ (RingHom.congr_fun hcomp x).symm
  have htf : Module.IsTorsionFree B C := Module.isTorsionFree_iff_algebraMap_injective.mpr hψ
  have hlie : w.asIdeal.LiesOver (comapOfNeBot ψ w hne).asIdeal := ⟨rfl⟩
  refine ⟨(comapOfNeBot ψ w hne).asIdeal.ramificationIdx w.asIdeal, fun u ↦ ?_⟩
  rw [valuationOfNeZero_eq_iff, WithZero.coe_pow, valuationOfNeZero_eq, Units.coe_map,
    MonoidHom.coe_coe]
  exact (valuation_liesOver N (comapOfNeBot ψ w hne) w (u : L)).symm

/-- Divisibility of adic valuations transports along compatible embeddings: if the valuation
of `u` at the contracted prime is divisible by `n`, so is the `w`-adic valuation of `φ u`. -/
theorem dvd_toAdd_valuationOfNeZero_map (φ : L →+* N) (ψ : B →+* C)
    (hcomp : (algebraMap C N).comp ψ = φ.comp (algebraMap B L))
    (w : HeightOneSpectrum C) (hne : w.asIdeal.comap ψ ≠ ⊥) {n : ℕ} (u : Lˣ)
    (h : (n : ℤ) ∣ Multiplicative.toAdd ((comapOfNeBot ψ w hne).valuationOfNeZero u)) :
    (n : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero (Units.map (φ : L →* N) u)) := by
  obtain ⟨e, he⟩ := exists_valuationOfNeZero_map_eq φ ψ hcomp w hne
  rw [he u, toAdd_pow, nsmul_eq_mul]
  exact h.mul_left _

/-- The maximal ideal of the ring of integers of the completion of `K` at `v` contracts
to `v` itself. -/
theorem comap_maximalIdeal_adicCompletionIntegers (v : HeightOneSpectrum R) :
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)).comap
      (algebraMap R (v.adicCompletionIntegers K)) = v.asIdeal := by
  ext x
  rw [Ideal.mem_comap, ← valuation_lt_one_iff_mem (K := K)]
  refine (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion K)
    (WithZero (Multiplicative ℤ))))).trans ?_
  rw [show ((algebraMap R (v.adicCompletionIntegers K) x : v.adicCompletionIntegers K) :
    v.adicCompletion K) = ((algebraMap R K x : K) : v.adicCompletion K) from rfl,
    valuedAdicCompletion_eq_valuation']

end IsDedekindDomain.HeightOneSpectrum

end DedekindDomain

namespace Polynomial

variable {R : Type*} [CommRing R] {g : R[X]}

/-- The resultant of `f` with the linear polynomial `C x - X` is `f.eval x`.
Note the absence of a sign: `C x - X` is `-(X - C x)`, and the two signs cancel. -/
lemma resultant_C_sub_X (f : R[X]) (x : R) (m : ℕ) (hm : f.natDegree ≤ m) :
    f.resultant (C x - X) m 1 = f.eval x := by
  have h : f.resultant (X - C x) m 1 = (-1) ^ m * f.eval x := by
    have := resultant_X_sub_C_pow_right f x m 1 hm
    rwa [pow_one, mul_one, pow_one] at this
  rw [show C x - X = C (-1 : R) * (X - C x) by simp, resultant_C_mul_right, h,
    ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

lemma Monic.resultant_one_right (hg : g.Monic) (n : ℕ) :
    g.resultant 1 g.natDegree n = 1 := by
  convert resultant_add_right_deg g 1 g.natDegree 0 n (by simp)
  · simp
  rw [← C_1, resultant_C_zero_right, one_pow, mul_one, hg.coeff_natDegree, one_pow]

/-- For monic `g`, the resultant does not depend on the size parameter used for the second
argument, as long as it is at least its degree. -/
lemma Monic.resultant_congr_right (hg : g.Monic) {p : R[X]} {n₁ n₂ : ℕ}
    (h₁ : p.natDegree ≤ n₁) (h₂ : n₁ ≤ n₂) :
    g.resultant p g.natDegree n₂ = g.resultant p g.natDegree n₁ := by
  rw [← Nat.add_sub_cancel' h₂, resultant_add_right_deg _ _ _ _ _ h₁, hg.coeff_natDegree,
    one_pow, one_mul]

private lemma succ_mul_div_two {n : ℕ} (hn : 0 < n) : (n + 1) * n / 2 = n * (n - 1) / 2 + n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  obtain ⟨k, hk⟩ := Nat.even_mul_succ_self m
  rw [mul_comm m] at hk
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  rw [show (m + 1 + 1) * (m + 1) = (m + 1) * m + 2 * (m + 1) by ring, hk]
  lia

private lemma resultant_X_sub_C_add_mul_derivative (hdeg : 0 < g.natDegree) (x : R) :
    (X - C x).resultant (g + (X - C x) * derivative g) 1 g.natDegree = g.eval x := by
  have hd' : (derivative g).natDegree + 1 ≤ g.natDegree := by
    have := natDegree_derivative_le g; lia
  rw [resultant_add_mul_right _ _ _ _ _ hd' (natDegree_X_sub_C_le x),
    resultant_X_sub_C_left _ _ _ le_rfl]

private lemma resultant_add_mul_derivative [Nontrivial R] (hg : g.Monic)
    (hdeg : 0 < g.natDegree) (x : R) :
    g.resultant (g + (X - C x) * derivative g) g.natDegree g.natDegree =
      (-1) ^ g.natDegree * g.eval x *
        g.resultant (derivative g) g.natDegree (g.natDegree - 1) := by
  have hd' : (derivative g).natDegree + 1 ≤ g.natDegree := by
    have := natDegree_derivative_le g; lia
  rw [show g + (X - C x) * derivative g = (X - C x) * derivative g + g * 1 by ring,
    resultant_add_mul_right _ _ _ _ _ (by simp) le_rfl,
    hg.resultant_congr_right natDegree_mul_le (by rw [natDegree_X_sub_C]; lia),
    resultant_mul_right g (X - C x) (derivative g) g.natDegree le_rfl, natDegree_X_sub_C,
    resultant_X_sub_C_right _ _ _ le_rfl,
    ← hg.resultant_congr_right (n₂ := g.natDegree - 1) le_rfl (natDegree_derivative_le g)]

/-- The discriminant of `(X - C x) * g` for monic `g` of positive degree is
`g.discr * g.eval x ^ 2`. -/
theorem discr_X_sub_C_mul (hg : g.Monic) (hdeg : 0 < g.natDegree) (x : R) :
    ((X - C x) * g).discr = g.discr * g.eval x ^ 2 := by
  nontriviality R
  have hmon : ((X - C x) * g).Monic := (monic_X_sub_C x).mul hg
  have hN : ((X - C x) * g).natDegree = g.natDegree + 1 := by
    rw [(monic_X_sub_C x).natDegree_mul hg, natDegree_X_sub_C, add_comm]
  have hder : derivative ((X - C x) * g) = g + (X - C x) * derivative g := by
    rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul]
  have hDle : (g + (X - C x) * derivative g).natDegree ≤ g.natDegree :=
    (natDegree_add_le _ _).trans (max_le le_rfl (natDegree_mul_le.trans
      (by rw [natDegree_X_sub_C]; have := natDegree_derivative_le g; lia)))
  -- compare the splitting of `Res((X - C x) * g, ((X - C x) * g)')` along the product with
  -- its expression through the discriminant
  have hsplit := resultant_mul_left (X - C x) g (g + (X - C x) * derivative g) g.natDegree hDle
  rw [natDegree_X_sub_C, add_comm 1 g.natDegree] at hsplit
  have hres := resultant_deriv (f := (X - C x) * g)
    (by rw [← natDegree_pos_iff_degree_pos, hN]; lia)
  rw [hN, hder, hmon.leadingCoeff, mul_one, Nat.add_sub_cancel, succ_mul_div_two hdeg,
    pow_add] at hres
  have hres2 := resultant_deriv (f := g) (natDegree_pos_iff_degree_pos.mp hdeg)
  rw [hg.leadingCoeff, mul_one] at hres2
  have hmain := hres.symm.trans hsplit
  rw [resultant_X_sub_C_add_mul_derivative hdeg x, resultant_add_mul_derivative hg hdeg x,
    hres2] at hmain
  -- now peel off the signs, which cancel
  have hpow (k : ℕ) : ((-1 : R) ^ k) * ((-1) ^ k) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  set s : R := (-1) ^ (g.natDegree * (g.natDegree - 1) / 2)
  set t : R := (-1) ^ g.natDegree
  have hs : s * s = 1 := hpow _
  have ht : t * t = 1 := hpow _
  calc ((X - C x) * g).discr
      = s * t * (s * t * ((X - C x) * g).discr) := by
        rw [← mul_assoc, mul_mul_mul_comm, hs, ht, one_mul, one_mul]
    _ = s * t * (g.eval x * (t * g.eval x * (s * g.discr))) := by rw [hmain]
    _ = s * s * (t * t) * (g.discr * g.eval x ^ 2) := by ring
    _ = g.discr * g.eval x ^ 2 := by rw [hs, ht, one_mul, one_mul]

lemma mem_degreeLT_natDegree_iff {q : R[X]} (hg : g ≠ 0) :
    q ∈ degreeLT R g.natDegree ↔ q.degree < g.degree := by
  rw [mem_degreeLT, degree_eq_natDegree hg]

/-- A monic real polynomial that is irreducible of degree `2` is positive definite: being
irreducible of degree `> 1` it has no real root, and its leading coefficient is `1 > 0`. -/
theorem eval_pos_of_monic_of_irreducible_of_natDegree_eq_two {q : ℝ[X]}
    (hm : q.Monic) (hirr : Irreducible q) (hd : q.natDegree = 2) (x : ℝ) : 0 < q.eval x :=
  zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
    (fun y hy ↦ absurd hy (hirr.not_isRoot_of_natDegree_ne_one (by lia)))
    (hm.leadingCoeff ▸ zero_le_one)

section

variable [Nontrivial R] {q : R[X]} {n : ℕ}

lemma exists_eq_C_mul_X_sub_C_of_natDegree_le_one {p : R[X]} (hdeg : p.natDegree ≤ 1)
    {x : R} (hx : p.IsRoot x) :
    ∃ γ, p = C γ * (X - C x) := by
  obtain ⟨q, rfl⟩ := dvd_iff_isRoot.mpr hx
  rcases eq_or_ne q 0 with rfl | hq
  · exact ⟨0, by simp⟩
  have h1 : (X - C x).leadingCoeff * q.leadingCoeff ≠ 0 := by
    rwa [(monic_X_sub_C x).leadingCoeff, one_mul, leadingCoeff_ne_zero]
  rw [natDegree_mul' h1, natDegree_X_sub_C] at hdeg
  refine ⟨q.coeff 0, ?_⟩
  nth_rw 1 [eq_C_of_natDegree_eq_zero (by lia : q.natDegree = 0), mul_comm]

lemma modByMonic_mem_degreeLT (hg : g.Monic) (q : R[X]) :
    q %ₘ g ∈ degreeLT R g.natDegree :=
  (mem_degreeLT_natDegree_iff hg.ne_zero).mpr <| degree_modByMonic_lt q hg

lemma divByMonic_mem_degreeLT (hg : g.Monic)
    (hq : q ∈ degreeLT R (g.natDegree + n)) : q /ₘ g ∈ degreeLT R n := by
  rw [mem_degreeLT] at hq ⊢
  rcases eq_or_ne (q /ₘ g) 0 with h | h
  · simp [h]
  have hq0 : q ≠ 0 := fun h0 ↦ h (by simp [h0])
  rw [← natDegree_lt_iff_degree_lt h, natDegree_divByMonic q hg]
  refine Nat.sub_lt_left_of_lt_add ?_ <| (natDegree_lt_iff_degree_lt hq0).mpr hq
  by_contra! hcon
  exact h <| (divByMonic_eq_zero_iff hg).mpr <| degree_lt_degree hcon

lemma eq_zero_of_monic_dvd_of_degree_lt (hg : g.Monic) (hdvd : g ∣ q)
    (hq : q.degree < g.degree) : q = 0 :=
  ((modByMonic_eq_self_iff hg).mpr hq).symm.trans <| (modByMonic_eq_zero_iff_dvd hg).mpr hdvd

private lemma Monic.divMod_mul_add (hg : g.Monic) (v u : R[X]) :
    (g * v + u) /ₘ g = v + u /ₘ g ∧ (g * v + u) %ₘ g = u %ₘ g := by
  refine div_modByMonic_unique _ _ hg ⟨?_, degree_modByMonic_lt u hg⟩
  conv_rhs => rw [← modByMonic_add_div u g]
  ring

lemma Monic.divByMonic_mul_add (hg : g.Monic) (v u : R[X]) :
    (g * v + u) /ₘ g = v + u /ₘ g :=
  (hg.divMod_mul_add v u).1

lemma Monic.modByMonic_mul_add (hg : g.Monic) (v u : R[X]) :
    (g * v + u) %ₘ g = u %ₘ g :=
  (hg.divMod_mul_add v u).2

end

section Sylvester

open Module LinearMap LinearEquiv

variable [Nontrivial R] {p : R[X]} {n : ℕ}

/-!
### The norm on `AdjoinRoot g` is the resultant

Write `m = g.natDegree` and `n = p.natDegree`. The Sylvester map
`S : R[X]_m × R[X]_n →ₗ R[X]_(m+n)`, `(u, v) ↦ g * v + p * u`, has the Sylvester matrix as its
matrix, so `det S = resultant g p m n`.

Taking `p = 1` gives a map `Ψ : (u, v) ↦ g * v + u`, which is a linear *equivalence* when `g` is
monic (its inverse is `q ↦ (q %ₘ g, q /ₘ g)`), and `det Ψ = resultant g 1 m n = 1`.

Now `S = Ψ ∘ₗ B` where `B := Ψ⁻¹ ∘ₗ S` is the endomorphism
`(u, v) ↦ ((p * u) %ₘ g, v + (p * u) /ₘ g)` of `R[X]_m × R[X]_n`, by `modByMonic_add_div`.
In the block decomposition the matrix of `B` is lower triangular with diagonal blocks
`mulModByMonic hg p` and `1`, so `det B = det (mulModByMonic hg p)`.

Finally `mk g : R[X]_m ≃ₗ AdjoinRoot g` conjugates `mulModByMonic hg p` into multiplication by
`mk g p`, whose determinant is by definition `Algebra.norm R (mk g p)`.

No signs appear anywhere: `B` is an endomorphism, so the two blocks are never reordered.
-/

/-- Multiplication by `p` on `R[X]_(g.natDegree)`, that is, `q ↦ (p * q) %ₘ g`. This is the
map that `mk g : R[X]_(g.natDegree) ≃ₗ AdjoinRoot g` turns into multiplication by `mk g p`. -/
noncomputable def mulModByMonic (hg : g.Monic) (p : R[X]) :
    degreeLT R g.natDegree →ₗ[R] degreeLT R g.natDegree where
  toFun q := ⟨p * (q : R[X]) %ₘ g, modByMonic_mem_degreeLT hg _⟩
  map_add' q₁ q₂ := by ext1; simp [mul_add, add_modByMonic]
  map_smul' c q := by ext1; simp [smul_modByMonic]

@[simp]
lemma mulModByMonic_apply_coe (hg : g.Monic) (p : R[X])
    (q : degreeLT R g.natDegree) : (mulModByMonic hg p q : R[X]) = p * (q : R[X]) %ₘ g :=
  rfl

/-- For monic `g`, the Sylvester map of `g` and `1`, namely `(u, v) ↦ g * v + u`, is a linear
equivalence `R[X]_(g.natDegree) × R[X]_n ≃ₗ R[X]_(g.natDegree + n)`. Its inverse is
`q ↦ (q %ₘ g, q /ₘ g)`. -/
noncomputable def sylvesterEquivOne (hg : g.Monic) (n : ℕ) :
    (degreeLT R g.natDegree × degreeLT R n) ≃ₗ[R] degreeLT R (g.natDegree + n) :=
  ofBijective (sylvesterMap g 1 le_rfl (by simp)) <| by
    constructor
    · intro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ ⟨⟨u', hu'⟩, ⟨v', hv'⟩⟩ h
      replace h : g * v + u = g * v' + u' := by simpa using congrArg Subtype.val h
      rw [mem_degreeLT_natDegree_iff hg.ne_zero] at hu hu'
      have hmod {w : R[X]} (hw : w.degree < g.degree) : w %ₘ g = w :=
        (modByMonic_eq_self_iff hg).mpr hw
      have hdiv {w : R[X]} (hw : w.degree < g.degree) : w /ₘ g = 0 :=
        (divByMonic_eq_zero_iff hg).mpr hw
      have h₁ : u = u' := by
        rw [← hmod hu, ← hmod hu', ← hg.modByMonic_mul_add v u, ← hg.modByMonic_mul_add v' u', h]
      have h₂ : v = v' := by
        have := congrArg (· /ₘ g) h
        simpa [hg.divByMonic_mul_add, hdiv hu, hdiv hu'] using this
      simp only [Prod.mk.injEq, Subtype.mk.injEq]
      exact ⟨h₁, h₂⟩
    · intro ⟨q, hq⟩
      refine ⟨(⟨q %ₘ g, modByMonic_mem_degreeLT hg q⟩,
        ⟨q /ₘ g, divByMonic_mem_degreeLT hg hq⟩), ?_⟩
      ext1
      simpa [add_comm] using modByMonic_add_div q g

@[simp]
lemma coe_sylvesterEquivOne (hg : g.Monic) (n : ℕ) :
    (sylvesterEquivOne hg n).toLinearMap = sylvesterMap g 1 le_rfl (by simp) :=
  rfl

/-- The inverse of `Ψ` is division with remainder by `g`. -/
lemma coe_sylvesterEquivOne_symm (hg : g.Monic) (n : ℕ)
    (q : degreeLT R (g.natDegree + n)) :
    ((((sylvesterEquivOne hg n).symm q).1 : R[X]) = (q : R[X]) %ₘ g) ∧
      ((((sylvesterEquivOne hg n).symm q).2 : R[X]) = (q : R[X]) /ₘ g) := by
  obtain ⟨w, rfl⟩ : ∃ w, q = sylvesterEquivOne hg n w :=
    ⟨_, ((sylvesterEquivOne hg n).apply_symm_apply q).symm⟩
  have hq : ((sylvesterEquivOne hg n w : degreeLT R (g.natDegree + n)) : R[X]) =
      g * (w.2 : R[X]) + (w.1 : R[X]) := by
    simp [sylvesterEquivOne]
  have h : (w.1 : R[X]).degree < g.degree := (mem_degreeLT_natDegree_iff hg.ne_zero).mp w.1.2
  rw [symm_apply_apply, hq]
  refine ⟨?_, ?_⟩
  · rw [hg.modByMonic_mul_add, (modByMonic_eq_self_iff hg).mpr h]
  · rw [hg.divByMonic_mul_add, (divByMonic_eq_zero_iff hg).mpr h, add_zero]

/-- The block-triangular endomorphism `B = Ψ⁻¹ ∘ₗ S` of `R[X]_(g.natDegree) × R[X]_n`. -/
noncomputable def sylvesterBlock (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n) :
    degreeLT R g.natDegree × degreeLT R n →ₗ[R] degreeLT R g.natDegree × degreeLT R n :=
  (sylvesterEquivOne hg n).symm.toLinearMap ∘ₗ sylvesterMap g p le_rfl hp

/-- The first coordinate of `B (u, v)` is `(p * u) %ₘ g`. -/
lemma coe_sylvesterBlock_apply_fst (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n)
    (u : degreeLT R g.natDegree) (v : degreeLT R n) :
    ((sylvesterBlock hg p hp (u, v)).1 : R[X]) = p * (u : R[X]) %ₘ g := by
  rw [sylvesterBlock, comp_apply, LinearEquiv.coe_coe,
    (coe_sylvesterEquivOne_symm hg n _).1, sylvesterMap_apply_coe, hg.modByMonic_mul_add]

/-- The second coordinate of `B (u, v)` is `v + (p * u) /ₘ g`. -/
lemma coe_sylvesterBlock_apply_snd (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n)
    (u : degreeLT R g.natDegree) (v : degreeLT R n) :
    ((sylvesterBlock hg p hp (u, v)).2 : R[X]) = (v : R[X]) + p * (u : R[X]) /ₘ g := by
  rw [sylvesterBlock, comp_apply, LinearEquiv.coe_coe,
    (coe_sylvesterEquivOne_symm hg n _).2, sylvesterMap_apply_coe, hg.divByMonic_mul_add]

open Matrix in
/-- The determinant of the block-triangular map `B` is the determinant of its upper-left block. -/
lemma det_sylvesterBlock (hg : g.Monic) (p : R[X]) (hp : p.natDegree ≤ n) :
    LinearMap.det (sylvesterBlock hg p hp) = LinearMap.det (mulModByMonic hg p) := by
  set bm := degreeLT.basis R g.natDegree
  set bn := degreeLT.basis R n
  have hinl j : (bm.prod bn) (Sum.inl j) = (bm j, 0) :=
    Prod.ext (Basis.prod_apply_inl_fst ..) (Basis.prod_apply_inl_snd ..)
  have hinr j : (bm.prod bn) (Sum.inr j) = (0, bn j) :=
    Prod.ext (Basis.prod_apply_inr_fst ..) (Basis.prod_apply_inr_snd ..)
  -- the upper-left block is `mulModByMonic hg p`, and `B` fixes `{0} × R[X]_n` pointwise
  have hfst u : (sylvesterBlock hg p hp (u, 0)).1 = mulModByMonic hg p u :=
    Subtype.ext <| by rw [coe_sylvesterBlock_apply_fst, mulModByMonic_apply_coe]
  have hz (v : degreeLT R n) :
      sylvesterBlock hg p hp ((0 : degreeLT R g.natDegree), v) = (0, v) :=
    Prod.ext (Subtype.ext <| by simp [coe_sylvesterBlock_apply_fst])
      (Subtype.ext <| by simp [coe_sylvesterBlock_apply_snd])
  rw [← det_toMatrix (bm.prod bn), ← det_toMatrix bm]
  have hmat : toMatrix (bm.prod bn) (bm.prod bn) (sylvesterBlock hg p hp) =
      fromBlocks (toMatrix bm bm (mulModByMonic hg p)) 0
        (.of fun i j ↦ bn.repr (sylvesterBlock hg p hp (bm j, 0)).2 i) 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rw [toMatrix_apply, hinl, Basis.prod_repr_inl, fromBlocks_apply₁₁, toMatrix_apply, hfst]
    · rw [toMatrix_apply, hinr, hz, Basis.prod_repr_inl, fromBlocks_apply₁₂]
      simp
    · rw [toMatrix_apply, hinl, Basis.prod_repr_inr, fromBlocks_apply₂₁, of_apply]
    · rw [toMatrix_apply, hinr, hz, Basis.prod_repr_inr, fromBlocks_apply₂₂,
        Basis.repr_self, one_apply, Finsupp.single_apply]
      exact if_congr eq_comm rfl rfl
  rw [hmat, det_fromBlocks_zero₁₂, det_one, mul_one]

end Sylvester

/-- To show that a monic polynomial over an integrally closed domain is irreducible over its
fraction field, it suffices to exhibit an irreducible image under some ring homomorphism to a
domain, e.g. reduction modulo a prime. -/
theorem Monic.irreducible_map_fraction_map_of_irreducible_map [IsIntegrallyClosed R]
    [IsDomain R] {S K : Type*} [CommRing S] [IsDomain S] [Field K] [Algebra R K]
    [IsFractionRing R K] (hg : g.Monic) (φ : R →+* S) (h : Irreducible (g.map φ)) :
    Irreducible (g.map (algebraMap R K)) :=
  (hg.irreducible_iff_irreducible_map_fraction_map (K := K)).mp
    (hg.irreducible_of_irreducible_map φ _ h)

end Polynomial

open Polynomial LinearMap LinearEquiv

namespace AdjoinRoot

variable {R : Type*} [CommRing R] {g : R[X]} {n : ℕ}

@[simp]
lemma mk_modByMonic (hg : g.Monic) (q : R[X]) : mk g (q %ₘ g) = mk g q := by
  simpa using mk_leftInverse hg (mk g q)

lemma exists_degree_lt_mk_eq [Nontrivial R] (hg : g.Monic) (a : AdjoinRoot g) :
    ∃ p, p.degree < g.degree ∧ a = mk g p := by
  obtain ⟨q, rfl⟩ := mk_surjective a
  exact ⟨q %ₘ g, degree_modByMonic_lt q hg, (mk_modByMonic hg q).symm⟩

lemma mk_eq_mk_iff_of_degree_lt [Nontrivial R] (hg : g.Monic) {p q : R[X]}
    (hp : p.degree < g.degree) (hq : q.degree < g.degree) :
    mk g p = mk g q ↔ p = q :=
  ⟨fun h ↦ sub_eq_zero.mp <| eq_zero_of_monic_dvd_of_degree_lt hg (mk_eq_mk.mp h) <|
    (degree_sub_le p q).trans_lt (max_lt hp hq), fun h ↦ h ▸ rfl⟩

/-- `mk g` is a linear equivalence from the polynomials of degree `< g.natDegree` onto
`AdjoinRoot g`, for `g` monic. -/
noncomputable def degreeLTEquiv [Nontrivial R] (hg : g.Monic) :
    degreeLT R g.natDegree ≃ₗ[R] AdjoinRoot g :=
  ofBijective ((mkₐ g).toLinearMap ∘ₗ (degreeLT R g.natDegree).subtype) <| by
    constructor
    · intro ⟨q, hq⟩ ⟨q', hq'⟩ h
      replace h : mk g q = mk g q' := h
      rw [mk_eq_mk] at h
      rw [mem_degreeLT_natDegree_iff hg.ne_zero] at hq hq'
      refine Subtype.ext (sub_eq_zero.mp <| eq_zero_of_monic_dvd_of_degree_lt hg h ?_)
      exact (degree_sub_le q q').trans_lt (max_lt hq hq')
    · intro a
      obtain ⟨q, rfl⟩ := mk_surjective a
      exact ⟨⟨q %ₘ g, modByMonic_mem_degreeLT hg q⟩, mk_modByMonic hg q⟩

@[simp]
lemma degreeLTEquiv_apply [Nontrivial R] (hg : g.Monic)
    (q : degreeLT R g.natDegree) :
    degreeLTEquiv hg q = mk g (q : R[X]) :=
  rfl

/-- For a monic irreducible quadratic `q : ℝ[X]`, the field `ℝ[X]/(q)` is `ℂ`: it is a degree-`2`
(hence not `ℝ`) algebraic extension of `ℝ`, and every such extension is `ℝ` or `ℂ`. -/
theorem nonempty_algEquiv_complex {q : ℝ[X]} (hm : q.Monic) (hirr : Irreducible q)
    (hd : q.natDegree = 2) : Nonempty (AdjoinRoot q ≃ₐ[ℝ] ℂ) := by
  have : Fact (Irreducible q) := ⟨hirr⟩
  have : FiniteDimensional ℝ (AdjoinRoot q) := (powerBasis' hm).finite
  refine (Real.nonempty_algEquiv_or (AdjoinRoot q)).resolve_left fun ⟨e⟩ ↦
    absurd e.toLinearEquiv.finrank_eq (by
      rw [Module.finrank_self, (powerBasis' hm).finrank, powerBasis'_dim, hd]
      norm_num)

/-- The norm of `mk g p` is the determinant of multiplication by `p` on `R[X]_(g.natDegree)`,
because `degreeLTEquiv hg` conjugates the latter into multiplication by `mk g p`. -/
lemma norm_mk_eq_det_mulModByMonic [Nontrivial R] (hg : g.Monic) (p : R[X]) :
    Algebra.norm R (mk g p) = LinearMap.det (mulModByMonic hg p) := by
  rw [Algebra.norm_apply, ← det_conj (mulModByMonic hg p) (degreeLTEquiv hg)]
  congr 1
  refine ext fun a ↦ ?_
  obtain ⟨q, rfl⟩ := (degreeLTEquiv hg).surjective a
  simp only [comp_apply, LinearEquiv.coe_coe, symm_apply_apply]
  simp only [degreeLTEquiv_apply, mulModByMonic_apply_coe, Algebra.coe_lmul_eq_mul,
    mul_apply']
  rw [mk_modByMonic hg, map_mul]

/-- The norm of `AdjoinRoot.mk g p` over the base ring, for `g` monic, is the resultant of `g`
and `p`. Equivalently, it is the product of the values of `p` at the roots of `g`. -/
lemma norm_mk_eq_resultant [Nontrivial R] (hg : g.Monic) (p : R[X]) :
    Algebra.norm R (mk g p) = g.resultant p g.natDegree p.natDegree := by
  set m := g.natDegree
  set k := p.natDegree
  set b₁ := ((degreeLT.basis R m).prod (degreeLT.basis R k)).reindex finSumFinEquiv
  set b₂ := degreeLT.basis R (m + k)
  have hΨ : (sylvesterMap g 1 le_rfl (by simp)) ∘ₗ sylvesterBlock hg p le_rfl =
      sylvesterMap g p le_rfl le_rfl := by
    rw [sylvesterBlock, ← LinearMap.comp_assoc, ← coe_sylvesterEquivOne hg k, comp_coe,
      symm_trans_self, refl_toLinearMap, id_comp]
  have key : (sylvesterMap g p le_rfl le_rfl).toMatrix b₁ b₂ =
      (sylvesterMap g 1 le_rfl (by simp)).toMatrix b₁ b₂ *
        (sylvesterBlock hg p le_rfl).toMatrix b₁ b₁ := by
    rw [← toMatrix_comp b₁ b₁ b₂, hΨ]
  rw [norm_mk_eq_det_mulModByMonic hg, ← det_sylvesterBlock hg p le_rfl,
    ← det_toMatrix b₁, resultant, ← toMatrix_sylvesterMap' g p le_rfl le_rfl, key,
    Matrix.det_mul, toMatrix_sylvesterMap' g 1 le_rfl (by simp), ← resultant,
    hg.resultant_one_right, one_mul]

/-- The root of `h = g.map φ` in `S[X]/(h)`, for `g` monic over `R`, is integral over `R`
(along the composite of `φ` with the canonical map). -/
theorem isIntegralElem_root_of_map {S : Type*} [CommRing S] (φ : R →+* S) {h : S[X]}
    (hg : g.Monic) (hmap : g.map φ = h) :
    ((algebraMap S (AdjoinRoot h)).comp φ).IsIntegralElem (root h) :=
  ⟨g, hg, by rw [← eval₂_map, hmap, ← aeval_def, aeval_eq, mk_self]⟩

section Map

variable {S : Type*} [CommRing S] (σ : R →+* S)

/-- Evaluation of `AdjoinRoot.map` on the class of a polynomial (the companion of Mathlib's
`AdjoinRoot.map_of` and `AdjoinRoot.map_root`). -/
@[simp]
lemma map_mk {p : R[X]} {q : S[X]} (hq : q ∣ p.map σ) (g : R[X]) :
    AdjoinRoot.map σ p q hq (mk p g) = mk q (g.map σ) := by
  rw [AdjoinRoot.map, lift_mk, ← Polynomial.eval₂_map, ← algebraMap_eq, ← Polynomial.aeval_def,
    aeval_eq]

end Map

end AdjoinRoot

/-- The base-change map `K[X]/(p) →+* K_v[X]/(q)` of `AdjoinRoot`s at a completion is
compatible with the algebra maps from the underlying Dedekind domain `R` and from the ring of
integers of the completion. -/
lemma AdjoinRoot.map_comp_algebraMap {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (v : IsDedekindDomain.HeightOneSpectrum R) {p : K[X]} {q : (v.adicCompletion K)[X]}
    (hq : q ∣ p.map (algebraMap K (v.adicCompletion K))) :
    (AdjoinRoot.map (algebraMap K (v.adicCompletion K)) p q hq).comp
        (algebraMap R (AdjoinRoot p)) =
      (algebraMap (v.adicCompletionIntegers K) (AdjoinRoot q)).comp
        (algebraMap R (v.adicCompletionIntegers K)) := by
  ext c
  simp only [RingHom.comp_apply]
  rw [IsScalarTower.algebraMap_apply R K (AdjoinRoot p), AdjoinRoot.algebraMap_eq, map_of,
    IsScalarTower.algebraMap_apply (v.adicCompletionIntegers K) (v.adicCompletion K)
      (AdjoinRoot q), AdjoinRoot.algebraMap_eq]
  rfl

/-! ### The norm on a product algebra -/

/-- The `R`-norm on a product algebra is the product of the norms. -/
theorem Algebra.norm_prod {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [Module.Free R A] [Module.Finite R A] [Module.Free R B] [Module.Finite R B]
    (x : A × B) : Algebra.norm R x = Algebra.norm R x.1 * Algebra.norm R x.2 := by
  have h : Algebra.lmul R (A × B) x = ((Algebra.lmul R A x.1).prodMap (Algebra.lmul R B x.2)) := by
    ext <;> simp
  rw [Algebra.norm_apply, Algebra.norm_apply, Algebra.norm_apply, h, LinearMap.det_prodMap]

/-- The `R`-norm on a finite product of `R`-algebras is the product of the norms. -/
theorem Algebra.norm_pi {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {S : ι → Type*}
    [(i : ι) → CommRing (S i)] [(i : ι) → Algebra R (S i)]
    [(i : ι) → Module.Free R (S i)] [(i : ι) → Module.Finite R (S i)]
    (g : (i : ι) → S i) :
    Algebra.norm R g = ∏ i, Algebra.norm R (g i) := by
  have h : Algebra.lmul R ((i : ι) → S i) g
      = LinearMap.pi fun i ↦ (Algebra.lmul R (S i) (g i)).comp (LinearMap.proj i) := by
    ext x j
    simp [Algebra.lmul]
  rw [Algebra.norm_apply, h, LinearMap.det_pi']
  simp_rw [← Algebra.norm_apply]

section EtaleDecomposition

/-!
### Decomposition of `K[X]/(f)` into a product of fields

For a nonzero squarefree `f` over a field `K`, the étale algebra `AdjoinRoot f` is the product
of the fields `AdjoinRoot p`, where `p` runs over the distinct irreducible factors of `f`.
This is what lets one talk about the primes, and hence the Selmer group, of `AdjoinRoot f`:
they are those of the factors.

If moreover `f` is separable, each factor is separable, so each `AdjoinRoot p` is a finite
separable extension of `K` and its integral closure over a Dedekind domain is again Dedekind.
-/

open Polynomial UniqueFactorizationMonoid

namespace Polynomial

variable {K : Type*} [Field K] {f : K[X]}

/-- The distinct monic irreducible factors of `f`, as an index type.

Note that this is *not* defined via `normalizedFactors` (which would require `DecidableEq K`);
membership in `normalizedFactors f` is characterized by `Factors.mem_normalizedFactors_iff`. -/
abbrev Factors (f : K[X]) : Type _ := {p : K[X] // p.Monic ∧ Irreducible p ∧ p ∣ f}

namespace Factors

lemma monic (p : f.Factors) : (p : K[X]).Monic := p.2.1

lemma irreducible (p : f.Factors) : Irreducible (p : K[X]) := p.2.2.1

lemma dvd (p : f.Factors) : (p : K[X]) ∣ f := p.2.2.2

/-- If `f` itself is monic and irreducible, then its only factor is `f`. -/
lemma coe_eq (hf : Irreducible f) (hmon : f.Monic) (p : f.Factors) : (p : K[X]) = f :=
  Polynomial.eq_of_monic_of_associated p.monic hmon (p.irreducible.associated_of_dvd hf p.dvd)

/-- A monic irreducible polynomial has itself as its only monic irreducible factor. -/
@[reducible]
def unique (hf : Irreducible f) (hmon : f.Monic) : Unique f.Factors where
  default := ⟨f, hmon, hf, dvd_rfl⟩
  uniq p := Subtype.ext (coe_eq hf hmon p)

lemma ne_zero (p : f.Factors) : (p : K[X]) ≠ 0 := p.irreducible.ne_zero

lemma prime (p : f.Factors) : Prime (p : K[X]) := p.irreducible.prime

lemma separable (hf : f.Separable) (p : f.Factors) : (p : K[X]).Separable :=
  hf.of_dvd p.dvd

/-- Membership in `normalizedFactors` (with its normalization from `DecidableEq K`) is
equivalent to being a monic irreducible factor. -/
lemma mem_normalizedFactors_iff [DecidableEq K] (hf : f ≠ 0) {p : K[X]} :
    p ∈ normalizedFactors f ↔ p.Monic ∧ Irreducible p ∧ p ∣ f := by
  rw [UniqueFactorizationMonoid.mem_normalizedFactors_iff' hf]
  exact ⟨fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₂ ▸ monic_normalize h₁.ne_zero, h₁, h₃⟩,
    fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₂, h₁.normalize_eq_self, h₃⟩⟩

lemma finite (hf : f ≠ 0) : Finite f.Factors := by
  classical
  have h : Finite {p : K[X] // p ∈ normalizedFactors f} :=
    (normalizedFactors f).finite_toSet.to_subtype
  exact .of_injective _
    (Subtype.impEmbedding _ (· ∈ normalizedFactors f)
      fun p hp ↦ (mem_normalizedFactors_iff hf).mpr hp).injective

lemma nonempty (hu : ¬ IsUnit f) : Nonempty f.Factors :=
  let ⟨p, hp⟩ := f.exists_monic_irreducible_factor hu
  ⟨⟨p, hp⟩⟩

/-- The monic linear factors of `f` correspond to the roots of `f`. -/
noncomputable def linearEquivRoots :
    {p : f.Factors // (p : K[X]).natDegree = 1} ≃ {x : K // f.eval x = 0} where
  toFun p := ⟨-((p : f.Factors) : K[X]).coeff 0,
    eval_eq_zero_of_dvd_of_eval_eq_zero (p : f.Factors).dvd <| by
      conv_lhs => rw [(p : f.Factors).monic.eq_X_add_C p.2]
      simp⟩
  invFun x := ⟨⟨X - C (x : K), monic_X_sub_C _, irreducible_X_sub_C _,
    dvd_iff_isRoot.mpr x.2⟩, natDegree_X_sub_C _⟩
  left_inv p := by
    refine Subtype.ext (Subtype.ext ?_)
    change X - C (-((p : f.Factors) : K[X]).coeff 0) = _
    conv_rhs => rw [(p : f.Factors).monic.eq_X_add_C p.2]
    rw [map_neg, sub_neg_eq_add]
  right_inv x := by
    refine Subtype.ext ?_
    change -(X - C (x : K)).coeff 0 = _
    simp

lemma isCoprime {p q : f.Factors} (hne : p ≠ q) : IsCoprime (p : K[X]) (q : K[X]) :=
  (Ideal.isCoprime_span_singleton_iff _ _).mp <| Ideal.isCoprime_iff_sup_eq.mpr <|
    Ideal.IsMaximal.coprime_of_ne
      (PrincipalIdealRing.isMaximal_of_irreducible p.irreducible)
      (PrincipalIdealRing.isMaximal_of_irreducible q.irreducible)
      fun h ↦ hne <| Subtype.ext <| eq_of_monic_of_associated p.monic q.monic <|
        Ideal.span_singleton_eq_span_singleton.mp h

lemma isCoprime_span {p q : f.Factors} (hne : p ≠ q) :
    IsCoprime (Ideal.span {(p : K[X])}) (Ideal.span {(q : K[X])}) :=
  (Ideal.isCoprime_span_singleton_iff _ _).mpr (isCoprime hne)

lemma associated_prod [Fintype f.Factors] (hf : f ≠ 0) (hsq : Squarefree f) :
    Associated (∏ p : f.Factors, (p : K[X])) f := by
  classical
  -- identify `f.Factors` with the subtype of the `Finset` of normalized factors
  have hprod : ∏ p : f.Factors, (p : K[X]) =
      ∏ p : {p : K[X] // p ∈ (normalizedFactors f).toFinset}, (p : K[X]) :=
    Fintype.prod_equiv (Equiv.subtypeEquivRight fun p ↦ by
        rw [Multiset.mem_toFinset, mem_normalizedFactors_iff hf]) _ _
      fun x ↦ by rw [Equiv.subtypeEquivRight_apply]
  have hcoe : ∏ p : {p : K[X] // p ∈ (normalizedFactors f).toFinset}, (p : K[X]) =
      ∏ p ∈ (normalizedFactors f).toFinset, p :=
    Finset.prod_coe_sort _ fun x ↦ x
  rw [hprod, hcoe, Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
    Multiset.dedup_eq_self.mpr ((squarefree_iff_nodup_normalizedFactors hf).mp hsq),
    Multiset.map_id']
  exact prod_normalizedFactors hf

/-- The degrees of the distinct monic irreducible factors of `f ≠ 0` sum to at most the
degree of `f` (with equality iff `f` is squarefree, up to normalization). -/
lemma sum_natDegree_le [Fintype f.Factors] (hf : f ≠ 0) :
    ∑ p : f.Factors, (p : K[X]).natDegree ≤ f.natDegree := by
  rw [← natDegree_prod _ _ fun p _ ↦ p.ne_zero]
  exact natDegree_le_of_dvd
    (Fintype.prod_dvd_of_coprime (fun p q hpq ↦ isCoprime hpq) fun p ↦ p.dvd) hf

lemma span_eq_iInf_span (hf : f ≠ 0) (hsq : Squarefree f) :
    Ideal.span {f} = ⨅ p : f.Factors, Ideal.span {(p : K[X])} := by
  have : Fintype f.Factors := @Fintype.ofFinite _ (finite hf)
  rw [Ideal.iInf_span_singleton fun _ _ hpq ↦ isCoprime hpq]
  exact (Ideal.span_singleton_eq_span_singleton.mpr (associated_prod hf hsq)).symm

/-- An irreducible factor of the image of `f` under a field embedding divides the image of
one of the irreducible factors of `f`. -/
lemma exists_dvd_map {L : Type*} [Field L] (σ : K →+* L) (hf : f ≠ 0)
    {q : L[X]} (hq : Prime q) (hdvd : q ∣ f.map σ) :
    ∃ p : f.Factors, q ∣ (p : K[X]).map σ := by
  classical
  have h1 : Associated ((normalizedFactors f).map (Polynomial.map σ)).prod (f.map σ) := by
    have h2 := (prod_normalizedFactors hf).map (mapRingHom σ)
    rwa [map_multiset_prod, coe_mapRingHom] at h2
  obtain ⟨g, hgmem, hgdvd⟩ := hq.exists_mem_multiset_dvd (hdvd.trans h1.symm.dvd)
  obtain ⟨p₀, hp₀, rfl⟩ := Multiset.mem_map.mp hgmem
  exact ⟨⟨p₀, (mem_normalizedFactors_iff hf).mp hp₀⟩, hgdvd⟩

end Factors

end Polynomial

namespace AdjoinRoot

variable {K : Type*} [Field K] {f : K[X]}

instance instFactIrreducible (p : f.Factors) : Fact (Irreducible (p : K[X])) := ⟨p.irreducible⟩

instance instFiniteDimensional (p : f.Factors) : FiniteDimensional K (AdjoinRoot (p : K[X])) :=
  (powerBasis p.irreducible.ne_zero).finite

instance instNumberField [NumberField K] (p : f.Factors) :
    NumberField (AdjoinRoot (p : K[X])) :=
  .of_module_finite K _

/-- The dimension of `K[X]/(f)` over `K` is the degree of `f`. -/
theorem finrank_eq_natDegree (hf : f ≠ 0) : Module.finrank K (AdjoinRoot f) = f.natDegree := by
  rw [(powerBasis hf).finrank, powerBasis_dim]

lemma minpoly_root_factor (p : f.Factors) : minpoly K (root (p : K[X])) = (p : K[X]) := by
  rw [minpoly_root p.irreducible.ne_zero, p.monic.leadingCoeff, inv_one, map_one, mul_one]

/-- The discriminant of the power basis of `K[X]/(f)`, for `f` monic irreducible with
derivative of the generic degree, is the discriminant of the polynomial `f`. -/
theorem discr_powerBasis_eq_discr [Fact (Irreducible f)] [Algebra.IsSeparable K (AdjoinRoot f)]
    (hf : f.Monic) (hd : f.derivative.natDegree = f.natDegree - 1) :
    Algebra.discr K (powerBasis hf.ne_zero).basis = f.discr := by
  have : Module.Finite K (AdjoinRoot f) := (powerBasis hf.ne_zero).finite
  rw [Algebra.discr_powerBasis_eq_norm, (powerBasis hf.ne_zero).finrank, powerBasis_dim,
    powerBasis_gen, minpoly_root hf.ne_zero, hf.leadingCoeff, inv_one, map_one, mul_one,
    aeval_eq, norm_mk_eq_resultant hf, hd, resultant_deriv (Fact.out : Irreducible f).degree_pos,
    hf.leadingCoeff, mul_one, ← mul_assoc, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_mul]

open IntermediateField in
/-- If `f` is separable, then each field factor of `K[X]/(f)` is a separable extension of `K`.
This is what `IsIntegralClosure.isDedekindDomain` needs. -/
lemma isSeparable_of_separable (hf : f.Separable) (p : f.Factors) :
    Algebra.IsSeparable K (AdjoinRoot (p : K[X])) := by
  have hsep : IsSeparable K (root (p : K[X])) := by
    rw [IsSeparable, minpoly_root_factor p]
    exact p.separable hf
  have htop : K⟮root (p : K[X])⟯ = ⊤ :=
    adjoin_eq_top_of_algebra (F := K) (S := {root (p : K[X])}) adjoinRoot_eq_top
  have h := (isSeparable_adjoin_simple_iff_isSeparable K (AdjoinRoot (p : K[X]))).2 hsep
  rw [htop] at h
  exact (isSeparable_top (F := K) (E := AdjoinRoot (p : K[X]))).mp h

/-- **Chinese Remainder Theorem** for `AdjoinRoot`: for `f` nonzero and squarefree,
`K[X]/(f)` is the product of the fields `K[X]/(p)` over the monic irreducible factors `p`
of `f`. -/
noncomputable def equivPiFactors (hf : f ≠ 0) (hsq : Squarefree f) :
    AdjoinRoot f ≃ₐ[K] ((p : f.Factors) → AdjoinRoot (p : K[X])) :=
  have : Finite f.Factors := Factors.finite hf
  AlgEquiv.ofRingEquiv (f :=
    (Ideal.quotEquivOfEq (Factors.span_eq_iInf_span hf hsq)).trans <|
      Ideal.quotientInfRingEquivPiQuotient _ fun _ _ hpq ↦ Factors.isCoprime_span hpq)
    fun _ ↦ rfl

@[simp]
lemma equivPiFactors_mk (hf : f ≠ 0) (hsq : Squarefree f) (q : K[X]) (p : f.Factors) :
    equivPiFactors hf hsq (mk f q) p = mk (p : K[X]) q :=
  rfl

/-- The projection of `K[X]/(f)` onto the field factor `K[X]/(p)`. -/
noncomputable def projFactor (hf : f ≠ 0) (hsq : Squarefree f) (p : f.Factors) :
    AdjoinRoot f →+* AdjoinRoot (p : K[X]) :=
  (Pi.evalRingHom _ p).comp (equivPiFactors hf hsq).toRingEquiv.toRingHom

@[simp]
lemma projFactor_mk (hf : f ≠ 0) (hsq : Squarefree f) (q : K[X]) (p : f.Factors) :
    projFactor hf hsq p (mk f q) = mk (p : K[X]) q :=
  rfl

/-- The `n`-th power classes of units of `K[X]/(f)` are the product of those of its
field factors. -/
noncomputable def modPowEquivPiFactors (hf : f ≠ 0) (hsq : Squarefree f) (n : ℕ) :
    Units.modPow (AdjoinRoot f) n ≃*
      ((p : f.Factors) → Units.modPow (AdjoinRoot (p : K[X])) n) :=
  (Units.modPow.congr (equivPiFactors hf hsq).toMulEquiv n).trans <|
    Units.modPow.piEquiv (fun p : f.Factors ↦ AdjoinRoot (p : K[X])) n

/-- On the class of a unit, `modPowEquivPiFactors` is componentwise projection to the factors. -/
@[simp]
lemma modPowEquivPiFactors_unit (hf : f ≠ 0) (hsq : Squarefree f) (n : ℕ) {a : AdjoinRoot f}
    (ha : IsUnit a) (p : f.Factors) :
    modPowEquivPiFactors hf hsq n (ha.unit : Units.modPow (AdjoinRoot f) n) p =
      ((ha.map (projFactor hf hsq p)).unit :
        Units.modPow (AdjoinRoot (p : K[X])) n) := by
  simp only [modPowEquivPiFactors, MulEquiv.trans_apply, Units.modPow.congr,
    QuotientGroup.congrRangePowMonoidHom, QuotientGroup.congr_mk, Units.modPow.piEquiv,
    QuotientGroup.mulEquivPiModRangePowMonoidHom_apply]
  exact congrArg _ (Units.ext rfl)

/-- On the class of a unit, `modPowEquivPiFactors` is componentwise projection to the factors
(`Units.map` version of `modPowEquivPiFactors_unit`). -/
@[simp]
lemma modPowEquivPiFactors_mk (hf : f ≠ 0) (hsq : Squarefree f) (n : ℕ)
    (u : (AdjoinRoot f)ˣ) (p : f.Factors) :
    modPowEquivPiFactors hf hsq n (QuotientGroup.mk u) p =
      QuotientGroup.mk (Units.map (projFactor hf hsq p).toMonoidHom u) := by
  have h := modPowEquivPiFactors_unit hf hsq n u.isUnit p
  rw [show u.isUnit.unit = u from Units.ext rfl] at h
  exact h.trans (congrArg QuotientGroup.mk (Units.ext rfl))

/-- The class of a unit of `K[X]/(f)` is trivial exactly when its components at all field
factors are trivial. -/
lemma modPow_mk_eq_one_iff_forall_factors (hf : f ≠ 0) (hsq : Squarefree f) (n : ℕ)
    (u : (AdjoinRoot f)ˣ) :
    (QuotientGroup.mk u : Units.modPow (AdjoinRoot f) n) = 1 ↔
      ∀ p : f.Factors,
        (QuotientGroup.mk (Units.map (projFactor hf hsq p).toMonoidHom u) :
          Units.modPow (AdjoinRoot (p : K[X])) n) = 1 := by
  rw [← map_eq_one_iff (modPowEquivPiFactors hf hsq n) (modPowEquivPiFactors hf hsq n).injective,
    funext_iff]
  exact forall_congr' fun p ↦ by rw [modPowEquivPiFactors_mk, Pi.one_apply]

/-- The norm of an element of `K[X]/(f)` is the product of the norms of its components in the
field factors. -/
theorem norm_eq_prod_norm_projFactor [Fintype f.Factors] (hf : f ≠ 0) (hsq : Squarefree f)
    (a : AdjoinRoot f) :
    Algebra.norm K a = ∏ p : f.Factors, Algebra.norm K (projFactor hf hsq p a) := by
  rw [← Algebra.norm_eq_of_algEquiv (equivPiFactors hf hsq) a, Algebra.norm_pi]
  rfl

/-- The norm of the component at the factor `p` of the class of `C x - X` is `p.eval x`. -/
lemma norm_projFactor_mk_C_sub_X (hf : f ≠ 0) (hsq : Squarefree f) (p : f.Factors) (x : K) :
    Algebra.norm K (projFactor hf hsq p (mk f (C x - X))) = (p : K[X]).eval x := by
  have hd : (C x - X).natDegree = 1 := by compute_degree!
  rw [projFactor_mk, norm_mk_eq_resultant p.monic, hd, resultant_C_sub_X _ _ _ le_rfl]

end AdjoinRoot

end EtaleDecomposition

/-!
### Rings of integers in finite extensions of number fields

The integral closure of `𝓞 K` in a finite extension `L` of a number field `K` is (isomorphic to)
the ring of integers of `L`; consequently the class number theorem and (the finite-generation
part of) Dirichlet's unit theorem apply to it.
-/

section NumberField

open NumberField

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

instance Rat.instIsPrincipalIdealRingRingOfIntegers : IsPrincipalIdealRing (𝓞 ℚ) :=
  .of_surjective (Rat.ringOfIntegersEquiv.symm : ℤ ≃+* 𝓞 ℚ) Rat.ringOfIntegersEquiv.symm.surjective

/-- The integral closure of `𝓞 K` in an extension `L` of `K` is the integral closure of `ℤ`
in `L`. -/
theorem isIntegralClosure_int_integralClosure :
    IsIntegralClosure (integralClosure (𝓞 K) L) ℤ L := by
  refine ⟨Subtype.val_injective, fun {x} ↦ ⟨fun hx ↦ ?_, fun ⟨y, hy⟩ ↦ ?_⟩⟩
  · exact ⟨⟨x, IsIntegral.tower_top (A := 𝓞 K) hx⟩, rfl⟩
  · have hyint : IsIntegral (𝓞 K) (y : L) := y.2
    have := isIntegral_trans (R := ℤ) (y : L) hyint
    rwa [show (y : L) = x from hy] at this

variable [NumberField K] [FiniteDimensional K L]

/-- The **class number theorem** for the integral closure of `𝓞 K` in a finite extension `L`
of the number field `K`: its class group is finite. -/
theorem NumberField.finite_classGroup_integralClosure :
    Finite (ClassGroup (integralClosure (𝓞 K) L)) := by
  have : NumberField L := .of_module_finite K L
  have := isIntegralClosure_int_integralClosure K L
  have := ClassGroup.fintypeOfAdmissibleOfFinite ℚ L
    (S := integralClosure (𝓞 K) L) AbsoluteValue.absIsAdmissible
  exact Finite.of_fintype _

/-- **Dirichlet's unit theorem** (finite generation) for the integral closure of `𝓞 K` in a
finite extension `L` of the number field `K`: its unit group is finitely generated. -/
theorem NumberField.fg_units_integralClosure :
    Group.FG (integralClosure (𝓞 K) L)ˣ := by
  have : NumberField L := .of_module_finite K L
  have e : integralClosure (𝓞 K) L ≃ₐ[𝓞 K] (𝓞 L) :=
    IsIntegralClosure.equiv (𝓞 K) (integralClosure (𝓞 K) L) L (𝓞 L)
  have : Group.FG (𝓞 L)ˣ := Group.fg_iff_monoid_fg.mpr inferInstance
  exact Group.fg_of_surjective
    (f := (Units.mapEquiv e.symm.toRingEquiv.toMulEquiv).toMonoidHom)
    (Units.mapEquiv e.symm.toRingEquiv.toMulEquiv).surjective

/-- If the ring of integers of `L` is a principal ideal domain, then the integral closure of
`𝓞 K` in `L` (being isomorphic to `𝓞 L`) has trivial class group. -/
theorem NumberField.subsingleton_classGroup_integralClosure (h : IsPrincipalIdealRing (𝓞 L)) :
    Subsingleton (ClassGroup (integralClosure (𝓞 K) L)) := by
  have : NumberField L := .of_module_finite K L
  have e : integralClosure (𝓞 K) L ≃ₐ[𝓞 K] 𝓞 L :=
    IsIntegralClosure.equiv (𝓞 K) (integralClosure (𝓞 K) L) L (𝓞 L)
  have : IsPrincipalIdealRing (integralClosure (𝓞 K) L) :=
    IsPrincipalIdealRing.of_surjective e.symm.toRingEquiv.toRingHom e.symm.surjective
  exact Fintype.card_le_one_iff_subsingleton.mp card_classGroup_eq_one.le

/-- The unit group of the integral closure of `𝓞 K` in a finite extension `L` has the same
rank as that of `𝓞 L` (they are isomorphic). -/
theorem NumberField.finrank_additive_units_integralClosure :
    Module.finrank ℤ (Additive (integralClosure (𝓞 K) L)ˣ) =
      Module.finrank ℤ (Additive (𝓞 L)ˣ) := by
  have : NumberField L := .of_module_finite K L
  have e : integralClosure (𝓞 K) L ≃ₐ[𝓞 K] 𝓞 L :=
    IsIntegralClosure.equiv (𝓞 K) (integralClosure (𝓞 K) L) L (𝓞 L)
  exact (MulEquiv.toAdditive
    (Units.mapEquiv e.toRingEquiv.toMulEquiv)).toIntLinearEquiv.finrank_eq

end NumberField

/-!
### Discriminants, class numbers, and unit ranks of cubic fields

The discriminant of a number field is the discriminant of any power basis with integral
generator divided by a square; consequently a cubic field whose power-basis discriminant is
at most `49` in absolute value has trivial class group (by the Minkowski bound), and the sign
of the power-basis discriminant determines the signature and hence, by Dirichlet's unit
theorem, the unit rank (`1` if negative, `2` if positive).
-/

section Discriminant

open NumberField Module

variable {K : Type*} [Field K] [NumberField K]

/-- The discriminant of any power basis of a number field `K` over `ℚ` with integral
generator (expressed via an integer `d` mapping to it) is the field discriminant times a
square. In particular, `discr K` divides `d` and has the same sign. -/
theorem NumberField.exists_eq_discr_mul_sq (pb : PowerBasis ℚ K)
    (hpb : IsIntegral ℤ pb.gen) {d : ℤ} (hd : Algebra.discr ℚ pb.basis = (d : ℚ)) :
    ∃ q : ℤ, d = discr K * q ^ 2 := by
  let b := (integralBasis K).reindex ((integralBasis K).indexEquiv pb.basis)
  have hP (i j : Fin pb.dim) : IsIntegral ℤ (b.toMatrix pb.basis i j) := by
    have hint : IsIntegral ℤ (pb.basis j) := by rw [pb.coe_basis]; exact hpb.pow _
    rw [Basis.toMatrix_apply, show pb.basis j = algebraMap (𝓞 K) K ⟨_, hint⟩ from rfl,
      Basis.repr_reindex_apply, integralBasis_repr_apply]
    exact isIntegral_algebraMap
  obtain ⟨q, hq⟩ := IsIntegrallyClosed.isIntegral_iff.mp (IsIntegral.det hP)
  rw [eq_intCast (algebraMap ℤ ℚ)] at hq
  have key : Algebra.discr ℚ pb.basis = (b.toMatrix pb.basis).det ^ 2 * Algebra.discr ℚ b := by
    nth_rw 1 [← b.toMatrix_map_vecMul pb.basis]
    rw [Algebra.discr_of_matrix_vecMul]
  have hb : Algebra.discr ℚ ⇑b = (discr K : ℚ) := by
    rw [Basis.coe_reindex, Algebra.discr_reindex, ← coe_discr]
  refine ⟨q, ?_⟩
  have h : (d : ℚ) = ((discr K * q ^ 2 : ℤ) : ℚ) := by
    push_cast
    rw [← hd, key, hb, ← hq]
    ring
  exact_mod_cast h

/-- A cubic number field with negative discriminant has unit rank `1`: its signature is
`(1, 1)`, so Dirichlet's unit theorem gives rank `1 + 1 - 1 = 1`. -/
theorem RingOfIntegers.finrank_additive_units_of_discr_neg (h3 : finrank ℚ K = 3)
    (hd : discr K < 0) : finrank ℤ (Additive (𝓞 K)ˣ) = 1 := by
  have hsign := sign_discr K
  rw [Int.sign_eq_neg_one_of_neg hd] at hsign
  have hodd : Odd (InfinitePlace.nrComplexPlaces K) := by
    by_contra hc
    rw [(Nat.not_odd_iff_even.mp hc).neg_one_pow] at hsign
    norm_num at hsign
  have h2 := InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [h3] at h2
  rw [Units.finrank_eq]
  simp only [Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  obtain ⟨k, hk⟩ := hodd
  lia

/-- A cubic number field with positive discriminant has unit rank `2`: it is totally real,
so Dirichlet's unit theorem gives rank `3 - 1 = 2`. -/
theorem RingOfIntegers.finrank_additive_units_of_discr_pos (h3 : finrank ℚ K = 3)
    (hd : 0 < discr K) : finrank ℤ (Additive (𝓞 K)ˣ) = 2 := by
  have hsign := sign_discr K
  rw [Int.sign_eq_one_of_pos hd] at hsign
  have heven : Even (InfinitePlace.nrComplexPlaces K) := by
    by_contra hc
    rw [(Nat.not_even_iff_odd.mp hc).neg_one_pow] at hsign
    norm_num at hsign
  have h2 := InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [h3] at h2
  rw [Units.finrank_eq]
  simp only [Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  obtain ⟨k, hk⟩ := heven
  lia

/-- A cubic number field with `|discr K| ≤ 49` has a principal ring of integers: its Minkowski
bound is less than `2` for either signature. -/
theorem RingOfIntegers.isPrincipalIdealRing_of_finrank_eq_three_of_abs_discr_le
    (h3 : finrank ℚ K = 3) (hd : |discr K| ≤ 49) : IsPrincipalIdealRing (𝓞 K) := by
  refine isPrincipalIdealRing_of_abs_discr_lt ?_
  have h2 := InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [h3] at h2
  have hd' : (|discr K| : ℝ) ≤ 49 := by exact_mod_cast hd
  have hpi := Real.pi_gt_d4
  set s := InfinitePlace.nrComplexPlaces K
  have hs : s ≤ 1 := by lia
  rw [h3]
  interval_cases s <;> norm_num <;> nlinarith

end Discriminant

end

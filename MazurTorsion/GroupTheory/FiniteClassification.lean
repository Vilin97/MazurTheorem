/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import MazurTorsion.GroupTheory.ClassificationCardinality
public import MazurTorsion.GroupTheory.ForbiddenEmbeddings

/-!
# The finite-abelian reduction in Mazur's torsion theorem

This file contains the elementary group-theoretic part of Mazur's theorem.  The main result is
stated for a finite abelian group already written in rank-two invariant-factor form.  It turns
the point-order theorem and the exclusion of the relevant square subgroups into Mazur's cyclic
and bicyclic list.

The rank-two normal form is the natural interface with the geometric fact that the `n`-torsion
of an elliptic curve has rank two.  A later file can derive that normal form from the geometric
torsion-cardinality theorem.
-/

@[expose] public section

namespace MazurTorsion

/-- The four possible second factors in Mazur's bicyclic groups. -/
def allowedBicyclicOrders : Finset ℕ :=
  {2, 4, 6, 8}

/-- The subgroup exclusions used by the finite-abelian reduction.

The first field is the rank-three obstruction.  The next four fields are the odd-prime and
four-torsion square obstructions.  The last two fields rule out the two oversized rank-two
groups whose elements still all have Mazur-allowed orders.
-/
structure AvoidsMazurForbiddenSubgroups (G : Type*) [AddCommGroup G] : Prop where
  c2Cube : ForbidsEmbedding (ZMod 2 × ZMod 2 × ZMod 2) G
  c3Square : ForbidsEmbedding (ZMod 3 × ZMod 3) G
  c4Square : ForbidsEmbedding (ZMod 4 × ZMod 4) G
  c5Square : ForbidsEmbedding (ZMod 5 × ZMod 5) G
  c7Square : ForbidsEmbedding (ZMod 7 × ZMod 7) G
  c2c10 : ForbidsEmbedding (ZMod 2 × ZMod 10) G
  c2c12 : ForbidsEmbedding (ZMod 2 × ZMod 12) G

/-- The group structures in Mazur's classification, written without reference to elliptic
curves. -/
def HasMazurGroupShape (G : Type*) [AddCommGroup G] : Prop :=
  (∃ n ∈ cyclicOrders, Nonempty (G ≃+ ZMod n)) ∨
    ∃ n ∈ allowedBicyclicOrders, Nonempty (G ≃+ (ZMod 2 × ZMod n))

private def zmodHomOfElement {A : Type*} [AddCommGroup A] (n : ℕ) (x : A)
    (hx : n • x = 0) : ZMod n →+ A :=
  ZMod.lift n
    ⟨
      { toFun := fun z : ℤ => z • x
        map_zero' := zero_zsmul x
        map_add' := fun a b => add_zsmul x a b },
      by simpa using hx⟩

private theorem zmodHomOfElement_injective {A : Type*} [AddCommGroup A] (n : ℕ) (x : A)
    (hx : n • x = 0) (horder : addOrderOf x = n) :
    Function.Injective (zmodHomOfElement n x hx) := by
  change Function.Injective (ZMod.lift n _)
  rw [ZMod.lift_injective]
  intro m hm
  change m • x = 0 at hm
  apply (CharP.intCast_eq_zero_iff (ZMod n) n m).2
  rw [← horder]
  exact (addOrderOf_dvd_iff_zsmul_eq_zero).2 hm

private theorem exists_zmod_embedding_of_dvd {d n : ℕ} (hd : d ∣ n) (_hdpos : 0 < d)
    (hn : n ≠ 0) :
    ∃ f : ZMod d →+ ZMod n, Function.Injective f := by
  let x : ZMod n := (n / d : ℕ)
  have hxorder : addOrderOf x = d := by
    rw [ZMod.addOrderOf_coe (n / d) hn, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hd),
      Nat.div_div_self hd hn]
  have hx : d • x = 0 := (addOrderOf_dvd_iff_nsmul_eq_zero.mp (hxorder ▸ dvd_rfl))
  exact ⟨zmodHomOfElement d x hx, zmodHomOfElement_injective d x hx hxorder⟩

private def directSumCoordinateHom
    {κ ι : Type*} [DecidableEq κ] [DecidableEq ι]
    (A : κ → Type*) (B : ι → Type*) [∀ j, AddCommMonoid (A j)]
    [∀ i, AddCommMonoid (B i)] (s : κ ↪ ι) (f : ∀ j, A j →+ B (s j)) :
    DirectSum κ A →+ DirectSum ι B :=
  DirectSum.toAddMonoid fun j => (DirectSum.of B (s j)).comp (f j)

private theorem directSumCoordinateHom_apply
    {κ ι : Type*} [DecidableEq κ] [DecidableEq ι]
    (A : κ → Type*) (B : ι → Type*) [∀ j, AddCommMonoid (A j)]
    [∀ i, AddCommMonoid (B i)] (s : κ ↪ ι) (f : ∀ j, A j →+ B (s j))
    (x : DirectSum κ A) (j : κ) :
    directSumCoordinateHom A B s f x (s j) = f j (x j) := by
  induction x using DirectSum.induction_on with
  | zero => simp [directSumCoordinateHom]
  | of i x =>
      by_cases hij : i = j
      · subst i
        simp [directSumCoordinateHom]
      · have hsij : s i ≠ s j := fun h => hij (s.injective h)
        rw [directSumCoordinateHom, DirectSum.toAddMonoid_of]
        change ((DirectSum.of B (s i)) (f i x)) (s j) =
          f j (((DirectSum.of A i) x) j)
        rw [DirectSum.of_apply, DirectSum.of_apply]
        simp [hij, hsij]
  | add x y hx hy =>
      rw [map_add, DirectSum.add_apply, DirectSum.add_apply, hx, hy, map_add]

private theorem directSumCoordinateHom_injective
    {κ ι : Type*} [DecidableEq κ] [DecidableEq ι]
    (A : κ → Type*) (B : ι → Type*) [∀ j, AddCommMonoid (A j)]
    [∀ i, AddCommMonoid (B i)] (s : κ ↪ ι) (f : ∀ j, A j →+ B (s j))
    (hf : ∀ j, Function.Injective (f j)) :
    Function.Injective (directSumCoordinateHom A B s f) := by
  intro x y hxy
  apply DFinsupp.ext
  intro j
  apply hf j
  rw [← directSumCoordinateHom_apply A B s f x j,
    ← directSumCoordinateHom_apply A B s f y j, hxy]

private theorem exists_pi_zmod_embedding_of_factors
    {G : Type*} [AddCommGroup G] {κ ι : Type*} [Finite κ]
    (d : κ → ℕ) (n : ι → ℕ) (s : κ ↪ ι)
    (hd : ∀ j, d j ∣ n (s j)) (hdpos : ∀ j, 0 < d j) (hn : ∀ i, n i ≠ 0)
    (e : G ≃+ DirectSum ι fun i => ZMod (n i)) :
    ∃ f : (∀ j, ZMod (d j)) →+ G, Function.Injective f := by
  classical
  letI := Fintype.ofFinite κ
  choose fj hfj using fun j => exists_zmod_embedding_of_dvd (hd j) (hdpos j) (hn (s j))
  let coordinates :
      DirectSum κ (fun j => ZMod (d j)) →+ DirectSum ι (fun i => ZMod (n i)) :=
    directSumCoordinateHom (fun j => ZMod (d j)) (fun i => ZMod (n i)) s fj
  let f : (∀ j, ZMod (d j)) →+ G :=
    e.symm.toAddMonoidHom.comp <|
      coordinates.comp (DirectSum.addEquivProd (fun j => ZMod (d j))).symm.toAddMonoidHom
  have hcoordinates : Function.Injective coordinates := by
    dsimp only [coordinates]
    exact directSumCoordinateHom_injective (fun j => ZMod (d j))
      (fun i => ZMod (n i)) s fj hfj
  refine ⟨f, ?_⟩
  intro x y hxy
  apply (DirectSum.addEquivProd (fun j => ZMod (d j))).symm.injective
  apply hcoordinates
  apply e.symm.injective
  exact hxy

/-- If a finite elementary-divisor presentation has at least `k` factors divisible by `d`, then
`(ZMod d) ^ k` embeds.  Consequently a forbidden elementary abelian subgroup bounds the number
of such factors. -/
theorem factor_count_lt_of_forbidden_pi
    {G : Type*} [AddCommGroup G] {ι : Type*} [Fintype ι]
    (n : ι → ℕ) (hn : ∀ i, n i ≠ 0)
    (e : G ≃+ DirectSum ι fun i => ZMod (n i))
    {d k : ℕ} (hdpos : 0 < d) (hforbid : ForbidsEmbedding (Fin k → ZMod d) G) :
    (Finset.univ.filter fun i => d ∣ n i).card < k := by
  classical
  by_contra hcount
  rw [not_lt] at hcount
  have hcard :
      Fintype.card (Fin k) ≤ Fintype.card {i : ι // d ∣ n i} := by
    rw [Fintype.card_fin, Fintype.card_subtype]
    exact hcount
  obtain ⟨s₀⟩ := Function.Embedding.nonempty_of_card_le hcard
  let s : Fin k ↪ ι := s₀.trans (Function.Embedding.subtype fun i : ι => d ∣ n i)
  have hs : ∀ j, d ∣ n (s j) := fun j => (s₀ j).2
  obtain ⟨f, hf⟩ := exists_pi_zmod_embedding_of_factors
    (fun _ : Fin k => d) n s hs (fun _ => hdpos) hn e
  exact hforbid f hf

/-- A square-subgroup exclusion says that at most one elementary-divisor factor is divisible by
`d`. -/
theorem factor_count_lt_two_of_forbidden_square
    {G : Type*} [AddCommGroup G] {ι : Type*} [Fintype ι]
    (n : ι → ℕ) (hn : ∀ i, n i ≠ 0)
    (e : G ≃+ DirectSum ι fun i => ZMod (n i))
    {d : ℕ} (hdpos : 0 < d) (hforbid : ForbidsEmbedding (ZMod d × ZMod d) G) :
    (Finset.univ.filter fun i => d ∣ n i).card < 2 := by
  let epi : (Fin 2 → ZMod d) ≃+ (ZMod d × ZMod d) :=
    (LinearEquiv.piFinTwo ℤ fun _ : Fin 2 => ZMod d).toAddEquiv
  exact factor_count_lt_of_forbidden_pi n hn e hdpos
    ((ForbidsEmbedding.addEquiv_source epi).mpr hforbid)

private def piFinThreeAddEquiv (A : Type*) [AddCommGroup A] :
    (Fin 3 → A) ≃+ (A × A × A) :=
  let e₁ : (Fin 3 → A) ≃ₗ[ℤ] (Option (Fin 2) → A) :=
    LinearEquiv.piCongrLeft ℤ (fun _ : Option (Fin 2) => A) (finSuccEquiv 2)
  let e₂ : (Option (Fin 2) → A) ≃ₗ[ℤ] (A × (Fin 2 → A)) :=
    LinearEquiv.piOptionEquivProd ℤ
  let e₃ : (A × (Fin 2 → A)) ≃ₗ[ℤ] (A × A × A) :=
    (LinearEquiv.refl ℤ A).prodCongr
      (LinearEquiv.piFinTwo ℤ fun _ : Fin 2 => A)
  (e₁.trans <| e₂.trans e₃).toAddEquiv

/-- A cube-subgroup exclusion says that at most two elementary-divisor factors are divisible by
`d`. -/
theorem factor_count_lt_three_of_forbidden_cube
    {G : Type*} [AddCommGroup G] {ι : Type*} [Fintype ι]
    (n : ι → ℕ) (hn : ∀ i, n i ≠ 0)
    (e : G ≃+ DirectSum ι fun i => ZMod (n i))
    {d : ℕ} (hdpos : 0 < d)
    (hforbid : ForbidsEmbedding (ZMod d × ZMod d × ZMod d) G) :
    (Finset.univ.filter fun i => d ∣ n i).card < 3 :=
  factor_count_lt_of_forbidden_pi n hn e hdpos
    ((ForbidsEmbedding.addEquiv_source (piFinThreeAddEquiv (ZMod d))).mpr hforbid)

private theorem square_embeds_of_dvd {G : Type*} [AddCommGroup G] {d m n : ℕ}
    (e : G ≃+ (ZMod m × ZMod n)) (hdm : d ∣ m) (hdn : d ∣ n) (hdpos : 0 < d)
    (hm : m ≠ 0) (hn : n ≠ 0) :
    ∃ f : ZMod d × ZMod d →+ G, Function.Injective f := by
  obtain ⟨fm, hfm⟩ := exists_zmod_embedding_of_dvd hdm hdpos hm
  obtain ⟨fn, hfn⟩ := exists_zmod_embedding_of_dvd hdn hdpos hn
  let f : ZMod d × ZMod d →+ G :=
    e.symm.toAddMonoidHom.comp (fm.prodMap fn)
  exact ⟨f, e.symm.injective.comp (hfm.prodMap hfn)⟩

private theorem left_factor_order {G : Type*} [AddCommGroup G] {m n : ℕ}
    (e : G ≃+ (ZMod m × ZMod n)) :
    addOrderOf (e.symm (1, 0)) = m := by
  calc
    addOrderOf (e.symm (1, 0)) = addOrderOf ((1, 0) : ZMod m × ZMod n) := by
      simp
    _ = addOrderOf (1 : ZMod m) := by
      exact addOrderOf_injective (AddMonoidHom.inl (ZMod m) (ZMod n))
        (fun _ _ h => congrArg Prod.fst h) 1
    _ = m := ZMod.addOrderOf_one m

private theorem right_factor_order {G : Type*} [AddCommGroup G] {m n : ℕ}
    (e : G ≃+ (ZMod m × ZMod n)) :
    addOrderOf (e.symm (0, 1)) = n := by
  calc
    addOrderOf (e.symm (0, 1)) = addOrderOf ((0, 1) : ZMod m × ZMod n) := by
      simp
    _ = addOrderOf (1 : ZMod n) := by
      exact addOrderOf_injective (AddMonoidHom.inr (ZMod m) (ZMod n))
        (fun _ _ h => congrArg Prod.snd h) 1
    _ = n := ZMod.addOrderOf_one n

private theorem no_square_dvd {G : Type*} [AddCommGroup G] {d m n : ℕ}
    (e : G ≃+ (ZMod m × ZMod n)) (hforbid : ForbidsEmbedding (ZMod d × ZMod d) G)
    (hdm : d ∣ m) (hdn : d ∣ n) (hdpos : 0 < d) (hm : m ≠ 0) (hn : n ≠ 0) :
    False := by
  obtain ⟨f, hf⟩ := square_embeds_of_dvd e hdm hdn hdpos hm hn
  exact hforbid f hf

/-- The pure rank-two finite-abelian reduction behind Mazur's classification.

The hypotheses say that `G` has invariant factors `m ∣ n`, every element of `G` has one of
Mazur's allowed point orders, and the seven standard obstruction groups do not embed.  The
conclusion is precisely Mazur's cyclic/bicyclic list.
-/
theorem hasMazurGroupShape_of_rankTwo
    {G : Type*} [AddCommGroup G] [Finite G]
    (horders : ∀ x : G, addOrderOf x ∈ cyclicOrders)
    (havoid : AvoidsMazurForbiddenSubgroups G)
    {m n : ℕ} (hmn : m ∣ n) (e : G ≃+ (ZMod m × ZMod n)) :
    HasMazurGroupShape G := by
  have hm : m ∈ cyclicOrders := by
    simpa [left_factor_order e] using horders (e.symm (1, 0))
  have hn : n ∈ cyclicOrders := by
    simpa [right_factor_order e] using horders (e.symm (0, 1))
  have hnzero : n ≠ 0 := by
    simp only [cyclicOrders, Finset.mem_insert, Finset.mem_singleton] at hn
    omega
  have hm_cases :
      m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨
        m = 8 ∨ m = 9 ∨ m = 10 ∨ m = 12 := by
    simpa only [cyclicOrders, Finset.mem_insert, Finset.mem_singleton] using hm
  rcases hm_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · left
    refine ⟨n, hn, ?_⟩
    exact ⟨e.trans AddEquiv.uniqueProd⟩
  · right
    have hn_cases :
        n = 2 ∨ n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 10 ∨ n = 12 := by
      have hn_all :
          n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨
            n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 12 := by
        simpa only [cyclicOrders, Finset.mem_insert, Finset.mem_singleton] using hn
      rcases hn_all with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp_all
    rcases hn_cases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨2, by simp [allowedBicyclicOrders], ⟨e⟩⟩
    · exact ⟨4, by simp [allowedBicyclicOrders], ⟨e⟩⟩
    · exact ⟨6, by simp [allowedBicyclicOrders], ⟨e⟩⟩
    · exact ⟨8, by simp [allowedBicyclicOrders], ⟨e⟩⟩
    · exact (havoid.c2c10 e.symm.toAddMonoidHom e.symm.injective).elim
    · exact (havoid.c2c12 e.symm.toAddMonoidHom e.symm.injective).elim
  · exact (no_square_dvd e havoid.c3Square (by norm_num) (dvd_trans (by norm_num) hmn)
      (by norm_num) (by norm_num) hnzero).elim
  · exact (no_square_dvd e havoid.c4Square (by norm_num) (dvd_trans (by norm_num) hmn)
      (by norm_num) (by norm_num) hnzero).elim
  · exact (no_square_dvd e havoid.c5Square (by norm_num) (dvd_trans (by norm_num) hmn)
      (by norm_num) (by norm_num) hnzero).elim
  · exact (no_square_dvd e havoid.c3Square (by norm_num) (dvd_trans (by norm_num) hmn)
      (by norm_num) (by norm_num) hnzero).elim
  · exact (no_square_dvd e havoid.c7Square (by norm_num) (dvd_trans (by norm_num) hmn)
      (by norm_num) (by norm_num) hnzero).elim
  · exact (no_square_dvd e havoid.c4Square (by norm_num) (dvd_trans (by norm_num) hmn)
      (by norm_num) (by norm_num) hnzero).elim
  · exact (no_square_dvd e havoid.c3Square (by norm_num) (dvd_trans (by norm_num) hmn)
      (by norm_num) (by norm_num) hnzero).elim
  · exact (no_square_dvd e havoid.c5Square (by norm_num) (dvd_trans (by norm_num) hmn)
      (by norm_num) (by norm_num) hnzero).elim
  · exact (no_square_dvd e havoid.c3Square (by norm_num) (dvd_trans (by norm_num) hmn)
      (by norm_num) (by norm_num) hnzero).elim

/-- The rank-two finite-abelian reduction immediately gives the numerical bound needed by the
LeanPool challenge. -/
theorem card_le_sixteen_of_rankTwo
    {G : Type*} [AddCommGroup G] [Finite G]
    (horders : ∀ x : G, addOrderOf x ∈ cyclicOrders)
    (havoid : AvoidsMazurForbiddenSubgroups G)
    {m n : ℕ} (hmn : m ∣ n) (e : G ≃+ (ZMod m × ZMod n)) :
    Nat.card G ≤ 16 := by
  rcases hasMazurGroupShape_of_rankTwo horders havoid hmn e with
    ⟨k, hk, ⟨ek⟩⟩ | ⟨k, hk, ⟨ek⟩⟩
  · rw [Nat.card_congr ek.toEquiv, Nat.card_zmod]
    simp only [cyclicOrders, Finset.mem_insert, Finset.mem_singleton] at hk
    omega
  · rw [Nat.card_congr ek.toEquiv, Nat.card_prod, Nat.card_zmod, Nat.card_zmod]
    simp only [allowedBicyclicOrders, Finset.mem_insert, Finset.mem_singleton] at hk
    omega

private theorem prime_pow_dvd_allowed_order_cases
    {p a D : ℕ} (hp : p.Prime) (hD : D ∈ cyclicOrders) (hdiv : p ^ a ∣ D) :
    p ^ a = 1 ∨ p ^ a = 2 ∨ p ^ a = 3 ∨ p ^ a = 4 ∨
      p ^ a = 5 ∨ p ^ a = 7 ∨ p ^ a = 8 ∨ p ^ a = 9 := by
  by_cases ha0 : a = 0
  · simp [ha0]
  have hDpos : 0 < D := by
    simp only [cyclicOrders, Finset.mem_insert, Finset.mem_singleton] at hD
    omega
  have hDle : D ≤ 12 := by
    simp only [cyclicOrders, Finset.mem_insert, Finset.mem_singleton] at hD
    omega
  have hqle : p ^ a ≤ D := Nat.le_of_dvd hDpos hdiv
  have ha : a < 4 := by
    by_contra ha
    rw [not_lt] at ha
    have h₁ : 2 ^ 4 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
    have h₂ : 2 ^ a ≤ p ^ a := Nat.pow_le_pow_left hp.two_le a
    norm_num at h₁
    omega
  have hple : p ≤ 12 := by
    exact (Nat.le_of_dvd (pow_pos hp.pos a) (dvd_pow_self p ha0)).trans
      (hqle.trans hDle)
  have hpcases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 := by
    rcases hp.eq_two_or_odd with hp2 | hpodd
    · exact Or.inl hp2
    have hpne9 : p ≠ 9 := by
      intro hp9
      subst p
      rcases hp.eq_one_or_self_of_dvd 3 (by norm_num) with h | h <;> omega
    have hpge : 2 ≤ p := hp.two_le
    interval_cases p <;> omega
  rcases hpcases with rfl | rfl | rfl | rfl | rfl <;>
    simp only [cyclicOrders, Finset.mem_insert, Finset.mem_singleton] at hD <;>
    rcases hD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    interval_cases a <;> norm_num at hdiv <;> norm_num

private theorem prod_indicator
    {ι : Type*} [Fintype ι] (q : ι → ℕ) (d r : ℕ) :
    (∏ i, if d ∣ q i then r else 1) =
      r ^ (Finset.univ.filter fun i => d ∣ q i).card := by
  classical
  rw [Finset.prod_ite]
  simp

private theorem elementary_product_le_sixteen
    {ι : Type*} [Fintype ι] (q : ι → ℕ) (D : ℕ)
    (hD : D ∈ cyclicOrders)
    (hq : ∀ i, q i = 1 ∨ q i = 2 ∨ q i = 3 ∨ q i = 4 ∨
      q i = 5 ∨ q i = 7 ∨ q i = 8 ∨ q i = 9)
    (hdiv : ∀ i, q i ∣ D)
    (hc2 : (Finset.univ.filter fun i => 2 ∣ q i).card < 3)
    (hc3 : (Finset.univ.filter fun i => 3 ∣ q i).card < 2)
    (hc4 : (Finset.univ.filter fun i => 4 ∣ q i).card < 2)
    (hc5 : (Finset.univ.filter fun i => 5 ∣ q i).card < 2)
    (hc7 : (Finset.univ.filter fun i => 7 ∣ q i).card < 2)
    (h10 : ¬((Finset.univ.filter fun i => 2 ∣ q i).card = 2 ∧
      (Finset.univ.filter fun i => 5 ∣ q i).card = 1))
    (h12 : ¬((Finset.univ.filter fun i => 2 ∣ q i).card = 2 ∧
      (Finset.univ.filter fun i => 4 ∣ q i).card = 1 ∧
      (Finset.univ.filter fun i => 3 ∣ q i).card = 1)) :
    ∏ i, q i ≤ 16 := by
  classical
  let c2 := (Finset.univ.filter fun i => 2 ∣ q i).card
  let c3 := (Finset.univ.filter fun i => 3 ∣ q i).card
  let c4 := (Finset.univ.filter fun i => 4 ∣ q i).card
  let c5 := (Finset.univ.filter fun i => 5 ∣ q i).card
  let c7 := (Finset.univ.filter fun i => 7 ∣ q i).card
  let c8 := (Finset.univ.filter fun i => 8 ∣ q i).card
  let c9 := (Finset.univ.filter fun i => 9 ∣ q i).card
  change ¬(c2 = 2 ∧ c5 = 1) at h10
  change ¬(c2 = 2 ∧ c4 = 1 ∧ c3 = 1) at h12
  have hc2le : c2 ≤ 2 := by omega
  have hc3le : c3 ≤ 1 := by omega
  have hc4le : c4 ≤ 1 := by omega
  have hc5le : c5 ≤ 1 := by omega
  have hc7le : c7 ≤ 1 := by omega
  have hc8le : c8 ≤ c4 := by
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact dvd_trans (by norm_num) hi
  have hc9le : c9 ≤ c3 := by
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact dvd_trans (by norm_num) hi
  simp only [cyclicOrders, Finset.mem_insert, Finset.mem_singleton] at hD
  rcases hD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hf : ∀ i, q i = 1 := by
      intro i
      have hi := hdiv i
      rcases hq i with h | h | h | h | h | h | h | h
      · exact h
      all_goals rw [h] at hi
      all_goals norm_num at hi
    simp_rw [hf]
    simp
  · have hf : ∀ i, q i = if 2 ∣ q i then 2 else 1 := by
      intro i
      have hi := hdiv i
      rcases hq i with h | h | h | h | h | h | h | h
      all_goals rw [h] at hi ⊢
      all_goals norm_num at hi <;> norm_num
    calc
      ∏ i, q i = 2 ^ c2 := by
        rw [Finset.prod_congr rfl (fun i _ => hf i), prod_indicator]
      _ ≤ 16 := by interval_cases c2 <;> norm_num
  · have hf : ∀ i, q i = if 3 ∣ q i then 3 else 1 := by
      intro i
      have hi := hdiv i
      rcases hq i with h | h | h | h | h | h | h | h
      all_goals rw [h] at hi ⊢
      all_goals norm_num at hi <;> norm_num
    calc
      ∏ i, q i = 3 ^ c3 := by
        rw [Finset.prod_congr rfl (fun i _ => hf i), prod_indicator]
      _ ≤ 16 := by interval_cases c3 <;> norm_num
  · have hf : ∀ i, q i =
        (if 2 ∣ q i then 2 else 1) * (if 4 ∣ q i then 2 else 1) := by
      intro i
      have hi := hdiv i
      rcases hq i with h | h | h | h | h | h | h | h
      all_goals rw [h] at hi ⊢
      all_goals norm_num at hi <;> norm_num
    calc
      ∏ i, q i = 2 ^ c2 * 2 ^ c4 := by
        rw [Finset.prod_congr rfl (fun i _ => hf i), Finset.prod_mul_distrib,
          prod_indicator, prod_indicator]
      _ ≤ 16 := by
        interval_cases c2 <;> interval_cases c4 <;> norm_num
  · have hf : ∀ i, q i = if 5 ∣ q i then 5 else 1 := by
      intro i
      have hi := hdiv i
      rcases hq i with h | h | h | h | h | h | h | h
      all_goals rw [h] at hi ⊢
      all_goals norm_num at hi <;> norm_num
    calc
      ∏ i, q i = 5 ^ c5 := by
        rw [Finset.prod_congr rfl (fun i _ => hf i), prod_indicator]
      _ ≤ 16 := by interval_cases c5 <;> norm_num
  · have hf : ∀ i, q i =
        (if 2 ∣ q i then 2 else 1) * (if 3 ∣ q i then 3 else 1) := by
      intro i
      have hi := hdiv i
      rcases hq i with h | h | h | h | h | h | h | h
      all_goals rw [h] at hi ⊢
      all_goals norm_num at hi <;> norm_num
    calc
      ∏ i, q i = 2 ^ c2 * 3 ^ c3 := by
        rw [Finset.prod_congr rfl (fun i _ => hf i), Finset.prod_mul_distrib,
          prod_indicator, prod_indicator]
      _ ≤ 16 := by
        interval_cases c2 <;> interval_cases c3 <;> norm_num
  · have hf : ∀ i, q i = if 7 ∣ q i then 7 else 1 := by
      intro i
      have hi := hdiv i
      rcases hq i with h | h | h | h | h | h | h | h
      all_goals rw [h] at hi ⊢
      all_goals norm_num at hi <;> norm_num
    calc
      ∏ i, q i = 7 ^ c7 := by
        rw [Finset.prod_congr rfl (fun i _ => hf i), prod_indicator]
      _ ≤ 16 := by interval_cases c7 <;> norm_num
  · have hf : ∀ i, q i =
        ((if 2 ∣ q i then 2 else 1) * (if 4 ∣ q i then 2 else 1)) *
          (if 8 ∣ q i then 2 else 1) := by
      intro i
      have hi := hdiv i
      rcases hq i with h | h | h | h | h | h | h | h
      all_goals rw [h] at hi ⊢
      all_goals norm_num at hi <;> norm_num
    calc
      ∏ i, q i = (2 ^ c2 * 2 ^ c4) * 2 ^ c8 := by
        rw [Finset.prod_congr rfl (fun i _ => hf i), Finset.prod_mul_distrib,
          Finset.prod_mul_distrib, prod_indicator, prod_indicator, prod_indicator]
      _ ≤ 16 := by
        interval_cases c2 <;> interval_cases c4 <;> interval_cases c8 <;> norm_num
  · have hf : ∀ i, q i =
        (if 3 ∣ q i then 3 else 1) * (if 9 ∣ q i then 3 else 1) := by
      intro i
      have hi := hdiv i
      rcases hq i with h | h | h | h | h | h | h | h
      all_goals rw [h] at hi ⊢
      all_goals norm_num at hi <;> norm_num
    calc
      ∏ i, q i = 3 ^ c3 * 3 ^ c9 := by
        rw [Finset.prod_congr rfl (fun i _ => hf i), Finset.prod_mul_distrib,
          prod_indicator, prod_indicator]
      _ ≤ 16 := by
        interval_cases c3 <;> interval_cases c9 <;> norm_num
  · have hf : ∀ i, q i =
        (if 2 ∣ q i then 2 else 1) * (if 5 ∣ q i then 5 else 1) := by
      intro i
      have hi := hdiv i
      rcases hq i with h | h | h | h | h | h | h | h
      all_goals rw [h] at hi ⊢
      all_goals norm_num at hi <;> norm_num
    have hformula : ∏ i, q i = 2 ^ c2 * 5 ^ c5 := by
      rw [Finset.prod_congr rfl (fun i _ => hf i), Finset.prod_mul_distrib,
        prod_indicator, prod_indicator]
    rw [hformula]
    interval_cases c2 <;> interval_cases c5 <;> norm_num
    exact (h10 ⟨rfl, rfl⟩).elim
  · have hf : ∀ i, q i =
        ((if 2 ∣ q i then 2 else 1) * (if 4 ∣ q i then 2 else 1)) *
          (if 3 ∣ q i then 3 else 1) := by
      intro i
      have hi := hdiv i
      rcases hq i with h | h | h | h | h | h | h | h
      all_goals rw [h] at hi ⊢
      all_goals norm_num at hi <;> norm_num
    have hformula : ∏ i, q i = (2 ^ c2 * 2 ^ c4) * 3 ^ c3 := by
      rw [Finset.prod_congr rfl (fun i _ => hf i), Finset.prod_mul_distrib,
        Finset.prod_mul_distrib, prod_indicator, prod_indicator, prod_indicator]
    rw [hformula]
    interval_cases c2 <;> interval_cases c4 <;> interval_cases c3 <;> norm_num
    exact (h12 ⟨rfl, rfl, rfl⟩).elim

private def d10 : Fin 3 → ℕ :=
  Fin.cases 2 (Fin.cases 2 fun _ => 5)

private def c2c10Coordinates :
    ZMod 2 × ZMod 10 →+ (∀ j : Fin 3, ZMod (d10 j)) :=
  let crt : ZMod 10 ≃+ ZMod 2 × ZMod 5 :=
    (ZMod.chineseRemainder (by norm_num : Nat.Coprime 2 5)).toAddEquiv
  let split : ZMod 2 × ZMod 10 →+ ZMod 2 × ZMod 5 :=
    crt.toAddMonoidHom.comp (AddMonoidHom.snd (ZMod 2) (ZMod 10))
  AddMonoidHom.pi fun j =>
    Fin.cases
      (AddMonoidHom.fst (ZMod 2) (ZMod 10))
      (Fin.cases
        ((AddMonoidHom.fst (ZMod 2) (ZMod 5)).comp split)
        (fun _ => (AddMonoidHom.snd (ZMod 2) (ZMod 5)).comp split))
      j

private theorem c2c10Coordinates_injective :
    Function.Injective c2c10Coordinates := by
  intro x y hxy
  apply Prod.ext
  · have h := congrFun hxy (0 : Fin 3)
    exact h
  · let crt : ZMod 10 ≃+ ZMod 2 × ZMod 5 :=
      (ZMod.chineseRemainder (by norm_num : Nat.Coprime 2 5)).toAddEquiv
    apply crt.injective
    apply Prod.ext
    · have h := congrFun hxy (1 : Fin 3)
      exact h
    · have h := congrFun hxy (2 : Fin 3)
      exact h

private def d12 : Fin 3 → ℕ :=
  Fin.cases 2 (Fin.cases 4 fun _ => 3)

private def c2c12Coordinates :
    ZMod 2 × ZMod 12 →+ (∀ j : Fin 3, ZMod (d12 j)) :=
  let crt : ZMod 12 ≃+ ZMod 4 × ZMod 3 :=
    (ZMod.chineseRemainder (by norm_num : Nat.Coprime 4 3)).toAddEquiv
  let split : ZMod 2 × ZMod 12 →+ ZMod 4 × ZMod 3 :=
    crt.toAddMonoidHom.comp (AddMonoidHom.snd (ZMod 2) (ZMod 12))
  AddMonoidHom.pi fun j =>
    Fin.cases
      (AddMonoidHom.fst (ZMod 2) (ZMod 12))
      (Fin.cases
        ((AddMonoidHom.fst (ZMod 4) (ZMod 3)).comp split)
        (fun _ => (AddMonoidHom.snd (ZMod 4) (ZMod 3)).comp split))
      j

private theorem c2c12Coordinates_injective :
    Function.Injective c2c12Coordinates := by
  intro x y hxy
  apply Prod.ext
  · have h := congrFun hxy (0 : Fin 3)
    exact h
  · let crt : ZMod 12 ≃+ ZMod 4 × ZMod 3 :=
      (ZMod.chineseRemainder (by norm_num : Nat.Coprime 4 3)).toAddEquiv
    apply crt.injective
    apply Prod.ext
    · have h := congrFun hxy (1 : Fin 3)
      exact h
    · have h := congrFun hxy (2 : Fin 3)
      exact h

private theorem c2c10EmbedsOfFactorCounts
    {G : Type*} [AddCommGroup G] {ι : Type*} [Fintype ι]
    (q : ι → ℕ) (hn : ∀ i, q i ≠ 0)
    (hq : ∀ i, q i = 1 ∨ q i = 2 ∨ q i = 3 ∨ q i = 4 ∨
      q i = 5 ∨ q i = 7 ∨ q i = 8 ∨ q i = 9)
    (e : G ≃+ DirectSum ι fun i => ZMod (q i))
    (hc2 : (Finset.univ.filter fun i => 2 ∣ q i).card = 2)
    (hc5 : (Finset.univ.filter fun i => 5 ∣ q i).card = 1) :
    ∃ f : ZMod 2 × ZMod 10 →+ G, Function.Injective f := by
  classical
  have hcard2 : Fintype.card {i : ι // 2 ∣ q i} = 2 := by
    rw [Fintype.card_subtype]
    exact hc2
  have hcard5 : Fintype.card {i : ι // 5 ∣ q i} = 1 := by
    rw [Fintype.card_subtype]
    exact hc5
  let e2 : {i : ι // 2 ∣ q i} ≃ Fin 2 :=
    Fintype.equivFinOfCardEq hcard2
  let e5 : {i : ι // 5 ∣ q i} ≃ Fin 1 :=
    Fintype.equivFinOfCardEq hcard5
  let i0 : ι := (e2.symm 0).1
  let i1 : ι := (e2.symm 1).1
  let i5 : ι := (e5.symm 0).1
  have hi0 : 2 ∣ q i0 := (e2.symm 0).2
  have hi1 : 2 ∣ q i1 := (e2.symm 1).2
  have hi5 : 5 ∣ q i5 := (e5.symm 0).2
  have hdisjoint : ∀ i, ¬(2 ∣ q i ∧ 5 ∣ q i) := by
    intro i hi
    rcases hq i with h | h | h | h | h | h | h | h
    all_goals rw [h] at hi
    all_goals norm_num at hi
  have hi01 : i0 ≠ i1 := by
    intro h
    have heq : e2.symm (0 : Fin 2) = e2.symm (1 : Fin 2) := Subtype.ext h
    exact Fin.zero_ne_one (e2.symm.injective heq)
  have hi05 : i0 ≠ i5 := by
    intro h
    apply hdisjoint i5
    exact ⟨h ▸ hi0, hi5⟩
  have hi15 : i1 ≠ i5 := by
    intro h
    apply hdisjoint i5
    exact ⟨h ▸ hi1, hi5⟩
  let sf : Fin 3 → ι :=
    ![i0, i1, i5]
  have hsf : Function.Injective sf := by
    intro j k h
    fin_cases j <;> fin_cases k <;> simp_all [sf]
  let s : Fin 3 ↪ ι := ⟨sf, hsf⟩
  have hd : ∀ j, d10 j ∣ q (s j) := by
    intro j
    fin_cases j
    · exact hi0
    · exact hi1
    · exact hi5
  have hdpos : ∀ j, 0 < d10 j := by
    intro j
    fin_cases j
    · change 0 < 2
      norm_num
    · change 0 < 2
      norm_num
    · change 0 < 5
      norm_num
  obtain ⟨f, hf⟩ :=
    exists_pi_zmod_embedding_of_factors d10 q s hd hdpos hn e
  exact ⟨f.comp c2c10Coordinates, hf.comp c2c10Coordinates_injective⟩

private theorem c2c12EmbedsOfFactorCounts
    {G : Type*} [AddCommGroup G] {ι : Type*} [Fintype ι]
    (q : ι → ℕ) (hn : ∀ i, q i ≠ 0)
    (hq : ∀ i, q i = 1 ∨ q i = 2 ∨ q i = 3 ∨ q i = 4 ∨
      q i = 5 ∨ q i = 7 ∨ q i = 8 ∨ q i = 9)
    (e : G ≃+ DirectSum ι fun i => ZMod (q i))
    (hc2 : (Finset.univ.filter fun i => 2 ∣ q i).card = 2)
    (hc4 : (Finset.univ.filter fun i => 4 ∣ q i).card = 1)
    (hc3 : (Finset.univ.filter fun i => 3 ∣ q i).card = 1) :
    ∃ f : ZMod 2 × ZMod 12 →+ G, Function.Injective f := by
  classical
  have hcard2 : Fintype.card {i : ι // 2 ∣ q i} = 2 := by
    rw [Fintype.card_subtype]
    exact hc2
  have hcard4 : Fintype.card {i : ι // 4 ∣ q i} = 1 := by
    rw [Fintype.card_subtype]
    exact hc4
  have hcard3 : Fintype.card {i : ι // 3 ∣ q i} = 1 := by
    rw [Fintype.card_subtype]
    exact hc3
  let e2 : {i : ι // 2 ∣ q i} ≃ Fin 2 :=
    Fintype.equivFinOfCardEq hcard2
  let e4 : {i : ι // 4 ∣ q i} ≃ Fin 1 :=
    Fintype.equivFinOfCardEq hcard4
  let e3 : {i : ι // 3 ∣ q i} ≃ Fin 1 :=
    Fintype.equivFinOfCardEq hcard3
  let i4 : ι := (e4.symm 0).1
  have hi4 : 4 ∣ q i4 := (e4.symm 0).2
  have hi4two : 2 ∣ q i4 := dvd_trans (by norm_num) hi4
  let i4as2 : {i : ι // 2 ∣ q i} := ⟨i4, hi4two⟩
  let k4 : Fin 2 := e2 i4as2
  let k2 : Fin 2 := if k4 = 0 then 1 else 0
  have hk2ne : k2 ≠ k4 := by
    by_cases hk : k4 = 0
    · simp [k2, hk]
    · have hk1 : k4 = 1 := Fin.eq_one_of_ne_zero k4 hk
      simp [k2, hk1]
  let i2 : ι := (e2.symm k2).1
  have hi2 : 2 ∣ q i2 := (e2.symm k2).2
  have hi24 : i2 ≠ i4 := by
    intro h
    have heq : e2.symm k2 = i4as2 := Subtype.ext h
    apply hk2ne
    calc
      k2 = e2 (e2.symm k2) := (e2.apply_symm_apply k2).symm
      _ = e2 i4as2 := congrArg e2 heq
      _ = k4 := rfl
  let i3 : ι := (e3.symm 0).1
  have hi3 : 3 ∣ q i3 := (e3.symm 0).2
  have hdisjoint : ∀ i, ¬(2 ∣ q i ∧ 3 ∣ q i) := by
    intro i hi
    rcases hq i with h | h | h | h | h | h | h | h
    all_goals rw [h] at hi
    all_goals norm_num at hi
  have hi23 : i2 ≠ i3 := by
    intro h
    apply hdisjoint i3
    exact ⟨h ▸ hi2, hi3⟩
  have hi43 : i4 ≠ i3 := by
    intro h
    apply hdisjoint i3
    exact ⟨h ▸ hi4two, hi3⟩
  let sf : Fin 3 → ι :=
    ![i2, i4, i3]
  have hsf : Function.Injective sf := by
    intro j k h
    fin_cases j <;> fin_cases k <;> simp_all [sf]
  let s : Fin 3 ↪ ι := ⟨sf, hsf⟩
  have hd : ∀ j, d12 j ∣ q (s j) := by
    intro j
    fin_cases j
    · exact hi2
    · exact hi4
    · exact hi3
  have hdpos : ∀ j, 0 < d12 j := by
    intro j
    fin_cases j
    · change 0 < 2
      norm_num
    · change 0 < 4
      norm_num
    · change 0 < 3
      norm_num
  obtain ⟨f, hf⟩ :=
    exists_pi_zmod_embedding_of_factors d12 q s hd hdpos hn e
  exact ⟨f.comp c2c12Coordinates, hf.comp c2c12Coordinates_injective⟩

/-- If every element of a finite abelian group has a Mazur-allowed order and none of the seven
standard obstruction groups embeds, then the group has at most sixteen elements. -/
theorem card_le_sixteen_of_allowed_orders_and_forbidden
    {G : Type*} [AddCommGroup G] [Finite G]
    (horders : ∀ x : G, addOrderOf x ∈ cyclicOrders)
    (havoid : AvoidsMazurForbiddenSubgroups G) :
    Nat.card G ≤ 16 := by
  classical
  obtain ⟨ι, hι, p, hp, a, ⟨e₀⟩⟩ :=
    AddCommGroup.equiv_directSum_zmod_of_finite G
  letI : Fintype ι := hι
  let q : ι → ℕ := fun i => p i ^ a i
  let e : G ≃+ DirectSum ι (fun i => ZMod (q i)) := e₀
  let eprod : G ≃+ (∀ i, ZMod (q i)) :=
    e.trans (DirectSum.addEquivProd fun i => ZMod (q i))
  let ones : ∀ i, ZMod (q i) := fun _ => 1
  let x : G := eprod.symm ones
  let D : ℕ := addOrderOf x
  have hD : D ∈ cyclicOrders := horders x
  have horder : addOrderOf ones = D := by
    simp [D, x]
  have hdiv : ∀ i, q i ∣ D := by
    intro i
    have hi :=
      addOrderOf_map_dvd (Pi.evalAddMonoidHom (fun i => ZMod (q i)) i) ones
    change addOrderOf (ones i) ∣ addOrderOf ones at hi
    rw [show addOrderOf (ones i) = q i by simp [ones, ZMod.addOrderOf_one],
      horder] at hi
    exact hi
  have hq :
      ∀ i, q i = 1 ∨ q i = 2 ∨ q i = 3 ∨ q i = 4 ∨
        q i = 5 ∨ q i = 7 ∨ q i = 8 ∨ q i = 9 := by
    intro i
    exact prime_pow_dvd_allowed_order_cases (hp i) hD (hdiv i)
  have hn : ∀ i, q i ≠ 0 := by
    intro i
    exact pow_ne_zero _ (hp i).ne_zero
  have hc2 :
      (Finset.univ.filter fun i => 2 ∣ q i).card < 3 :=
    factor_count_lt_three_of_forbidden_cube q hn e (by norm_num) havoid.c2Cube
  have hc3 :
      (Finset.univ.filter fun i => 3 ∣ q i).card < 2 :=
    factor_count_lt_two_of_forbidden_square q hn e (by norm_num) havoid.c3Square
  have hc4 :
      (Finset.univ.filter fun i => 4 ∣ q i).card < 2 :=
    factor_count_lt_two_of_forbidden_square q hn e (by norm_num) havoid.c4Square
  have hc5 :
      (Finset.univ.filter fun i => 5 ∣ q i).card < 2 :=
    factor_count_lt_two_of_forbidden_square q hn e (by norm_num) havoid.c5Square
  have hc7 :
      (Finset.univ.filter fun i => 7 ∣ q i).card < 2 :=
    factor_count_lt_two_of_forbidden_square q hn e (by norm_num) havoid.c7Square
  have h10 :
      ¬((Finset.univ.filter fun i => 2 ∣ q i).card = 2 ∧
        (Finset.univ.filter fun i => 5 ∣ q i).card = 1) := by
    rintro ⟨h2, h5⟩
    obtain ⟨f, hf⟩ := c2c10EmbedsOfFactorCounts q hn hq e h2 h5
    exact havoid.c2c10 f hf
  have h12 :
      ¬((Finset.univ.filter fun i => 2 ∣ q i).card = 2 ∧
        (Finset.univ.filter fun i => 4 ∣ q i).card = 1 ∧
        (Finset.univ.filter fun i => 3 ∣ q i).card = 1) := by
    rintro ⟨h2, h4, h3⟩
    obtain ⟨f, hf⟩ := c2c12EmbedsOfFactorCounts q hn hq e h2 h4 h3
    exact havoid.c2c12 f hf
  have hcard : Nat.card G = ∏ i, q i := by
    calc
      Nat.card G = Nat.card (∀ i, ZMod (q i)) :=
        Nat.card_congr eprod.toEquiv
      _ = ∏ i, Nat.card (ZMod (q i)) := Nat.card_pi
      _ = ∏ i, q i := by simp [Nat.card_zmod]
  rw [hcard]
  exact elementary_product_le_sixteen q D hD hq hdiv hc2 hc3 hc4 hc5 hc7 h10 h12

end MazurTorsion

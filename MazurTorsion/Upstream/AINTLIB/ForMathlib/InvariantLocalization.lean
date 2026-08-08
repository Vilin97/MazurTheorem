/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate. Tickets T-Q3a, T-Q3b, T-Q3c.
-/
import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Group actions on localizations at an invariant element

For a group `G` acting on a commutative ring `B` and an element `h : B` fixed by the
action, the action descends to the localization away from `h`:

* `MulSemiringAction.awayHom hfix g : Localization.Away h →+* Localization.Away h` —
  the ring endomorphism induced by `g • ·`, with `awayHom_one`, `awayHom_mul`,
  `awayHom_mk'`, `awayHom_mk'_pow`.
* `MulSemiringAction.away hfix : MulSemiringAction G (Localization.Away h)` — the
  bundled action; a `def`, not an instance (it depends on the hypothesis
  `hfix : ∀ g, g • h = h`); consumers bring it into scope with `letI`, following the
  `IsFractionRing.mulSemiringAction` precedent.
* `exists_fixed_mk'_eq_of_forall_awayHom_eq` (T-Q3b): for **finite** `G`, every fixed
  element of `Localization.Away h` is of the form `b / hⁿ` with `b` invariant —
  "invariants of the localization = localization of the invariants", surjectivity
  half. No averaging: the numerator is corrected by a power of `h` instead of
  dividing by `|G|`, so there is no invertibility hypothesis on `|G|`.
* `fixedPoints_awayMap_injective` (T-Q3c(i)): the induced map `(Bᴳ)_h → B_h` is
  injective.

This is the algebra backend of the affine quotient `Spec B → Spec Bᴳ` by a finite
group ([Loeffler, *Modular curves*, Prop 3.6.1] "one can show that these patch
nicely"; SGA I V.1.1; Stacks 07S5): the scheme-level universal property is
`ModularCurves/ForMathlib/AffineQuotient.lean` (ticket T-Q3).
-/

universe u v

variable {G : Type*} [Group G] {B : Type u} [CommRing B] [MulSemiringAction G B]
variable {h : B}

namespace MulSemiringAction

theorem powers_le_comap_toRingHom (hfix : ∀ g : G, g • h = h) (g : G) :
    Submonoid.powers h ≤ (Submonoid.powers h).comap (toRingHom G B g) := by
  rintro x ⟨n, rfl⟩
  refine Submonoid.mem_comap.mpr ⟨n, ?_⟩
  show h ^ n = g • h ^ n
  rw [smul_pow', hfix]

private theorem mk'_congr {a a' : B} {s s' : Submonoid.powers h} (ha : a = a')
    (hs : (s : B) = (s' : B)) :
    IsLocalization.mk' (Localization.Away h) a s =
      IsLocalization.mk' (Localization.Away h) a' s' := by
  subst ha
  exact congrArg _ (Subtype.ext hs)

/-- The ring endomorphism of `Localization.Away h` induced by localizing `g • ·` at
the invariant element `h`. Bundled into an action by `MulSemiringAction.away`. -/
noncomputable def awayHom (hfix : ∀ g : G, g • h = h) (g : G) :
    Localization.Away h →+* Localization.Away h :=
  IsLocalization.map (Localization.Away h) (toRingHom G B g)
    (powers_le_comap_toRingHom hfix g)

theorem awayHom_algebraMap (hfix : ∀ g : G, g • h = h) (g : G) (b : B) :
    awayHom hfix g (algebraMap B (Localization.Away h) b) =
      algebraMap B (Localization.Away h) (g • b) :=
  IsLocalization.map_eq _ b

theorem awayHom_mk' (hfix : ∀ g : G, g • h = h) (g : G) (b : B)
    (s : Submonoid.powers h) :
    awayHom hfix g (IsLocalization.mk' (Localization.Away h) b s) =
      IsLocalization.mk' (Localization.Away h) (g • b)
        (⟨g • (s : B), Submonoid.mem_comap.mp
          (powers_le_comap_toRingHom hfix g s.2)⟩ : Submonoid.powers h) :=
  IsLocalization.map_mk' _ b s

/-- `awayHom` on a fraction with invariant denominator `hⁿ`: only the numerator
moves. -/
theorem awayHom_mk'_pow (hfix : ∀ g : G, g • h = h) (g : G) (b : B) (n : ℕ) :
    awayHom hfix g (IsLocalization.mk' (Localization.Away h) b
        (⟨h ^ n, n, rfl⟩ : Submonoid.powers h)) =
      IsLocalization.mk' (Localization.Away h) (g • b)
        (⟨h ^ n, n, rfl⟩ : Submonoid.powers h) := by
  rw [awayHom_mk']
  exact mk'_congr rfl (by show g • h ^ n = h ^ n; rw [smul_pow', hfix])

theorem awayHom_one (hfix : ∀ g : G, g • h = h) (x : Localization.Away h) :
    awayHom hfix (1 : G) x = x := by
  obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers h) x
  rw [awayHom_mk']
  exact mk'_congr (one_smul G b) (one_smul G (s : B))

theorem awayHom_mul (hfix : ∀ g : G, g • h = h) (g g' : G) (x : Localization.Away h) :
    awayHom hfix (g * g') x = awayHom hfix g (awayHom hfix g' x) := by
  obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers h) x
  rw [awayHom_mk', awayHom_mk', awayHom_mk']
  exact mk'_congr (mul_smul g g' b) (mul_smul g g' (s : B))

/-- The action of `G` on `Localization.Away h` induced by localizing each `g • ·` at
the invariant element `h`. Not an instance (it depends on the invariance hypothesis):
bring it into scope with `letI := MulSemiringAction.away hfix`. -/
@[implicit_reducible]
noncomputable def away (hfix : ∀ g : G, g • h = h) :
    MulSemiringAction G (Localization.Away h) where
  smul g x := awayHom hfix g x
  one_smul := awayHom_one hfix
  mul_smul := awayHom_mul hfix
  smul_zero g := map_zero (awayHom hfix g)
  smul_add g := map_add (awayHom hfix g)
  smul_one g := map_one (awayHom hfix g)
  smul_mul g := map_mul (awayHom hfix g)

/-- **Invariants of a localization are the localization of the invariants**
(surjectivity half, T-Q3b): for a finite group and an invariant element `h`, every
fixed element of `Localization.Away h` is `b / hⁿ` for an invariant numerator `b`.

Stated via `awayHom` (`x` is fixed under the action `MulSemiringAction.away hfix`).
No averaging over `G` — the numerator is corrected by a power of `h` instead, so
there is no hypothesis on `|G|` being invertible in `B`. -/
theorem exists_fixed_mk'_eq_of_forall_awayHom_eq [Finite G]
    (hfix : ∀ g : G, g • h = h) (x : Localization.Away h)
    (hx : ∀ g : G, awayHom hfix g x = x) :
    ∃ (b : B) (n : ℕ), (∀ g : G, g • b = b) ∧
      IsLocalization.mk' (Localization.Away h) b
        (⟨h ^ n, n, rfl⟩ : Submonoid.powers h) = x := by
  obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers h) x
  obtain ⟨sv, N, rfl⟩ := s
  have key : ∀ g : G, ∃ m : ℕ, h ^ m * (g • b) = h ^ m * b := by
    intro g
    have hg := hx g
    rw [awayHom_mk'_pow hfix g b, IsLocalization.mk'_eq_iff_eq] at hg
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers h) _).mp hg
    obtain ⟨cv, k, rfl⟩ := c
    refine ⟨k + N, ?_⟩
    calc h ^ (k + N) * (g • b) = h ^ k * (h ^ N * (g • b)) := by ring
      _ = h ^ k * (h ^ N * b) := hc
      _ = h ^ (k + N) * b := by ring
  choose m hm using key
  cases nonempty_fintype G
  refine ⟨h ^ (Finset.univ.sup m) * b, N + Finset.univ.sup m, fun g => ?_, ?_⟩
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (Finset.mem_univ g))
    rw [smul_mul', smul_pow', hfix, hk]
    calc h ^ (m g + k) * (g • b) = h ^ k * (h ^ m g * (g • b)) := by ring
      _ = h ^ k * (h ^ m g * b) := by rw [hm g]
      _ = h ^ (m g + k) * b := by ring
  · exact (mk'_congr (mul_comm _ _)
      (by rw [Submonoid.coe_mul]; exact pow_add h N _)).trans
      (IsLocalization.mk'_cancel b (⟨h ^ N, N, rfl⟩ : Submonoid.powers h)
        (⟨h ^ (Finset.univ.sup m), Finset.univ.sup m, rfl⟩ : Submonoid.powers h))

end MulSemiringAction

section FixedSubalgebra

variable (R : Type v) [CommRing R] [Algebra R B] [SMulCommClass G R B]

theorem Submonoid.powers_le_comap_algebraMap (h : FixedPoints.subalgebra R B G) :
    Submonoid.powers h ≤ (Submonoid.powers (h : B)).comap
      (algebraMap (FixedPoints.subalgebra R B G) B) := by
  rintro x ⟨n, rfl⟩
  exact Submonoid.mem_comap.mpr ⟨n, by rw [map_pow]; rfl⟩

/-- The localization at `h` of the inclusion of the fixed subalgebra is injective
(T-Q3c(i)). -/
theorem fixedPoints_awayMap_injective (h : FixedPoints.subalgebra R B G) :
    Function.Injective (IsLocalization.map (Localization.Away (h : B))
      (algebraMap (FixedPoints.subalgebra R B G) B)
      (Submonoid.powers_le_comap_algebraMap R h) :
        Localization.Away h →+* Localization.Away (h : B)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers h) x
  rw [IsLocalization.map_mk', IsLocalization.mk'_eq_zero_iff] at hx
  obtain ⟨c, hc⟩ := hx
  obtain ⟨cv, k, rfl⟩ := c
  rw [IsLocalization.mk'_eq_zero_iff]
  refine ⟨⟨h ^ k, k, rfl⟩, Subtype.ext ?_⟩
  simpa using hc

/-- The range of the localized inclusion `(Bᴳ)_h → B_h` consists exactly of the fixed
points of the localized action (T-Q3c(ii)). -/
theorem mem_range_fixedPoints_awayMap_iff [Finite G]
    (h : FixedPoints.subalgebra R B G) (x : Localization.Away (h : B)) :
    x ∈ Set.range (IsLocalization.map (Localization.Away (h : B))
        (algebraMap (FixedPoints.subalgebra R B G) B)
        (Submonoid.powers_le_comap_algebraMap R h) :
          Localization.Away h →+* Localization.Away (h : B)) ↔
      ∀ g : G, MulSemiringAction.awayHom (fun g => h.2 g) g x = x := by
  constructor
  · rintro ⟨y, rfl⟩ g
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers h) y
    obtain ⟨sv, n, rfl⟩ := s
    rw [IsLocalization.map_mk', MulSemiringAction.awayHom_mk']
    refine MulSemiringAction.mk'_congr (a.2 g) ?_
    show g • algebraMap (FixedPoints.subalgebra R B G) B (h ^ n)
      = algebraMap (FixedPoints.subalgebra R B G) B (h ^ n)
    rw [map_pow]
    show g • ((h : B)) ^ n = ((h : B)) ^ n
    rw [smul_pow', h.2 g]
  · intro hx
    obtain ⟨b, n, hb, hbx⟩ :=
      MulSemiringAction.exists_fixed_mk'_eq_of_forall_awayHom_eq (fun g => h.2 g) x hx
    refine ⟨IsLocalization.mk' (Localization.Away h) (⟨b, hb⟩ :
      FixedPoints.subalgebra R B G) (⟨h ^ n, n, rfl⟩ : Submonoid.powers h), ?_⟩
    rw [IsLocalization.map_mk']
    refine (MulSemiringAction.mk'_congr rfl ?_).trans hbx
    show algebraMap (FixedPoints.subalgebra R B G) B (h ^ n) = (h : B) ^ n
    rw [map_pow]
    rfl

end FixedSubalgebra

/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import MazurTorsion.Upstream.AINTLIB.ForMathlib.TotalComplexUpNat

/-!
# Low degrees of a first-quadrant total complex

Expose component projections, the decompositions in total degrees zero and one, and the
signed differential formula for mathlib's total complex of an `ℕ × ℕ` cochain bicomplex.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ))
variable [K.HasTotal (.up ℕ)]

/-- Projection from a total degree onto one bidegree. It is zero unless the bidegree
belongs to the specified total degree. -/
noncomputable def πTotalUpNat (q p n : ℕ) :
    (K.total (.up ℕ)).X n ⟶ (K.X q).X p :=
  K.totalDesc (c₁₂ := .up ℕ) fun q' p' _ ↦
    if hq : q' = q then
      if hp : p' = p then (K.XXIsoOfEq _ _ _ hq hp).hom else 0
    else 0

@[reassoc (attr := simp)]
theorem ιTotal_πTotalUpNat (q' p' n : ℕ) (h : q' + p' = n) (q p : ℕ) :
    K.ιTotal (.up ℕ) q' p' n h ≫ K.πTotalUpNat q p n =
      if hq : q' = q then
        if hp : p' = p then (K.XXIsoOfEq _ _ _ hq hp).hom else 0
      else 0 := by
  simp [πTotalUpNat]

@[simp]
theorem ιTotal_πTotalUpNat_self (q p : ℕ) :
    K.ιTotal (.up ℕ) q p (q + p) rfl ≫ K.πTotalUpNat q p (q + p) = 𝟙 _ := by
  simp [πTotalUpNat]

/-- Total degree zero consists only of bidegree `(0,0)`. -/
theorem totalUpNat_zero_decomposition :
    K.πTotalUpNat 0 0 0 ≫ K.ιTotal (.up ℕ) 0 0 0 rfl = 𝟙 _ := by
  apply HomologicalComplex₂.total.hom_ext
  intro q p h
  change q + p = 0 at h
  have hq : q = 0 := by omega
  have hp : p = 0 := by omega
  subst q p
  simp

/-- Total degree one is the sum of bidegrees `(0,1)` and `(1,0)`. -/
theorem totalUpNat_one_decomposition :
    K.πTotalUpNat 0 1 1 ≫ K.ιTotal (.up ℕ) 0 1 1 rfl +
      K.πTotalUpNat 1 0 1 ≫ K.ιTotal (.up ℕ) 1 0 1 rfl = 𝟙 _ := by
  apply HomologicalComplex₂.total.hom_ext
  intro q p h
  change q + p = 1 at h
  rcases show (q = 0 ∧ p = 1) ∨ (q = 1 ∧ p = 0) by omega with h | h
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · obtain ⟨rfl, rfl⟩ := h
    simp

/-- The total differential on a bidegree is the resolution differential plus the
signed Cech differential. -/
@[reassoc]
theorem ιTotal_d_upNat (q p : ℕ) :
    K.ιTotal (.up ℕ) q p (q + p) rfl ≫
        (K.total (.up ℕ)).d (q + p) (q + p + 1) =
      (K.d q (q + 1)).f p ≫
          K.ιTotal (.up ℕ) (q + 1) p (q + p + 1)
            (by change q + 1 + p = q + p + 1; omega) +
        ((-1 : ℤˣ) ^ q) • ((K.X q).d p (p + 1) ≫
          K.ιTotal (.up ℕ) q (p + 1) (q + p + 1)
            (by change q + (p + 1) = q + p + 1; omega)) := by
  change _ ≫ (K.D₁ (.up ℕ) (q + p) (q + p + 1) +
      K.D₂ (.up ℕ) (q + p) (q + p + 1)) = _
  calc
    _ = (K.ιTotal (.up ℕ) q p (q + p) rfl ≫
          K.D₁ (.up ℕ) (q + p) (q + p + 1)) +
        (K.ιTotal (.up ℕ) q p (q + p) rfl ≫
          K.D₂ (.up ℕ) (q + p) (q + p + 1)) :=
      Preadditive.comp_add _ _ _ _ _ _
    _ = _ := by
      congr 1
      · calc
          _ = K.d₁ (.up ℕ) q p (q + p + 1) :=
            K.ι_D₁ (.up ℕ) (q + p) (q + p + 1) q p rfl
          _ = _ := by
            rw [K.d₁_eq (.up ℕ)
              (show (ComplexShape.up ℕ).Rel q (q + 1) by rfl) p (q + p + 1)
              (by change q + 1 + p = q + p + 1; omega)]
            simp
      · calc
          _ = K.d₂ (.up ℕ) q p (q + p + 1) :=
            K.ι_D₂ (.up ℕ) (q + p) (q + p + 1) q p rfl
          _ = _ := by
            rw [K.d₂_eq (.up ℕ) q
              (show (ComplexShape.up ℕ).Rel p (p + 1) by rfl) (q + p + 1)
              (by change q + (p + 1) = q + p + 1; omega)]
            simp

end HomologicalComplex₂

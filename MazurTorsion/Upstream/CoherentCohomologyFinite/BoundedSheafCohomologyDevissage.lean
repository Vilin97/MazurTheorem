/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.CohomologyDevissage
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafAffineCover
import MazurTorsion.Upstream.CoherentCohomologyFinite.SheafRestrictionExactness

/-!
# Bounded dévissage for rationalized scheme-module cohomology

This is the scheme-module counterpart of
`linearExtFinite_of_bounded_quotient_presentations`.  It works directly
with the underlying abelian sheaves and rationalizes their long exact
cohomology sequence.  Thus a presentation in `X.Modules` can be used
without first constructing an exact functor to sheaves of rational vector
spaces.
-/


open CategoryTheory Limits AlgebraicGeometry TensorProduct

noncomputable section

namespace MazurTorsion.AlgebraicGeometry.CoherentCohomology

noncomputable local instance boundedCohomologyAddCommGroup
    {Z : TopCat.{0}}
    (G : Z.Sheaf AddCommGrpCat.{0}) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H G n) := by
  dsimp only [CategoryTheory.Sheaf.H]
  exact CategoryTheory.Abelian.Ext.instAddCommGroup

/--
Suppose a class of scheme modules has a uniform cohomological bound and
every object in the class is a quotient of an object with finite
rationalized cohomology, with kernel still in the class.  Then every
object in the class has finite rationalized cohomology in every degree.
-/
theorem rationalizedSheafH_finite_of_bounded_quotient_presentations
    {X : Scheme.{0}}
    (P Good : X.Modules → Prop) (bound : ℕ)
    (hvanish :
      ∀ (Y : X.Modules), P Y → ∀ n : ℕ, bound < n →
        Subsingleton (Y.sheaf.H n))
    (hpresentation :
      ∀ (Y : X.Modules), P Y →
        ∃ (E : X.Modules) (f : E ⟶ Y),
          Epi f ∧ Good E ∧ P (kernel f))
    (hgood :
      ∀ (E : X.Modules), Good E → ∀ n : ℕ,
        Module.Finite ℚ (ℚ ⊗[ℤ] E.sheaf.H n))
    (Y : X.Modules) (hY : P Y) (n : ℕ) :
    Module.Finite ℚ (ℚ ⊗[ℤ] Y.sheaf.H n) := by
  by_cases hn : bound < n
  · letI : Subsingleton (Y.sheaf.H n) :=
      hvanish Y hY n hn
    infer_instance
  · have hnle : n ≤ bound := Nat.le_of_not_gt hn
    let distance := bound - n
    induction hdistance : distance using Nat.strong_induction_on
      generalizing n Y with
    | h k ih =>
        obtain ⟨E, f, hf, hE, hker⟩ :=
          hpresentation Y hY
        letI : Epi f := hf
        let S := ShortComplex.kernelSequence f
        haveI : Epi S.g := by
          dsimp [S, ShortComplex.kernelSequence]
          infer_instance
        have hS : S.ShortExact :=
          { exact := ShortComplex.kernelSequence_exact f }
        let Ssheaf := S.map (Scheme.Modules.toUnderlyingSheaf X)
        have hSsheaf : Ssheaf.ShortExact :=
          ShortComplex.ShortExact.map_of_exact hS
            (Scheme.Modules.toUnderlyingSheaf X)
        have hkernel :
            Module.Finite ℚ
              (ℚ ⊗[ℤ] (kernel f).sheaf.H (n + 1)) := by
          by_cases htop : bound < n + 1
          · letI :
                Subsingleton ((kernel f).sheaf.H (n + 1)) :=
              hvanish (kernel f) hker (n + 1) htop
            infer_instance
          · have hnextle : n + 1 ≤ bound :=
              Nat.le_of_not_gt htop
            have hlt :
                bound - (n + 1) < k := by
              dsimp [distance] at hdistance
              omega
            exact
              ih (bound - (n + 1)) hlt
                (kernel f) hker (n + 1)
                htop hnextle rfl
        let constantZ :=
          (constantSheaf
            (Opens.grothendieckTopology X)
            AddCommGrpCat.{0}).obj
              (AddCommGrpCat.of (ULift ℤ))
        have hmiddle :
            Module.Finite ℚ
              (ℚ ⊗[ℤ]
                Abelian.Ext constantZ Ssheaf.X₂ n) := by
          change
            Module.Finite ℚ
              (ℚ ⊗[ℤ] E.sheaf.H n)
          exact hgood E hE n
        have hfirst :
            Module.Finite ℚ
              (ℚ ⊗[ℤ]
                Abelian.Ext constantZ Ssheaf.X₁ (n + 1)) := by
          change
            Module.Finite ℚ
              (ℚ ⊗[ℤ] (kernel f).sheaf.H (n + 1))
          exact hkernel
        exact
          @MazurTorsion.AlgebraicGeometry.CoherentCohomology.rationalized_ext_finite_right
            (TopCat.Sheaf AddCommGrpCat.{0} X)
            inferInstance inferInstance inferInstance
            constantZ Ssheaf hSsheaf n hmiddle hfirst

/--
The preceding result bundled as finite rationalized cohomology in every
degree.
-/
theorem rationalizedSheafH_finite_all_of_bounded_quotient_presentations
    {X : Scheme.{0}}
    (P Good : X.Modules → Prop) (bound : ℕ)
    (hvanish :
      ∀ (Y : X.Modules), P Y → ∀ n : ℕ, bound < n →
        Subsingleton (Y.sheaf.H n))
    (hpresentation :
      ∀ (Y : X.Modules), P Y →
        ∃ (E : X.Modules) (f : E ⟶ Y),
          Epi f ∧ Good E ∧ P (kernel f))
    (hgood :
      ∀ (E : X.Modules), Good E → ∀ n : ℕ,
        Module.Finite ℚ (ℚ ⊗[ℤ] E.sheaf.H n))
    (Y : X.Modules) (hY : P Y) :
    ∀ n : ℕ, Module.Finite ℚ (ℚ ⊗[ℤ] Y.sheaf.H n) :=
  fun n =>
    rationalizedSheafH_finite_of_bounded_quotient_presentations
      P Good bound hvanish hpresentation hgood Y hY n

end MazurTorsion.AlgebraicGeometry.CoherentCohomology

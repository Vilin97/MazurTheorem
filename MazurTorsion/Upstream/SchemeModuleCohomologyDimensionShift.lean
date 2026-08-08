/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Upstream.AINTLIB.ForMathlib.SheafCohomologyExact
import MazurTorsion.Upstream.AINTLIB.ForMathlib.SchemeModuleSheaf
import MazurTorsion.Upstream.SchemeModuleCohomologyAffineCoverMono

/-!
# The injective step in affine dimension shifting

This file isolates the exact-sequence step used in Kempf's affine-vanishing
argument.  Given a short exact sequence of modules on a scheme, vanishing of
degree `n` cohomology for the cokernel makes the induced map on degree
`n + 1` cohomology injective.  The proof applies the actual connecting map in
the long exact sequence of the underlying abelian sheaves.

The second theorem is a checked downstream consumer for the genuine
affine-cover inclusion and cokernel constructed in
`SchemeModuleCohomologyAffineCoverMono`.  It deliberately retains the
cokernel-cohomology hypothesis: proving that hypothesis from local killing is
the remaining mathematical part of affine vanishing.

The long exact sequence and exact forgetful functor are retained from
AINTLIB commit `7ecbba9dbb7fee076a1b77a6cd516fc6de46d684`; see `PORTING.md`.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace
open _root_.AlgebraicGeometry

namespace MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

/-- In a short exact sequence, if degree-`n` cohomology of the cokernel is
subsingleton, then the first map is injective on degree `n + 1` cohomology. -/
theorem cohomology_succ_map_injective_of_cokernel_subsingleton
    {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (n : ℕ) [Subsingleton (H S.X₃ n)] :
    Function.Injective ((zariskiFunctor X (n + 1)).map S.f) := by
  let Ssheaf := S.map (Scheme.Modules.toSheaf X)
  have hSsheaf : Ssheaf.ShortExact :=
    ShortComplex.ShortExact.map_of_exact hS
      (Scheme.Modules.toSheaf X)
  letI : Subsingleton (CategoryTheory.Sheaf.H Ssheaf.X₃ n) := by
    change Subsingleton (H S.X₃ n)
    infer_instance
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨x, hx⟩ := CategoryTheory.Sheaf.H.longSequence_exact₁
    hSsheaf n (n + 1) rfl c hc
  rw [← hx, Subsingleton.elim x 0, map_zero]
  rfl

/-- The affine-cover inclusion is injective on degree `n + 1` cohomology as
soon as degree-`n` cohomology of its actual cokernel vanishes. -/
theorem toAffineCoverModule_H_succ_injective_of_cokernel_subsingleton
    {R : CommRingCat.{u}} {I : Type u} (M : (Spec R).Modules)
    (U : I → (Spec R).Opens) (hU : IsOpenCover U) (n : ℕ)
    [Subsingleton (H (cokernel (toAffineCoverModule M U)) n)] :
    Function.Injective
      ((zariskiFunctor (Spec R) (n + 1)).map
        (toAffineCoverModule M U)) := by
  exact cohomology_succ_map_injective_of_cokernel_subsingleton
    (affineCoverCokernel_shortExact M U hU) n

end MazurTorsion.AlgebraicGeometry.SchemeModuleCohomology

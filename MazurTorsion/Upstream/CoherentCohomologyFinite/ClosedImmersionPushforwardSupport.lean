/-
Copyright (c) 2026 Vasil V. and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasil V., OpenAI Codex
-/
import MazurTorsion.Upstream.CoherentCohomologyFinite.ModuleSupport
import MazurTorsion.Upstream.CoherentCohomologyFinite.SchemePushforwardCohomology

/-!
# Support of a closed-immersion pushforward

The stalk of a direct image along a closed immersion vanishes away from
the closed image.  Hence the closed stalk support of every pushed-forward
module is contained in that image.
-/


open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{0}}

/-- The closed support of a closed-immersion pushforward lies in its
set-theoretic image. -/
theorem closedStalkSupport_pushforward_le_range
    (i : X ⟶ Y) [IsClosedImmersion i]
    (M : X.Modules) :
    closedStalkSupport ((pushforward i).obj M) ≤
      (⟨Set.range i,
        i.isClosedEmbedding.isClosed_range⟩ : Closeds Y) := by
  change
    closure (stalkSupport ((pushforward i).obj M)) ⊆
      Set.range i
  apply closure_minimal
  · intro y hy
    by_contra hyrange
    apply hy
    rw [AddCommGrpCat.isZero_iff_subsingleton]
    constructor
    intro a b
    rw [
      MazurTorsion.AlgebraicGeometry.CoherentCohomology.TopCat.pushforward_stalk_eq_zero_of_not_mem_range
        i.isClosedEmbedding M.sheaf.property hyrange a,
      MazurTorsion.AlgebraicGeometry.CoherentCohomology.TopCat.pushforward_stalk_eq_zero_of_not_mem_range
        i.isClosedEmbedding M.sheaf.property hyrange b]
  · exact i.isClosedEmbedding.isClosed_range

end AlgebraicGeometry.Scheme.Modules

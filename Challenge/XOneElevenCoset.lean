/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.NumberTheory.XOneElevenDescent

/-!
# Challenge: the five-coset bound on X_1(11)

This is the remaining arithmetic input to the compiled order-eleven
reduction. The downstream file already proves that this proposition
classifies every rational point on the selected genus-one model.
-/

namespace MazurTheorem.Challenge

/-- Every rational point on the selected `X_1(11)` model differs from one
of the five visible torsion points by five times another rational point. -/
theorem xOneEleven_fiveCosetBound :
    MazurTorsion.XOneEleven.FiveCosetBound := sorry

end MazurTheorem.Challenge

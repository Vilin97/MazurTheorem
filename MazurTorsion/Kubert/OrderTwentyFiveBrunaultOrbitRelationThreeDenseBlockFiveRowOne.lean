/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseCertificate

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationThreeDenseCertificate

private def leftRow :=
  ((leftTailFive.take 5).drop 1).take 1

private def rightRow :=
  ((rightTailFive.take 5).drop 1).take 1

theorem certificateBlockFiveRowOne : leftRow = rightRow := by decide

end MazurTorsion.Kubert.OrderTwentyFiveRelationThreeDenseCertificate

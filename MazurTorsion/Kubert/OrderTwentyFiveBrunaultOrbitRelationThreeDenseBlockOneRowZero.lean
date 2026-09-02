/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationThreeDenseCertificate

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationThreeDenseCertificate

private def leftRow :=
  (leftTailOne.take 5).take 1

private def rightRow :=
  (rightTailOne.take 5).take 1

theorem certificateBlockOneRowZero : leftRow = rightRow := by decide

end MazurTorsion.Kubert.OrderTwentyFiveRelationThreeDenseCertificate

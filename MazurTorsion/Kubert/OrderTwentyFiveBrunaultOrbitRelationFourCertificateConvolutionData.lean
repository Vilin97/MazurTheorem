/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateNumerator
import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitRelationFourCertificateQuotient

/-!
# Aggregate convolution data for the split RelationFour certificate

The convolution is supported in degrees `0` through `34`; its catch-all branch
is zero. Each displayed branch is mechanically identical to the corresponding
row in the frozen monolith, with coefficient names replaced by aggregate
function applications.
-/

namespace MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal

def convolutionOf (a b : Nat → ℚ) (n : Nat) : ℚ :=
  match n with
  | 0 => a 0 * b 0
  | 1 => a 0 * b 1 + a 1 * b 0
  | 2 => a 0 * b 2 + a 1 * b 1 + a 2 * b 0
  | 3 => a 0 * b 3 + a 1 * b 2 + a 2 * b 1 + a 3 * b 0
  | 4 => a 0 * b 4 + a 1 * b 3 + a 2 * b 2 + a 3 * b 1 + a 4 * b 0
  | 5 => a 0 * b 5 + a 1 * b 4 + a 2 * b 3 + a 3 * b 2 + a 4 * b 1 + a 5 * b 0
  | 6 =>
      a 0 * b 6 + a 1 * b 5 + a 2 * b 4 + a 3 * b 3 + a 4 * b 2 + a 5 * b 1
          + a 6 * b 0
  | 7 =>
      a 0 * b 7 + a 1 * b 6 + a 2 * b 5 + a 3 * b 4 + a 4 * b 3 + a 5 * b 2
          + a 6 * b 1 + a 7 * b 0
  | 8 =>
      a 0 * b 8 + a 1 * b 7 + a 2 * b 6 + a 3 * b 5 + a 4 * b 4 + a 5 * b 3
          + a 6 * b 2 + a 7 * b 1 + a 8 * b 0
  | 9 =>
      a 0 * b 9 + a 1 * b 8 + a 2 * b 7 + a 3 * b 6 + a 4 * b 5 + a 5 * b 4
          + a 6 * b 3 + a 7 * b 2 + a 8 * b 1 + a 9 * b 0
  | 10 =>
      a 0 * b 10 + a 1 * b 9 + a 2 * b 8 + a 3 * b 7 + a 4 * b 6 + a 5 * b 5
          + a 6 * b 4 + a 7 * b 3 + a 8 * b 2 + a 9 * b 1 + a 10 * b 0
  | 11 =>
      a 0 * b 11 + a 1 * b 10 + a 2 * b 9 + a 3 * b 8 + a 4 * b 7 + a 5 * b 6
          + a 6 * b 5 + a 7 * b 4 + a 8 * b 3 + a 9 * b 2 + a 10 * b 1
  | 12 =>
      a 0 * b 12 + a 1 * b 11 + a 2 * b 10 + a 3 * b 9 + a 4 * b 8 + a 5 * b 7
          + a 6 * b 6 + a 7 * b 5 + a 8 * b 4 + a 9 * b 3 + a 10 * b 2
  | 13 =>
      a 0 * b 13 + a 1 * b 12 + a 2 * b 11 + a 3 * b 10 + a 4 * b 9 + a 5 * b 8
          + a 6 * b 7 + a 7 * b 6 + a 8 * b 5 + a 9 * b 4 + a 10 * b 3
  | 14 =>
      a 0 * b 14 + a 1 * b 13 + a 2 * b 12 + a 3 * b 11 + a 4 * b 10 + a 5 * b 9
          + a 6 * b 8 + a 7 * b 7 + a 8 * b 6 + a 9 * b 5 + a 10 * b 4
  | 15 =>
      a 0 * b 15 + a 1 * b 14 + a 2 * b 13 + a 3 * b 12 + a 4 * b 11
          + a 5 * b 10 + a 6 * b 9 + a 7 * b 8 + a 8 * b 7 + a 9 * b 6
          + a 10 * b 5
  | 16 =>
      a 0 * b 16 + a 1 * b 15 + a 2 * b 14 + a 3 * b 13 + a 4 * b 12
          + a 5 * b 11 + a 6 * b 10 + a 7 * b 9 + a 8 * b 8 + a 9 * b 7
          + a 10 * b 6
  | 17 =>
      a 0 * b 17 + a 1 * b 16 + a 2 * b 15 + a 3 * b 14 + a 4 * b 13
          + a 5 * b 12 + a 6 * b 11 + a 7 * b 10 + a 8 * b 9 + a 9 * b 8
          + a 10 * b 7
  | 18 =>
      a 0 * b 18 + a 1 * b 17 + a 2 * b 16 + a 3 * b 15 + a 4 * b 14
          + a 5 * b 13 + a 6 * b 12 + a 7 * b 11 + a 8 * b 10 + a 9 * b 9
          + a 10 * b 8
  | 19 =>
      a 0 * b 19 + a 1 * b 18 + a 2 * b 17 + a 3 * b 16 + a 4 * b 15
          + a 5 * b 14 + a 6 * b 13 + a 7 * b 12 + a 8 * b 11 + a 9 * b 10
          + a 10 * b 9
  | 20 =>
      a 0 * b 20 + a 1 * b 19 + a 2 * b 18 + a 3 * b 17 + a 4 * b 16
          + a 5 * b 15 + a 6 * b 14 + a 7 * b 13 + a 8 * b 12 + a 9 * b 11
          + a 10 * b 10
  | 21 =>
      a 0 * b 21 + a 1 * b 20 + a 2 * b 19 + a 3 * b 18 + a 4 * b 17
          + a 5 * b 16 + a 6 * b 15 + a 7 * b 14 + a 8 * b 13 + a 9 * b 12
          + a 10 * b 11
  | 22 =>
      a 0 * b 22 + a 1 * b 21 + a 2 * b 20 + a 3 * b 19 + a 4 * b 18
          + a 5 * b 17 + a 6 * b 16 + a 7 * b 15 + a 8 * b 14 + a 9 * b 13
          + a 10 * b 12
  | 23 =>
      a 0 * b 23 + a 1 * b 22 + a 2 * b 21 + a 3 * b 20 + a 4 * b 19
          + a 5 * b 18 + a 6 * b 17 + a 7 * b 16 + a 8 * b 15 + a 9 * b 14
          + a 10 * b 13
  | 24 =>
      a 0 * b 24 + a 1 * b 23 + a 2 * b 22 + a 3 * b 21 + a 4 * b 20
          + a 5 * b 19 + a 6 * b 18 + a 7 * b 17 + a 8 * b 16 + a 9 * b 15
          + a 10 * b 14
  | 25 =>
      a 1 * b 24 + a 2 * b 23 + a 3 * b 22 + a 4 * b 21 + a 5 * b 20
          + a 6 * b 19 + a 7 * b 18 + a 8 * b 17 + a 9 * b 16 + a 10 * b 15
  | 26 =>
      a 2 * b 24 + a 3 * b 23 + a 4 * b 22 + a 5 * b 21 + a 6 * b 20
          + a 7 * b 19 + a 8 * b 18 + a 9 * b 17 + a 10 * b 16
  | 27 =>
      a 3 * b 24 + a 4 * b 23 + a 5 * b 22 + a 6 * b 21 + a 7 * b 20
          + a 8 * b 19 + a 9 * b 18 + a 10 * b 17
  | 28 =>
      a 4 * b 24 + a 5 * b 23 + a 6 * b 22 + a 7 * b 21 + a 8 * b 20
          + a 9 * b 19 + a 10 * b 18
  | 29 =>
      a 5 * b 24 + a 6 * b 23 + a 7 * b 22 + a 8 * b 21 + a 9 * b 20
          + a 10 * b 19
  | 30 => a 6 * b 24 + a 7 * b 23 + a 8 * b 22 + a 9 * b 21 + a 10 * b 20
  | 31 => a 7 * b 24 + a 8 * b 23 + a 9 * b 22 + a 10 * b 21
  | 32 => a 8 * b 24 + a 9 * b 23 + a 10 * b 22
  | 33 => a 9 * b 24 + a 10 * b 23
  | 34 => a 10 * b 24
  | _ => 0

def convolutionCoefficient (n : Nat) (s : ℚ) : ℚ :=
  convolutionOf (fun i => fCoefficient i s) (fun i => quotientCoefficient i s) n

def convolutionCoefficientEq (n : Nat) (s : ℚ) : Prop :=
  convolutionCoefficient n s = numeratorCoefficient n s

end MazurTorsion.Kubert.OrderTwentyFiveRelationFourCertificate.Internal

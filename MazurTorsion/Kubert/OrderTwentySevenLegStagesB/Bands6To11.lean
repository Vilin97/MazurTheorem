/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

module
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part00
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part01
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part02
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part03
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part04
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part05
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part06
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part07
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part08
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part09
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part10
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part17
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part18
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part19
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part20
public import MazurTorsion.Kubert.OrderTwentySevenLegChunks.Part21
import Mathlib.Tactic.SuppressCompilation
import Mathlib.Tactic.Ring

/-!
# Band identities 6 through 11

The second independent band identities for the trisection certificate.
-/

suppress_compilation

public section

namespace MazurTorsion.Kubert

lemma tl_band6 (f ξ : ℚ) :
    (((((tlNCbP0c6 f ξ + tlNCbP1c6 f ξ) + (tlNCbP2c6 f ξ + tlNCbP3c6 f ξ)) + ((tlNCbP4c6 f ξ +
      tlNCbP5c6 f ξ) + (tlNCbP6c5 f ξ + tlNCbP7c4 f ξ))) + (((tlNCbP8c6 f ξ + tlNCbP9c6 f ξ) +
      (tlNCbP10c6 f ξ + tlNCbP11c6 f ξ)) + ((tlNCbP12c6 f ξ + tlNCbP13c6 f ξ) + (tlNCbP14c5 f ξ +
      tlNCbP15c5 f ξ)))) + ((((tlNCbP16c4 f ξ + tlNCbP17c3 f ξ) + (tlNCbP18c6 f ξ + tlNCbP19c6 f
      ξ)) + ((tlNCbP20c6 f ξ + tlNCbP21c6 f ξ) + (tlNCbP22c6 f ξ + tlNCbP23c6 f ξ))) +
      (((tlNCbP24c5 f ξ + tlNCbP25c5 f ξ) + (tlNCbP26c4 f ξ + tlNCbP27c3 f ξ)) + ((tlNCbP28c2 f ξ
      + tlNCbP29c6 f ξ) + (tlNCbP30c6 f ξ + tlNCbP31c6 f ξ))))) + (((((tlNCbP32c6 f ξ + tlNCbP33c6
      f ξ) + (tlNCbP34c6 f ξ + tlNCbP35c5 f ξ)) + ((tlNCbP36c5 f ξ + tlNCbP37c4 f ξ) + (tlNCbP38c3
      f ξ + tlNCbP39c2 f ξ))) + (((tlNCbP40c1 f ξ + tlWTwoXP0c6 f ξ) + (tlWTwoXP1c6 f ξ +
      tlWTwoXP2c6 f ξ)) + ((tlWTwoXP3c6 f ξ + tlWOneXP0c6 f ξ) + (tlWOneXP1c6 f ξ + tlWOneXP2c6 f
      ξ)))) + (((tlWOneXP3c5 f ξ + tlWOneXP4c5 f ξ) + (tlWOneXP5c3 f ξ + tlWZeroXP0c6 f ξ)) +
      (tlWZeroXP1c5 f ξ + tlWZeroXP2c3 f ξ))) = 0 := by
  simp only [tlNCbP0c6, tlNCbP1c6, tlNCbP2c6, tlNCbP3c6, tlNCbP4c6, tlNCbP5c6, tlNCbP6c5,
      tlNCbP7c4, tlNCbP8c6, tlNCbP9c6, tlNCbP10c6, tlNCbP11c6, tlNCbP12c6,
      tlNCbP13c6, tlNCbP14c5, tlNCbP15c5, tlNCbP16c4, tlNCbP17c3, tlNCbP18c6,
      tlNCbP19c6, tlNCbP20c6, tlNCbP21c6, tlNCbP22c6, tlNCbP23c6, tlNCbP24c5,
      tlNCbP25c5, tlNCbP26c4, tlNCbP27c3, tlNCbP28c2, tlNCbP29c6, tlNCbP30c6,
      tlNCbP31c6, tlNCbP32c6, tlNCbP33c6, tlNCbP34c6, tlNCbP35c5, tlNCbP36c5,
      tlNCbP37c4, tlNCbP38c3, tlNCbP39c2, tlNCbP40c1, tlWTwoXP0c6, tlWTwoXP1c6,
      tlWTwoXP2c6, tlWTwoXP3c6, tlWOneXP0c6, tlWOneXP1c6, tlWOneXP2c6, tlWOneXP3c5,
      tlWOneXP4c5, tlWOneXP5c3, tlWZeroXP0c6, tlWZeroXP1c5, tlWZeroXP2c3]
  ring1

lemma tl_band7 (f ξ : ℚ) :
    (((((tlNCbP0c7 f ξ + tlNCbP1c7 f ξ) + (tlNCbP2c7 f ξ + tlNCbP3c7 f ξ)) + ((tlNCbP4c7 f ξ +
      tlNCbP5c7 f ξ) + (tlNCbP6c6 f ξ + tlNCbP7c5 f ξ))) + (((tlNCbP8c7 f ξ + tlNCbP9c7 f ξ) +
      (tlNCbP10c7 f ξ + tlNCbP11c7 f ξ)) + ((tlNCbP12c7 f ξ + tlNCbP13c7 f ξ) + (tlNCbP14c6 f ξ +
      tlNCbP15c6 f ξ)))) + ((((tlNCbP16c5 f ξ + tlNCbP17c4 f ξ) + (tlNCbP18c7 f ξ + tlNCbP19c7 f
      ξ)) + ((tlNCbP20c7 f ξ + tlNCbP21c7 f ξ) + (tlNCbP22c7 f ξ + tlNCbP23c7 f ξ))) +
      (((tlNCbP24c6 f ξ + tlNCbP25c6 f ξ) + (tlNCbP26c5 f ξ + tlNCbP27c4 f ξ)) + ((tlNCbP28c3 f ξ
      + tlNCbP29c7 f ξ) + (tlNCbP30c7 f ξ + tlNCbP31c7 f ξ))))) + (((((tlNCbP32c7 f ξ + tlNCbP33c7
      f ξ) + (tlNCbP34c7 f ξ + tlNCbP35c6 f ξ)) + ((tlNCbP36c6 f ξ + tlNCbP37c5 f ξ) + (tlNCbP38c4
      f ξ + tlNCbP39c3 f ξ))) + (((tlNCbP40c2 f ξ + tlWTwoXP0c7 f ξ) + (tlWTwoXP1c7 f ξ +
      tlWTwoXP2c7 f ξ)) + ((tlWTwoXP3c7 f ξ + tlWOneXP0c7 f ξ) + (tlWOneXP1c7 f ξ + tlWOneXP2c7 f
      ξ)))) + (((tlWOneXP3c6 f ξ + tlWOneXP4c6 f ξ) + (tlWOneXP5c4 f ξ + tlWZeroXP0c7 f ξ)) +
      (tlWZeroXP1c6 f ξ + tlWZeroXP2c4 f ξ))) = 0 := by
  simp only [tlNCbP0c7, tlNCbP1c7, tlNCbP2c7, tlNCbP3c7, tlNCbP4c7, tlNCbP5c7, tlNCbP6c6,
      tlNCbP7c5, tlNCbP8c7, tlNCbP9c7, tlNCbP10c7, tlNCbP11c7, tlNCbP12c7,
      tlNCbP13c7, tlNCbP14c6, tlNCbP15c6, tlNCbP16c5, tlNCbP17c4, tlNCbP18c7,
      tlNCbP19c7, tlNCbP20c7, tlNCbP21c7, tlNCbP22c7, tlNCbP23c7, tlNCbP24c6,
      tlNCbP25c6, tlNCbP26c5, tlNCbP27c4, tlNCbP28c3, tlNCbP29c7, tlNCbP30c7,
      tlNCbP31c7, tlNCbP32c7, tlNCbP33c7, tlNCbP34c7, tlNCbP35c6, tlNCbP36c6,
      tlNCbP37c5, tlNCbP38c4, tlNCbP39c3, tlNCbP40c2, tlWTwoXP0c7, tlWTwoXP1c7,
      tlWTwoXP2c7, tlWTwoXP3c7, tlWOneXP0c7, tlWOneXP1c7, tlWOneXP2c7, tlWOneXP3c6,
      tlWOneXP4c6, tlWOneXP5c4, tlWZeroXP0c7, tlWZeroXP1c6, tlWZeroXP2c4]
  ring1

lemma tl_band8 (f ξ : ℚ) :
    (((((tlNCbP0c8 f ξ + tlNCbP1c8 f ξ) + (tlNCbP2c8 f ξ + tlNCbP3c8 f ξ)) + ((tlNCbP4c8 f ξ +
      tlNCbP5c8 f ξ) + (tlNCbP6c7 f ξ + tlNCbP7c6 f ξ))) + (((tlNCbP8c8 f ξ + tlNCbP9c8 f ξ) +
      (tlNCbP10c8 f ξ + tlNCbP11c8 f ξ)) + ((tlNCbP12c8 f ξ + tlNCbP13c8 f ξ) + (tlNCbP14c7 f ξ +
      tlNCbP15c7 f ξ)))) + ((((tlNCbP16c6 f ξ + tlNCbP17c5 f ξ) + (tlNCbP18c8 f ξ + tlNCbP19c8 f
      ξ)) + ((tlNCbP20c8 f ξ + tlNCbP21c8 f ξ) + (tlNCbP22c8 f ξ + tlNCbP23c8 f ξ))) +
      (((tlNCbP24c7 f ξ + tlNCbP25c7 f ξ) + (tlNCbP26c6 f ξ + tlNCbP27c5 f ξ)) + ((tlNCbP28c4 f ξ
      + tlNCbP29c8 f ξ) + (tlNCbP30c8 f ξ + tlNCbP31c8 f ξ))))) + (((((tlNCbP32c8 f ξ + tlNCbP33c8
      f ξ) + (tlNCbP34c8 f ξ + tlNCbP35c7 f ξ)) + ((tlNCbP36c7 f ξ + tlNCbP37c6 f ξ) + (tlNCbP38c5
      f ξ + tlNCbP39c4 f ξ))) + (((tlNCbP40c3 f ξ + tlWTwoXP0c8 f ξ) + (tlWTwoXP1c8 f ξ +
      tlWTwoXP2c8 f ξ)) + ((tlWTwoXP3c8 f ξ + tlWOneXP0c8 f ξ) + (tlWOneXP1c8 f ξ + tlWOneXP2c8 f
      ξ)))) + (((tlWOneXP3c7 f ξ + tlWOneXP4c7 f ξ) + (tlWOneXP5c5 f ξ + tlWZeroXP0c8 f ξ)) +
      ((tlWZeroXP1c7 f ξ + tlWZeroXP2c5 f ξ) + tlWZeroXP3c0 f ξ))) = 0 := by
  simp only [tlNCbP0c8, tlNCbP1c8, tlNCbP2c8, tlNCbP3c8, tlNCbP4c8, tlNCbP5c8, tlNCbP6c7,
      tlNCbP7c6, tlNCbP8c8, tlNCbP9c8, tlNCbP10c8, tlNCbP11c8, tlNCbP12c8,
      tlNCbP13c8, tlNCbP14c7, tlNCbP15c7, tlNCbP16c6, tlNCbP17c5, tlNCbP18c8,
      tlNCbP19c8, tlNCbP20c8, tlNCbP21c8, tlNCbP22c8, tlNCbP23c8, tlNCbP24c7,
      tlNCbP25c7, tlNCbP26c6, tlNCbP27c5, tlNCbP28c4, tlNCbP29c8, tlNCbP30c8,
      tlNCbP31c8, tlNCbP32c8, tlNCbP33c8, tlNCbP34c8, tlNCbP35c7, tlNCbP36c7,
      tlNCbP37c6, tlNCbP38c5, tlNCbP39c4, tlNCbP40c3, tlWTwoXP0c8, tlWTwoXP1c8,
      tlWTwoXP2c8, tlWTwoXP3c8, tlWOneXP0c8, tlWOneXP1c8, tlWOneXP2c8, tlWOneXP3c7,
      tlWOneXP4c7, tlWOneXP5c5, tlWZeroXP0c8, tlWZeroXP1c7, tlWZeroXP2c5,
      tlWZeroXP3c0]
  ring1

lemma tl_band9 (f ξ : ℚ) :
    (((((tlNCbP0c9 f ξ + tlNCbP1c9 f ξ) + (tlNCbP2c9 f ξ + tlNCbP3c9 f ξ)) + ((tlNCbP4c9 f ξ +
      tlNCbP5c9 f ξ) + (tlNCbP6c8 f ξ + tlNCbP7c7 f ξ))) + (((tlNCbP8c9 f ξ + tlNCbP9c9 f ξ) +
      (tlNCbP10c9 f ξ + tlNCbP11c9 f ξ)) + ((tlNCbP12c9 f ξ + tlNCbP13c9 f ξ) + (tlNCbP14c8 f ξ +
      tlNCbP15c8 f ξ)))) + ((((tlNCbP16c7 f ξ + tlNCbP17c6 f ξ) + (tlNCbP18c9 f ξ + tlNCbP19c9 f
      ξ)) + ((tlNCbP20c9 f ξ + tlNCbP21c9 f ξ) + (tlNCbP22c9 f ξ + tlNCbP23c9 f ξ))) +
      (((tlNCbP24c8 f ξ + tlNCbP25c8 f ξ) + (tlNCbP26c7 f ξ + tlNCbP27c6 f ξ)) + ((tlNCbP28c5 f ξ
      + tlNCbP29c9 f ξ) + (tlNCbP30c9 f ξ + tlNCbP31c9 f ξ))))) + (((((tlNCbP32c9 f ξ + tlNCbP33c9
      f ξ) + (tlNCbP34c9 f ξ + tlNCbP35c8 f ξ)) + ((tlNCbP36c8 f ξ + tlNCbP37c7 f ξ) + (tlNCbP38c6
      f ξ + tlNCbP39c5 f ξ))) + (((tlNCbP40c4 f ξ + tlWTwoXP0c9 f ξ) + (tlWTwoXP1c9 f ξ +
      tlWTwoXP2c9 f ξ)) + ((tlWTwoXP3c9 f ξ + tlWOneXP0c9 f ξ) + (tlWOneXP1c9 f ξ + tlWOneXP2c9 f
      ξ)))) + (((tlWOneXP3c8 f ξ + tlWOneXP4c8 f ξ) + (tlWOneXP5c6 f ξ + tlWZeroXP0c9 f ξ)) +
      ((tlWZeroXP1c8 f ξ + tlWZeroXP2c6 f ξ) + tlWZeroXP3c1 f ξ))) = 0 := by
  simp only [tlNCbP0c9, tlNCbP1c9, tlNCbP2c9, tlNCbP3c9, tlNCbP4c9, tlNCbP5c9, tlNCbP6c8,
      tlNCbP7c7, tlNCbP8c9, tlNCbP9c9, tlNCbP10c9, tlNCbP11c9, tlNCbP12c9,
      tlNCbP13c9, tlNCbP14c8, tlNCbP15c8, tlNCbP16c7, tlNCbP17c6, tlNCbP18c9,
      tlNCbP19c9, tlNCbP20c9, tlNCbP21c9, tlNCbP22c9, tlNCbP23c9, tlNCbP24c8,
      tlNCbP25c8, tlNCbP26c7, tlNCbP27c6, tlNCbP28c5, tlNCbP29c9, tlNCbP30c9,
      tlNCbP31c9, tlNCbP32c9, tlNCbP33c9, tlNCbP34c9, tlNCbP35c8, tlNCbP36c8,
      tlNCbP37c7, tlNCbP38c6, tlNCbP39c5, tlNCbP40c4, tlWTwoXP0c9, tlWTwoXP1c9,
      tlWTwoXP2c9, tlWTwoXP3c9, tlWOneXP0c9, tlWOneXP1c9, tlWOneXP2c9, tlWOneXP3c8,
      tlWOneXP4c8, tlWOneXP5c6, tlWZeroXP0c9, tlWZeroXP1c8, tlWZeroXP2c6,
      tlWZeroXP3c1]
  ring1

lemma tl_band10 (f ξ : ℚ) :
    (((((tlNCbP0c10 f ξ + tlNCbP1c10 f ξ) + (tlNCbP2c10 f ξ + tlNCbP3c10 f ξ)) + ((tlNCbP4c10 f ξ
      + tlNCbP5c10 f ξ) + (tlNCbP6c9 f ξ + tlNCbP7c8 f ξ))) + (((tlNCbP8c10 f ξ + tlNCbP9c10 f ξ)
      + (tlNCbP10c10 f ξ + tlNCbP11c10 f ξ)) + ((tlNCbP12c10 f ξ + tlNCbP13c10 f ξ) + (tlNCbP14c9
      f ξ + tlNCbP15c9 f ξ)))) + ((((tlNCbP16c8 f ξ + tlNCbP17c7 f ξ) + (tlNCbP18c10 f ξ +
      tlNCbP19c10 f ξ)) + ((tlNCbP20c10 f ξ + tlNCbP21c10 f ξ) + (tlNCbP22c10 f ξ + tlNCbP23c10 f
      ξ))) + (((tlNCbP24c9 f ξ + tlNCbP25c9 f ξ) + (tlNCbP26c8 f ξ + tlNCbP27c7 f ξ)) +
      ((tlNCbP28c6 f ξ + tlNCbP29c10 f ξ) + (tlNCbP30c10 f ξ + tlNCbP31c10 f ξ))))) +
      (((((tlNCbP32c10 f ξ + tlNCbP33c10 f ξ) + (tlNCbP34c10 f ξ + tlNCbP35c9 f ξ)) + ((tlNCbP36c9
      f ξ + tlNCbP37c8 f ξ) + (tlNCbP38c7 f ξ + tlNCbP39c6 f ξ))) + (((tlNCbP40c5 f ξ +
      tlWTwoXP0c10 f ξ) + (tlWTwoXP1c10 f ξ + tlWTwoXP2c10 f ξ)) + ((tlWTwoXP3c10 f ξ +
      tlWOneXP0c10 f ξ) + (tlWOneXP1c10 f ξ + tlWOneXP2c10 f ξ)))) + (((tlWOneXP3c9 f ξ +
      tlWOneXP4c9 f ξ) + (tlWOneXP5c7 f ξ + tlWZeroXP0c10 f ξ)) + ((tlWZeroXP1c9 f ξ +
      tlWZeroXP2c7 f ξ) + tlWZeroXP3c2 f ξ))) = 0 := by
  simp only [tlNCbP0c10, tlNCbP1c10, tlNCbP2c10, tlNCbP3c10, tlNCbP4c10, tlNCbP5c10,
      tlNCbP6c9, tlNCbP7c8, tlNCbP8c10, tlNCbP9c10, tlNCbP10c10, tlNCbP11c10,
      tlNCbP12c10, tlNCbP13c10, tlNCbP14c9, tlNCbP15c9, tlNCbP16c8, tlNCbP17c7,
      tlNCbP18c10, tlNCbP19c10, tlNCbP20c10, tlNCbP21c10, tlNCbP22c10, tlNCbP23c10,
      tlNCbP24c9, tlNCbP25c9, tlNCbP26c8, tlNCbP27c7, tlNCbP28c6, tlNCbP29c10,
      tlNCbP30c10, tlNCbP31c10, tlNCbP32c10, tlNCbP33c10, tlNCbP34c10, tlNCbP35c9,
      tlNCbP36c9, tlNCbP37c8, tlNCbP38c7, tlNCbP39c6, tlNCbP40c5, tlWTwoXP0c10,
      tlWTwoXP1c10, tlWTwoXP2c10, tlWTwoXP3c10, tlWOneXP0c10, tlWOneXP1c10,
      tlWOneXP2c10, tlWOneXP3c9, tlWOneXP4c9, tlWOneXP5c7, tlWZeroXP0c10,
      tlWZeroXP1c9, tlWZeroXP2c7, tlWZeroXP3c2]
  ring1

lemma tl_band11 (f ξ : ℚ) :
    (((((tlNCbP1c11 f ξ + tlNCbP2c11 f ξ) + (tlNCbP3c11 f ξ + tlNCbP4c11 f ξ)) + ((tlNCbP5c11 f ξ
      + tlNCbP6c10 f ξ) + (tlNCbP7c9 f ξ + tlNCbP9c11 f ξ))) + (((tlNCbP10c11 f ξ + tlNCbP11c11 f
      ξ) + (tlNCbP12c11 f ξ + tlNCbP13c11 f ξ)) + ((tlNCbP14c10 f ξ + tlNCbP15c10 f ξ) +
      (tlNCbP16c9 f ξ + tlNCbP17c8 f ξ)))) + ((((tlNCbP19c11 f ξ + tlNCbP20c11 f ξ) + (tlNCbP21c11
      f ξ + tlNCbP22c11 f ξ)) + ((tlNCbP23c11 f ξ + tlNCbP24c10 f ξ) + (tlNCbP25c10 f ξ +
      tlNCbP26c9 f ξ))) + (((tlNCbP27c8 f ξ + tlNCbP28c7 f ξ) + (tlNCbP30c11 f ξ + tlNCbP31c11 f
      ξ)) + ((tlNCbP32c11 f ξ + tlNCbP33c11 f ξ) + (tlNCbP34c11 f ξ + tlNCbP35c10 f ξ))))) +
      (((((tlNCbP36c10 f ξ + tlNCbP37c9 f ξ) + (tlNCbP38c8 f ξ + tlNCbP39c7 f ξ)) + ((tlNCbP40c6 f
      ξ + tlWTwoXP0c11 f ξ) + (tlWTwoXP1c11 f ξ + tlWTwoXP2c11 f ξ))) + (((tlWTwoXP3c11 f ξ +
      tlWOneXP0c11 f ξ) + (tlWOneXP1c11 f ξ + tlWOneXP2c11 f ξ)) + ((tlWOneXP3c10 f ξ +
      tlWOneXP4c10 f ξ) + (tlWOneXP5c8 f ξ + tlWZeroXP0c11 f ξ)))) + ((tlWZeroXP1c10 f ξ +
      tlWZeroXP2c8 f ξ) + tlWZeroXP3c3 f ξ)) = 0 := by
  simp only [tlNCbP1c11, tlNCbP2c11, tlNCbP3c11, tlNCbP4c11, tlNCbP5c11, tlNCbP6c10,
      tlNCbP7c9, tlNCbP9c11, tlNCbP10c11, tlNCbP11c11, tlNCbP12c11, tlNCbP13c11,
      tlNCbP14c10, tlNCbP15c10, tlNCbP16c9, tlNCbP17c8, tlNCbP19c11, tlNCbP20c11,
      tlNCbP21c11, tlNCbP22c11, tlNCbP23c11, tlNCbP24c10, tlNCbP25c10, tlNCbP26c9,
      tlNCbP27c8, tlNCbP28c7, tlNCbP30c11, tlNCbP31c11, tlNCbP32c11, tlNCbP33c11,
      tlNCbP34c11, tlNCbP35c10, tlNCbP36c10, tlNCbP37c9, tlNCbP38c8, tlNCbP39c7,
      tlNCbP40c6, tlWTwoXP0c11, tlWTwoXP1c11, tlWTwoXP2c11, tlWTwoXP3c11,
      tlWOneXP0c11, tlWOneXP1c11, tlWOneXP2c11, tlWOneXP3c10, tlWOneXP4c10,
      tlWOneXP5c8, tlWZeroXP0c11, tlWZeroXP1c10, tlWZeroXP2c8, tlWZeroXP3c3]
  ring1


end MazurTorsion.Kubert

end

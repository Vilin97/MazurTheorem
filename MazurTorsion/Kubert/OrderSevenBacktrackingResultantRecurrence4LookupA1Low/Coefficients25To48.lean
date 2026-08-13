/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData4
import Mathlib.Tactic.NormNum

/-!
# Recurrence 4 lookup certificate: A1 source coefficients, low half

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence4A1_coeff_25 :
    remainder4Coefficient1.coeff 25 =
      (-2440782889814689114143345791756460874707886213473249228266 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_26 :
    remainder4Coefficient1.coeff 26 =
      (71611976960909361709623286107178577864223922136607516429486 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_27 :
    remainder4Coefficient1.coeff 27 =
      (-1910893655236790414036807360120439706498056222349982999372260 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_28 :
    remainder4Coefficient1.coeff 28 =
      (46544511128236073210085191888112542851680838041596196178995233 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_29 :
    remainder4Coefficient1.coeff 29 =
      (-1038382401547817885136538493771201872301813264476381906664283005 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_30 :
    remainder4Coefficient1.coeff 30 =
      (21285255821139194749000870147779267836589650298476565440425515592 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_31 :
    remainder4Coefficient1.coeff 31 =
      (-402085487617173171346990294959042376926569851681638036112426825704 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_32 :
    remainder4Coefficient1.coeff 32 =
      (7019056457487341598636866118648688426911261501437102308811044247647 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_33 :
    remainder4Coefficient1.coeff 33 =
      (-113523928149350087463274312433599322256128549853878190619109597165150 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_34 :
    remainder4Coefficient1.coeff 34 =
      (1705308121530463853100420746914649885839122515704567802777551156880432 : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_35 :
    remainder4Coefficient1.coeff 35 =
      -((2 * 10 ^ 70 +
        3846242155032942185219835867887039027276005848195794060774553771719276) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_36 :
    remainder4Coefficient1.coeff 36 =
      ((31 * 10 ^ 70 +
        1081990263117924439353141722672607209777681404731533157872778141782439) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_37 :
    remainder4Coefficient1.coeff 37 =
      -((379 * 10 ^ 70 +
        3582370910840075862409938468717334008044243103250093032519498845893707) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_38 :
    remainder4Coefficient1.coeff 38 =
      ((4332 * 10 ^ 70 +
        8679102116464914644499967959765679694413608273947868630111004415558231) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_39 :
    remainder4Coefficient1.coeff 39 =
      -((46434 * 10 ^ 70 +
        1412824802207795165982896394565698905327169863766004237044652872787051) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_40 :
    remainder4Coefficient1.coeff 40 =
      ((467709 * 10 ^ 70 +
        9489640300693453277827296233261471078251682098182814108216217126233074) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_41 :
    remainder4Coefficient1.coeff 41 =
      -((4434999 * 10 ^ 70 +
        3169001452735916826949746261266378307625072208658338631430722105224758) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_42 :
    remainder4Coefficient1.coeff 42 =
      ((39650697 * 10 ^ 70 +
        4715509006355921014001756983287399272159843432897646526140258307256269) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_43 :
    remainder4Coefficient1.coeff 43 =
      -((334715223 * 10 ^ 70 +
        1218939706398567819690138921574942427585452799742893316378194253424408) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_44 :
    remainder4Coefficient1.coeff 44 =
      ((2671537060 * 10 ^ 70 +
        2051296174841611855241922811619513307918884962763545869732363137094506) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_45 :
    remainder4Coefficient1.coeff 45 =
      -((20186943079 * 10 ^ 70 +
        0592368397514798445235365221231949766144764030429083619970355494260923) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_46 :
    remainder4Coefficient1.coeff 46 =
      ((144589483213 * 10 ^ 70 +
        8634850830470801259681251655578745859131861940650802324456658941038276) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_47 :
    remainder4Coefficient1.coeff 47 =
      -((982800184742 * 10 ^ 70 +
        4781282784301230391310291474605166532410612621780784206841688976628421) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A1_coeff_48 :
    remainder4Coefficient1.coeff 48 =
      ((6346521276594 * 10 ^ 70 +
        5515894754749045243451932014894939781253382315596239544403847447594929) : ℚ) := by
  unfold
    remainder4Coefficient1
    remainder4Coefficient1Block1
    remainder4Coefficient1Block0
    remainder4Coefficient1Chunk23
    remainder4Coefficient1Chunk22
    remainder4Coefficient1Chunk21
    remainder4Coefficient1Chunk20
    remainder4Coefficient1Chunk19
    remainder4Coefficient1Chunk18
    remainder4Coefficient1Chunk17
    remainder4Coefficient1Chunk16
    remainder4Coefficient1Chunk15
    remainder4Coefficient1Chunk14
    remainder4Coefficient1Chunk13
    remainder4Coefficient1Chunk12
    remainder4Coefficient1Chunk11
    remainder4Coefficient1Chunk10
    remainder4Coefficient1Chunk9
    remainder4Coefficient1Chunk8
    remainder4Coefficient1Chunk7
    remainder4Coefficient1Chunk6
    remainder4Coefficient1Chunk5
    remainder4Coefficient1Chunk4
    remainder4Coefficient1Chunk3
    remainder4Coefficient1Chunk2
    remainder4Coefficient1Chunk1
    remainder4Coefficient1Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

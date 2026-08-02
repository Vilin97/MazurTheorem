/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData2
import Mathlib.Tactic.NormNum

/-!
# Recurrence 2 lookup certificate: A4 source coefficients, high half

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2A4_coeff_52 :
    remainder2Coefficient4.coeff 52 =
      (58164678579912948160930285935213101064005480685185 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_53 :
    remainder2Coefficient4.coeff 53 =
      (320673134121474499950016185509383657477202553957550 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_54 :
    remainder2Coefficient4.coeff 54 =
      (-966410230161405973775927755796471384338588517172481 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_55 :
    remainder2Coefficient4.coeff 55 =
      (1057521205019777592525830018825566490236496451057365 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_56 :
    remainder2Coefficient4.coeff 56 =
      (742127755010771180546078381774652053372379927188243 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_57 :
    remainder2Coefficient4.coeff 57 =
      (-4785959974880926339643565685229096339862358294612527 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_58 :
    remainder2Coefficient4.coeff 58 =
      (8760490003044905330957105454623115941276373458917434 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_59 :
    remainder2Coefficient4.coeff 59 =
      (-8203512958915321638917069527219780641033470636605772 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_60 :
    remainder2Coefficient4.coeff 60 =
      (124873650185766338123408195979723000643560020942470 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_61 :
    remainder2Coefficient4.coeff 61 =
      (13137889188370020679157083869417823052352801227592109 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_62 :
    remainder2Coefficient4.coeff 62 =
      (-24260889690025450128779071629645492560555871074703942 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_63 :
    remainder2Coefficient4.coeff 63 =
      (26214602613453567649132125504002244590507094605348433 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_64 :
    remainder2Coefficient4.coeff 64 =
      (-17819254933458328320669253465733783739288751672154723 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_65 :
    remainder2Coefficient4.coeff 65 =
      (4325601937530417313343374923753902307504119361121808 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_66 :
    remainder2Coefficient4.coeff 66 =
      (7085160897111292059077791287867026927987327952014566 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_67 :
    remainder2Coefficient4.coeff 67 =
      (-12241834034897506887363455958967121012693100190156582 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_68 :
    remainder2Coefficient4.coeff 68 =
      (11415768083294728785940734875671568824441361346817452 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_69 :
    remainder2Coefficient4.coeff 69 =
      (-7445759028232835325223788537982047007543276937229425 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_70 :
    remainder2Coefficient4.coeff 70 =
      (3219440258276007637241900872819713062091450575441678 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_71 :
    remainder2Coefficient4.coeff 71 =
      (-355308909916774060665370153856512577405243427200776 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_72 :
    remainder2Coefficient4.coeff 72 =
      (-855610967830138214679424247973466442497801794595178 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_73 :
    remainder2Coefficient4.coeff 73 =
      (919773290386774278560369110956023102289357227011826 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_74 :
    remainder2Coefficient4.coeff 74 =
      (-535092720771623363396985167307577928365692065974083 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_75 :
    remainder2Coefficient4.coeff 75 =
      (180092494351645424091732349753438665506657826740768 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_76 :
    remainder2Coefficient4.coeff 76 =
      (-8425469595670461199404319368098727400289044590510 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_77 :
    remainder2Coefficient4.coeff 77 =
      (-28226822940414173111034757461886101215568527671949 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_78 :
    remainder2Coefficient4.coeff 78 =
      (16873132029904715975144283624084105259274856352785 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_79 :
    remainder2Coefficient4.coeff 79 =
      (-4470227893646445815672202856041563204717756135371 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_80 :
    remainder2Coefficient4.coeff 80 =
      (41103553665028866702092783573336178371067872994 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_81 :
    remainder2Coefficient4.coeff 81 =
      (391988867676424019441773103447860968897246402867 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_82 :
    remainder2Coefficient4.coeff 82 =
      (-125515986126920090053261260794941424373115036152 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_83 :
    remainder2Coefficient4.coeff 83 =
      (8766011014486695941776157846266783124975520055 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_84 :
    remainder2Coefficient4.coeff 84 =
      (4405610885467658215728651561274847243551785183 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_85 :
    remainder2Coefficient4.coeff 85 =
      (-1108541808326678930214575740370730576125023045 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_86 :
    remainder2Coefficient4.coeff 86 =
      (1168967674723539927797550980063930000826216 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_87 :
    remainder2Coefficient4.coeff 87 =
      (28253243546566767172168785893940385861585496 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_88 :
    remainder2Coefficient4.coeff 88 =
      (-1543504786611669941401850724286147096140207 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_89 :
    remainder2Coefficient4.coeff 89 =
      (-403947522433154763994537377347421116546424 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_90 :
    remainder2Coefficient4.coeff 90 =
      (12319330366236617959699752080407913790123 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_91 :
    remainder2Coefficient4.coeff 91 =
      (3998392909408417154375212108573971126095 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_92 :
    remainder2Coefficient4.coeff 92 =
      (220383357605673005449700582181334082101 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_93 :
    remainder2Coefficient4.coeff 93 =
      (5397653765049896892328607975682692166 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_94 :
    remainder2Coefficient4.coeff 94 =
      (65698345123983352604138413107212789 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_95 :
    remainder2Coefficient4.coeff 95 =
      (390118339111116952445252584220795 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_96 :
    remainder2Coefficient4.coeff 96 =
      (939164548290806025064203691306 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_97 :
    remainder2Coefficient4.coeff 97 =
      (-215132251974574146416121296 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_98 :
    remainder2Coefficient4.coeff 98 =
      (-3936944843241963325483716 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_99 :
    remainder2Coefficient4.coeff 99 =
      (-3878580211389726856884 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_100 :
    remainder2Coefficient4.coeff 100 =
      (-755768532071763755 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_101 :
    remainder2Coefficient4.coeff 101 =
      (-16728815392683 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2A4_coeff_102 :
    remainder2Coefficient4.coeff 102 =
      (-9250026 : ℚ) := by
  unfold
    remainder2Coefficient4
    remainder2Coefficient4Block1
    remainder2Coefficient4Block0
    remainder2Coefficient4Chunk12
    remainder2Coefficient4Chunk11
    remainder2Coefficient4Chunk10
    remainder2Coefficient4Chunk9
    remainder2Coefficient4Chunk8
    remainder2Coefficient4Chunk7
    remainder2Coefficient4Chunk6
    remainder2Coefficient4Chunk5
    remainder2Coefficient4Chunk4
    remainder2Coefficient4Chunk3
    remainder2Coefficient4Chunk2
    remainder2Coefficient4Chunk1
    remainder2Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

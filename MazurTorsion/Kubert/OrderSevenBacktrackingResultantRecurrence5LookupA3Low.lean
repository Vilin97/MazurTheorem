/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData5
import Mathlib.Tactic.NormNum

/-!
# Recurrence 5 lookup certificate: A3 source coefficients, low half

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence5A3_coeff_0 :
    remainder5Coefficient3.coeff 0 =
      (44628871650183547488 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_1 :
    remainder5Coefficient3.coeff 1 =
      (-101240104527640512674952 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_2 :
    remainder5Coefficient3.coeff 2 =
      (87557480293910528383866378 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_3 :
    remainder5Coefficient3.coeff 3 =
      (-17874654837571402443629296374 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_4 :
    remainder5Coefficient3.coeff 4 =
      (5792348008208369009856522675166 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_5 :
    remainder5Coefficient3.coeff 5 =
      (-3806052411410356690277128193857762 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_6 :
    remainder5Coefficient3.coeff 6 =
      (794138340736874213339747440019444146 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_7 :
    remainder5Coefficient3.coeff 7 =
      (459572625303106389282958919799380335773 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_8 :
    remainder5Coefficient3.coeff 8 =
      (-358577994602045914617846182412852893324183 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_9 :
    remainder5Coefficient3.coeff 9 =
      (117453494423525901032793741396672926492322148 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_10 :
    remainder5Coefficient3.coeff 10 =
      (-23256833699296850816234761216087472158657143063 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_11 :
    remainder5Coefficient3.coeff 11 =
      (2945773668955325960286820698289656482971377267830 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_12 :
    remainder5Coefficient3.coeff 12 =
      (-213822084719556136916781023460835071703455272203752 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_13 :
    remainder5Coefficient3.coeff 13 =
      (638886660829311632136262248982227233100505496765003 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_14 :
    remainder5Coefficient3.coeff 14 =
      (2040033871472087327222112859996188953567916500121335778 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_15 :
    remainder5Coefficient3.coeff 15 =
      (-303356374870980680186516623408014726166869672865918546455 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_16 :
    remainder5Coefficient3.coeff 16 =
      (27730199851722782796550094216799884647900218900608773236702 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_17 :
    remainder5Coefficient3.coeff 17 =
      (-1880852812837032786044553218841490043822390045096627260650327 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_18 :
    remainder5Coefficient3.coeff 18 =
      (100864985408863943121681035028321503095156460571072129419339276 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_19 :
    remainder5Coefficient3.coeff 19 =
      (-4410561464911732753207669038807696428063173251376098165235630603 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_20 :
    remainder5Coefficient3.coeff 20 =
      (159958046781633673359015285134972040331564158001488513695799457938 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_21 :
    remainder5Coefficient3.coeff 21 =
      (-4852920224108041789164917886602639001013879859584390128251128829788 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_22 :
    remainder5Coefficient3.coeff 22 =
      (123257136392501107939563763872623318895344303785687679174999064768092 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_23 :
    remainder5Coefficient3.coeff 23 =
      (-2593243379732581424840542851652796204036169948577154626758769763893779 : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_24 :
    remainder5Coefficient3.coeff 24 =
      ((4 * 10 ^ 70 +
        3639508018785041573247180859238733990704107143751221924005819018214348) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_25 :
    remainder5Coefficient3.coeff 25 =
      -((52 * 10 ^ 70 +
        2794408701580335029475811808443136074388803142042355658886481700668681) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_26 :
    remainder5Coefficient3.coeff 26 =
      ((191 * 10 ^ 70 +
        0800112660215775106529785918169646466978923319780337901262085447916480) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_27 :
    remainder5Coefficient3.coeff 27 =
      ((11141 * 10 ^ 70 +
        3511849857216329474832474685406054859943744049806329572261682694130480) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_28 :
    remainder5Coefficient3.coeff 28 =
      -((407290 * 10 ^ 70 +
        3045987907383496458581635985232366476277965491894248531863059559825720) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_29 :
    remainder5Coefficient3.coeff 29 =
      ((9217574 * 10 ^ 70 +
        9135549243686721976790272765036986315615762241351172599843197969659141) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_30 :
    remainder5Coefficient3.coeff 30 =
      -((165739073 * 10 ^ 70 +
        8393178619170115022086353822073760034466568321710302299436160939754865) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_31 :
    remainder5Coefficient3.coeff 31 =
      ((2540769236 * 10 ^ 70 +
        2737971722656249732995630127499560807923539459419138645281364863186103) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_32 :
    remainder5Coefficient3.coeff 32 =
      -((34270630597 * 10 ^ 70 +
        5260375396576147330082376590665487935628609878541057979824300840798187) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_33 :
    remainder5Coefficient3.coeff 33 =
      ((413968417707 * 10 ^ 70 +
        0768159759312506681994710158431281578805781514805631149378436838856709) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_34 :
    remainder5Coefficient3.coeff 34 =
      -((4529547653390 * 10 ^ 70 +
        1180946419997081820169868900828037856659224689506173041399967110786179) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_35 :
    remainder5Coefficient3.coeff 35 =
      ((45259190598688 * 10 ^ 70 +
        8705858952268869282324877065553902415677684874140261754770859710778076) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_36 :
    remainder5Coefficient3.coeff 36 =
      -((415529713467702 * 10 ^ 70 +
        2256702769604287657926372522304740296578776848683506033533823842366501) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_37 :
    remainder5Coefficient3.coeff 37 =
      ((3522738397409662 * 10 ^ 70 +
        4016765220425349130370239446390403149450876222015931131791111769436942) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_38 :
    remainder5Coefficient3.coeff 38 =
      -((27689309725903479 * 10 ^ 70 +
        1961743517649459054498191698281766604177925978164467786718202996985242) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_39 :
    remainder5Coefficient3.coeff 39 =
      ((202488576089517049 * 10 ^ 70 +
        1696255787168471123939034187087325004894994085022988928254956506980802) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_40 :
    remainder5Coefficient3.coeff 40 =
      -((1381803467072592727 * 10 ^ 70 +
        7086368517291335988072343009157215537630642398269828330309867435445702) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_41 :
    remainder5Coefficient3.coeff 41 =
      ((8822474274536780436 * 10 ^ 70 +
        4990974459380609890451868111985563423608624364041208087612101263072947) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_42 :
    remainder5Coefficient3.coeff 42 =
      -((52825521249394570211 * 10 ^ 70 +
        4615331109661900485788728582253642400579556475127797217417838636669950) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_43 :
    remainder5Coefficient3.coeff 43 =
      ((297240737775830770274 * 10 ^ 70 +
        9160458132610332085770345246328111212309508165290986148828927357884739) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_44 :
    remainder5Coefficient3.coeff 44 =
      -((1574680488576089355221 * 10 ^ 70 +
        4523281339076651529136900701325305605349286265756642418669605000989285) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_45 :
    remainder5Coefficient3.coeff 45 =
      ((7867249852070201216064 * 10 ^ 70 +
        4582835354055577965000807081833002153251072128419035711651336086330043) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_46 :
    remainder5Coefficient3.coeff 46 =
      -((37123957959450155191197 * 10 ^ 70 +
        5760124693843893992999240140695448580657861924359895389868942142704525) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_47 :
    remainder5Coefficient3.coeff 47 =
      ((165682260176268317782593 * 10 ^ 70 +
        3301302915762501451795128919014615783043301872209447394357760640162962) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_48 :
    remainder5Coefficient3.coeff 48 =
      -((700195090778100769094274 * 10 ^ 70 +
        8961002776286462335460067580822388325139769117933516121830207390101326) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_49 :
    remainder5Coefficient3.coeff 49 =
      ((2805181297952191698703511 * 10 ^ 70 +
        4776570915940082225965402050322675838233111360589180583551808423453981) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_50 :
    remainder5Coefficient3.coeff 50 =
      -((10664250381209080862072008 * 10 ^ 70 +
        2326907715331445896771055055246870257405639879221159800257161159462394) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_51 :
    remainder5Coefficient3.coeff 51 =
      ((38504475019789786704776645 * 10 ^ 70 +
        8983006396996869648774868427255246670954591488729041129914535157342160) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_52 :
    remainder5Coefficient3.coeff 52 =
      -((132143671912190097130357614 * 10 ^ 70 +
        4292946229161457166517579558328668493992549462154369996659440440454057) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_53 :
    remainder5Coefficient3.coeff 53 =
      ((431360872159782438654316825 * 10 ^ 70 +
        8036234880811649746678849258530024470712135587579214664102542225019780) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_54 :
    remainder5Coefficient3.coeff 54 =
      -((1340183506109571497063902606 * 10 ^ 70 +
        2376382648473338818437309227430397538446428911475890408860555908029445) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_55 :
    remainder5Coefficient3.coeff 55 =
      ((3965102563816793613007104873 * 10 ^ 70 +
        7669836139003918374109012278136128989120729332211179373540528643837118) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_56 :
    remainder5Coefficient3.coeff 56 =
      -((11176826442697718790593752299 * 10 ^ 70 +
        5434698714825192511936337469587818835461986256407366175319783321875354) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_57 :
    remainder5Coefficient3.coeff 57 =
      ((30028626859400933284660010329 * 10 ^ 70 +
        2821577589971645848195152637548155203957977694406158654881782336323996) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_58 :
    remainder5Coefficient3.coeff 58 =
      -((76923222386908198612469439296 * 10 ^ 70 +
        0003341194214874610232811023433697815611875690756115326982193355517231) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_59 :
    remainder5Coefficient3.coeff 59 =
      ((187936418308826523724173820517 * 10 ^ 70 +
        3245106368782011791923298190367214568750222911985006402781060698683424) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_60 :
    remainder5Coefficient3.coeff 60 =
      -((438023451097027151791482911844 * 10 ^ 70 +
        7730213746101738616011029091076778232278377432590124436548815285823537) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_61 :
    remainder5Coefficient3.coeff 61 =
      ((974077291448852087966243994640 * 10 ^ 70 +
        8619478279412257834487582460082751292906198899490640198705715130289422) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_62 :
    remainder5Coefficient3.coeff 62 =
      -((2067048972359633442255109285324 * 10 ^ 70 +
        6305738516992480214451493913560409004826797519381376076376508744007102) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_63 :
    remainder5Coefficient3.coeff 63 =
      ((4185960399566808657599633892773 * 10 ^ 70 +
        0447811639384939185270759361273199707590360886771823322064469177780768) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_64 :
    remainder5Coefficient3.coeff 64 =
      -((8089554946889475071618186414570 * 10 ^ 70 +
        1895120309868715185005122925394629156628694877375415094607516245733311) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_65 :
    remainder5Coefficient3.coeff 65 =
      ((14917891086999057645249953472131 * 10 ^ 70 +
        7182661947196199063760607425716135498471289896763515264000941677838133) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_66 :
    remainder5Coefficient3.coeff 66 =
      -((26246899527128897795645212887958 * 10 ^ 70 +
        3583827882949268707360638022258960270588776673077786299802417875371295) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_67 :
    remainder5Coefficient3.coeff 67 =
      ((44048603046095353377532741500233 * 10 ^ 70 +
        4110620260441435799385807582797872265380934413664318372670975578709411) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_68 :
    remainder5Coefficient3.coeff 68 =
      -((70488758504919722125862871750294 * 10 ^ 70 +
        5797899621271760029891666424743278626201206348764449607413507104102322) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_69 :
    remainder5Coefficient3.coeff 69 =
      ((107506734088341871590558360622254 * 10 ^ 70 +
        5853391154416279115576164407500622941278008186419272679752691266609818) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_70 :
    remainder5Coefficient3.coeff 70 =
      -((156172567192240961368311352868088 * 10 ^ 70 +
        0832188305485343202405222131616440113529551191027063581008026694684880) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_71 :
    remainder5Coefficient3.coeff 71 =
      ((215905312135622316386388829973640 * 10 ^ 70 +
        4150111837670667056683079682540821233822168908662523663492426956798173) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_72 :
    remainder5Coefficient3.coeff 72 =
      -((283746138931585440565379915717879 * 10 ^ 70 +
        7009736779007018113494667782115832625249975579570903766136417339645489) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_73 :
    remainder5Coefficient3.coeff 73 =
      ((353966701013215527976567122246798 * 10 ^ 70 +
        9475444560026207689510546158924523244269220605787077959012473179569303) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_74 :
    remainder5Coefficient3.coeff 74 =
      -((418302556100057284066113364708798 * 10 ^ 70 +
        3368134098031839614036812729567800301335034507507892651867841021289729) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_75 :
    remainder5Coefficient3.coeff 75 =
      ((466989545386178572791198025680847 * 10 ^ 70 +
        4618926056407144463538334815773833405340377379702610354691358391129612) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_76 :
    remainder5Coefficient3.coeff 76 =
      -((490547659350129264547771562843313 * 10 ^ 70 +
        5765235804124122310591950203756087085187378185536250437642820594675614) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_77 :
    remainder5Coefficient3.coeff 77 =
      ((481963803343730379591219664934208 * 10 ^ 70 +
        0797713169024014102697671774008190735681225826766876223926065977504657) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_78 :
    remainder5Coefficient3.coeff 78 =
      -((438685785455757082394429316503438 * 10 ^ 70 +
        9971832649563398329956573298717006220741802878350499538441111088018414) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_79 :
    remainder5Coefficient3.coeff 79 =
      ((363776410241906267150856140275008 * 10 ^ 70 +
        3666959042408336993729472472236887947459308342183623692484889321248307) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_80 :
    remainder5Coefficient3.coeff 80 =
      -((265756197179930269188800932349881 * 10 ^ 70 +
        7855889992975456826301417432471310176545788550286663062198216203431520) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_81 :
    remainder5Coefficient3.coeff 81 =
      ((157051856645012416764023332324660 * 10 ^ 70 +
        8861731037690843658743470204948967759312879879751776858305124001783265) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence5A3_coeff_82 :
    remainder5Coefficient3.coeff 82 =
      -((51428654316374346130452468229279 * 10 ^ 70 +
        5177134521289598425608709100741533805154815794406205125847464435015873) : ℚ) := by
  unfold
    remainder5Coefficient3
    remainder5Coefficient3Block1
    remainder5Coefficient3Block0
    remainder5Coefficient3Chunk20
    remainder5Coefficient3Chunk19
    remainder5Coefficient3Chunk18
    remainder5Coefficient3Chunk17
    remainder5Coefficient3Chunk16
    remainder5Coefficient3Chunk15
    remainder5Coefficient3Chunk14
    remainder5Coefficient3Chunk13
    remainder5Coefficient3Chunk12
    remainder5Coefficient3Chunk11
    remainder5Coefficient3Chunk10
    remainder5Coefficient3Chunk9
    remainder5Coefficient3Chunk8
    remainder5Coefficient3Chunk7
    remainder5Coefficient3Chunk6
    remainder5Coefficient3Chunk5
    remainder5Coefficient3Chunk4
    remainder5Coefficient3Chunk3
    remainder5Coefficient3Chunk2
    remainder5Coefficient3Chunk1
    remainder5Coefficient3Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

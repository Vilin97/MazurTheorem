/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData2
import Mathlib.Tactic.NormNum

/-!
# Recurrence 2 lookup certificate: C2 source coefficients, low half

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence2C2_coeff_48 :
    remainder4Coefficient2.coeff 48 =
      ((10656141591253 * 10 ^ 70 +
        0388736594233790307679285788639835123700399110820348711834784139946210) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_49 :
    remainder4Coefficient2.coeff 49 =
      -((62828644072256 * 10 ^ 70 +
        4372221074878478319663331087712869600443498394183629209322141957220871) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_50 :
    remainder4Coefficient2.coeff 50 =
      ((352750445912482 * 10 ^ 70 +
        8133320043293001879892906443836767458358775472717950775576274049273412) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_51 :
    remainder4Coefficient2.coeff 51 =
      -((1887674865668027 * 10 ^ 70 +
        3205647851608673811072682858565939327139301575123805574631489506014132) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_52 :
    remainder4Coefficient2.coeff 52 =
      ((9636385934816933 * 10 ^ 70 +
        1004485810552715227163237389300311685144067034040308815989435281077356) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_53 :
    remainder4Coefficient2.coeff 53 =
      -((46966405385741741 * 10 ^ 70 +
        3368351807891529581108980668168416776785878007589101027058749348241794) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_54 :
    remainder4Coefficient2.coeff 54 =
      ((218719506213624762 * 10 ^ 70 +
        1427064741214456220758710836272029834510901805363754100951499846177369) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_55 :
    remainder4Coefficient2.coeff 55 =
      -((973954659731464715 * 10 ^ 70 +
        8648378262686849800818103444677813569226336057558089742588288155163844) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_56 :
    remainder4Coefficient2.coeff 56 =
      ((4150007509834221740 * 10 ^ 70 +
        3680147496646869493094372101595165010823405888385624326657738585175024) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_57 :
    remainder4Coefficient2.coeff 57 =
      -((16932089581160756195 * 10 ^ 70 +
        6785742371007369644483548852057274836126980165944762473991987035413858) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_58 :
    remainder4Coefficient2.coeff 58 =
      ((66191442280922050599 * 10 ^ 70 +
        8224800097474783918835593992977463016985735798888404218072789683943778) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_59 :
    remainder4Coefficient2.coeff 59 =
      -((248077277567451272603 * 10 ^ 70 +
        3346179085935314668915769646020135962083482309196217859589315964566200) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_60 :
    remainder4Coefficient2.coeff 60 =
      ((891901810636039035903 * 10 ^ 70 +
        8487649127147390305761838732234926072901701483960436358593955270941114) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_61 :
    remainder4Coefficient2.coeff 61 =
      -((3077729878565279932698 * 10 ^ 70 +
        7273893010823505062771513497221044900781778745877849746532495811320130) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_62 :
    remainder4Coefficient2.coeff 62 =
      ((10198911517450411867818 * 10 ^ 70 +
        8265611275741086766571688033292335826059259129676171535618569719932037) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_63 :
    remainder4Coefficient2.coeff 63 =
      -((32471474340401189655587 * 10 ^ 70 +
        7155563488039607472355536975006636679594949551017189553984374588390709) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_64 :
    remainder4Coefficient2.coeff 64 =
      ((99375439441874071090678 * 10 ^ 70 +
        8461293322277674844128970662024087483488231093300220474004635214731074) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_65 :
    remainder4Coefficient2.coeff 65 =
      -((292468083468597291561124 * 10 ^ 70 +
        3609126573313260397542941078657176225738049308901941379015695880819701) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_66 :
    remainder4Coefficient2.coeff 66 =
      ((828101686947707215193765 * 10 ^ 70 +
        5911106606954355052514843137822270941059516961744390602789408673771650) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_67 :
    remainder4Coefficient2.coeff 67 =
      -((2256671628369314291976269 * 10 ^ 70 +
        7518287981461960451834270808873875619044106360371072603386115313764921) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_68 :
    remainder4Coefficient2.coeff 68 =
      ((5921026740809069934994780 * 10 ^ 70 +
        2423313928314391663721331837469721046736187553438976299543737136728616) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_69 :
    remainder4Coefficient2.coeff 69 =
      -((14963222798095145602913718 * 10 ^ 70 +
        0606635211617287637954181092775888903559699432864573765820471597929886) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_70 :
    remainder4Coefficient2.coeff 70 =
      ((36433395279547574999232290 * 10 ^ 70 +
        7106778035948051559467320724861525528262376576186578361319515661870036) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_71 :
    remainder4Coefficient2.coeff 71 =
      -((85498632699300719803348288 * 10 ^ 70 +
        0502365132423169332523310590882918208689262171156245731532508319439615) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_72 :
    remainder4Coefficient2.coeff 72 =
      ((193434693770070372008240833 * 10 ^ 70 +
        7223743874277185834401683657197060963104143382786898758820798983698851) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_73 :
    remainder4Coefficient2.coeff 73 =
      -((422034741013949425480939590 * 10 ^ 70 +
        1148001564088970089038787852206353993115811085787084360170381512928960) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_74 :
    remainder4Coefficient2.coeff 74 =
      ((888211074294128082329361588 * 10 ^ 70 +
        0373373889415502999932613975650630861745995507045417387700964281867362) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_75 :
    remainder4Coefficient2.coeff 75 =
      -((1803626641255156282950351649 * 10 ^ 70 +
        7383993496191666320846231917583198181561309070525628661977132698390120) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_76 :
    remainder4Coefficient2.coeff 76 =
      ((3534605514705894813177772723 * 10 ^ 70 +
        3474278013192487099134756130163153669711824799115428733409238479196973) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_77 :
    remainder4Coefficient2.coeff 77 =
      -((6686421551978203422996160975 * 10 ^ 70 +
        8224803949331496788189400204802888991817907542481725736055939187704901) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_78 :
    remainder4Coefficient2.coeff 78 =
      ((12212179305057105926541068046 * 10 ^ 70 +
        7956950583533818323380669662812983585593684234675443721969063703637986) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_79 :
    remainder4Coefficient2.coeff 79 =
      -((21538775393854985404213127596 * 10 ^ 70 +
        1574061195061056555166692664129199622093659264106934117043743125237880) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_80 :
    remainder4Coefficient2.coeff 80 =
      ((36690440903384647644763931966 * 10 ^ 70 +
        2927974378790342185073919586757118861297427876283524256255084729818174) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_81 :
    remainder4Coefficient2.coeff 81 =
      -((60375211521786864465868451615 * 10 ^ 70 +
        1200740790114727420822655729345957748755141536965846498325660566273595) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_82 :
    remainder4Coefficient2.coeff 82 =
      ((95984733268740667568953764596 * 10 ^ 70 +
        8450310900226297748472655474363391638912942693374688475488241118018005) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_83 :
    remainder4Coefficient2.coeff 83 =
      -((147448978675660617338157549656 * 10 ^ 70 +
        6396784075936960116521968124698124445780037675371462894761876966470162) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_84 :
    remainder4Coefficient2.coeff 84 =
      ((218892252433145884291542309621 * 10 ^ 70 +
        2554568569882908791278909871983891823874436530448808342861587660505699) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_85 :
    remainder4Coefficient2.coeff 85 =
      -((314062187206594230587038850414 * 10 ^ 70 +
        3014145178409502194934683165199900636416263404022746489263071046526215) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_86 :
    remainder4Coefficient2.coeff 86 =
      ((435552036027729819824764840679 * 10 ^ 70 +
        7307554567999191950821442201508489032820912197449449474447902954506351) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_87 :
    remainder4Coefficient2.coeff 87 =
      -((583903538059132727089209263241 * 10 ^ 70 +
        7412519662542313947483600507328704891912320718414589915683415857935327) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_88 :
    remainder4Coefficient2.coeff 88 =
      ((756748433199527775844580598249 * 10 ^ 70 +
        3854960037548204726401879001103135132298619969125831139530899088068468) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_89 :
    remainder4Coefficient2.coeff 89 =
      -((948198698086687502385996383951 * 10 ^ 70 +
        6077410535422110262749055797820823441908047011301749945288814607788429) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_90 :
    remainder4Coefficient2.coeff 90 =
      ((1148703911544035274752762430256 * 10 ^ 70 +
        5126901497616571146657109744611313294923879027151200572884000115715139) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_91 :
    remainder4Coefficient2.coeff 91 =
      -((1345540973618139205350386177161 * 10 ^ 70 +
        8492342642518286104420303234204772726985976545847068312851787136043423) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_92 :
    remainder4Coefficient2.coeff 92 =
      ((1523985366802048875101310630457 * 10 ^ 70 +
        0450159015511582268803776589428910216084561837992394568837912577020244) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence2C2_coeff_93 :
    remainder4Coefficient2.coeff 93 =
      -((1669054940321917222182339972505 * 10 ^ 70 +
        8212908934709544089911296039693967331634309604203488359676909752809639) : ℚ) := by
  unfold
    remainder4Coefficient2
    remainder4Coefficient2Block1
    remainder4Coefficient2Block0
    remainder4Coefficient2Chunk23
    remainder4Coefficient2Chunk22
    remainder4Coefficient2Chunk21
    remainder4Coefficient2Chunk20
    remainder4Coefficient2Chunk19
    remainder4Coefficient2Chunk18
    remainder4Coefficient2Chunk17
    remainder4Coefficient2Chunk16
    remainder4Coefficient2Chunk15
    remainder4Coefficient2Chunk14
    remainder4Coefficient2Chunk13
    remainder4Coefficient2Chunk12
    remainder4Coefficient2Chunk11
    remainder4Coefficient2Chunk10
    remainder4Coefficient2Chunk9
    remainder4Coefficient2Chunk8
    remainder4Coefficient2Chunk7
    remainder4Coefficient2Chunk6
    remainder4Coefficient2Chunk5
    remainder4Coefficient2Chunk4
    remainder4Coefficient2Chunk3
    remainder4Coefficient2Chunk2
    remainder4Coefficient2Chunk1
    remainder4Coefficient2Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

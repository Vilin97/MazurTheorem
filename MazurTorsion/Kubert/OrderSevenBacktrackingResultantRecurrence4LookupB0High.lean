/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData4
import Mathlib.Tactic.NormNum

/-!
# Recurrence 4 lookup certificate: B0 source coefficients, high half

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence4B0_coeff_89 :
    remainder5Coefficient0.coeff 89 =
      ((243147735284975507376814912992944908 * 10 ^ 70 +
        8557715862645962643237058026038259758378686283339453029262466594182846) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_90 :
    remainder5Coefficient0.coeff 90 =
      -((196570064417209207402024567782066485 * 10 ^ 70 +
        8111306650775855388461585614486476679213270750269932217180976499493967) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_91 :
    remainder5Coefficient0.coeff 91 =
      ((153159057587230801202148153108656317 * 10 ^ 70 +
        2371274006398823507317617931899219375721860364188342865194779142944771) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_92 :
    remainder5Coefficient0.coeff 92 =
      -((114954094916425396884730080291259003 * 10 ^ 70 +
        2792712530220514662369310636128444097904970134081365575234313593152034) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_93 :
    remainder5Coefficient0.coeff 93 =
      ((83036932908714184707010020885642192 * 10 ^ 70 +
        8180836420984302120492298484868299040857209327288072906445955283454234) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_94 :
    remainder5Coefficient0.coeff 94 =
      -((57648068286239957301060107129095405 * 10 ^ 70 +
        7035210123962120614755934021842561134490370038735923881214201333468459) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_95 :
    remainder5Coefficient0.coeff 95 =
      ((38389762264277030046579145302915826 * 10 ^ 70 +
        6681065842038195951380479463027602637776250928807350202649955707771321) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_96 :
    remainder5Coefficient0.coeff 96 =
      -((24457109512611868896120714431405630 * 10 ^ 70 +
        6213559414400152043678921729199868713918134083833479972128498362382139) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_97 :
    remainder5Coefficient0.coeff 97 =
      ((14852510626318070971062415596573688 * 10 ^ 70 +
        6052146140850048889052129686785818056474144078353406580514072726697656) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_98 :
    remainder5Coefficient0.coeff 98 =
      -((8556666442269158542558965486346253 * 10 ^ 70 +
        0230385368537477086586246254262546027335658736017785069761755587786893) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_99 :
    remainder5Coefficient0.coeff 99 =
      ((4645396585339123012614011814285997 * 10 ^ 70 +
        4449249604938466792344043431391243197675021868939705326673292109206927) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_100 :
    remainder5Coefficient0.coeff 100 =
      -((2353733508847175662626747827303171 * 10 ^ 70 +
        7208968374930526935172732079770057668347536457970980205070256731535507) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_101 :
    remainder5Coefficient0.coeff 101 =
      ((1096400251195361400687322073877634 * 10 ^ 70 +
        2187822014915311889885588065678227428990509937482551342006991423807757) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_102 :
    remainder5Coefficient0.coeff 102 =
      -((457417378843535249802960581365541 * 10 ^ 70 +
        3749588542164142283616094506616877596267244894223507590051238437445642) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_103 :
    remainder5Coefficient0.coeff 103 =
      ((161983040533764105986659116397817 * 10 ^ 70 +
        2751583295579569863183358137912290665706498709369211644210932496200687) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_104 :
    remainder5Coefficient0.coeff 104 =
      -((41845421165489106026092352796684 * 10 ^ 70 +
        8597459227611041110905029128701503198432737703891170201816556514751186) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_105 :
    remainder5Coefficient0.coeff 105 =
      ((2159391006824730258889566808068 * 10 ^ 70 +
        5302122669599958645441666054294363715553449188196563257461324658206009) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_106 :
    remainder5Coefficient0.coeff 106 =
      ((5696934172940541909492250700915 * 10 ^ 70 +
        7373672361709008357828642295050743274493503998843202954909200069833600) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_107 :
    remainder5Coefficient0.coeff 107 =
      -((3863636548224382591159830846335 * 10 ^ 70 +
        5550978757712434009339348008476559615591525269150040422651695833175372) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_108 :
    remainder5Coefficient0.coeff 108 =
      ((841169725366383847040162135903 * 10 ^ 70 +
        9511785654292213986225019770864666863336955780064885234603825355291909) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_109 :
    remainder5Coefficient0.coeff 109 =
      ((1024161288242507256645800178189 * 10 ^ 70 +
        3390729301498229185917056961900451246816906096164091827440421611503911) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_110 :
    remainder5Coefficient0.coeff 110 =
      -((1670368045689599111114273818286 * 10 ^ 70 +
        9391503879636949963052931115318987632564808474664005623971586409273665) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_111 :
    remainder5Coefficient0.coeff 111 =
      ((1593997083119938781403534683931 * 10 ^ 70 +
        8496918812958137121736647966491670155137472242564124000747565932613095) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_112 :
    remainder5Coefficient0.coeff 112 =
      -((1234288876313796264416859699911 * 10 ^ 70 +
        8461886589969575162032870965001679247256338208875450009791135827275439) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_113 :
    remainder5Coefficient0.coeff 113 =
      ((844578931664838150766039177732 * 10 ^ 70 +
        6112705147119230080226986792298173541085891999262694215541791777493960) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_114 :
    remainder5Coefficient0.coeff 114 =
      -((529484751881035101822712075718 * 10 ^ 70 +
        5784914426773869240849284914099962252426850401793369926017668116409019) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_115 :
    remainder5Coefficient0.coeff 115 =
      ((309812870731337635597895601898 * 10 ^ 70 +
        5084253551032465766806105318652391809344922883339956226243279068962493) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_116 :
    remainder5Coefficient0.coeff 116 =
      -((170927936886847447825651158008 * 10 ^ 70 +
        8023500933175430472055517414721674730006278031403976084303550370938652) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_117 :
    remainder5Coefficient0.coeff 117 =
      ((89415540521749414159018107725 * 10 ^ 70 +
        3439400542409004623976051472163064015715535602220001649552470347502198) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_118 :
    remainder5Coefficient0.coeff 118 =
      -((44469171990311416289235491650 * 10 ^ 70 +
        3957417586821878164850538327027222721028245692085029329095873882667009) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_119 :
    remainder5Coefficient0.coeff 119 =
      ((21040807759889349771785685457 * 10 ^ 70 +
        5353533538699886952713033174688695610426419692270826974193161873519428) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_120 :
    remainder5Coefficient0.coeff 120 =
      -((9465088171831752309947675701 * 10 ^ 70 +
        2781917262888451990194361349099395133088053597550710049900965460678000) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_121 :
    remainder5Coefficient0.coeff 121 =
      ((4040860868032843815326194946 * 10 ^ 70 +
        9735108119713053817123270770854259983089440422377134083102682718225267) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_122 :
    remainder5Coefficient0.coeff 122 =
      -((1632776998959620086454938713 * 10 ^ 70 +
        7474316416771531471138480497502003118761635555894063087977592702343781) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_123 :
    remainder5Coefficient0.coeff 123 =
      ((622135469841639913279685672 * 10 ^ 70 +
        5947542732221817158107068829798138411939810685592715849411844263491525) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_124 :
    remainder5Coefficient0.coeff 124 =
      -((222459478398654489789662170 * 10 ^ 70 +
        1830764086318134137208598825965633817770289233964116192749411487584429) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_125 :
    remainder5Coefficient0.coeff 125 =
      ((74167272409662596251154948 * 10 ^ 70 +
        3208446313540233721311060330738107009945446501460931979925055335285557) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_126 :
    remainder5Coefficient0.coeff 126 =
      -((22841616050653819348824538 * 10 ^ 70 +
        7595500405439137082878496696109210434146581132849047361836296048184862) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_127 :
    remainder5Coefficient0.coeff 127 =
      ((6400242853473661187606654 * 10 ^ 70 +
        9716422262958750080723348537930461833671267119919693862555190552421355) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_128 :
    remainder5Coefficient0.coeff 128 =
      -((1583070870835501147948935 * 10 ^ 70 +
        8592912452557020375826155502969265289417072883460140889990102360925485) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_129 :
    remainder5Coefficient0.coeff 129 =
      ((318938877647812508699132 * 10 ^ 70 +
        8004679114249331820660016855086132223663268043506072381836184953049583) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_130 :
    remainder5Coefficient0.coeff 130 =
      -((35730162632940079321348 * 10 ^ 70 +
        2585678697441586119655958272918934512938400235136469418215558070204793) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_131 :
    remainder5Coefficient0.coeff 131 =
      -((10216470526272953616320 * 10 ^ 70 +
        6793447503767788393313174732067631709404023188160824359004238341882141) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_132 :
    remainder5Coefficient0.coeff 132 =
      ((9959358253138980130578 * 10 ^ 70 +
        8921495409047217195552076528779598528081702773167860193156349723852519) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_133 :
    remainder5Coefficient0.coeff 133 =
      -((5094005008172515223000 * 10 ^ 70 +
        9574589833856924154510024863213111905795250544582483418243732103658939) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_134 :
    remainder5Coefficient0.coeff 134 =
      ((2067174673303288754986 * 10 ^ 70 +
        0097274479399497094285627069204995388661921159320586796119303064478406) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_135 :
    remainder5Coefficient0.coeff 135 =
      -((698548542985301428710 * 10 ^ 70 +
        2543802896846559642250219231629421114088915228277206866055150921255061) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_136 :
    remainder5Coefficient0.coeff 136 =
      ((189609607354891277970 * 10 ^ 70 +
        9021722112687325878665062607500270209148314517536557820562268162353329) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_137 :
    remainder5Coefficient0.coeff 137 =
      -((36147732930624206529 * 10 ^ 70 +
        6021266816670478006740168810929175548945650703891366221910023974900107) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_138 :
    remainder5Coefficient0.coeff 138 =
      ((2358553686222011319 * 10 ^ 70 +
        6860303659011575325798060235920015615413218859640181824460191336757715) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_139 :
    remainder5Coefficient0.coeff 139 =
      ((971192652277583301 * 10 ^ 70 +
        2216238527911636326615615977682935761547525621855824932413501544007498) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_140 :
    remainder5Coefficient0.coeff 140 =
      ((21645448536587636 * 10 ^ 70 +
        5123264619246104505909241490866124199263892612581024937573032839223221) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_141 :
    remainder5Coefficient0.coeff 141 =
      -((442416726729687242 * 10 ^ 70 +
        8992292561498011467221786421491281082008860919300615479577452585124148) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_142 :
    remainder5Coefficient0.coeff 142 =
      ((352270911252513566 * 10 ^ 70 +
        3616914779812836977095880332182724665602888362541493986677173879556301) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_143 :
    remainder5Coefficient0.coeff 143 =
      -((182747877787643959 * 10 ^ 70 +
        4131715304858009066110465093977803156127460024064469225093569350908056) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_144 :
    remainder5Coefficient0.coeff 144 =
      ((76030172293771624 * 10 ^ 70 +
        3590606200115923192542927966514113742434932207480199020690712351709619) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_145 :
    remainder5Coefficient0.coeff 145 =
      -((27607862729546024 * 10 ^ 70 +
        8842397958076327167088243213394559264310404135340648549545264449299360) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_146 :
    remainder5Coefficient0.coeff 146 =
      ((9162807715100615 * 10 ^ 70 +
        6612953693441551507746556849210950951578476463755901946137357595939196) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_147 :
    remainder5Coefficient0.coeff 147 =
      -((2835834934193267 * 10 ^ 70 +
        4011416952528692266692170626886786853529965041213933902793321059324753) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_148 :
    remainder5Coefficient0.coeff 148 =
      ((816923273050565 * 10 ^ 70 +
        7210958019345291153317207561399895363901393129376243042063776397201872) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_149 :
    remainder5Coefficient0.coeff 149 =
      -((215830066128311 * 10 ^ 70 +
        6421695095790720903406199805953987456387271219038782543375231190979905) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_150 :
    remainder5Coefficient0.coeff 150 =
      ((51409809174318 * 10 ^ 70 +
        0507119370595627147283610374118237365879410321627366296475086060366249) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_151 :
    remainder5Coefficient0.coeff 151 =
      -((10899974796293 * 10 ^ 70 +
        4966705983469305583762388362397722295363297434176946085816051297808553) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_152 :
    remainder5Coefficient0.coeff 152 =
      ((2044532623099 * 10 ^ 70 +
        0463417226636951143015099389660107335721027252813200151097809632433810) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_153 :
    remainder5Coefficient0.coeff 153 =
      -((339645745982 * 10 ^ 70 +
        0240830011722431724203760747022910402314210109607347885206914802144674) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_154 :
    remainder5Coefficient0.coeff 154 =
      ((50391159002 * 10 ^ 70 +
        5259039850681847668682838031682438707803970728124337943070617416765458) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_155 :
    remainder5Coefficient0.coeff 155 =
      -((6772520759 * 10 ^ 70 +
        1569508501889556651033790379855854667996664790494874744940898033690106) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_156 :
    remainder5Coefficient0.coeff 156 =
      ((835639066 * 10 ^ 70 +
        8446787866317617510745858970068897208187307841239549973097918076325983) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_157 :
    remainder5Coefficient0.coeff 157 =
      -((94316617 * 10 ^ 70 +
        5986102626254233917143732839769472888377957425525506595001360476058166) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_158 :
    remainder5Coefficient0.coeff 158 =
      ((9311295 * 10 ^ 70 +
        3159070155810858163197306597951494675483482975524395305832381858106517) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_159 :
    remainder5Coefficient0.coeff 159 =
      -((711257 * 10 ^ 70 +
        5381760457338263627442336783044560967834790600989907984264990130153667) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_160 :
    remainder5Coefficient0.coeff 160 =
      ((27997 * 10 ^ 70 +
        7683558938809548202635556624522589400986871333307419679496074685498330) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_161 :
    remainder5Coefficient0.coeff 161 =
      ((1685 * 10 ^ 70 +
        3087028750081903031846109477894234011225120776616170221669113503157825) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_162 :
    remainder5Coefficient0.coeff 162 =
      -((357 * 10 ^ 70 +
        0938561128905602994101094906208763892603307388238154958514349705039372) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_163 :
    remainder5Coefficient0.coeff 163 =
      ((24 * 10 ^ 70 +
        5330041988896958633548850969285021398045305333097909439213858212950283) : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_164 :
    remainder5Coefficient0.coeff 164 =
      (-7249778412873998133748802006845370228676119425865786497080138061596134 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_165 :
    remainder5Coefficient0.coeff 165 =
      (52956952622783827709881861482560071963290333685460121885825744846323 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_166 :
    remainder5Coefficient0.coeff 166 =
      (280152685655969885879173634551080225175486884028181547038251690722 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_167 :
    remainder5Coefficient0.coeff 167 =
      (-2031690952404327765609612130635720034174061933756701558852622761 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_168 :
    remainder5Coefficient0.coeff 168 =
      (-1458928063823863028050875425433121845305555066201276383078993 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_169 :
    remainder5Coefficient0.coeff 169 =
      (17431834505586844323129159562726344394790113806316568604074 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_170 :
    remainder5Coefficient0.coeff 170 =
      (-22878977253084650022265554947451972454998443751804602608 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_171 :
    remainder5Coefficient0.coeff 171 =
      (8465739853890267008832801209206747768551353802553124 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_172 :
    remainder5Coefficient0.coeff 172 =
      (-805368785374396620874539479169423728718837961557 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_173 :
    remainder5Coefficient0.coeff 173 =
      (15842754036030934147022086546074136452896574 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_174 :
    remainder5Coefficient0.coeff 174 =
      (-45305433673927959040925527740176360349 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_175 :
    remainder5Coefficient0.coeff 175 =
      (10459335688262185635633707671032 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4B0_coeff_176 :
    remainder5Coefficient0.coeff 176 =
      (-65860748014005733131201 : ℚ) := by
  unfold
    remainder5Coefficient0
    remainder5Coefficient0Block1
    remainder5Coefficient0Block0
    remainder5Coefficient0Chunk21
    remainder5Coefficient0Chunk20
    remainder5Coefficient0Chunk19
    remainder5Coefficient0Chunk18
    remainder5Coefficient0Chunk17
    remainder5Coefficient0Chunk16
    remainder5Coefficient0Chunk15
    remainder5Coefficient0Chunk14
    remainder5Coefficient0Chunk13
    remainder5Coefficient0Chunk12
    remainder5Coefficient0Chunk11
    remainder5Coefficient0Chunk10
    remainder5Coefficient0Chunk9
    remainder5Coefficient0Chunk8
    remainder5Coefficient0Chunk7
    remainder5Coefficient0Chunk6
    remainder5Coefficient0Chunk5
    remainder5Coefficient0Chunk4
    remainder5Coefficient0Chunk3
    remainder5Coefficient0Chunk2
    remainder5Coefficient0Chunk1
    remainder5Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

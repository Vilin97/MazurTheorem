/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData4
import Mathlib.Tactic.NormNum

/-!
# Recurrence 4 lookup certificate: C0 source coefficients, high half

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence4C0_coeff_77 :
    remainder6Coefficient0.coeff 77 =
      ((7042416439600824981175212202559402681235800626477020924162 * 10 ^ 70 +
        3775791209803646339836453822379267260290631171624805898027767343901369) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_78 :
    remainder6Coefficient0.coeff 78 =
      -((4333777558656447969444594486941627675125589467831831294526 * 10 ^ 70 +
        0222387151347534109648121321789486462344309222830113004172299535075139) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_79 :
    remainder6Coefficient0.coeff 79 =
      ((2516439488195369851192953188707540450561124005927895493985 * 10 ^ 70 +
        6388217734415338692960727593906912294083786851615809455093229588575319) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_80 :
    remainder6Coefficient0.coeff 80 =
      -((1368172363228574544859910196242219586895815793433433622588 * 10 ^ 70 +
        4510887858629851730925295059619981057207041738260701807622679979231790) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_81 :
    remainder6Coefficient0.coeff 81 =
      ((685629388771414091582667919418712732771642000030183730334 * 10 ^ 70 +
        4100149625850514682843635643803738849216030475241228370850930463995932) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_82 :
    remainder6Coefficient0.coeff 82 =
      -((305408929221347743127421034375009535365762024315518406240 * 10 ^ 70 +
        0195208401942724262159009016291365177289078252152567385059530948831621) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_83 :
    remainder6Coefficient0.coeff 83 =
      ((108780485440016920151143192802011808397651631170893696240 * 10 ^ 70 +
        3479232751643530077841676755856186276025133534401389034051723397910670) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_84 :
    remainder6Coefficient0.coeff 84 =
      -((16499173282162382665335009635612334728153405421515460200 * 10 ^ 70 +
        9130553893592896631104040134724966070817987820035741230502787046521920) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_85 :
    remainder6Coefficient0.coeff 85 =
      -((20480492218801474173622026797990687745572300249578378665 * 10 ^ 70 +
        4176239198333020247668146581390775408160260167460689803602895951055108) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_86 :
    remainder6Coefficient0.coeff 86 =
      ((30468510690501817006944176592081708488380947754203165530 * 10 ^ 70 +
        5438981644855597874897774151592108562196762723015626484857433629425209) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_87 :
    remainder6Coefficient0.coeff 87 =
      -((28738618767794090380975428031464114003768603159718545850 * 10 ^ 70 +
        9983371713515769295528531392553824550998773290147139944846119175295612) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_88 :
    remainder6Coefficient0.coeff 88 =
      ((22965374796967857588642433915971625782304375621831782573 * 10 ^ 70 +
        0999454015086814523191777096417688958631350104473882633513443500841826) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_89 :
    remainder6Coefficient0.coeff 89 =
      -((16680357232706379237613949322563272661695518661105386467 * 10 ^ 70 +
        7452849108522610423410897001719968543819296806132235360019073270144992) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_90 :
    remainder6Coefficient0.coeff 90 =
      ((11292205539266749874861642796083954180901776457045474820 * 10 ^ 70 +
        9679752911728599431888913748031939071272384583807382228126579703821542) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_91 :
    remainder6Coefficient0.coeff 91 =
      -((7189309887615754654555423465786622186710340175897774855 * 10 ^ 70 +
        2684152139520235643435923532024102184165603936294261022706481183313493) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_92 :
    remainder6Coefficient0.coeff 92 =
      ((4309809143035331895806396159964299706264294668354641264 * 10 ^ 70 +
        4164502187770412718993970069436778156831940924184568383264247144606308) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_93 :
    remainder6Coefficient0.coeff 93 =
      -((2424056829267100738459702760017041498621737179330892336 * 10 ^ 70 +
        7208910042101750909652105789856870518597137309153205826807722496540586) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_94 :
    remainder6Coefficient0.coeff 94 =
      ((1269484153797651344916319388798676758133831726369932242 * 10 ^ 70 +
        7287679010156099681555204807670511841303326754826560023016600151511732) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_95 :
    remainder6Coefficient0.coeff 95 =
      -((611206023090921508401388991559125192551048023421644599 * 10 ^ 70 +
        1643768857076390485510295643358397397260476977922415396480945109421732) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_96 :
    remainder6Coefficient0.coeff 96 =
      ((264738000204735231192264992409749098252625840964515125 * 10 ^ 70 +
        9721728729457169677204321773312252261302842639221556480243309954040575) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_97 :
    remainder6Coefficient0.coeff 97 =
      -((98877303594059357079654337801341481891225349938077006 * 10 ^ 70 +
        4788868309441948448409758398552192038593390911659487963611367869141393) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_98 :
    remainder6Coefficient0.coeff 98 =
      ((28531841049603031319257428833518381446952782925951149 * 10 ^ 70 +
        7622066940179618517221483878505286441804448298752021993656324545677445) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_99 :
    remainder6Coefficient0.coeff 99 =
      -((3521843803453590010974830377674181445164577029342151 * 10 ^ 70 +
        0688293116843038427776834875846102029181368560359133512713957951118392) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_100 :
    remainder6Coefficient0.coeff 100 =
      -((2790504111339937132729549178574872110039177364668834 * 10 ^ 70 +
        1408100936130621217935347407246561731963264202225421436233869965414056) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_101 :
    remainder6Coefficient0.coeff 101 =
      ((2885955320455334783507397261047980958218514361467875 * 10 ^ 70 +
        8125259102511017192982166778552256571643396967775379364294260513224605) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_102 :
    remainder6Coefficient0.coeff 102 =
      -((1720414816868963085637396353826404226766249710610362 * 10 ^ 70 +
        4247473537135420326762613238121323084684601004912366659705378074817445) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_103 :
    remainder6Coefficient0.coeff 103 =
      ((792520869621764104836406981275996013371865862570388 * 10 ^ 70 +
        6192566419355627920154863991879184226068128032560095866907767799989717) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_104 :
    remainder6Coefficient0.coeff 104 =
      -((298227503551884963158826194402625448425323763872734 * 10 ^ 70 +
        5522997911588126446060266786775704691877800289548713169077323744846287) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_105 :
    remainder6Coefficient0.coeff 105 =
      ((92062404039608877391074607416608957416073282407365 * 10 ^ 70 +
        6659802550817270028860284394495740108714712352779622896592891969295908) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_106 :
    remainder6Coefficient0.coeff 106 =
      -((23405683274524219241402368720258012723781555588566 * 10 ^ 70 +
        3209288152537895866030161708310333421510860702364351093398028318234773) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_107 :
    remainder6Coefficient0.coeff 107 =
      ((5811872092054713908334868897376484582322876538273 * 10 ^ 70 +
        2064500846002971525339538737040030886350790307394560235285214463472702) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_108 :
    remainder6Coefficient0.coeff 108 =
      -((2573049585694577098544444275172123043366621925316 * 10 ^ 70 +
        9413793339096093373972213600241134090102063973859694462158317922913028) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_109 :
    remainder6Coefficient0.coeff 109 =
      ((1934040705490317939031495573753825920758663767108 * 10 ^ 70 +
        9332783255249792990183300545056640838840984886655028867555698326999598) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_110 :
    remainder6Coefficient0.coeff 110 =
      -((1395760659022698794001983159127896258850181983704 * 10 ^ 70 +
        3875302887647977285675869414109673794014028586139085793614903627732882) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_111 :
    remainder6Coefficient0.coeff 111 =
      ((852179348675876821072221724181714942504861724664 * 10 ^ 70 +
        7103460632365971123948863119099168523017653387298377340934416637333803) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_112 :
    remainder6Coefficient0.coeff 112 =
      -((449401755381186494734142111793788297776785136398 * 10 ^ 70 +
        2837133227222328644492133140354090561313505323945925989018912813737660) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_113 :
    remainder6Coefficient0.coeff 113 =
      ((211270506647490365102202776554166582905563934860 * 10 ^ 70 +
        5353244550470355482305700701693227820251516000703161066513189870585353) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_114 :
    remainder6Coefficient0.coeff 114 =
      -((90771576545213832803146397025661344059108357425 * 10 ^ 70 +
        4006512125638428183550763839931918472153006616894798284417918609786656) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_115 :
    remainder6Coefficient0.coeff 115 =
      ((36272666133923598896210470675574880314207056835 * 10 ^ 70 +
        7571341465443487595546715114079533669358505868152800112177571180339909) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_116 :
    remainder6Coefficient0.coeff 116 =
      -((13627458041632117714699783044083683806660217545 * 10 ^ 70 +
        4195456557559981586342032667676150283692488707792252963142585584536937) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_117 :
    remainder6Coefficient0.coeff 117 =
      ((4836991832354259322689619339221147576606237891 * 10 ^ 70 +
        6783869685497196648273651000030967848310358596210709159111826585071098) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_118 :
    remainder6Coefficient0.coeff 118 =
      -((1622841963945511821369426378340252070099841034 * 10 ^ 70 +
        7754365241956510892541108090584910486094039228906966688819958112062473) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_119 :
    remainder6Coefficient0.coeff 119 =
      ((513834937837274310790248867472524267349050035 * 10 ^ 70 +
        3793191587409995732987621773288667456404421120021358486521096793015039) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_120 :
    remainder6Coefficient0.coeff 120 =
      -((153385247830991839235846166001868689660831219 * 10 ^ 70 +
        3302324326097872469939730730529759908988830831404002732715351707908941) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_121 :
    remainder6Coefficient0.coeff 121 =
      ((43268977025759519748288312363554334778840473 * 10 ^ 70 +
        3643068351936562222107046471567431523286272920293651352407691323368721) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_122 :
    remainder6Coefficient0.coeff 122 =
      -((11625356771159546810968124751953069701859794 * 10 ^ 70 +
        9592482600848854722217487376355921725819018577597776341972626623371089) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_123 :
    remainder6Coefficient0.coeff 123 =
      ((3010363655007025248433173674606814540051422 * 10 ^ 70 +
        3156692192484491112855098661928126482468142824272077219862516892832661) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_124 :
    remainder6Coefficient0.coeff 124 =
      -((753787827508682712057668830567283731334133 * 10 ^ 70 +
        1393325448943613538614094271072815368501973656819640314183733586927485) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_125 :
    remainder6Coefficient0.coeff 125 =
      ((175880055701805298451551468709469930975663 * 10 ^ 70 +
        1815901534982032571768080171189951609233105825274825429301550532793903) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_126 :
    remainder6Coefficient0.coeff 126 =
      -((33060048780662551024052597621677972233681 * 10 ^ 70 +
        9297189696508451671243131189110936581430036410237433730802963717403316) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_127 :
    remainder6Coefficient0.coeff 127 =
      ((2226366477192429577366154270471475291764 * 10 ^ 70 +
        6315157238057824254920353907674254749321344905789132748923417683523727) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_128 :
    remainder6Coefficient0.coeff 128 =
      ((1721622556172604691938273111274200043861 * 10 ^ 70 +
        3718043498708509006327684468436113496935387787900505166760322770068586) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_129 :
    remainder6Coefficient0.coeff 129 =
      -((948677049435354802767362108935098873542 * 10 ^ 70 +
        7161562216487575618124201841851271815348040672694553363211888291545275) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_130 :
    remainder6Coefficient0.coeff 130 =
      ((250499486353611620506031945702216196769 * 10 ^ 70 +
        1768573984238015380432358636623602580985636285318427265574829401381504) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_131 :
    remainder6Coefficient0.coeff 131 =
      -((22788046871107052161590286900541872406 * 10 ^ 70 +
        3634642444454031194044307173767584775516201215004931211199843955370043) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_132 :
    remainder6Coefficient0.coeff 132 =
      -((9821649789686610546322663551998362397 * 10 ^ 70 +
        2081098910448173716328260408008322834480921916201446303018261645849775) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_133 :
    remainder6Coefficient0.coeff 133 =
      ((4811429932686631121954567797441945948 * 10 ^ 70 +
        5026660720373732669409380672913059079506120499283423317262724358513753) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_134 :
    remainder6Coefficient0.coeff 134 =
      -((978244586701715013408469136699312777 * 10 ^ 70 +
        2301804990356542220136730768241563953272279362511237673829406373775077) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_135 :
    remainder6Coefficient0.coeff 135 =
      ((68436425736631111529026380422940404 * 10 ^ 70 +
        1056939669968602172451088903829265477878420885880740905084239396432829) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_136 :
    remainder6Coefficient0.coeff 136 =
      ((13886741992941871929954290099110822 * 10 ^ 70 +
        0256698589281831146600362522795001221184006764411549350487641733246627) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_137 :
    remainder6Coefficient0.coeff 137 =
      -((3778671061845974604461928018904093 * 10 ^ 70 +
        3968237711826787559552597079095542984405795858083745564135664466242848) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_138 :
    remainder6Coefficient0.coeff 138 =
      ((235083058449474239281650455780128 * 10 ^ 70 +
        8836238854677877943778292131885808325594775847709219297747434078292101) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_139 :
    remainder6Coefficient0.coeff 139 =
      ((27888745123962574494007526911981 * 10 ^ 70 +
        3500704485102708323844693614014388659968268257160277499083287181443224) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_140 :
    remainder6Coefficient0.coeff 140 =
      -((3835260375222585733258292553293 * 10 ^ 70 +
        9126590106632189660597492774862875526016695004135944968492704380460258) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_141 :
    remainder6Coefficient0.coeff 141 =
      -((100911670348140664582273233919 * 10 ^ 70 +
        7080632813991068887499225992140514843699408958206164792793083982406218) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_142 :
    remainder6Coefficient0.coeff 142 =
      ((19113838009905526829430648565 * 10 ^ 70 +
        8995443631631496363996511023979123993293676179280980424863445038603587) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_143 :
    remainder6Coefficient0.coeff 143 =
      ((869929980025340894370315746 * 10 ^ 70 +
        5955635348757780565312249766272365388789685721551146498370366296312299) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_144 :
    remainder6Coefficient0.coeff 144 =
      ((12246599569794225424392972 * 10 ^ 70 +
        2126391987127786882930855636161187210269086829799846414203760791328441) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_145 :
    remainder6Coefficient0.coeff 145 =
      ((69638713848159290332988 * 10 ^ 70 +
        5256352181862514777629143291461659469243738177890934890193696487550318) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_146 :
    remainder6Coefficient0.coeff 146 =
      ((138257791436571438515 * 10 ^ 70 +
        2048737118836413229904856003565272708847469289715773194168251441321905) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_147 :
    remainder6Coefficient0.coeff 147 =
      -((113273456964717550 * 10 ^ 70 +
        0288714514845431446269255646978303098437510940968902759648300857844097) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_148 :
    remainder6Coefficient0.coeff 148 =
      -((634061875119979 * 10 ^ 70 +
        1781175838895430994766258546972889693929715069587307820395617859670203) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_149 :
    remainder6Coefficient0.coeff 149 =
      -((425964754708 * 10 ^ 70 +
        3440507652692273529109066434625663133190140826025129909804229611595157) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_150 :
    remainder6Coefficient0.coeff 150 =
      -((49857869 * 10 ^ 70 +
        9344578730403967957107071629118684300830830953738459368582372039571628) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_151 :
    remainder6Coefficient0.coeff 151 =
      -((736 * 10 ^ 70 +
        9726035909930009157578415287677426927206524375908958170486829976587832) : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_152 :
    remainder6Coefficient0.coeff 152 =
      (-6887705664784635288982906342362505374220275595023009803387494452840 : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4C0_coeff_153 :
    remainder6Coefficient0.coeff 153 =
      (-171910651576204265134294769707019620352195984168302791988841 : ℚ) := by
  unfold
    remainder6Coefficient0
    remainder6Coefficient0Block1
    remainder6Coefficient0Block0
    remainder6Coefficient0Chunk19
    remainder6Coefficient0Chunk18
    remainder6Coefficient0Chunk17
    remainder6Coefficient0Chunk16
    remainder6Coefficient0Chunk15
    remainder6Coefficient0Chunk14
    remainder6Coefficient0Chunk13
    remainder6Coefficient0Chunk12
    remainder6Coefficient0Chunk11
    remainder6Coefficient0Chunk10
    remainder6Coefficient0Chunk9
    remainder6Coefficient0Chunk8
    remainder6Coefficient0Chunk7
    remainder6Coefficient0Chunk6
    remainder6Coefficient0Chunk5
    remainder6Coefficient0Chunk4
    remainder6Coefficient0Chunk3
    remainder6Coefficient0Chunk2
    remainder6Coefficient0Chunk1
    remainder6Coefficient0Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

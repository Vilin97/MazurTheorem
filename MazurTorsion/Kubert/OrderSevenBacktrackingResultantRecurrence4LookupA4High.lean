/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantCertificateData4
import Mathlib.Tactic.NormNum

/-!
# Recurrence 4 lookup certificate: A4 source coefficients, high half

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

theorem recurrence4A4_coeff_90 :
    remainder4Coefficient4.coeff 90 =
      ((6210420738552904494225994994 * 10 ^ 70 +
        0686289484120249041336375928705806317762389016918791591075768597445252) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_91 :
    remainder4Coefficient4.coeff 91 =
      -((6581994871993202286249679846 * 10 ^ 70 +
        9479778532291202471128205707467871911106490057203564089293008850216717) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_92 :
    remainder4Coefficient4.coeff 92 =
      ((6735266917308732707472504411 * 10 ^ 70 +
        8189695046460205389778759885755358408467579406097326053985494402097542) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_93 :
    remainder4Coefficient4.coeff 93 =
      -((6654132170779652911378936589 * 10 ^ 70 +
        3269654396591840065680149808340965511387782098109881478937017950746100) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_94 :
    remainder4Coefficient4.coeff 94 =
      ((6346585665206735929615808504 * 10 ^ 70 +
        8215724337587306860125243558213916606130127114516718325137033758265934) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_95 :
    remainder4Coefficient4.coeff 95 =
      -((5843431133120115195221730980 * 10 ^ 70 +
        8538256518778490297912786247634886104338508703755948921392211217016678) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_96 :
    remainder4Coefficient4.coeff 96 =
      ((5193209928108119021555096413 * 10 ^ 70 +
        2391738047325528662554319116703631201279933714794839550176899184663721) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_97 :
    remainder4Coefficient4.coeff 97 =
      -((4454502695544242401241266584 * 10 ^ 70 +
        0564382533206960669975216378414681604851816187422209504469444923325602) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_98 :
    remainder4Coefficient4.coeff 98 =
      ((3687290035255789466748041298 * 10 ^ 70 +
        3495260736797743326459227355337035101247642209753988092065343827977189) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_99 :
    remainder4Coefficient4.coeff 99 =
      -((2945123269492600016689978494 * 10 ^ 70 +
        4899468868784200092993764679169534891293083068131905070795139713280425) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_100 :
    remainder4Coefficient4.coeff 100 =
      ((2269473587641257466327857326 * 10 ^ 70 +
        2601923942060886116267164754225409439668608839258438579272789447599544) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_101 :
    remainder4Coefficient4.coeff 101 =
      -((1686955297106901174483989548 * 10 ^ 70 +
        0087536785074755614294509298308344688957807427793810184645953840367182) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_102 :
    remainder4Coefficient4.coeff 102 =
      ((1209383289691897792690081485 * 10 ^ 70 +
        4480655959580371032030685208361240420977265888012754723399525824646434) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_103 :
    remainder4Coefficient4.coeff 103 =
      -((836036458962234012804703235 * 10 ^ 70 +
        0310480721415116591340449013261227441068363155607628376259832097609075) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_104 :
    remainder4Coefficient4.coeff 104 =
      ((557185593979977413220940120 * 10 ^ 70 +
        2199648167527154417929965386722848731819689564127511489736752827311937) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_105 :
    remainder4Coefficient4.coeff 105 =
      -((357926588004230691439407809 * 10 ^ 70 +
        5102251189048938203875141211786131836178731843755126286417998195817138) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_106 :
    remainder4Coefficient4.coeff 106 =
      ((221567849700912147005751175 * 10 ^ 70 +
        1984069583252799643273235169417592697827462240875969365795342137446337) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_107 :
    remainder4Coefficient4.coeff 107 =
      -((132138865098665292845378265 * 10 ^ 70 +
        2759911432590871680366802617536859832974150205176506551808493946581874) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_108 :
    remainder4Coefficient4.coeff 108 =
      ((75901560007842297404270428 * 10 ^ 70 +
        0090939334313878442323577850035240047946698365671645680461664502202999) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_109 :
    remainder4Coefficient4.coeff 109 =
      -((41980279921955775914085615 * 10 ^ 70 +
        2193527005953105376843810320195165314296140637481900552245630331728656) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_110 :
    remainder4Coefficient4.coeff 110 =
      ((22350441650431528431228845 * 10 ^ 70 +
        3395739653126256680851182254319018315428678578260951400105073250327199) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_111 :
    remainder4Coefficient4.coeff 111 =
      -((11450899387002501470401585 * 10 ^ 70 +
        9413250820759960266371341799071682523182753816953183431388369982489086) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_112 :
    remainder4Coefficient4.coeff 112 =
      ((5643784134951827112283683 * 10 ^ 70 +
        9629698119366801527094024816754112975316201427577378659062305797100309) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_113 :
    remainder4Coefficient4.coeff 113 =
      -((2675142847488356287627834 * 10 ^ 70 +
        9721298906954658224713415926411352559287034989952976971087647710921845) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_114 :
    remainder4Coefficient4.coeff 114 =
      ((1219134407349354642814059 * 10 ^ 70 +
        6880990181180089038528244742070850527962578053008338554443138586490933) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_115 :
    remainder4Coefficient4.coeff 115 =
      -((534066697096263445114891 * 10 ^ 70 +
        4048019190472597622560570642069584086164824469417179248629004686878098) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_116 :
    remainder4Coefficient4.coeff 116 =
      ((224874696649380389252977 * 10 ^ 70 +
        4617888509302421960210705452999369077409440661405116965223592868793315) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_117 :
    remainder4Coefficient4.coeff 117 =
      -((91017873647578202937535 * 10 ^ 70 +
        6207263838153553588830314160649045020038547163728918115795927879520818) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_118 :
    remainder4Coefficient4.coeff 118 =
      ((35424245168842571119710 * 10 ^ 70 +
        4647030894731091489536568015106624902165430761226738818778561029115072) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_119 :
    remainder4Coefficient4.coeff 119 =
      -((13265896892185361456985 * 10 ^ 70 +
        9768696282944525561174370778026751507896666546756943297186061988034724) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_120 :
    remainder4Coefficient4.coeff 120 =
      ((4784394203273554029143 * 10 ^ 70 +
        1419858300881266057247987170370984389640023870148766648224570620345439) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_121 :
    remainder4Coefficient4.coeff 121 =
      -((1663427202525079230938 * 10 ^ 70 +
        1202325793316517410852716118726642460695811906999767498578805217727246) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_122 :
    remainder4Coefficient4.coeff 122 =
      ((557860212949992930891 * 10 ^ 70 +
        4087950975495947997104490417024268929857874284414583646778010187528439) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_123 :
    remainder4Coefficient4.coeff 123 =
      -((180301329830428494187 * 10 ^ 70 +
        2038929741657565978703813599435324811576961230444056221302086149512139) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_124 :
    remainder4Coefficient4.coeff 124 =
      ((55890950950301215424 * 10 ^ 70 +
        0220729973597370949265169863859927558836246710020035751157977507827761) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_125 :
    remainder4Coefficient4.coeff 125 =
      -((16378512205863762538 * 10 ^ 70 +
        9089135477919797431962329773517885340258827396104957518949509560136417) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_126 :
    remainder4Coefficient4.coeff 126 =
      ((4353344837498179262 * 10 ^ 70 +
        6112850267318820084096592260922119883191126135083800023163045208605087) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_127 :
    remainder4Coefficient4.coeff 127 =
      -((907588927164474076 * 10 ^ 70 +
        6398630736756589004642729865915085452837603574743263806014364353106016) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_128 :
    remainder4Coefficient4.coeff 128 =
      ((25519060589270721 * 10 ^ 70 +
        5774412122592332342012434451836128891876566291782254376017445027952399) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_129 :
    remainder4Coefficient4.coeff 129 =
      ((138158260300660659 * 10 ^ 70 +
        6592689715527343596432001432110834316124330707404513402089855716671960) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_130 :
    remainder4Coefficient4.coeff 130 =
      -((124955248840235861 * 10 ^ 70 +
        9067539719307382659869977022674061726665387033969667336314649990791786) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_131 :
    remainder4Coefficient4.coeff 131 =
      ((83499258298824992 * 10 ^ 70 +
        7417144175463553005553660265708019106153948807175617973980498971328733) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_132 :
    remainder4Coefficient4.coeff 132 =
      -((49123395817065368 * 10 ^ 70 +
        9128621576264693540916615084672051870689377535241762969316670834679603) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_133 :
    remainder4Coefficient4.coeff 133 =
      ((26540293971453107 * 10 ^ 70 +
        4369408629416436195321508381914986370299131039760769808350988693589865) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_134 :
    remainder4Coefficient4.coeff 134 =
      -((13317460590976925 * 10 ^ 70 +
        6805638583704068273821313315646740678131722141705465053112975339491586) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_135 :
    remainder4Coefficient4.coeff 135 =
      ((6212553598504407 * 10 ^ 70 +
        4238916863489848457710735003575081389058303720837271317856121940453176) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_136 :
    remainder4Coefficient4.coeff 136 =
      -((2685335082901387 * 10 ^ 70 +
        5686229228979889657283283870165894931486525236511650187814627936884257) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_137 :
    remainder4Coefficient4.coeff 137 =
      ((1068807201464699 * 10 ^ 70 +
        8655420831241993695517516253347367474681547032008599355949270014132500) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_138 :
    remainder4Coefficient4.coeff 138 =
      -((387957355983257 * 10 ^ 70 +
        5508028655406617722108153200363505861119417594993213051838142236818847) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_139 :
    remainder4Coefficient4.coeff 139 =
      ((126455964093411 * 10 ^ 70 +
        1884152309099598738598442191697892728467857522445832727804603026593886) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_140 :
    remainder4Coefficient4.coeff 140 =
      -((36002488192354 * 10 ^ 70 +
        3842213115730975629648308174133851804186399480063538097260249536642325) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_141 :
    remainder4Coefficient4.coeff 141 =
      ((8428313489602 * 10 ^ 70 +
        7013315514375359597905245095794130126753475765787971858380601307648885) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_142 :
    remainder4Coefficient4.coeff 142 =
      -((1336401855253 * 10 ^ 70 +
        6870106112488135192565731441381999351929648986298365038924702054279607) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_143 :
    remainder4Coefficient4.coeff 143 =
      -((32734369917 * 10 ^ 70 +
        0464699761577302195337859688747287944340462394824154300059207815927899) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_144 :
    remainder4Coefficient4.coeff 144 =
      ((132016461434 * 10 ^ 70 +
        8386054945744650273411942337121270898397010916003411711181767723643938) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_145 :
    remainder4Coefficient4.coeff 145 =
      -((64885929403 * 10 ^ 70 +
        1554303075994940072301282245381788888328688285925895513176919200506617) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_146 :
    remainder4Coefficient4.coeff 146 =
      ((22083875493 * 10 ^ 70 +
        4821328039472574611241147356114157598311043155632389385373058272559210) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_147 :
    remainder4Coefficient4.coeff 147 =
      -((5980929851 * 10 ^ 70 +
        7875523413435358484867096141946328509644746511162971903616631684174536) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_148 :
    remainder4Coefficient4.coeff 148 =
      ((1326869935 * 10 ^ 70 +
        8787120083745940782141519398626870522869114268170496163073085797698098) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_149 :
    remainder4Coefficient4.coeff 149 =
      -((237975880 * 10 ^ 70 +
        6351378093643712567944979390393126207060485801086902854493514851917653) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_150 :
    remainder4Coefficient4.coeff 150 =
      ((32349513 * 10 ^ 70 +
        6230844301152310059355271687388990380724381784426088649625088068668506) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_151 :
    remainder4Coefficient4.coeff 151 =
      -((2587275 * 10 ^ 70 +
        9314091325945026746045196141902077915564978069299674746520061572358274) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_152 :
    remainder4Coefficient4.coeff 152 =
      -((128469 * 10 ^ 70 +
        0873474399391019722153023448905064209907681060632575395376874198328604) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_153 :
    remainder4Coefficient4.coeff 153 =
      ((88969 * 10 ^ 70 +
        3859826930515708567559217677735760752606262560394097025119268347418528) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_154 :
    remainder4Coefficient4.coeff 154 =
      -((17339 * 10 ^ 70 +
        5091353026135608808498531891181617944919444523197138612866070863771009) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_155 :
    remainder4Coefficient4.coeff 155 =
      ((2023 * 10 ^ 70 +
        6685049441599450289572457170115668287006499522177571665671457256767497) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_156 :
    remainder4Coefficient4.coeff 156 =
      -((125 * 10 ^ 70 +
        6136201231641186548779047411422033760566110036447839779100566856773266) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_157 :
    remainder4Coefficient4.coeff 157 =
      -((2 * 10 ^ 70 +
        4501604770112356169935138166389348876600541569682831993610892447640274) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_158 :
    remainder4Coefficient4.coeff 158 =
      ((1 * 10 ^ 70 +
        3335260588995795924656128037700143969471139677639424496675889859002725) : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_159 :
    remainder4Coefficient4.coeff 159 =
      (-1163123244074168701712233519379576182152983757991445529539737750498651 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_160 :
    remainder4Coefficient4.coeff 160 =
      (21664307316394258428735903829881156747239925744515118153476674339312 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_161 :
    remainder4Coefficient4.coeff 161 =
      (3384172692885868106582451463616483541142166180715354811216882644238 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_162 :
    remainder4Coefficient4.coeff 162 =
      (-188391336234227262898315958015782851506076385498017735975800887275 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_163 :
    remainder4Coefficient4.coeff 163 =
      (-4378531681813236440999709152190562860789739148045625214906966669 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_164 :
    remainder4Coefficient4.coeff 164 =
      (303496158003747514968309558031202635822473022819075445357142534 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_165 :
    remainder4Coefficient4.coeff 165 =
      (11047171988402173238537502599947084984260062381468603612768813 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_166 :
    remainder4Coefficient4.coeff 166 =
      (142455568902971257235176322545022958493146926991750416525808 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_167 :
    remainder4Coefficient4.coeff 167 =
      (882580807154962979793387492417905075636275494192502490072 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_168 :
    remainder4Coefficient4.coeff 168 =
      (2596925732091123444498782404864018183819006687965575742 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_169 :
    remainder4Coefficient4.coeff 169 =
      (1996688805956656106656189129783569768314598137016426 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_170 :
    remainder4Coefficient4.coeff 170 =
      (-7032119049508479189059666386400262979855029581022 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_171 :
    remainder4Coefficient4.coeff 171 =
      (-16892523735677694300412872131821010869892502577 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_172 :
    remainder4Coefficient4.coeff 172 =
      (-12438441861216259363932837305967914513437153 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_173 :
    remainder4Coefficient4.coeff 173 =
      (-3246147819256494214890850375688151153526 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_174 :
    remainder4Coefficient4.coeff 174 =
      (-269696150398856188469200042343654125 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_175 :
    remainder4Coefficient4.coeff 175 =
      (-5820904611090347453238735248540 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_176 :
    remainder4Coefficient4.coeff 176 =
      (-23746675225620686797463689 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_177 :
    remainder4Coefficient4.coeff 177 =
      (-10702991793672512235 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

theorem recurrence4A4_coeff_178 :
    remainder4Coefficient4.coeff 178 =
      (-152365481437 : ℚ) := by
  unfold
    remainder4Coefficient4
    remainder4Coefficient4Block1
    remainder4Coefficient4Block0
    remainder4Coefficient4Chunk22
    remainder4Coefficient4Chunk21
    remainder4Coefficient4Chunk20
    remainder4Coefficient4Chunk19
    remainder4Coefficient4Chunk18
    remainder4Coefficient4Chunk17
    remainder4Coefficient4Chunk16
    remainder4Coefficient4Chunk15
    remainder4Coefficient4Chunk14
    remainder4Coefficient4Chunk13
    remainder4Coefficient4Chunk12
    remainder4Coefficient4Chunk11
    remainder4Coefficient4Chunk10
    remainder4Coefficient4Chunk9
    remainder4Coefficient4Chunk8
    remainder4Coefficient4Chunk7
    remainder4Coefficient4Chunk6
    remainder4Coefficient4Chunk5
    remainder4Coefficient4Chunk4
    remainder4Coefficient4Chunk3
    remainder4Coefficient4Chunk2
    remainder4Coefficient4Chunk1
    remainder4Coefficient4Chunk0
    coefficientTerm
  norm_num [Polynomial.coeff_monomial]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

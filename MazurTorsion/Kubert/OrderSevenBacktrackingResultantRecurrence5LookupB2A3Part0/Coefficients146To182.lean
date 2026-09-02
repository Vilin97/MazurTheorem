/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB2
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB2A3Part0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: B2A3 coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence5B2_coeff_0
  recurrence5B2_coeff_1
  recurrence5B2_coeff_2
  recurrence5B2_coeff_3
  recurrence5B2_coeff_4
  recurrence5B2_coeff_5
  recurrence5B2_coeff_6
  recurrence5B2_coeff_7
  recurrence5B2_coeff_8
  recurrence5B2_coeff_9
  recurrence5B2_coeff_10
  recurrence5B2_coeff_11
  recurrence5B2_coeff_12
  recurrence5B2_coeff_13
  recurrence5B2_coeff_14
  recurrence5B2_coeff_15
  recurrence5B2_coeff_16
  recurrence5B2_coeff_17
  recurrence5B2_coeff_18
  recurrence5B2_coeff_19
  recurrence5B2_coeff_20
  recurrence5B2_coeff_21
  recurrence5B2_coeff_22
  recurrence5B2_coeff_23
  recurrence5B2_coeff_24
  recurrence5B2_coeff_25
  recurrence5B2_coeff_26
  recurrence5B2_coeff_27
  recurrence5B2_coeff_28
  recurrence5B2_coeff_29
  recurrence5B2_coeff_30
  recurrence5B2_coeff_31
  recurrence5B2_coeff_32
  recurrence5B2_coeff_33
  recurrence5B2_coeff_34
  recurrence5B2_coeff_35
  recurrence5B2_coeff_36
  recurrence5B2_coeff_37
  recurrence5B2_coeff_38
  recurrence5B2_coeff_39
  recurrence5B2_coeff_40
  recurrence5B2_coeff_41
  recurrence5B2_coeff_42
  recurrence5B2_coeff_43
  recurrence5B2_coeff_44
  recurrence5B2_coeff_45
  recurrence5B2_coeff_46
  recurrence5B2_coeff_47
  recurrence5B2_coeff_48
  recurrence5B2_coeff_49
  recurrence5B2_coeff_50
  recurrence5B2_coeff_51
  recurrence5B2_coeff_52
  recurrence5B2_coeff_53
  recurrence5B2_coeff_54
  recurrence5B2_coeff_55
  recurrence5B2_coeff_56
  recurrence5B2_coeff_57
  recurrence5B2_coeff_58
  recurrence5B2_coeff_59
  recurrence5B2_coeff_60
  recurrence5B2_coeff_61
  recurrence5B2_coeff_62
  recurrence5B2_coeff_63

attribute [local simp]
  recurrence5B2_coeff_64
  recurrence5B2_coeff_65
  recurrence5B2_coeff_66
  recurrence5B2_coeff_67
  recurrence5B2_coeff_68
  recurrence5B2_coeff_69
  recurrence5B2_coeff_70
  recurrence5B2_coeff_71
  recurrence5B2_coeff_72
  recurrence5B2_coeff_73
  recurrence5B2_coeff_74
  recurrence5B2_coeff_75
  recurrence5B2_coeff_76
  recurrence5B2_coeff_77
  recurrence5B2_coeff_78
  recurrence5B2_coeff_79
  recurrence5B2_coeff_80
  recurrence5B2_coeff_81
  recurrence5B2_coeff_82
  recurrence5B2_coeff_83
  recurrence5B2_coeff_84
  recurrence5B2_coeff_85
  recurrence5B2_coeff_86
  recurrence5B2_coeff_87
  recurrence5B2_coeff_88
  recurrence5B2_coeff_89
  recurrence5B2_coeff_90
  recurrence5B2_coeff_91
  recurrence5B2_coeff_92
  recurrence5B2_coeff_93
  recurrence5B2_coeff_94
  recurrence5B2_coeff_95
  recurrence5B2_coeff_96
  recurrence5B2_coeff_97
  recurrence5B2_coeff_98
  recurrence5B2_coeff_99
  recurrence5B2_coeff_100
  recurrence5B2_coeff_101
  recurrence5B2_coeff_102
  recurrence5B2_coeff_103
  recurrence5B2_coeff_104
  recurrence5B2_coeff_105
  recurrence5B2_coeff_106
  recurrence5B2_coeff_107
  recurrence5B2_coeff_108
  recurrence5B2_coeff_109
  recurrence5B2_coeff_110
  recurrence5B2_coeff_111
  recurrence5B2_coeff_112
  recurrence5B2_coeff_113
  recurrence5B2_coeff_114
  recurrence5B2_coeff_115
  recurrence5B2_coeff_116
  recurrence5B2_coeff_117
  recurrence5B2_coeff_118
  recurrence5B2_coeff_119
  recurrence5B2_coeff_120
  recurrence5B2_coeff_121
  recurrence5B2_coeff_122
  recurrence5B2_coeff_123
  recurrence5B2_coeff_124
  recurrence5B2_coeff_125
  recurrence5B2_coeff_126
  recurrence5B2_coeff_127

attribute [local simp]
  recurrence5B2_coeff_128
  recurrence5B2_coeff_129
  recurrence5B2_coeff_130
  recurrence5B2_coeff_131
  recurrence5B2_coeff_132
  recurrence5B2_coeff_133
  recurrence5B2_coeff_134
  recurrence5B2_coeff_135
  recurrence5B2_coeff_136
  recurrence5B2_coeff_137
  recurrence5B2_coeff_138
  recurrence5B2_coeff_139
  recurrence5B2_coeff_140
  recurrence5B2_coeff_141
  recurrence5B2_coeff_142
  recurrence5B2_coeff_143
  recurrence5B2_coeff_144
  recurrence5B2_coeff_145
  recurrence5A3_coeff_0
  recurrence5A3_coeff_1
  recurrence5A3_coeff_2
  recurrence5A3_coeff_3
  recurrence5A3_coeff_4
  recurrence5A3_coeff_5
  recurrence5A3_coeff_6
  recurrence5A3_coeff_7
  recurrence5A3_coeff_8
  recurrence5A3_coeff_9
  recurrence5A3_coeff_10
  recurrence5A3_coeff_11
  recurrence5A3_coeff_12
  recurrence5A3_coeff_13
  recurrence5A3_coeff_14
  recurrence5A3_coeff_15
  recurrence5A3_coeff_16
  recurrence5A3_coeff_17
  recurrence5A3_coeff_18
  recurrence5A3_coeff_19
  recurrence5A3_coeff_20
  recurrence5A3_coeff_21
  recurrence5A3_coeff_22
  recurrence5A3_coeff_23
  recurrence5A3_coeff_24
  recurrence5A3_coeff_25
  recurrence5A3_coeff_26
  recurrence5A3_coeff_27
  recurrence5A3_coeff_28
  recurrence5A3_coeff_29
  recurrence5A3_coeff_30
  recurrence5A3_coeff_31
  recurrence5A3_coeff_32
  recurrence5A3_coeff_33
  recurrence5A3_coeff_34
  recurrence5A3_coeff_35
  recurrence5A3_coeff_36
  recurrence5A3_coeff_37
  recurrence5A3_coeff_38
  recurrence5A3_coeff_39
  recurrence5A3_coeff_40
  recurrence5A3_coeff_41
  recurrence5A3_coeff_42
  recurrence5A3_coeff_43
  recurrence5A3_coeff_44
  recurrence5A3_coeff_45

attribute [local simp]
  recurrence5A3_coeff_46
  recurrence5A3_coeff_47
  recurrence5A3_coeff_48
  recurrence5A3_coeff_49
  recurrence5A3_coeff_50
  recurrence5A3_coeff_51
  recurrence5A3_coeff_52
  recurrence5A3_coeff_53
  recurrence5A3_coeff_54
  recurrence5A3_coeff_55
  recurrence5A3_coeff_56
  recurrence5A3_coeff_57
  recurrence5A3_coeff_58
  recurrence5A3_coeff_59
  recurrence5A3_coeff_60
  recurrence5A3_coeff_61
  recurrence5A3_coeff_62
  recurrence5A3_coeff_63
  recurrence5A3_coeff_64
  recurrence5A3_coeff_65
  recurrence5A3_coeff_66
  recurrence5A3_coeff_67
  recurrence5A3_coeff_68
  recurrence5A3_coeff_69
  recurrence5A3_coeff_70
  recurrence5A3_coeff_71
  recurrence5A3_coeff_72
  recurrence5A3_coeff_73
  recurrence5A3_coeff_74
  recurrence5A3_coeff_75
  recurrence5A3_coeff_76
  recurrence5A3_coeff_77
  recurrence5A3_coeff_78
  recurrence5A3_coeff_79
  recurrence5A3_coeff_80
  recurrence5A3_coeff_81
  recurrence5A3_coeff_82
  recurrence5A3_coeff_83
  recurrence5A3_coeff_84
  recurrence5A3_coeff_85
  recurrence5A3_coeff_86
  recurrence5A3_coeff_87
  recurrence5A3_coeff_88
  recurrence5A3_coeff_89
  recurrence5A3_coeff_90
  recurrence5A3_coeff_91
  recurrence5A3_coeff_92
  recurrence5A3_coeff_93
  recurrence5A3_coeff_94
  recurrence5A3_coeff_95
  recurrence5A3_coeff_96
  recurrence5A3_coeff_97
  recurrence5A3_coeff_98
  recurrence5A3_coeff_99
  recurrence5A3_coeff_100
  recurrence5A3_coeff_101
  recurrence5A3_coeff_102
  recurrence5A3_coeff_103
  recurrence5A3_coeff_104
  recurrence5A3_coeff_105
  recurrence5A3_coeff_106
  recurrence5A3_coeff_107
  recurrence5A3_coeff_108
  recurrence5A3_coeff_109

attribute [local simp]
  recurrence5A3_coeff_110
  recurrence5A3_coeff_111
  recurrence5A3_coeff_112
  recurrence5A3_coeff_113
  recurrence5A3_coeff_114
  recurrence5A3_coeff_115
  recurrence5A3_coeff_116
  recurrence5A3_coeff_117
  recurrence5A3_coeff_118
  recurrence5A3_coeff_119
  recurrence5A3_coeff_120
  recurrence5A3_coeff_121
  recurrence5A3_coeff_122
  recurrence5A3_coeff_123
  recurrence5A3_coeff_124
  recurrence5A3_coeff_125
  recurrence5A3_coeff_126
  recurrence5A3_coeff_127
  recurrence5A3_coeff_128
  recurrence5A3_coeff_129
  recurrence5A3_coeff_130
  recurrence5A3_coeff_131
  recurrence5A3_coeff_132
  recurrence5A3_coeff_133
  recurrence5A3_coeff_134
  recurrence5A3_coeff_135
  recurrence5A3_coeff_136
  recurrence5A3_coeff_137
  recurrence5A3_coeff_138
  recurrence5A3_coeff_139
  recurrence5A3_coeff_140
  recurrence5A3_coeff_141
  recurrence5A3_coeff_142
  recurrence5A3_coeff_143
  recurrence5A3_coeff_144
  recurrence5A3_coeff_145
  recurrence5A3_coeff_146
  recurrence5A3_coeff_147
  recurrence5A3_coeff_148
  recurrence5A3_coeff_149
  recurrence5A3_coeff_150
  recurrence5A3_coeff_151
  recurrence5A3_coeff_152
  recurrence5A3_coeff_153
  recurrence5A3_coeff_154
  recurrence5A3_coeff_155
  recurrence5A3_coeff_156
  recurrence5A3_coeff_157
  recurrence5A3_coeff_158
  recurrence5A3_coeff_159
  recurrence5A3_coeff_160
  recurrence5A3_coeff_161
  recurrence5A3_coeff_162
  recurrence5A3_coeff_163
  recurrence5A3_coeff_164

private theorem recurrence5B2A3_coeff_146_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (146 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_146 :
    recurrence5B2A3.coeff 146 =
      ((((53004408474654000522 * 10 ^ 70 +
        9611925827463304631259607920592550212110385238695884822988485853715405) * 10 ^ 70 +
        8363249434209960066376833547331526482403277669120088399250310175558818) * 10 ^ 70 +
        7638906587065482330097590106657657368990183769606574003186262685908669) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 147 = 0 +
    147 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 18 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_146_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_147_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (147 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_147 :
    recurrence5B2A3.coeff 147 =
      -((((29096292211474475296 * 10 ^ 70 +
        7995395455862421799620424308556576681726967162858009151072109886870227) * 10 ^ 70 +
        2452368097610724452498160421180639011728583169759208837522353401243654) * 10 ^ 70 +
        9081468877072577081150571615767587425983348096642318608005121047754502) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 148 = 0 +
    148 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 148 = 32 +
      116 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 116 = 32 +
      84 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 84 = 32 +
      52 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 18 +
      2 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_147_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_148_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (148 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_148 :
    recurrence5B2A3.coeff 148 =
      ((((7998061486996811739 * 10 ^ 70 +
        5970116549663901476634124928338779314238051669555229971510569828421100) * 10 ^ 70 +
        1752635513483929079870733529178422184386819782443593038251762053947635) * 10 ^ 70 +
        6069053840702116929421965734255470228718765317747783027686863916847972) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 149 = 0 +
    149 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 149 = 32 +
      117 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 117 = 32 +
      85 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 18 +
      3 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_148_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_149_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (149 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_149 :
    recurrence5B2A3.coeff 149 =
      ((((9292253853043611941 * 10 ^ 70 +
        4126640789505515014455088339428447657316898297875389164229703446551006) * 10 ^ 70 +
        4205492434181869306396108664927852040067423861371389559843014253638515) * 10 ^ 70 +
        1148071367750654175445103871842545176333758916506603250684135596988842) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 150 = 0 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 18 +
      4 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_149_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_150_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (150 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_150 :
    recurrence5B2A3.coeff 150 =
      -((((22246061320683474256 * 10 ^ 70 +
        5393668794547888729454947044210143564376071395732400603276429693997845) * 10 ^ 70 +
        3278040113019386257273303231487459269338772814209656594109510861625449) * 10 ^ 70 +
        4624655591724150992522039412224725505515894164981709423344357174715219) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 151 = 0 +
    151 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 18 +
      5 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_150_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_151_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (151 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_151 :
    recurrence5B2A3.coeff 151 =
      ((((30799218932177135680 * 10 ^ 70 +
        3657011985011052484516580820163170749826102773150414082499733915962127) * 10 ^ 70 +
        9640341814901306290078182266270081156421633764949769026442555988990881) * 10 ^ 70 +
        2326476516003671517556055544850354394284603610385058742930841884954008) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 152 = 0 +
    152 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 152 = 32 +
      120 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 120 = 32 +
      88 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 88 = 32 +
      56 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 18 +
      6 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_151_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_152_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (152 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_152 :
    recurrence5B2A3.coeff 152 =
      -((((35286649927210064780 * 10 ^ 70 +
        5938946968749822792007080395809881037549378071256546389681648837344232) * 10 ^ 70 +
        3379844652405196851259849737670536688348392252154332805462928811523658) * 10 ^ 70 +
        8276295097462668905337868891017938280838384187307670278384865103203133) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 153 = 0 +
    153 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 153 = 32 +
      121 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 121 = 32 +
      89 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 18 +
      7 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_152_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_153_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (153 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_153 :
    recurrence5B2A3.coeff 153 =
      ((((36335367073180564643 * 10 ^ 70 +
        8740709800868203458260526885325822454776542085697438869002026722070825) * 10 ^ 70 +
        3640468637505278027722624459650328232871656346019787515226151416674011) * 10 ^ 70 +
        0354743640205397931865262017943473960154870645587077069116366758693245) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 154 = 0 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 18 +
      8 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_153_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_154_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (154 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_154 :
    recurrence5B2A3.coeff 154 =
      -((((34739001830002142541 * 10 ^ 70 +
        3818093932589611276999254814768848368654906929977741899261727878885447) * 10 ^ 70 +
        1287023963832946808026087150321068942758686076682323873293375640999817) * 10 ^ 70 +
        3908646535344506889450701716392722297707261226206152716599365946595273) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 155 = 0 +
    155 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 32 +
      59 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 18 +
      9 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_154_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_155_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (155 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_155 :
    recurrence5B2A3.coeff 155 =
      ((((31336077637203017449 * 10 ^ 70 +
        7341781580359141129220286914673216554953620153855359124552427894044392) * 10 ^ 70 +
        7992097449119862558512729698057320291968418683003182964491963142320765) * 10 ^ 70 +
        7032173330283439057827381038382605548217249228882921611669148441898735) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 156 = 0 +
    156 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 156 = 32 +
      124 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 124 = 32 +
      92 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 92 = 32 +
      60 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 18 +
      10 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_155_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_156_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (156 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_156 :
    recurrence5B2A3.coeff 156 =
      -((((26909320986093728586 * 10 ^ 70 +
        7066826604975513389862074553488395034637803833621632085441957375062524) * 10 ^ 70 +
        4876604160832371609060453624539476105781423562653543046546300106927094) * 10 ^ 70 +
        2899833847335148541346283485289052516742666703693083727437294103975477) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 157 = 0 +
    157 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 157 = 32 +
      125 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 125 = 32 +
      93 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 93 = 32 +
      61 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 18 +
      11 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_156_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_157_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (157 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_157 :
    recurrence5B2A3.coeff 157 =
      ((((22116083193368037019 * 10 ^ 70 +
        2026194478705153771452642752092938405657763900070086733726268838078882) * 10 ^ 70 +
        3013422084451034421510286205043346989723617886346172655164015562014163) * 10 ^ 70 +
        2427938047550740087938582762171900802109125265977705710637088259129038) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 158 = 0 +
    158 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 158 = 32 +
      126 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 126 = 32 +
      94 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 94 = 32 +
      62 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 18 +
      12 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_157_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_158_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (158 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_158 :
    recurrence5B2A3.coeff 158 =
      -((((17452429389069999126 * 10 ^ 70 +
        9968120860454475721053490833139574943119450663691138648790743560394332) * 10 ^ 70 +
        9298798142884233380352125669502636943089223771163022008936793767871471) * 10 ^ 70 +
        5131180149512333553488398338612461062182157557921678881657487603809099) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 159 = 0 +
    159 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 18 +
      13 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_158_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_159_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (159 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_159 :
    recurrence5B2A3.coeff 159 =
      ((((13247258230331290438 * 10 ^ 70 +
        8716252619227681912813221021675071468597523484599286534754522006805207) * 10 ^ 70 +
        7287755064554322192497297257890291037860565531302175010385291302330802) * 10 ^ 70 +
        2273620631099091691770366320711232910060438501075297474095546246651996) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 160 = 0 +
    160 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 160 = 32 +
      128 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 128 = 32 +
      96 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 18 +
      14 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_159_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (160 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_160 :
    recurrence5B2A3.coeff 160 =
      -((((9678886761559339602 * 10 ^ 70 +
        5378004227993245050878129836532425238062389942396156436417489371305939) * 10 ^ 70 +
        9522460634210852545760406580390157778008547757229344070555787549979933) * 10 ^ 70 +
        1665119423699917090012656838575620213701304981948321781190290036700438) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 161 = 0 +
    161 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 161 = 32 +
      129 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 129 = 32 +
      97 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 97 = 32 +
      65 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 65 = 32 +
      33 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 33 = 18 +
      15 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_160_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_161_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (161 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_161 :
    recurrence5B2A3.coeff 161 =
      ((((6805066291257012977 * 10 ^ 70 +
        7335403242129249112330335878309475609075967950191529975087126611599468) * 10 ^ 70 +
        6001989362806831429383138415792077157436639665900651049451419301042339) * 10 ^ 70 +
        3696276529982583461612954487572260639265892513524524648726289065302934) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 162 = 0 +
    162 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 162 = 32 +
      130 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 130 = 32 +
      98 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 98 = 32 +
      66 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 66 = 32 +
      34 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 34 = 18 +
      16 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_161_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_162_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (162 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_162 :
    recurrence5B2A3.coeff 162 =
      -((((4597985963462190791 * 10 ^ 70 +
        2998370441604750016804977865580698293928875272387847360840210762129320) * 10 ^ 70 +
        2128150842778610627494369571484436692868860064287990026313181262442785) * 10 ^ 70 +
        6227388048424001071341417976218755806977783022992893560510375835440445) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 163 = 0 +
    163 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 18 +
      17 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_162_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_163_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (163 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_163 :
    recurrence5B2A3.coeff 163 =
      ((((2977734495562014044 * 10 ^ 70 +
        2219350957692283305333716182994404456026553244265870779068348399957940) * 10 ^ 70 +
        8873329847634508687723418370097065362066729363770365387713021283952062) * 10 ^ 70 +
        0758952129534051167051828438124372648527804370767957088745184160029385) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 164 = 0 +
    164 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 164 = 32 +
      132 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 132 = 32 +
      100 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 100 = 32 +
      68 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 68 = 32 +
      36 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 36 = 18 +
      18 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_163_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_164_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (164 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_164 :
    recurrence5B2A3.coeff 164 =
      -((((1840130105970638463 * 10 ^ 70 +
        3556226536370025712746031159984295450081583175123552219770259150969334) * 10 ^ 70 +
        7271201233269408297348876391809424029772474549449166440424272935133546) * 10 ^ 70 +
        4142970868343618640813478031711842994540973318124595157545597995567222) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 165 = 0 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 18 +
      19 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_164_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_165_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (165 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (165 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_165 :
    recurrence5B2A3.coeff 165 =
      ((((1077142817055600210 * 10 ^ 70 +
        0870942636855391358285495946195376735149155116078965401257354313713951) * 10 ^ 70 +
        0139684888531211163645507811212437719040713224824340459209092464049678) * 10 ^ 70 +
        5922344635584405042124016944167592343729481189854456451103132313451389) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 166 = 1 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 17 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_165_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_165_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_166_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (166 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (166 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (166 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_166 :
    recurrence5B2A3.coeff 166 =
      -((((589920634810582804 * 10 ^ 70 +
        1151869042895778006487792722750827752290959688008624347539107679189918) * 10 ^ 70 +
        8465422673372832673746516591830866850800130061255333253786587170630038) * 10 ^ 70 +
        1262740223100332872056176381604860799088126011562202157847120247814918) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 167 = 2 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 16 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_166_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_166_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_167_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (167 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (167 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (167 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_167 :
    recurrence5B2A3.coeff 167 =
      ((((295545544826960237 * 10 ^ 70 +
        8375620061028405855117471097061350670942833509776737421426214323911089) * 10 ^ 70 +
        0298241592303852818995336422122648306295200596273973919252085749474534) * 10 ^ 70 +
        1025529250621122583735789808607121961433540641074868308758358297861270) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 168 = 3 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 15 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_167_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_167_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_168_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (168 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (168 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (168 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_168 :
    recurrence5B2A3.coeff 168 =
      -((((129136069238719625 * 10 ^ 70 +
        7708970947275021209986305932267016744811256903160017608979692868603595) * 10 ^ 70 +
        9979124016007845442110627114082003858825567878035916508660401028677999) * 10 ^ 70 +
        4115409904970844740097236596980621980956156576343568165568354500442443) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 169 = 4 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 14 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_168_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_168_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_169_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (169 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (169 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (169 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_169 :
    recurrence5B2A3.coeff 169 =
      ((((42938663291851582 * 10 ^ 70 +
        5507558784369621861603878526077763516388425726368231127393203099175687) * 10 ^ 70 +
        5687533966665894206581873776251464169300028471616984972233302506004716) * 10 ^ 70 +
        5552409958568118963546305498693136248779983694163375230668387305577826) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 170 = 5 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 13 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_169_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_169_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_170_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (170 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (170 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (170 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_170 :
    recurrence5B2A3.coeff 170 =
      -((((3798591993263922 * 10 ^ 70 +
        1101732191987322226469965983307747779637821134300261239624407620183468) * 10 ^ 70 +
        5733310552205879610872571344915887491924366732187945078862297562308506) * 10 ^ 70 +
        9939740150625794618245420056660383104732261259740267272036977640275721) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 171 = 6 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 12 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_170_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_170_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_171_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (171 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (171 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (171 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_171 :
    recurrence5B2A3.coeff 171 =
      -((((9964290086495450 * 10 ^ 70 +
        4886812379638302480619127111432388309277600916234528634502517520262377) * 10 ^ 70 +
        7511155888245078047700499959315953487779370432595060955103399151578186) * 10 ^ 70 +
        0614647900210431634269262398170818269553738438058024728593794132508815) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 172 = 7 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 11 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_171_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_171_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_172_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (172 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (172 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (172 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_172 :
    recurrence5B2A3.coeff 172 =
      ((((11614347209406440 * 10 ^ 70 +
        7467903802161495642947840273525598629847355584605485052421321608947728) * 10 ^ 70 +
        7750694660746558239119792322541372818965083261145835116194372650181773) * 10 ^ 70 +
        1427685171878184573629022825785351746572473803848431925862248247980085) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 173 = 8 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 10 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_172_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_172_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (173 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (173 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_173 :
    recurrence5B2A3.coeff 173 =
      -((((8635590250451800 * 10 ^ 70 +
        1748517495855765187778672329619050379208419328790435714073641970378097) * 10 ^ 70 +
        8362817079015011443204075306313803799761894826357163647541981113541434) * 10 ^ 70 +
        9709728004399398187399266899794296227036172443270280551564255972200077) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 174 = 9 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 9 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_173_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_173_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (174 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (174 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_174 :
    recurrence5B2A3.coeff 174 =
      ((((4804518517760279 * 10 ^ 70 +
        3719427902249051769984849148593519220559198539507836892732511436856961) * 10 ^ 70 +
        7645869161216947011962984640767164852127514592103138952850871917689413) * 10 ^ 70 +
        8434622767078863414054119311680898669403749711261369627651315853830431) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 175 = 10 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 8 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_174_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_174_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (175 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (175 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_175 :
    recurrence5B2A3.coeff 175 =
      -((((1700153944919593 * 10 ^ 70 +
        1303228751228143154972789103399999704644353472736512125836102183673238) * 10 ^ 70 +
        3596346141986460874338078584853323768625561553625083253840308792614132) * 10 ^ 70 +
        6066040642171526218556771852857617918414332117579906055363831850394492) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 176 = 11 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 7 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_175_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_175_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (176 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (176 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_176 :
    recurrence5B2A3.coeff 176 =
      -((((273807457213637 * 10 ^ 70 +
        9533587877892804150006033595874274282992427754880542822431311742172662) * 10 ^ 70 +
        3272566500350764975255731090323661083808506230281214333654004593191879) * 10 ^ 70 +
        1544031702402574943366875376097273972673202590701346170512831396219438) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 177 = 12 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 6 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_176_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_176_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (177 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (177 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_177 :
    recurrence5B2A3.coeff 177 =
      ((((1249746337629726 * 10 ^ 70 +
        3251305464378004495496934902177216395473189086886848387695994059172227) * 10 ^ 70 +
        7676206281752787194539439557636675472072396621861014592672334717577478) * 10 ^ 70 +
        8556870559122917861906268726490850700864648955720523566261390184635516) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 178 = 13 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 5 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_177_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_177_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (178 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (178 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_178 :
    recurrence5B2A3.coeff 178 =
      -((((1533122808269340 * 10 ^ 70 +
        3039941496092612657966023249803460431997857211763442687004985087908440) * 10 ^ 70 +
        7032365459016582136140395929379203143378120027935148859446144319665775) * 10 ^ 70 +
        7212075808283725070924919466075255726987066409072228199962497891941729) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 179 = 14 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 4 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_178_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_178_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (179 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (179 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_179 :
    recurrence5B2A3.coeff 179 =
      ((((1422895393243076 * 10 ^ 70 +
        1060655786634562774186528664415067553332401562923037936283562397203627) * 10 ^ 70 +
        4511328209314206838238331445387295206132438904548510391085017153157230) * 10 ^ 70 +
        9350257909828823085519090602960879992475667469044728445891170983450390) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 180 = 15 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 3 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_179_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_179_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (180 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (180 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_180 :
    recurrence5B2A3.coeff 180 =
      -((((1142780404012983 * 10 ^ 70 +
        1868106735158263860236220093201600789951923427098617896352405923405576) * 10 ^ 70 +
        1662588401541691395456451152217384148378782724650789469670493666163239) * 10 ^ 70 +
        8435987974335600761052915172794059133190547547994745085802108313853825) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 181 = 16 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 2 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_180_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_180_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (181 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (181 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_181 :
    recurrence5B2A3.coeff 181 =
      ((((831692892770933 * 10 ^ 70 +
        9838406854555735707307116055137756715977769977821716451184225308698500) * 10 ^ 70 +
        5713730819445154502097407353070204348915202391509385058112553754589470) * 10 ^ 70 +
        7874784021722173901274362381969889969220893823906184163454345481825717) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 182 = 17 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 1 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_181_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_181_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A3_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (182 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (182 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_182 :
    recurrence5B2A3.coeff 182 =
      -((((559996543992191 * 10 ^ 70 +
        2137880438968606639565601097837948926481344843499177733692622839504454) * 10 ^ 70 +
        3188598713540091255718969877813515485582376937531081626384534944339593) * 10 ^ 70 +
        8181964433682236648926969864747116148463943979765949881198291383739229) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 183 = 18 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_182_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_182_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

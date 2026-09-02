/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3A4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2FirstPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar2First coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4B1_coeff_1
  recurrence4B1_coeff_10
  recurrence4B1_coeff_100
  recurrence4B1_coeff_101
  recurrence4B1_coeff_102
  recurrence4B1_coeff_103
  recurrence4B1_coeff_104
  recurrence4B1_coeff_105
  recurrence4B1_coeff_106
  recurrence4B1_coeff_107
  recurrence4B1_coeff_108
  recurrence4B1_coeff_109
  recurrence4B1_coeff_11
  recurrence4B1_coeff_110
  recurrence4B1_coeff_111
  recurrence4B1_coeff_112
  recurrence4B1_coeff_113
  recurrence4B1_coeff_114
  recurrence4B1_coeff_115
  recurrence4B1_coeff_116
  recurrence4B1_coeff_117
  recurrence4B1_coeff_118
  recurrence4B1_coeff_119
  recurrence4B1_coeff_12
  recurrence4B1_coeff_120
  recurrence4B1_coeff_121
  recurrence4B1_coeff_122
  recurrence4B1_coeff_123
  recurrence4B1_coeff_124
  recurrence4B1_coeff_125
  recurrence4B1_coeff_126
  recurrence4B1_coeff_127
  recurrence4B1_coeff_128
  recurrence4B1_coeff_129
  recurrence4B1_coeff_13
  recurrence4B1_coeff_130
  recurrence4B1_coeff_131
  recurrence4B1_coeff_132
  recurrence4B1_coeff_133
  recurrence4B1_coeff_134
  recurrence4B1_coeff_135
  recurrence4B1_coeff_136
  recurrence4B1_coeff_137
  recurrence4B1_coeff_138
  recurrence4B1_coeff_139
  recurrence4B1_coeff_14
  recurrence4B1_coeff_140
  recurrence4B1_coeff_141
  recurrence4B1_coeff_142
  recurrence4B1_coeff_143
  recurrence4B1_coeff_144
  recurrence4B1_coeff_145
  recurrence4B1_coeff_146
  recurrence4B1_coeff_147
  recurrence4B1_coeff_148
  recurrence4B1_coeff_149
  recurrence4B1_coeff_15
  recurrence4B1_coeff_150
  recurrence4B1_coeff_151
  recurrence4B1_coeff_152
  recurrence4B1_coeff_153
  recurrence4B1_coeff_154
  recurrence4B1_coeff_155
  recurrence4B1_coeff_156

attribute [local simp]
  recurrence4B1_coeff_157
  recurrence4B1_coeff_158
  recurrence4B1_coeff_159
  recurrence4B1_coeff_16
  recurrence4B1_coeff_160
  recurrence4B1_coeff_161
  recurrence4B1_coeff_162
  recurrence4B1_coeff_163
  recurrence4B1_coeff_164
  recurrence4B1_coeff_165
  recurrence4B1_coeff_166
  recurrence4B1_coeff_167
  recurrence4B1_coeff_168
  recurrence4B1_coeff_169
  recurrence4B1_coeff_17
  recurrence4B1_coeff_170
  recurrence4B1_coeff_18
  recurrence4B1_coeff_19
  recurrence4B1_coeff_2
  recurrence4B1_coeff_20
  recurrence4B1_coeff_21
  recurrence4B1_coeff_22
  recurrence4B1_coeff_23
  recurrence4B1_coeff_24
  recurrence4B1_coeff_25
  recurrence4B1_coeff_26
  recurrence4B1_coeff_27
  recurrence4B1_coeff_28
  recurrence4B1_coeff_29
  recurrence4B1_coeff_3
  recurrence4B1_coeff_30
  recurrence4B1_coeff_31
  recurrence4B1_coeff_32
  recurrence4B1_coeff_33
  recurrence4B1_coeff_34
  recurrence4B1_coeff_35
  recurrence4B1_coeff_36
  recurrence4B1_coeff_37
  recurrence4B1_coeff_38
  recurrence4B1_coeff_39
  recurrence4B1_coeff_4
  recurrence4B1_coeff_40
  recurrence4B1_coeff_41
  recurrence4B1_coeff_42
  recurrence4B1_coeff_43
  recurrence4B1_coeff_44
  recurrence4B1_coeff_45
  recurrence4B1_coeff_46
  recurrence4B1_coeff_47
  recurrence4B1_coeff_48
  recurrence4B1_coeff_49
  recurrence4B1_coeff_5
  recurrence4B1_coeff_50
  recurrence4B1_coeff_51
  recurrence4B1_coeff_52
  recurrence4B1_coeff_53
  recurrence4B1_coeff_54
  recurrence4B1_coeff_55
  recurrence4B1_coeff_56
  recurrence4B1_coeff_57
  recurrence4B1_coeff_58
  recurrence4B1_coeff_59
  recurrence4B1_coeff_6
  recurrence4B1_coeff_60

attribute [local simp]
  recurrence4B1_coeff_61
  recurrence4B1_coeff_62
  recurrence4B1_coeff_63
  recurrence4B1_coeff_64
  recurrence4B1_coeff_65
  recurrence4B1_coeff_66
  recurrence4B1_coeff_67
  recurrence4B1_coeff_68
  recurrence4B1_coeff_69
  recurrence4B1_coeff_7
  recurrence4B1_coeff_70
  recurrence4B1_coeff_71
  recurrence4B1_coeff_72
  recurrence4B1_coeff_73
  recurrence4B1_coeff_74
  recurrence4B1_coeff_75
  recurrence4B1_coeff_76
  recurrence4B1_coeff_77
  recurrence4B1_coeff_78
  recurrence4B1_coeff_79
  recurrence4B1_coeff_8
  recurrence4B1_coeff_80
  recurrence4B1_coeff_81
  recurrence4B1_coeff_82
  recurrence4B1_coeff_83
  recurrence4B1_coeff_84
  recurrence4B1_coeff_85
  recurrence4B1_coeff_86
  recurrence4B1_coeff_87
  recurrence4B1_coeff_88
  recurrence4B1_coeff_89
  recurrence4B1_coeff_9
  recurrence4B1_coeff_90
  recurrence4B1_coeff_91
  recurrence4B1_coeff_92
  recurrence4B1_coeff_93
  recurrence4B1_coeff_94
  recurrence4B1_coeff_95
  recurrence4B1_coeff_96
  recurrence4B1_coeff_97
  recurrence4B1_coeff_98
  recurrence4B1_coeff_99
  recurrence4B3A4_coeff_0
  recurrence4B3A4_coeff_1
  recurrence4B3A4_coeff_10
  recurrence4B3A4_coeff_100
  recurrence4B3A4_coeff_101
  recurrence4B3A4_coeff_102
  recurrence4B3A4_coeff_103
  recurrence4B3A4_coeff_104
  recurrence4B3A4_coeff_105
  recurrence4B3A4_coeff_106
  recurrence4B3A4_coeff_107
  recurrence4B3A4_coeff_108
  recurrence4B3A4_coeff_109
  recurrence4B3A4_coeff_11
  recurrence4B3A4_coeff_110
  recurrence4B3A4_coeff_111
  recurrence4B3A4_coeff_112
  recurrence4B3A4_coeff_113
  recurrence4B3A4_coeff_114
  recurrence4B3A4_coeff_115
  recurrence4B3A4_coeff_116
  recurrence4B3A4_coeff_117

attribute [local simp]
  recurrence4B3A4_coeff_118
  recurrence4B3A4_coeff_119
  recurrence4B3A4_coeff_12
  recurrence4B3A4_coeff_120
  recurrence4B3A4_coeff_121
  recurrence4B3A4_coeff_122
  recurrence4B3A4_coeff_123
  recurrence4B3A4_coeff_124
  recurrence4B3A4_coeff_125
  recurrence4B3A4_coeff_126
  recurrence4B3A4_coeff_127
  recurrence4B3A4_coeff_128
  recurrence4B3A4_coeff_129
  recurrence4B3A4_coeff_13
  recurrence4B3A4_coeff_130
  recurrence4B3A4_coeff_131
  recurrence4B3A4_coeff_132
  recurrence4B3A4_coeff_133
  recurrence4B3A4_coeff_134
  recurrence4B3A4_coeff_135
  recurrence4B3A4_coeff_136
  recurrence4B3A4_coeff_137
  recurrence4B3A4_coeff_138
  recurrence4B3A4_coeff_139
  recurrence4B3A4_coeff_14
  recurrence4B3A4_coeff_140
  recurrence4B3A4_coeff_141
  recurrence4B3A4_coeff_142
  recurrence4B3A4_coeff_143
  recurrence4B3A4_coeff_144
  recurrence4B3A4_coeff_145
  recurrence4B3A4_coeff_146
  recurrence4B3A4_coeff_147
  recurrence4B3A4_coeff_148
  recurrence4B3A4_coeff_149
  recurrence4B3A4_coeff_15
  recurrence4B3A4_coeff_150
  recurrence4B3A4_coeff_151
  recurrence4B3A4_coeff_152
  recurrence4B3A4_coeff_153
  recurrence4B3A4_coeff_154
  recurrence4B3A4_coeff_155
  recurrence4B3A4_coeff_156
  recurrence4B3A4_coeff_157
  recurrence4B3A4_coeff_158
  recurrence4B3A4_coeff_159
  recurrence4B3A4_coeff_16
  recurrence4B3A4_coeff_160
  recurrence4B3A4_coeff_161
  recurrence4B3A4_coeff_162
  recurrence4B3A4_coeff_163
  recurrence4B3A4_coeff_164
  recurrence4B3A4_coeff_165
  recurrence4B3A4_coeff_166
  recurrence4B3A4_coeff_167
  recurrence4B3A4_coeff_168
  recurrence4B3A4_coeff_169
  recurrence4B3A4_coeff_17
  recurrence4B3A4_coeff_18
  recurrence4B3A4_coeff_19
  recurrence4B3A4_coeff_2
  recurrence4B3A4_coeff_20
  recurrence4B3A4_coeff_21
  recurrence4B3A4_coeff_22

attribute [local simp]
  recurrence4B3A4_coeff_23
  recurrence4B3A4_coeff_24
  recurrence4B3A4_coeff_25
  recurrence4B3A4_coeff_26
  recurrence4B3A4_coeff_27
  recurrence4B3A4_coeff_28
  recurrence4B3A4_coeff_29
  recurrence4B3A4_coeff_3
  recurrence4B3A4_coeff_30
  recurrence4B3A4_coeff_31
  recurrence4B3A4_coeff_32
  recurrence4B3A4_coeff_33
  recurrence4B3A4_coeff_34
  recurrence4B3A4_coeff_35
  recurrence4B3A4_coeff_36
  recurrence4B3A4_coeff_37
  recurrence4B3A4_coeff_38
  recurrence4B3A4_coeff_39
  recurrence4B3A4_coeff_4
  recurrence4B3A4_coeff_40
  recurrence4B3A4_coeff_41
  recurrence4B3A4_coeff_42
  recurrence4B3A4_coeff_43
  recurrence4B3A4_coeff_44
  recurrence4B3A4_coeff_45
  recurrence4B3A4_coeff_46
  recurrence4B3A4_coeff_47
  recurrence4B3A4_coeff_48
  recurrence4B3A4_coeff_49
  recurrence4B3A4_coeff_5
  recurrence4B3A4_coeff_50
  recurrence4B3A4_coeff_51
  recurrence4B3A4_coeff_52
  recurrence4B3A4_coeff_53
  recurrence4B3A4_coeff_54
  recurrence4B3A4_coeff_55
  recurrence4B3A4_coeff_56
  recurrence4B3A4_coeff_57
  recurrence4B3A4_coeff_58
  recurrence4B3A4_coeff_59
  recurrence4B3A4_coeff_6
  recurrence4B3A4_coeff_60
  recurrence4B3A4_coeff_61
  recurrence4B3A4_coeff_62
  recurrence4B3A4_coeff_63
  recurrence4B3A4_coeff_64
  recurrence4B3A4_coeff_65
  recurrence4B3A4_coeff_66
  recurrence4B3A4_coeff_67
  recurrence4B3A4_coeff_68
  recurrence4B3A4_coeff_69
  recurrence4B3A4_coeff_7
  recurrence4B3A4_coeff_70
  recurrence4B3A4_coeff_71
  recurrence4B3A4_coeff_72
  recurrence4B3A4_coeff_73
  recurrence4B3A4_coeff_74
  recurrence4B3A4_coeff_75
  recurrence4B3A4_coeff_76
  recurrence4B3A4_coeff_77
  recurrence4B3A4_coeff_78
  recurrence4B3A4_coeff_79
  recurrence4B3A4_coeff_8
  recurrence4B3A4_coeff_80

attribute [local simp]
  recurrence4B3A4_coeff_81
  recurrence4B3A4_coeff_82
  recurrence4B3A4_coeff_83
  recurrence4B3A4_coeff_84
  recurrence4B3A4_coeff_85
  recurrence4B3A4_coeff_86
  recurrence4B3A4_coeff_87
  recurrence4B3A4_coeff_88
  recurrence4B3A4_coeff_89
  recurrence4B3A4_coeff_9
  recurrence4B3A4_coeff_90
  recurrence4B3A4_coeff_91
  recurrence4B3A4_coeff_92
  recurrence4B3A4_coeff_93
  recurrence4B3A4_coeff_94
  recurrence4B3A4_coeff_95
  recurrence4B3A4_coeff_96
  recurrence4B3A4_coeff_97
  recurrence4B3A4_coeff_98
  recurrence4B3A4_coeff_99

private theorem recurrence4Scalar2First_coeff_135_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (135 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (135 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_135 :
    recurrence4Scalar2First.coeff 135 =
      -((((180011544192083890856624659995347251574532967512848386265 * 10 ^ 70 +
        3431824470914981603605145987148838377644871815097350586675220048781099) * 10 ^ 70 +
        7043327682544307377854478258931887718082673080832233784121077701426938) * 10 ^ 70 +
        4927014149520823771181033860629934288689280844482664366058576040874083) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 136,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (135 - x)) = _
  rw [show 136 = 1 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_135_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_136_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (136 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (136 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_136 :
    recurrence4Scalar2First.coeff 136 =
      ((((1002228748330007235886381119128549344503174451882293596986 * 10 ^ 70 +
        1781157804698553471892814544257276487289092422749573536965906358421583) * 10 ^ 70 +
        5138657786674785282854536506702685459910898840526950421368788617607739) * 10 ^ 70 +
        6690404415925987496546977619265437708853606906742804623694546449620730) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 137,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (136 - x)) = _
  rw [show 137 = 1 +
    136 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 136 = 32 +
      104 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 104 = 32 +
      72 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 72 = 32 +
      40 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_136_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_137_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (137 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (137 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_137 :
    recurrence4Scalar2First.coeff 137 =
      -((((5476852908987378148662580912658001297812529235053988949859 * 10 ^ 70 +
        7939355404293759555348538896981105136740804733147039565238874682278611) * 10 ^ 70 +
        4161489851166606561920114908446662963543910364103351157258755437516854) * 10 ^ 70 +
        1278759846489516820094451008092647186952272438841964405901141191845018) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 138,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (137 - x)) = _
  rw [show 138 = 1 +
    137 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 32 +
      41 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_137_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_138_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (138 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (138 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_138 :
    recurrence4Scalar2First.coeff 138 =
      ((((29380565805858881903260830581584462513145094313736850295126 * 10 ^ 70 +
        3758508761050444788056910741089775443341099927735775806965841492434755) * 10 ^ 70 +
        4216962494851861820083761514705062804046647104127002840943295531398730) * 10 ^ 70 +
        5894243587083591608972071167241172309949260072101477829334086538886843) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 139,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (138 - x)) = _
  rw [show 139 = 1 +
    138 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 32 +
      74 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 74 = 32 +
      42 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_138_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_139_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (139 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (139 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_139 :
    recurrence4Scalar2First.coeff 139 =
      -((((154745960008811971184850981776125429688811549819227934318774 * 10 ^ 70 +
        2431944973469564452463242385877330879572895706120345897083325795326655) * 10 ^ 70 +
        8374051304667599235357971092579035431440570532111743253171363068297521) * 10 ^ 70 +
        7131323694536410990461072329292061387678182873292802152997317776610780) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 140,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (139 - x)) = _
  rw [show 140 = 1 +
    139 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 139 = 32 +
      107 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_139_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_140_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (140 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (140 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_140 :
    recurrence4Scalar2First.coeff 140 =
      ((((800335291703524337270644256600183919153212001938722028571333 * 10 ^ 70 +
        2280690219675111077699487342490365441531340784200688565829759749628838) * 10 ^ 70 +
        9831502117930350759202597326261760862859893358942635772787034307937230) * 10 ^ 70 +
        7496364424641887611823538844948322538361078108471835787919725169512302) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 141,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (140 - x)) = _
  rw [show 141 = 1 +
    140 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 140 = 32 +
      108 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 108 = 32 +
      76 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 76 = 32 +
      44 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_140_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_141_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (141 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (141 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_141 :
    recurrence4Scalar2First.coeff 141 =
      -((((4065179535766720550622721822734078195225240907255434289450499 * 10 ^ 70 +
        7327846069929714903218342772292597700338877861420857803357328909034321) * 10 ^ 70 +
        1487621640497160444388942289799058648089890397262254686790855607952064) * 10 ^ 70 +
        6267366125680878178826173002371838967416544286545885253427187055721043) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 142,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (141 - x)) = _
  rw [show 142 = 1 +
    141 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_141_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_142_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (142 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (142 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_142 :
    recurrence4Scalar2First.coeff 142 =
      ((((20281614912343762060350662769181219574269230401286300485844365 * 10 ^ 70 +
        3131251865406317611461254295500473526178068294768297575531107252747278) * 10 ^ 70 +
        4194620810398510934704859819737419871397489254364211618954639420327826) * 10 ^ 70 +
        2187049389445259364908868690390263684749461873531989316388413729677877) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 143,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (142 - x)) = _
  rw [show 143 = 1 +
    142 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 142 = 32 +
      110 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 110 = 32 +
      78 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 78 = 32 +
      46 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_142_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_143_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (143 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (143 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_143 :
    recurrence4Scalar2First.coeff 143 =
      -((((99402807570212626575370619430044987669369779475402788395860961 * 10 ^ 70 +
        5157594635120212788860820102475707499292450140014704954209763069364763) * 10 ^ 70 +
        7093198577729290726512307029498686640881704348473228432232736513493823) * 10 ^ 70 +
        1382555421339408985603251978259982856536696753857218895944094566230769) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 144,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (143 - x)) = _
  rw [show 144 = 1 +
    143 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 143 = 32 +
      111 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_143_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_144_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (144 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (144 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_144 :
    recurrence4Scalar2First.coeff 144 =
      ((((478657391794455437085720954120945205981823008579079881210100442 * 10 ^ 70 +
        8899970425427723852816494345126866562136323068118027212701457132160645) * 10 ^ 70 +
        3658897014837890724545418294381636624255309807606031976961302539058777) * 10 ^ 70 +
        3088641613339754698579358394622600240431151926744611649756134197752305) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 145,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (144 - x)) = _
  rw [show 145 = 1 +
    144 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 144 = 32 +
      112 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 112 = 32 +
      80 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 80 = 32 +
      48 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_144_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_145_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (145 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (145 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_145 :
    recurrence4Scalar2First.coeff 145 =
      -((((2264832201462555152110211081582827500386084369857531286895159091 * 10 ^ 70 +
        5376379660254241699443120352858581514888085239714653912042008820068707) * 10 ^ 70 +
        2339354875771638049990170041607287415292086374731616357932850819625324) * 10 ^ 70 +
        8214622349203494638263284021720308511425710920111703744829600722104882) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 146,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (145 - x)) = _
  rw [show 146 = 1 +
    145 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_145_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_146_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (146 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (146 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_146 :
    recurrence4Scalar2First.coeff 146 =
      ((((10531399354504203319202116218534021209728659131486883391275625056 * 10 ^ 70 +
        5876131367179353019718819201243092270755922927950029671584923521963761) * 10 ^ 70 +
        9678238719255338040708691441217667565110629828949118867535129538300657) * 10 ^ 70 +
        2151742358009415772239488223456163198157646896985225380797564862819266) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 147,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (146 - x)) = _
  rw [show 147 = 1 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_146_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_147_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (147 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (147 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_147 :
    recurrence4Scalar2First.coeff 147 =
      -((((48131247651155045773012313399937320940597665023323872368310639032 * 10 ^ 70 +
        8740493475061944518688304183575967728897320041971670292442702717504147) * 10 ^ 70 +
        8472460711378288049392899154291090601000113641519728965415877969326737) * 10 ^ 70 +
        9521820095400098371513243643307303179404085659977363293320317535531796) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 148,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (147 - x)) = _
  rw [show 148 = 1 +
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
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_147_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_148_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (148 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (148 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_148 :
    recurrence4Scalar2First.coeff 148 =
      ((((216227007012734650162536268463803302100986157852094626882741255464 * 10 ^ 70 +
        2792898957056807273675000693536971197428932609329228876539831817026231) * 10 ^ 70 +
        4016529445866094619260105047258370425936663340001335974332963179124245) * 10 ^ 70 +
        7486409533233085220591710791057702311682980139532183897422348397190694) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 149,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (148 - x)) = _
  rw [show 149 = 1 +
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
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_148_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_149_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (149 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (149 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_149 :
    recurrence4Scalar2First.coeff 149 =
      -((((954957317060552086028017964034540157093661255466558147487954716657 * 10 ^ 70 +
        1398134139029240096683460323066625779036047892413164582975907339662702) * 10 ^ 70 +
        3585696964987479529201253927185516064258333820241187742691252320899433) * 10 ^ 70 +
        9017183429102095270289543895855349420442808819535133818583939733867350) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 150,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (149 - x)) = _
  rw [show 150 = 1 +
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
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_149_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_150_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (150 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (150 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_150 :
    recurrence4Scalar2First.coeff 150 =
      ((((4146649154259387421540851083906629545611884523484038086141355165734 * 10 ^ 70 +
        5502093027156925249005805560584512925291717845117647462889867369826255) * 10 ^ 70 +
        0010051135889964862405471587663314398160632807988225743644627617116320) * 10 ^ 70 +
        0048980499450348128970988669131063874652723461070710152274500087867423) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 151,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (150 - x)) = _
  rw [show 151 = 1 +
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
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_150_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_151_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (151 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (151 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_151 :
    recurrence4Scalar2First.coeff 151 =
      -((((17705032990267336746824923810006323018691640958673383023330754456779 * 10 ^ 70 +
        6540005836472031547928415829022918156974559221822795502767226243548794) * 10 ^ 70 +
        7501829310729069594860231553713429365854786863153747494608791322665201) * 10 ^ 70 +
        7363587085608982450652563870243516182691078365286143305470108798528552) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 152,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (151 - x)) = _
  rw [show 152 = 1 +
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_151_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_152_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (152 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (152 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_152 :
    recurrence4Scalar2First.coeff 152 =
      ((((74340908478625699504379446910320593358486053230790520712313931612675 * 10 ^ 70 +
        4964151685751705274697732189142259362181429670897074096722155988577668) * 10 ^ 70 +
        6935955345676248558283244137574935314444414555736768906273852284070017) * 10 ^ 70 +
        7895571007031016052848632634818676996527834667876824120163130322455818) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 153,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (152 - x)) = _
  rw [show 153 = 1 +
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
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_152_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_153_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (153 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (153 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_153 :
    recurrence4Scalar2First.coeff 153 =
      -((((306997613202565783579107356091263989512946323302195733320993186550060 * 10 ^ 70 +
        3043979126663146248063890552791211743159987375444269606931713137092989) * 10 ^ 70 +
        1057079896296276500342052424615828991358658123509296144156961808365346) * 10 ^ 70 +
        2904488261338181274359345337125477872383871311809088131893263423046295) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 154,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (153 - x)) = _
  rw [show 154 = 1 +
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
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_153_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_154_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (154 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (154 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_154 :
    recurrence4Scalar2First.coeff 154 =
      ((((1246985183026721541918874282389713707488161750632476708647849746626016 * 10 ^ 70 +
        2474332267131400380479647472066484815371415074504368538233515002367940) * 10 ^ 70 +
        2506207412737678141480689167036865057837862416065696680770570151103420) * 10 ^ 70 +
        6245156650281203292933971246751982305313740702628704814739253607662152) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 155,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (154 - x)) = _
  rw [show 155 = 1 +
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
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_154_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_155_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (155 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (155 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_155 :
    recurrence4Scalar2First.coeff 155 =
      -((((4982516400249822411939906348293609830007470129577830800984867865666726 * 10 ^ 70 +
        2270600711004488145708153135770840130391685179382025922417763701000451) * 10 ^ 70 +
        4075319454100652063733472960672368108407675086560380556755755155928949) * 10 ^ 70 +
        8739409887924417722227487497396036780637745347136999229174849727661452) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 156,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (155 - x)) = _
  rw [show 156 = 1 +
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
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_155_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_156_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (156 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (156 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_156 :
    recurrence4Scalar2First.coeff 156 =
      (((((1 * 10 ^ 70 +
        9585659180697986698464935028558997928739341676122464195302062405073455) * 10 ^ 70 +
        0523497892762364070885386378261778909039344653527657097301816136135623) * 10 ^ 70 +
        6735735600212725120376084551588755861257768369686868805399982521201113) * 10 ^ 70 +
        7443610060549382379743633051479398100646910284050243566341263165013876) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 157,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (156 - x)) = _
  rw [show 157 = 1 +
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
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_156_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_157_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (157 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (157 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_157 :
    recurrence4Scalar2First.coeff 157 =
      -(((((7 * 10 ^ 70 +
        5747695416222010917966834515496075331629943329153327153326858121924403) * 10 ^ 70 +
        6283090730679536312379328202901599996850755465261831007115778762130798) * 10 ^ 70 +
        0554138124942248620335226279639830337763515302957066233647038839360587) * 10 ^ 70 +
        0121593401775430145780980751948866191301649529172194364808365006772433) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 158,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (157 - x)) = _
  rw [show 158 = 1 +
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
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_157_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_158_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (158 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (158 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_158 :
    recurrence4Scalar2First.coeff 158 =
      (((((28 * 10 ^ 70 +
        8257835855162873403576699626767489829624793963711278790965780171901728) * 10 ^ 70 +
        5018519543838774035846867642058257695782449141533850480154092156558147) * 10 ^ 70 +
        6035785975590620901844905669431696543075454449684075993765829481229897) * 10 ^ 70 +
        3270728186209123104102328194236184221643251416281859691822952653174870) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 159,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (158 - x)) = _
  rw [show 159 = 1 +
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
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_158_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_159_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (159 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (159 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_159 :
    recurrence4Scalar2First.coeff 159 =
      -(((((107 * 10 ^ 70 +
        9470878451638148365580250861970468726797501756935642310966856470770803) * 10 ^ 70 +
        7831681582040418343821307993392325039336970259753688083983167997660414) * 10 ^ 70 +
        9779861915009868955236071478776233399841051206037411278361428654949440) * 10 ^ 70 +
        9096144851345720223609109322906099307537721850777042524548559912693787) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 160,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (159 - x)) = _
  rw [show 160 = 1 +
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
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_159_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_160_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (160 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (160 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_160 :
    recurrence4Scalar2First.coeff 160 =
      (((((397 * 10 ^ 70 +
        8281177927295801055425563689587959255899986307745727414817065448050015) * 10 ^ 70 +
        8727716434429854002097946793145395948000618948128249986041773655126431) * 10 ^ 70 +
        2207851772261117537202097936076093589001686744809964481776219768565719) * 10 ^ 70 +
        2180461267504590215906939299447282914862987805056044101701448909623697) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 161,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (160 - x)) = _
  rw [show 161 = 1 +
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
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_160_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_161_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (161 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (161 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_161 :
    recurrence4Scalar2First.coeff 161 =
      -(((((1443 * 10 ^ 70 +
        0134635539137491055454102465884851170297373044794049113797826035473777) * 10 ^ 70 +
        6927580810577956344353352118647621464280389749324350469270952788203294) * 10 ^ 70 +
        5246840971751434673309266305553826626136589593163008498704335489527596) * 10 ^ 70 +
        6819272259287132624998937811203701933427047437464179796398103903041379) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 162,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (161 - x)) = _
  rw [show 162 = 1 +
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
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_161_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_162_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (162 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (162 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_162 :
    recurrence4Scalar2First.coeff 162 =
      (((((5151 * 10 ^ 70 +
        9342294604044035799888419592860247511097459238547312945477989385139162) * 10 ^ 70 +
        4468338754837650206289201360497120537374474713196134463807315916510091) * 10 ^ 70 +
        1703695953116785098813640542552052327172651153238204230788911476310885) * 10 ^ 70 +
        6401423590827722961021030516735052490106445301439039127890839817203175) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 163,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (162 - x)) = _
  rw [show 163 = 1 +
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
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_162_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_163_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (163 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (163 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_163 :
    recurrence4Scalar2First.coeff 163 =
      -(((((18106 * 10 ^ 70 +
        2686886842230521461831948386470578567664848550544334794227217375898904) * 10 ^ 70 +
        1406451358882189096465888782922149288021497251681951936270252425479450) * 10 ^ 70 +
        5373650121956286272356066185693957083578814462174190751338169909582069) * 10 ^ 70 +
        3541763064638239414809431548281436187795697050559109576048659054736787) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 164,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (163 - x)) = _
  rw [show 164 = 1 +
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
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_163_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_164_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (164 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (164 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_164 :
    recurrence4Scalar2First.coeff 164 =
      (((((62643 * 10 ^ 70 +
        9467455537495201072063165255954398158567685653183290970551881404006870) * 10 ^ 70 +
        6164839325880133862341663298609116887065191345214923695202956209232681) * 10 ^ 70 +
        5463297981523869130273974193212195262049197323464450256204455046866152) * 10 ^ 70 +
        0652884387774462420588598997316858449396607839838924935543722270688972) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 165,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (164 - x)) = _
  rw [show 165 = 1 +
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
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_164_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_165_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (165 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (165 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_165 :
    recurrence4Scalar2First.coeff 165 =
      -(((((213379 * 10 ^ 70 +
        4697875622817213079455875836230566249721150350743170899100329599887857) * 10 ^ 70 +
        7310624135640886640309724728746327818522341910504023265604606568926847) * 10 ^ 70 +
        1505391191393127901225088219018624594477197654411537716308742917082443) * 10 ^ 70 +
        2936935225096956329312020634358518059043865786524176603739869274161424) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 166,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (165 - x)) = _
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
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_165_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_166_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (166 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (166 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_166 :
    recurrence4Scalar2First.coeff 166 =
      (((((715616 * 10 ^ 70 +
        7582755540689082420339242413167911986388647916066631015681170011488384) * 10 ^ 70 +
        7093685895563513124852776393605820143476414774046407727158523644683717) * 10 ^ 70 +
        7910265068350385539490469267321960041656401320363880385776216377365111) * 10 ^ 70 +
        9434294108600596354587485854895290410864781287914590517854732154537071) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 167,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (166 - x)) = _
  rw [show 167 = 1 +
    166 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 32 +
      70 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 70 = 32 +
      38 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_166_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_167_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (167 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (167 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_167 :
    recurrence4Scalar2First.coeff 167 =
      -(((((2363158 * 10 ^ 70 +
        4249501193626123291519358709433106406500376571254393187408125771584521) * 10 ^ 70 +
        4810010811358234059667237889773069594003803033082554268357289887777540) * 10 ^ 70 +
        9288562587272146936936696053343649778692647401729833741506408832278386) * 10 ^ 70 +
        7848419964419122202011115467393190370401686842779443603307212329549969) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 168,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (167 - x)) = _
  rw [show 168 = 1 +
    167 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 167 = 32 +
      135 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_167_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_168_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (168 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (168 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_168 :
    recurrence4Scalar2First.coeff 168 =
      (((((7684558 * 10 ^ 70 +
        1630199865498522550864673098485247738269740851331145061608613588273539) * 10 ^ 70 +
        8288118749805618646200742805067366396213061327133199797378565394012005) * 10 ^ 70 +
        8266418162092923103188118197618002594189902432084453038207607815236155) * 10 ^ 70 +
        4978396115661421550766011551373894830242439733246703779550649762031361) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 169,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (168 - x)) = _
  rw [show 169 = 1 +
    168 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 168 = 32 +
      136 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 136 = 32 +
      104 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 104 = 32 +
      72 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 72 = 32 +
      40 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_168_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_169_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (169 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (169 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_169 :
    recurrence4Scalar2First.coeff 169 =
      -(((((24608612 * 10 ^ 70 +
        6204056318763424557022648447242611406723534389239986259718609275482932) * 10 ^ 70 +
        1840784688829562103040948823214801868481626042365998454174620223242809) * 10 ^ 70 +
        1152791120066236253907704220132541730363245204038815075705673460850169) * 10 ^ 70 +
        1394045440374798236856129144884762899454933607076956386513451376981874) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 170,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (169 - x)) = _
  rw [show 170 = 1 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 32 +
      41 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_169_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_170_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (170 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (170 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar2First_coeff_170 :
    recurrence4Scalar2First.coeff 170 =
      (((((77611332 * 10 ^ 70 +
        7339032365695888581503346677456928228628410468568237115580230810823091) * 10 ^ 70 +
        5777429130272270265249930096095915303559510754809512149759817326425607) * 10 ^ 70 +
        1791194431820914256571696602618269946096659304847276836644591226487453) * 10 ^ 70 +
        1123427408891979116992579862953658020484911394586749364391750786975136) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 171,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (170 - x)) = _
  rw [show 171 = 1 +
    170 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 32 +
      74 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 74 = 32 +
      42 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_170_prefix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

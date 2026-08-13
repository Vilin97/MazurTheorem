/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB2
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB2A4Part1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: B2A4 coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4A4_coeff_100
  recurrence4A4_coeff_101
  recurrence4A4_coeff_102
  recurrence4A4_coeff_103
  recurrence4A4_coeff_104
  recurrence4A4_coeff_105
  recurrence4A4_coeff_106
  recurrence4A4_coeff_107
  recurrence4A4_coeff_108
  recurrence4A4_coeff_109
  recurrence4A4_coeff_110
  recurrence4A4_coeff_111
  recurrence4A4_coeff_112
  recurrence4A4_coeff_113
  recurrence4A4_coeff_114
  recurrence4A4_coeff_115
  recurrence4A4_coeff_116
  recurrence4A4_coeff_117
  recurrence4A4_coeff_118
  recurrence4A4_coeff_119
  recurrence4A4_coeff_120
  recurrence4A4_coeff_121
  recurrence4A4_coeff_122
  recurrence4A4_coeff_123
  recurrence4A4_coeff_124
  recurrence4A4_coeff_125
  recurrence4A4_coeff_126
  recurrence4A4_coeff_127
  recurrence4A4_coeff_128
  recurrence4A4_coeff_129
  recurrence4A4_coeff_130
  recurrence4A4_coeff_131
  recurrence4A4_coeff_132
  recurrence4A4_coeff_133
  recurrence4A4_coeff_134
  recurrence4A4_coeff_135
  recurrence4A4_coeff_136
  recurrence4A4_coeff_137
  recurrence4A4_coeff_138
  recurrence4A4_coeff_139
  recurrence4A4_coeff_140
  recurrence4A4_coeff_141
  recurrence4A4_coeff_142
  recurrence4A4_coeff_143
  recurrence4A4_coeff_144
  recurrence4A4_coeff_145
  recurrence4A4_coeff_146
  recurrence4A4_coeff_147
  recurrence4A4_coeff_148
  recurrence4A4_coeff_149
  recurrence4A4_coeff_150
  recurrence4A4_coeff_151
  recurrence4A4_coeff_152
  recurrence4A4_coeff_153
  recurrence4A4_coeff_154
  recurrence4A4_coeff_155
  recurrence4A4_coeff_156
  recurrence4A4_coeff_157
  recurrence4A4_coeff_158
  recurrence4A4_coeff_159
  recurrence4A4_coeff_160
  recurrence4A4_coeff_161
  recurrence4A4_coeff_162
  recurrence4A4_coeff_163

attribute [local simp]
  recurrence4A4_coeff_164
  recurrence4A4_coeff_165
  recurrence4A4_coeff_166
  recurrence4A4_coeff_167
  recurrence4A4_coeff_168
  recurrence4A4_coeff_169
  recurrence4A4_coeff_170
  recurrence4A4_coeff_171
  recurrence4A4_coeff_172
  recurrence4A4_coeff_173
  recurrence4A4_coeff_174
  recurrence4A4_coeff_175
  recurrence4A4_coeff_176
  recurrence4A4_coeff_177
  recurrence4A4_coeff_178
  recurrence4A4_coeff_48
  recurrence4A4_coeff_49
  recurrence4A4_coeff_50
  recurrence4A4_coeff_51
  recurrence4A4_coeff_52
  recurrence4A4_coeff_53
  recurrence4A4_coeff_54
  recurrence4A4_coeff_55
  recurrence4A4_coeff_56
  recurrence4A4_coeff_57
  recurrence4A4_coeff_58
  recurrence4A4_coeff_59
  recurrence4A4_coeff_60
  recurrence4A4_coeff_61
  recurrence4A4_coeff_62
  recurrence4A4_coeff_63
  recurrence4A4_coeff_64
  recurrence4A4_coeff_65
  recurrence4A4_coeff_66
  recurrence4A4_coeff_67
  recurrence4A4_coeff_68
  recurrence4A4_coeff_69
  recurrence4A4_coeff_70
  recurrence4A4_coeff_71
  recurrence4A4_coeff_72
  recurrence4A4_coeff_73
  recurrence4A4_coeff_74
  recurrence4A4_coeff_75
  recurrence4A4_coeff_76
  recurrence4A4_coeff_77
  recurrence4A4_coeff_78
  recurrence4A4_coeff_79
  recurrence4A4_coeff_80
  recurrence4A4_coeff_81
  recurrence4A4_coeff_82
  recurrence4A4_coeff_83
  recurrence4A4_coeff_84
  recurrence4A4_coeff_85
  recurrence4A4_coeff_86
  recurrence4A4_coeff_87
  recurrence4A4_coeff_88
  recurrence4A4_coeff_89
  recurrence4A4_coeff_90
  recurrence4A4_coeff_91
  recurrence4A4_coeff_92
  recurrence4A4_coeff_93
  recurrence4A4_coeff_94
  recurrence4A4_coeff_95
  recurrence4A4_coeff_96

attribute [local simp]
  recurrence4A4_coeff_97
  recurrence4A4_coeff_98
  recurrence4A4_coeff_99
  recurrence4B2_coeff_100
  recurrence4B2_coeff_101
  recurrence4B2_coeff_102
  recurrence4B2_coeff_103
  recurrence4B2_coeff_104
  recurrence4B2_coeff_105
  recurrence4B2_coeff_106
  recurrence4B2_coeff_107
  recurrence4B2_coeff_108
  recurrence4B2_coeff_109
  recurrence4B2_coeff_110
  recurrence4B2_coeff_111
  recurrence4B2_coeff_112
  recurrence4B2_coeff_113
  recurrence4B2_coeff_114
  recurrence4B2_coeff_115
  recurrence4B2_coeff_116
  recurrence4B2_coeff_117
  recurrence4B2_coeff_118
  recurrence4B2_coeff_119
  recurrence4B2_coeff_120
  recurrence4B2_coeff_121
  recurrence4B2_coeff_122
  recurrence4B2_coeff_123
  recurrence4B2_coeff_124
  recurrence4B2_coeff_125
  recurrence4B2_coeff_126
  recurrence4B2_coeff_127
  recurrence4B2_coeff_128
  recurrence4B2_coeff_129
  recurrence4B2_coeff_130
  recurrence4B2_coeff_131
  recurrence4B2_coeff_132
  recurrence4B2_coeff_133
  recurrence4B2_coeff_134
  recurrence4B2_coeff_135
  recurrence4B2_coeff_136
  recurrence4B2_coeff_137
  recurrence4B2_coeff_138
  recurrence4B2_coeff_139
  recurrence4B2_coeff_140
  recurrence4B2_coeff_141
  recurrence4B2_coeff_142
  recurrence4B2_coeff_143
  recurrence4B2_coeff_144
  recurrence4B2_coeff_145
  recurrence4B2_coeff_146
  recurrence4B2_coeff_147
  recurrence4B2_coeff_148
  recurrence4B2_coeff_149
  recurrence4B2_coeff_150
  recurrence4B2_coeff_151
  recurrence4B2_coeff_152
  recurrence4B2_coeff_153
  recurrence4B2_coeff_154
  recurrence4B2_coeff_155
  recurrence4B2_coeff_156
  recurrence4B2_coeff_157
  recurrence4B2_coeff_158
  recurrence4B2_coeff_159
  recurrence4B2_coeff_160

attribute [local simp]
  recurrence4B2_coeff_161
  recurrence4B2_coeff_162
  recurrence4B2_coeff_163
  recurrence4B2_coeff_164
  recurrence4B2_coeff_165
  recurrence4B2_coeff_166
  recurrence4B2_coeff_167
  recurrence4B2_coeff_168
  recurrence4B2_coeff_38
  recurrence4B2_coeff_39
  recurrence4B2_coeff_40
  recurrence4B2_coeff_41
  recurrence4B2_coeff_42
  recurrence4B2_coeff_43
  recurrence4B2_coeff_44
  recurrence4B2_coeff_45
  recurrence4B2_coeff_46
  recurrence4B2_coeff_47
  recurrence4B2_coeff_48
  recurrence4B2_coeff_49
  recurrence4B2_coeff_50
  recurrence4B2_coeff_51
  recurrence4B2_coeff_52
  recurrence4B2_coeff_53
  recurrence4B2_coeff_54
  recurrence4B2_coeff_55
  recurrence4B2_coeff_56
  recurrence4B2_coeff_57
  recurrence4B2_coeff_58
  recurrence4B2_coeff_59
  recurrence4B2_coeff_60
  recurrence4B2_coeff_61
  recurrence4B2_coeff_62
  recurrence4B2_coeff_63
  recurrence4B2_coeff_64
  recurrence4B2_coeff_65
  recurrence4B2_coeff_66
  recurrence4B2_coeff_67
  recurrence4B2_coeff_68
  recurrence4B2_coeff_69
  recurrence4B2_coeff_70
  recurrence4B2_coeff_71
  recurrence4B2_coeff_72
  recurrence4B2_coeff_73
  recurrence4B2_coeff_74
  recurrence4B2_coeff_75
  recurrence4B2_coeff_76
  recurrence4B2_coeff_77
  recurrence4B2_coeff_78
  recurrence4B2_coeff_79
  recurrence4B2_coeff_80
  recurrence4B2_coeff_81
  recurrence4B2_coeff_82
  recurrence4B2_coeff_83
  recurrence4B2_coeff_84
  recurrence4B2_coeff_85
  recurrence4B2_coeff_86
  recurrence4B2_coeff_87
  recurrence4B2_coeff_88
  recurrence4B2_coeff_89
  recurrence4B2_coeff_90
  recurrence4B2_coeff_91
  recurrence4B2_coeff_92
  recurrence4B2_coeff_93

attribute [local simp]
  recurrence4B2_coeff_94
  recurrence4B2_coeff_95
  recurrence4B2_coeff_96
  recurrence4B2_coeff_97
  recurrence4B2_coeff_98
  recurrence4B2_coeff_99

private theorem recurrence4B2A4_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (277 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 109,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (277 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_277 :
    recurrence4B2A4.coeff 277 =
      (((17895263502851563503590368469691 * 10 ^ 70 +
        4107236141892483684634950739574094755187449619081849020195242166816233) * 10 ^ 70 +
        7080786296059333347496988999770307022996396922201786824327262515269645) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 278,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (277 - x)) = _
  rw [show 278 = 99 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 6 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_277_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (278 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 110,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (278 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_278 :
    recurrence4B2A4.coeff 278 =
      -(((6119163007893538555947812174575 * 10 ^ 70 +
        6620307414408691161024575253402574982230146629192735590526650040654982) * 10 ^ 70 +
        7686427043987843255027039347731910094566386705846184216555435271015727) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 279,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (278 - x)) = _
  rw [show 279 = 100 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 5 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_278_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (279 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 111,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (279 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_279 :
    recurrence4B2A4.coeff 279 =
      (((1977819197030521113939928910923 * 10 ^ 70 +
        6180488525223890270049624099456813632110815090416572748230859117385100) * 10 ^ 70 +
        2266413003429704977959586767081063418067319584804412335207833624199227) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 280,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (279 - x)) = _
  rw [show 280 = 101 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 4 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_279_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (280 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 112,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (280 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_280 :
    recurrence4B2A4.coeff 280 =
      -(((597710087861672253939152566001 * 10 ^ 70 +
        2197122061063567169393380762255555991524126897561501784186620427794597) * 10 ^ 70 +
        7388882536720210024252847061045017699507859699861109940071608136900462) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 281,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (280 - x)) = _
  rw [show 281 = 102 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 3 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_280_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (281 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 113,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (281 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_281 :
    recurrence4B2A4.coeff 281 =
      (((166001841842094956996534480613 * 10 ^ 70 +
        2274474153146152486712595199327278568338878371796678246616709571802825) * 10 ^ 70 +
        7318873289334185706435222299174580516936668295888385042830656552494488) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 282,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (281 - x)) = _
  rw [show 282 = 103 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 2 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_281_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (282 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 114,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (282 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_282 :
    recurrence4B2A4.coeff 282 =
      -(((41069538245658022709410643154 * 10 ^ 70 +
        0850673477731790083080659625585991494456278464015077727166130714450594) * 10 ^ 70 +
        1619181049473708710425391754789575413319316511632814450494092999359151) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 283,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (282 - x)) = _
  rw [show 283 = 104 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 1 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_282_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (283 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 115,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (283 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_283 :
    recurrence4B2A4.coeff 283 =
      (((8432613365932767513106312800 * 10 ^ 70 +
        1994697612452804045380129709063298165350921845589238440111525559986453) * 10 ^ 70 +
        2221136471184089074081141327561604821141857246826649298888377596136346) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 284,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (283 - x)) = _
  rw [show 284 = 105 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_283_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (284 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 116,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (284 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_284 :
    recurrence4B2A4.coeff 284 =
      -(((1111660795608050353613930905 * 10 ^ 70 +
        1652658570591181184369357911743065196465053188745181603801429214732521) * 10 ^ 70 +
        0225027593871477604359591760654856755431989711599025057416479510430947) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 285,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (284 - x)) = _
  rw [show 285 = 106 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 31 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_284_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (285 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 117,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (285 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_285 :
    recurrence4B2A4.coeff 285 =
      -(((109535104403255444193538560 * 10 ^ 70 +
        3066418591635153592237989900705121525065531896936780112196666042573668) * 10 ^ 70 +
        9625830102648819289777793526636479303907987376192520840945931290564356) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 286,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (285 - x)) = _
  rw [show 286 = 107 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 30 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_285_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (286 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 118,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (286 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_286 :
    recurrence4B2A4.coeff 286 =
      (((151727232633205517020836761 * 10 ^ 70 +
        1778613894082890417857312488627972309657167201835576322183873725423243) * 10 ^ 70 +
        5012458822367279463251046422994328701571374216992268240460088275178428) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 287,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (286 - x)) = _
  rw [show 287 = 108 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 29 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_286_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (287 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 119,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (287 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_287 :
    recurrence4B2A4.coeff 287 =
      -(((72001580661553729723264021 * 10 ^ 70 +
        6046437145264973829584507755345327574375604937275535583102552622979915) * 10 ^ 70 +
        2495683532124488515275750444816070185500417193361718148082447536811815) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 288,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (287 - x)) = _
  rw [show 288 = 109 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 28 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_287_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 110,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (288 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 120,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (288 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_288 :
    recurrence4B2A4.coeff 288 =
      (((25916966337025013303459252 * 10 ^ 70 +
        5134644533164500716674599340782072128812017905516054869394700642629532) * 10 ^ 70 +
        7233563117596361227968538927767232639982698630674349439583890733957501) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 289,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (288 - x)) = _
  rw [show 289 = 110 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 27 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_288_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 111,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (289 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 121,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (289 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_289 :
    recurrence4B2A4.coeff 289 =
      -(((7955689825198669725878092 * 10 ^ 70 +
        7269871759943304643246355806809217100028759376786430878903249707698819) * 10 ^ 70 +
        4456812668708928194283869792860459539250556042714694657376736256930070) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 290,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (289 - x)) = _
  rw [show 290 = 111 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 26 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_289_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (290 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 122,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (290 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_290 :
    recurrence4B2A4.coeff 290 =
      (((2164267495353398145022534 * 10 ^ 70 +
        9465932894208392475684608464100868894727941525786500480179406775422454) * 10 ^ 70 +
        9544534689231847126822311774374235699433244015897842015753037655388850) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 291,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (290 - x)) = _
  rw [show 291 = 112 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 25 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_290_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (291 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 123,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (291 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_291 :
    recurrence4B2A4.coeff 291 =
      -(((529469390948379761734777 * 10 ^ 70 +
        9537655464016269778501691867948052711075521474066922466075475379331677) * 10 ^ 70 +
        4155974215357293687394696671667440514632665257811412074344611303484932) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 292,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (291 - x)) = _
  rw [show 292 = 113 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 24 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_291_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (292 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 124,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (292 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_292 :
    recurrence4B2A4.coeff 292 =
      (((116900770439539526389351 * 10 ^ 70 +
        7122897551348849473254573741384129384444968357559809345472193200341596) * 10 ^ 70 +
        3396286374561535237045813113704300237305130483266665969992243665125095) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 293,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (292 - x)) = _
  rw [show 293 = 114 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 23 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_292_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (293 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 125,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (293 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_293 :
    recurrence4B2A4.coeff 293 =
      -(((23194210933135697163529 * 10 ^ 70 +
        2655341763068558022071703453438005412753589993614605377359309374082509) * 10 ^ 70 +
        7654999801745979943319782633065868933003230036747973578440664256194536) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 294,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (293 - x)) = _
  rw [show 294 = 115 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 22 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_293_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (294 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 126,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (294 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_294 :
    recurrence4B2A4.coeff 294 =
      (((4081058085983550965374 * 10 ^ 70 +
        4723361565200098674581433896051191147527991081807166457987146612680066) * 10 ^ 70 +
        6622293800964453278148097862192073979559418334406823800702209898785797) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 295,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (294 - x)) = _
  rw [show 295 = 116 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 21 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_294_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (295 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 127,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (295 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_295 :
    recurrence4B2A4.coeff 295 =
      -(((618537153695629182024 * 10 ^ 70 +
        7697823931425654802995336133984763432460133847064770322902620044885898) * 10 ^ 70 +
        6503874228054358046607396853387572419141115443696113676800067864534713) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 296,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (295 - x)) = _
  rw [show 296 = 117 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 20 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_295_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (296 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 128,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (296 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_296 :
    recurrence4B2A4.coeff 296 =
      (((75273038020124357691 * 10 ^ 70 +
        9739129796234781985882682553007662504178467405215395901283186317281732) * 10 ^ 70 +
        4746104581082236390313069337907143327116898787914725559162127650071971) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 297,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (296 - x)) = _
  rw [show 297 = 118 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 19 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_296_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (297 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 129,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (297 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_297 :
    recurrence4B2A4.coeff 297 =
      -(((5695300635668121693 * 10 ^ 70 +
        2164437430996808958979075318043214175905865377030944173850282160331442) * 10 ^ 70 +
        7091476843598818538515596470966008100613091466814792659075074950681361) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 298,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (297 - x)) = _
  rw [show 298 = 119 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 18 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_297_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (298 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 130,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (298 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_298 :
    recurrence4B2A4.coeff 298 =
      -(((297763483305709540 * 10 ^ 70 +
        8218646234961931531120640341910757240651110650826371901378612880036055) * 10 ^ 70 +
        6213601133011903180866509188207256999996741503476152063368557726040607) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 299,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (298 - x)) = _
  rw [show 299 = 120 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 17 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_298_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (299 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 131,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (299 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_299 :
    recurrence4B2A4.coeff 299 =
      (((220338644437793786 * 10 ^ 70 +
        0234810854319186366291866155050595307764458244259547774997550577789505) * 10 ^ 70 +
        2294953256170715347431820952359353951226160264048864293391539462408611) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 300,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (299 - x)) = _
  rw [show 300 = 121 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 16 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_299_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (300 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 132,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (300 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_300 :
    recurrence4B2A4.coeff 300 =
      -(((51650307588158803 * 10 ^ 70 +
        3918663274460913693104150357967389767550027087859575284078450382635346) * 10 ^ 70 +
        7490481737847919306221874337373185644304494313510952702425411965216692) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 301,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (300 - x)) = _
  rw [show 301 = 122 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 15 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_300_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (301 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 133,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (301 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_301 :
    recurrence4B2A4.coeff 301 =
      (((8438674339922750 * 10 ^ 70 +
        2630290364904141406247901376920491968191700264131280996851107726709873) * 10 ^ 70 +
        2008688527093027595535438592065510400203119055334784292705883911976857) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 302,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (301 - x)) = _
  rw [show 302 = 123 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 14 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_301_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (302 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 134,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (302 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_302 :
    recurrence4B2A4.coeff 302 =
      -(((1030619730505232 * 10 ^ 70 +
        4510757442809382763041549264570377932847411509755392982254167269824403) * 10 ^ 70 +
        1159414227965208878944948314437588959073379938364852235277466054003487) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 303,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (302 - x)) = _
  rw [show 303 = 124 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 13 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_302_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (303 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 135,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (303 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_303 :
    recurrence4B2A4.coeff 303 =
      (((85293026545254 * 10 ^ 70 +
        9154241651685360534725110954919943219928944191914063700508102039215047) * 10 ^ 70 +
        6030162249600181681180170030255399168581890523177014747018164544501421) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 304,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (303 - x)) = _
  rw [show 304 = 125 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 12 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_303_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (304 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 136,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (304 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_304 :
    recurrence4B2A4.coeff 304 =
      -(((1677164784925 * 10 ^ 70 +
        5673385474657361967506116175893985231289327103368584933510183847424147) * 10 ^ 70 +
        0854009648691998418146252842145118905251937973052132399528418779452018) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 305,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (304 - x)) = _
  rw [show 305 = 126 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 11 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_304_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (305 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 137,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (305 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_305 :
    recurrence4B2A4.coeff 305 =
      -(((921683278699 * 10 ^ 70 +
        0627717878797486511412995425768277885170698726154758447054452406059263) * 10 ^ 70 +
        3700621659779002340418457917783089368318585833281203534523836055013100) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 306,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (305 - x)) = _
  rw [show 306 = 127 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 10 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_305_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (306 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 138,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (306 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_306 :
    recurrence4B2A4.coeff 306 =
      (((200259054003 * 10 ^ 70 +
        5728549342702557780116451776566463570891940108140522935124125861395652) * 10 ^ 70 +
        8532097847364135726018637697700337697299687246148850632748879495407986) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 307,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (306 - x)) = _
  rw [show 307 = 128 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 9 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_306_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (307 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 139,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (307 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_307 :
    recurrence4B2A4.coeff 307 =
      -(((25184851815 * 10 ^ 70 +
        2131314677188985064630284568334177328375882026443802895239214342895555) * 10 ^ 70 +
        5335832297050207791934706209633174971622683556324339261172390645407802) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 308,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (307 - x)) = _
  rw [show 308 = 129 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 8 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_307_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (308 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 140,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (308 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_308 :
    recurrence4B2A4.coeff 308 =
      (((2127241998 * 10 ^ 70 +
        8344873470183831537927098341333092399297667481784624307640334907319761) * 10 ^ 70 +
        6639274826067595139250143026751811312692733633205013832876143160596256) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 309,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (308 - x)) = _
  rw [show 309 = 130 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 7 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_308_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4B2A4_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4_coeff_high (309 - x) (by
    omega)]
  norm_num

private theorem recurrence4B2A4_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 141,
      remainder5Coefficient2.coeff (169 + x) *
        remainder4Coefficient4.coeff (309 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B2_coeff_high (169 + x) (by
    omega)]
  norm_num

theorem recurrence4B2A4_coeff_309 :
    recurrence4B2A4.coeff 309 =
      -(((99870731 * 10 ^ 70 +
        6065541556276123292453106569354673157287751487559167142677980084908823) * 10 ^ 70 +
        6238311253747384022434219359674578635380273703781364746475393004125374) : ℚ) := by
  unfold recurrence4B2A4
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 310,
    remainder5Coefficient2.coeff x * remainder4Coefficient4.coeff (309 - x)) = _
  rw [show 310 = 131 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 6 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence4B2A4_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4B2A4_coeff_309_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

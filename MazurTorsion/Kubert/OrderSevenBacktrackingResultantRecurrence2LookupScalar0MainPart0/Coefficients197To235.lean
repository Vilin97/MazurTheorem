/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar0MainPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar0Main coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2B0_coeff_0
  recurrence2B0_coeff_1
  recurrence2B0_coeff_2
  recurrence2B0_coeff_3
  recurrence2B0_coeff_4
  recurrence2B0_coeff_5
  recurrence2B0_coeff_6
  recurrence2B0_coeff_7
  recurrence2B0_coeff_8
  recurrence2B0_coeff_9
  recurrence2B0_coeff_10
  recurrence2B0_coeff_11
  recurrence2B0_coeff_12
  recurrence2B0_coeff_13
  recurrence2B0_coeff_14
  recurrence2B0_coeff_15
  recurrence2B0_coeff_16
  recurrence2B0_coeff_17
  recurrence2B0_coeff_18
  recurrence2B0_coeff_19
  recurrence2B0_coeff_20
  recurrence2B0_coeff_21
  recurrence2B0_coeff_22
  recurrence2B0_coeff_23
  recurrence2B0_coeff_24
  recurrence2B0_coeff_25
  recurrence2B0_coeff_26
  recurrence2B0_coeff_27
  recurrence2B0_coeff_28
  recurrence2B0_coeff_29
  recurrence2B0_coeff_30
  recurrence2B0_coeff_31
  recurrence2B0_coeff_32
  recurrence2B0_coeff_33
  recurrence2B0_coeff_34
  recurrence2B0_coeff_35
  recurrence2B0_coeff_36
  recurrence2B0_coeff_37
  recurrence2B0_coeff_38
  recurrence2B0_coeff_39
  recurrence2B0_coeff_40
  recurrence2B0_coeff_41
  recurrence2B0_coeff_42
  recurrence2B0_coeff_43
  recurrence2B0_coeff_44
  recurrence2B0_coeff_45
  recurrence2B0_coeff_46
  recurrence2B0_coeff_47
  recurrence2B0_coeff_48
  recurrence2B0_coeff_49
  recurrence2B0_coeff_50
  recurrence2B0_coeff_51
  recurrence2B0_coeff_52
  recurrence2B0_coeff_53
  recurrence2B0_coeff_54
  recurrence2B0_coeff_55
  recurrence2B0_coeff_56
  recurrence2B0_coeff_57
  recurrence2B0_coeff_58
  recurrence2B0_coeff_59
  recurrence2B0_coeff_60
  recurrence2B0_coeff_61
  recurrence2B0_coeff_62
  recurrence2B0_coeff_63
  recurrence2B0_coeff_64
  recurrence2B0_coeff_65
  recurrence2B0_coeff_66
  recurrence2B0_coeff_67
  recurrence2B0_coeff_68
  recurrence2B0_coeff_69
  recurrence2B0_coeff_70
  recurrence2B0_coeff_71
  recurrence2B0_coeff_72
  recurrence2B0_coeff_73
  recurrence2B0_coeff_74
  recurrence2B0_coeff_75
  recurrence2B0_coeff_76
  recurrence2B0_coeff_77
  recurrence2B0_coeff_78
  recurrence2B0_coeff_79
  recurrence2B0_coeff_80
  recurrence2B0_coeff_81
  recurrence2B0_coeff_82
  recurrence2B0_coeff_83
  recurrence2B0_coeff_84
  recurrence2B0_coeff_85
  recurrence2B0_coeff_86
  recurrence2B0_coeff_87
  recurrence2B0_coeff_88
  recurrence2B0_coeff_89
  recurrence2B0_coeff_90
  recurrence2B0_coeff_91
  recurrence2B0_coeff_92
  recurrence2B0_coeff_93
  recurrence2B0_coeff_94
  recurrence2B0_coeff_95
  recurrence2B0_coeff_96
  recurrence2B0_coeff_97
  recurrence2B0_coeff_98
  recurrence2B0_coeff_99
  recurrence2B0_coeff_100
  recurrence2B0_coeff_101
  recurrence2B0_coeff_102
  recurrence2B0_coeff_103
  recurrence2B0_coeff_104
  recurrence2B0_coeff_105
  recurrence2B0_coeff_106
  recurrence2B0_coeff_107
  recurrence2B0_coeff_108
  recurrence2B0_coeff_109
  recurrence2B0_coeff_110
  recurrence2B0_coeff_111
  recurrence2B0_coeff_112
  recurrence2B0_coeff_113
  recurrence2B0_coeff_114
  recurrence2B0_coeff_115
  recurrence2B0_coeff_116
  recurrence2B0_coeff_117
  recurrence2B0_coeff_118
  recurrence2B0_coeff_119
  recurrence2B0_coeff_120
  recurrence2B0_coeff_121
  recurrence2B0_coeff_122
  recurrence2B0_coeff_123
  recurrence2B0_coeff_124
  recurrence2B0_coeff_125
  recurrence2B0_coeff_126
  recurrence2B0_coeff_127
  recurrence2B0_coeff_128
  recurrence2B0_coeff_129
  recurrence2B0_coeff_130
  recurrence2B0_coeff_131
  recurrence2B0_coeff_132
  recurrence2B0_coeff_133
  recurrence2B0_coeff_134
  recurrence2B0_coeff_135
  recurrence2B0_coeff_136
  recurrence2B0_coeff_137
  recurrence2B0_coeff_138
  recurrence2B0_coeff_139
  recurrence2B0_coeff_140
  recurrence2B0_coeff_141
  recurrence2B0_coeff_142
  recurrence2B0_coeff_143
  recurrence2B0_coeff_144
  recurrence2B0_coeff_145
  recurrence2B0_coeff_146
  recurrence2B0_coeff_147
  recurrence2B0_coeff_148
  recurrence2B0_coeff_149
  recurrence2B0_coeff_150
  recurrence2B0_coeff_151
  recurrence2B0_coeff_152
  recurrence2B0_coeff_153
  recurrence2B0_coeff_154
  recurrence2QuotientConstant_coeff_0
  recurrence2QuotientConstant_coeff_1
  recurrence2QuotientConstant_coeff_2
  recurrence2QuotientConstant_coeff_3
  recurrence2QuotientConstant_coeff_4
  recurrence2QuotientConstant_coeff_5
  recurrence2QuotientConstant_coeff_6
  recurrence2QuotientConstant_coeff_7
  recurrence2QuotientConstant_coeff_8
  recurrence2QuotientConstant_coeff_9
  recurrence2QuotientConstant_coeff_10
  recurrence2QuotientConstant_coeff_11
  recurrence2QuotientConstant_coeff_12
  recurrence2QuotientConstant_coeff_13
  recurrence2QuotientConstant_coeff_14
  recurrence2QuotientConstant_coeff_15
  recurrence2QuotientConstant_coeff_16
  recurrence2QuotientConstant_coeff_17
  recurrence2QuotientConstant_coeff_18
  recurrence2QuotientConstant_coeff_19
  recurrence2QuotientConstant_coeff_20
  recurrence2QuotientConstant_coeff_21
  recurrence2QuotientConstant_coeff_22
  recurrence2QuotientConstant_coeff_23
  recurrence2QuotientConstant_coeff_24
  recurrence2QuotientConstant_coeff_25
  recurrence2QuotientConstant_coeff_26
  recurrence2QuotientConstant_coeff_27
  recurrence2QuotientConstant_coeff_28
  recurrence2QuotientConstant_coeff_29
  recurrence2QuotientConstant_coeff_30
  recurrence2QuotientConstant_coeff_31
  recurrence2QuotientConstant_coeff_32
  recurrence2QuotientConstant_coeff_33
  recurrence2QuotientConstant_coeff_34
  recurrence2QuotientConstant_coeff_35
  recurrence2QuotientConstant_coeff_36
  recurrence2QuotientConstant_coeff_37
  recurrence2QuotientConstant_coeff_38
  recurrence2QuotientConstant_coeff_39
  recurrence2QuotientConstant_coeff_40
  recurrence2QuotientConstant_coeff_41
  recurrence2QuotientConstant_coeff_42
  recurrence2QuotientConstant_coeff_43
  recurrence2QuotientConstant_coeff_44
  recurrence2QuotientConstant_coeff_45
  recurrence2QuotientConstant_coeff_46
  recurrence2QuotientConstant_coeff_47
  recurrence2QuotientConstant_coeff_48
  recurrence2QuotientConstant_coeff_49
  recurrence2QuotientConstant_coeff_50
  recurrence2QuotientConstant_coeff_51
  recurrence2QuotientConstant_coeff_52
  recurrence2QuotientConstant_coeff_53
  recurrence2QuotientConstant_coeff_54
  recurrence2QuotientConstant_coeff_55
  recurrence2QuotientConstant_coeff_56
  recurrence2QuotientConstant_coeff_57
  recurrence2QuotientConstant_coeff_58
  recurrence2QuotientConstant_coeff_59
  recurrence2QuotientConstant_coeff_60
  recurrence2QuotientConstant_coeff_61
  recurrence2QuotientConstant_coeff_62
  recurrence2QuotientConstant_coeff_63
  recurrence2QuotientConstant_coeff_64
  recurrence2QuotientConstant_coeff_65
  recurrence2QuotientConstant_coeff_66
  recurrence2QuotientConstant_coeff_67
  recurrence2QuotientConstant_coeff_68
  recurrence2QuotientConstant_coeff_69
  recurrence2QuotientConstant_coeff_70
  recurrence2QuotientConstant_coeff_71
  recurrence2QuotientConstant_coeff_72
  recurrence2QuotientConstant_coeff_73
  recurrence2QuotientConstant_coeff_74
  recurrence2QuotientConstant_coeff_75
  recurrence2QuotientConstant_coeff_76
  recurrence2QuotientConstant_coeff_77
  recurrence2QuotientConstant_coeff_78
  recurrence2QuotientConstant_coeff_79
  recurrence2QuotientConstant_coeff_80
  recurrence2QuotientConstant_coeff_81
  recurrence2QuotientConstant_coeff_82
  recurrence2QuotientConstant_coeff_83
  recurrence2QuotientConstant_coeff_84
  recurrence2QuotientConstant_coeff_85
  recurrence2QuotientConstant_coeff_86
  recurrence2QuotientConstant_coeff_87
  recurrence2QuotientConstant_coeff_88
  recurrence2QuotientConstant_coeff_89
  recurrence2QuotientConstant_coeff_90
  recurrence2QuotientConstant_coeff_91
  recurrence2QuotientConstant_coeff_92
  recurrence2QuotientConstant_coeff_93
  recurrence2QuotientConstant_coeff_94
  recurrence2QuotientConstant_coeff_95
  recurrence2QuotientConstant_coeff_96
  recurrence2QuotientConstant_coeff_97
  recurrence2QuotientConstant_coeff_98
  recurrence2QuotientConstant_coeff_99
  recurrence2QuotientConstant_coeff_100
  recurrence2QuotientConstant_coeff_101
  recurrence2QuotientConstant_coeff_102
  recurrence2QuotientConstant_coeff_103
  recurrence2QuotientConstant_coeff_104
  recurrence2QuotientConstant_coeff_105
  recurrence2QuotientConstant_coeff_106
  recurrence2QuotientConstant_coeff_107
  recurrence2QuotientConstant_coeff_108
  recurrence2QuotientConstant_coeff_109
  recurrence2QuotientConstant_coeff_110
  recurrence2QuotientConstant_coeff_111
  recurrence2QuotientConstant_coeff_112
  recurrence2QuotientConstant_coeff_113
  recurrence2QuotientConstant_coeff_114
  recurrence2QuotientConstant_coeff_115
  recurrence2QuotientConstant_coeff_116
  recurrence2QuotientConstant_coeff_117
  recurrence2QuotientConstant_coeff_118
  recurrence2QuotientConstant_coeff_119
  recurrence2QuotientConstant_coeff_120
  recurrence2QuotientConstant_coeff_121
  recurrence2QuotientConstant_coeff_122
  recurrence2QuotientConstant_coeff_123
  recurrence2QuotientConstant_coeff_124
  recurrence2QuotientConstant_coeff_125
  recurrence2QuotientConstant_coeff_126
  recurrence2QuotientConstant_coeff_127
  recurrence2QuotientConstant_coeff_128
  recurrence2QuotientConstant_coeff_129
  recurrence2QuotientConstant_coeff_130
  recurrence2QuotientConstant_coeff_131
  recurrence2QuotientConstant_coeff_132
  recurrence2QuotientConstant_coeff_133
  recurrence2QuotientConstant_coeff_134
  recurrence2QuotientConstant_coeff_135
  recurrence2QuotientConstant_coeff_136
  recurrence2QuotientConstant_coeff_137
  recurrence2QuotientConstant_coeff_138
  recurrence2QuotientConstant_coeff_139
  recurrence2QuotientConstant_coeff_140
  recurrence2QuotientConstant_coeff_141
  recurrence2QuotientConstant_coeff_142
  recurrence2QuotientConstant_coeff_143
  recurrence2QuotientConstant_coeff_144
  recurrence2QuotientConstant_coeff_145
  recurrence2QuotientConstant_coeff_146
  recurrence2QuotientConstant_coeff_147
  recurrence2QuotientConstant_coeff_148
  recurrence2QuotientConstant_coeff_149
  recurrence2QuotientConstant_coeff_150
  recurrence2QuotientConstant_coeff_151
  recurrence2QuotientConstant_coeff_152
  recurrence2QuotientConstant_coeff_153
  recurrence2QuotientConstant_coeff_154
  recurrence2QuotientConstant_coeff_155
  recurrence2QuotientConstant_coeff_156
  recurrence2QuotientConstant_coeff_157
  recurrence2QuotientConstant_coeff_158
  recurrence2QuotientConstant_coeff_159
  recurrence2QuotientConstant_coeff_160
  recurrence2QuotientConstant_coeff_161
  recurrence2QuotientConstant_coeff_162
  recurrence2QuotientConstant_coeff_163
  recurrence2QuotientConstant_coeff_164
  recurrence2QuotientConstant_coeff_165
  recurrence2QuotientConstant_coeff_166
  recurrence2QuotientConstant_coeff_167
  recurrence2QuotientConstant_coeff_168
  recurrence2QuotientConstant_coeff_169
  recurrence2QuotientConstant_coeff_170
  recurrence2QuotientConstant_coeff_171
  recurrence2QuotientConstant_coeff_172
  recurrence2QuotientConstant_coeff_173
  recurrence2QuotientConstant_coeff_174
  recurrence2QuotientConstant_coeff_175
  recurrence2QuotientConstant_coeff_176
  recurrence2QuotientConstant_coeff_177
  recurrence2QuotientConstant_coeff_178
  recurrence2QuotientConstant_coeff_179
  recurrence2QuotientConstant_coeff_180
  recurrence2QuotientConstant_coeff_181
  recurrence2QuotientConstant_coeff_182
  recurrence2QuotientConstant_coeff_183
  recurrence2QuotientConstant_coeff_184
  recurrence2QuotientConstant_coeff_185
  recurrence2QuotientConstant_coeff_186
  recurrence2QuotientConstant_coeff_187
  recurrence2QuotientConstant_coeff_188
  recurrence2QuotientConstant_coeff_189
  recurrence2QuotientConstant_coeff_190
  recurrence2QuotientConstant_coeff_191
  recurrence2QuotientConstant_coeff_192
  recurrence2QuotientConstant_coeff_193
  recurrence2QuotientConstant_coeff_194
  recurrence2QuotientConstant_coeff_195
  recurrence2QuotientConstant_coeff_196
  recurrence2QuotientConstant_coeff_197
  recurrence2QuotientConstant_coeff_198
  recurrence2QuotientConstant_coeff_199
  recurrence2QuotientConstant_coeff_200
  recurrence2QuotientConstant_coeff_201
  recurrence2QuotientConstant_coeff_202
  recurrence2QuotientConstant_coeff_203
  recurrence2QuotientConstant_coeff_204
  recurrence2QuotientConstant_coeff_205
  recurrence2QuotientConstant_coeff_206
  recurrence2QuotientConstant_coeff_207
  recurrence2QuotientConstant_coeff_208
  recurrence2QuotientConstant_coeff_209
  recurrence2QuotientConstant_coeff_210
  recurrence2QuotientConstant_coeff_211
  recurrence2QuotientConstant_coeff_212
  recurrence2QuotientConstant_coeff_213
  recurrence2QuotientConstant_coeff_214
  recurrence2QuotientConstant_coeff_215
  recurrence2QuotientConstant_coeff_216
  recurrence2QuotientConstant_coeff_217
  recurrence2QuotientConstant_coeff_218
  recurrence2QuotientConstant_coeff_219
  recurrence2QuotientConstant_coeff_220
  recurrence2QuotientConstant_coeff_221
  recurrence2QuotientConstant_coeff_222
  recurrence2QuotientConstant_coeff_223
  recurrence2QuotientConstant_coeff_224
  recurrence2QuotientConstant_coeff_225
  recurrence2QuotientConstant_coeff_226
  recurrence2QuotientConstant_coeff_227
  recurrence2QuotientConstant_coeff_228
  recurrence2QuotientConstant_coeff_229
  recurrence2QuotientConstant_coeff_230
  recurrence2QuotientConstant_coeff_231
  recurrence2QuotientConstant_coeff_232
  recurrence2QuotientConstant_coeff_233

private theorem recurrence2Scalar0Main_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (197 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_197 :
    recurrence2Scalar0Main.coeff 197 =
      (((512543809503711841059539719243599893553308504354712687203379143 * 10 ^ 70 +
        1790082514576770805393640092359503711341353412346217001852999469286684) * 10 ^ 70 +
        3308704942805971465723623076506669453611878610444512571483566225477886) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 198 = 0 +
    198 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
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
    rw [show 70 = 27 +
      43 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_197_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (198 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_198 :
    recurrence2Scalar0Main.coeff 198 =
      (((1619447353792636702998926731538572792488540138925222772371547266 * 10 ^ 70 +
        3212160027254596726962134141423074256956448020497882790705894846282829) * 10 ^ 70 +
        9221972002505453659101992048149600978772496315449316989225991101211217) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 199 = 0 +
    199 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 199 = 32 +
      167 by norm_num, Finset.sum_range_add]
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
    rw [show 71 = 27 +
      44 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_198_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (199 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_199 :
    recurrence2Scalar0Main.coeff 199 =
      -(((9502803458120758331571304939676827310213680939678240457611524453 * 10 ^ 70 +
        5115753418352870130547398265621104623861870771294053254954303907729057) * 10 ^ 70 +
        6101248561811073050500385538752745398047792798931969251265154439118023) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 200 = 0 +
    200 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 200 = 32 +
      168 by norm_num, Finset.sum_range_add]
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
    rw [show 72 = 27 +
      45 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_199_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (200 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_200 :
    recurrence2Scalar0Main.coeff 200 =
      (((27138426003291213106867284727220966873626730229651138311721822755 * 10 ^ 70 +
        9438705111871720824306244666160196308039459775079310275496277598264695) * 10 ^ 70 +
        2139878955924993213353816502413363649833637697107825433550632609286400) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 201 = 0 +
    201 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 201 = 32 +
      169 by norm_num, Finset.sum_range_add]
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
    rw [show 73 = 27 +
      46 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_200_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (201 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_201 :
    recurrence2Scalar0Main.coeff 201 =
      -(((48763698208382335263726808135302600849063752874068423737250989081 * 10 ^ 70 +
        8277825315305486214415422178205005380985636591133981519834187477850277) * 10 ^ 70 +
        0719975022079909990063826708564977441410263259039788563051165161420693) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 202 = 0 +
    202 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
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
    rw [show 74 = 27 +
      47 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_201_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (202 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_202 :
    recurrence2Scalar0Main.coeff 202 =
      (((30314950455465665832091264378984030424552642151107226292122861560 * 10 ^ 70 +
        4575011288946916923801265952030142826003943679013974376058395491149772) * 10 ^ 70 +
        0664407342166385036816282693864888376433450248122124738785513923686850) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 203 = 0 +
    203 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 203 = 32 +
      171 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 171 = 32 +
      139 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 139 = 32 +
      107 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 27 +
      48 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_202_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (203 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_203 :
    recurrence2Scalar0Main.coeff 203 =
      (((163250864039074833868464283153990068148764346978848591960909451825 * 10 ^ 70 +
        4819316822714699230560681188899814953176463557588240264235392305109466) * 10 ^ 70 +
        3363336221692738056908677177808155154852008889667221660194688264074362) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 204 = 0 +
    204 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 204 = 32 +
      172 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 172 = 32 +
      140 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 140 = 32 +
      108 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 108 = 32 +
      76 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 76 = 27 +
      49 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_203_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (204 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_204 :
    recurrence2Scalar0Main.coeff 204 =
      -(((806544082957949124219042041917766128151394845559920579733340316855 * 10 ^ 70 +
        8108836133443980462058071232424760817618645787161342065476609527143922) * 10 ^ 70 +
        0489720745964022892300851121487424376278833463690434541754456405711662) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 205 = 0 +
    205 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 205 = 32 +
      173 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 27 +
      50 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_204_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (205 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_205 :
    recurrence2Scalar0Main.coeff 205 =
      (((2230494282487526142703925274781293701203421199729424709712984317796 * 10 ^ 70 +
        8909182036390470711247434943562605887742458747624507046363932071768786) * 10 ^ 70 +
        4700126460679039476662599812081005211005512811540179396405711124492942) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 206 = 0 +
    206 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 206 = 32 +
      174 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 174 = 32 +
      142 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 142 = 32 +
      110 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 110 = 32 +
      78 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 78 = 27 +
      51 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_205_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (206 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_206 :
    recurrence2Scalar0Main.coeff 206 =
      -(((4282590052405085668240657082446982244942539025528054776537071598376 * 10 ^ 70 +
        7453605234242746284640913057339399968671856384720620944733249895344187) * 10 ^ 70 +
        3517104756551522023315025315658286872573237104364584616135789958531283) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 207 = 0 +
    207 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 207 = 32 +
      175 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 175 = 32 +
      143 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 143 = 32 +
      111 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 27 +
      52 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_206_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (207 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_207 :
    recurrence2Scalar0Main.coeff 207 =
      (((4750593637605217934411486677396311239170982210461508917960720287008 * 10 ^ 70 +
        0920875569099924873119311502350286741691762968247211728394282281735112) * 10 ^ 70 +
        8043145955023500116526487246211241756887177227118776823349416546365547) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 208 = 0 +
    208 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 208 = 32 +
      176 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 176 = 32 +
      144 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 144 = 32 +
      112 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 112 = 32 +
      80 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 80 = 27 +
      53 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_207_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (208 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_208 :
    recurrence2Scalar0Main.coeff 208 =
      (((3891440956485842246256885780864644536116918674753338618093911103376 * 10 ^ 70 +
        9963346093014245595705825072573063394146189976281065764236858187781085) * 10 ^ 70 +
        5502030608161634655885828078254100967130683140699734664221732857174285) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 209 = 0 +
    209 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 209 = 32 +
      177 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 27 +
      54 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_208_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (209 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_209 :
    recurrence2Scalar0Main.coeff 209 =
      -(((39242350204705210747298165352624941404762179039387598936473411975956 * 10 ^ 70 +
        3589887789799085335748701257109411966862883943829488518190542103857612) * 10 ^ 70 +
        4151639228609766352226309574530947991552029722752704293843952229047310) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 210 = 0 +
    210 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 210 = 32 +
      178 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 178 = 32 +
      146 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 27 +
      55 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_209_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (210 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_210 :
    recurrence2Scalar0Main.coeff 210 =
      (((132078702326884389572161696181358489019681411665019578986768625352702 * 10 ^ 70 +
        7759106918943047912654206813354368138552278617048169746717937693698938) * 10 ^ 70 +
        5201997904702091226548789156159273843536318331315614776453997475860658) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 211 = 0 +
    211 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 211 = 32 +
      179 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 27 +
      56 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_210_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (211 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_211 :
    recurrence2Scalar0Main.coeff 211 =
      -(((317657295732530095977004763914703172430214563849924064772425230961686 * 10 ^ 70 +
        1535778253431585095323004618440645760021771299291824648403704864788297) * 10 ^ 70 +
        2525931027258889892760047175471191297323135703162751063316404553670549) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 212 = 0 +
    212 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 212 = 32 +
      180 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 180 = 32 +
      148 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 148 = 32 +
      116 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 116 = 32 +
      84 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 84 = 27 +
      57 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_211_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (212 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_212 :
    recurrence2Scalar0Main.coeff 212 =
      (((592507382461223672898893151936669426821587802136287449300757929184144 * 10 ^ 70 +
        0799980127151673622814726367666979838187131364743663241164789965549170) * 10 ^ 70 +
        3642309178140446090458114859442998112560080362379769366663361082370987) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 213 = 0 +
    213 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 213 = 32 +
      181 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 181 = 32 +
      149 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 149 = 32 +
      117 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 117 = 32 +
      85 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 85 = 27 +
      58 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_212_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (213 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_213 :
    recurrence2Scalar0Main.coeff 213 =
      -(((796493968741677396506071901750975789410107568649343390605726255883350 * 10 ^ 70 +
        3272980246804241553281307921342720589100886691610170305721119907614265) * 10 ^ 70 +
        1936101958156895146533802262435622096584671660623207513409840115789808) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 214 = 0 +
    214 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 214 = 32 +
      182 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 182 = 32 +
      150 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 27 +
      59 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_213_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (214 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_214 :
    recurrence2Scalar0Main.coeff 214 =
      (((363455838429281447432520151926672528076015611149620836027991153929566 * 10 ^ 70 +
        0091141540218310626769339018013628104726114481167295634851178491514613) * 10 ^ 70 +
        2160137053375464841090319735951968186606132384216178086829340217445081) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 215 = 0 +
    215 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 215 = 32 +
      183 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 27 +
      60 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_214_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (215 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_215 :
    recurrence2Scalar0Main.coeff 215 =
      (((2116804250504527762223776718573470200309487281378073655523891614735427 * 10 ^ 70 +
        9815402572409903340936165108845388540995589357071502120406040121599813) * 10 ^ 70 +
        8748265183983318298862604064233897357259547176670654766155115427105448) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 216 = 0 +
    216 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 216 = 32 +
      184 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 184 = 32 +
      152 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 152 = 32 +
      120 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 120 = 32 +
      88 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 88 = 27 +
      61 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_215_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (216 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_216 :
    recurrence2Scalar0Main.coeff 216 =
      -(((9541451845983921418015633653398907090824329314366918286829591695420225 * 10 ^ 70 +
        0698006543281905809324064544291941702029269882267460934859639933912908) * 10 ^ 70 +
        1572734452531367168546425326888772394323152188925167440904311784933852) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 217 = 0 +
    217 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 217 = 32 +
      185 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 185 = 32 +
      153 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 153 = 32 +
      121 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 121 = 32 +
      89 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 89 = 27 +
      62 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_216_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (217 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_217 :
    recurrence2Scalar0Main.coeff 217 =
      ((((2 * 10 ^ 70 +
        7044135839114358993029359919257407773744732231460666962748967161692942) * 10 ^ 70 +
        4775579754645322130520624417277856803836007847436503686472226785573749) * 10 ^ 70 +
        6776247096903083035867329979853398579219813129759465328574882151194681) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 218 = 0 +
    218 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 32 +
      154 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 27 +
      63 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_217_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (218 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_218 :
    recurrence2Scalar0Main.coeff 218 =
      -((((6 * 10 ^ 70 +
        2538967047282081821004930822668329564178279709386288839318492995053703) * 10 ^ 70 +
        3612365289085911496526414956916778114309304338558181926390797750409800) * 10 ^ 70 +
        3544379016712539350866106379955802522149141420440091521976232549447807) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 219 = 0 +
    219 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 219 = 32 +
      187 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 27 +
      64 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_218_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (219 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_219 :
    recurrence2Scalar0Main.coeff 219 =
      ((((12 * 10 ^ 70 +
        6439066589252220239128087720391064117766986428728711619462746074248723) * 10 ^ 70 +
        1684254522463313285999884996816366794595754628787882372839767529901127) * 10 ^ 70 +
        6129066646801823096495781456302815636735894219580251900623037318553813) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 220 = 0 +
    220 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 220 = 32 +
      188 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 188 = 32 +
      156 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 156 = 32 +
      124 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 124 = 32 +
      92 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 92 = 27 +
      65 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_219_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (220 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_220 :
    recurrence2Scalar0Main.coeff 220 =
      -((((22 * 10 ^ 70 +
        9593397308996101828504449833599142402540079844017306385526294173139221) * 10 ^ 70 +
        2014905060329964058462530104408083490161648848595340788344450755161971) * 10 ^ 70 +
        2416139441024971620326033838648014087732165750260196507615683255044859) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 221 = 0 +
    221 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 221 = 32 +
      189 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 189 = 32 +
      157 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 157 = 32 +
      125 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 125 = 32 +
      93 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 93 = 27 +
      66 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_220_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (221 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_221 :
    recurrence2Scalar0Main.coeff 221 =
      ((((37 * 10 ^ 70 +
        8267552489233198117958156125016027818170873831241827737875792890059303) * 10 ^ 70 +
        5665685288512651629343720437410466754723436243053192379751484819455413) * 10 ^ 70 +
        6251588826920821035390245443466786793936003956943084979465411175354490) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 222 = 0 +
    222 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 222 = 32 +
      190 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 190 = 32 +
      158 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 158 = 32 +
      126 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 126 = 32 +
      94 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 94 = 27 +
      67 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_221_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (222 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_222 :
    recurrence2Scalar0Main.coeff 222 =
      -((((56 * 10 ^ 70 +
        5115522048409354569149498399435580344911516411547118135201408957438311) * 10 ^ 70 +
        1078921233041604114737325604666329744544164813362554891602835337926488) * 10 ^ 70 +
        5955832313154847234104024110785523093186601409747742247883851970639920) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 223 = 0 +
    223 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 223 = 32 +
      191 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 27 +
      68 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_222_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (223 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_223 :
    recurrence2Scalar0Main.coeff 223 =
      ((((75 * 10 ^ 70 +
        5788857859565195826551753360670762524504062217065205363657435637230656) * 10 ^ 70 +
        4940818025556161167993458344833649778662619790417827587208090577587802) * 10 ^ 70 +
        6745968556519435388020747046996093480649170452915055185491072357463871) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 224 = 0 +
    224 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 224 = 32 +
      192 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 192 = 32 +
      160 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 160 = 32 +
      128 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 128 = 32 +
      96 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 96 = 27 +
      69 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_223_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (224 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_224 :
    recurrence2Scalar0Main.coeff 224 =
      -((((87 * 10 ^ 70 +
        2252601188096239956345822950677259059215519921121583733475619994267507) * 10 ^ 70 +
        6661552127377246646430148391195555870384959033402913393661644364379595) * 10 ^ 70 +
        3074376134042007850141282420068400883331173183939127237592947046576190) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 225 = 0 +
    225 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 225 = 32 +
      193 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 193 = 32 +
      161 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 161 = 32 +
      129 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 129 = 32 +
      97 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 97 = 27 +
      70 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_224_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (225 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_225 :
    recurrence2Scalar0Main.coeff 225 =
      ((((77 * 10 ^ 70 +
        5933970461636268309473880911283474144993296272809546748981352231100969) * 10 ^ 70 +
        1935566419895195922550305557545089185444871211005115145734818348874789) * 10 ^ 70 +
        7766884754548167365894705279279490951538735439319628847900133991299469) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 226 = 0 +
    226 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 226 = 32 +
      194 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 194 = 32 +
      162 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 162 = 32 +
      130 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 130 = 32 +
      98 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 98 = 27 +
      71 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_225_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (226 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_226 :
    recurrence2Scalar0Main.coeff 226 =
      -((((25 * 10 ^ 70 +
        6078765673983019972693586676741668159288599131656452671979729806558153) * 10 ^ 70 +
        0428163219460405467096942511708506054868656488341879321148573109989109) * 10 ^ 70 +
        1577905614899222190024729196581539252157586114822909585366054031136298) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 227 = 0 +
    227 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 227 = 32 +
      195 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 27 +
      72 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_226_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (227 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_227 :
    recurrence2Scalar0Main.coeff 227 =
      -((((96 * 10 ^ 70 +
        9672335858234332120276697690791020921575890710730077923567836365593551) * 10 ^ 70 +
        4220998879772604200834349402429005631802727737737331698314434361030027) * 10 ^ 70 +
        1491576068254013301790920757117224829670723390819788018229550598119510) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 228 = 0 +
    228 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 228 = 32 +
      196 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 196 = 32 +
      164 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 164 = 32 +
      132 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 132 = 32 +
      100 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 100 = 27 +
      73 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_227_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (228 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_228 :
    recurrence2Scalar0Main.coeff 228 =
      ((((323 * 10 ^ 70 +
        5455236209801424610041435857794449550698297753882092810500358181051908) * 10 ^ 70 +
        4862081396301230589760872013070860107126658928474316566068483903791139) * 10 ^ 70 +
        7527840334643789797052081708805664721101153027499153674146158291949379) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 229 = 0 +
    229 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 229 = 32 +
      197 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 197 = 32 +
      165 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 27 +
      74 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_228_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (229 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_229 :
    recurrence2Scalar0Main.coeff 229 =
      -((((688 * 10 ^ 70 +
        3527544025375376708662954634292833355128301300388723997055376185069115) * 10 ^ 70 +
        7609223411657174185782757905863084079443216219432825051119953285814959) * 10 ^ 70 +
        3989270870057328343039452379404802047644896669379371387630778687174335) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 230 = 0 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 27 +
      75 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_229_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (230 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_230 :
    recurrence2Scalar0Main.coeff 230 =
      ((((1219 * 10 ^ 70 +
        7419526177743481023114519374405427627524231051376201976010109397736349) * 10 ^ 70 +
        0814381942232088147396429503047721117146722999671362984436367290989612) * 10 ^ 70 +
        1284206151867546401623162905321900199415567033334377752558603318206497) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 231 = 0 +
    231 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 231 = 32 +
      199 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 199 = 32 +
      167 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 167 = 32 +
      135 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 27 +
      76 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_230_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (231 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_231 :
    recurrence2Scalar0Main.coeff 231 =
      -((((1931 * 10 ^ 70 +
        9775546212692469152463269242029469807897860589010600419960718070433207) * 10 ^ 70 +
        8250197724177131728735357557546204984915701365461379496445603656179019) * 10 ^ 70 +
        7654508671113161442739801517340258362730248678641276071571674754970312) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 232 = 0 +
    232 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 232 = 32 +
      200 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 200 = 32 +
      168 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 168 = 32 +
      136 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 136 = 32 +
      104 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 104 = 27 +
      77 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_231_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (232 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_232 :
    recurrence2Scalar0Main.coeff 232 =
      ((((2817 * 10 ^ 70 +
        0295988678013253409163933522864067461773760504267117075990684960914462) * 10 ^ 70 +
        7669641792510907336541756721339511894115184229384238946340784312801879) * 10 ^ 70 +
        7311836215902119111258904866591548671781764857938786452225287840910362) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 233 = 0 +
    233 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 233 = 32 +
      201 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 201 = 32 +
      169 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 27 +
      78 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_232_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (233 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_233 :
    recurrence2Scalar0Main.coeff 233 =
      -((((3838 * 10 ^ 70 +
        4473875765882953468411278992795376291041440610849406368768812805798214) * 10 ^ 70 +
        4286792638022729688586007372284338219952823707501476968888486810856871) * 10 ^ 70 +
        7354383957617641737184101715960457586542999588868229037534821336045059) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 234 = 0 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 27 +
      79 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_233_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (234 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (234 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_234 :
    recurrence2Scalar0Main.coeff 234 =
      ((((4929 * 10 ^ 70 +
        4368763117735551828559682002406263335004923530953242705717342925338493) * 10 ^ 70 +
        6100946441501695072451523700190378913619691322455815441029712959762428) * 10 ^ 70 +
        4936829260051910850926350584238525733570343838517004723417103719249988) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 235 = 1 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 26 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_234_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (235 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (235 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_235 :
    recurrence2Scalar0Main.coeff 235 =
      -((((5996 * 10 ^ 70 +
        6977061976955231560115705808862635910987540626833836465651591019392047) * 10 ^ 70 +
        2055458738780199586624367727987362618885488527166923057485094367205854) * 10 ^ 70 +
        4697327418380295987151912663377008082480773236450417185893581112627223) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 236 = 2 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 25 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_235_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB5A6
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar2Shift coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2B1_coeff_0
  recurrence2B1_coeff_1
  recurrence2B1_coeff_2
  recurrence2B1_coeff_3
  recurrence2B1_coeff_4
  recurrence2B1_coeff_5
  recurrence2B1_coeff_6
  recurrence2B1_coeff_7
  recurrence2B1_coeff_8
  recurrence2B1_coeff_9
  recurrence2B1_coeff_10
  recurrence2B1_coeff_11
  recurrence2B1_coeff_12
  recurrence2B1_coeff_13
  recurrence2B1_coeff_14
  recurrence2B1_coeff_15
  recurrence2B1_coeff_16
  recurrence2B1_coeff_17
  recurrence2B1_coeff_18
  recurrence2B1_coeff_19
  recurrence2B1_coeff_20
  recurrence2B1_coeff_21
  recurrence2B1_coeff_22
  recurrence2B1_coeff_23
  recurrence2B1_coeff_24
  recurrence2B1_coeff_25
  recurrence2B1_coeff_26
  recurrence2B1_coeff_27
  recurrence2B1_coeff_28
  recurrence2B1_coeff_29
  recurrence2B1_coeff_30
  recurrence2B1_coeff_31
  recurrence2B1_coeff_32
  recurrence2B1_coeff_33
  recurrence2B1_coeff_34
  recurrence2B1_coeff_35
  recurrence2B1_coeff_36
  recurrence2B1_coeff_37
  recurrence2B1_coeff_38
  recurrence2B1_coeff_39
  recurrence2B1_coeff_40
  recurrence2B1_coeff_41
  recurrence2B1_coeff_42
  recurrence2B1_coeff_43
  recurrence2B1_coeff_44
  recurrence2B1_coeff_45
  recurrence2B1_coeff_46
  recurrence2B1_coeff_47
  recurrence2B1_coeff_48
  recurrence2B1_coeff_49
  recurrence2B1_coeff_50
  recurrence2B1_coeff_51
  recurrence2B1_coeff_52
  recurrence2B1_coeff_53
  recurrence2B1_coeff_54
  recurrence2B1_coeff_55
  recurrence2B1_coeff_56
  recurrence2B1_coeff_57
  recurrence2B1_coeff_58
  recurrence2B1_coeff_59
  recurrence2B1_coeff_60
  recurrence2B1_coeff_61
  recurrence2B1_coeff_62
  recurrence2B1_coeff_63
  recurrence2B1_coeff_64
  recurrence2B1_coeff_65
  recurrence2B1_coeff_66
  recurrence2B1_coeff_67
  recurrence2B1_coeff_68
  recurrence2B1_coeff_69
  recurrence2B1_coeff_70
  recurrence2B1_coeff_71
  recurrence2B1_coeff_72
  recurrence2B1_coeff_73
  recurrence2B1_coeff_74
  recurrence2B1_coeff_75
  recurrence2B1_coeff_76
  recurrence2B1_coeff_77
  recurrence2B1_coeff_78
  recurrence2B1_coeff_79
  recurrence2B1_coeff_80
  recurrence2B1_coeff_81
  recurrence2B1_coeff_82
  recurrence2B1_coeff_83
  recurrence2B1_coeff_84
  recurrence2B1_coeff_85
  recurrence2B1_coeff_86
  recurrence2B1_coeff_87
  recurrence2B1_coeff_88
  recurrence2B1_coeff_89
  recurrence2B1_coeff_90
  recurrence2B1_coeff_91
  recurrence2B1_coeff_92
  recurrence2B1_coeff_93
  recurrence2B1_coeff_94
  recurrence2B1_coeff_95
  recurrence2B1_coeff_96
  recurrence2B1_coeff_97
  recurrence2B1_coeff_98
  recurrence2B1_coeff_99
  recurrence2B1_coeff_100
  recurrence2B1_coeff_101
  recurrence2B1_coeff_102
  recurrence2B1_coeff_103
  recurrence2B1_coeff_104
  recurrence2B1_coeff_105
  recurrence2B1_coeff_106
  recurrence2B1_coeff_107
  recurrence2B1_coeff_108
  recurrence2B1_coeff_109
  recurrence2B1_coeff_110
  recurrence2B1_coeff_111
  recurrence2B1_coeff_112
  recurrence2B1_coeff_113
  recurrence2B1_coeff_114
  recurrence2B1_coeff_115
  recurrence2B1_coeff_116
  recurrence2B1_coeff_117
  recurrence2B1_coeff_118
  recurrence2B1_coeff_119
  recurrence2B1_coeff_120
  recurrence2B1_coeff_121
  recurrence2B1_coeff_122
  recurrence2B1_coeff_123
  recurrence2B1_coeff_124
  recurrence2B1_coeff_125
  recurrence2B1_coeff_126
  recurrence2B1_coeff_127
  recurrence2B1_coeff_128
  recurrence2B1_coeff_129
  recurrence2B1_coeff_130
  recurrence2B1_coeff_131
  recurrence2B1_coeff_132
  recurrence2B1_coeff_133
  recurrence2B1_coeff_134
  recurrence2B1_coeff_135
  recurrence2B1_coeff_136
  recurrence2B1_coeff_137
  recurrence2B1_coeff_138
  recurrence2B1_coeff_139
  recurrence2B1_coeff_140
  recurrence2B1_coeff_141
  recurrence2B1_coeff_142
  recurrence2B1_coeff_143
  recurrence2B1_coeff_144
  recurrence2B1_coeff_145
  recurrence2B1_coeff_146
  recurrence2B1_coeff_147
  recurrence2B1_coeff_148
  recurrence2B1_coeff_149
  recurrence2B1_coeff_150
  recurrence2B5A6_coeff_0
  recurrence2B5A6_coeff_1
  recurrence2B5A6_coeff_2
  recurrence2B5A6_coeff_3
  recurrence2B5A6_coeff_4
  recurrence2B5A6_coeff_5
  recurrence2B5A6_coeff_6
  recurrence2B5A6_coeff_7
  recurrence2B5A6_coeff_8
  recurrence2B5A6_coeff_9
  recurrence2B5A6_coeff_10
  recurrence2B5A6_coeff_11
  recurrence2B5A6_coeff_12
  recurrence2B5A6_coeff_13
  recurrence2B5A6_coeff_14
  recurrence2B5A6_coeff_15
  recurrence2B5A6_coeff_16
  recurrence2B5A6_coeff_17
  recurrence2B5A6_coeff_18
  recurrence2B5A6_coeff_19
  recurrence2B5A6_coeff_20
  recurrence2B5A6_coeff_21
  recurrence2B5A6_coeff_22
  recurrence2B5A6_coeff_23
  recurrence2B5A6_coeff_24
  recurrence2B5A6_coeff_25
  recurrence2B5A6_coeff_26
  recurrence2B5A6_coeff_27
  recurrence2B5A6_coeff_28
  recurrence2B5A6_coeff_29
  recurrence2B5A6_coeff_30
  recurrence2B5A6_coeff_31
  recurrence2B5A6_coeff_32
  recurrence2B5A6_coeff_33
  recurrence2B5A6_coeff_34
  recurrence2B5A6_coeff_35
  recurrence2B5A6_coeff_36
  recurrence2B5A6_coeff_37
  recurrence2B5A6_coeff_38
  recurrence2B5A6_coeff_39
  recurrence2B5A6_coeff_40
  recurrence2B5A6_coeff_41
  recurrence2B5A6_coeff_42
  recurrence2B5A6_coeff_43
  recurrence2B5A6_coeff_44
  recurrence2B5A6_coeff_45
  recurrence2B5A6_coeff_46
  recurrence2B5A6_coeff_47
  recurrence2B5A6_coeff_48
  recurrence2B5A6_coeff_49
  recurrence2B5A6_coeff_50
  recurrence2B5A6_coeff_51
  recurrence2B5A6_coeff_52
  recurrence2B5A6_coeff_53
  recurrence2B5A6_coeff_54
  recurrence2B5A6_coeff_55
  recurrence2B5A6_coeff_56
  recurrence2B5A6_coeff_57
  recurrence2B5A6_coeff_58
  recurrence2B5A6_coeff_59
  recurrence2B5A6_coeff_60
  recurrence2B5A6_coeff_61
  recurrence2B5A6_coeff_62
  recurrence2B5A6_coeff_63
  recurrence2B5A6_coeff_64
  recurrence2B5A6_coeff_65
  recurrence2B5A6_coeff_66
  recurrence2B5A6_coeff_67
  recurrence2B5A6_coeff_68
  recurrence2B5A6_coeff_69
  recurrence2B5A6_coeff_70
  recurrence2B5A6_coeff_71
  recurrence2B5A6_coeff_72
  recurrence2B5A6_coeff_73
  recurrence2B5A6_coeff_74
  recurrence2B5A6_coeff_75
  recurrence2B5A6_coeff_76
  recurrence2B5A6_coeff_77
  recurrence2B5A6_coeff_78
  recurrence2B5A6_coeff_79
  recurrence2B5A6_coeff_80
  recurrence2B5A6_coeff_81
  recurrence2B5A6_coeff_82
  recurrence2B5A6_coeff_83
  recurrence2B5A6_coeff_84
  recurrence2B5A6_coeff_85
  recurrence2B5A6_coeff_86
  recurrence2B5A6_coeff_87
  recurrence2B5A6_coeff_88
  recurrence2B5A6_coeff_89
  recurrence2B5A6_coeff_90
  recurrence2B5A6_coeff_91
  recurrence2B5A6_coeff_92
  recurrence2B5A6_coeff_93
  recurrence2B5A6_coeff_94
  recurrence2B5A6_coeff_95
  recurrence2B5A6_coeff_96
  recurrence2B5A6_coeff_97
  recurrence2B5A6_coeff_98
  recurrence2B5A6_coeff_99
  recurrence2B5A6_coeff_100
  recurrence2B5A6_coeff_101
  recurrence2B5A6_coeff_102
  recurrence2B5A6_coeff_103
  recurrence2B5A6_coeff_104
  recurrence2B5A6_coeff_105
  recurrence2B5A6_coeff_106
  recurrence2B5A6_coeff_107
  recurrence2B5A6_coeff_108
  recurrence2B5A6_coeff_109
  recurrence2B5A6_coeff_110
  recurrence2B5A6_coeff_111
  recurrence2B5A6_coeff_112
  recurrence2B5A6_coeff_113
  recurrence2B5A6_coeff_114
  recurrence2B5A6_coeff_115
  recurrence2B5A6_coeff_116
  recurrence2B5A6_coeff_117
  recurrence2B5A6_coeff_118
  recurrence2B5A6_coeff_119
  recurrence2B5A6_coeff_120
  recurrence2B5A6_coeff_121
  recurrence2B5A6_coeff_122
  recurrence2B5A6_coeff_123
  recurrence2B5A6_coeff_124
  recurrence2B5A6_coeff_125
  recurrence2B5A6_coeff_126
  recurrence2B5A6_coeff_127
  recurrence2B5A6_coeff_128
  recurrence2B5A6_coeff_129
  recurrence2B5A6_coeff_130
  recurrence2B5A6_coeff_131
  recurrence2B5A6_coeff_132
  recurrence2B5A6_coeff_133
  recurrence2B5A6_coeff_134
  recurrence2B5A6_coeff_135
  recurrence2B5A6_coeff_136
  recurrence2B5A6_coeff_137
  recurrence2B5A6_coeff_138
  recurrence2B5A6_coeff_139
  recurrence2B5A6_coeff_140
  recurrence2B5A6_coeff_141
  recurrence2B5A6_coeff_142
  recurrence2B5A6_coeff_143
  recurrence2B5A6_coeff_144
  recurrence2B5A6_coeff_145
  recurrence2B5A6_coeff_146
  recurrence2B5A6_coeff_147
  recurrence2B5A6_coeff_148
  recurrence2B5A6_coeff_149
  recurrence2B5A6_coeff_150
  recurrence2B5A6_coeff_151
  recurrence2B5A6_coeff_152
  recurrence2B5A6_coeff_153
  recurrence2B5A6_coeff_154
  recurrence2B5A6_coeff_155
  recurrence2B5A6_coeff_156
  recurrence2B5A6_coeff_157
  recurrence2B5A6_coeff_158
  recurrence2B5A6_coeff_159
  recurrence2B5A6_coeff_160
  recurrence2B5A6_coeff_161
  recurrence2B5A6_coeff_162
  recurrence2B5A6_coeff_163
  recurrence2B5A6_coeff_164
  recurrence2B5A6_coeff_165
  recurrence2B5A6_coeff_166
  recurrence2B5A6_coeff_167
  recurrence2B5A6_coeff_168
  recurrence2B5A6_coeff_169
  recurrence2B5A6_coeff_170
  recurrence2B5A6_coeff_171
  recurrence2B5A6_coeff_172
  recurrence2B5A6_coeff_173
  recurrence2B5A6_coeff_174
  recurrence2B5A6_coeff_175
  recurrence2B5A6_coeff_176
  recurrence2B5A6_coeff_177
  recurrence2B5A6_coeff_178
  recurrence2B5A6_coeff_179
  recurrence2B5A6_coeff_180
  recurrence2B5A6_coeff_181
  recurrence2B5A6_coeff_182
  recurrence2B5A6_coeff_183
  recurrence2B5A6_coeff_184
  recurrence2B5A6_coeff_185
  recurrence2B5A6_coeff_186
  recurrence2B5A6_coeff_187
  recurrence2B5A6_coeff_188
  recurrence2B5A6_coeff_189
  recurrence2B5A6_coeff_190
  recurrence2B5A6_coeff_191
  recurrence2B5A6_coeff_192
  recurrence2B5A6_coeff_193
  recurrence2B5A6_coeff_194
  recurrence2B5A6_coeff_195
  recurrence2B5A6_coeff_196
  recurrence2B5A6_coeff_197
  recurrence2B5A6_coeff_198
  recurrence2B5A6_coeff_199
  recurrence2B5A6_coeff_200
  recurrence2B5A6_coeff_201
  recurrence2B5A6_coeff_202
  recurrence2B5A6_coeff_203
  recurrence2B5A6_coeff_204
  recurrence2B5A6_coeff_205
  recurrence2B5A6_coeff_206
  recurrence2B5A6_coeff_207
  recurrence2B5A6_coeff_208
  recurrence2B5A6_coeff_209
  recurrence2B5A6_coeff_210
  recurrence2B5A6_coeff_211
  recurrence2B5A6_coeff_212
  recurrence2B5A6_coeff_213
  recurrence2B5A6_coeff_214
  recurrence2B5A6_coeff_215
  recurrence2B5A6_coeff_216
  recurrence2B5A6_coeff_217
  recurrence2B5A6_coeff_218
  recurrence2B5A6_coeff_219
  recurrence2B5A6_coeff_220
  recurrence2B5A6_coeff_221
  recurrence2B5A6_coeff_222
  recurrence2B5A6_coeff_223
  recurrence2B5A6_coeff_224
  recurrence2B5A6_coeff_225
  recurrence2B5A6_coeff_226
  recurrence2B5A6_coeff_227
  recurrence2B5A6_coeff_228
  recurrence2B5A6_coeff_229

private theorem recurrence2Scalar2Shift_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (234 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (234 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_234 :
    recurrence2Scalar2Shift.coeff 234 =
      ((((48 * 10 ^ 70 +
        2962827913965204441738001666219567317871876274463657598126022907390265) * 10 ^ 70 +
        4228325507692423703258496434312210842870779908511480452241313174463135) * 10 ^ 70 +
        8822618747197629630089221450846338301362698919453238836795882130225162) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 235 = 5 +
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
    rw [show 102 = 18 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_234_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (235 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (235 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_235 :
    recurrence2Scalar2Shift.coeff 235 =
      -((((36 * 10 ^ 70 +
        2190689495487898547553993397841742446260549355813899767495833555470646) * 10 ^ 70 +
        2255438662295955506395230489630087629770362854344266139853695647341779) * 10 ^ 70 +
        6159830212430958205332965387328957645179393088121560477028201041078707) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 236 = 6 +
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
    rw [show 102 = 17 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_235_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (236 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (236 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_236 :
    recurrence2Scalar2Shift.coeff 236 =
      ((((20 * 10 ^ 70 +
        6010266253252941148904635726743268413616435238082671175756339892389530) * 10 ^ 70 +
        0588795760586034099322676167261349373158733624403364961842527709648878) * 10 ^ 70 +
        9746247687887126252704257534950366944620699215499268069674213661896012) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 237 = 7 +
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
    rw [show 102 = 16 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_236_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (237 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (237 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_237 :
    recurrence2Scalar2Shift.coeff 237 =
      -((((2 * 10 ^ 70 +
        9246045897399059095618852318896129876438809197590827390277497678048309) * 10 ^ 70 +
        6614978567776163825088581937738593259403337879591990988311370807252985) * 10 ^ 70 +
        2343904691615547347767057109886289353524004495151013188075864552135695) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 238 = 8 +
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
    rw [show 102 = 15 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_237_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (238 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (238 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_238 :
    recurrence2Scalar2Shift.coeff 238 =
      -((((15 * 10 ^ 70 +
        0122941114894798788877071021396046095083558579569677103214018185327495) * 10 ^ 70 +
        5350157152480672470110101849793445359574342417755076337042735012957221) * 10 ^ 70 +
        0849628554476050027605364856023632828864816053221488850508551319845589) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 239 = 9 +
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
    rw [show 102 = 14 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_238_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (239 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (239 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_239 :
    recurrence2Scalar2Shift.coeff 239 =
      ((((31 * 10 ^ 70 +
        3858421888809494486613324232295619512155046974038151311654249997290172) * 10 ^ 70 +
        9372577647722527013012939313254466216831348304518412440356046991208905) * 10 ^ 70 +
        5103138692793371382250468381176230086712235553860372746506428103697279) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 240 = 10 +
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
    rw [show 102 = 13 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_239_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (240 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (240 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_240 :
    recurrence2Scalar2Shift.coeff 240 =
      -((((44 * 10 ^ 70 +
        6376390115002654768713496314733985290443342732597194420154043448242590) * 10 ^ 70 +
        5404429024374801901306310022051828010954946983124356642539954428828292) * 10 ^ 70 +
        1463717980521246198721095751136827342579518915942150687285790205804255) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 241 = 11 +
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
    rw [show 102 = 12 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_240_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (241 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (241 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_241 :
    recurrence2Scalar2Shift.coeff 241 =
      ((((53 * 10 ^ 70 +
        7058635175361350180945849030648275047288110065710904922239093746067700) * 10 ^ 70 +
        3357137623813454306645449992188275759573278730017794292045914902998213) * 10 ^ 70 +
        3042315987536898038463144777346122425694811804411936792083626186189959) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 242 = 12 +
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
    rw [show 102 = 11 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_241_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (242 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 92,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (242 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_242 :
    recurrence2Scalar2Shift.coeff 242 =
      -((((58 * 10 ^ 70 +
        1510036327376251140569163515681145650661985163124413412653386260759354) * 10 ^ 70 +
        2262370887992595835357832129209939838809659875144981511887877665063058) * 10 ^ 70 +
        4428951997396214693773513451069550465839807339074210949494090374594583) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 243 = 13 +
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
    rw [show 102 = 10 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_242_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (243 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 93,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (243 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_243 :
    recurrence2Scalar2Shift.coeff 243 =
      ((((58 * 10 ^ 70 +
        1584894767227658790863341269289325003285141116989983957972891375880732) * 10 ^ 70 +
        6860605727937503424618345668639522275440435140459566140236617025641166) * 10 ^ 70 +
        6406405075009981528426457265746255063894723534878210252819370603458177) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 244 = 14 +
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
    rw [show 102 = 9 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_243_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (244 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 94,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (244 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_244 :
    recurrence2Scalar2Shift.coeff 244 =
      -((((54 * 10 ^ 70 +
        4304089357797021876148075169687403562272725315516804003565278763557885) * 10 ^ 70 +
        4206222861174817058489621720318896158554309611513062238028566750499401) * 10 ^ 70 +
        2968827249611740100901531153609395777325740925458931948667020697754325) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 245 = 15 +
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
    rw [show 102 = 8 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_244_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (245 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 95,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (245 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_245 :
    recurrence2Scalar2Shift.coeff 245 =
      ((((48 * 10 ^ 70 +
        0021732619105953940122364599892271432592321085994290384043415676851913) * 10 ^ 70 +
        7732047748980429357450297228285252845199532473999790186050706444794691) * 10 ^ 70 +
        9738886844371714569090433930401288171144423296186654796652546950685414) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 246 = 16 +
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
    rw [show 102 = 7 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_245_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (246 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 96,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (246 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_246 :
    recurrence2Scalar2Shift.coeff 246 =
      -((((40 * 10 ^ 70 +
        0317810926116711082879961142581124328373381458388114661474967101447268) * 10 ^ 70 +
        4495886788183502668557485476236752839496482454238369687402670229033129) * 10 ^ 70 +
        7850718211361120538963653449418562204580234037022107999942751438355413) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 247 = 17 +
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
    rw [show 102 = 6 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_246_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (247 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 97,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (247 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_247 :
    recurrence2Scalar2Shift.coeff 247 =
      ((((31 * 10 ^ 70 +
        6076749295505813183146786870569200735429142380123354995612980988313379) * 10 ^ 70 +
        9393518053817560584652340640180902255884096458984227454954923404092530) * 10 ^ 70 +
        1798688169452839111214344765908693927091252430859363887462660566225911) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 248 = 18 +
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
    rw [show 102 = 5 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_247_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (248 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 98,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (248 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_248 :
    recurrence2Scalar2Shift.coeff 248 =
      -((((23 * 10 ^ 70 +
        6086835459845646092975590954239387139590395017201379410284940719192771) * 10 ^ 70 +
        5782546402808545392024902236658362183194198405319372362452936896568532) * 10 ^ 70 +
        7599725458797910033801271489668915814650429118362336943624220128370271) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 249 = 19 +
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
    rw [show 102 = 4 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_248_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (249 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 99,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (249 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_249 :
    recurrence2Scalar2Shift.coeff 249 =
      ((((16 * 10 ^ 70 +
        6314474328256077317266682372041941362249313996353358837954215977000053) * 10 ^ 70 +
        2441178602412307935876369392598258509578304257340366960149613961401043) * 10 ^ 70 +
        3371836281923524654322962549210100797213043960683712526460610464728062) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 250 = 20 +
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
    rw [show 102 = 3 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_249_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (250 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 100,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (250 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_250 :
    recurrence2Scalar2Shift.coeff 250 =
      -((((10 * 10 ^ 70 +
        9828627824549486149701963195261944605109566581065176994788877118413484) * 10 ^ 70 +
        3674996153446893828663972694753898790625531984231583578068208374139489) * 10 ^ 70 +
        3154277891426453826051354743039905560324405162727538425119669455053522) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 251 = 21 +
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
    rw [show 102 = 2 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_250_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (251 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 101,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (251 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_251 :
    recurrence2Scalar2Shift.coeff 251 =
      ((((6 * 10 ^ 70 +
        7219871008979510213505086662747763326655953933827576876226701581620840) * 10 ^ 70 +
        1423281795987172193108027504851744869841938594389142316395843052784844) * 10 ^ 70 +
        6417225282550830204072361991292161538073812385328254657054127412326918) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 252 = 22 +
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
    rw [show 102 = 1 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_251_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_251_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (252 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 102,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (252 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_252 :
    recurrence2Scalar2Shift.coeff 252 =
      -((((3 * 10 ^ 70 +
        7296954300550042501373299481379288831624076877499066961801085208932339) * 10 ^ 70 +
        6055422100922595465670072018909736494358034338813947297894772478557420) * 10 ^ 70 +
        6227974827135937429466095573149666726655048732217771033782439173300694) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 253 = 23 +
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
  rw [recurrence2Scalar2Shift_coeff_252_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_252_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (253 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 103,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (253 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_253 :
    recurrence2Scalar2Shift.coeff 253 =
      ((((1 * 10 ^ 70 +
        7848885883886769583070130980775502699272880485400698682945631377818524) * 10 ^ 70 +
        2267073548768168704835685225143641456050899737859263601371376349389145) * 10 ^ 70 +
        6975862832398219151988746282524805902120523660961826330366817798923190) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 254 = 24 +
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
    rw [show 134 = 31 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_253_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (254 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 104,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (254 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_254 :
    recurrence2Scalar2Shift.coeff 254 =
      -(((6312301770305459578442851637688437330439525166073941787173585596013019 * 10 ^ 70 +
        5064674725781192943165362067747739738344651869589431054648656555092429) * 10 ^ 70 +
        4842497528055149182312964893515837630176651768248178050636747527526282) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 255 = 25 +
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
    rw [show 134 = 30 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_254_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (255 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 105,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (255 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_255 :
    recurrence2Scalar2Shift.coeff 255 =
      (((255506465793852879611511993813218072286857349565370743806458533566380 * 10 ^ 70 +
        3291942862738296113168727366691280166717468146026876336451058243375929) * 10 ^ 70 +
        9949001716473500565900826735529646268306800196654613780890075364144263) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 256 = 26 +
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
    rw [show 134 = 29 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_255_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (256 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 106,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (256 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_256 :
    recurrence2Scalar2Shift.coeff 256 =
      (((2341796344176257440915365955761500643035478445033530852623957660550082 * 10 ^ 70 +
        7643358211697304369876400276781785135908801634224907523648623137945087) * 10 ^ 70 +
        1552827999472881497396604853999999523287495197468108649528242216522749) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 257 = 27 +
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
    rw [show 134 = 28 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_256_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (257 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 107,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (257 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_257 :
    recurrence2Scalar2Shift.coeff 257 =
      -(((2985464885138773705026035345829957780384117370691217714074807626208396 * 10 ^ 70 +
        8947986140864625982232791447288102997838222658077907942831902521015713) * 10 ^ 70 +
        9950737582014413972258120223303533352839028461597623888593301278136762) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 258 = 28 +
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
    rw [show 134 = 27 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_257_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (258 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 108,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (258 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_258 :
    recurrence2Scalar2Shift.coeff 258 =
      (((2688329394878073578326619194496281170623274222416528761643644139255876 * 10 ^ 70 +
        7463853446094363907172524664025796664876909855909341013404545861158847) * 10 ^ 70 +
        8705595290620570861371839682500534691640284558742849103892526084781435) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 259 = 29 +
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
    rw [show 134 = 26 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_258_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (259 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 109,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (259 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_259 :
    recurrence2Scalar2Shift.coeff 259 =
      -(((2060110971312770383784079461313145951045947354015574116523588982841499 * 10 ^ 70 +
        3576701471306738119860373164832965848054134488222503517024887749911158) * 10 ^ 70 +
        4384333548310348675467345074811113490039334315004720333124413808505513) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 260 = 30 +
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
    rw [show 134 = 25 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_259_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (260 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 110,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (260 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_260 :
    recurrence2Scalar2Shift.coeff 260 =
      (((1419859840253737887937127792723299402643702874169276421101596325671142 * 10 ^ 70 +
        9471817969395373191800104151588213794204035395033005929678238916931064) * 10 ^ 70 +
        9035493899111856804970892038096331022219441971985117544454032624221347) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 261 = 31 +
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
    rw [show 134 = 24 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_260_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (261 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 111,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (261 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_261 :
    recurrence2Scalar2Shift.coeff 261 =
      -(((900624950193395317982976310468280861340696507335073300295596730983903 * 10 ^ 70 +
        3942701259104463084878728337627769672451978613963136278481035830642665) * 10 ^ 70 +
        6297039465373009725265104056806966979173863055623753364272346593797505) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 262 = 32 +
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
    rw [show 134 = 23 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_261_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (262 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 112,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (262 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_262 :
    recurrence2Scalar2Shift.coeff 262 =
      (((531401147264142943434836783412510489851410766072982544702024155092776 * 10 ^ 70 +
        8588637295225962560581157425080166335336807911393127747654167587531273) * 10 ^ 70 +
        2706248311266452239978360530760256871954000426551338820885854232534930) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 263 = 33 +
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
    rw [show 134 = 22 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_262_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (263 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 113,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (263 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_263 :
    recurrence2Scalar2Shift.coeff 263 =
      -(((292952003725448832628172272851543689366298682011011097511294213513572 * 10 ^ 70 +
        0131526671754217837706904778839777322156158002626079365557897306803038) * 10 ^ 70 +
        4892015756361626397892704042614965947895353030563388130296001799967647) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 264 = 34 +
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
    rw [show 134 = 21 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_263_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (264 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 114,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (264 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_264 :
    recurrence2Scalar2Shift.coeff 264 =
      (((150920580440551130199955047097878107706258140745910022308530430347533 * 10 ^ 70 +
        9363033958752869837498274703092293712100810087439661866303399769036142) * 10 ^ 70 +
        3639548729485558579533534580954945282253694050569096037317424154862627) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 265 = 35 +
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
    rw [show 134 = 20 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_264_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (265 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 115,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (265 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_265 :
    recurrence2Scalar2Shift.coeff 265 =
      -(((72382307710137060036792432980666829050645212783618265776723306297419 * 10 ^ 70 +
        5770244255423849928431998392523851052974819389464321776889297284747928) * 10 ^ 70 +
        1930849293888061121148829401236610678470442778865663156508328476293976) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 266 = 36 +
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
    rw [show 134 = 19 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_265_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (266 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 116,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (266 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_266 :
    recurrence2Scalar2Shift.coeff 266 =
      (((32025426077174270233886456060290433743208691193223241601221168369851 * 10 ^ 70 +
        0461956998040511591549963431763140670947456506080749731972124305964381) * 10 ^ 70 +
        9327051817690650480933060640508862269294171483289567623583306361124276) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 267 = 37 +
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
    rw [show 134 = 18 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_266_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (267 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 117,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (267 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_267 :
    recurrence2Scalar2Shift.coeff 267 =
      -(((12830409958372056761191967383443123580807413530696797696974570545777 * 10 ^ 70 +
        5404080132971994843664661136377874584234488163637172208627381999105666) * 10 ^ 70 +
        6092673117634037446672713813393041602369757044173733061596645120813107) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 268 = 38 +
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
    rw [show 134 = 17 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_267_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (268 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 118,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (268 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_268 :
    recurrence2Scalar2Shift.coeff 268 =
      (((4467265312436043746002885869480827786537808428563770938911573631806 * 10 ^ 70 +
        2719293989369163298282844590657378626413185421997949869287045930715570) * 10 ^ 70 +
        1079860660926905123863786978996573324848816514027543147177937096809645) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 269 = 39 +
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
    rw [show 134 = 16 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_268_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (269 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 119,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (269 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_269 :
    recurrence2Scalar2Shift.coeff 269 =
      -(((1203479375274657055289267183182563427642579086575001355381679730473 * 10 ^ 70 +
        6462254616119439622312153402482463777226386251556572824238399313072041) * 10 ^ 70 +
        1749223463434334336267061011381465059098530526482636315303531742535810) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 270 = 40 +
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
    rw [show 134 = 15 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_269_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (270 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 120,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (270 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_270 :
    recurrence2Scalar2Shift.coeff 270 =
      (((121061429829506239845213466482725873126934532452909499079044683830 * 10 ^ 70 +
        9943780168106947855197028742090272651935137075094446671248009728640714) * 10 ^ 70 +
        7087198776527659916178923021463024773814199682086666954764530879272921) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 271 = 41 +
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
    rw [show 134 = 14 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_270_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (271 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 121,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (271 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_271 :
    recurrence2Scalar2Shift.coeff 271 =
      (((136447268273609378952565838790899711138987923622979187303105363956 * 10 ^ 70 +
        6187567675269018781684277915956080928623144225195018802007016097826782) * 10 ^ 70 +
        1643530469776696591201539484615283198556770779687179834179310352286739) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 272 = 42 +
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
    rw [show 134 = 13 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_271_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (272 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 122,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (272 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_272 :
    recurrence2Scalar2Shift.coeff 272 =
      -(((136692103957674260766955318055045477476979960331381952331932487099 * 10 ^ 70 +
        8835717429248434138340262156251317499372825250046766505148597278354818) * 10 ^ 70 +
        2073886823382376535651186871998136493735926298210598814893450622678065) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 273 = 43 +
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
    rw [show 134 = 12 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_272_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (273 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 123,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (273 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_273 :
    recurrence2Scalar2Shift.coeff 273 =
      (((86278162971422170754309043267651668728131907132887655738497600570 * 10 ^ 70 +
        3575339058942497803349205047805066663648994574888523403847848127238780) * 10 ^ 70 +
        8648705463675450746844817259980724204697062503533947373556342347592647) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 274 = 44 +
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
    rw [show 134 = 11 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_273_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (274 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 124,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (274 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_274 :
    recurrence2Scalar2Shift.coeff 274 =
      -(((44667983946692880239030397728351590438751669051557647770409190873 * 10 ^ 70 +
        6504914380971383181707980884766933029919429764493066474722306215166438) * 10 ^ 70 +
        0524019926947105574769160201228875049655339541999397200252145073884013) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 275 = 45 +
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
    rw [show 134 = 10 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_274_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (275 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 125,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (275 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_275 :
    recurrence2Scalar2Shift.coeff 275 =
      (((20238405382895585452412703717783741503221326716096687523036596029 * 10 ^ 70 +
        7705060796653513016870456179282082940361784738615895202366683815464094) * 10 ^ 70 +
        5260839924944995915572008830966724061583705266229790360168749306392583) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 276 = 46 +
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
    rw [show 134 = 9 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_275_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (276 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 126,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (276 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_276 :
    recurrence2Scalar2Shift.coeff 276 =
      -(((8193772790726924955349766474125609786974905452209596907920057838 * 10 ^ 70 +
        5349931444603792257965818851500911144711636861361356279316209265560635) * 10 ^ 70 +
        9915312400115999340398431788729205461366917372495106175861288296770314) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 277 = 47 +
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
    rw [show 134 = 8 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_276_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (277 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 127,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (277 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_277 :
    recurrence2Scalar2Shift.coeff 277 =
      (((2968413801362859009150152677795644358107001267942265271061227731 * 10 ^ 70 +
        4129849218772029327601789875681991763106961661797370267816200066130297) * 10 ^ 70 +
        7682679666520112741000886188759924247363240252430057908188119544786346) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 278 = 48 +
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
    rw [show 134 = 7 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_277_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (278 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 128,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (278 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_278 :
    recurrence2Scalar2Shift.coeff 278 =
      -(((947089763352013695381244865909725440752269597902289289358212228 * 10 ^ 70 +
        3568562710420271151667232627411099008580412899084517654058410127517176) * 10 ^ 70 +
        3133156536328754442077765691383169167716342113252034548947925051347903) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 279 = 49 +
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
    rw [show 134 = 6 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_278_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (279 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 129,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (279 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_279 :
    recurrence2Scalar2Shift.coeff 279 =
      (((253665504201147603807725474404269497743327095660191298092514436 * 10 ^ 70 +
        0660248443993538669072322953445294013003376967430791334581844904268056) * 10 ^ 70 +
        4284022152760979328893950167328870994100145017722005412385044479223132) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 280 = 50 +
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
    rw [show 134 = 5 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_279_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (280 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 130,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (280 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_280 :
    recurrence2Scalar2Shift.coeff 280 =
      -(((48562162441140780324700127285147913164609128059807418309992523 * 10 ^ 70 +
        2110652818739285135638502401917443386847898510786162933026403200374530) * 10 ^ 70 +
        9166352817173652487903236651739540275316318608139444200872781842216431) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 281 = 51 +
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
    rw [show 134 = 4 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_280_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (281 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 131,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (281 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_281 :
    recurrence2Scalar2Shift.coeff 281 =
      (((525433296574843902275555657726520289404396906368748768019115 * 10 ^ 70 +
        7084284897645315149854403534728932435838775198468620325307745638447886) * 10 ^ 70 +
        1752231070370673966951560223898837362698650387499585393889833064555051) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 282 = 52 +
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
    rw [show 134 = 3 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_281_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (282 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 132,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (282 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_282 :
    recurrence2Scalar2Shift.coeff 282 =
      (((5429901153611952300959760981010144828046311785192474136986457 * 10 ^ 70 +
        9338857453996735111049787497239022077428307329652879678114483254845673) * 10 ^ 70 +
        5568204219730577917673879050188538578937063379889252458221388475528617) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 283 = 53 +
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
    rw [show 134 = 2 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_282_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (283 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 133,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (283 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_283 :
    recurrence2Scalar2Shift.coeff 283 =
      -(((3464894190870487358557965569082695986809887198846807398758333 * 10 ^ 70 +
        8698515436132428744044669080874262848342993686310981333240604368657205) * 10 ^ 70 +
        1807333185707522034263319715354562055887850402483028069226016816383953) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 284 = 54 +
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
    rw [show 134 = 1 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_283_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 55,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (284 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 134,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (284 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_284 :
    recurrence2Scalar2Shift.coeff 284 =
      (((1528591349494439856204600559164719135354950610588628225886382 * 10 ^ 70 +
        6546171320108478386241342388939331813413304087458880464781535651337708) * 10 ^ 70 +
        6347184606881013113253936137999739879653152739628483866101306368648596) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 285 = 55 +
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
  rw [recurrence2Scalar2Shift_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_284_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 56,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (285 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 135,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (285 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_285 :
    recurrence2Scalar2Shift.coeff 285 =
      -(((551026473495782837516117679917596802880797368874796430366849 * 10 ^ 70 +
        4291410267577492273684523998333696777003350334042871063057029628853589) * 10 ^ 70 +
        9086959557666324637480729029756569643348810520438746253902724092435993) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 286 = 56 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 31 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_285_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 57,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (286 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 136,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (286 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_286 :
    recurrence2Scalar2Shift.coeff 286 =
      (((168142943748715401308358358424614574454191259506948651619579 * 10 ^ 70 +
        7780388160619303430735529204473696665368640459943079363288101546553917) * 10 ^ 70 +
        5537637412945497191957061302520442354005197321496062424265972763419095) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 287 = 57 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 30 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_286_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 58,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (287 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 137,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (287 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_287 :
    recurrence2Scalar2Shift.coeff 287 =
      -(((42756480222530860649345186297827821060076442897094567900269 * 10 ^ 70 +
        9537256030622366379529160269511727076326355091491871245211294788310085) * 10 ^ 70 +
        3176709650501777587656160023698034606394466563537506726671094439848463) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 288 = 58 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 29 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_287_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 59,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (288 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 138,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (288 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_288 :
    recurrence2Scalar2Shift.coeff 288 =
      (((8254060128515612340602177706734701732823701276698275767371 * 10 ^ 70 +
        2876555883731262085472088219972041188385820704683279623276539173325864) * 10 ^ 70 +
        1495927512420373886261470108688035940413757810469953612583046602985478) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 289 = 59 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 28 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_288_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 60,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 139,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (289 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_289 :
    recurrence2Scalar2Shift.coeff 289 =
      -(((690367696313948815877618184017168937590339752029980199231 * 10 ^ 70 +
        6906890151189638082747376102178723287128981071617434016568424429534966) * 10 ^ 70 +
        3755309709877465686025620762957722476446160184218828465354903434783176) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 290 = 60 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 27 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_289_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 61,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 140,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (290 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_290 :
    recurrence2Scalar2Shift.coeff 290 =
      -(((339182002236006524029978111828257937123143190892132846878 * 10 ^ 70 +
        5169145229440759940893831850306648918068346770063557517347648346377733) * 10 ^ 70 +
        9202127754625710573557341697667886346994800082782144171265416474407176) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 291 = 61 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 26 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_290_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 62,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (291 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 141,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (291 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_291 :
    recurrence2Scalar2Shift.coeff 291 =
      (((234070587960755050412152252841200379019986280619531854590 * 10 ^ 70 +
        3767357644271380392949369349773605397958189514239799262969279287835581) * 10 ^ 70 +
        1724720993947189799629360660278758161108885290732871414446424734911551) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 292 = 62 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 25 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_291_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 63,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (292 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 142,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (292 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_292 :
    recurrence2Scalar2Shift.coeff 292 =
      -(((92820369671971294090691578337936774116902777396789856335 * 10 ^ 70 +
        2433659738167036178851760826596435248509184278513844115405390244312879) * 10 ^ 70 +
        2290550093550435850763717263767552090322776733974318602422390607580135) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 293 = 63 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 24 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_292_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 64,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (293 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 143,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (293 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_293 :
    recurrence2Scalar2Shift.coeff 293 =
      (((28665506374262170563717902182871733089921030203381595473 * 10 ^ 70 +
        8934061086717027389813781110965897235058232091344389081735471253991948) * 10 ^ 70 +
        3862259346186415061478543011087558883962606438381945161086528925858261) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 294 = 64 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 23 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_293_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 65,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (294 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 144,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (294 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_294 :
    recurrence2Scalar2Shift.coeff 294 =
      -(((7281364781744811320894888437826495908951131275395621998 * 10 ^ 70 +
        7181445106028205970337325419657530875499126679121562176926982217272284) * 10 ^ 70 +
        3024436774200736200225135356180504182421125163965451951116594603417913) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 295 = 65 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 22 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_294_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (295 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 145,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (295 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_295 :
    recurrence2Scalar2Shift.coeff 295 =
      (((1493795809075001434190071456489441092252450803602883865 * 10 ^ 70 +
        1547782166956496858582556063022951436129575957452907245286402453935811) * 10 ^ 70 +
        9696762023645577475685973835859138116602126244931400874598702546627065) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 296 = 66 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 21 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_295_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (296 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 146,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (296 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_296 :
    recurrence2Scalar2Shift.coeff 296 =
      -(((217165507425195798722801188377005935370268532617130327 * 10 ^ 70 +
        7276575492775654753793422826743926011960326956149041389934687439895308) * 10 ^ 70 +
        9607789970045014608227933632831514414833662865968448673467594101364554) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 297 = 67 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 20 +
      146 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_296_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (297 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 147,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (297 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_297 :
    recurrence2Scalar2Shift.coeff 297 =
      (((5702462625085868787804276865735180638135996602029187 * 10 ^ 70 +
        8052102335682960113596734057434764498446600600112086682475051821472211) * 10 ^ 70 +
        5104256837409248185659251890332235998174213001815952158443882428294662) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 298 = 68 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 19 +
      147 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_297_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (298 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 148,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (298 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_298 :
    recurrence2Scalar2Shift.coeff 298 =
      (((10102127990504837050937526522508646487186322725440209 * 10 ^ 70 +
        1952605197899198642441295938384785729825054057286243533856342919827409) * 10 ^ 70 +
        6674172954094825983041921855749437312136331246848389852805660082070871) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 299 = 69 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 18 +
      148 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_298_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (299 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 149,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (299 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_299 :
    recurrence2Scalar2Shift.coeff 299 =
      -(((4568904120008293905792115646582877759414873138658628 * 10 ^ 70 +
        4424618453604155123036329079875604107515719492458786117872612738419659) * 10 ^ 70 +
        2557776001240169878063771199593669132762352191324668071459680935405766) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 300 = 70 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 17 +
      149 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_299_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (300 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 150,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (300 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_300 :
    recurrence2Scalar2Shift.coeff 300 =
      (((1344061608988275739421175627475843445442114387392985 * 10 ^ 70 +
        8075301338095348540238315516052150097467097276570510834602692807637444) * 10 ^ 70 +
        5232260313016604823319350313603727632909712806064231449670192648965551) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 301 = 71 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 16 +
      150 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_300_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (301 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 151,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (301 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_301 :
    recurrence2Scalar2Shift.coeff 301 =
      -(((308984761107351702072276557666125552507509314238114 * 10 ^ 70 +
        4116765914874078873554423309210855917217928884197955090750262315410804) * 10 ^ 70 +
        6286924977909789077253883868188357249894585107116947696072410579277033) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 302 = 72 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 15 +
      151 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_301_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 152,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (302 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_302 :
    recurrence2Scalar2Shift.coeff 302 =
      (((56531109356958453874531121119323598325459748983966 * 10 ^ 70 +
        8316472959906479442332476946656867109838124538321817707018742359918171) * 10 ^ 70 +
        8066406139219832808766293792405957181339400972135857184254937033046232) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 303 = 73 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 14 +
      152 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_302_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 153,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (303 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_303 :
    recurrence2Scalar2Shift.coeff 303 =
      -(((7544756191348171920929456221251964924730286781909 * 10 ^ 70 +
        2950150716553270286444822890883120730390972250145605857636141913576026) * 10 ^ 70 +
        3761886901368318984426454369039493321209082760776297243279346635278212) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 304 = 74 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 13 +
      153 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_303_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 154,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (304 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_304 :
    recurrence2Scalar2Shift.coeff 304 =
      (((387380667874796710521320457194671748300738857128 * 10 ^ 70 +
        2091634420008123802251864738993649379815316313453366437042376799201194) * 10 ^ 70 +
        1822011167082817003517582399480634266011359199921605843608580857904590) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 305 = 75 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 12 +
      154 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_304_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 155,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (305 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_305 :
    recurrence2Scalar2Shift.coeff 305 =
      (((159555135070741614655828881815535224123031875525 * 10 ^ 70 +
        7696059041571811926278595588189926128671543300947072995211029734439181) * 10 ^ 70 +
        7905495944488155896172107018974622542850413770905800237087762732192572) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 306 = 76 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 11 +
      155 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_305_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 156,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (306 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_306 :
    recurrence2Scalar2Shift.coeff 306 =
      -(((68702290666267382153232313904396274235866057601 * 10 ^ 70 +
        7021140785149825760817480430482859031168684309635685736921926252159169) * 10 ^ 70 +
        4848297443980890621990537762309732557924477542347210991540872468508720) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 307 = 77 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 10 +
      156 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_306_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (307 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 157,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (307 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_307 :
    recurrence2Scalar2Shift.coeff 307 =
      (((17149049075139393637146495841863569550378830320 * 10 ^ 70 +
        8381573722891833794045170378086597133351963052872924577183260376740194) * 10 ^ 70 +
        1741860589025847166479227923510907594436020581532827830274090940532810) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 308 = 78 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 9 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_307_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (308 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 158,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (308 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_308 :
    recurrence2Scalar2Shift.coeff 308 =
      -(((3245525526901188806512110997853544485644439413 * 10 ^ 70 +
        4998573619693989138344167545311364965022665241411066202539368622520535) * 10 ^ 70 +
        2832328357876301809005604769582749081945054335880280335554115066219173) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 309 = 79 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 8 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_308_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 159,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (309 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_309 :
    recurrence2Scalar2Shift.coeff 309 =
      (((481706024861809648528995913492470820104661990 * 10 ^ 70 +
        3773368187555274450903869050959203632605621251334527213901957045699693) * 10 ^ 70 +
        2650124013820675682282245062483239812558895509008327559077095170935481) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 310 = 80 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 7 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_309_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 160,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (310 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_310 :
    recurrence2Scalar2Shift.coeff 310 =
      -(((52059813765743852628365948970171631776348343 * 10 ^ 70 +
        8075348634891490799636986600321135991795557176058475034457172701031885) * 10 ^ 70 +
        4440823655813582594160177442275468745900523042764435677946777107596216) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 311 = 81 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 6 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_310_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 161,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (311 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_311 :
    recurrence2Scalar2Shift.coeff 311 =
      (((2433207032017117137571786631794502380034617 * 10 ^ 70 +
        3869829144524447137340178968027442130190556215130319814787030031442878) * 10 ^ 70 +
        0043494300965351079630564850098837114008184795338554355608573951235453) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 312 = 82 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 5 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_311_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 162,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (312 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_312 :
    recurrence2Scalar2Shift.coeff 312 =
      (((552253338483753230971940742182184109041044 * 10 ^ 70 +
        3260808331657794729910267747726535815334164664376155713289587852950759) * 10 ^ 70 +
        2408397929585044503289071487417892937877889719148890009603437478841343) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 313 = 83 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 4 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_312_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 163,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (313 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_313 :
    recurrence2Scalar2Shift.coeff 313 =
      -(((191316924085719770471773105292836587814895 * 10 ^ 70 +
        1477233637540735107050300345649276905851981780528575088819279363768364) * 10 ^ 70 +
        0508705477146453816208226159760507833056750526781210734579008145894063) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 314 = 84 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 3 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_313_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 164,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (314 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_314 :
    recurrence2Scalar2Shift.coeff 314 =
      (((35372006347470969764424346186130586463586 * 10 ^ 70 +
        5416904328157552745139622371491243713784456981892242337285504433663775) * 10 ^ 70 +
        1120236855636385185805699096343770516649227268866085753782295968706641) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 315 = 85 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 2 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_314_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 165,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (315 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_315 :
    recurrence2Scalar2Shift.coeff 315 =
      -(((4687691783439434701264128590790780063500 * 10 ^ 70 +
        9513347855353960634825700068642905487390277675974391053623717153125173) * 10 ^ 70 +
        2385079246905586379418379645470994455551345544634949218320864419220375) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 316 = 86 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 1 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_315_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 166,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (316 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_316 :
    recurrence2Scalar2Shift.coeff 316 =
      (((439117346704483048115107244616843087021 * 10 ^ 70 +
        6167517558429231058159161927920357276447022068307547887428612442376850) * 10 ^ 70 +
        2591159178637809445571734918006943021373079441727803506797780367074763) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 317 = 87 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_316_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 167,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (317 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_317 :
    recurrence2Scalar2Shift.coeff 317 =
      -(((19682267087557350951279478090097942619 * 10 ^ 70 +
        9871152599794562337929624641592131467187783304486405449285797886162589) * 10 ^ 70 +
        3231958577541271222722875638303472788405219405432377988921778330144310) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 318 = 88 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 31 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_317_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 168,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (318 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_318 :
    recurrence2Scalar2Shift.coeff 318 =
      -(((2326210158239207663862690204725938040 * 10 ^ 70 +
        4898021237607022641794877533501001037849913017045592572730756641615882) * 10 ^ 70 +
        5524020885552983886641519386894244152008938453465199318498592570884982) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 319 = 89 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 30 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_318_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 169,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (319 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_319 :
    recurrence2Scalar2Shift.coeff 319 =
      (((702446444250908903225852632599603971 * 10 ^ 70 +
        3066908883895583051335865780549200622888620749158934321241640980960129) * 10 ^ 70 +
        5848574213447606071242001156368288630806221842676956076933277660610049) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 320 = 90 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 29 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_319_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 170,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (320 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_320 :
    recurrence2Scalar2Shift.coeff 320 =
      -(((99422209210133751821668422989127460 * 10 ^ 70 +
        1623978028687040045440283649118293809320862258881599861701205535142471) * 10 ^ 70 +
        8018120980144001408239338497868998714200841593965782327833309675058434) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 321 = 91 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 28 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_320_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 171,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (321 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_321 :
    recurrence2Scalar2Shift.coeff 321 =
      (((9374327130842815664345925489198151 * 10 ^ 70 +
        0407008103649330820304402064511619409455115853103170718915619842612087) * 10 ^ 70 +
        9639215219911845930661543516728279322599738696872529447828994037285196) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 322 = 92 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 27 +
      171 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_321_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 172,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (322 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_322 :
    recurrence2Scalar2Shift.coeff 322 =
      -(((527770931051918216721934122690443 * 10 ^ 70 +
        6495069927212679012062925000509861669815221490611524410584122552301705) * 10 ^ 70 +
        7016139721406402658493316151853278548911400976725023317405993083828085) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 323 = 93 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 26 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_322_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 173,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (323 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_323 :
    recurrence2Scalar2Shift.coeff 323 =
      -(((4831186900238517649925686875102 * 10 ^ 70 +
        9719272068437578285670068465336807538863770375022658741930829441182007) * 10 ^ 70 +
        0475114684321079618524459650551711748682227850003698371766914645058800) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 324 = 94 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 25 +
      173 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_323_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 174,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (324 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_324 :
    recurrence2Scalar2Shift.coeff 324 =
      (((5179095443412610486433425237779 * 10 ^ 70 +
        0991892921105293519106374072918471717489675623588866485722462927158611) * 10 ^ 70 +
        0856303977639058272880287090635799183008449368724831800344771826533351) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 325 = 95 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 24 +
      174 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_324_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (325 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 175,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (325 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_325 :
    recurrence2Scalar2Shift.coeff 325 =
      -(((688560609863678863819723030329 * 10 ^ 70 +
        3686336797237342458385215730784315529602885874358881629107950201257175) * 10 ^ 70 +
        4280948168775818928906125876346804668257904500563115395159863796415462) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 326 = 96 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 23 +
      175 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_325_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (326 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 176,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (326 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_326 :
    recurrence2Scalar2Shift.coeff 326 =
      (((55489993721153613290326674223 * 10 ^ 70 +
        8077194139110870451974413625050627124778409865526352229241924864070761) * 10 ^ 70 +
        0462792593391765566135041558536878666824191596842946944325027311463981) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 327 = 97 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 22 +
      176 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_326_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (327 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 177,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (327 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_327 :
    recurrence2Scalar2Shift.coeff 327 =
      -(((2696997217982737922739758747 * 10 ^ 70 +
        8206548868280415927991922120391839994232261176709073145202668553286301) * 10 ^ 70 +
        9032007640423395782943053326948057001901645373661510091608869691330845) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 328 = 98 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 21 +
      177 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_327_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (328 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 178,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (328 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_328 :
    recurrence2Scalar2Shift.coeff 328 =
      (((16539826368328404698973650 * 10 ^ 70 +
        7219012765741742283664578363035362823096872311543550226230865339631628) * 10 ^ 70 +
        9931381535146830633680470375131260819857996519710383218793319990688477) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 329 = 99 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 20 +
      178 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_328_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (329 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 179,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (329 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_329 :
    recurrence2Scalar2Shift.coeff 329 =
      (((10608904176994182022051160 * 10 ^ 70 +
        5238515893417758346514938210014703947282117087829664143350191683763678) * 10 ^ 70 +
        2687452371452695322686209784714743067553647912074321433472031675314138) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 330 = 100 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 19 +
      179 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_329_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (330 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 180,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (330 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_330 :
    recurrence2Scalar2Shift.coeff 330 =
      -(((1098230217067524219234117 * 10 ^ 70 +
        0832701535493644889222215137815601612248618322536932546639530050085237) * 10 ^ 70 +
        0239014009338948994443425650834983578248185630089096610225628342794058) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 331 = 101 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 18 +
      180 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_330_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (331 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 181,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (331 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_331 :
    recurrence2Scalar2Shift.coeff 331 =
      (((61730037861214972356897 * 10 ^ 70 +
        7670779974175721622072331451350063519577108811745434266232993580206194) * 10 ^ 70 +
        1462151228522504023351144277142548269113391514605376760461183566824629) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 332 = 102 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 17 +
      181 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_331_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (332 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 182,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (332 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_332 :
    recurrence2Scalar2Shift.coeff 332 =
      -(((1818859585508881544805 * 10 ^ 70 +
        8114633831259786331837490077521776498892273041456404035792614258144265) * 10 ^ 70 +
        8661011615392757543590286927919225782763658234902355269264931852674278) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 333 = 103 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 16 +
      182 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_332_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (333 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 183,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (333 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_333 :
    recurrence2Scalar2Shift.coeff 333 =
      -(((18007146556516504884 * 10 ^ 70 +
        5297807813097462985415101148662278407820299047768087384910925825251240) * 10 ^ 70 +
        2528673481278790046667032504264084112574486670494498984814824045273328) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 334 = 104 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 15 +
      183 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_333_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (334 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 184,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (334 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_334 :
    recurrence2Scalar2Shift.coeff 334 =
      (((4924469564155364067 * 10 ^ 70 +
        2774412947658833058114994007229914366427414041458956291634043707569307) * 10 ^ 70 +
        4839273396835234514608801128432044262450424747170712236489823984326647) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 335 = 105 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 14 +
      184 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_334_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (335 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 185,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (335 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_335 :
    recurrence2Scalar2Shift.coeff 335 =
      -(((258701784841772862 * 10 ^ 70 +
        2801413076615569301493041318135533229774468441909551069072413500878601) * 10 ^ 70 +
        7857917252830296382607908205666493480165915970858196558108927835234134) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 336 = 106 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 13 +
      185 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_335_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (336 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 186,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (336 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_336 :
    recurrence2Scalar2Shift.coeff 336 =
      (((6553731471795901 * 10 ^ 70 +
        7488093568946334491625027899028998469182070668326607201797126154378401) * 10 ^ 70 +
        6504905033126892418163682176215273690079010766514651285875351312160569) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 337 = 107 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 12 +
      186 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_336_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (337 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 187,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (337 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_337 :
    recurrence2Scalar2Shift.coeff 337 =
      -(((4661966371210 * 10 ^ 70 +
        6358311362669926762088481247006399561379513501003755830676065553411314) * 10 ^ 70 +
        2915043026508386236816455701008223170500617146435178524940180894998275) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 338 = 108 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 11 +
      187 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_337_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (338 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 188,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (338 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_338 :
    recurrence2Scalar2Shift.coeff 338 =
      -(((5778786031055 * 10 ^ 70 +
        2335687071286094486961663076555375787175330782941148407483544434098996) * 10 ^ 70 +
        5273810871066513466232116400358791003544943950261789762254746642075197) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 339 = 109 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 10 +
      188 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_338_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 110,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (339 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 189,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (339 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_339 :
    recurrence2Scalar2Shift.coeff 339 =
      (((198673512367 * 10 ^ 70 +
        1077689650285588964614482296738935022722479095535754973004835187885711) * 10 ^ 70 +
        2340695314270316521260679222910893419723850404160078216380484809997686) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 340 = 110 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 9 +
      189 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_339_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 111,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (340 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 190,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (340 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_340 :
    recurrence2Scalar2Shift.coeff 340 =
      -(((2426635354 * 10 ^ 70 +
        6563436944277708324132343996993699191321277464239235909718299423927665) * 10 ^ 70 +
        7511489069832839830145747258294401103694370141183421136124051713030155) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 341 = 111 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 8 +
      190 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_340_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (341 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 191,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (341 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_341 :
    recurrence2Scalar2Shift.coeff 341 =
      -(((28389610 * 10 ^ 70 +
        9025214977511055237606527127340279099163680348027987799100490965834281) * 10 ^ 70 +
        7886218089847867488394348304745335789678333043641446062007304485546755) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 342 = 112 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 7 +
      191 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_341_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (342 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 192,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (342 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_342 :
    recurrence2Scalar2Shift.coeff 342 =
      (((1352471 * 10 ^ 70 +
        2332062430782527680433354862627482926733788477785140579386434090659608) * 10 ^ 70 +
        9549872095294541799779993992469157563078973727312082535016960041897461) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 343 = 113 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 6 +
      192 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_342_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (343 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 193,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (343 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_343 :
    recurrence2Scalar2Shift.coeff 343 =
      -(((13977 * 10 ^ 70 +
        4661209390748484090511382268732777924736338734666598222556910888511116) * 10 ^ 70 +
        1796656032332666209674625258871452832042332029130842470335661038336611) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 344 = 114 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 5 +
      193 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_343_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (344 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 194,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (344 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_344 :
    recurrence2Scalar2Shift.coeff 344 =
      -(((83 * 10 ^ 70 +
        3963007973445647394684802868540561777195674272148845292374426526779394) * 10 ^ 70 +
        8589201925685753303004058481637921907619735234748901321452020709701604) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 345 = 115 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 4 +
      194 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_344_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (345 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 195,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (345 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_345 :
    recurrence2Scalar2Shift.coeff 345 =
      (((2 * 10 ^ 70 +
        7658723067520799003264735789928602753875477731574051065293387444972044) * 10 ^ 70 +
        2733102632544597222914205310123416038807758540976419243304376011578891) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 346 = 116 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 3 +
      195 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_345_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (346 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 196,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (346 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_346 :
    recurrence2Scalar2Shift.coeff 346 =
      -((104556923824198389197223672247681097578920536715784198335562232850617 * 10 ^ 70 +
        2733162134986152752944552209251921601480579497558719092785196254136564) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 347 = 117 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 2 +
      196 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_346_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (347 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 197,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (347 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_347 :
    recurrence2Scalar2Shift.coeff 347 =
      -((1773065701499771117282861667572733360367736915290598846513713556738 * 10 ^ 70 +
        6991455763697212834257259083349573116540458797671488071196448767203649) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 348 = 118 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 1 +
      197 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_347_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (348 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 198,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (348 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_348 :
    recurrence2Scalar2Shift.coeff 348 =
      ((13883616697406172259149793168734082563697578679239142889823589802 * 10 ^ 70 +
        8723486323890445625824786090064489184972918477483956899135020551026786) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 349 = 119 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_348_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (349 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 199,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (349 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_349 :
    recurrence2Scalar2Shift.coeff 349 =
      ((48637901797724479647081716574618131718667183019782447289440313 * 10 ^ 70 +
        0609461265111850276425698306553536315036995486831559210584343868978770) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 350 = 120 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 31 +
      199 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_349_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (350 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 200,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (350 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_350 :
    recurrence2Scalar2Shift.coeff 350 =
      -((663587699540309659411128101367960197878841566351339071298078 * 10 ^ 70 +
        5375596872786672431686631619627272107793808787569531471794618341846905) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 351 = 121 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 30 +
      200 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_350_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (351 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 201,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (351 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_351 :
    recurrence2Scalar2Shift.coeff 351 =
      -((295104117160331000655067078740751632594048344301302673594 * 10 ^ 70 +
        6136493055204515830988002993112191670135241962032001192004479014990201) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 352 = 122 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 29 +
      201 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_351_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (352 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 202,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (352 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_352 :
    recurrence2Scalar2Shift.coeff 352 =
      ((16552293616994860898276104118920731878641519155764719737 * 10 ^ 70 +
        9644423227427761642468478653589608620621175246561613005876739952764098) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 353 = 123 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 28 +
      202 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_352_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (353 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 203,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (353 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_353 :
    recurrence2Scalar2Shift.coeff 353 =
      -((16437273075595903160937542975402694738636658071103770 * 10 ^ 70 +
        6856389201279867494525506038263382615913870144405965993124243865151160) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 354 = 124 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 27 +
      203 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_353_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (354 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 204,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (354 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_354 :
    recurrence2Scalar2Shift.coeff 354 =
      -((226556500277038000492229348408799591477301397050391 * 10 ^ 70 +
        6834349952019541430892757367058266973148162025058637122348847514667572) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 355 = 125 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 26 +
      204 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_354_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (355 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 205,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (355 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_355 :
    recurrence2Scalar2Shift.coeff 355 =
      ((461614717978296496022578514876381953460105916696 * 10 ^ 70 +
        3130482444491374148937527488617864345656836046705338922027578620011790) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 356 = 126 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 25 +
      205 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_355_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (356 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 206,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (356 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_356 :
    recurrence2Scalar2Shift.coeff 356 =
      ((1535646552129404526727560724551810138890634433 * 10 ^ 70 +
        8750874175168757165143429344607042162791942661995270779939945695082900) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 357 = 127 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 24 +
      206 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_356_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (357 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 207,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (357 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_357 :
    recurrence2Scalar2Shift.coeff 357 =
      -((5139850723875795629331451755637974084483401 * 10 ^ 70 +
        8352563594444732830265615595930204202766840376329462164246038138631201) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 358 = 128 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 23 +
      207 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_357_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (358 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 208,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (358 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_358 :
    recurrence2Scalar2Shift.coeff 358 =
      -((2313702845568565530415398987431232892493 * 10 ^ 70 +
        7728700059381116685251321798622926388693622892121183168924045086833539) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 359 = 129 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 22 +
      208 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_358_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (359 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 209,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (359 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_359 :
    recurrence2Scalar2Shift.coeff 359 =
      ((24627294337240439637338081448985985812 * 10 ^ 70 +
        1126948231690071024957436647925151387730394745376886905562163062049882) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 360 = 130 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 21 +
      209 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_359_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (360 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 210,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (360 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_360 :
    recurrence2Scalar2Shift.coeff 360 =
      -((23098802881734089736756213522286287 * 10 ^ 70 +
        7289779074218179321893469342500389930167713340689369742885168940296003) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 361 = 131 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 20 +
      210 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_360_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 132,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (361 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 211,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (361 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_361 :
    recurrence2Scalar2Shift.coeff 361 =
      -((27412882424994836981216441344195 * 10 ^ 70 +
        0987391626341116739434822587701329107935238162299255092856851501069094) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 362 = 132 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 19 +
      211 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_361_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 133,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (362 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 212,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (362 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_362 :
    recurrence2Scalar2Shift.coeff 362 =
      ((66381187252545886914105714805 * 10 ^ 70 +
        8839851901313131558780029244944991649076579413174102705124069021886649) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 363 = 133 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 18 +
      212 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_362_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 134,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (363 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 213,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (363 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_363 :
    recurrence2Scalar2Shift.coeff 363 =
      -((42269920347035084466766204 * 10 ^ 70 +
        9505610790435517101310508923741488999289164359805252878270845883747506) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 364 = 134 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 17 +
      213 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_363_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 135,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (364 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 214,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (364 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_364 :
    recurrence2Scalar2Shift.coeff 364 =
      ((1441878404944981873787 * 10 ^ 70 +
        7868839393847877829633575889587564781950971090812093617448482981553356) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 365 = 135 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 16 +
      214 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_364_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 136,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (365 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 215,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (365 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_365 :
    recurrence2Scalar2Shift.coeff 365 =
      ((9378695081447625320 * 10 ^ 70 +
        2080155126996890273893904604449552343087024251166309094594484759471213) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 366 = 136 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 15 +
      215 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_365_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 137,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (366 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 216,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (366 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_366 :
    recurrence2Scalar2Shift.coeff 366 =
      -((3907193356887333 * 10 ^ 70 +
        3836043868019426240340717492647342362803543124882775221109984303318960) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 367 = 137 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 14 +
      216 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_366_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 138,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (367 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 217,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (367 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_367 :
    recurrence2Scalar2Shift.coeff 367 =
      ((561997906271 * 10 ^ 70 +
        5494429701032508268890386466862784877464913594422174070297961782685286) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 368 = 138 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 13 +
      217 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_367_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 139,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (368 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 218,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (368 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_368 :
    recurrence2Scalar2Shift.coeff 368 =
      -((14572594 * 10 ^ 70 +
        3894983591051645115314716535612074173183188716354308215725481462148398) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 369 = 139 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 12 +
      218 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_368_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 140,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (369 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 219,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (369 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_369 :
    recurrence2Scalar2Shift.coeff 369 =
      -((2739 * 10 ^ 70 +
        3570940864937326967300021910482763294962810303007411004902032802076913) : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 370 = 140 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 11 +
      219 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_369_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 141,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (370 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 220,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (370 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_370 :
    recurrence2Scalar2Shift.coeff 370 =
      (1910243966047913114248399737805887557802228692164026247523475754151739 : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 371 = 141 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 10 +
      220 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_370_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 142,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (371 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 221,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (371 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_371 :
    recurrence2Scalar2Shift.coeff 371 =
      (-36917311953252292795537222966523524068792196790010526163665254815 : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 372 = 142 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 9 +
      221 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_371_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 143,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (372 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 222,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (372 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_372 :
    recurrence2Scalar2Shift.coeff 372 =
      (183363243886378695115034101466851023187338729371592055258833 : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 373 = 143 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 8 +
      222 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_372_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 144,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (373 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 223,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (373 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_373 :
    recurrence2Scalar2Shift.coeff 373 =
      (325625577524957324677044466501864311979116908083955817 : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 374 = 144 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 7 +
      223 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_373_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 145,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (374 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 224,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (374 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_374 :
    recurrence2Scalar2Shift.coeff 374 =
      (-2079834844921096051394689788341353856730288452634 : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 375 = 145 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 6 +
      224 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_374_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 146,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (375 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 225,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (375 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_375 :
    recurrence2Scalar2Shift.coeff 375 =
      (1518996951250413818027197278673846063992040 : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 376 = 146 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 5 +
      225 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_375_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_376_prefix_zero :
    (∑ x ∈ Finset.range 147,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (376 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (376 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_376_suffix_zero :
    (∑ x ∈ Finset.range 226,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (376 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_376 :
    recurrence2Scalar2Shift.coeff 376 =
      (-127251674289765160684473866441357158 : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 377 = 147 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 4 +
      226 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_376_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_376_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 148,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (377 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_377_suffix_zero :
    (∑ x ∈ Finset.range 227,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (377 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_377 :
    recurrence2Scalar2Shift.coeff 377 =
      (671580179972517182291550039 : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 378 = 148 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 3 +
      227 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_377_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_377_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_378_prefix_zero :
    (∑ x ∈ Finset.range 149,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (378 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (378 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_378_suffix_zero :
    (∑ x ∈ Finset.range 228,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (378 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_378 :
    recurrence2Scalar2Shift.coeff 378 =
      (981405724590120839 : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 379 = 149 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 2 +
      228 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_378_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_378_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Shift_coeff_379_prefix_zero :
    (∑ x ∈ Finset.range 150,
      remainder3Coefficient1.coeff x * recurrence2B5A6.coeff (379 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (379 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Shift_coeff_379_suffix_zero :
    (∑ x ∈ Finset.range 229,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2B5A6.coeff (379 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Shift_coeff_379 :
    recurrence2Scalar2Shift.coeff 379 =
      (-656766259 : ℚ) := by
  unfold recurrence2Scalar2Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 380 = 150 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 1 +
      229 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Shift_coeff_379_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Shift_coeff_379_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

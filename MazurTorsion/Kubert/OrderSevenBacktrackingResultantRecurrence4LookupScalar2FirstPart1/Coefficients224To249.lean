/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3A4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2FirstPart1Simp
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
  recurrence4B1_coeff_171
  recurrence4B1_coeff_172
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

attribute [local simp]
  recurrence4B1_coeff_6
  recurrence4B1_coeff_60
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

attribute [local simp]
  recurrence4B3A4_coeff_116
  recurrence4B3A4_coeff_117
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
  recurrence4B3A4_coeff_170
  recurrence4B3A4_coeff_171
  recurrence4B3A4_coeff_172
  recurrence4B3A4_coeff_173

attribute [local simp]
  recurrence4B3A4_coeff_174
  recurrence4B3A4_coeff_175
  recurrence4B3A4_coeff_176
  recurrence4B3A4_coeff_177
  recurrence4B3A4_coeff_178
  recurrence4B3A4_coeff_179
  recurrence4B3A4_coeff_18
  recurrence4B3A4_coeff_180
  recurrence4B3A4_coeff_181
  recurrence4B3A4_coeff_182
  recurrence4B3A4_coeff_183
  recurrence4B3A4_coeff_184
  recurrence4B3A4_coeff_185
  recurrence4B3A4_coeff_186
  recurrence4B3A4_coeff_187
  recurrence4B3A4_coeff_188
  recurrence4B3A4_coeff_189
  recurrence4B3A4_coeff_19
  recurrence4B3A4_coeff_190
  recurrence4B3A4_coeff_191
  recurrence4B3A4_coeff_192
  recurrence4B3A4_coeff_193
  recurrence4B3A4_coeff_194
  recurrence4B3A4_coeff_195
  recurrence4B3A4_coeff_196
  recurrence4B3A4_coeff_197
  recurrence4B3A4_coeff_198
  recurrence4B3A4_coeff_199
  recurrence4B3A4_coeff_2
  recurrence4B3A4_coeff_20
  recurrence4B3A4_coeff_200
  recurrence4B3A4_coeff_201
  recurrence4B3A4_coeff_202
  recurrence4B3A4_coeff_203
  recurrence4B3A4_coeff_204
  recurrence4B3A4_coeff_205
  recurrence4B3A4_coeff_206
  recurrence4B3A4_coeff_207
  recurrence4B3A4_coeff_208
  recurrence4B3A4_coeff_209
  recurrence4B3A4_coeff_21
  recurrence4B3A4_coeff_210
  recurrence4B3A4_coeff_211
  recurrence4B3A4_coeff_212
  recurrence4B3A4_coeff_213
  recurrence4B3A4_coeff_214
  recurrence4B3A4_coeff_215
  recurrence4B3A4_coeff_216
  recurrence4B3A4_coeff_217
  recurrence4B3A4_coeff_218
  recurrence4B3A4_coeff_219
  recurrence4B3A4_coeff_22
  recurrence4B3A4_coeff_220
  recurrence4B3A4_coeff_221
  recurrence4B3A4_coeff_222
  recurrence4B3A4_coeff_223
  recurrence4B3A4_coeff_224
  recurrence4B3A4_coeff_225
  recurrence4B3A4_coeff_226
  recurrence4B3A4_coeff_227
  recurrence4B3A4_coeff_228
  recurrence4B3A4_coeff_229
  recurrence4B3A4_coeff_23
  recurrence4B3A4_coeff_230

attribute [local simp]
  recurrence4B3A4_coeff_231
  recurrence4B3A4_coeff_232
  recurrence4B3A4_coeff_233
  recurrence4B3A4_coeff_234
  recurrence4B3A4_coeff_235
  recurrence4B3A4_coeff_236
  recurrence4B3A4_coeff_237
  recurrence4B3A4_coeff_238
  recurrence4B3A4_coeff_239
  recurrence4B3A4_coeff_24
  recurrence4B3A4_coeff_240
  recurrence4B3A4_coeff_241
  recurrence4B3A4_coeff_242
  recurrence4B3A4_coeff_243
  recurrence4B3A4_coeff_244
  recurrence4B3A4_coeff_245
  recurrence4B3A4_coeff_246
  recurrence4B3A4_coeff_247
  recurrence4B3A4_coeff_248
  recurrence4B3A4_coeff_249
  recurrence4B3A4_coeff_25
  recurrence4B3A4_coeff_250
  recurrence4B3A4_coeff_251
  recurrence4B3A4_coeff_252
  recurrence4B3A4_coeff_253
  recurrence4B3A4_coeff_254
  recurrence4B3A4_coeff_255
  recurrence4B3A4_coeff_256
  recurrence4B3A4_coeff_257
  recurrence4B3A4_coeff_258
  recurrence4B3A4_coeff_259
  recurrence4B3A4_coeff_26
  recurrence4B3A4_coeff_260
  recurrence4B3A4_coeff_261
  recurrence4B3A4_coeff_262
  recurrence4B3A4_coeff_263
  recurrence4B3A4_coeff_264
  recurrence4B3A4_coeff_265
  recurrence4B3A4_coeff_266
  recurrence4B3A4_coeff_267
  recurrence4B3A4_coeff_268
  recurrence4B3A4_coeff_269
  recurrence4B3A4_coeff_27
  recurrence4B3A4_coeff_270
  recurrence4B3A4_coeff_271
  recurrence4B3A4_coeff_272
  recurrence4B3A4_coeff_273
  recurrence4B3A4_coeff_274
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

attribute [local simp]
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

private theorem recurrence4Scalar2First_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (224 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (224 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_224 :
    recurrence4Scalar2First.coeff 224 =
      (((((29779670545848756549524873 * 10 ^ 70 +
        9486535928457399151725290212775034765462419143820543724222144791963051) * 10 ^ 70 +
        4170898506202786533018580513862731413649669269367376241870295125228831) * 10 ^ 70 +
        1489115152082784709983547529763785766571781742549681073050235161302075) * 10 ^ 70 +
        1029783705751015677914777242033256333193289452041714641409290220801050) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 225,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (224 - x)) = _
  rw [show 225 = 1 +
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
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 12 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_224_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_224_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (225 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (225 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_225 :
    recurrence4Scalar2First.coeff 225 =
      -(((((42713566116555600745441056 * 10 ^ 70 +
        1046522700109605050784673291534885199144021204113206389808786659921210) * 10 ^ 70 +
        5640007263592535623274143804653257058466763855007617468658189688708742) * 10 ^ 70 +
        6885688744386906446875987123457454785773003181530734453521861799042741) * 10 ^ 70 +
        6467805654117793798577947442346322698222872879947255760220025236567085) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 226,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (225 - x)) = _
  rw [show 226 = 1 +
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
    rw [show 97 = 32 +
      65 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 65 = 12 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_225_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_225_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (226 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (226 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_226 :
    recurrence4Scalar2First.coeff 226 =
      (((((60395488201633375156740613 * 10 ^ 70 +
        3735595892424475782493236241017265447211859258675294433756779704129879) * 10 ^ 70 +
        3680268390022895102079025259422305952059935005183282539117697119352543) * 10 ^ 70 +
        1769878827907047829768001978671989100092631340233744869141685680430427) * 10 ^ 70 +
        4215694173777142610635380789397233316144529750511434634622024222897517) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 227,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (226 - x)) = _
  rw [show 227 = 1 +
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
    rw [show 98 = 32 +
      66 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 66 = 12 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_226_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_226_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (227 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (227 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_227 :
    recurrence4Scalar2First.coeff 227 =
      -(((((84181027840910637881844599 * 10 ^ 70 +
        1292775877765901764679433570745485508430717599890776973473820086482019) * 10 ^ 70 +
        0842122537701048485077871075333396139479920465006703730824498397510515) * 10 ^ 70 +
        1692802234765999634183810139010032935909855289643645795913922013819727) * 10 ^ 70 +
        6385595733882945278461198911891679995148708525969492900526052405952176) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 228,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (227 - x)) = _
  rw [show 228 = 1 +
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
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 12 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_227_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_227_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (228 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (228 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_228 :
    recurrence4Scalar2First.coeff 228 =
      (((((115656712166275357445617125 * 10 ^ 70 +
        9279293702105091934189425617051165719756692560276845103921320896324876) * 10 ^ 70 +
        8674868344330368978416645763617355075705823076578605293431740024963506) * 10 ^ 70 +
        6611898140365364250895713977346796466488104793893510195542642982973378) * 10 ^ 70 +
        7180055105924045521843757598045594788085315702888303912977581153271968) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 229,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (228 - x)) = _
  rw [show 229 = 1 +
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
    rw [show 100 = 32 +
      68 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 68 = 12 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_228_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_228_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (229 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (229 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_229 :
    recurrence4Scalar2First.coeff 229 =
      -(((((156620062915992876864164357 * 10 ^ 70 +
        5321527077818792035419211472803600337106511835498971566979021759002202) * 10 ^ 70 +
        4650548587008875730323975620815924879592018118747403194146266725877976) * 10 ^ 70 +
        9371682164144374349654875988062685912842372738346027947118097989222520) * 10 ^ 70 +
        4336625168926428732226541785198550218503852718865305252962777540881986) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 230,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (229 - x)) = _
  rw [show 230 = 1 +
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
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 12 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_229_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_229_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (230 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (230 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_230 :
    recurrence4Scalar2First.coeff 230 =
      (((((209032507385703260322899197 * 10 ^ 70 +
        5916513711022549577124911040072186420261449789395386440959441936004657) * 10 ^ 70 +
        0838403014519629064505536947793843744480865758266640502522432536791058) * 10 ^ 70 +
        4296623705257329838895477621667644646743899027403427892044174181581387) * 10 ^ 70 +
        2222223605468285977744022951368062695838207013677482071603537361168784) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 231,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (230 - x)) = _
  rw [show 231 = 1 +
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
    rw [show 102 = 32 +
      70 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 70 = 12 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_230_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_230_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (231 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (231 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_231 :
    recurrence4Scalar2First.coeff 231 =
      -(((((274939187987268097577134605 * 10 ^ 70 +
        9061339435967021827220790679095649267890297447073554826005610425807726) * 10 ^ 70 +
        3932932053934581244281892419622031641850173178700489508114775641020034) * 10 ^ 70 +
        4245632599680862341141996702604989600879951054392603865304437487193797) * 10 ^ 70 +
        6629755427427240379078162812537242863653210171823092816503513312138042) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 232,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (231 - x)) = _
  rw [show 232 = 1 +
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
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 12 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_231_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_231_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (232 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (232 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_232 :
    recurrence4Scalar2First.coeff 232 =
      (((((356351391428846571829383708 * 10 ^ 70 +
        0085247423630771696833899162458628839871168427675876620635224224226539) * 10 ^ 70 +
        1561967019486428274141328685992701069950953176155405690705348149760432) * 10 ^ 70 +
        7296533166116420102612496459114078393108121734050246798812961949923220) * 10 ^ 70 +
        5306107546022854578748523474934766451464328062073482511548839391207663) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 233,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (232 - x)) = _
  rw [show 233 = 1 +
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
    rw [show 104 = 32 +
      72 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 72 = 12 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_232_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_232_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (233 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (233 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_233 :
    recurrence4Scalar2First.coeff 233 =
      -(((((455090230018128916212706796 * 10 ^ 70 +
        0314141608666961469059860691149883176546452698873373257761902807295970) * 10 ^ 70 +
        7723752128589139813165736419718253568226276913087270142996196637103167) * 10 ^ 70 +
        5241280874817025428507595812284099242899192835430316541694889973469064) * 10 ^ 70 +
        9168139025941792450243129440868527721952417202032401078771566393524995) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 234,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (233 - x)) = _
  rw [show 234 = 1 +
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
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 12 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_233_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_233_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (234 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (234 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_234 :
    recurrence4Scalar2First.coeff 234 =
      (((((572594382231456766588969514 * 10 ^ 70 +
        0153753253937416025121508919709331280352736449852724614339935537645982) * 10 ^ 70 +
        5846909286734347429684561628061130274713286773341459625961693040363618) * 10 ^ 70 +
        3498082931675780704991821435456457072761061314821776682471962469092227) * 10 ^ 70 +
        5851327525824927911358804416629806453746541574159644410947681423807514) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 235,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (234 - x)) = _
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
    rw [show 106 = 32 +
      74 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 74 = 12 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_234_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (235 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (235 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_235 :
    recurrence4Scalar2First.coeff 235 =
      -(((((709699962731139355198373666 * 10 ^ 70 +
        3125479108718790874114030031047846870252873966567107136749143843150482) * 10 ^ 70 +
        4522281264799554815110567238616591364308744010617496855862416901229606) * 10 ^ 70 +
        8918726703654774469275759468376460926515505577437349397164135070429436) * 10 ^ 70 +
        8393179719531458334590496912406775610124298029897133783299491081209777) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 236,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (235 - x)) = _
  rw [show 236 = 1 +
    235 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 235 = 32 +
      203 by norm_num, Finset.sum_range_add]
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
    rw [show 75 = 12 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_235_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (236 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (236 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_236 :
    recurrence4Scalar2First.coeff 236 =
      (((((866406525944924555177135901 * 10 ^ 70 +
        0412639311150970936021038688798939601847369786457296156649369616939379) * 10 ^ 70 +
        6002431172609203683838262832547185222585862600940829587672783454932633) * 10 ^ 70 +
        4282027949688132492789259180287085741927433503649544956977608519174159) * 10 ^ 70 +
        8124335865867481971379243482321942459176868909261296141741204424255720) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 237,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (236 - x)) = _
  rw [show 237 = 1 +
    236 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 236 = 32 +
      204 by norm_num, Finset.sum_range_add]
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
    rw [show 76 = 12 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_236_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (237 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (237 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_237 :
    recurrence4Scalar2First.coeff 237 =
      -(((((1041649143216617533601874208 * 10 ^ 70 +
        7702958943315884287647323199190574121420343005926607217551991906654606) * 10 ^ 70 +
        4753889387699237932822395356894064638916161359587641618796736897046587) * 10 ^ 70 +
        2168176497689440870349083583570931323067287334197690414681588026422119) * 10 ^ 70 +
        2516851428031015191179549494000261042837981263280770096099805048105504) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 238,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (237 - x)) = _
  rw [show 238 = 1 +
    237 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 237 = 32 +
      205 by norm_num, Finset.sum_range_add]
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
    rw [show 77 = 12 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_237_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (238 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (238 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_238 :
    recurrence4Scalar2First.coeff 238 =
      (((((1233101548437668503738407164 * 10 ^ 70 +
        0856595564905061631232750733481286768256665407617723266291194918838372) * 10 ^ 70 +
        1121227197340350716737908677431862654523488438420316089009492211007661) * 10 ^ 70 +
        0728133156963652650173430135335523483149970777428384862680308766650497) * 10 ^ 70 +
        6459561584405393416707513185303832331622270331986051218033460846932570) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 239,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (238 - x)) = _
  rw [show 239 = 1 +
    238 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 238 = 32 +
      206 by norm_num, Finset.sum_range_add]
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
    rw [show 78 = 12 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_238_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (239 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (239 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_239 :
    recurrence4Scalar2First.coeff 239 =
      -(((((1437038514858019344040235686 * 10 ^ 70 +
        2443545431832096053222024954832593826592657188819315423534063139715782) * 10 ^ 70 +
        2387127192999081692620430469904886828666049066921112988355646868160385) * 10 ^ 70 +
        0164195937017975109896157198041696262637827054105116247129794518846280) * 10 ^ 70 +
        6079356825465060833454105378935727591533697011034444297387716709945275) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 240,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (239 - x)) = _
  rw [show 240 = 1 +
    239 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 239 = 32 +
      207 by norm_num, Finset.sum_range_add]
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
    rw [show 79 = 12 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_239_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (240 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (240 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_240 :
    recurrence4Scalar2First.coeff 240 =
      (((((1648285919412869266047619925 * 10 ^ 70 +
        8713805443643998466536052095015221999252773934643131937816753523651535) * 10 ^ 70 +
        9741606837053493237035167431010627931164822452679014879002036548884933) * 10 ^ 70 +
        8802280797620478109263413309733166338990688107774640232481158201893410) * 10 ^ 70 +
        9318589225896097163301683485302316226540619797204593562297773769528153) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 241,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (240 - x)) = _
  rw [show 241 = 1 +
    240 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 240 = 32 +
      208 by norm_num, Finset.sum_range_add]
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
    rw [show 80 = 12 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_240_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (241 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (241 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_241 :
    recurrence4Scalar2First.coeff 241 =
      -(((((1860283581930751958362105194 * 10 ^ 70 +
        1501750838419572023727319581560023899866562103907698676163086314901273) * 10 ^ 70 +
        9340823512159671842726402647813430474776257299585712780583994340655464) * 10 ^ 70 +
        8863040808419628518586626647158251282717537186366847295002915654005564) * 10 ^ 70 +
        5819890424551424673592897260972314605479459535600179130535805265440776) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 242,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (241 - x)) = _
  rw [show 242 = 1 +
    241 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 241 = 32 +
      209 by norm_num, Finset.sum_range_add]
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
    rw [show 81 = 12 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_241_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (242 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (242 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_242 :
    recurrence4Scalar2First.coeff 242 =
      (((((2065278535487233381859692151 * 10 ^ 70 +
        5017057060762204499562477059454482430148587967483623822045544254620835) * 10 ^ 70 +
        0971689083141721030381805039562302450061876899532193930579599468081752) * 10 ^ 70 +
        6944288861157130265106167190444256946576074839334759937122294335289808) * 10 ^ 70 +
        8629653884386916434986260574806826462319669918206786629260762388375193) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 243,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (242 - x)) = _
  rw [show 243 = 1 +
    242 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 242 = 32 +
      210 by norm_num, Finset.sum_range_add]
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
    rw [show 82 = 12 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_242_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (243 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (243 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_243 :
    recurrence4Scalar2First.coeff 243 =
      -(((((2254655045615650545996717367 * 10 ^ 70 +
        5767094324580463008548474553439456171010702724188247515605433799449411) * 10 ^ 70 +
        4840097494437139345429756051802270117650895882478365720399697084641244) * 10 ^ 70 +
        5757190698876543973195589151899776187255230090544006876109180867906778) * 10 ^ 70 +
        9993431461085122928184461197706367203862845118183595580139614406083991) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 244,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (243 - x)) = _
  rw [show 244 = 1 +
    243 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 243 = 32 +
      211 by norm_num, Finset.sum_range_add]
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
    rw [show 83 = 12 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_243_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (244 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (244 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_244 :
    recurrence4Scalar2First.coeff 244 =
      (((((2419393259382966163679188345 * 10 ^ 70 +
        3532044659263427359434533706998934004071859363393027238846242904769604) * 10 ^ 70 +
        0278706173860328651786494680505487316553604560257272335180162106344637) * 10 ^ 70 +
        1538716237027858293091301935748217978931003883240578876245355911899967) * 10 ^ 70 +
        5968978931808557721284596328250244943102714278768412336149874549960557) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 245,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (244 - x)) = _
  rw [show 245 = 1 +
    244 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 244 = 32 +
      212 by norm_num, Finset.sum_range_add]
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
    rw [show 84 = 12 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_244_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (245 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (245 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_245 :
    recurrence4Scalar2First.coeff 245 =
      -(((((2550632294730470008007678171 * 10 ^ 70 +
        2728500684706056088049090816739060856124848267667403872408079075680108) * 10 ^ 70 +
        6126771487072964214226304224388031108150926048685738364199173075186361) * 10 ^ 70 +
        1973516142456010248201467567299744574356462407357092018831170890966537) * 10 ^ 70 +
        9391099394408064214277270525282210012499798768400885292022624282779870) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 246,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (245 - x)) = _
  rw [show 246 = 1 +
    245 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 245 = 32 +
      213 by norm_num, Finset.sum_range_add]
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
    rw [show 85 = 12 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_245_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (246 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (246 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_246 :
    recurrence4Scalar2First.coeff 246 =
      (((((2640297873689708097729878250 * 10 ^ 70 +
        2802901634950504742474564321658498876239799102674611144302119948406176) * 10 ^ 70 +
        4273998695475590961249909033116573646534889472638838048747141438710297) * 10 ^ 70 +
        0644032437126068223785554018488194348564037565573549231813128152940896) * 10 ^ 70 +
        3412225997576160179636436661462794192746442809031749114615685134124464) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 247,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (246 - x)) = _
  rw [show 247 = 1 +
    246 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 246 = 32 +
      214 by norm_num, Finset.sum_range_add]
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
    rw [show 86 = 12 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_246_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (247 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (247 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_247 :
    recurrence4Scalar2First.coeff 247 =
      -(((((2681741547870752980950100706 * 10 ^ 70 +
        9265158976811070124928729764553514243352657005159872565077381779096428) * 10 ^ 70 +
        9187020581600595217352631738539873953291321832044264019372660185069667) * 10 ^ 70 +
        1167113908864913801811476215999402174316457898509112317843680500541127) * 10 ^ 70 +
        3100757351882069350891506018259773223985665840383612089948425905839320) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 248,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (247 - x)) = _
  rw [show 248 = 1 +
    247 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
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
    rw [show 87 = 12 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_247_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (248 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (248 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_248 :
    recurrence4Scalar2First.coeff 248 =
      (((((2670330399030223936246806548 * 10 ^ 70 +
        5206830888257802689744677207977916387766754915922916379245445573923012) * 10 ^ 70 +
        3652841184800831963242122932264554551350313172996613169885699241316647) * 10 ^ 70 +
        6114908964549017402971133832026769901983657189830004729982515221762519) * 10 ^ 70 +
        4837629758531480092399603147363753917343387313191582187060344603651731) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 249,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (248 - x)) = _
  rw [show 249 = 1 +
    248 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 248 = 32 +
      216 by norm_num, Finset.sum_range_add]
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
    rw [show 88 = 12 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_248_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2First_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B1_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (249 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar2First_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder5Coefficient1.coeff (173 + x) *
        recurrence4B3A4.coeff (249 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B1_coeff_high (173 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2First_coeff_249 :
    recurrence4Scalar2First.coeff 249 =
      -(((((2603924624465504293563147265 * 10 ^ 70 +
        9829421029659085340931753409733351444592887749786916963063713908407196) * 10 ^ 70 +
        9912960673575216087217004003337812241647032386427579341528272767697533) * 10 ^ 70 +
        8045624586772618898696327654746772005497544390175363212255992839325281) * 10 ^ 70 +
        3022871026695349534587627003438372040604073019314033823363271587875906) : ℚ) := by
  unfold recurrence4Scalar2First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 250,
    remainder5Coefficient1.coeff x * recurrence4B3A4.coeff (249 - x)) = _
  rw [show 250 = 1 +
    249 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 249 = 32 +
      217 by norm_num, Finset.sum_range_add]
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
    rw [show 89 = 12 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2First_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2First_coeff_249_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

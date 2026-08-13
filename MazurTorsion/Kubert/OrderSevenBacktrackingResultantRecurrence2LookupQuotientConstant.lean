/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB5A5
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB4A6
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: quotient constant coefficient subtraction

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2B5A5_coeff_0
  recurrence2B5A5_coeff_1
  recurrence2B5A5_coeff_2
  recurrence2B5A5_coeff_3
  recurrence2B5A5_coeff_4
  recurrence2B5A5_coeff_5
  recurrence2B5A5_coeff_6
  recurrence2B5A5_coeff_7
  recurrence2B5A5_coeff_8
  recurrence2B5A5_coeff_9
  recurrence2B5A5_coeff_10
  recurrence2B5A5_coeff_11
  recurrence2B5A5_coeff_12
  recurrence2B5A5_coeff_13
  recurrence2B5A5_coeff_14
  recurrence2B5A5_coeff_15
  recurrence2B5A5_coeff_16
  recurrence2B5A5_coeff_17
  recurrence2B5A5_coeff_18
  recurrence2B5A5_coeff_19
  recurrence2B5A5_coeff_20
  recurrence2B5A5_coeff_21
  recurrence2B5A5_coeff_22
  recurrence2B5A5_coeff_23
  recurrence2B5A5_coeff_24
  recurrence2B5A5_coeff_25
  recurrence2B5A5_coeff_26
  recurrence2B5A5_coeff_27
  recurrence2B5A5_coeff_28
  recurrence2B5A5_coeff_29
  recurrence2B5A5_coeff_30
  recurrence2B5A5_coeff_31
  recurrence2B5A5_coeff_32
  recurrence2B5A5_coeff_33
  recurrence2B5A5_coeff_34
  recurrence2B5A5_coeff_35
  recurrence2B5A5_coeff_36
  recurrence2B5A5_coeff_37
  recurrence2B5A5_coeff_38
  recurrence2B5A5_coeff_39
  recurrence2B5A5_coeff_40
  recurrence2B5A5_coeff_41
  recurrence2B5A5_coeff_42
  recurrence2B5A5_coeff_43
  recurrence2B5A5_coeff_44
  recurrence2B5A5_coeff_45
  recurrence2B5A5_coeff_46
  recurrence2B5A5_coeff_47
  recurrence2B5A5_coeff_48
  recurrence2B5A5_coeff_49
  recurrence2B5A5_coeff_50
  recurrence2B5A5_coeff_51
  recurrence2B5A5_coeff_52
  recurrence2B5A5_coeff_53
  recurrence2B5A5_coeff_54
  recurrence2B5A5_coeff_55
  recurrence2B5A5_coeff_56
  recurrence2B5A5_coeff_57
  recurrence2B5A5_coeff_58
  recurrence2B5A5_coeff_59
  recurrence2B5A5_coeff_60
  recurrence2B5A5_coeff_61
  recurrence2B5A5_coeff_62
  recurrence2B5A5_coeff_63
  recurrence2B5A5_coeff_64
  recurrence2B5A5_coeff_65
  recurrence2B5A5_coeff_66
  recurrence2B5A5_coeff_67
  recurrence2B5A5_coeff_68
  recurrence2B5A5_coeff_69
  recurrence2B5A5_coeff_70
  recurrence2B5A5_coeff_71
  recurrence2B5A5_coeff_72
  recurrence2B5A5_coeff_73
  recurrence2B5A5_coeff_74
  recurrence2B5A5_coeff_75
  recurrence2B5A5_coeff_76
  recurrence2B5A5_coeff_77
  recurrence2B5A5_coeff_78
  recurrence2B5A5_coeff_79
  recurrence2B5A5_coeff_80
  recurrence2B5A5_coeff_81
  recurrence2B5A5_coeff_82
  recurrence2B5A5_coeff_83
  recurrence2B5A5_coeff_84
  recurrence2B5A5_coeff_85
  recurrence2B5A5_coeff_86
  recurrence2B5A5_coeff_87
  recurrence2B5A5_coeff_88
  recurrence2B5A5_coeff_89
  recurrence2B5A5_coeff_90
  recurrence2B5A5_coeff_91
  recurrence2B5A5_coeff_92
  recurrence2B5A5_coeff_93
  recurrence2B5A5_coeff_94
  recurrence2B5A5_coeff_95
  recurrence2B5A5_coeff_96
  recurrence2B5A5_coeff_97
  recurrence2B5A5_coeff_98
  recurrence2B5A5_coeff_99
  recurrence2B5A5_coeff_100
  recurrence2B5A5_coeff_101
  recurrence2B5A5_coeff_102
  recurrence2B5A5_coeff_103
  recurrence2B5A5_coeff_104
  recurrence2B5A5_coeff_105
  recurrence2B5A5_coeff_106
  recurrence2B5A5_coeff_107
  recurrence2B5A5_coeff_108
  recurrence2B5A5_coeff_109
  recurrence2B5A5_coeff_110
  recurrence2B5A5_coeff_111
  recurrence2B5A5_coeff_112
  recurrence2B5A5_coeff_113
  recurrence2B5A5_coeff_114
  recurrence2B5A5_coeff_115
  recurrence2B5A5_coeff_116
  recurrence2B5A5_coeff_117
  recurrence2B5A5_coeff_118
  recurrence2B5A5_coeff_119
  recurrence2B5A5_coeff_120
  recurrence2B5A5_coeff_121
  recurrence2B5A5_coeff_122
  recurrence2B5A5_coeff_123
  recurrence2B5A5_coeff_124
  recurrence2B5A5_coeff_125
  recurrence2B5A5_coeff_126
  recurrence2B5A5_coeff_127
  recurrence2B5A5_coeff_128
  recurrence2B5A5_coeff_129
  recurrence2B5A5_coeff_130
  recurrence2B5A5_coeff_131
  recurrence2B5A5_coeff_132
  recurrence2B5A5_coeff_133
  recurrence2B5A5_coeff_134
  recurrence2B5A5_coeff_135
  recurrence2B5A5_coeff_136
  recurrence2B5A5_coeff_137
  recurrence2B5A5_coeff_138
  recurrence2B5A5_coeff_139
  recurrence2B5A5_coeff_140
  recurrence2B5A5_coeff_141
  recurrence2B5A5_coeff_142
  recurrence2B5A5_coeff_143
  recurrence2B5A5_coeff_144
  recurrence2B5A5_coeff_145
  recurrence2B5A5_coeff_146
  recurrence2B5A5_coeff_147
  recurrence2B5A5_coeff_148
  recurrence2B5A5_coeff_149
  recurrence2B5A5_coeff_150
  recurrence2B5A5_coeff_151
  recurrence2B5A5_coeff_152
  recurrence2B5A5_coeff_153
  recurrence2B5A5_coeff_154
  recurrence2B5A5_coeff_155
  recurrence2B5A5_coeff_156
  recurrence2B5A5_coeff_157
  recurrence2B5A5_coeff_158
  recurrence2B5A5_coeff_159
  recurrence2B5A5_coeff_160
  recurrence2B5A5_coeff_161
  recurrence2B5A5_coeff_162
  recurrence2B5A5_coeff_163
  recurrence2B5A5_coeff_164
  recurrence2B5A5_coeff_165
  recurrence2B5A5_coeff_166
  recurrence2B5A5_coeff_167
  recurrence2B5A5_coeff_168
  recurrence2B5A5_coeff_169
  recurrence2B5A5_coeff_170
  recurrence2B5A5_coeff_171
  recurrence2B5A5_coeff_172
  recurrence2B5A5_coeff_173
  recurrence2B5A5_coeff_174
  recurrence2B5A5_coeff_175
  recurrence2B5A5_coeff_176
  recurrence2B5A5_coeff_177
  recurrence2B5A5_coeff_178
  recurrence2B5A5_coeff_179
  recurrence2B5A5_coeff_180
  recurrence2B5A5_coeff_181
  recurrence2B5A5_coeff_182
  recurrence2B5A5_coeff_183
  recurrence2B5A5_coeff_184
  recurrence2B5A5_coeff_185
  recurrence2B5A5_coeff_186
  recurrence2B5A5_coeff_187
  recurrence2B5A5_coeff_188
  recurrence2B5A5_coeff_189
  recurrence2B5A5_coeff_190
  recurrence2B5A5_coeff_191
  recurrence2B5A5_coeff_192
  recurrence2B5A5_coeff_193
  recurrence2B5A5_coeff_194
  recurrence2B5A5_coeff_195
  recurrence2B5A5_coeff_196
  recurrence2B5A5_coeff_197
  recurrence2B5A5_coeff_198
  recurrence2B5A5_coeff_199
  recurrence2B5A5_coeff_200
  recurrence2B5A5_coeff_201
  recurrence2B5A5_coeff_202
  recurrence2B5A5_coeff_203
  recurrence2B5A5_coeff_204
  recurrence2B5A5_coeff_205
  recurrence2B5A5_coeff_206
  recurrence2B5A5_coeff_207
  recurrence2B5A5_coeff_208
  recurrence2B5A5_coeff_209
  recurrence2B5A5_coeff_210
  recurrence2B5A5_coeff_211
  recurrence2B5A5_coeff_212
  recurrence2B5A5_coeff_213
  recurrence2B5A5_coeff_214
  recurrence2B5A5_coeff_215
  recurrence2B5A5_coeff_216
  recurrence2B5A5_coeff_217
  recurrence2B5A5_coeff_218
  recurrence2B5A5_coeff_219
  recurrence2B5A5_coeff_220
  recurrence2B5A5_coeff_221
  recurrence2B5A5_coeff_222
  recurrence2B5A5_coeff_223
  recurrence2B5A5_coeff_224
  recurrence2B5A5_coeff_225
  recurrence2B5A5_coeff_226
  recurrence2B5A5_coeff_227
  recurrence2B5A5_coeff_228
  recurrence2B5A5_coeff_229
  recurrence2B5A5_coeff_230
  recurrence2B5A5_coeff_231
  recurrence2B5A5_coeff_232
  recurrence2B4A6_coeff_0
  recurrence2B4A6_coeff_1
  recurrence2B4A6_coeff_2
  recurrence2B4A6_coeff_3
  recurrence2B4A6_coeff_4
  recurrence2B4A6_coeff_5
  recurrence2B4A6_coeff_6
  recurrence2B4A6_coeff_7
  recurrence2B4A6_coeff_8
  recurrence2B4A6_coeff_9
  recurrence2B4A6_coeff_10
  recurrence2B4A6_coeff_11
  recurrence2B4A6_coeff_12
  recurrence2B4A6_coeff_13
  recurrence2B4A6_coeff_14
  recurrence2B4A6_coeff_15
  recurrence2B4A6_coeff_16
  recurrence2B4A6_coeff_17
  recurrence2B4A6_coeff_18
  recurrence2B4A6_coeff_19
  recurrence2B4A6_coeff_20
  recurrence2B4A6_coeff_21
  recurrence2B4A6_coeff_22
  recurrence2B4A6_coeff_23
  recurrence2B4A6_coeff_24
  recurrence2B4A6_coeff_25
  recurrence2B4A6_coeff_26
  recurrence2B4A6_coeff_27
  recurrence2B4A6_coeff_28
  recurrence2B4A6_coeff_29
  recurrence2B4A6_coeff_30
  recurrence2B4A6_coeff_31
  recurrence2B4A6_coeff_32
  recurrence2B4A6_coeff_33
  recurrence2B4A6_coeff_34
  recurrence2B4A6_coeff_35
  recurrence2B4A6_coeff_36
  recurrence2B4A6_coeff_37
  recurrence2B4A6_coeff_38
  recurrence2B4A6_coeff_39
  recurrence2B4A6_coeff_40
  recurrence2B4A6_coeff_41
  recurrence2B4A6_coeff_42
  recurrence2B4A6_coeff_43
  recurrence2B4A6_coeff_44
  recurrence2B4A6_coeff_45
  recurrence2B4A6_coeff_46
  recurrence2B4A6_coeff_47
  recurrence2B4A6_coeff_48
  recurrence2B4A6_coeff_49
  recurrence2B4A6_coeff_50
  recurrence2B4A6_coeff_51
  recurrence2B4A6_coeff_52
  recurrence2B4A6_coeff_53
  recurrence2B4A6_coeff_54
  recurrence2B4A6_coeff_55
  recurrence2B4A6_coeff_56
  recurrence2B4A6_coeff_57
  recurrence2B4A6_coeff_58
  recurrence2B4A6_coeff_59
  recurrence2B4A6_coeff_60
  recurrence2B4A6_coeff_61
  recurrence2B4A6_coeff_62
  recurrence2B4A6_coeff_63
  recurrence2B4A6_coeff_64
  recurrence2B4A6_coeff_65
  recurrence2B4A6_coeff_66
  recurrence2B4A6_coeff_67
  recurrence2B4A6_coeff_68
  recurrence2B4A6_coeff_69
  recurrence2B4A6_coeff_70
  recurrence2B4A6_coeff_71
  recurrence2B4A6_coeff_72
  recurrence2B4A6_coeff_73
  recurrence2B4A6_coeff_74
  recurrence2B4A6_coeff_75
  recurrence2B4A6_coeff_76
  recurrence2B4A6_coeff_77
  recurrence2B4A6_coeff_78
  recurrence2B4A6_coeff_79
  recurrence2B4A6_coeff_80
  recurrence2B4A6_coeff_81
  recurrence2B4A6_coeff_82
  recurrence2B4A6_coeff_83
  recurrence2B4A6_coeff_84
  recurrence2B4A6_coeff_85
  recurrence2B4A6_coeff_86
  recurrence2B4A6_coeff_87
  recurrence2B4A6_coeff_88
  recurrence2B4A6_coeff_89
  recurrence2B4A6_coeff_90
  recurrence2B4A6_coeff_91
  recurrence2B4A6_coeff_92
  recurrence2B4A6_coeff_93
  recurrence2B4A6_coeff_94
  recurrence2B4A6_coeff_95
  recurrence2B4A6_coeff_96
  recurrence2B4A6_coeff_97
  recurrence2B4A6_coeff_98
  recurrence2B4A6_coeff_99
  recurrence2B4A6_coeff_100
  recurrence2B4A6_coeff_101
  recurrence2B4A6_coeff_102
  recurrence2B4A6_coeff_103
  recurrence2B4A6_coeff_104
  recurrence2B4A6_coeff_105
  recurrence2B4A6_coeff_106
  recurrence2B4A6_coeff_107
  recurrence2B4A6_coeff_108
  recurrence2B4A6_coeff_109
  recurrence2B4A6_coeff_110
  recurrence2B4A6_coeff_111
  recurrence2B4A6_coeff_112
  recurrence2B4A6_coeff_113
  recurrence2B4A6_coeff_114
  recurrence2B4A6_coeff_115
  recurrence2B4A6_coeff_116
  recurrence2B4A6_coeff_117
  recurrence2B4A6_coeff_118
  recurrence2B4A6_coeff_119
  recurrence2B4A6_coeff_120
  recurrence2B4A6_coeff_121
  recurrence2B4A6_coeff_122
  recurrence2B4A6_coeff_123
  recurrence2B4A6_coeff_124
  recurrence2B4A6_coeff_125
  recurrence2B4A6_coeff_126
  recurrence2B4A6_coeff_127
  recurrence2B4A6_coeff_128
  recurrence2B4A6_coeff_129
  recurrence2B4A6_coeff_130
  recurrence2B4A6_coeff_131
  recurrence2B4A6_coeff_132
  recurrence2B4A6_coeff_133
  recurrence2B4A6_coeff_134
  recurrence2B4A6_coeff_135
  recurrence2B4A6_coeff_136
  recurrence2B4A6_coeff_137
  recurrence2B4A6_coeff_138
  recurrence2B4A6_coeff_139
  recurrence2B4A6_coeff_140
  recurrence2B4A6_coeff_141
  recurrence2B4A6_coeff_142
  recurrence2B4A6_coeff_143
  recurrence2B4A6_coeff_144
  recurrence2B4A6_coeff_145
  recurrence2B4A6_coeff_146
  recurrence2B4A6_coeff_147
  recurrence2B4A6_coeff_148
  recurrence2B4A6_coeff_149
  recurrence2B4A6_coeff_150
  recurrence2B4A6_coeff_151
  recurrence2B4A6_coeff_152
  recurrence2B4A6_coeff_153
  recurrence2B4A6_coeff_154
  recurrence2B4A6_coeff_155
  recurrence2B4A6_coeff_156
  recurrence2B4A6_coeff_157
  recurrence2B4A6_coeff_158
  recurrence2B4A6_coeff_159
  recurrence2B4A6_coeff_160
  recurrence2B4A6_coeff_161
  recurrence2B4A6_coeff_162
  recurrence2B4A6_coeff_163
  recurrence2B4A6_coeff_164
  recurrence2B4A6_coeff_165
  recurrence2B4A6_coeff_166
  recurrence2B4A6_coeff_167
  recurrence2B4A6_coeff_168
  recurrence2B4A6_coeff_169
  recurrence2B4A6_coeff_170
  recurrence2B4A6_coeff_171
  recurrence2B4A6_coeff_172
  recurrence2B4A6_coeff_173
  recurrence2B4A6_coeff_174
  recurrence2B4A6_coeff_175
  recurrence2B4A6_coeff_176
  recurrence2B4A6_coeff_177
  recurrence2B4A6_coeff_178
  recurrence2B4A6_coeff_179
  recurrence2B4A6_coeff_180
  recurrence2B4A6_coeff_181
  recurrence2B4A6_coeff_182
  recurrence2B4A6_coeff_183
  recurrence2B4A6_coeff_184
  recurrence2B4A6_coeff_185
  recurrence2B4A6_coeff_186
  recurrence2B4A6_coeff_187
  recurrence2B4A6_coeff_188
  recurrence2B4A6_coeff_189
  recurrence2B4A6_coeff_190
  recurrence2B4A6_coeff_191
  recurrence2B4A6_coeff_192
  recurrence2B4A6_coeff_193
  recurrence2B4A6_coeff_194
  recurrence2B4A6_coeff_195
  recurrence2B4A6_coeff_196
  recurrence2B4A6_coeff_197
  recurrence2B4A6_coeff_198
  recurrence2B4A6_coeff_199
  recurrence2B4A6_coeff_200
  recurrence2B4A6_coeff_201
  recurrence2B4A6_coeff_202
  recurrence2B4A6_coeff_203
  recurrence2B4A6_coeff_204
  recurrence2B4A6_coeff_205
  recurrence2B4A6_coeff_206
  recurrence2B4A6_coeff_207
  recurrence2B4A6_coeff_208
  recurrence2B4A6_coeff_209
  recurrence2B4A6_coeff_210
  recurrence2B4A6_coeff_211
  recurrence2B4A6_coeff_212
  recurrence2B4A6_coeff_213
  recurrence2B4A6_coeff_214
  recurrence2B4A6_coeff_215
  recurrence2B4A6_coeff_216
  recurrence2B4A6_coeff_217
  recurrence2B4A6_coeff_218
  recurrence2B4A6_coeff_219
  recurrence2B4A6_coeff_220
  recurrence2B4A6_coeff_221
  recurrence2B4A6_coeff_222
  recurrence2B4A6_coeff_223
  recurrence2B4A6_coeff_224
  recurrence2B4A6_coeff_225
  recurrence2B4A6_coeff_226
  recurrence2B4A6_coeff_227
  recurrence2B4A6_coeff_228
  recurrence2B4A6_coeff_229
  recurrence2B4A6_coeff_230
  recurrence2B4A6_coeff_231
  recurrence2B4A6_coeff_232
  recurrence2B4A6_coeff_233

theorem recurrence2QuotientConstant_coeff_0 :
    recurrence2QuotientConstant.coeff 0 =
      (-512 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_1 :
    recurrence2QuotientConstant.coeff 1 =
      (-491856 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_2 :
    recurrence2QuotientConstant.coeff 2 =
      (41240007168 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_3 :
    recurrence2QuotientConstant.coeff 3 =
      (-14993788820288 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_4 :
    recurrence2QuotientConstant.coeff 4 =
      (55040297674273916 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_5 :
    recurrence2QuotientConstant.coeff 5 =
      (-8226350332907563616 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_6 :
    recurrence2QuotientConstant.coeff 6 =
      (-13429596565689134208692 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_7 :
    recurrence2QuotientConstant.coeff 7 =
      (6837148942685031773950688 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_8 :
    recurrence2QuotientConstant.coeff 8 =
      (-2557971651439688603044965766 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_9 :
    recurrence2QuotientConstant.coeff 9 =
      (479304576296494976698921436057 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_10 :
    recurrence2QuotientConstant.coeff 10 =
      (-55479584549982053336861615100348 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_11 :
    recurrence2QuotientConstant.coeff 11 =
      (3934283096582064772599663806558006 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_12 :
    recurrence2QuotientConstant.coeff 12 =
      (-111016944769371363974096291016842559 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_13 :
    recurrence2QuotientConstant.coeff 13 =
      (-4481497092329180833939431036318462021 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_14 :
    recurrence2QuotientConstant.coeff 14 =
      (670059977701344982484758428075133859051 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_15 :
    recurrence2QuotientConstant.coeff 15 =
      (-39304505795705944531680598508787237352111 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_16 :
    recurrence2QuotientConstant.coeff 16 =
      (1541858071174660046682959562129940423997845 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_17 :
    recurrence2QuotientConstant.coeff 17 =
      (-26878512836566824524587502470940571413673534 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_18 :
    recurrence2QuotientConstant.coeff 18 =
      (-2679565980827566916744794319700731118846165826 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_19 :
    recurrence2QuotientConstant.coeff 19 =
      (291207472840372727991489701440832284192160605827 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_20 :
    recurrence2QuotientConstant.coeff 20 =
      (-14145306134120324608186373766855888258791230604712 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_21 :
    recurrence2QuotientConstant.coeff 21 =
      (370137092276992865357884991607197674275244374337665 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_22 :
    recurrence2QuotientConstant.coeff 22 =
      (-3024751742613743375877922680147169286638662209754567 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_23 :
    recurrence2QuotientConstant.coeff 23 =
      (-127562459010379512298760798646356529825748898037328606 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_24 :
    recurrence2QuotientConstant.coeff 24 =
      (4488122303225925264568232446752906222189978714040522529 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_25 :
    recurrence2QuotientConstant.coeff 25 =
      (-30434771321913889535460479608083486458568151391692456072 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_26 :
    recurrence2QuotientConstant.coeff 26 =
      (-1544120433553692765365679616544613149298514199380375354668 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_27 :
    recurrence2QuotientConstant.coeff 27 =
      (46905768153046890595146264271291295392505484157443688085318 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_28 :
    recurrence2QuotientConstant.coeff 28 =
      (-383573234390155491399674889607964245679021863083044971547985 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_29 :
    recurrence2QuotientConstant.coeff 29 =
      (-9292563013062650441403549600223007941893376515863368741208230 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_30 :
    recurrence2QuotientConstant.coeff 30 =
      (365659203469113390596188329311614309651043555275286551797021314 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_31 :
    recurrence2QuotientConstant.coeff 31 =
      (-6985526664534040839039170027560757131574612646865493327879577476 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_32 :
    recurrence2QuotientConstant.coeff 32 =
      (108174935299609563298773703765608046587988061805273057266931799688 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_33 :
    recurrence2QuotientConstant.coeff 33 =
      (-1772549939023963891202963720607214327653863552292308627938210110852 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_34 :
    recurrence2QuotientConstant.coeff 34 =
      (30667889913218020520558222196253596124992386731447103379412919727650 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_35 :
    recurrence2QuotientConstant.coeff 35 =
      (-466971491314630702736538424714023526259121169402586410440376296986439 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_36 :
    recurrence2QuotientConstant.coeff 36 =
      (5504941396339381699755478393572890504368707072490375474566510081739856 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_37 :
    recurrence2QuotientConstant.coeff 37 =
      -((4 * 10 ^ 70 +
        5441716887979583877030826628563245054371781905901861791128080846865581) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_38 :
    recurrence2QuotientConstant.coeff 38 =
      ((18 * 10 ^ 70 +
        0565022875822634338030378656685773432973674959563527811862745376380984) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_39 :
    recurrence2QuotientConstant.coeff 39 =
      ((182 * 10 ^ 70 +
        4264957427737717860798704087583086227436480046104836082734456750626170) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_40 :
    recurrence2QuotientConstant.coeff 40 =
      -((5692 * 10 ^ 70 +
        0897715716714736663142264770966164519698227357359563428678687325721360) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_41 :
    recurrence2QuotientConstant.coeff 41 =
      ((97619 * 10 ^ 70 +
        3119666579389958048732668976054650542514807751583073842545053452986522) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_42 :
    recurrence2QuotientConstant.coeff 42 =
      -((1380636 * 10 ^ 70 +
        5331913537366355862103784154414774463360385578455598909749699293415936) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_43 :
    recurrence2QuotientConstant.coeff 43 =
      ((16839753 * 10 ^ 70 +
        3195740321931647912394047810101257695649234576518971125586965364594487) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_44 :
    recurrence2QuotientConstant.coeff 44 =
      -((178084458 * 10 ^ 70 +
        2491609748865691950599518636534548470587058581007994932634393605183483) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_45 :
    recurrence2QuotientConstant.coeff 45 =
      ((1659608292 * 10 ^ 70 +
        6838873304450554177130908786542132987468419431283889818823285872038235) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_46 :
    recurrence2QuotientConstant.coeff 46 =
      -((14034516941 * 10 ^ 70 +
        8359958636050692680840320654595112994603133354654258926853899046311363) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_47 :
    recurrence2QuotientConstant.coeff 47 =
      ((110926813597 * 10 ^ 70 +
        6665971365555360856515655885143069904294483076499505023043498901227520) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_48 :
    recurrence2QuotientConstant.coeff 48 =
      -((830580129752 * 10 ^ 70 +
        0591668167623769537792269029810772667147172112235472137761054949104380) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_49 :
    recurrence2QuotientConstant.coeff 49 =
      ((5846976405830 * 10 ^ 70 +
        2862227062764583279082826103997924622854695529738872246560956994683811) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_50 :
    recurrence2QuotientConstant.coeff 50 =
      -((38059898998041 * 10 ^ 70 +
        1499311094167950349243611868712825531755495646315918748555334575036048) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_51 :
    recurrence2QuotientConstant.coeff 51 =
      ((227128448498313 * 10 ^ 70 +
        7616733427334575549253140387349383253199659283987349788606014160563102) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_52 :
    recurrence2QuotientConstant.coeff 52 =
      -((1255594086457142 * 10 ^ 70 +
        3569772228296985813627822849602518173889374960953381027976619030662179) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_53 :
    recurrence2QuotientConstant.coeff 53 =
      ((6617468925365368 * 10 ^ 70 +
        1988544146829381913130334109956335573600291290149569722257006740314962) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_54 :
    recurrence2QuotientConstant.coeff 54 =
      -((34117205201671284 * 10 ^ 70 +
        5172064217712460019211587693913644843831537644799282602752915920310376) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_55 :
    recurrence2QuotientConstant.coeff 55 =
      ((169755965269596841 * 10 ^ 70 +
        3318373041206685181452617176283819720496993467484501307576983082813196) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_56 :
    recurrence2QuotientConstant.coeff 56 =
      -((766641639447800853 * 10 ^ 70 +
        3387034871257730686482606031537916613320695841607444518834210587995657) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_57 :
    recurrence2QuotientConstant.coeff 57 =
      ((2916809913109180048 * 10 ^ 70 +
        4564001758953672927651130830574233786817963504147122410159732402016296) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_58 :
    recurrence2QuotientConstant.coeff 58 =
      -((9172110913695764411 * 10 ^ 70 +
        1460699962962591431015168362547887069746628978849469480805020102401897) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_59 :
    recurrence2QuotientConstant.coeff 59 =
      ((29762202203722210505 * 10 ^ 70 +
        3251210235293333096260720031907763663420062398406122297652613166863483) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_60 :
    recurrence2QuotientConstant.coeff 60 =
      -((146081790880175238718 * 10 ^ 70 +
        1008772766227951487920802288515751905312526799123418313466368726246215) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_61 :
    recurrence2QuotientConstant.coeff 61 =
      ((763727882896622020552 * 10 ^ 70 +
        3205263877770620648370590416307820180152202843092586392838073861203031) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_62 :
    recurrence2QuotientConstant.coeff 62 =
      -((2274951724541142068927 * 10 ^ 70 +
        5638036582557516368884889515107395491767177142902130852982177966588402) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_63 :
    recurrence2QuotientConstant.coeff 63 =
      -((2480351411886220277298 * 10 ^ 70 +
        7036108477132599956751663781365776150696192733628171656146911712678032) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_64 :
    recurrence2QuotientConstant.coeff 64 =
      ((52425135468259393014407 * 10 ^ 70 +
        1984653007696844678161092416848103250747710358759112544340954570750849) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_65 :
    recurrence2QuotientConstant.coeff 65 =
      -((168063336814355064638129 * 10 ^ 70 +
        5886920539616519239265679944796130194031749111040836586831010143648582) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_66 :
    recurrence2QuotientConstant.coeff 66 =
      -((236209919853327551790269 * 10 ^ 70 +
        0681755856038342831975158396839020377873211010013926273080844481120632) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_67 :
    recurrence2QuotientConstant.coeff 67 =
      ((3677645205092967810425028 * 10 ^ 70 +
        8903776220895781960642658576589875765025256816621882749610137422246142) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_68 :
    recurrence2QuotientConstant.coeff 68 =
      -((12287369320872756633678056 * 10 ^ 70 +
        7311849853681166168735448217339262341911186685078207120572464326344651) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_69 :
    recurrence2QuotientConstant.coeff 69 =
      ((3270925225131787526284757 * 10 ^ 70 +
        0544037786362436849797349472366537762035457847578975282792177735866502) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_70 :
    recurrence2QuotientConstant.coeff 70 =
      ((235348652834069686279836881 * 10 ^ 70 +
        0644162226689815855564394340252937060633484064668594780140308346207197) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_71 :
    recurrence2QuotientConstant.coeff 71 =
      -((2049250246016993979444245450 * 10 ^ 70 +
        9968860401589938913062136316622411988280100127498824627799768363853729) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_72 :
    recurrence2QuotientConstant.coeff 72 =
      ((8640225281057068520099586970 * 10 ^ 70 +
        1085385443447195385804443566282497836290637817687907493466916106076967) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_73 :
    recurrence2QuotientConstant.coeff 73 =
      ((5143413541651453514281350645 * 10 ^ 70 +
        3899665003690833068328633976972446723122950700253078760475535129588570) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_74 :
    recurrence2QuotientConstant.coeff 74 =
      -((270373815778684308946011709564 * 10 ^ 70 +
        8765283618261008892855730310810429503169160272831367150819461014779134) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_75 :
    recurrence2QuotientConstant.coeff 75 =
      ((1228765850541740897750508596697 * 10 ^ 70 +
        5783768574332299242396184620467219554090624274105643325952178708497035) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_76 :
    recurrence2QuotientConstant.coeff 76 =
      ((610236060929655750921819803466 * 10 ^ 70 +
        3796163816080140446265509795613941698253028902326778467884221613562250) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_77 :
    recurrence2QuotientConstant.coeff 77 =
      -((28408410738002195935450556389816 * 10 ^ 70 +
        6857909117157324683454287924490069116932232452520224662376805352442218) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_78 :
    recurrence2QuotientConstant.coeff 78 =
      ((99579459016686315974347698038176 * 10 ^ 70 +
        5797773748666279389355775400192853923413150738869853907220074064938146) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_79 :
    recurrence2QuotientConstant.coeff 79 =
      ((141570683035464950781160801684074 * 10 ^ 70 +
        2367178159695077765357490812093757512232719693141693742348372951752027) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_80 :
    recurrence2QuotientConstant.coeff 80 =
      -((2114382532510757308745650305711220 * 10 ^ 70 +
        0973803621534569820921130649510734758547323281698500979721250797821460) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_81 :
    recurrence2QuotientConstant.coeff 81 =
      ((4362750821924344231812361987378544 * 10 ^ 70 +
        3350272963902900098516350836723071686938470199467966002671720738971429) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_82 :
    recurrence2QuotientConstant.coeff 82 =
      ((18592838473436541214238271363674415 * 10 ^ 70 +
        1075674150802653876096388189028863299418074870361243606583864480826001) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_83 :
    recurrence2QuotientConstant.coeff 83 =
      -((109284722057959599775055145425493679 * 10 ^ 70 +
        2709313540716131655714518054819995011401157547404301407692914895447040) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_84 :
    recurrence2QuotientConstant.coeff 84 =
      -((10783244650457873189064119904770888 * 10 ^ 70 +
        6480750957392816133096539430284817999774884121412471788424377534131506) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_85 :
    recurrence2QuotientConstant.coeff 85 =
      ((1646671993543596036498971869561716922 * 10 ^ 70 +
        5097381715933586781548072327319454266937012389126088777534017714706047) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_86 :
    recurrence2QuotientConstant.coeff 86 =
      -((3623710275857113897918814513022267326 * 10 ^ 70 +
        2047234758453804506974829580245272547133469672296648708834131871189750) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_87 :
    recurrence2QuotientConstant.coeff 87 =
      -((17804515240494486031174414848195527106 * 10 ^ 70 +
        0353110685563153197777512637881674297297375886007428815497467968050368) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_88 :
    recurrence2QuotientConstant.coeff 88 =
      ((109819875147487474951848620847521118730 * 10 ^ 70 +
        3786690514887028837495000996080645401517857778648762531545483927751244) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_89 :
    recurrence2QuotientConstant.coeff 89 =
      -((43479516004994828284049100161020378083 * 10 ^ 70 +
        4454065487101522658263374149578323163512461383904940907868406233687555) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_90 :
    recurrence2QuotientConstant.coeff 90 =
      -((1575670093804982792504869956244921883012 * 10 ^ 70 +
        4584488776579807908790950880258702010468132159863488278868204432478506) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_91 :
    recurrence2QuotientConstant.coeff 91 =
      ((5761770105668258228442210549958319807407 * 10 ^ 70 +
        8606281761082598699579997888241697315944867157892033920987150659032843) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_92 :
    recurrence2QuotientConstant.coeff 92 =
      ((3466263493870793861362960010629657768104 * 10 ^ 70 +
        5927352560662254868736609201025061156376434012352179189226465853961129) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_93 :
    recurrence2QuotientConstant.coeff 93 =
      -((89145475998524054471995730056771416366087 * 10 ^ 70 +
        2784181714586796988549309828285651062931339153629867960412071229692547) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_94 :
    recurrence2QuotientConstant.coeff 94 =
      ((244626419505478463636741156213445781676622 * 10 ^ 70 +
        4138052109797547524710716412817151989710416854653127023969535656875244) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_95 :
    recurrence2QuotientConstant.coeff 95 =
      ((321033667443742940740579325541664297233793 * 10 ^ 70 +
        5377835393857854953385240680922960799892383621220657621503084282241443) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_96 :
    recurrence2QuotientConstant.coeff 96 =
      -((3974352740438724381045029954028617766691032 * 10 ^ 70 +
        4598281393241356255167724714031056435913883074360051439536851219324471) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_97 :
    recurrence2QuotientConstant.coeff 97 =
      ((8943914708837888281727953477847887559908258 * 10 ^ 70 +
        8805302506240597353528653458755622077224292228705831304352250923129755) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_98 :
    recurrence2QuotientConstant.coeff 98 =
      ((16715876236737359265886978670874668647526320 * 10 ^ 70 +
        6605007606926401194373157344602908883602449156490046475631677008112061) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_99 :
    recurrence2QuotientConstant.coeff 99 =
      -((153164572031443580979230872632563514613962083 * 10 ^ 70 +
        3394474496790427624321824408411977677996241166256820375241051070186492) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_100 :
    recurrence2QuotientConstant.coeff 100 =
      ((312821429446844043715115280481958706438344398 * 10 ^ 70 +
        2533055087404715418503269234517694628570496434303725024176216715834613) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_101 :
    recurrence2QuotientConstant.coeff 101 =
      ((606044111082700366140534931023153583418477776 * 10 ^ 70 +
        2838784131123432567727890392274063849527730347968079425015825819528545) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_102 :
    recurrence2QuotientConstant.coeff 102 =
      -((5211436520226292698162738689391789460286762191 * 10 ^ 70 +
        7062059273441741367923076521830852159258805001882896018371766720569455) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_103 :
    recurrence2QuotientConstant.coeff 103 =
      ((11068398584470050768938965593870828846329111784 * 10 ^ 70 +
        8858332884599801352636948493506444145080699295105567690008753546905420) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_104 :
    recurrence2QuotientConstant.coeff 104 =
      ((14262136811574748132183119476019354064708589386 * 10 ^ 70 +
        9402021898636445998096384736576377650217772947544128756055542484654268) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_105 :
    recurrence2QuotientConstant.coeff 105 =
      -((152426729422230276615741117795729212670411148729 * 10 ^ 70 +
        9530274172305660965636739398585281497923596084661564727449668392920724) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_106 :
    recurrence2QuotientConstant.coeff 106 =
      ((376954200513294890652162085389816735740701328453 * 10 ^ 70 +
        6182533049326046546841798951292875813244233888234887363180918693543899) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_107 :
    recurrence2QuotientConstant.coeff 107 =
      ((104104624706548845658215888541052195281673198816 * 10 ^ 70 +
        5929472598900598659856545018069984651371683963445053583478225663891981) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_108 :
    recurrence2QuotientConstant.coeff 108 =
      -((3632285999282725773394377813568813932248942530952 * 10 ^ 70 +
        3007009596504018364591781153092015327656736082335413441769356634955115) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_109 :
    recurrence2QuotientConstant.coeff 109 =
      ((11353016827959084255712830504828454858515848646596 * 10 ^ 70 +
        8595326536330183671108610118217534744229128755073042818580895299041768) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_110 :
    recurrence2QuotientConstant.coeff 110 =
      -((8468484322462321303177760812141932338913225510961 * 10 ^ 70 +
        0519057002452837951287239985279797644950562138667868632128710454925030) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_111 :
    recurrence2QuotientConstant.coeff 111 =
      -((62106092304978807582767106173196609549184304059236 * 10 ^ 70 +
        9164854429345988804260403090604756777131384804091062913458707969504631) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_112 :
    recurrence2QuotientConstant.coeff 112 =
      ((276895325482153851043139769351273098764436357197284 * 10 ^ 70 +
        3430768819048569746651143265586468380083200586647482616591787727709146) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_113 :
    recurrence2QuotientConstant.coeff 113 =
      -((474520123548883663076843845334148688051631758513923 * 10 ^ 70 +
        7513861001088788849747209721781422524621330298315928606025547037008021) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_114 :
    recurrence2QuotientConstant.coeff 114 =
      -((410454055309558148862138550622967258953223736505888 * 10 ^ 70 +
        8202200965862533165016309129795922343100369573712861889348639396522137) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_115 :
    recurrence2QuotientConstant.coeff 115 =
      ((4786691939656948245143440229092630052553173076672789 * 10 ^ 70 +
        3554838963611424217608147195126691330262307007813282777311262256496846) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_116 :
    recurrence2QuotientConstant.coeff 116 =
      -((13584729819977392192224831137763626937600529871701236 * 10 ^ 70 +
        6234217890308696999238595665415245890394290256218334705228761143927865) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_117 :
    recurrence2QuotientConstant.coeff 117 =
      ((14553449522769838504947298757132823885441255342144987 * 10 ^ 70 +
        7688071682820947593636034272109254011332113397659328302536210196444328) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_118 :
    recurrence2QuotientConstant.coeff 118 =
      ((38421061629395343428410715464952263498082885387657095 * 10 ^ 70 +
        2091082142950124845054562161986718428528674998400653171141785282040337) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_119 :
    recurrence2QuotientConstant.coeff 119 =
      -((224506863828432501957919503275285657066487637482043953 * 10 ^ 70 +
        8868001636023422583751729883073088140779892018045548530632287908936013) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_120 :
    recurrence2QuotientConstant.coeff 120 =
      ((539610729977985941370156222894702227602243401786382212 * 10 ^ 70 +
        1519385594818881451867544152790312106717453214825195816643253114982122) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_121 :
    recurrence2QuotientConstant.coeff 121 =
      -((530882496708788477781774037713838305004785268156991517 * 10 ^ 70 +
        3005696657966557309871762750237149026348443415841289754569267119474873) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_122 :
    recurrence2QuotientConstant.coeff 122 =
      -((1269938802222189150396172960854037515366270106975874693 * 10 ^ 70 +
        1145602140484068328625021891049265547575724784705514585930491646606066) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_123 :
    recurrence2QuotientConstant.coeff 123 =
      ((7350467843357570093886203414163509732115683121857595034 * 10 ^ 70 +
        0764371077892956849517332015497429604477440809771782463660889478455036) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_124 :
    recurrence2QuotientConstant.coeff 124 =
      -((18576180423114147135491801595645774794599113512673504046 * 10 ^ 70 +
        2287487387965230844389500464050220317264521238966630992915629111774407) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_125 :
    recurrence2QuotientConstant.coeff 125 =
      ((25912241669225592487474624148028989488103359239221660537 * 10 ^ 70 +
        2911739678710835785161535910374460432865598240014780761421327875303258) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_126 :
    recurrence2QuotientConstant.coeff 126 =
      ((3996052784783883042446319948877594097183307875459104636 * 10 ^ 70 +
        8883654129640300622197206988869882935686930283124300088321643217102491) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_127 :
    recurrence2QuotientConstant.coeff 127 =
      -((139567153565437668989036680225570877524195576807469894570 * 10 ^ 70 +
        5525747812183738798806256902833119029423250969862070801027481482576650) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_128 :
    recurrence2QuotientConstant.coeff 128 =
      ((461446736157732506389338431256588953874972757917456008431 * 10 ^ 70 +
        6715728039285648315881755866715888507630968026470277128983295989965440) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_129 :
    recurrence2QuotientConstant.coeff 129 =
      -((954752864946387209940715031755626079719503288688777566067 * 10 ^ 70 +
        6389863061332160395820207947667924978544273712068079032392050993123254) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_130 :
    recurrence2QuotientConstant.coeff 130 =
      ((1268199011858944756931844599916361777544614611204110165613 * 10 ^ 70 +
        1268632440826353187751009096794597380217091629645823172350269145978027) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_131 :
    recurrence2QuotientConstant.coeff 131 =
      -((358631838407693789914185125649142847200126601113383397908 * 10 ^ 70 +
        9086918517345813929158784092765052568739728279485071924202880759209736) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_132 :
    recurrence2QuotientConstant.coeff 132 =
      -((3805057398051767717914333115392866341190473859771646663928 * 10 ^ 70 +
        1556004731962305419290909289228045698756244507377705048166579312087368) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_133 :
    recurrence2QuotientConstant.coeff 133 =
      ((14096806775714869045941356921400785348964578476035811051178 * 10 ^ 70 +
        6193784450437677645331602803144192620077234417636849179121399520355482) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_134 :
    recurrence2QuotientConstant.coeff 134 =
      -((33140064985293142466029300370071271587405860349710023281552 * 10 ^ 70 +
        6177128946107426615108772716430079639620114169283638995765866345374252) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_135 :
    recurrence2QuotientConstant.coeff 135 =
      ((60926725957872608422840793362837984011292820668536080111200 * 10 ^ 70 +
        1017464269340333192485767305517440397810240122046435304205762033926908) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_136 :
    recurrence2QuotientConstant.coeff 136 =
      -((91428632249168593949420579762382701180782477114405878317790 * 10 ^ 70 +
        9516483132920582116699879531793540692183291545222770688446917905264227) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_137 :
    recurrence2QuotientConstant.coeff 137 =
      ((109471456751321865773231464463994624732056343761611150387478 * 10 ^ 70 +
        3727180744915572824497229690115623209814661476050138476803854039120328) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_138 :
    recurrence2QuotientConstant.coeff 138 =
      -((90042299163315994238164265670186904274076950144370143422367 * 10 ^ 70 +
        7192399907017331611511262618591213043910389269974007020732003794176980) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_139 :
    recurrence2QuotientConstant.coeff 139 =
      ((2282693115568516506004492226106469869781729648521455497901 * 10 ^ 70 +
        9149809077389882520668786546973211039552966488631783957192637876086061) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_140 :
    recurrence2QuotientConstant.coeff 140 =
      ((180927719908863112808422727585832946840210901333542680598005 * 10 ^ 70 +
        9586512184792431757375686153816505464386868177196083281604613553150178) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_141 :
    recurrence2QuotientConstant.coeff 141 =
      -((469594701818081754898092682072601298806103762845387480896173 * 10 ^ 70 +
        9872570078363436208754467562528968752002232012968210645241079341265258) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_142 :
    recurrence2QuotientConstant.coeff 142 =
      ((844238264154912805754265397525096386583720680736843331201541 * 10 ^ 70 +
        8325083083703553642635846202801946820818630411742418354068108735853849) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_143 :
    recurrence2QuotientConstant.coeff 143 =
      -((1250868617632128055064513941997600662889323008482130056007989 * 10 ^ 70 +
        4843553497579117977318859867265113409324789984274623602343550270115447) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_144 :
    recurrence2QuotientConstant.coeff 144 =
      ((1608230149306672499383716794188314937082559113268185740438177 * 10 ^ 70 +
        6408341162278439876562458810108824078463493139235879858201827829458780) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_145 :
    recurrence2QuotientConstant.coeff 145 =
      -((1827701115660462369079474634297481552754581079182798700602611 * 10 ^ 70 +
        2679086621868871469438104097209544137987381645488168236744197866748984) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_146 :
    recurrence2QuotientConstant.coeff 146 =
      ((1840315744251132012810060450481789892761476089790009991211647 * 10 ^ 70 +
        8142316590356678435501712457030776921991185990042471066874600645074338) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_147 :
    recurrence2QuotientConstant.coeff 147 =
      -((1621031778667591610945805256756189322382750837831101345718785 * 10 ^ 70 +
        0953997747052897283284817947593342777547027094276964060179345380359551) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_148 :
    recurrence2QuotientConstant.coeff 148 =
      ((1200207172444041963478171060371427881610264973003425065756947 * 10 ^ 70 +
        0731723772650660505260307706310858593536417640961280578333824915414427) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_149 :
    recurrence2QuotientConstant.coeff 149 =
      -((656880709449187041183238910057570312639281146457890130938073 * 10 ^ 70 +
        2229540973392137313156269556578139216482084569320848005800301206032373) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_150 :
    recurrence2QuotientConstant.coeff 150 =
      ((95893146373533393986887376109979124151491417821339136924382 * 10 ^ 70 +
        5670720647987327987652202954769889847308809935132589981713380949500720) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_151 :
    recurrence2QuotientConstant.coeff 151 =
      ((382460236684890508680904308337005106058795356435930262822284 * 10 ^ 70 +
        7236053066272422981195162064009273864342196103044576491825922585948153) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_152 :
    recurrence2QuotientConstant.coeff 152 =
      -((708913745339995733241519790712227287327983648481800455292451 * 10 ^ 70 +
        0585029734424901250135956080541462300410643810274725050227860188273744) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_153 :
    recurrence2QuotientConstant.coeff 153 =
      ((858963302922781509832691742126821236561034757030188123425632 * 10 ^ 70 +
        1475153499886234010047081198341489869320539413563602774575832432180133) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_154 :
    recurrence2QuotientConstant.coeff 154 =
      -((850925918756968244376525963665967520451968242671961688002641 * 10 ^ 70 +
        6770722588500228636008526290383048672582300802808610910471929698493244) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_155 :
    recurrence2QuotientConstant.coeff 155 =
      ((731761817552505989188102354012565558135135219717367623201848 * 10 ^ 70 +
        1341807440808906634915277597656355630959806943667078717418895946306497) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_156 :
    recurrence2QuotientConstant.coeff 156 =
      -((557944448406574890953283433061703636181133487080234441772406 * 10 ^ 70 +
        0009941371148982996143291529403691844257900720133296865451483141237052) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_157 :
    recurrence2QuotientConstant.coeff 157 =
      ((378798863359898353739866538857390835654619166256134582735988 * 10 ^ 70 +
        3637316388836198503259655844614934335488622120263635117968763259812190) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_158 :
    recurrence2QuotientConstant.coeff 158 =
      -((226916665431685235977528295537794158385351277490913525890312 * 10 ^ 70 +
        5542179280375930323987246051570206015283071991993793518950693212909579) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_159 :
    recurrence2QuotientConstant.coeff 159 =
      ((116430637466789982116580564290487620870305925948955712136036 * 10 ^ 70 +
        1141928718438248001627825227703492430231119243761174631308473530141326) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_160 :
    recurrence2QuotientConstant.coeff 160 =
      -((46969874058074426649686299964259771480300949743135275714549 * 10 ^ 70 +
        0748263245282945431993451488515721501945736872338080111368379339986501) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_161 :
    recurrence2QuotientConstant.coeff 161 =
      ((9956259496947514445995084057129225394550375207844883431332 * 10 ^ 70 +
        0855890586507287088344392641210610412804241412307635912646973724781156) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_162 :
    recurrence2QuotientConstant.coeff 162 =
      ((5604913734766179909416719226718478206728218028683780677127 * 10 ^ 70 +
        8966358542457783592496581881937048191978971052986807544989544902370087) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_163 :
    recurrence2QuotientConstant.coeff 163 =
      -((9350411077379022623763815578304283774916335913100486528665 * 10 ^ 70 +
        0207907997181880290722299373267698740658035521233152464276625791117773) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_164 :
    recurrence2QuotientConstant.coeff 164 =
      ((7988114685340280336434960857159703454783745919592923596623 * 10 ^ 70 +
        2445895319718174087672914346535647702782111973341781942245621468649043) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_165 :
    recurrence2QuotientConstant.coeff 165 =
      -((5314325883302852082332740863990397514419419338901063522821 * 10 ^ 70 +
        5759805713485966977684761824596273850562897757730451042708144706095903) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_166 :
    recurrence2QuotientConstant.coeff 166 =
      ((2994539931082249717841910656357652834415852952779071665489 * 10 ^ 70 +
        0487384537428363692889588305886454998956517038159489783100347423187105) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_167 :
    recurrence2QuotientConstant.coeff 167 =
      -((1464927403511696642559621990366639321187509488115918284712 * 10 ^ 70 +
        4738226442666820447250270701615185273003410003158094649005602497130180) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_168 :
    recurrence2QuotientConstant.coeff 168 =
      ((621934337756461026561531467976901794114290660216857286179 * 10 ^ 70 +
        8264243677001715508926021105104370987670932889619090902217619568352209) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_169 :
    recurrence2QuotientConstant.coeff 169 =
      -((223551385347235223748878653454126442502186614342881605366 * 10 ^ 70 +
        6218935615496433888289476914444609331153765164918957400723376251492010) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_170 :
    recurrence2QuotientConstant.coeff 170 =
      ((62836532774209909228659309619382685704339854522967204724 * 10 ^ 70 +
        8245867820838411297730007952149104871677961937385904650457589759308777) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_171 :
    recurrence2QuotientConstant.coeff 171 =
      -((9605195303024301908729258072169689456424430952347403392 * 10 ^ 70 +
        0930268354974780148587722595605215698286750599135996083699659550906593) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_172 :
    recurrence2QuotientConstant.coeff 172 =
      -((2989474569748585703583111254384705552450472662814128677 * 10 ^ 70 +
        2327104838124850436260698364885247855330471745436479671753967029507059) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_173 :
    recurrence2QuotientConstant.coeff 173 =
      ((3543723214529108134157355844999472671947150009760231659 * 10 ^ 70 +
        6619584467974102963399229321083473917084389079178294127979621006330190) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_174 :
    recurrence2QuotientConstant.coeff 174 =
      -((1997741141822818033831988686816508476508681675587538743 * 10 ^ 70 +
        0965734577829793785545261986606852169341879926165195581252848820444137) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_175 :
    recurrence2QuotientConstant.coeff 175 =
      ((852475815153771389031367954616327977909760351610676489 * 10 ^ 70 +
        8918139307335357665143021539293647700425971189430136599570800583671689) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_176 :
    recurrence2QuotientConstant.coeff 176 =
      -((298820935985060571231451663794862658233557202785676830 * 10 ^ 70 +
        5217836966627931067054585365324303813486051094129978534435753619566663) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_177 :
    recurrence2QuotientConstant.coeff 177 =
      ((87021963670566521171551612100471110192139038236547433 * 10 ^ 70 +
        4826154636130799655230771343534195433778632664839418690325864323264154) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_178 :
    recurrence2QuotientConstant.coeff 178 =
      -((20311733397066662880263019715544249002347486348452585 * 10 ^ 70 +
        6204808004478346031992437152320021456567850476064831716385638656922117) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_179 :
    recurrence2QuotientConstant.coeff 179 =
      ((3265234354851933742721061813141109935286511024023582 * 10 ^ 70 +
        7648827691910525272162295020200079374222793883375326817380379397741497) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_180 :
    recurrence2QuotientConstant.coeff 180 =
      -((44713021969286522367134204638884490043621366015332 * 10 ^ 70 +
        9497263038114396866174582262371178462908381924811209771736103500975702) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_181 :
    recurrence2QuotientConstant.coeff 181 =
      -((214417448267323906932149540854142254314368569655693 * 10 ^ 70 +
        9179181093046394602820174764348092544381874540286669478097616965873838) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_182 :
    recurrence2QuotientConstant.coeff 182 =
      ((100987725054697621614197377932512284231402950040842 * 10 ^ 70 +
        1970741765551276275715695199026098994211452449692504381194792573397884) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_183 :
    recurrence2QuotientConstant.coeff 183 =
      -((30982403971037860027549869640766150935404524670332 * 10 ^ 70 +
        7420738193159438187584649987961695369951735038582763231590779326072882) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_184 :
    recurrence2QuotientConstant.coeff 184 =
      ((7256238890422583051812639417863408710138143744928 * 10 ^ 70 +
        9347546046405461650394633089749203772452036484275286247227102686228421) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_185 :
    recurrence2QuotientConstant.coeff 185 =
      -((1302016343332057409324976288609642758918744719393 * 10 ^ 70 +
        8326508425732832385524088350726311292094737095612679429566440281510924) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_186 :
    recurrence2QuotientConstant.coeff 186 =
      ((157577058029595215182862004892453010776842828301 * 10 ^ 70 +
        9723114850895770313481567350989736148041291403973544783199286999839477) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_187 :
    recurrence2QuotientConstant.coeff 187 =
      -((3008235695494971830058778960902351729366331092 * 10 ^ 70 +
        9032568123453831976511969210050375701166459204123928297498897278024332) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_188 :
    recurrence2QuotientConstant.coeff 188 =
      -((4544908117087317908857500816503922769375719821 * 10 ^ 70 +
        1660656029393131728344400979574358068200494190410523185623511893586013) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_189 :
    recurrence2QuotientConstant.coeff 189 =
      ((1459004563825452814637068602309365138368664006 * 10 ^ 70 +
        5591160838253338377569669620019209577541676379156964326951077247453067) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_190 :
    recurrence2QuotientConstant.coeff 190 =
      -((283172202573338366848731413392542072110763942 * 10 ^ 70 +
        4814835019234049633741820835345644447624087322025386772256260796555056) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_191 :
    recurrence2QuotientConstant.coeff 191 =
      ((38117405023946771806411130202098864275915099 * 10 ^ 70 +
        2803386925118570509595633644335741628320545262439837568069682275864768) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_192 :
    recurrence2QuotientConstant.coeff 192 =
      -((3106381913655928709487652995700176007447873 * 10 ^ 70 +
        2209617733178649209752149511396033050967421113747180611421215304884658) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_193 :
    recurrence2QuotientConstant.coeff 193 =
      -((28027058942878123755612621269083127289179 * 10 ^ 70 +
        9296794513271806002386897415637431824120420084584154024632310423995369) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_194 :
    recurrence2QuotientConstant.coeff 194 =
      ((57260041824563086134819059894986200462836 * 10 ^ 70 +
        3314196584053920440457683084824219169816979795320431192066187782136534) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_195 :
    recurrence2QuotientConstant.coeff 195 =
      -((10414979449678146893103215059846699221308 * 10 ^ 70 +
        0417269953460772832875824653847582724172944286250087150014612326365558) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_196 :
    recurrence2QuotientConstant.coeff 196 =
      ((1083013041597422689197823539377980988288 * 10 ^ 70 +
        5810193998382851108058551425329887224083795421615857920728711310761296) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_197 :
    recurrence2QuotientConstant.coeff 197 =
      -((58221218840419683474668299009566732515 * 10 ^ 70 +
        5068685640823962060424499816747389879162006561412368538728681329662926) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_198 :
    recurrence2QuotientConstant.coeff 198 =
      -((1629235014129455671682073024418080283 * 10 ^ 70 +
        3700781165640908679396829454796914925962198480211764280771676648647312) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_199 :
    recurrence2QuotientConstant.coeff 199 =
      ((650679695234379409287250676899551635 * 10 ^ 70 +
        2675087646629905909750746573613167027259554118470516544185992415423420) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_200 :
    recurrence2QuotientConstant.coeff 200 =
      -((62115122420769253729341425744899549 * 10 ^ 70 +
        0737830209242688421867580788898531807356525163340088522746961495122982) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_201 :
    recurrence2QuotientConstant.coeff 201 =
      ((2629816691335603310115444629347417 * 10 ^ 70 +
        3383542467667156174154137921168337887964238452401870972497900607752400) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_202 :
    recurrence2QuotientConstant.coeff 202 =
      ((45652778026540827956412737385129 * 10 ^ 70 +
        1077485080483895918560098305769684500368837150686690209107380296734257) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_203 :
    recurrence2QuotientConstant.coeff 203 =
      -((12442185172085348930000861885536 * 10 ^ 70 +
        2291679809752345739856162874109580175112004676763333829410168098243315) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_204 :
    recurrence2QuotientConstant.coeff 204 =
      ((628268306502756354941488607491 * 10 ^ 70 +
        3588196130142087880935474252511645722427809781404910153444126849428908) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_205 :
    recurrence2QuotientConstant.coeff 205 =
      -((4659316524780720644311108097 * 10 ^ 70 +
        0636803663656747086365197002136338265316884400379085696552200122944113) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_206 :
    recurrence2QuotientConstant.coeff 206 =
      -((833113622632005345442709562 * 10 ^ 70 +
        8462413553372335075004449389555539848405540612818347416691423326699559) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_207 :
    recurrence2QuotientConstant.coeff 207 =
      ((31153439038524456192670448 * 10 ^ 70 +
        6224961971060531304956862959419885150386173329416525808829030804328607) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_208 :
    recurrence2QuotientConstant.coeff 208 =
      ((6821770829024919152514 * 10 ^ 70 +
        6113844795733196162314785547838488405000800170992885230243609590558043) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_209 :
    recurrence2QuotientConstant.coeff 209 =
      -((18700826987024195195132 * 10 ^ 70 +
        4673597098675402406414553985919317822364430451742676743711144134670888) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_210 :
    recurrence2QuotientConstant.coeff 210 =
      ((193931450496828927871 * 10 ^ 70 +
        5225450417719817097079793967401542585637130328706567685437241855269502) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_211 :
    recurrence2QuotientConstant.coeff 211 =
      ((3673517003845062464 * 10 ^ 70 +
        1782139218436916322219669406053827633926700203944634601945150847547485) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_212 :
    recurrence2QuotientConstant.coeff 212 =
      -((44075568224480154 * 10 ^ 70 +
        2720647374415857153275912222364071580303644526668340925244488310706336) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_213 :
    recurrence2QuotientConstant.coeff 213 =
      -((338563055209808 * 10 ^ 70 +
        6455208786886099495445449703607952493756187273688660417336415492884311) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_214 :
    recurrence2QuotientConstant.coeff 214 =
      ((2968614396318 * 10 ^ 70 +
        2225368479737164397374256300582859031001318192999280247089486452405973) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_215 :
    recurrence2QuotientConstant.coeff 215 =
      ((16240503964 * 10 ^ 70 +
        3035830289759231303106232836451904541293230389417568570554662320521799) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_216 :
    recurrence2QuotientConstant.coeff 216 =
      -((74416878 * 10 ^ 70 +
        2239339949912970774980621872233418843276409650833682848429404635099686) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_217 :
    recurrence2QuotientConstant.coeff 217 =
      -((327551 * 10 ^ 70 +
        9780073237673523474922082504259875013487175952385307685588280453578473) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_218 :
    recurrence2QuotientConstant.coeff 218 =
      ((877 * 10 ^ 70 +
        2986500975113664353698119223587184457558104645518480772617254556028554) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_219 :
    recurrence2QuotientConstant.coeff 219 =
      ((2 * 10 ^ 70 +
        6000107174468575299956714803342533322659583290259548992347841665434909) : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_220 :
    recurrence2QuotientConstant.coeff 220 =
      (-58553478584701549446486050408661965899809475543588091231540472571301 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_221 :
    recurrence2QuotientConstant.coeff 221 =
      (-68044546804840794059624694178018393453649629953417256746030094545 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_222 :
    recurrence2QuotientConstant.coeff 222 =
      (175880479702955804719591173843435347371329084635708655851004517 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_223 :
    recurrence2QuotientConstant.coeff 223 =
      (-18806760907251416916704308899116823647924965111289760165078 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_224 :
    recurrence2QuotientConstant.coeff 224 =
      (-86749314121611778643738667856608548195325537057542354408 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_225 :
    recurrence2QuotientConstant.coeff 225 =
      (26484378998984957760670938660242558156645603210807801 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_226 :
    recurrence2QuotientConstant.coeff 226 =
      (1075541355230338967727710535633525200782908180246 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_227 :
    recurrence2QuotientConstant.coeff 227 =
      (-400157255354913850027889312204011703921468887 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_228 :
    recurrence2QuotientConstant.coeff 228 =
      (8025460828076037971253998873963679639567 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_229 :
    recurrence2QuotientConstant.coeff 229 =
      (42041590789136486228117788384782237 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_230 :
    recurrence2QuotientConstant.coeff 230 =
      (-278989539137490472364032405276 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_231 :
    recurrence2QuotientConstant.coeff 231 =
      (60861543156184359369418 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_232 :
    recurrence2QuotientConstant.coeff 232 =
      (565805156706936 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence2QuotientConstant_coeff_233 :
    recurrence2QuotientConstant.coeff 233 =
      (-794588 : ℚ) := by
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  rw [recurrence2B5A5_coeff_high 233 (by norm_num)]
  norm_num

theorem recurrence2QuotientConstant_natDegree_le :
    recurrence2QuotientConstant.natDegree ≤ 233 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n h
  unfold recurrence2QuotientConstant
  rw [Polynomial.coeff_sub]
  rw [recurrence2B5A5_coeff_high n (by omega)]
  rw [recurrence2B4A6_coeff_high n (by omega)]
  norm_num

theorem recurrence2QuotientConstant_coeff_high
    (n : ℕ) (h : 233 < n) :
    recurrence2QuotientConstant.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence2QuotientConstant_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

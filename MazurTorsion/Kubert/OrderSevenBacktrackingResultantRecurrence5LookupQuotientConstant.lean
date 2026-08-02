/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB2A2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB1A3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: quotient constant coefficient subtraction

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence5B2A2_coeff_0
  recurrence5B2A2_coeff_1
  recurrence5B2A2_coeff_2
  recurrence5B2A2_coeff_3
  recurrence5B2A2_coeff_4
  recurrence5B2A2_coeff_5
  recurrence5B2A2_coeff_6
  recurrence5B2A2_coeff_7
  recurrence5B2A2_coeff_8
  recurrence5B2A2_coeff_9
  recurrence5B2A2_coeff_10
  recurrence5B2A2_coeff_11
  recurrence5B2A2_coeff_12
  recurrence5B2A2_coeff_13
  recurrence5B2A2_coeff_14
  recurrence5B2A2_coeff_15
  recurrence5B2A2_coeff_16
  recurrence5B2A2_coeff_17
  recurrence5B2A2_coeff_18
  recurrence5B2A2_coeff_19
  recurrence5B2A2_coeff_20
  recurrence5B2A2_coeff_21
  recurrence5B2A2_coeff_22
  recurrence5B2A2_coeff_23
  recurrence5B2A2_coeff_24
  recurrence5B2A2_coeff_25
  recurrence5B2A2_coeff_26
  recurrence5B2A2_coeff_27
  recurrence5B2A2_coeff_28
  recurrence5B2A2_coeff_29
  recurrence5B2A2_coeff_30
  recurrence5B2A2_coeff_31
  recurrence5B2A2_coeff_32
  recurrence5B2A2_coeff_33
  recurrence5B2A2_coeff_34
  recurrence5B2A2_coeff_35
  recurrence5B2A2_coeff_36
  recurrence5B2A2_coeff_37
  recurrence5B2A2_coeff_38
  recurrence5B2A2_coeff_39
  recurrence5B2A2_coeff_40
  recurrence5B2A2_coeff_41
  recurrence5B2A2_coeff_42
  recurrence5B2A2_coeff_43
  recurrence5B2A2_coeff_44
  recurrence5B2A2_coeff_45
  recurrence5B2A2_coeff_46
  recurrence5B2A2_coeff_47
  recurrence5B2A2_coeff_48
  recurrence5B2A2_coeff_49
  recurrence5B2A2_coeff_50
  recurrence5B2A2_coeff_51
  recurrence5B2A2_coeff_52
  recurrence5B2A2_coeff_53
  recurrence5B2A2_coeff_54
  recurrence5B2A2_coeff_55
  recurrence5B2A2_coeff_56
  recurrence5B2A2_coeff_57
  recurrence5B2A2_coeff_58
  recurrence5B2A2_coeff_59
  recurrence5B2A2_coeff_60
  recurrence5B2A2_coeff_61
  recurrence5B2A2_coeff_62
  recurrence5B2A2_coeff_63

attribute [local simp]
  recurrence5B2A2_coeff_64
  recurrence5B2A2_coeff_65
  recurrence5B2A2_coeff_66
  recurrence5B2A2_coeff_67
  recurrence5B2A2_coeff_68
  recurrence5B2A2_coeff_69
  recurrence5B2A2_coeff_70
  recurrence5B2A2_coeff_71
  recurrence5B2A2_coeff_72
  recurrence5B2A2_coeff_73
  recurrence5B2A2_coeff_74
  recurrence5B2A2_coeff_75
  recurrence5B2A2_coeff_76
  recurrence5B2A2_coeff_77
  recurrence5B2A2_coeff_78
  recurrence5B2A2_coeff_79
  recurrence5B2A2_coeff_80
  recurrence5B2A2_coeff_81
  recurrence5B2A2_coeff_82
  recurrence5B2A2_coeff_83
  recurrence5B2A2_coeff_84
  recurrence5B2A2_coeff_85
  recurrence5B2A2_coeff_86
  recurrence5B2A2_coeff_87
  recurrence5B2A2_coeff_88
  recurrence5B2A2_coeff_89
  recurrence5B2A2_coeff_90
  recurrence5B2A2_coeff_91
  recurrence5B2A2_coeff_92
  recurrence5B2A2_coeff_93
  recurrence5B2A2_coeff_94
  recurrence5B2A2_coeff_95
  recurrence5B2A2_coeff_96
  recurrence5B2A2_coeff_97
  recurrence5B2A2_coeff_98
  recurrence5B2A2_coeff_99
  recurrence5B2A2_coeff_100
  recurrence5B2A2_coeff_101
  recurrence5B2A2_coeff_102
  recurrence5B2A2_coeff_103
  recurrence5B2A2_coeff_104
  recurrence5B2A2_coeff_105
  recurrence5B2A2_coeff_106
  recurrence5B2A2_coeff_107
  recurrence5B2A2_coeff_108
  recurrence5B2A2_coeff_109
  recurrence5B2A2_coeff_110
  recurrence5B2A2_coeff_111
  recurrence5B2A2_coeff_112
  recurrence5B2A2_coeff_113
  recurrence5B2A2_coeff_114
  recurrence5B2A2_coeff_115
  recurrence5B2A2_coeff_116
  recurrence5B2A2_coeff_117
  recurrence5B2A2_coeff_118
  recurrence5B2A2_coeff_119
  recurrence5B2A2_coeff_120
  recurrence5B2A2_coeff_121
  recurrence5B2A2_coeff_122
  recurrence5B2A2_coeff_123
  recurrence5B2A2_coeff_124
  recurrence5B2A2_coeff_125
  recurrence5B2A2_coeff_126
  recurrence5B2A2_coeff_127

attribute [local simp]
  recurrence5B2A2_coeff_128
  recurrence5B2A2_coeff_129
  recurrence5B2A2_coeff_130
  recurrence5B2A2_coeff_131
  recurrence5B2A2_coeff_132
  recurrence5B2A2_coeff_133
  recurrence5B2A2_coeff_134
  recurrence5B2A2_coeff_135
  recurrence5B2A2_coeff_136
  recurrence5B2A2_coeff_137
  recurrence5B2A2_coeff_138
  recurrence5B2A2_coeff_139
  recurrence5B2A2_coeff_140
  recurrence5B2A2_coeff_141
  recurrence5B2A2_coeff_142
  recurrence5B2A2_coeff_143
  recurrence5B2A2_coeff_144
  recurrence5B2A2_coeff_145
  recurrence5B2A2_coeff_146
  recurrence5B2A2_coeff_147
  recurrence5B2A2_coeff_148
  recurrence5B2A2_coeff_149
  recurrence5B2A2_coeff_150
  recurrence5B2A2_coeff_151
  recurrence5B2A2_coeff_152
  recurrence5B2A2_coeff_153
  recurrence5B2A2_coeff_154
  recurrence5B2A2_coeff_155
  recurrence5B2A2_coeff_156
  recurrence5B2A2_coeff_157
  recurrence5B2A2_coeff_158
  recurrence5B2A2_coeff_159
  recurrence5B2A2_coeff_160
  recurrence5B2A2_coeff_161
  recurrence5B2A2_coeff_162
  recurrence5B2A2_coeff_163
  recurrence5B2A2_coeff_164
  recurrence5B2A2_coeff_165
  recurrence5B2A2_coeff_166
  recurrence5B2A2_coeff_167
  recurrence5B2A2_coeff_168
  recurrence5B2A2_coeff_169
  recurrence5B2A2_coeff_170
  recurrence5B2A2_coeff_171
  recurrence5B2A2_coeff_172
  recurrence5B2A2_coeff_173
  recurrence5B2A2_coeff_174
  recurrence5B2A2_coeff_175
  recurrence5B2A2_coeff_176
  recurrence5B2A2_coeff_177
  recurrence5B2A2_coeff_178
  recurrence5B2A2_coeff_179
  recurrence5B2A2_coeff_180
  recurrence5B2A2_coeff_181
  recurrence5B2A2_coeff_182
  recurrence5B2A2_coeff_183
  recurrence5B2A2_coeff_184
  recurrence5B2A2_coeff_185
  recurrence5B2A2_coeff_186
  recurrence5B2A2_coeff_187
  recurrence5B2A2_coeff_188
  recurrence5B2A2_coeff_189
  recurrence5B2A2_coeff_190
  recurrence5B2A2_coeff_191

attribute [local simp]
  recurrence5B2A2_coeff_192
  recurrence5B2A2_coeff_193
  recurrence5B2A2_coeff_194
  recurrence5B2A2_coeff_195
  recurrence5B2A2_coeff_196
  recurrence5B2A2_coeff_197
  recurrence5B2A2_coeff_198
  recurrence5B2A2_coeff_199
  recurrence5B2A2_coeff_200
  recurrence5B2A2_coeff_201
  recurrence5B2A2_coeff_202
  recurrence5B2A2_coeff_203
  recurrence5B2A2_coeff_204
  recurrence5B2A2_coeff_205
  recurrence5B2A2_coeff_206
  recurrence5B2A2_coeff_207
  recurrence5B2A2_coeff_208
  recurrence5B2A2_coeff_209
  recurrence5B2A2_coeff_210
  recurrence5B2A2_coeff_211
  recurrence5B2A2_coeff_212
  recurrence5B2A2_coeff_213
  recurrence5B2A2_coeff_214
  recurrence5B2A2_coeff_215
  recurrence5B2A2_coeff_216
  recurrence5B2A2_coeff_217
  recurrence5B2A2_coeff_218
  recurrence5B2A2_coeff_219
  recurrence5B2A2_coeff_220
  recurrence5B2A2_coeff_221
  recurrence5B2A2_coeff_222
  recurrence5B2A2_coeff_223
  recurrence5B2A2_coeff_224
  recurrence5B2A2_coeff_225
  recurrence5B2A2_coeff_226
  recurrence5B2A2_coeff_227
  recurrence5B2A2_coeff_228
  recurrence5B2A2_coeff_229
  recurrence5B2A2_coeff_230
  recurrence5B2A2_coeff_231
  recurrence5B2A2_coeff_232
  recurrence5B2A2_coeff_233
  recurrence5B2A2_coeff_234
  recurrence5B2A2_coeff_235
  recurrence5B2A2_coeff_236
  recurrence5B2A2_coeff_237
  recurrence5B2A2_coeff_238
  recurrence5B2A2_coeff_239
  recurrence5B2A2_coeff_240
  recurrence5B2A2_coeff_241
  recurrence5B2A2_coeff_242
  recurrence5B2A2_coeff_243
  recurrence5B2A2_coeff_244
  recurrence5B2A2_coeff_245
  recurrence5B2A2_coeff_246
  recurrence5B2A2_coeff_247
  recurrence5B2A2_coeff_248
  recurrence5B2A2_coeff_249
  recurrence5B2A2_coeff_250
  recurrence5B2A2_coeff_251
  recurrence5B2A2_coeff_252
  recurrence5B2A2_coeff_253
  recurrence5B2A2_coeff_254
  recurrence5B2A2_coeff_255

attribute [local simp]
  recurrence5B2A2_coeff_256
  recurrence5B2A2_coeff_257
  recurrence5B2A2_coeff_258
  recurrence5B2A2_coeff_259
  recurrence5B2A2_coeff_260
  recurrence5B2A2_coeff_261
  recurrence5B2A2_coeff_262
  recurrence5B2A2_coeff_263
  recurrence5B2A2_coeff_264
  recurrence5B2A2_coeff_265
  recurrence5B2A2_coeff_266
  recurrence5B2A2_coeff_267
  recurrence5B2A2_coeff_268
  recurrence5B2A2_coeff_269
  recurrence5B2A2_coeff_270
  recurrence5B2A2_coeff_271
  recurrence5B2A2_coeff_272
  recurrence5B2A2_coeff_273
  recurrence5B2A2_coeff_274
  recurrence5B2A2_coeff_275
  recurrence5B2A2_coeff_276
  recurrence5B2A2_coeff_277
  recurrence5B2A2_coeff_278
  recurrence5B2A2_coeff_279
  recurrence5B2A2_coeff_280
  recurrence5B2A2_coeff_281
  recurrence5B2A2_coeff_282
  recurrence5B2A2_coeff_283
  recurrence5B2A2_coeff_284
  recurrence5B2A2_coeff_285
  recurrence5B2A2_coeff_286
  recurrence5B2A2_coeff_287
  recurrence5B2A2_coeff_288
  recurrence5B2A2_coeff_289
  recurrence5B2A2_coeff_290
  recurrence5B2A2_coeff_291
  recurrence5B2A2_coeff_292
  recurrence5B2A2_coeff_293
  recurrence5B2A2_coeff_294
  recurrence5B2A2_coeff_295
  recurrence5B2A2_coeff_296
  recurrence5B2A2_coeff_297
  recurrence5B2A2_coeff_298
  recurrence5B2A2_coeff_299
  recurrence5B2A2_coeff_300
  recurrence5B2A2_coeff_301
  recurrence5B2A2_coeff_302
  recurrence5B2A2_coeff_303
  recurrence5B2A2_coeff_304
  recurrence5B2A2_coeff_305
  recurrence5B2A2_coeff_306
  recurrence5B2A2_coeff_307
  recurrence5B2A2_coeff_308
  recurrence5B2A2_coeff_309
  recurrence5B2A2_coeff_310
  recurrence5B2A2_coeff_311
  recurrence5B2A2_coeff_312
  recurrence5B2A2_coeff_313
  recurrence5B1A3_coeff_0
  recurrence5B1A3_coeff_1
  recurrence5B1A3_coeff_2
  recurrence5B1A3_coeff_3
  recurrence5B1A3_coeff_4
  recurrence5B1A3_coeff_5

attribute [local simp]
  recurrence5B1A3_coeff_6
  recurrence5B1A3_coeff_7
  recurrence5B1A3_coeff_8
  recurrence5B1A3_coeff_9
  recurrence5B1A3_coeff_10
  recurrence5B1A3_coeff_11
  recurrence5B1A3_coeff_12
  recurrence5B1A3_coeff_13
  recurrence5B1A3_coeff_14
  recurrence5B1A3_coeff_15
  recurrence5B1A3_coeff_16
  recurrence5B1A3_coeff_17
  recurrence5B1A3_coeff_18
  recurrence5B1A3_coeff_19
  recurrence5B1A3_coeff_20
  recurrence5B1A3_coeff_21
  recurrence5B1A3_coeff_22
  recurrence5B1A3_coeff_23
  recurrence5B1A3_coeff_24
  recurrence5B1A3_coeff_25
  recurrence5B1A3_coeff_26
  recurrence5B1A3_coeff_27
  recurrence5B1A3_coeff_28
  recurrence5B1A3_coeff_29
  recurrence5B1A3_coeff_30
  recurrence5B1A3_coeff_31
  recurrence5B1A3_coeff_32
  recurrence5B1A3_coeff_33
  recurrence5B1A3_coeff_34
  recurrence5B1A3_coeff_35
  recurrence5B1A3_coeff_36
  recurrence5B1A3_coeff_37
  recurrence5B1A3_coeff_38
  recurrence5B1A3_coeff_39
  recurrence5B1A3_coeff_40
  recurrence5B1A3_coeff_41
  recurrence5B1A3_coeff_42
  recurrence5B1A3_coeff_43
  recurrence5B1A3_coeff_44
  recurrence5B1A3_coeff_45
  recurrence5B1A3_coeff_46
  recurrence5B1A3_coeff_47
  recurrence5B1A3_coeff_48
  recurrence5B1A3_coeff_49
  recurrence5B1A3_coeff_50
  recurrence5B1A3_coeff_51
  recurrence5B1A3_coeff_52
  recurrence5B1A3_coeff_53
  recurrence5B1A3_coeff_54
  recurrence5B1A3_coeff_55
  recurrence5B1A3_coeff_56
  recurrence5B1A3_coeff_57
  recurrence5B1A3_coeff_58
  recurrence5B1A3_coeff_59
  recurrence5B1A3_coeff_60
  recurrence5B1A3_coeff_61
  recurrence5B1A3_coeff_62
  recurrence5B1A3_coeff_63
  recurrence5B1A3_coeff_64
  recurrence5B1A3_coeff_65
  recurrence5B1A3_coeff_66
  recurrence5B1A3_coeff_67
  recurrence5B1A3_coeff_68
  recurrence5B1A3_coeff_69

attribute [local simp]
  recurrence5B1A3_coeff_70
  recurrence5B1A3_coeff_71
  recurrence5B1A3_coeff_72
  recurrence5B1A3_coeff_73
  recurrence5B1A3_coeff_74
  recurrence5B1A3_coeff_75
  recurrence5B1A3_coeff_76
  recurrence5B1A3_coeff_77
  recurrence5B1A3_coeff_78
  recurrence5B1A3_coeff_79
  recurrence5B1A3_coeff_80
  recurrence5B1A3_coeff_81
  recurrence5B1A3_coeff_82
  recurrence5B1A3_coeff_83
  recurrence5B1A3_coeff_84
  recurrence5B1A3_coeff_85
  recurrence5B1A3_coeff_86
  recurrence5B1A3_coeff_87
  recurrence5B1A3_coeff_88
  recurrence5B1A3_coeff_89
  recurrence5B1A3_coeff_90
  recurrence5B1A3_coeff_91
  recurrence5B1A3_coeff_92
  recurrence5B1A3_coeff_93
  recurrence5B1A3_coeff_94
  recurrence5B1A3_coeff_95
  recurrence5B1A3_coeff_96
  recurrence5B1A3_coeff_97
  recurrence5B1A3_coeff_98
  recurrence5B1A3_coeff_99
  recurrence5B1A3_coeff_100
  recurrence5B1A3_coeff_101
  recurrence5B1A3_coeff_102
  recurrence5B1A3_coeff_103
  recurrence5B1A3_coeff_104
  recurrence5B1A3_coeff_105
  recurrence5B1A3_coeff_106
  recurrence5B1A3_coeff_107
  recurrence5B1A3_coeff_108
  recurrence5B1A3_coeff_109
  recurrence5B1A3_coeff_110
  recurrence5B1A3_coeff_111
  recurrence5B1A3_coeff_112
  recurrence5B1A3_coeff_113
  recurrence5B1A3_coeff_114
  recurrence5B1A3_coeff_115
  recurrence5B1A3_coeff_116
  recurrence5B1A3_coeff_117
  recurrence5B1A3_coeff_118
  recurrence5B1A3_coeff_119
  recurrence5B1A3_coeff_120
  recurrence5B1A3_coeff_121
  recurrence5B1A3_coeff_122
  recurrence5B1A3_coeff_123
  recurrence5B1A3_coeff_124
  recurrence5B1A3_coeff_125
  recurrence5B1A3_coeff_126
  recurrence5B1A3_coeff_127
  recurrence5B1A3_coeff_128
  recurrence5B1A3_coeff_129
  recurrence5B1A3_coeff_130
  recurrence5B1A3_coeff_131
  recurrence5B1A3_coeff_132
  recurrence5B1A3_coeff_133

attribute [local simp]
  recurrence5B1A3_coeff_134
  recurrence5B1A3_coeff_135
  recurrence5B1A3_coeff_136
  recurrence5B1A3_coeff_137
  recurrence5B1A3_coeff_138
  recurrence5B1A3_coeff_139
  recurrence5B1A3_coeff_140
  recurrence5B1A3_coeff_141
  recurrence5B1A3_coeff_142
  recurrence5B1A3_coeff_143
  recurrence5B1A3_coeff_144
  recurrence5B1A3_coeff_145
  recurrence5B1A3_coeff_146
  recurrence5B1A3_coeff_147
  recurrence5B1A3_coeff_148
  recurrence5B1A3_coeff_149
  recurrence5B1A3_coeff_150
  recurrence5B1A3_coeff_151
  recurrence5B1A3_coeff_152
  recurrence5B1A3_coeff_153
  recurrence5B1A3_coeff_154
  recurrence5B1A3_coeff_155
  recurrence5B1A3_coeff_156
  recurrence5B1A3_coeff_157
  recurrence5B1A3_coeff_158
  recurrence5B1A3_coeff_159
  recurrence5B1A3_coeff_160
  recurrence5B1A3_coeff_161
  recurrence5B1A3_coeff_162
  recurrence5B1A3_coeff_163
  recurrence5B1A3_coeff_164
  recurrence5B1A3_coeff_165
  recurrence5B1A3_coeff_166
  recurrence5B1A3_coeff_167
  recurrence5B1A3_coeff_168
  recurrence5B1A3_coeff_169
  recurrence5B1A3_coeff_170
  recurrence5B1A3_coeff_171
  recurrence5B1A3_coeff_172
  recurrence5B1A3_coeff_173
  recurrence5B1A3_coeff_174
  recurrence5B1A3_coeff_175
  recurrence5B1A3_coeff_176
  recurrence5B1A3_coeff_177
  recurrence5B1A3_coeff_178
  recurrence5B1A3_coeff_179
  recurrence5B1A3_coeff_180
  recurrence5B1A3_coeff_181
  recurrence5B1A3_coeff_182
  recurrence5B1A3_coeff_183
  recurrence5B1A3_coeff_184
  recurrence5B1A3_coeff_185
  recurrence5B1A3_coeff_186
  recurrence5B1A3_coeff_187
  recurrence5B1A3_coeff_188
  recurrence5B1A3_coeff_189
  recurrence5B1A3_coeff_190
  recurrence5B1A3_coeff_191
  recurrence5B1A3_coeff_192
  recurrence5B1A3_coeff_193
  recurrence5B1A3_coeff_194
  recurrence5B1A3_coeff_195
  recurrence5B1A3_coeff_196
  recurrence5B1A3_coeff_197

attribute [local simp]
  recurrence5B1A3_coeff_198
  recurrence5B1A3_coeff_199
  recurrence5B1A3_coeff_200
  recurrence5B1A3_coeff_201
  recurrence5B1A3_coeff_202
  recurrence5B1A3_coeff_203
  recurrence5B1A3_coeff_204
  recurrence5B1A3_coeff_205
  recurrence5B1A3_coeff_206
  recurrence5B1A3_coeff_207
  recurrence5B1A3_coeff_208
  recurrence5B1A3_coeff_209
  recurrence5B1A3_coeff_210
  recurrence5B1A3_coeff_211
  recurrence5B1A3_coeff_212
  recurrence5B1A3_coeff_213
  recurrence5B1A3_coeff_214
  recurrence5B1A3_coeff_215
  recurrence5B1A3_coeff_216
  recurrence5B1A3_coeff_217
  recurrence5B1A3_coeff_218
  recurrence5B1A3_coeff_219
  recurrence5B1A3_coeff_220
  recurrence5B1A3_coeff_221
  recurrence5B1A3_coeff_222
  recurrence5B1A3_coeff_223
  recurrence5B1A3_coeff_224
  recurrence5B1A3_coeff_225
  recurrence5B1A3_coeff_226
  recurrence5B1A3_coeff_227
  recurrence5B1A3_coeff_228
  recurrence5B1A3_coeff_229
  recurrence5B1A3_coeff_230
  recurrence5B1A3_coeff_231
  recurrence5B1A3_coeff_232
  recurrence5B1A3_coeff_233
  recurrence5B1A3_coeff_234
  recurrence5B1A3_coeff_235
  recurrence5B1A3_coeff_236
  recurrence5B1A3_coeff_237
  recurrence5B1A3_coeff_238
  recurrence5B1A3_coeff_239
  recurrence5B1A3_coeff_240
  recurrence5B1A3_coeff_241
  recurrence5B1A3_coeff_242
  recurrence5B1A3_coeff_243
  recurrence5B1A3_coeff_244
  recurrence5B1A3_coeff_245
  recurrence5B1A3_coeff_246
  recurrence5B1A3_coeff_247
  recurrence5B1A3_coeff_248
  recurrence5B1A3_coeff_249
  recurrence5B1A3_coeff_250
  recurrence5B1A3_coeff_251
  recurrence5B1A3_coeff_252
  recurrence5B1A3_coeff_253
  recurrence5B1A3_coeff_254
  recurrence5B1A3_coeff_255
  recurrence5B1A3_coeff_256
  recurrence5B1A3_coeff_257
  recurrence5B1A3_coeff_258
  recurrence5B1A3_coeff_259
  recurrence5B1A3_coeff_260
  recurrence5B1A3_coeff_261

attribute [local simp]
  recurrence5B1A3_coeff_262
  recurrence5B1A3_coeff_263
  recurrence5B1A3_coeff_264
  recurrence5B1A3_coeff_265
  recurrence5B1A3_coeff_266
  recurrence5B1A3_coeff_267
  recurrence5B1A3_coeff_268
  recurrence5B1A3_coeff_269
  recurrence5B1A3_coeff_270
  recurrence5B1A3_coeff_271
  recurrence5B1A3_coeff_272
  recurrence5B1A3_coeff_273
  recurrence5B1A3_coeff_274
  recurrence5B1A3_coeff_275
  recurrence5B1A3_coeff_276
  recurrence5B1A3_coeff_277
  recurrence5B1A3_coeff_278
  recurrence5B1A3_coeff_279
  recurrence5B1A3_coeff_280
  recurrence5B1A3_coeff_281
  recurrence5B1A3_coeff_282
  recurrence5B1A3_coeff_283
  recurrence5B1A3_coeff_284
  recurrence5B1A3_coeff_285
  recurrence5B1A3_coeff_286
  recurrence5B1A3_coeff_287
  recurrence5B1A3_coeff_288
  recurrence5B1A3_coeff_289
  recurrence5B1A3_coeff_290
  recurrence5B1A3_coeff_291
  recurrence5B1A3_coeff_292
  recurrence5B1A3_coeff_293
  recurrence5B1A3_coeff_294
  recurrence5B1A3_coeff_295
  recurrence5B1A3_coeff_296
  recurrence5B1A3_coeff_297
  recurrence5B1A3_coeff_298
  recurrence5B1A3_coeff_299
  recurrence5B1A3_coeff_300
  recurrence5B1A3_coeff_301
  recurrence5B1A3_coeff_302
  recurrence5B1A3_coeff_303
  recurrence5B1A3_coeff_304
  recurrence5B1A3_coeff_305
  recurrence5B1A3_coeff_306
  recurrence5B1A3_coeff_307
  recurrence5B1A3_coeff_308
  recurrence5B1A3_coeff_309
  recurrence5B1A3_coeff_310
  recurrence5B1A3_coeff_311
  recurrence5B1A3_coeff_312
  recurrence5B1A3_coeff_313

theorem recurrence5QuotientConstant_coeff_0 :
    recurrence5QuotientConstant.coeff 0 =
      (7089163485397076864120412862377044524896337959722123147124301376024576 : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_1 :
    recurrence5QuotientConstant.coeff 1 =
      ((1815 * 10 ^ 70 +
        8210903917181891086173872843392513154293197564232544018601888997974272) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_2 :
    recurrence5QuotientConstant.coeff 2 =
      -((33572663 * 10 ^ 70 +
        4058260289794836726874443359552267351830874108412971594755077343577200) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_3 :
    recurrence5QuotientConstant.coeff 3 =
      ((106745754319 * 10 ^ 70 +
        0809390647477528775464729510339368529078202722564638648544477590031952) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_4 :
    recurrence5QuotientConstant.coeff 4 =
      -((205590904342716 * 10 ^ 70 +
        2875713141907325785880073177468521403332597411228149922014718551737876) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_5 :
    recurrence5QuotientConstant.coeff 5 =
      ((279345531397135211 * 10 ^ 70 +
        5539025840686118285139790905883242538017400152510596073368474032142436) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_6 :
    recurrence5QuotientConstant.coeff 6 =
      -((236317930566366882739 * 10 ^ 70 +
        1200577207758085240984476927481378102658374755078978484467047917881000) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_7 :
    recurrence5QuotientConstant.coeff 7 =
      ((110279120890777390959455 * 10 ^ 70 +
        6341996166127405797919191062492684624805338669250804256200097373897396) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_8 :
    recurrence5QuotientConstant.coeff 8 =
      -((7779484646000897491196047 * 10 ^ 70 +
        5214773275448088977867876799293536737508425669202147060772337340849476) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_9 :
    recurrence5QuotientConstant.coeff 9 =
      -((25645040697003565764066432267 * 10 ^ 70 +
        9471108284226318742173918777234045258162235262641097543223714450309320) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_10 :
    recurrence5QuotientConstant.coeff 10 =
      ((18843035294326309279761580409585 * 10 ^ 70 +
        0628635343248472286658067198282495698134531864012113135374971545088312) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_11 :
    recurrence5QuotientConstant.coeff 11 =
      -((7007767748801341379932668566592026 * 10 ^ 70 +
        0978198206458666576254416797525714536440906024861930997737178560880980) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_12 :
    recurrence5QuotientConstant.coeff 12 =
      ((1427157114305151758668951165035610991 * 10 ^ 70 +
        2852314999891991975116261757821096241425785476415400055908542369959440) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_13 :
    recurrence5QuotientConstant.coeff 13 =
      -((113521210006494882425813411099152294512 * 10 ^ 70 +
        5316240485278155641191065765209931826195926114891911623267750523159328) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_14 :
    recurrence5QuotientConstant.coeff 14 =
      ((38620015565220775862885250740665873772879 * 10 ^ 70 +
        6071919520841775451759687950034893725801785889102278863824307722952407) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_15 :
    recurrence5QuotientConstant.coeff 15 =
      -((63943106150336316823954527976623129944538848 * 10 ^ 70 +
        1215799208218529149485612397127110037988609408593018418735810662791579) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_16 :
    recurrence5QuotientConstant.coeff 16 =
      ((43597002189457151890783112602717904662936958635 * 10 ^ 70 +
        9156552596543060019989334517435930103893127847008385085434105651810616) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_17 :
    recurrence5QuotientConstant.coeff 17 =
      -((18699863354870435516934483147653210444695046199179 * 10 ^ 70 +
        3585278542331805179609761373637335364151080547875044551743032733099958) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_18 :
    recurrence5QuotientConstant.coeff 18 =
      ((5872408270339965117023046924154872387190725089525663 * 10 ^ 70 +
        7944794487162347973674233029822134223365415073809435401652666404677313) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_19 :
    recurrence5QuotientConstant.coeff 19 =
      -((1434618783587662774380990883150156527611448779387010280 * 10 ^ 70 +
        2146210495637478508458527496124256651141425254197607014757508847888682) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_20 :
    recurrence5QuotientConstant.coeff 20 =
      ((278889291402329777920627446824156475312464458015371933861 * 10 ^ 70 +
        5346411259787088989543614985018124178115269345869335526307589848722942) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_21 :
    recurrence5QuotientConstant.coeff 21 =
      -((42911792408846977047560880860499301313565617739201449990671 * 10 ^ 70 +
        6007356030046757526303561871696390313616271129656743941816761889860934) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_22 :
    recurrence5QuotientConstant.coeff 22 =
      ((4961103656944323569074098609399623014746481939219978204142605 * 10 ^ 70 +
        3435945073479714454819403135769251194386582844672009481063462751767007) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_23 :
    recurrence5QuotientConstant.coeff 23 =
      -((339285075890683504467961885977991095987503711620340098768658340 * 10 ^ 70 +
        8447707425570504754219640867270228861762884034172628693731845846993372) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_24 :
    recurrence5QuotientConstant.coeff 24 =
      -((15289170644557532413748077088565016246385158591954502393465197236 * 10 ^ 70 +
        9892281528837080674641803464330423975478812916205495155000824931900823) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_25 :
    recurrence5QuotientConstant.coeff 25 =
      ((9735634626336926919793347204064633702835843636563879688974210204826 * 10 ^ 70 +
        8915691030098791535935117215463259409683850134340298708759373332787911) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_26 :
    recurrence5QuotientConstant.coeff 26 =
      -((1957289327635559301408620508547203104804287880466326990618280208563949 * 10 ^ 70 +
        6964619904648526039521292768145284626928633784346060368101501890258923) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_27 :
    recurrence5QuotientConstant.coeff 27 =
      (((28 * 10 ^ 70 +
        3354532383394747832634739054901281932169814267579870349583195792749381) * 10 ^ 70 +
        0741266643691808963229451517256548777646447145103502176507270906976363) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_28 :
    recurrence5QuotientConstant.coeff 28 =
      -(((3350 * 10 ^ 70 +
        3245154365441401651918785938996605733162723893938910210313197848774673) * 10 ^ 70 +
        3810927898750137652622878567121093663197845028246425553001955815092715) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_29 :
    recurrence5QuotientConstant.coeff 29 =
      (((338951 * 10 ^ 70 +
        3993501902266350161023465285318593171734369669519262834219417545615155) * 10 ^ 70 +
        5150164096112051689327408572491648346676529775081112705694447223839243) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_30 :
    recurrence5QuotientConstant.coeff 30 =
      -(((30037876 * 10 ^ 70 +
        6556651491334297463323080307653462949568949243314957953812489722460782) * 10 ^ 70 +
        8832816795259547019967059451264662345661052157117158907221269335619780) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_31 :
    recurrence5QuotientConstant.coeff 31 =
      (((2364816693 * 10 ^ 70 +
        5641619951494473296257410143329795378164068617881309339741991321003393) * 10 ^ 70 +
        3526155438683758815536666152939154662120581445236729371800922124712632) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_32 :
    recurrence5QuotientConstant.coeff 32 =
      -(((166967111820 * 10 ^ 70 +
        4601036588314757016331363423703344540615573577704240059659873674803513) * 10 ^ 70 +
        2637937957251501882260775050851698209765673584388062649187308165074064) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_33 :
    recurrence5QuotientConstant.coeff 33 =
      (((10645104712918 * 10 ^ 70 +
        3762611621823577602328342071043452913211881525655695907482379650417509) * 10 ^ 70 +
        4393444691203949393446381305420670625228990319290213543101546845837515) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_34 :
    recurrence5QuotientConstant.coeff 34 =
      -(((616073918243678 * 10 ^ 70 +
        4285411159919953573880703560019258969864536833803046268128141108304596) * 10 ^ 70 +
        6781060523893994433020334194615542710615811199310847866097102221082979) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_35 :
    recurrence5QuotientConstant.coeff 35 =
      (((32499945734777759 * 10 ^ 70 +
        5339953356133242349623866155607681887740382899453570289885590353858596) * 10 ^ 70 +
        6064885120894554423217490551520151475570241495124460440479678640238278) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_36 :
    recurrence5QuotientConstant.coeff 36 =
      -(((1568031424364500039 * 10 ^ 70 +
        1520956775157663159216378751715729986045382489368982797693843684366782) * 10 ^ 70 +
        3279295074141884634884308114299559215188465286564732322082497181921466) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_37 :
    recurrence5QuotientConstant.coeff 37 =
      (((69379306445243778151 * 10 ^ 70 +
        1514313261645289820938347521883978446303499095757883204994962479478896) * 10 ^ 70 +
        0591602569882407605787596608134397674905550061801234321595491125017927) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_38 :
    recurrence5QuotientConstant.coeff 38 =
      -(((2821328157197929187645 * 10 ^ 70 +
        2489168262003825426710419395939045722478936504899522192248192532109931) * 10 ^ 70 +
        3815019663348411707149945772478171681248934792741783352910294881140581) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_39 :
    recurrence5QuotientConstant.coeff 39 =
      (((105621101690471837673807 * 10 ^ 70 +
        4998026557702653049772246390686622013963975525002849450840096318021364) * 10 ^ 70 +
        7085504447534527435734372124439571381582322128107239584819794063718393) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_40 :
    recurrence5QuotientConstant.coeff 40 =
      -(((3644342436828086497985816 * 10 ^ 70 +
        4935715354131457312886184483567405532978382271507388067737586021388855) * 10 ^ 70 +
        1114256774034435555087205302924302483959221633498969613095264782290171) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_41 :
    recurrence5QuotientConstant.coeff 41 =
      (((115957556495357638317275523 * 10 ^ 70 +
        2703538587804385484769195241410733058433397871634843448052399922323663) * 10 ^ 70 +
        2869828489483828873342281508219507513113269328373854900523523787017223) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_42 :
    recurrence5QuotientConstant.coeff 42 =
      -(((3401790647137321878409230040 * 10 ^ 70 +
        9594875791861740784267157791564921671376312769776750417775509590876910) * 10 ^ 70 +
        5159533801321949811597808384486584231945049910694770576070971655100174) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_43 :
    recurrence5QuotientConstant.coeff 43 =
      (((91900808989752817581963047239 * 10 ^ 70 +
        5307532205700805983113190070480776512055730537554409789639639369479515) * 10 ^ 70 +
        1533263536061312670667345979358246479195388015887749569257508612300352) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_44 :
    recurrence5QuotientConstant.coeff 44 =
      -(((2280054013345846710524928644168 * 10 ^ 70 +
        7579364415142630890007713816946624960403990714214193737550793541704807) * 10 ^ 70 +
        6906865220605909763493806618691036151139715623244663559875824863583568) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_45 :
    recurrence5QuotientConstant.coeff 45 =
      (((51677925697432868231446515873985 * 10 ^ 70 +
        8506826559278603892111205898459004657101119376611885513798986485922368) * 10 ^ 70 +
        6960966672521957430355872073356713555456440534113773511104719007001869) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_46 :
    recurrence5QuotientConstant.coeff 46 =
      -(((1059570902250293674470166957550710 * 10 ^ 70 +
        0978232501098478971852605432468454452973059850107696347134513510281970) * 10 ^ 70 +
        9929012191083722238672288780757690646925178923474911449338322467148455) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_47 :
    recurrence5QuotientConstant.coeff 47 =
      (((19275532480486850938212988919180907 * 10 ^ 70 +
        3003642086956785276774911590334272428612004129582991326406005209569559) * 10 ^ 70 +
        8735936578411340629672443257902100672468595022589557380960251246172353) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_48 :
    recurrence5QuotientConstant.coeff 48 =
      -(((297873429989805706568621582328358247 * 10 ^ 70 +
        1042823680217126527733409811668070810802737281922560871554753589154855) * 10 ^ 70 +
        3678444710559228159563770648003372881567042861070570046575448437511602) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_49 :
    recurrence5QuotientConstant.coeff 49 =
      (((3434609732146300012308428898784516904 * 10 ^ 70 +
        4643690125742693127356195156005572592813185619189309890194087376862002) * 10 ^ 70 +
        0271291889652507122760439520149681831683837596760527741845578859948187) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_50 :
    recurrence5QuotientConstant.coeff 50 =
      -(((10822547851867706297351939332304479109 * 10 ^ 70 +
        8650388251380399146852080118476340117513851024806602078903992275053895) * 10 ^ 70 +
        9478870639260775376489186517926889331514128616237943992447780413756367) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_51 :
    recurrence5QuotientConstant.coeff 51 =
      -(((898639700359205338986207684878624269267 * 10 ^ 70 +
        6160892080956159268393710189098528623658229770792086066128656385973389) * 10 ^ 70 +
        2215273968514400183611753054869355660623850661645032076250348200952885) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_52 :
    recurrence5QuotientConstant.coeff 52 =
      (((36025879942782176827451602172184157990862 * 10 ^ 70 +
        4555024549955365932342153233692426751195076852994021221712138488228101) * 10 ^ 70 +
        1491481387858041945699063612821396970242976680450581318684475598434390) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_53 :
    recurrence5QuotientConstant.coeff 53 =
      -(((953143934932040785374187530549381128490916 * 10 ^ 70 +
        7259577270661456400703467858603131821367220456141396858473061673498143) * 10 ^ 70 +
        4256718027765712610866630703980787158759706283796484111322282665493632) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_54 :
    recurrence5QuotientConstant.coeff 54 =
      (((20912707736234395370276683068735181677361995 * 10 ^ 70 +
        0535779969710084220883761300329899913658087980753555797116209864126272) * 10 ^ 70 +
        0731450391731088979118358536182761288251730187469604636701692780232597) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_55 :
    recurrence5QuotientConstant.coeff 55 =
      -(((406000475429960407885497614428804128598405881 * 10 ^ 70 +
        9221947217600127159260906486244055451675143520612165871837514054873707) * 10 ^ 70 +
        3537998263769817209916853645097089819943936340512104811965266476369222) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_56 :
    recurrence5QuotientConstant.coeff 56 =
      (((7173307400294625833339501325692920931140615376 * 10 ^ 70 +
        2105051214483010182911996070130684246548032112671008964162778137408830) * 10 ^ 70 +
        1178215533804510544231280331525826804735805364630938317266139202692245) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_57 :
    recurrence5QuotientConstant.coeff 57 =
      -(((117091122932042963495906797652194505378952364984 * 10 ^ 70 +
        4374917139411998772833211329401834065322514473889083856585268970158798) * 10 ^ 70 +
        6914965870830932337588328159552957090754449696999551049891784004856775) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_58 :
    recurrence5QuotientConstant.coeff 58 =
      (((1782095411413240973950223896923580306491196655180 * 10 ^ 70 +
        8713655909267161480279489184080941905929950396052775896371836252593607) * 10 ^ 70 +
        6739310985248044927245837345408222837110220466673119090565913300896286) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_59 :
    recurrence5QuotientConstant.coeff 59 =
      -(((25445722499046770331122109608594161776383829049709 * 10 ^ 70 +
        9292644223269980272924648517859668525543866519639141997320924653757044) * 10 ^ 70 +
        9852267541396778090179196079073387863331273775936444755214164583465617) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_60 :
    recurrence5QuotientConstant.coeff 60 =
      (((342370954044521347906935022186738424557368451793381 * 10 ^ 70 +
        9007972483079574749092104566221124047945344359124720272957419335378950) * 10 ^ 70 +
        1411399684552594898019054481203126641438736329699308331967942544493539) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_61 :
    recurrence5QuotientConstant.coeff 61 =
      -(((4355465894897126335666553718691631508335693804654012 * 10 ^ 70 +
        6928047017176954303206049443323212850624044153014102486639648786624892) * 10 ^ 70 +
        7890989981322124296253210982856487762311731951097119491212553100789104) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_62 :
    recurrence5QuotientConstant.coeff 62 =
      (((52526901343957941440226650745072623569681865460524113 * 10 ^ 70 +
        9060185664433862132709113952364042129329432121464952158047448218304002) * 10 ^ 70 +
        1162061439924737054222020836382706684752911651226303616501108619651454) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_63 :
    recurrence5QuotientConstant.coeff 63 =
      -(((601844475154625778795373584823249917857152058495550010 * 10 ^ 70 +
        4299871974483816012547779264281887961676037297041796429213978319401637) * 10 ^ 70 +
        0560809594808272397532792957886168446992509761012778381124597378580706) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_64 :
    recurrence5QuotientConstant.coeff 64 =
      (((6563561709336878451685060975141380027674940433618532335 * 10 ^ 70 +
        9913913855238421092380641472463089438469321410317744134001127916064625) * 10 ^ 70 +
        7094147220425127094347281566851071955073366602188637749077988569509916) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_65 :
    recurrence5QuotientConstant.coeff 65 =
      -(((68239460395381492810455458323749916446942595519198757113 * 10 ^ 70 +
        0724949249663603694957127831153089650931472072138739561840187805979266) * 10 ^ 70 +
        0086292370449527463318375755206375097205975758287691429040478189478558) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_66 :
    recurrence5QuotientConstant.coeff 66 =
      (((677293543885520200494450101973910880307935905573826136540 * 10 ^ 70 +
        9071064971265275561819702623249738022685057390650159331592418473924400) * 10 ^ 70 +
        4270017098684816340706158530822551478848765897769775261509557680723193) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_67 :
    recurrence5QuotientConstant.coeff 67 =
      -(((6425445521935629166196727612346087321850127046825086700328 * 10 ^ 70 +
        2740458949268423298370216455933453018630274047198415377164894132738311) * 10 ^ 70 +
        0845222882929990124273837789870895726510189405861432557218560346798810) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_68 :
    recurrence5QuotientConstant.coeff 68 =
      (((58331373893806393089872825625251625691520766765827037725156 * 10 ^ 70 +
        9354586100656187579364218236090929018969159682355054055173965562133667) * 10 ^ 70 +
        8414141669244214171243274066666166307967318241505306151136632822521653) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_69 :
    recurrence5QuotientConstant.coeff 69 =
      -(((507246615443248390114843554268085483280322606047772134077550 * 10 ^ 70 +
        5544048802879971811052276074263817431341747679402965398306789864904007) * 10 ^ 70 +
        2763170755235596278494281417488444648482341547459313905929798387330045) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_70 :
    recurrence5QuotientConstant.coeff 70 =
      (((4229258720091275164239724411765565331650796255243987504496190 * 10 ^ 70 +
        2589158639730731188725665474215756200987354402630233852363012881095376) * 10 ^ 70 +
        1570371346163632057674399266248029471548703806148831270401887796792029) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_71 :
    recurrence5QuotientConstant.coeff 71 =
      -(((33839029552475911912516079205707266907571820708667016709223264 * 10 ^ 70 +
        7578184578899716019479791362423993852837538250168470670821483815943454) * 10 ^ 70 +
        0404259448543573041354303681594569017997418980638862277581495371337522) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_72 :
    recurrence5QuotientConstant.coeff 72 =
      (((260036899626453709955587842576652940988941758140039207971388411 * 10 ^ 70 +
        3883318329667702040353758111223449504958102022335455532707597543853015) * 10 ^ 70 +
        4670272414441779694190792314896316966172850324000124032053324531016842) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_73 :
    recurrence5QuotientConstant.coeff 73 =
      -(((1920649713456704621089870580972670336621695822442391351757490531 * 10 ^ 70 +
        5631841325115507862442613996008955967179955165499898585037162079154749) * 10 ^ 70 +
        2626321005414547083929192666249321343383463544577103609160767309557544) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_74 :
    recurrence5QuotientConstant.coeff 74 =
      (((13644906554576851275277661657081041216159119362723999420139211300 * 10 ^ 70 +
        7257354815055299344436979767641967257119478505398583463361030175699517) * 10 ^ 70 +
        0856843101128511886270188571729910839259600494347954738523152191708618) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_75 :
    recurrence5QuotientConstant.coeff 75 =
      -(((93303482508481888370362240358028468134902921755338812330270627656 * 10 ^ 70 +
        8121881759253433547361521497759619530698049173495083117672294573582243) * 10 ^ 70 +
        1575583254581811550877597611771002672201221816375123448633353622786704) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_76 :
    recurrence5QuotientConstant.coeff 76 =
      (((614483204080696066336933337532486514777328481919367977124583682296 * 10 ^ 70 +
        3964329919207382496926665669972643724693528822262214500798819288105082) * 10 ^ 70 +
        1590796426410061919716139700429968512393600878159233309901177395841184) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_77 :
    recurrence5QuotientConstant.coeff 77 =
      -(((3900073529277368589532632294125045721793795284268575027814164062755 * 10 ^ 70 +
        1521233671178144298710082205819697976128384684500168879534197985711478) * 10 ^ 70 +
        3646665630273331344310377574851179494908486837306769090427088729890816) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_78 :
    recurrence5QuotientConstant.coeff 78 =
      (((23869256407094328530679302748115639894837803061915421653866278663494 * 10 ^ 70 +
        5295671912631666630990104162637761157854995236199421008856961924298693) * 10 ^ 70 +
        8776472139662874245499538862873431415086188225814141146674665129633977) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_79 :
    recurrence5QuotientConstant.coeff 79 =
      -(((140944774745836310660292726705590790626036571843701730591050372851533 * 10 ^ 70 +
        1805224539020923596266307682664776393676246362466556261886857673799974) * 10 ^ 70 +
        2988926641256769464753788724398748943843390998369664602224544439829757) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_80 :
    recurrence5QuotientConstant.coeff 80 =
      (((803401413312527114678375409624815255153345190527857920921303962829114 * 10 ^ 70 +
        9091130973139607625418750525110814548144936350251991454702697612101516) * 10 ^ 70 +
        7723430206024291256549641591677764088634426541227475240478618843342095) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_81 :
    recurrence5QuotientConstant.coeff 81 =
      -(((4422917576974454417939364683378595926175035584481095918044363401882623 * 10 ^ 70 +
        6988135605082598427530502884958131424149782264390200262402499320712682) * 10 ^ 70 +
        5678564088229113901401130681164696310561707354450952638574940346684069) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_82 :
    recurrence5QuotientConstant.coeff 82 =
      ((((2 * 10 ^ 70 +
        3528113886291448119255921260785726138048182721286536354268133167392111) * 10 ^ 70 +
        1613980176830202547790341543557410686012970308464031941385002795124868) * 10 ^ 70 +
        2216892673018746838298513723413468018458899954628690618896275657490434) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_83 :
    recurrence5QuotientConstant.coeff 83 =
      -((((12 * 10 ^ 70 +
        0995044456962886634778300458671442111536215071694856646887603946053871) * 10 ^ 70 +
        0767199901822093762020213666759194837912556684376124571967937477635049) * 10 ^ 70 +
        5621921955039784143736157246237590014653927684626816051146933287067987) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_84 :
    recurrence5QuotientConstant.coeff 84 =
      ((((60 * 10 ^ 70 +
        1785574621782374522369401937635495963334121241552730672559929064784759) * 10 ^ 70 +
        7745577754938471183008399687845361434628322804046274737103962489825014) * 10 ^ 70 +
        8312074000797594063634464055631609118388504485329829642345593787969922) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_85 :
    recurrence5QuotientConstant.coeff 85 =
      -((((289 * 10 ^ 70 +
        5962825288836881996141254938756844105782629700645560335960834667522716) * 10 ^ 70 +
        8039540783234386769544596433356369066066433281951915808254808059969166) * 10 ^ 70 +
        4813409739423682521212842695765120320780043374041463932610169931689878) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_86 :
    recurrence5QuotientConstant.coeff 86 =
      ((((1348 * 10 ^ 70 +
        9526497241503833394970782522454353059418346088100767688961335211138012) * 10 ^ 70 +
        9138299339294285861311563121129269157582468329094709812025843886059264) * 10 ^ 70 +
        6523324459705904322898943421912695929786101353579682670787532898135752) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_87 :
    recurrence5QuotientConstant.coeff 87 =
      -((((6084 * 10 ^ 70 +
        4454617016455442628914313815786883645626582540131133311245223808080397) * 10 ^ 70 +
        2137273948707247864098176278544581552474277858920021265816908671583189) * 10 ^ 70 +
        8992825972391346830276589244448985821135971901787593424406569542523543) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_88 :
    recurrence5QuotientConstant.coeff 88 =
      ((((26584 * 10 ^ 70 +
        3989623640877312630442429846763092133831844912119930693082757371282922) * 10 ^ 70 +
        5627735417750099796145349651613646546131522727064537019350572541442358) * 10 ^ 70 +
        4978566225100320440893166977478937889844012110450631203416191389532986) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_89 :
    recurrence5QuotientConstant.coeff 89 =
      -((((112555 * 10 ^ 70 +
        9446093498612021144848196644305546844742413931870599604682690122214690) * 10 ^ 70 +
        2954388139621622458338397985330578011650304368508049856204678301654197) * 10 ^ 70 +
        5714777974789685107795752468204778181858127461685417902063894736172661) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_90 :
    recurrence5QuotientConstant.coeff 90 =
      ((((461948 * 10 ^ 70 +
        4391470110141508717691862496391542742981113484496772724353737170302137) * 10 ^ 70 +
        2623580703113001841538411451293661890572300077305080243628753544832415) * 10 ^ 70 +
        1509599536652656220517775437339152599222426696671819092077114593604452) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_91 :
    recurrence5QuotientConstant.coeff 91 =
      -((((1838415 * 10 ^ 70 +
        1059551175889839076860793538448356384524131708288104813598284016752115) * 10 ^ 70 +
        2299796924340971538925942094539629757830942253540535085116547599276760) * 10 ^ 70 +
        9311011797296930390897264043903984954785029890434973123983937580070634) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_92 :
    recurrence5QuotientConstant.coeff 92 =
      ((((7096664 * 10 ^ 70 +
        3655253791186668407768208965816601353696348800109297086469944459363429) * 10 ^ 70 +
        8608622306917152852878927033905040760328780783199575935209011660493602) * 10 ^ 70 +
        2894154293096097380102801542565704746397167015869465750208956772654081) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_93 :
    recurrence5QuotientConstant.coeff 93 =
      -((((26580030 * 10 ^ 70 +
        8814840137435417950513173871414999126375144692347156127604700032815220) * 10 ^ 70 +
        3826307789438294001626432604326129345663899230044213122788338698049266) * 10 ^ 70 +
        0445177614152859925358379331255891907021634718424657637340188707118274) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_94 :
    recurrence5QuotientConstant.coeff 94 =
      ((((96621038 * 10 ^ 70 +
        4150349769170807299036622748063222996472058357554108998722390716576587) * 10 ^ 70 +
        7462004600433767601899273831969159840866444888516292978166842168706681) * 10 ^ 70 +
        7317424282945221282474287676481562202945917859704309061043129036031180) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_95 :
    recurrence5QuotientConstant.coeff 95 =
      -((((340974720 * 10 ^ 70 +
        9535400542487495956023201220242260730664130191315683385024005985672996) * 10 ^ 70 +
        5621159130962421518216786606250726113488270678037002322286310698254407) * 10 ^ 70 +
        9079786551512738909604056753938392012219769954425441393532428338026366) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_96 :
    recurrence5QuotientConstant.coeff 96 =
      ((((1168479740 * 10 ^ 70 +
        9674723190829465232105725772590329839229293071809714800912592869890959) * 10 ^ 70 +
        2742021287193423301078584463189100627555077970279316208642229096891095) * 10 ^ 70 +
        9506383249254060025192493276267946115641629532033578887357111899921118) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_97 :
    recurrence5QuotientConstant.coeff 97 =
      -((((3889360374 * 10 ^ 70 +
        5002789401927851773114525695114879259697291309908481352003379051178723) * 10 ^ 70 +
        0678195317451755697628611433164521865677390834070880683648891101005738) * 10 ^ 70 +
        2973807905498619098481160279057541250345355729178114999196425622340970) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_98 :
    recurrence5QuotientConstant.coeff 98 =
      ((((12577608201 * 10 ^ 70 +
        2289437174974918465999765252286485398927944048009341642913612710347216) * 10 ^ 70 +
        4139432832030533409651156260712723368911796394848698575297441166036397) * 10 ^ 70 +
        5614076501144353014328398555777015671157856878444213910241477243590245) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_99 :
    recurrence5QuotientConstant.coeff 99 =
      -((((39525858436 * 10 ^ 70 +
        7963526261067671598458530657946520468959800348015125803161672357460632) * 10 ^ 70 +
        5956274911130535439177568540652363090727702977722343022409560756412795) * 10 ^ 70 +
        3344822169076488960327916595787645100905948546101520120873313461551598) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_100 :
    recurrence5QuotientConstant.coeff 100 =
      ((((120732507558 * 10 ^ 70 +
        0145382260878433625278280619950451982482826859730768019542897220141963) * 10 ^ 70 +
        8617555191128614601590988287813345102534622476546712780477121084444097) * 10 ^ 70 +
        0132592944443721968784535993302738761786216647893106483916333607153678) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_101 :
    recurrence5QuotientConstant.coeff 101 =
      -((((358524681658 * 10 ^ 70 +
        5778525195362326562191768743826649641913986004810228878564857076192262) * 10 ^ 70 +
        9587057823532624569781301460593847972362729809156355880641120175451664) * 10 ^ 70 +
        6961425391703791572500624797099953569173014857898111533032903136946136) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_102 :
    recurrence5QuotientConstant.coeff 102 =
      ((((1035271466854 * 10 ^ 70 +
        3011161807064552249661179448800516793843482374607750689399568314484524) * 10 ^ 70 +
        9743914326670757908933749069967756262853344442154138776879288064750526) * 10 ^ 70 +
        8678161175589819197930958725307094684530233830033824856410849074743867) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_103 :
    recurrence5QuotientConstant.coeff 103 =
      -((((2907465160545 * 10 ^ 70 +
        1142620172713255252526789585923561757408135215996578705494502767087633) * 10 ^ 70 +
        6163766780513716106539656715819939227223326273123610914172215357379366) * 10 ^ 70 +
        6897565102125459281768650918509102124423982914000172673369071711194268) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_104 :
    recurrence5QuotientConstant.coeff 104 =
      ((((7942936853019 * 10 ^ 70 +
        6812757073833457751654383696660615950135579655239939264217670740272550) * 10 ^ 70 +
        5296822675497424937406413995034116582992900502950355744572202821615748) * 10 ^ 70 +
        4057080185640259509955464238962806581631681377976484561206187427422672) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_105 :
    recurrence5QuotientConstant.coeff 105 =
      -((((21112121941094 * 10 ^ 70 +
        9949173215633921956078937777527056495482506067838477617655528026985537) * 10 ^ 70 +
        8950222238997628305492840471317349576788806015293568694633725621477913) * 10 ^ 70 +
        0007200955015995207097463018626295296008891707003395108733699358094384) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_106 :
    recurrence5QuotientConstant.coeff 106 =
      ((((54606144214370 * 10 ^ 70 +
        1040866476710256738862854955989440442103530560551035000746464936570106) * 10 ^ 70 +
        9758763835729166441877540656028478094490097161745685012782966890765126) * 10 ^ 70 +
        9093562871345922078070419438698462157519795504237446074088271266333305) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_107 :
    recurrence5QuotientConstant.coeff 107 =
      -((((137461663752226 * 10 ^ 70 +
        5868005548027731148264951103115571038004257497774644692511730221127410) * 10 ^ 70 +
        1936688419351636757099137983754720643737089579653332746113947926255219) * 10 ^ 70 +
        6790500485625827899091790888676686128105222879426627732592425457431946) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_108 :
    recurrence5QuotientConstant.coeff 108 =
      ((((336837807739549 * 10 ^ 70 +
        1520072055117515761633769231459437708795025371080675275956734094979982) * 10 ^ 70 +
        6430619726360322504746164241061105090659265719545454577233801025893999) * 10 ^ 70 +
        9651724837805472589913669771625172320190606340356619982273978207399441) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_109 :
    recurrence5QuotientConstant.coeff 109 =
      -((((803572632446782 * 10 ^ 70 +
        0924433167991902999970495518823555620169874681919457802749793654652243) * 10 ^ 70 +
        0349253324619108219185008286450146074182088971678102958786858580335130) * 10 ^ 70 +
        3941987851310773042565459685316570528459661871070735854179762029113144) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_110 :
    recurrence5QuotientConstant.coeff 110 =
      ((((1866628047697882 * 10 ^ 70 +
        0820081657393524831402549227579529352539859505505318045215975101913373) * 10 ^ 70 +
        0758675834515551153307305716174231111019774797333121230076333071248262) * 10 ^ 70 +
        0300446770472959935185309730227741566148769371787590329378478907300992) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_111 :
    recurrence5QuotientConstant.coeff 111 =
      -((((4222596130125024 * 10 ^ 70 +
        9740629006516308103804887050946365577172680429191829839531589814823534) * 10 ^ 70 +
        7020986472314919551705601834737271457028068421025630535283356351786437) * 10 ^ 70 +
        6543361274554207570883081889959342766990512638104236097090853740889329) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_112 :
    recurrence5QuotientConstant.coeff 112 =
      ((((9303552045676298 * 10 ^ 70 +
        6928431238252902128609723875429671127180116540710468815441250245568334) * 10 ^ 70 +
        7928042306968177567369758845561039887866953241738822646967053920801477) * 10 ^ 70 +
        7038153464152859787260188169104598246436588722344876991370331808914963) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_113 :
    recurrence5QuotientConstant.coeff 113 =
      -((((19967405856088013 * 10 ^ 70 +
        8242948679364962001557846776623814803672494104540836065413645647373876) * 10 ^ 70 +
        5653484976035261510328375920869431053207980336851881642836310977403767) * 10 ^ 70 +
        4523886728446612345437241972964702205031531668263660525223957308174437) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_114 :
    recurrence5QuotientConstant.coeff 114 =
      ((((41749577957781164 * 10 ^ 70 +
        8875715949270616085704822532061331998063491739198775273979194336945350) * 10 ^ 70 +
        7529611575146988845089599805190678651851476677293169617891290779096800) * 10 ^ 70 +
        6740103724053129794241865743017589465216040671799745356338456831806583) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_115 :
    recurrence5QuotientConstant.coeff 115 =
      -((((85053480316093478 * 10 ^ 70 +
        5397779472141122633213131721820023427425801164540492750541737695476915) * 10 ^ 70 +
        5388323402891910157704996898379755098824599541747876328410080456224455) * 10 ^ 70 +
        8492336406594055475911027943173340852461424478598242467544292279453367) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_116 :
    recurrence5QuotientConstant.coeff 116 =
      ((((168846363780858741 * 10 ^ 70 +
        8079589688048079344634115673564316072806962458343476956517769728453890) * 10 ^ 70 +
        9502486579050845511121422240638483032735757123390391705043180918332970) * 10 ^ 70 +
        8771359683688255615837181908694202982978005572132899739628388881193384) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_117 :
    recurrence5QuotientConstant.coeff 117 =
      -((((326662474491878554 * 10 ^ 70 +
        1738705454277786867851691431000056801077556641176225660068797825423769) * 10 ^ 70 +
        6408512397011127093780689474001017615509500697232389517944979153162577) * 10 ^ 70 +
        8684600485519937153577216843155395957533974811526950137857354644371999) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_118 :
    recurrence5QuotientConstant.coeff 118 =
      ((((615972500992911054 * 10 ^ 70 +
        3685790530060635427902188462207840198515759544963314305144653912337957) * 10 ^ 70 +
        2556646688530563871271560281879420175793664479776953393305406027608722) * 10 ^ 70 +
        1370941979000434108705495658512500776737750056119448719949093666918315) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_119 :
    recurrence5QuotientConstant.coeff 119 =
      -((((1132199688493004601 * 10 ^ 70 +
        2336543720703429462336284551600640785239854891337086754924083857281394) * 10 ^ 70 +
        9002659599804759985527539404968448257012709289497148164756843980053136) * 10 ^ 70 +
        2334982337184116003576660202836508302519949813882117554037922938823810) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_120 :
    recurrence5QuotientConstant.coeff 120 =
      ((((2028747681797450044 * 10 ^ 70 +
        2210648188424035704994484639353932341416511764930072895084656655991560) * 10 ^ 70 +
        5160067812355874562783507779956075983243835630714258393055179768450763) * 10 ^ 70 +
        8044426179987417043059410302878267760807267631400015309832549098341367) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_121 :
    recurrence5QuotientConstant.coeff 121 =
      -((((3544204003541016838 * 10 ^ 70 +
        6272625874838158915416374677562289894421361571659777652960615199921275) * 10 ^ 70 +
        0770982554395347819109540520100073136748647754928637251113494238127705) * 10 ^ 70 +
        1979680808618367661310992090318649602521029304135540363106080840002764) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_122 :
    recurrence5QuotientConstant.coeff 122 =
      ((((6037209604921105262 * 10 ^ 70 +
        8291165584530585288661454359263168469758906105167362161014639611880638) * 10 ^ 70 +
        4109615714293863265679991413370740622551625177898006576147936954946333) * 10 ^ 70 +
        4240158698181737265317108437768525854319772946791015967365945103123103) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_123 :
    recurrence5QuotientConstant.coeff 123 =
      -((((10028149844230211481 * 10 ^ 70 +
        4789862475002487095047075107555971696435094519863133023002352378328842) * 10 ^ 70 +
        9560198104325631359450194124272569134202547643817564884913461134296788) * 10 ^ 70 +
        2329151200583441393964886152936039846645564281013302117098949193568128) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_124 :
    recurrence5QuotientConstant.coeff 124 =
      ((((16244697401423241251 * 10 ^ 70 +
        7086077317526064331887610134464948937122138048752261477917476734554324) * 10 ^ 70 +
        1213752822874187742025320792150065154699834103997414767697885635678638) * 10 ^ 70 +
        3751053469007322099188745765104677949641576226607764342784142584331590) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_125 :
    recurrence5QuotientConstant.coeff 125 =
      -((((25665346656695061862 * 10 ^ 70 +
        2605597862633874778110225849074613920445708059077679444854537000540880) * 10 ^ 70 +
        7442064277260791964150284775784387868380393943638149335182729696739060) * 10 ^ 70 +
        7956483802293386099790374789508156063207034932980514012635688523223658) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_126 :
    recurrence5QuotientConstant.coeff 126 =
      ((((39551698145106223229 * 10 ^ 70 +
        7982709993273777490187902430939891609836408338738375491175597623964079) * 10 ^ 70 +
        2012079836013777308971386850410396284318488703836120518599949563986232) * 10 ^ 70 +
        3121353831586147506636294870564579270850178077258868966527965085487821) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_127 :
    recurrence5QuotientConstant.coeff 127 =
      -((((59456987642833793912 * 10 ^ 70 +
        9563042841686655491757527551810842990936361292216124306211465579097212) * 10 ^ 70 +
        9534423654389497210845686702212465483528306955274656571284435774750861) * 10 ^ 70 +
        5350068112083724070716862732022836031457531498370573677587445877587835) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_128 :
    recurrence5QuotientConstant.coeff 128 =
      ((((87196154137761167164 * 10 ^ 70 +
        4327565695434174156799022520665876011837521545946366071077940070716616) * 10 ^ 70 +
        0208891389707753541095331896484142107793603387809640098208176420488342) * 10 ^ 70 +
        1653448785659675746542810729183023810256401977253104036351177111604622) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_129 :
    recurrence5QuotientConstant.coeff 129 =
      -((((124762785678270130966 * 10 ^ 70 +
        0064279709741104424491575736763617648968106208238431944985357748338260) * 10 ^ 70 +
        5169802572090135755231399779285736565569829408241596599962346903789110) * 10 ^ 70 +
        0941308269570607277338454335029770407856156468479770834275880582143235) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_130 :
    recurrence5QuotientConstant.coeff 130 =
      ((((174181739172113906424 * 10 ^ 70 +
        3804304563982813988616261765903513200105153937613879363514946176352184) * 10 ^ 70 +
        9477243434843551349294362866979874710621489559656805857819201713130084) * 10 ^ 70 +
        3340561944991444876241050799273800014735938012063500961643742417213641) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_131 :
    recurrence5QuotientConstant.coeff 131 =
      -((((237293876686652821382 * 10 ^ 70 +
        7771097215062510845106755899704850038139102678371257854700964686780126) * 10 ^ 70 +
        5634246725109215818783579725730897962214426213064080189891839208808932) * 10 ^ 70 +
        2757921520580979003630563921180454134365498029320670537414143664327109) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_132 :
    recurrence5QuotientConstant.coeff 132 =
      ((((315481153313210894337 * 10 ^ 70 +
        6516917336108231506087919920955503464424784465205587482837627541176046) * 10 ^ 70 +
        6806834852212212684411817468204588080750758002831704061669083125957228) * 10 ^ 70 +
        3546653768407046402570787430705222736623484496708374748387541653894763) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_133 :
    recurrence5QuotientConstant.coeff 133 =
      -((((409355013710248314505 * 10 ^ 70 +
        7268884473787213326447971573914632685638236840848843611526943650004944) * 10 ^ 70 +
        3067577934446756843946972319745484026318923690141711089122019854166633) * 10 ^ 70 +
        0655863313824996759936284002146561217901015987272093748856633348850054) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_134 :
    recurrence5QuotientConstant.coeff 134 =
      ((((518446202525799978111 * 10 ^ 70 +
        7993295997163313355030169625783165482740424320535710170830146534070097) * 10 ^ 70 +
        7178370920212611243083504922041119788629920446759350998148866940141046) * 10 ^ 70 +
        3790655435023807119388581650185335348373818031114404595986800838963242) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_135 :
    recurrence5QuotientConstant.coeff 135 =
      -((((640946139892495511483 * 10 ^ 70 +
        9742894263009985882854448780960732147537459126502606651285996106044528) * 10 ^ 70 +
        9370500130982831828059720206768507213916753758222588763522911555352512) * 10 ^ 70 +
        5292371137475668623686945156563197613505341629942961114395211029645333) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_136 :
    recurrence5QuotientConstant.coeff 136 =
      ((((773555091173130172777 * 10 ^ 70 +
        2107924816408706945020773534420754042716484264472235128284774374871932) * 10 ^ 70 +
        2615636614064099534349196802697860154309040736344921741221267237589928) * 10 ^ 70 +
        2901883266136046215338027272073170371098776913313443005551252425016346) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_137 :
    recurrence5QuotientConstant.coeff 137 =
      -((((911487284210294885918 * 10 ^ 70 +
        6450172113281357159362609745076056755676894105609663305581554397088515) * 10 ^ 70 +
        3300473682535287340995126217938316791882460706944415352845565933083299) * 10 ^ 70 +
        2884980295963997691945405756384091176554591509718480918662166858738568) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_138 :
    recurrence5QuotientConstant.coeff 138 =
      ((((1048666494821797515605 * 10 ^ 70 +
        7260497248884593755588305293395572939071556913181513053173775222187008) * 10 ^ 70 +
        8563862463982335858719664851852905674720460646685005853252764548543574) * 10 ^ 70 +
        0386000903511989266949529621043023474845464967657507483510421742153927) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_139 :
    recurrence5QuotientConstant.coeff 139 =
      -((((1178118653559251935912 * 10 ^ 70 +
        4481785820055476652673553270431323481298939812447241936526165886454864) * 10 ^ 70 +
        8657808046968743943593515814103972284229942911657947553463721493695339) * 10 ^ 70 +
        4097120464049116145903988852322899478388671532796709441074610000707930) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_140 :
    recurrence5QuotientConstant.coeff 140 =
      ((((1292534804137396721221 * 10 ^ 70 +
        8169418330667656428230190575218097175988791757165882347751899201041940) * 10 ^ 70 +
        4150419041759630943077472003943484089133946601044032734660330113378270) * 10 ^ 70 +
        6592635061399129347064457976000042098103813449928992197960761845842814) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_141 :
    recurrence5QuotientConstant.coeff 141 =
      -((((1384944627340809333406 * 10 ^ 70 +
        9314991519312031830032077012397366025656783940867189462932670794956213) * 10 ^ 70 +
        5564963399598880868279866017734893109726013248665729637710063057275996) * 10 ^ 70 +
        0714923789646984822239949933122548049142628491180642553332205661900689) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_142 :
    recurrence5QuotientConstant.coeff 142 =
      ((((1449415019171012809168 * 10 ^ 70 +
        8557011687600689806993030793674538423737839665451590032998091644432677) * 10 ^ 70 +
        0756593907466192296998731180689464999264679978998057176942028350212420) * 10 ^ 70 +
        1319166228370897913834434309810802172832202480908994859635511361210698) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_143 :
    recurrence5QuotientConstant.coeff 143 =
      -((((1481676265371721571689 * 10 ^ 70 +
        0811921879945678934491145573575775135043183366160618335900954646064977) * 10 ^ 70 +
        3707414905777560541762956827795669796206526563449737014616030349244550) * 10 ^ 70 +
        2107365062686275007136006121226337600280171535672647497132596800885334) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_144 :
    recurrence5QuotientConstant.coeff 144 =
      ((((1479583896871022720047 * 10 ^ 70 +
        0690974834550856911774504508698940809350503405768005243057821312332485) * 10 ^ 70 +
        3174749565673710297921571371625856036728060283094524498015576422984307) * 10 ^ 70 +
        6721337136943638953299330717224701212614070960985451143342894949412689) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_145 :
    recurrence5QuotientConstant.coeff 145 =
      -((((1443347201055631407986 * 10 ^ 70 +
        7718316793316495067135637543043747972800422221615629299008506590900872) * 10 ^ 70 +
        9350005799959641787200753053269850011605080969147174898349151781670432) * 10 ^ 70 +
        9212225843031339437598384908838130925072893998131908173902581726479420) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_146 :
    recurrence5QuotientConstant.coeff 146 =
      ((((1375491441381420621370 * 10 ^ 70 +
        5063682501080655562797370559254570979024156341065677396918807859146566) * 10 ^ 70 +
        4901489814339970422890897422678558922453034401319708150785665617810116) * 10 ^ 70 +
        2616172656432027076310893590705745242079268280633209371526577666094912) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_147 :
    recurrence5QuotientConstant.coeff 147 =
      -((((1280562861640023851162 * 10 ^ 70 +
        3381506158570428869700979700536563156183840026469913590254795777962199) * 10 ^ 70 +
        2610887155618103150772795188795694518574129289544329546531252780410244) * 10 ^ 70 +
        3080004028179853964202235948665845021171283760778436062239142079095672) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_148 :
    recurrence5QuotientConstant.coeff 148 =
      ((((1164624993163569403254 * 10 ^ 70 +
        2596388248180908303081656531155406269035948837870059150451242177967231) * 10 ^ 70 +
        9757536301270059547247029077086278000824530839533851327830991432737288) * 10 ^ 70 +
        0338585444870429853985682489140991791215044837793513785055662484856433) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_149 :
    recurrence5QuotientConstant.coeff 149 =
      -((((1034623946684819595740 * 10 ^ 70 +
        5724338868034816973535919617288895914751427766734435366027054311486454) * 10 ^ 70 +
        4572404478903218644281499390360871840358975905965000621957973976799478) * 10 ^ 70 +
        9050059193325224270996168932149714059893885759893683008308703122062056) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_150 :
    recurrence5QuotientConstant.coeff 150 =
      ((((897714211552204011841 * 10 ^ 70 +
        9772025698809516477244176242598128784029383513778667556371886184805195) * 10 ^ 70 +
        8239910773810469568882095008265126953034508070019579937899687164179225) * 10 ^ 70 +
        2602138474097838679130994542789187673801624320402219130365317463157642) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_151 :
    recurrence5QuotientConstant.coeff 151 =
      -((((760633630680160812007 * 10 ^ 70 +
        0829815280742569823250882127017896833459049917005277745262093373226343) * 10 ^ 70 +
        6766627158184707940811914888626962528023383846736688714678711547757829) * 10 ^ 70 +
        3653390210212497294119813615239742818283494730985367543606548795649666) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_152 :
    recurrence5QuotientConstant.coeff 152 =
      ((((629198955298592797936 * 10 ^ 70 +
        1205125734420769611351358123318646185454757079321538816530656846904950) * 10 ^ 70 +
        2845140825392029737020429166351638619493492338962560475399840371482655) * 10 ^ 70 +
        4467412590049138475305856990708732903062805751531196650903698410577319) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_153 :
    recurrence5QuotientConstant.coeff 153 =
      -((((507966711281988661653 * 10 ^ 70 +
        0669686259764254469069497832959203493575727354809026248688985411812848) * 10 ^ 70 +
        8942693234809941622644149125351858877172078292223424495329235521390840) * 10 ^ 70 +
        3865223559164540262345717421570216455107380625780650448412046030903739) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_154 :
    recurrence5QuotientConstant.coeff 154 =
      ((((400074245524540074930 * 10 ^ 70 +
        5250235468121794971909541975932774893257738533335922384596951901762586) * 10 ^ 70 +
        9786825127122117374634121438870153528864068590039263446358745267168731) * 10 ^ 70 +
        6750090940903520694631039914398417078750041133056342523099729457673094) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_155 :
    recurrence5QuotientConstant.coeff 155 =
      -((((307248620615201411952 * 10 ^ 70 +
        5755920555723502618281482290696513201083949919059443458176839812501125) * 10 ^ 70 +
        6905319409667893149065237756435708643823433398031677205360954714303548) * 10 ^ 70 +
        0114004578318259126279966732663621100868545899073796174781388293189979) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_156 :
    recurrence5QuotientConstant.coeff 156 =
      ((((229950759163263341719 * 10 ^ 70 +
        1584804056622693091802566908982747194425763093029947378698908765725808) * 10 ^ 70 +
        9188874635241356424865371683017227163433419314793145894627202558454608) * 10 ^ 70 +
        0714892499923448785988497277032996555750564712790591728418152067438441) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_157 :
    recurrence5QuotientConstant.coeff 157 =
      -((((167610982450223650287 * 10 ^ 70 +
        2736758390978036308369289156690889420413907529612965240412048143830416) * 10 ^ 70 +
        0430107763357719514952143245663928751135048429208962622240750336674818) * 10 ^ 70 +
        0725350773006474464686601543418150154086003666940856812674997660342139) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_158 :
    recurrence5QuotientConstant.coeff 158 =
      ((((118909760406318380494 * 10 ^ 70 +
        8999431439329489164209775708214733963519647932930582793697090563855169) * 10 ^ 70 +
        1575221708735033482188443565013613976989333956688197909724534215998745) * 10 ^ 70 +
        9905393228354236439943484321003011904228348625002701772307649829222226) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_159 :
    recurrence5QuotientConstant.coeff 159 =
      -((((82062377625901499989 * 10 ^ 70 +
        5623711078578860686326690976947684860057107747946123636773510214028934) * 10 ^ 70 +
        4275543889117942768845695846188897880525910564013300506803858550994547) * 10 ^ 70 +
        8256027929823675296320442725753505003082358466239977609287053217579827) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_160 :
    recurrence5QuotientConstant.coeff 160 =
      ((((55075741220908291669 * 10 ^ 70 +
        8303795062845074356446234474701724770065962293241913552283237076955201) * 10 ^ 70 +
        6709368421132314229785841501150582162437071370506151310961476405710336) * 10 ^ 70 +
        0394861105735871292849609803463912265479447758494308929391350734041569) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_161 :
    recurrence5QuotientConstant.coeff 161 =
      -((((35957010037597316604 * 10 ^ 70 +
        8053866058630972813588794507511872088602438341533445050161433856003200) * 10 ^ 70 +
        5098663922069505106674401858376281281853124954853283297989693056942253) * 10 ^ 70 +
        2063082699254915234581237619535721843550682519048523209897733921620382) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_162 :
    recurrence5QuotientConstant.coeff 162 =
      ((((22864848497587574794 * 10 ^ 70 +
        5170479307660453682458302190699467262066844579562402346704593780331954) * 10 ^ 70 +
        0484123449049408845422659844700260557880437531341554173316517288112737) * 10 ^ 70 +
        5600394411825129990774449064285524928487677630378990954812070698579692) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_163 :
    recurrence5QuotientConstant.coeff 163 =
      -((((14203367207920303290 * 10 ^ 70 +
        9046771365953736168593898934139938723939259770234264237278914082477554) * 10 ^ 70 +
        6653140131597395291820989309312484996264021206038749726896408189134413) * 10 ^ 70 +
        0414852677382398576071063281860844878353282820692648276891544630359305) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_164 :
    recurrence5QuotientConstant.coeff 164 =
      ((((8665441731224477699 * 10 ^ 70 +
        5319317138323202237886119458757124922531693353654437675561714546019100) * 10 ^ 70 +
        7260195412965339181719609580906810131925123954003824144738146731051379) * 10 ^ 70 +
        3022676457956087363151049774146538089813443647382436092649285463012188) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_165 :
    recurrence5QuotientConstant.coeff 165 =
      -((((5235978286995887755 * 10 ^ 70 +
        0166345882980627497548279719696237077255013891924020839516380060146750) * 10 ^ 70 +
        8558724160262524316818445061161955828958691387760371667688389243842515) * 10 ^ 70 +
        4596248272332917465634086644417648088677350679827617768336631709636696) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_166 :
    recurrence5QuotientConstant.coeff 166 =
      ((((3167136741821456758 * 10 ^ 70 +
        4909969695306320260077956277612793900242047218657877938409629919818995) * 10 ^ 70 +
        4451379396179710982296196973257820785847836706679795475291082122834173) * 10 ^ 70 +
        2765483467108661552140991920809022246222143239259304753960000613564177) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_167 :
    recurrence5QuotientConstant.coeff 167 =
      -((((1937076588301319801 * 10 ^ 70 +
        5831623325158200744235266336391826244444425445507510170349827947976049) * 10 ^ 70 +
        6599978615974452576403425006261166651639590613513638447972777978503897) * 10 ^ 70 +
        9192793749800312629674526687640032088535649344818272606628025334466455) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_168 :
    recurrence5QuotientConstant.coeff 168 =
      ((((1202082180765235398 * 10 ^ 70 +
        2680029412636974228641302906478254681754584185923082346381024454366278) * 10 ^ 70 +
        9305327188030119783862971547722695135572773376933976462059159522594089) * 10 ^ 70 +
        1703396427909984526419068122752588558683149516577708217009413150750718) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_169 :
    recurrence5QuotientConstant.coeff 169 =
      -((((749536793089273046 * 10 ^ 70 +
        8865684624992432419386653323097670657880667519364758509958442981790458) * 10 ^ 70 +
        2660673800136919346035067752753323072258222922223124948912033030008754) * 10 ^ 70 +
        0670026945573377611227428027722426982054758745633032578350327578339402) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_170 :
    recurrence5QuotientConstant.coeff 170 =
      ((((456646151633281533 * 10 ^ 70 +
        1494026643569763838591958587759501389879160040570005370079308968696118) * 10 ^ 70 +
        8366141003524705342203641288357641680119535820804654718987714046709050) * 10 ^ 70 +
        1760533057375211344094418252155055920886418570074888378621115681676661) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_171 :
    recurrence5QuotientConstant.coeff 171 =
      -((((257436902583790332 * 10 ^ 70 +
        5270260033060136142434081881768580203853102016230989687740207647290292) * 10 ^ 70 +
        8477041400994728884847716099092008360169001320548223630727884690581834) * 10 ^ 70 +
        8409828468447363830175477101072565594311947725406223084904598521310858) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_172 :
    recurrence5QuotientConstant.coeff 172 =
      ((((118622636003791800 * 10 ^ 70 +
        9159937840113036268003137738135593378525210512331298349908259300943918) * 10 ^ 70 +
        4862902728771723459751611515497558267233598462583529843409062108561382) * 10 ^ 70 +
        7385357627728039592583815931579224353305479832911008235560307452005273) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_173 :
    recurrence5QuotientConstant.coeff 173 =
      -((((23564433683653067 * 10 ^ 70 +
        6240721224493175985778628468640369790044395683856996332164227368839665) * 10 ^ 70 +
        9670106058484731678844212236158845695977184975332210768766238917126198) * 10 ^ 70 +
        6374258842694359498700417733777043807532249524497056099143219099891491) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_174 :
    recurrence5QuotientConstant.coeff 174 =
      -((((37231159235926385 * 10 ^ 70 +
        7595061689818783976460618316875126388459382168576843716154980612856310) * 10 ^ 70 +
        9648774520765186487173621939721356168145641620698151711141357361544169) * 10 ^ 70 +
        0026007803190335513598778306633672374504238314671705703379565840553974) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_175 :
    recurrence5QuotientConstant.coeff 175 =
      ((((70909151844485066 * 10 ^ 70 +
        1693562540612693864903768641850434232745072206004379966771045401664140) * 10 ^ 70 +
        9973943989205110472468655254437858897715403288445549545817066875700113) * 10 ^ 70 +
        7420495088537495794874865502816984934384803886163078542252757809536162) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_176 :
    recurrence5QuotientConstant.coeff 176 =
      -((((84085998821890756 * 10 ^ 70 +
        4880413875992195300571828399025386493228660472357963871833626369257595) * 10 ^ 70 +
        2643025497205966351118287756853881169831952539806744414120484853059187) * 10 ^ 70 +
        9032984554898076441800948368951628835126485258758873605349397704867975) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_177 :
    recurrence5QuotientConstant.coeff 177 =
      ((((83086368256005790 * 10 ^ 70 +
        0344336944870093199700722860972897875608506572860912875212830897837506) * 10 ^ 70 +
        1022292210460376221114224809536850273145649365380357349256863327405704) * 10 ^ 70 +
        2261111750400758627108420338804742160939964952630990084056260536103222) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_178 :
    recurrence5QuotientConstant.coeff 178 =
      -((((73568171939617523 * 10 ^ 70 +
        0859594726476970659509152905808394619397833024265328943983116224827841) * 10 ^ 70 +
        8910553604857215980483336069249346232982643672566872461714888475095078) * 10 ^ 70 +
        6479895114151783400854784992661313873375813339712862217607814315339629) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_179 :
    recurrence5QuotientConstant.coeff 179 =
      ((((60104120338522266 * 10 ^ 70 +
        4430306783817576836213544896983811378758470107932364616238750757025594) * 10 ^ 70 +
        6656149788278300273648162050687571483774846413146596638988699230596430) * 10 ^ 70 +
        3816699990094254217980834427177964901520922105606220793285800286212587) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_180 :
    recurrence5QuotientConstant.coeff 180 =
      -((((45969877730598489 * 10 ^ 70 +
        6827148520725788040637131986910670153208244833942356296133948008443808) * 10 ^ 70 +
        2640919013580316429752406534483237593340640310014067848742336025483252) * 10 ^ 70 +
        7906646958759203044179032087430906724835937035035433820339325544204579) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_181 :
    recurrence5QuotientConstant.coeff 181 =
      ((((33179698459743910 * 10 ^ 70 +
        1118106940404845378365031444653230408179353315145161493398604444467330) * 10 ^ 70 +
        7400150928505395667184207100447975786778049743050245051846540399833679) * 10 ^ 70 +
        0371203602946664706457650433758883321616303605474254530359434558133741) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_182 :
    recurrence5QuotientConstant.coeff 182 =
      -((((22702738169140671 * 10 ^ 70 +
        8540956042261516869486147620437935280439074746119719935653357236021584) * 10 ^ 70 +
        0085582053087087896150665664111480515970448172470423650568813867446603) * 10 ^ 70 +
        7792300787643578506655576416819824754797779730168698310605171056443117) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_183 :
    recurrence5QuotientConstant.coeff 183 =
      ((((14761574917970461 * 10 ^ 70 +
        3950458568242149237437232458634610610502582544737759493375279217551387) * 10 ^ 70 +
        5154678654746200278815963535025030393364409590266375042757593908728104) * 10 ^ 70 +
        7635699066850122207991053974521394399706088658935785990449997372877868) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_184 :
    recurrence5QuotientConstant.coeff 184 =
      -((((9128163604821443 * 10 ^ 70 +
        7655701608812284956428799524016826709090763594687143214077988885130772) * 10 ^ 70 +
        1177800610598578612087357057581972969121683058935882590301865510874792) * 10 ^ 70 +
        0987336890765516308937588550185631035865793386459334595737736151216281) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_185 :
    recurrence5QuotientConstant.coeff 185 =
      ((((5364740321116454 * 10 ^ 70 +
        6468736311300049464140116943814217460279067524375037700616987268894373) * 10 ^ 70 +
        5564115573484325716387761218084325718511931374077659254759565526091486) * 10 ^ 70 +
        7792375294668990626824853139713795765075148908107266726798455442060367) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_186 :
    recurrence5QuotientConstant.coeff 186 =
      -((((2989809373723908 * 10 ^ 70 +
        7020317663225191459442387698733808305813815687547559679752049002625260) * 10 ^ 70 +
        7920208936995235100927404963443133358342906487816120697317710359296226) * 10 ^ 70 +
        2914678864734795122917346800708237640183969276279525255547416973539639) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_187 :
    recurrence5QuotientConstant.coeff 187 =
      ((((1573004773895670 * 10 ^ 70 +
        5490940134883428842170657983231336076594691647406491607361644603984114) * 10 ^ 70 +
        3349301412166185245084110041591161706994431343730163540315080689306605) * 10 ^ 70 +
        3815079013242387229442082964404504747687761790679784912395996334914567) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_188 :
    recurrence5QuotientConstant.coeff 188 =
      -((((775086013205849 * 10 ^ 70 +
        8947145826190626123290336705299247751425948193507863420643943708589010) * 10 ^ 70 +
        0262005025593203186360187762587009813057360302766095501909664790576680) * 10 ^ 70 +
        1704859638725013452008236154436062007956110735131086164899062403384456) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_189 :
    recurrence5QuotientConstant.coeff 189 =
      ((((352548352719769 * 10 ^ 70 +
        6392655049764422719318525940570825188996451257376700719321542823346319) * 10 ^ 70 +
        5709228462698588847388573416876891927452452486765090302320866782444435) * 10 ^ 70 +
        2554252807469477162659158153462868546489411475369908530458649433339002) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_190 :
    recurrence5QuotientConstant.coeff 190 =
      -((((143815530319025 * 10 ^ 70 +
        3048133063847403002868503640230252612249911345574438633394692945661463) * 10 ^ 70 +
        7017936577565172759717779921899536608009706150834074365215114069686858) * 10 ^ 70 +
        4664050223460179896596071074469489112136619580233435413875445557118804) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_191 :
    recurrence5QuotientConstant.coeff 191 =
      ((((49068402406927 * 10 ^ 70 +
        2413974788813343044360060011900765575267820944712312263800823892147324) * 10 ^ 70 +
        0573039634811812294639508461872391497652107561375889374170363787070295) * 10 ^ 70 +
        1693273479420775793090147931888225812448838828166801491536789715879087) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_192 :
    recurrence5QuotientConstant.coeff 192 =
      -((((10766020248746 * 10 ^ 70 +
        1959323975220427290694818638630189354045515962191865222765725351792873) * 10 ^ 70 +
        2372014921480400583299785838948310571002147063092970742564177330923653) * 10 ^ 70 +
        7339205578263043178467611906331782941444325951049308870002636849180446) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_193 :
    recurrence5QuotientConstant.coeff 193 =
      -((((1979406122663 * 10 ^ 70 +
        3279546912053593023851881039366029905462689730095634725505175934067076) * 10 ^ 70 +
        1142594043052056007231487156304016730210817443802389662075046622929133) * 10 ^ 70 +
        3328129496739839298964542803328506850229850479043866411384851030326181) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_194 :
    recurrence5QuotientConstant.coeff 194 =
      ((((4495768248583 * 10 ^ 70 +
        2686971825530199286678595364775169178309748612814840941416722870092542) * 10 ^ 70 +
        5323962720866952506079247868143013556509490022574628465972281501838207) * 10 ^ 70 +
        6973613100858002226967737365630648726389309142453795499542457329073721) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_195 :
    recurrence5QuotientConstant.coeff 195 =
      -((((3701502226252 * 10 ^ 70 +
        9258554465926525457449622957807396308993371751054052931095520596211445) * 10 ^ 70 +
        2113672918835654899320676771058648805210985045162614819149852558217433) * 10 ^ 70 +
        5515705683967118772399640854337074234742497876018636015781056891589239) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_196 :
    recurrence5QuotientConstant.coeff 196 =
      ((((2335049999351 * 10 ^ 70 +
        2335458145409523066154880017688067352058692884908730333015119105934118) * 10 ^ 70 +
        8801959670727064342651697985236904839894768977905618941013852210766882) * 10 ^ 70 +
        7250560597188765163134966727046187272821351812991989642649342547001646) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_197 :
    recurrence5QuotientConstant.coeff 197 =
      -((((1255609902622 * 10 ^ 70 +
        4868002160309916456123772955465642645500388173257755008330198832671852) * 10 ^ 70 +
        8403812768595295804515258830627893907197215728002256888169051332866283) * 10 ^ 70 +
        7214750659661632920236353634813368507444159977918264790907237575714647) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_198 :
    recurrence5QuotientConstant.coeff 198 =
      ((((587797330964 * 10 ^ 70 +
        9730265011096069895013787747465047089469398153615956271732889897678855) * 10 ^ 70 +
        7308192011042304417340340775439039757285950006956068727129834554325417) * 10 ^ 70 +
        2816904656205291872629380682637637207175791179520146073537487594409158) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_199 :
    recurrence5QuotientConstant.coeff 199 =
      -((((233689061729 * 10 ^ 70 +
        9252182051535920303292247144895920041945790427738702036424851159838797) * 10 ^ 70 +
        9898070503335940082537118524303379469960155665095975382993854944533645) * 10 ^ 70 +
        6128388594584568287221232561540694845294271971633614936235508850787985) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_200 :
    recurrence5QuotientConstant.coeff 200 =
      ((((70154987023 * 10 ^ 70 +
        1135757482799831006446402825639612516463526934281352323242775004390348) * 10 ^ 70 +
        8982731361791580998345244995841948538854087596080415729225210652285043) * 10 ^ 70 +
        0086068393993671948897207593197443132536642108161508543915737237733115) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_201 :
    recurrence5QuotientConstant.coeff 201 =
      -((((6296073089 * 10 ^ 70 +
        3065673062266502421686187841118086317507558757017713719799992482568420) * 10 ^ 70 +
        3315781851638712821572520563586058083893924816821683788411715115936338) * 10 ^ 70 +
        2660968175994746931486842212222088655444628995283376941826495960524367) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_202 :
    recurrence5QuotientConstant.coeff 202 =
      -((((12163484391 * 10 ^ 70 +
        9224607905503561436979129356307543301179320737320176013866455750568969) * 10 ^ 70 +
        9553744968948099887475073790945405161308667179612842754965408145215002) * 10 ^ 70 +
        5539929304041784289369053685637529587224040875655079051149869098448080) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_203 :
    recurrence5QuotientConstant.coeff 203 =
      ((((13229035446 * 10 ^ 70 +
        7399865287888260056434540969179097484808274362771032464527965155099200) * 10 ^ 70 +
        9187808543395850272087100818069033544844586404212226018864316907910244) * 10 ^ 70 +
        5557253085971641782085505762981105296814165189605546401041890500441917) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_204 :
    recurrence5QuotientConstant.coeff 204 =
      -((((9476854810 * 10 ^ 70 +
        7924159949827221924391141455141730016074832019046295478210890809891511) * 10 ^ 70 +
        6560802784957092667502248973985291997370834306256919302900606803737888) * 10 ^ 70 +
        2579502035810808055453424415800346051735232798273869195298862080235912) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_205 :
    recurrence5QuotientConstant.coeff 205 =
      ((((5628564235 * 10 ^ 70 +
        8946290487667264731865519090218066621748323120638704917355476094076662) * 10 ^ 70 +
        2231388307404100494182774132027600238903989528950165384157642121995291) * 10 ^ 70 +
        9612257209205245818192966145829473088347209561997070927414139290673569) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_206 :
    recurrence5QuotientConstant.coeff 206 =
      -((((2929480306 * 10 ^ 70 +
        9379420600867961051974689502934936710947725684337750823219455265356517) * 10 ^ 70 +
        3492888279247462959249422760132830703974075702405075335447885584387003) * 10 ^ 70 +
        9030111025338279356460003508717707732054231483109532188359567379056926) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_207 :
    recurrence5QuotientConstant.coeff 207 =
      ((((1347876523 * 10 ^ 70 +
        7883071799302768456555834929916910277159722075371658001128392143104231) * 10 ^ 70 +
        9441588303954987148386657052801144508082611988181016322049465792779477) * 10 ^ 70 +
        0294027943867106476293998822762672866262448476888232130148508610018014) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_208 :
    recurrence5QuotientConstant.coeff 208 =
      -((((533850581 * 10 ^ 70 +
        7041111026092266178803930761044644417876595246050996185080911315444147) * 10 ^ 70 +
        9183984689307202156291901313340834387354104894480030920247097813623949) * 10 ^ 70 +
        9449000361458123763634634614610598942871919804869371589202415473611955) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_209 :
    recurrence5QuotientConstant.coeff 209 =
      ((((163389076 * 10 ^ 70 +
        7237935729770705849079329772312488455828252346502564754179911570685502) * 10 ^ 70 +
        0105327529465961586500986544968108768867681394550436780361382894438648) * 10 ^ 70 +
        6044141255472538733034795748151840502249769594553936489307394250643019) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_210 :
    recurrence5QuotientConstant.coeff 210 =
      -((((18495990 * 10 ^ 70 +
        3835734152998286237401161275020153406168614741226714884502280893658643) * 10 ^ 70 +
        5136316546268263038612549943079951601076392106352623882427263475394967) * 10 ^ 70 +
        3440988672418407048110247029880864164290051673443573009530937181902685) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_211 :
    recurrence5QuotientConstant.coeff 211 =
      -((((24993920 * 10 ^ 70 +
        2284907555505863874558160755270855285860436291643762029581146830028819) * 10 ^ 70 +
        6957805909504252552411008226669209135265445078471357271010313109165598) * 10 ^ 70 +
        9870365881432990772239907212909453985803515016656605935978332365019545) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_212 :
    recurrence5QuotientConstant.coeff 212 =
      ((((29409426 * 10 ^ 70 +
        4936233379881569253878349247541002578506418991255437522300921138377590) * 10 ^ 70 +
        5575982447788449661174471348162319432001242511366964241346150890871184) * 10 ^ 70 +
        5846345022551074231315881976978843104833102773818909022088397545601297) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_213 :
    recurrence5QuotientConstant.coeff 213 =
      -((((22387554 * 10 ^ 70 +
        5244782551414488164594231066293405011460768153993335314783243764825885) * 10 ^ 70 +
        7240860075791650200956823715495836160973042819288944191713721405550185) * 10 ^ 70 +
        1433477954276837818811143369074777553850715595958926815806964021604648) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_214 :
    recurrence5QuotientConstant.coeff 214 =
      ((((14393882 * 10 ^ 70 +
        7235112170115614131406885429674903650093454016357627202508662672963212) * 10 ^ 70 +
        2208868176396766279018351531030265878143781034962948752538512997379654) * 10 ^ 70 +
        2541003323733840545074068485702423121100690542958689942326232634588518) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_215 :
    recurrence5QuotientConstant.coeff 215 =
      -((((8396429 * 10 ^ 70 +
        8166491989721274712543173729998901050811223323418133868631538341208469) * 10 ^ 70 +
        1184445025013632731116426366262260149016888118917678321823651921243004) * 10 ^ 70 +
        4398658069096565567804975107238025205979238483912662509162072110424859) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_216 :
    recurrence5QuotientConstant.coeff 216 =
      ((((4581111 * 10 ^ 70 +
        6052484268159553316884352192061726306366622143734392360614524396863228) * 10 ^ 70 +
        3703660234490350386967697035910715526865543407231871720744817370156128) * 10 ^ 70 +
        0988337430638939035516425130686185678210168425063393607580180427605739) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_217 :
    recurrence5QuotientConstant.coeff 217 =
      -((((2375352 * 10 ^ 70 +
        6786014502627505186540306562278855092685970808909326697367838452540446) * 10 ^ 70 +
        3359802486254452370460137449183276598853040069106419439766708005974909) * 10 ^ 70 +
        6088481997588192895267233514958243736542158415479979753506106911613018) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_218 :
    recurrence5QuotientConstant.coeff 218 =
      ((((1181453 * 10 ^ 70 +
        0378618723490827763235464592797821857806209988689847041098840256430008) * 10 ^ 70 +
        7724324133615017955753264766487349911915037660499795885474336226916311) * 10 ^ 70 +
        7495884195920691001240099183255533680227941340062495204742209233734704) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_219 :
    recurrence5QuotientConstant.coeff 219 =
      -((((566926 * 10 ^ 70 +
        4702589084508210877602925251819026260202759549990914915372675850431219) * 10 ^ 70 +
        2271285465074619381344577652546916294575515841010786583349618561712249) * 10 ^ 70 +
        1393380807599779001708400546207004067551100455144595395711190539788668) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_220 :
    recurrence5QuotientConstant.coeff 220 =
      ((((263383 * 10 ^ 70 +
        6496578507430755766720631865560569953692363489201638502385770991770833) * 10 ^ 70 +
        5755026699002123808831496360299838700107061212720166030897879841623533) * 10 ^ 70 +
        8485570979751897636442874114741643891410843529843102156683416222762481) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_221 :
    recurrence5QuotientConstant.coeff 221 =
      -((((118710 * 10 ^ 70 +
        0192671820102715244917280669999069968828097016398193131421615118271289) * 10 ^ 70 +
        6689800189768758870855216351307747671040002179083129884103497409901052) * 10 ^ 70 +
        5495444476029387995200997483924709035265901268483609647069195114601692) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_222 :
    recurrence5QuotientConstant.coeff 222 =
      ((((51958 * 10 ^ 70 +
        0347269492876833336486660646104548356854894641802517406733659118262497) * 10 ^ 70 +
        9073404277676586439618584761612241261140805148647590888523692342782856) * 10 ^ 70 +
        8033659437450361666832554795499033134205054433606729392275594921926376) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_223 :
    recurrence5QuotientConstant.coeff 223 =
      -((((22089 * 10 ^ 70 +
        7012466204361008367028681394513698867835660000016683152021491455120833) * 10 ^ 70 +
        3402499034483270711035376855454023177249855066463290385470650382831460) * 10 ^ 70 +
        4779204251370139911360910437780984435238968212911467733289488807971568) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_224 :
    recurrence5QuotientConstant.coeff 224 =
      ((((9119 * 10 ^ 70 +
        5077076284722210482366788912148689701969475490096170567318230616724178) * 10 ^ 70 +
        1040380263735851100017801186104286759316406403676873370237006514923122) * 10 ^ 70 +
        5070276804931729934473608260407791942163691008528074056032026893812452) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_225 :
    recurrence5QuotientConstant.coeff 225 =
      -((((3653 * 10 ^ 70 +
        4578378708636103384270087388524507527582576008650226515731232450666129) * 10 ^ 70 +
        4133106584931877187246214223288001923831074602923695640443822585744691) * 10 ^ 70 +
        1808437792960889221472039236537551358076082642344649448605155868967623) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_226 :
    recurrence5QuotientConstant.coeff 226 =
      ((((1418 * 10 ^ 70 +
        9668904445022666096651894944397361898583133455978433052252471650425751) * 10 ^ 70 +
        7106396312742853645685971846026422794381724962049998830396180386032159) * 10 ^ 70 +
        5604995460615753430730739620234477015217168945788066361887374692606984) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_227 :
    recurrence5QuotientConstant.coeff 227 =
      -((((533 * 10 ^ 70 +
        6538176731193088049488692667011017234902692196820805627428709919220309) * 10 ^ 70 +
        1149339872444351389015310590901602354249984360272076150255767552019239) * 10 ^ 70 +
        1449849255747579820909864106415176295718913981820225297392555951669952) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_228 :
    recurrence5QuotientConstant.coeff 228 =
      ((((194 * 10 ^ 70 +
        0663053739402757751652603175321047542049820884786435269959086426363024) * 10 ^ 70 +
        5797743475341662715260304497349908708626813813576759252595973817531694) * 10 ^ 70 +
        8222001987195090730456674104316364907573477445717617562241488853500024) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_229 :
    recurrence5QuotientConstant.coeff 229 =
      -((((68 * 10 ^ 70 +
        1251225581357164603526210406613436106481551404766422077644085515887936) * 10 ^ 70 +
        8562572278598068548094322244758349079967014933339025696375111812446371) * 10 ^ 70 +
        6388800134491296923180413920815446559030646446773347361709067257354751) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_230 :
    recurrence5QuotientConstant.coeff 230 =
      ((((23 * 10 ^ 70 +
        0371603000592711128859783337971909893252415300998461103122565399505588) * 10 ^ 70 +
        5670383992446121052834151071235942215120084115576076493828374432005679) * 10 ^ 70 +
        7693527222571579233814913249828758401714384286991819236480199000093995) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_231 :
    recurrence5QuotientConstant.coeff 231 =
      -((((7 * 10 ^ 70 +
        4845984997608133148021516928173047573409308041492443959519321598591374) * 10 ^ 70 +
        4998291392191004119912270072452102941785450387133739561947686317734183) * 10 ^ 70 +
        2638172333606675605544175981053162308579528323168635009237760158121819) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_232 :
    recurrence5QuotientConstant.coeff 232 =
      ((((2 * 10 ^ 70 +
        3280847692968118219487745536526333719356228374382364732163759855835925) * 10 ^ 70 +
        2334026820097541095743508272530909491282951910117452164106782993381483) * 10 ^ 70 +
        2562998531884548305885933030086664366008844680390767533964126081410627) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_233 :
    recurrence5QuotientConstant.coeff 233 =
      -(((6898568876458171306006508494721436841725115792974384945790733497613312 * 10 ^ 70 +
        5545931694075626836559775993261732750343198902047777910400876858590211) * 10 ^ 70 +
        9966141069236029955134079790202221984083799971504304109461551446116808) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_234 :
    recurrence5QuotientConstant.coeff 234 =
      (((1932557895533688001319763414712908422627266357767015941613334877578422 * 10 ^ 70 +
        0428455490550281615268440625753353286332576274833872223875778352158030) * 10 ^ 70 +
        8905876833719728891196137704859269573567871954533989146794631069201765) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_235 :
    recurrence5QuotientConstant.coeff 235 =
      -(((505157105828608592064739259760842657949062839242558499280254790964204 * 10 ^ 70 +
        3278298139020450553174040912358398225846455113050574086506784687333983) * 10 ^ 70 +
        6558913897151135079144459677542276367169867515265719030036296472202590) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_236 :
    recurrence5QuotientConstant.coeff 236 =
      (((120015804436982479857571805576126090921159437036574323653562746613678 * 10 ^ 70 +
        4589715877654112484702974957285881419542071634659485360242288663091388) * 10 ^ 70 +
        6724994863451971013413577373291899685653609264070397438264819919209440) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_237 :
    recurrence5QuotientConstant.coeff 237 =
      -(((24256374700732240829507419176526730928310396660925877971308950306281 * 10 ^ 70 +
        5143082047574802297643314554098850141645503691769990429276971662820772) * 10 ^ 70 +
        7839243926695509698852425072595883321430578923466019855262329268212233) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_238 :
    recurrence5QuotientConstant.coeff 238 =
      (((3204647111502239665226506431789587148969579698195632724928077343427 * 10 ^ 70 +
        5833533632108721503578919573537626076366040387375384459662424289131405) * 10 ^ 70 +
        6594553828830955721291560216670696744772190063174399289404527525016382) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_239 :
    recurrence5QuotientConstant.coeff 239 =
      (((401843010132835949643451052877338276127953892919071291666170309736 * 10 ^ 70 +
        2238153961242791468931949822791371990641622984786421895849640015967239) * 10 ^ 70 +
        0894144565931697420575606691882266721598247822753203236714095926589728) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_240 :
    recurrence5QuotientConstant.coeff 240 =
      -(((576093563837838495939910704753420425696999608627170484963040877177 * 10 ^ 70 +
        6839450954769346687642616516222909523965313857023233343483408648380010) * 10 ^ 70 +
        7366349413538265509813154213517923317207915246242365074601043633936308) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_241 :
    recurrence5QuotientConstant.coeff 241 =
      (((328816934067549885458350400921749804482199179225614773766335132668 * 10 ^ 70 +
        3396430233001020340079630829810378971877287858145608062459144851056455) * 10 ^ 70 +
        5565995871769792665966171563673322430919375525543392078558478050304155) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_242 :
    recurrence5QuotientConstant.coeff 242 =
      -(((154016202610888377485969767626073900545359256932102726032552428751 * 10 ^ 70 +
        0369916971590773970138806654101489672088946578110594608400804439905025) * 10 ^ 70 +
        9246218691667209422316630363459127144010794278218569000908988331289124) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_243 :
    recurrence5QuotientConstant.coeff 243 =
      (((66459645232299295771362146031166007007657686586848674482844903560 * 10 ^ 70 +
        1791403133462524865928707769855353332130709333472172526930297377267325) * 10 ^ 70 +
        8767605425055449430209968575380642286103497819789347785730184334437885) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_244 :
    recurrence5QuotientConstant.coeff 244 =
      -(((27449741048087130985066361087861717382805801369961572700083329207 * 10 ^ 70 +
        9619545056403838551052008526338438828071186546648593743947677499329173) * 10 ^ 70 +
        0581620112057953085319644816314321678693659560053248117422385279403026) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_245 :
    recurrence5QuotientConstant.coeff 245 =
      (((11012388707807919973943413886263355563042263963785551448926578398 * 10 ^ 70 +
        9424381712214033226851905925072478886895265972976354255699802769912828) * 10 ^ 70 +
        1065295134849267305849918675441156365048646245113218188788796322195724) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_246 :
    recurrence5QuotientConstant.coeff 246 =
      -(((4315139613646920801562586312017448041542843344435078997933033201 * 10 ^ 70 +
        2406764963026512324152474207729523985934909896789931435466405937740526) * 10 ^ 70 +
        0828650502365625280226687106996821223204290263437822269247662418973866) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_247 :
    recurrence5QuotientConstant.coeff 247 =
      (((1654454973753836246729052212873407415536673238065435350861599999 * 10 ^ 70 +
        2132252315547235291430737913504005505337722942980171078576305070607973) * 10 ^ 70 +
        1654298152458622695310532589452930583217600600380562517550927285226934) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_248 :
    recurrence5QuotientConstant.coeff 248 =
      -(((620742357591375373364784515178201531114492670079304841316169207 * 10 ^ 70 +
        6701509648276871886018877742426794659535170282967798485877174473692408) * 10 ^ 70 +
        4744671796804774120351009636743232150368373095843531833124317620619694) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_249 :
    recurrence5QuotientConstant.coeff 249 =
      (((227708900229000457667657146343926867471147076016662323919963962 * 10 ^ 70 +
        4373543539594315974743287297949262810725252703333394899168283879208417) * 10 ^ 70 +
        2600324646329718999659652150008959310938136859379130206003833204304403) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_250 :
    recurrence5QuotientConstant.coeff 250 =
      -(((81530838327339137998068840014381553612210515379587328670070828 * 10 ^ 70 +
        1112279631467759552676255766241465638108828375377887583093996762366140) * 10 ^ 70 +
        4892312528302906246204632719759209599629275046780395991088463543471313) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_251 :
    recurrence5QuotientConstant.coeff 251 =
      (((28425051016340113066288990341382764279343112715202130126590365 * 10 ^ 70 +
        8359625293992953302269215091583281853204507109250662797279542169103940) * 10 ^ 70 +
        8172351739387463509748454331536653314862691912330325826926287895560701) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_252 :
    recurrence5QuotientConstant.coeff 252 =
      -(((9622488635730842024535561980737555488377090101575220270363708 * 10 ^ 70 +
        9665285904554996294317350722791862425047259092560566203318012283853711) * 10 ^ 70 +
        7508084563291121368464458523803311927683343119728035692056316680288866) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_253 :
    recurrence5QuotientConstant.coeff 253 =
      (((3153499481904775099416200747648281259299019962632940136859331 * 10 ^ 70 +
        5721013201340950381992662880167361729178877852815068273008904991922207) * 10 ^ 70 +
        0149244244551707193954548493785712614567095618738977916095246466017515) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_254 :
    recurrence5QuotientConstant.coeff 254 =
      -(((997725478431053242200620350016830206142648545850302877822408 * 10 ^ 70 +
        3450143408937658729564680737288614705622300720614453105800079581072885) * 10 ^ 70 +
        2207123352521322897933169888081752735763274043462611516329852630196634) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_255 :
    recurrence5QuotientConstant.coeff 255 =
      (((304035700818314782156271328678258571853588956380997530117928 * 10 ^ 70 +
        5218000908657691878841312353782503690569098738647120006127969261927562) * 10 ^ 70 +
        0908398949174314576048410879893268748586971121908148139680533556276003) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_256 :
    recurrence5QuotientConstant.coeff 256 =
      -(((89076398113710282006234606722489114922671094514391720264224 * 10 ^ 70 +
        6052970659617409523509649874907505653604624341586784881799854458056316) * 10 ^ 70 +
        7558848293064418229040007844626365882312969289903225893185741736530503) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_257 :
    recurrence5QuotientConstant.coeff 257 =
      (((25061442228766484837701973625052509913687602780664975910780 * 10 ^ 70 +
        0679519604827230463055388424996236131929609961646341733093965477885359) * 10 ^ 70 +
        3473640078888044777888023973193437073617675938227507418190664019920356) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_258 :
    recurrence5QuotientConstant.coeff 258 =
      -(((6766138611054230906608463703246095331970218827015649888231 * 10 ^ 70 +
        0728856501133641114589613471166115454065913332824723042514227091861480) * 10 ^ 70 +
        3406669208336687434150501715022392849207202516576858563341064731850525) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_259 :
    recurrence5QuotientConstant.coeff 259 =
      (((1752165263404023154735422876295084590112629798750307278376 * 10 ^ 70 +
        8633420384542520044145824559482973253818809616120728742062114901472568) * 10 ^ 70 +
        6965381895887602820579808377926294755868691784296990840028070506255042) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_260 :
    recurrence5QuotientConstant.coeff 260 =
      -(((435056627855968177675888350255498864469915871198994374351 * 10 ^ 70 +
        4600275346311414110583174359395051944887869146377527003017354510036084) * 10 ^ 70 +
        4569588768149299551461815557662908803163383787650816325612646969666821) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_261 :
    recurrence5QuotientConstant.coeff 261 =
      (((103528468617571292305986269509991582550271305502884861216 * 10 ^ 70 +
        4222796142888116708916917506883705038802750625820854201142425270629785) * 10 ^ 70 +
        7961025517868845045132696894537362050095079563277610086540475952619975) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_262 :
    recurrence5QuotientConstant.coeff 262 =
      -(((23599614932020980709885493696492437641489269718833990104 * 10 ^ 70 +
        1504494160696809831956046634469992885194768529750170129179330580622459) * 10 ^ 70 +
        1206477492154130659259692640440392660452195813352866660619158936746438) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_263 :
    recurrence5QuotientConstant.coeff 263 =
      (((5151411033365757976434006752669231381418985359561434758 * 10 ^ 70 +
        6871773046508219076668489631217493359597773078248903429795245645596714) * 10 ^ 70 +
        4168141794798795048949868308401196259064302260178028412481479189739350) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_264 :
    recurrence5QuotientConstant.coeff 264 =
      -(((1076596265630808713747626545785428571706965912703753107 * 10 ^ 70 +
        9351374432927879381796570391752789457194173054525566575541051584633967) * 10 ^ 70 +
        0013689173821284809587542318505209645513102028500163688584979035537112) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_265 :
    recurrence5QuotientConstant.coeff 265 =
      (((215278558974211303176610477635849168441305323893026257 * 10 ^ 70 +
        3332070897784295973245568666398916167718235774210312919006174992750822) * 10 ^ 70 +
        2749768537441354961359245004773048300917403151744519921496354764047971) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_266 :
    recurrence5QuotientConstant.coeff 266 =
      -(((41040880079900197110389113610595040215339990799834972 * 10 ^ 70 +
        8035324792198021443852988307866644286436936583965991510695329175513916) * 10 ^ 70 +
        5452302276808911661307515793822033671724144458691478570102951996146107) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_267 :
    recurrence5QuotientConstant.coeff 267 =
      (((7371175186767220397990532848142465522679618304397570 * 10 ^ 70 +
        2928140255799832959298103351052455993118326534965535184611890848356972) * 10 ^ 70 +
        2566479342870327612106856691364823371818310692130136314886991190524606) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_268 :
    recurrence5QuotientConstant.coeff 268 =
      -(((1209373706630859684302452253167669509890510390390698 * 10 ^ 70 +
        2421430493198427166366800573828451546798288236980937627778967580011295) * 10 ^ 70 +
        9839819498505534536658009442560153476903234357142979428162169037030871) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_269 :
    recurrence5QuotientConstant.coeff 269 =
      (((167675502814289296673792199538596430274484397738655 * 10 ^ 70 +
        0258543884685776639563418100298435660570862253072711143728633044833132) * 10 ^ 70 +
        2839802291693599956414017630061514787734247595027092707269916209776523) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_270 :
    recurrence5QuotientConstant.coeff 270 =
      -(((14876754951663323602406926638062745193482483242333 * 10 ^ 70 +
        3353844698072935366404713480079622680159996696997739512716025670596098) * 10 ^ 70 +
        4508479628378153444237229890019281445858620161680850770833906332294183) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_271 :
    recurrence5QuotientConstant.coeff 271 =
      -(((1135625734867170053520867118021205599622087939411 * 10 ^ 70 +
        2213628571679804474610150141209156315355137129928314245399369970658102) * 10 ^ 70 +
        7657031537369590002380538832354934012928121225737799213779717860974467) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_272 :
    recurrence5QuotientConstant.coeff 272 =
      (((988054064205518773308609827798552958732891855418 * 10 ^ 70 +
        4485275631363749491739369900432480906507103857409930930671012676294159) * 10 ^ 70 +
        0774270397294445852884740742552164239715847362513687734900698619628484) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_273 :
    recurrence5QuotientConstant.coeff 273 =
      -(((306875765311897492176253909085141671904854252499 * 10 ^ 70 +
        9099964699141904384376080155333111005863010754092451378613824893345722) * 10 ^ 70 +
        2645656829902747215296460335419067472335173391602804702062508090569221) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_274 :
    recurrence5QuotientConstant.coeff 274 =
      (((70633499583835470098762192676177099756882037778 * 10 ^ 70 +
        7176129967778800325007670394944591291937719532434701671465133880132550) * 10 ^ 70 +
        2309655968792217826037872327173707278749630702507915298272874918135714) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_275 :
    recurrence5QuotientConstant.coeff 275 =
      -(((13470653951556522079823437891626038117382808742 * 10 ^ 70 +
        9093729400026460266883286392447955932992297872273889598730906429329912) * 10 ^ 70 +
        5081287874839532114632271573910961615524665116352345664064990365704835) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_276 :
    recurrence5QuotientConstant.coeff 276 =
      (((2214698519271463122489031151406157774320647655 * 10 ^ 70 +
        2137140996692371539658092280438849511992449331353835738744528396474960) * 10 ^ 70 +
        6940432759324141776287589950060028877083247335881408287252231035770558) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_277 :
    recurrence5QuotientConstant.coeff 277 =
      -(((320354664199699701364040226241000314368040906 * 10 ^ 70 +
        7756117385536467322108676851112713423695684595212241724137621003366038) * 10 ^ 70 +
        4375041710562016187809511840581242679727329896556734050967875995164121) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_278 :
    recurrence5QuotientConstant.coeff 278 =
      (((41239131796704293324916911430224333375197409 * 10 ^ 70 +
        9131639791322552563379176923117211530484097424130387499359939448168007) * 10 ^ 70 +
        9134141735702941670391101761945535968802830312883913133814533807329562) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_279 :
    recurrence5QuotientConstant.coeff 279 =
      -(((4719008009526981180160656101803807828738202 * 10 ^ 70 +
        3756026292752186346694653837720897759583659376499300749244414573594696) * 10 ^ 70 +
        6006646310815237557820441425198939908849098085329384395452229732924219) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_280 :
    recurrence5QuotientConstant.coeff 280 =
      (((464981808991812954540871315968245331850236 * 10 ^ 70 +
        4091214900947456291178726764860439254711382567787318320202252987084822) * 10 ^ 70 +
        6461960308096881283374410388538164654892871501824061226444351604202618) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_281 :
    recurrence5QuotientConstant.coeff 281 =
      -(((34979478298392863846676580236734068342004 * 10 ^ 70 +
        3524466908640007526915819505328096374582613337716025254710875231820819) * 10 ^ 70 +
        0766427803594601227183256659082339988614616960895945223300293935792629) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_282 :
    recurrence5QuotientConstant.coeff 282 =
      (((973557521387902038178866829249189822620 * 10 ^ 70 +
        8681711675256211194762076822791151408139160447257101114748503117587875) * 10 ^ 70 +
        1232566896784460469802862732920424512431475243100262261973587691512811) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_283 :
    recurrence5QuotientConstant.coeff 283 =
      (((258997884699415870864611147251556464364 * 10 ^ 70 +
        3066930210447699235083702484755050757510336597952458900002557892550860) * 10 ^ 70 +
        0553127023389208833732723279538281985127254292876058624073792587365360) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_284 :
    recurrence5QuotientConstant.coeff 284 =
      -(((58785099993743844872282448424766650287 * 10 ^ 70 +
        1328841936307210580567780379755581116102327420008333661112979537065252) * 10 ^ 70 +
        6926120589647777606412409792590145645402805273671072780223045165154781) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_285 :
    recurrence5QuotientConstant.coeff 285 =
      (((7146935927059393165618519549034555054 * 10 ^ 70 +
        3308661745323311264107348475009107059018904953570448935018193204920143) * 10 ^ 70 +
        1757256131438086710770664555493840787105996864501761137803345400576958) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_286 :
    recurrence5QuotientConstant.coeff 286 =
      -(((568640964890841949447457056456535110 * 10 ^ 70 +
        5325747561160363955601321263972245656628047350812367416305047897156580) * 10 ^ 70 +
        0980251159823688562814245785085528420231228883123256223251567864293383) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_287 :
    recurrence5QuotientConstant.coeff 287 =
      (((27320335693022512956302021441894763 * 10 ^ 70 +
        0185835324920755295396273541652277934525900333846583555377710159519204) * 10 ^ 70 +
        4614313132883189880411877962807868937202227663674932988322523433687685) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_288 :
    recurrence5QuotientConstant.coeff 288 =
      -(((390997910773837114686926832752054 * 10 ^ 70 +
        4527507382329609793676365046029089820371985111956113573084552278767956) * 10 ^ 70 +
        7355985304890200616244006370103606958792451839240290543469343675087681) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_289 :
    recurrence5QuotientConstant.coeff 289 =
      -(((37735404488995614932003961712598 * 10 ^ 70 +
        3088551659634888181381175012964288770965917560949917524968634428251965) * 10 ^ 70 +
        6710394792789069024198083698609517429015480066497564689729356451604079) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_290 :
    recurrence5QuotientConstant.coeff 290 =
      (((2160465261141365216825913126717 * 10 ^ 70 +
        7964724582535190849939306946128624247732744995783730939373169446624341) * 10 ^ 70 +
        3152359414565062438012751635063049821775599071332375893126976820806263) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_291 :
    recurrence5QuotientConstant.coeff 291 =
      -(((18139495370941717932731894585 * 10 ^ 70 +
        9426146329756493980365333104287730668169048634331419094350958268200673) * 10 ^ 70 +
        7248397246781950492846857277109123728138952848794917729320440018115057) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_292 :
    recurrence5QuotientConstant.coeff 292 =
      -(((968165283934379050026952114 * 10 ^ 70 +
        0249043409837457380293788584823865729672964101660644200314125073614194) * 10 ^ 70 +
        5978339582159792526119519937502513429632148292077971369076096868317639) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_293 :
    recurrence5QuotientConstant.coeff 293 =
      (((2657210726578502606045711 * 10 ^ 70 +
        6559286798770192233215830880349764286939596391978821078362466979934449) * 10 ^ 70 +
        2844346788417169841579425982431169830951708992061180638841852086462196) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_294 :
    recurrence5QuotientConstant.coeff 294 =
      (((128817720100336073893586 * 10 ^ 70 +
        7706500888406672863932920227550497180094457867931825792606557275925248) * 10 ^ 70 +
        2829846674256861197482961985843340640210585154205387634539602366022691) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_295 :
    recurrence5QuotientConstant.coeff 295 =
      (((419422678169643888064 * 10 ^ 70 +
        4076219390631267008533614043879344823979808590085716644764053041603074) * 10 ^ 70 +
        4487766272989842162408187649713493666020119712396091721922966221653547) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_296 :
    recurrence5QuotientConstant.coeff 296 =
      -(((2679420413629128290 * 10 ^ 70 +
        6823342242135602578828647723943074416512063323887752987470174447788200) * 10 ^ 70 +
        1865169956237450722528906799650085608338521213420694611856155231842481) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_297 :
    recurrence5QuotientConstant.coeff 297 =
      -(((13755591320840199 * 10 ^ 70 +
        4692612877590888918642154282587146091577884166484880125343881228883970) * 10 ^ 70 +
        5244718140941820107337930519623082292984514010463137233562831765948294) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_298 :
    recurrence5QuotientConstant.coeff 298 =
      (((11852072037786 * 10 ^ 70 +
        6700288994420347467308115283185391412123379008899419908004149541725793) * 10 ^ 70 +
        1734087255466034744986938548844246215720289565593111796862072722269786) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_299 :
    recurrence5QuotientConstant.coeff 299 =
      (((114868381019 * 10 ^ 70 +
        7821272277975067608299600539004072395847189780613762723494232855869370) * 10 ^ 70 +
        6923062312176899303190953236099750204087581849062584502644072334081309) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_300 :
    recurrence5QuotientConstant.coeff 300 =
      -(((18832498 * 10 ^ 70 +
        4871706866966485053148385746593693846183791247890263685282016402111788) * 10 ^ 70 +
        1600680854468118428055150898303359150592949930964723332365421865988325) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_301 :
    recurrence5QuotientConstant.coeff 301 =
      -(((381409 * 10 ^ 70 +
        4817381713297449705819124600164952405058423534529926898785694047612131) * 10 ^ 70 +
        8368367742481699509567964773237595925111064278324302223776670111580258) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_302 :
    recurrence5QuotientConstant.coeff 302 =
      (((101 * 10 ^ 70 +
        5969577655177026630596525259253863842370737684072652263137799658213236) * 10 ^ 70 +
        0669240442864556054228185599682202462956094212102173498047383369489218) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_303 :
    recurrence5QuotientConstant.coeff 303 =
      ((3495285898993490725161661861567522939871900487580397164973306172723618 * 10 ^ 70 +
        5855237635983769685403448314766616525763980657069005708769059689858123) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_304 :
    recurrence5QuotientConstant.coeff 304 =
      -((900378725060116726267794516168093927544825440626823339592541080371 * 10 ^ 70 +
        7640757938025289137355927073752990987443557124041720163200119436508252) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_305 :
    recurrence5QuotientConstant.coeff 305 =
      -((255701728927512090993838459180323367882345581215749147939572748 * 10 ^ 70 +
        4364115821923743228802140963759022423996051100326045144220852111924688) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_306 :
    recurrence5QuotientConstant.coeff 306 =
      ((28816174420777838205279750820847863895306630085095031166571 * 10 ^ 70 +
        8113138415812879430203516050002631302520748883696703579564406403177469) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_307 :
    recurrence5QuotientConstant.coeff 307 =
      ((670632634394845064811873698922484073093800970198194072 * 10 ^ 70 +
        7136707897869158762967320138615944505338383147129322659517876852279726) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_308 :
    recurrence5QuotientConstant.coeff 308 =
      -((25414105551138615657720602158187147624016564986383 * 10 ^ 70 +
        4554600202111511499806959095324199350574675139858577460849747823619296) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_309 :
    recurrence5QuotientConstant.coeff 309 =
      -((16122381409783326110172541075538110722776235 * 10 ^ 70 +
        5428982900704767245094012387269540352124101907978784779879968890212697) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_310 :
    recurrence5QuotientConstant.coeff 310 =
      ((285128446095739486296030755269732056789 * 10 ^ 70 +
        3650932602434571761846572340262490251810798087488033019904347538222359) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_311 :
    recurrence5QuotientConstant.coeff 311 =
      -((19139917398119177410916809010878 * 10 ^ 70 +
        1586542644772214182520624494436470715711407259814896361806995574779533) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_312 :
    recurrence5QuotientConstant.coeff 312 =
      -((12292817857799054979374401 * 10 ^ 70 +
        2589994505645001265367650337495358307215747880957717230591258014188654) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_coeff_313 :
    recurrence5QuotientConstant.coeff 313 =
      ((56558796881688867 * 10 ^ 70 +
        9087872408743322883006753074138718050770562539463631428692261239001589) : ℚ) := by
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence5QuotientConstant_natDegree_le :
    recurrence5QuotientConstant.natDegree ≤ 313 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n h
  unfold recurrence5QuotientConstant
  rw [Polynomial.coeff_sub]
  rw [recurrence5B2A2_coeff_high n (by omega)]
  rw [recurrence5B1A3_coeff_high n (by omega)]
  norm_num

theorem recurrence5QuotientConstant_coeff_high
    (n : ℕ) (h : 313 < n) :
    recurrence5QuotientConstant.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence5QuotientConstant_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3A3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB2A4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: quotient constant coefficient subtraction

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4B3A3_coeff_0
  recurrence4B3A3_coeff_1
  recurrence4B3A3_coeff_2
  recurrence4B3A3_coeff_3
  recurrence4B3A3_coeff_4
  recurrence4B3A3_coeff_5
  recurrence4B3A3_coeff_6
  recurrence4B3A3_coeff_7
  recurrence4B3A3_coeff_8
  recurrence4B3A3_coeff_9
  recurrence4B3A3_coeff_10
  recurrence4B3A3_coeff_11
  recurrence4B3A3_coeff_12
  recurrence4B3A3_coeff_13
  recurrence4B3A3_coeff_14
  recurrence4B3A3_coeff_15
  recurrence4B3A3_coeff_16
  recurrence4B3A3_coeff_17
  recurrence4B3A3_coeff_18
  recurrence4B3A3_coeff_19
  recurrence4B3A3_coeff_20
  recurrence4B3A3_coeff_21
  recurrence4B3A3_coeff_22
  recurrence4B3A3_coeff_23
  recurrence4B3A3_coeff_24
  recurrence4B3A3_coeff_25
  recurrence4B3A3_coeff_26
  recurrence4B3A3_coeff_27
  recurrence4B3A3_coeff_28
  recurrence4B3A3_coeff_29
  recurrence4B3A3_coeff_30
  recurrence4B3A3_coeff_31
  recurrence4B3A3_coeff_32
  recurrence4B3A3_coeff_33
  recurrence4B3A3_coeff_34
  recurrence4B3A3_coeff_35
  recurrence4B3A3_coeff_36
  recurrence4B3A3_coeff_37
  recurrence4B3A3_coeff_38
  recurrence4B3A3_coeff_39
  recurrence4B3A3_coeff_40
  recurrence4B3A3_coeff_41
  recurrence4B3A3_coeff_42
  recurrence4B3A3_coeff_43
  recurrence4B3A3_coeff_44
  recurrence4B3A3_coeff_45
  recurrence4B3A3_coeff_46
  recurrence4B3A3_coeff_47
  recurrence4B3A3_coeff_48
  recurrence4B3A3_coeff_49
  recurrence4B3A3_coeff_50
  recurrence4B3A3_coeff_51
  recurrence4B3A3_coeff_52
  recurrence4B3A3_coeff_53
  recurrence4B3A3_coeff_54
  recurrence4B3A3_coeff_55
  recurrence4B3A3_coeff_56
  recurrence4B3A3_coeff_57
  recurrence4B3A3_coeff_58
  recurrence4B3A3_coeff_59
  recurrence4B3A3_coeff_60
  recurrence4B3A3_coeff_61
  recurrence4B3A3_coeff_62
  recurrence4B3A3_coeff_63

attribute [local simp]
  recurrence4B3A3_coeff_64
  recurrence4B3A3_coeff_65
  recurrence4B3A3_coeff_66
  recurrence4B3A3_coeff_67
  recurrence4B3A3_coeff_68
  recurrence4B3A3_coeff_69
  recurrence4B3A3_coeff_70
  recurrence4B3A3_coeff_71
  recurrence4B3A3_coeff_72
  recurrence4B3A3_coeff_73
  recurrence4B3A3_coeff_74
  recurrence4B3A3_coeff_75
  recurrence4B3A3_coeff_76
  recurrence4B3A3_coeff_77
  recurrence4B3A3_coeff_78
  recurrence4B3A3_coeff_79
  recurrence4B3A3_coeff_80
  recurrence4B3A3_coeff_81
  recurrence4B3A3_coeff_82
  recurrence4B3A3_coeff_83
  recurrence4B3A3_coeff_84
  recurrence4B3A3_coeff_85
  recurrence4B3A3_coeff_86
  recurrence4B3A3_coeff_87
  recurrence4B3A3_coeff_88
  recurrence4B3A3_coeff_89
  recurrence4B3A3_coeff_90
  recurrence4B3A3_coeff_91
  recurrence4B3A3_coeff_92
  recurrence4B3A3_coeff_93
  recurrence4B3A3_coeff_94
  recurrence4B3A3_coeff_95
  recurrence4B3A3_coeff_96
  recurrence4B3A3_coeff_97
  recurrence4B3A3_coeff_98
  recurrence4B3A3_coeff_99
  recurrence4B3A3_coeff_100
  recurrence4B3A3_coeff_101
  recurrence4B3A3_coeff_102
  recurrence4B3A3_coeff_103
  recurrence4B3A3_coeff_104
  recurrence4B3A3_coeff_105
  recurrence4B3A3_coeff_106
  recurrence4B3A3_coeff_107
  recurrence4B3A3_coeff_108
  recurrence4B3A3_coeff_109
  recurrence4B3A3_coeff_110
  recurrence4B3A3_coeff_111
  recurrence4B3A3_coeff_112
  recurrence4B3A3_coeff_113
  recurrence4B3A3_coeff_114
  recurrence4B3A3_coeff_115
  recurrence4B3A3_coeff_116
  recurrence4B3A3_coeff_117
  recurrence4B3A3_coeff_118
  recurrence4B3A3_coeff_119
  recurrence4B3A3_coeff_120
  recurrence4B3A3_coeff_121
  recurrence4B3A3_coeff_122
  recurrence4B3A3_coeff_123
  recurrence4B3A3_coeff_124
  recurrence4B3A3_coeff_125
  recurrence4B3A3_coeff_126
  recurrence4B3A3_coeff_127

attribute [local simp]
  recurrence4B3A3_coeff_128
  recurrence4B3A3_coeff_129
  recurrence4B3A3_coeff_130
  recurrence4B3A3_coeff_131
  recurrence4B3A3_coeff_132
  recurrence4B3A3_coeff_133
  recurrence4B3A3_coeff_134
  recurrence4B3A3_coeff_135
  recurrence4B3A3_coeff_136
  recurrence4B3A3_coeff_137
  recurrence4B3A3_coeff_138
  recurrence4B3A3_coeff_139
  recurrence4B3A3_coeff_140
  recurrence4B3A3_coeff_141
  recurrence4B3A3_coeff_142
  recurrence4B3A3_coeff_143
  recurrence4B3A3_coeff_144
  recurrence4B3A3_coeff_145
  recurrence4B3A3_coeff_146
  recurrence4B3A3_coeff_147
  recurrence4B3A3_coeff_148
  recurrence4B3A3_coeff_149
  recurrence4B3A3_coeff_150
  recurrence4B3A3_coeff_151
  recurrence4B3A3_coeff_152
  recurrence4B3A3_coeff_153
  recurrence4B3A3_coeff_154
  recurrence4B3A3_coeff_155
  recurrence4B3A3_coeff_156
  recurrence4B3A3_coeff_157
  recurrence4B3A3_coeff_158
  recurrence4B3A3_coeff_159
  recurrence4B3A3_coeff_160
  recurrence4B3A3_coeff_161
  recurrence4B3A3_coeff_162
  recurrence4B3A3_coeff_163
  recurrence4B3A3_coeff_164
  recurrence4B3A3_coeff_165
  recurrence4B3A3_coeff_166
  recurrence4B3A3_coeff_167
  recurrence4B3A3_coeff_168
  recurrence4B3A3_coeff_169
  recurrence4B3A3_coeff_170
  recurrence4B3A3_coeff_171
  recurrence4B3A3_coeff_172
  recurrence4B3A3_coeff_173
  recurrence4B3A3_coeff_174
  recurrence4B3A3_coeff_175
  recurrence4B3A3_coeff_176
  recurrence4B3A3_coeff_177
  recurrence4B3A3_coeff_178
  recurrence4B3A3_coeff_179
  recurrence4B3A3_coeff_180
  recurrence4B3A3_coeff_181
  recurrence4B3A3_coeff_182
  recurrence4B3A3_coeff_183
  recurrence4B3A3_coeff_184
  recurrence4B3A3_coeff_185
  recurrence4B3A3_coeff_186
  recurrence4B3A3_coeff_187
  recurrence4B3A3_coeff_188
  recurrence4B3A3_coeff_189
  recurrence4B3A3_coeff_190
  recurrence4B3A3_coeff_191

attribute [local simp]
  recurrence4B3A3_coeff_192
  recurrence4B3A3_coeff_193
  recurrence4B3A3_coeff_194
  recurrence4B3A3_coeff_195
  recurrence4B3A3_coeff_196
  recurrence4B3A3_coeff_197
  recurrence4B3A3_coeff_198
  recurrence4B3A3_coeff_199
  recurrence4B3A3_coeff_200
  recurrence4B3A3_coeff_201
  recurrence4B3A3_coeff_202
  recurrence4B3A3_coeff_203
  recurrence4B3A3_coeff_204
  recurrence4B3A3_coeff_205
  recurrence4B3A3_coeff_206
  recurrence4B3A3_coeff_207
  recurrence4B3A3_coeff_208
  recurrence4B3A3_coeff_209
  recurrence4B3A3_coeff_210
  recurrence4B3A3_coeff_211
  recurrence4B3A3_coeff_212
  recurrence4B3A3_coeff_213
  recurrence4B3A3_coeff_214
  recurrence4B3A3_coeff_215
  recurrence4B3A3_coeff_216
  recurrence4B3A3_coeff_217
  recurrence4B3A3_coeff_218
  recurrence4B3A3_coeff_219
  recurrence4B3A3_coeff_220
  recurrence4B3A3_coeff_221
  recurrence4B3A3_coeff_222
  recurrence4B3A3_coeff_223
  recurrence4B3A3_coeff_224
  recurrence4B3A3_coeff_225
  recurrence4B3A3_coeff_226
  recurrence4B3A3_coeff_227
  recurrence4B3A3_coeff_228
  recurrence4B3A3_coeff_229
  recurrence4B3A3_coeff_230
  recurrence4B3A3_coeff_231
  recurrence4B3A3_coeff_232
  recurrence4B3A3_coeff_233
  recurrence4B3A3_coeff_234
  recurrence4B3A3_coeff_235
  recurrence4B3A3_coeff_236
  recurrence4B3A3_coeff_237
  recurrence4B3A3_coeff_238
  recurrence4B3A3_coeff_239
  recurrence4B3A3_coeff_240
  recurrence4B3A3_coeff_241
  recurrence4B3A3_coeff_242
  recurrence4B3A3_coeff_243
  recurrence4B3A3_coeff_244
  recurrence4B3A3_coeff_245
  recurrence4B3A3_coeff_246
  recurrence4B3A3_coeff_247
  recurrence4B3A3_coeff_248
  recurrence4B3A3_coeff_249
  recurrence4B3A3_coeff_250
  recurrence4B3A3_coeff_251
  recurrence4B3A3_coeff_252
  recurrence4B3A3_coeff_253
  recurrence4B3A3_coeff_254
  recurrence4B3A3_coeff_255

attribute [local simp]
  recurrence4B3A3_coeff_256
  recurrence4B3A3_coeff_257
  recurrence4B3A3_coeff_258
  recurrence4B3A3_coeff_259
  recurrence4B3A3_coeff_260
  recurrence4B3A3_coeff_261
  recurrence4B3A3_coeff_262
  recurrence4B3A3_coeff_263
  recurrence4B3A3_coeff_264
  recurrence4B3A3_coeff_265
  recurrence4B3A3_coeff_266
  recurrence4B3A3_coeff_267
  recurrence4B3A3_coeff_268
  recurrence4B3A3_coeff_269
  recurrence4B3A3_coeff_270
  recurrence4B3A3_coeff_271
  recurrence4B3A3_coeff_272
  recurrence4B3A3_coeff_273
  recurrence4B3A3_coeff_274
  recurrence4B3A3_coeff_275
  recurrence4B3A3_coeff_276
  recurrence4B3A3_coeff_277
  recurrence4B3A3_coeff_278
  recurrence4B3A3_coeff_279
  recurrence4B3A3_coeff_280
  recurrence4B3A3_coeff_281
  recurrence4B3A3_coeff_282
  recurrence4B3A3_coeff_283
  recurrence4B3A3_coeff_284
  recurrence4B3A3_coeff_285
  recurrence4B3A3_coeff_286
  recurrence4B3A3_coeff_287
  recurrence4B3A3_coeff_288
  recurrence4B3A3_coeff_289
  recurrence4B3A3_coeff_290
  recurrence4B3A3_coeff_291
  recurrence4B3A3_coeff_292
  recurrence4B3A3_coeff_293
  recurrence4B3A3_coeff_294
  recurrence4B3A3_coeff_295
  recurrence4B3A3_coeff_296
  recurrence4B3A3_coeff_297
  recurrence4B3A3_coeff_298
  recurrence4B3A3_coeff_299
  recurrence4B3A3_coeff_300
  recurrence4B3A3_coeff_301
  recurrence4B3A3_coeff_302
  recurrence4B3A3_coeff_303
  recurrence4B3A3_coeff_304
  recurrence4B3A3_coeff_305
  recurrence4B3A3_coeff_306
  recurrence4B3A3_coeff_307
  recurrence4B3A3_coeff_308
  recurrence4B3A3_coeff_309
  recurrence4B3A3_coeff_310
  recurrence4B3A3_coeff_311
  recurrence4B3A3_coeff_312
  recurrence4B3A3_coeff_313
  recurrence4B3A3_coeff_314
  recurrence4B3A3_coeff_315
  recurrence4B3A3_coeff_316
  recurrence4B3A3_coeff_317
  recurrence4B3A3_coeff_318
  recurrence4B3A3_coeff_319

attribute [local simp]
  recurrence4B3A3_coeff_320
  recurrence4B3A3_coeff_321
  recurrence4B3A3_coeff_322
  recurrence4B3A3_coeff_323
  recurrence4B3A3_coeff_324
  recurrence4B3A3_coeff_325
  recurrence4B3A3_coeff_326
  recurrence4B3A3_coeff_327
  recurrence4B3A3_coeff_328
  recurrence4B3A3_coeff_329
  recurrence4B3A3_coeff_330
  recurrence4B3A3_coeff_331
  recurrence4B3A3_coeff_332
  recurrence4B3A3_coeff_333
  recurrence4B3A3_coeff_334
  recurrence4B3A3_coeff_335
  recurrence4B3A3_coeff_336
  recurrence4B3A3_coeff_337
  recurrence4B3A3_coeff_338
  recurrence4B3A3_coeff_339
  recurrence4B3A3_coeff_340
  recurrence4B3A3_coeff_341
  recurrence4B3A3_coeff_342
  recurrence4B3A3_coeff_343
  recurrence4B3A3_coeff_344
  recurrence4B3A3_coeff_345
  recurrence4B3A3_coeff_346
  recurrence4B2A4_coeff_0
  recurrence4B2A4_coeff_1
  recurrence4B2A4_coeff_2
  recurrence4B2A4_coeff_3
  recurrence4B2A4_coeff_4
  recurrence4B2A4_coeff_5
  recurrence4B2A4_coeff_6
  recurrence4B2A4_coeff_7
  recurrence4B2A4_coeff_8
  recurrence4B2A4_coeff_9
  recurrence4B2A4_coeff_10
  recurrence4B2A4_coeff_11
  recurrence4B2A4_coeff_12
  recurrence4B2A4_coeff_13
  recurrence4B2A4_coeff_14
  recurrence4B2A4_coeff_15
  recurrence4B2A4_coeff_16
  recurrence4B2A4_coeff_17
  recurrence4B2A4_coeff_18
  recurrence4B2A4_coeff_19
  recurrence4B2A4_coeff_20
  recurrence4B2A4_coeff_21
  recurrence4B2A4_coeff_22
  recurrence4B2A4_coeff_23
  recurrence4B2A4_coeff_24
  recurrence4B2A4_coeff_25
  recurrence4B2A4_coeff_26
  recurrence4B2A4_coeff_27
  recurrence4B2A4_coeff_28
  recurrence4B2A4_coeff_29
  recurrence4B2A4_coeff_30
  recurrence4B2A4_coeff_31
  recurrence4B2A4_coeff_32
  recurrence4B2A4_coeff_33
  recurrence4B2A4_coeff_34
  recurrence4B2A4_coeff_35
  recurrence4B2A4_coeff_36

attribute [local simp]
  recurrence4B2A4_coeff_37
  recurrence4B2A4_coeff_38
  recurrence4B2A4_coeff_39
  recurrence4B2A4_coeff_40
  recurrence4B2A4_coeff_41
  recurrence4B2A4_coeff_42
  recurrence4B2A4_coeff_43
  recurrence4B2A4_coeff_44
  recurrence4B2A4_coeff_45
  recurrence4B2A4_coeff_46
  recurrence4B2A4_coeff_47
  recurrence4B2A4_coeff_48
  recurrence4B2A4_coeff_49
  recurrence4B2A4_coeff_50
  recurrence4B2A4_coeff_51
  recurrence4B2A4_coeff_52
  recurrence4B2A4_coeff_53
  recurrence4B2A4_coeff_54
  recurrence4B2A4_coeff_55
  recurrence4B2A4_coeff_56
  recurrence4B2A4_coeff_57
  recurrence4B2A4_coeff_58
  recurrence4B2A4_coeff_59
  recurrence4B2A4_coeff_60
  recurrence4B2A4_coeff_61
  recurrence4B2A4_coeff_62
  recurrence4B2A4_coeff_63
  recurrence4B2A4_coeff_64
  recurrence4B2A4_coeff_65
  recurrence4B2A4_coeff_66
  recurrence4B2A4_coeff_67
  recurrence4B2A4_coeff_68
  recurrence4B2A4_coeff_69
  recurrence4B2A4_coeff_70
  recurrence4B2A4_coeff_71
  recurrence4B2A4_coeff_72
  recurrence4B2A4_coeff_73
  recurrence4B2A4_coeff_74
  recurrence4B2A4_coeff_75
  recurrence4B2A4_coeff_76
  recurrence4B2A4_coeff_77
  recurrence4B2A4_coeff_78
  recurrence4B2A4_coeff_79
  recurrence4B2A4_coeff_80
  recurrence4B2A4_coeff_81
  recurrence4B2A4_coeff_82
  recurrence4B2A4_coeff_83
  recurrence4B2A4_coeff_84
  recurrence4B2A4_coeff_85
  recurrence4B2A4_coeff_86
  recurrence4B2A4_coeff_87
  recurrence4B2A4_coeff_88
  recurrence4B2A4_coeff_89
  recurrence4B2A4_coeff_90
  recurrence4B2A4_coeff_91
  recurrence4B2A4_coeff_92
  recurrence4B2A4_coeff_93
  recurrence4B2A4_coeff_94
  recurrence4B2A4_coeff_95
  recurrence4B2A4_coeff_96
  recurrence4B2A4_coeff_97
  recurrence4B2A4_coeff_98
  recurrence4B2A4_coeff_99
  recurrence4B2A4_coeff_100

attribute [local simp]
  recurrence4B2A4_coeff_101
  recurrence4B2A4_coeff_102
  recurrence4B2A4_coeff_103
  recurrence4B2A4_coeff_104
  recurrence4B2A4_coeff_105
  recurrence4B2A4_coeff_106
  recurrence4B2A4_coeff_107
  recurrence4B2A4_coeff_108
  recurrence4B2A4_coeff_109
  recurrence4B2A4_coeff_110
  recurrence4B2A4_coeff_111
  recurrence4B2A4_coeff_112
  recurrence4B2A4_coeff_113
  recurrence4B2A4_coeff_114
  recurrence4B2A4_coeff_115
  recurrence4B2A4_coeff_116
  recurrence4B2A4_coeff_117
  recurrence4B2A4_coeff_118
  recurrence4B2A4_coeff_119
  recurrence4B2A4_coeff_120
  recurrence4B2A4_coeff_121
  recurrence4B2A4_coeff_122
  recurrence4B2A4_coeff_123
  recurrence4B2A4_coeff_124
  recurrence4B2A4_coeff_125
  recurrence4B2A4_coeff_126
  recurrence4B2A4_coeff_127
  recurrence4B2A4_coeff_128
  recurrence4B2A4_coeff_129
  recurrence4B2A4_coeff_130
  recurrence4B2A4_coeff_131
  recurrence4B2A4_coeff_132
  recurrence4B2A4_coeff_133
  recurrence4B2A4_coeff_134
  recurrence4B2A4_coeff_135
  recurrence4B2A4_coeff_136
  recurrence4B2A4_coeff_137
  recurrence4B2A4_coeff_138
  recurrence4B2A4_coeff_139
  recurrence4B2A4_coeff_140
  recurrence4B2A4_coeff_141
  recurrence4B2A4_coeff_142
  recurrence4B2A4_coeff_143
  recurrence4B2A4_coeff_144
  recurrence4B2A4_coeff_145
  recurrence4B2A4_coeff_146
  recurrence4B2A4_coeff_147
  recurrence4B2A4_coeff_148
  recurrence4B2A4_coeff_149
  recurrence4B2A4_coeff_150
  recurrence4B2A4_coeff_151
  recurrence4B2A4_coeff_152
  recurrence4B2A4_coeff_153
  recurrence4B2A4_coeff_154
  recurrence4B2A4_coeff_155
  recurrence4B2A4_coeff_156
  recurrence4B2A4_coeff_157
  recurrence4B2A4_coeff_158
  recurrence4B2A4_coeff_159
  recurrence4B2A4_coeff_160
  recurrence4B2A4_coeff_161
  recurrence4B2A4_coeff_162
  recurrence4B2A4_coeff_163
  recurrence4B2A4_coeff_164

attribute [local simp]
  recurrence4B2A4_coeff_165
  recurrence4B2A4_coeff_166
  recurrence4B2A4_coeff_167
  recurrence4B2A4_coeff_168
  recurrence4B2A4_coeff_169
  recurrence4B2A4_coeff_170
  recurrence4B2A4_coeff_171
  recurrence4B2A4_coeff_172
  recurrence4B2A4_coeff_173
  recurrence4B2A4_coeff_174
  recurrence4B2A4_coeff_175
  recurrence4B2A4_coeff_176
  recurrence4B2A4_coeff_177
  recurrence4B2A4_coeff_178
  recurrence4B2A4_coeff_179
  recurrence4B2A4_coeff_180
  recurrence4B2A4_coeff_181
  recurrence4B2A4_coeff_182
  recurrence4B2A4_coeff_183
  recurrence4B2A4_coeff_184
  recurrence4B2A4_coeff_185
  recurrence4B2A4_coeff_186
  recurrence4B2A4_coeff_187
  recurrence4B2A4_coeff_188
  recurrence4B2A4_coeff_189
  recurrence4B2A4_coeff_190
  recurrence4B2A4_coeff_191
  recurrence4B2A4_coeff_192
  recurrence4B2A4_coeff_193
  recurrence4B2A4_coeff_194
  recurrence4B2A4_coeff_195
  recurrence4B2A4_coeff_196
  recurrence4B2A4_coeff_197
  recurrence4B2A4_coeff_198
  recurrence4B2A4_coeff_199
  recurrence4B2A4_coeff_200
  recurrence4B2A4_coeff_201
  recurrence4B2A4_coeff_202
  recurrence4B2A4_coeff_203
  recurrence4B2A4_coeff_204
  recurrence4B2A4_coeff_205
  recurrence4B2A4_coeff_206
  recurrence4B2A4_coeff_207
  recurrence4B2A4_coeff_208
  recurrence4B2A4_coeff_209
  recurrence4B2A4_coeff_210
  recurrence4B2A4_coeff_211
  recurrence4B2A4_coeff_212
  recurrence4B2A4_coeff_213
  recurrence4B2A4_coeff_214
  recurrence4B2A4_coeff_215
  recurrence4B2A4_coeff_216
  recurrence4B2A4_coeff_217
  recurrence4B2A4_coeff_218
  recurrence4B2A4_coeff_219
  recurrence4B2A4_coeff_220
  recurrence4B2A4_coeff_221
  recurrence4B2A4_coeff_222
  recurrence4B2A4_coeff_223
  recurrence4B2A4_coeff_224
  recurrence4B2A4_coeff_225
  recurrence4B2A4_coeff_226
  recurrence4B2A4_coeff_227
  recurrence4B2A4_coeff_228

attribute [local simp]
  recurrence4B2A4_coeff_229
  recurrence4B2A4_coeff_230
  recurrence4B2A4_coeff_231
  recurrence4B2A4_coeff_232
  recurrence4B2A4_coeff_233
  recurrence4B2A4_coeff_234
  recurrence4B2A4_coeff_235
  recurrence4B2A4_coeff_236
  recurrence4B2A4_coeff_237
  recurrence4B2A4_coeff_238
  recurrence4B2A4_coeff_239
  recurrence4B2A4_coeff_240
  recurrence4B2A4_coeff_241
  recurrence4B2A4_coeff_242
  recurrence4B2A4_coeff_243
  recurrence4B2A4_coeff_244
  recurrence4B2A4_coeff_245
  recurrence4B2A4_coeff_246
  recurrence4B2A4_coeff_247
  recurrence4B2A4_coeff_248
  recurrence4B2A4_coeff_249
  recurrence4B2A4_coeff_250
  recurrence4B2A4_coeff_251
  recurrence4B2A4_coeff_252
  recurrence4B2A4_coeff_253
  recurrence4B2A4_coeff_254
  recurrence4B2A4_coeff_255
  recurrence4B2A4_coeff_256
  recurrence4B2A4_coeff_257
  recurrence4B2A4_coeff_258
  recurrence4B2A4_coeff_259
  recurrence4B2A4_coeff_260
  recurrence4B2A4_coeff_261
  recurrence4B2A4_coeff_262
  recurrence4B2A4_coeff_263
  recurrence4B2A4_coeff_264
  recurrence4B2A4_coeff_265
  recurrence4B2A4_coeff_266
  recurrence4B2A4_coeff_267
  recurrence4B2A4_coeff_268
  recurrence4B2A4_coeff_269
  recurrence4B2A4_coeff_270
  recurrence4B2A4_coeff_271
  recurrence4B2A4_coeff_272
  recurrence4B2A4_coeff_273
  recurrence4B2A4_coeff_274
  recurrence4B2A4_coeff_275
  recurrence4B2A4_coeff_276
  recurrence4B2A4_coeff_277
  recurrence4B2A4_coeff_278
  recurrence4B2A4_coeff_279
  recurrence4B2A4_coeff_280
  recurrence4B2A4_coeff_281
  recurrence4B2A4_coeff_282
  recurrence4B2A4_coeff_283
  recurrence4B2A4_coeff_284
  recurrence4B2A4_coeff_285
  recurrence4B2A4_coeff_286
  recurrence4B2A4_coeff_287
  recurrence4B2A4_coeff_288
  recurrence4B2A4_coeff_289
  recurrence4B2A4_coeff_290
  recurrence4B2A4_coeff_291
  recurrence4B2A4_coeff_292

attribute [local simp]
  recurrence4B2A4_coeff_293
  recurrence4B2A4_coeff_294
  recurrence4B2A4_coeff_295
  recurrence4B2A4_coeff_296
  recurrence4B2A4_coeff_297
  recurrence4B2A4_coeff_298
  recurrence4B2A4_coeff_299
  recurrence4B2A4_coeff_300
  recurrence4B2A4_coeff_301
  recurrence4B2A4_coeff_302
  recurrence4B2A4_coeff_303
  recurrence4B2A4_coeff_304
  recurrence4B2A4_coeff_305
  recurrence4B2A4_coeff_306
  recurrence4B2A4_coeff_307
  recurrence4B2A4_coeff_308
  recurrence4B2A4_coeff_309
  recurrence4B2A4_coeff_310
  recurrence4B2A4_coeff_311
  recurrence4B2A4_coeff_312
  recurrence4B2A4_coeff_313
  recurrence4B2A4_coeff_314
  recurrence4B2A4_coeff_315
  recurrence4B2A4_coeff_316
  recurrence4B2A4_coeff_317
  recurrence4B2A4_coeff_318
  recurrence4B2A4_coeff_319
  recurrence4B2A4_coeff_320
  recurrence4B2A4_coeff_321
  recurrence4B2A4_coeff_322
  recurrence4B2A4_coeff_323
  recurrence4B2A4_coeff_324
  recurrence4B2A4_coeff_325
  recurrence4B2A4_coeff_326
  recurrence4B2A4_coeff_327
  recurrence4B2A4_coeff_328
  recurrence4B2A4_coeff_329
  recurrence4B2A4_coeff_330
  recurrence4B2A4_coeff_331
  recurrence4B2A4_coeff_332
  recurrence4B2A4_coeff_333
  recurrence4B2A4_coeff_334
  recurrence4B2A4_coeff_335
  recurrence4B2A4_coeff_336
  recurrence4B2A4_coeff_337
  recurrence4B2A4_coeff_338
  recurrence4B2A4_coeff_339
  recurrence4B2A4_coeff_340
  recurrence4B2A4_coeff_341
  recurrence4B2A4_coeff_342
  recurrence4B2A4_coeff_343
  recurrence4B2A4_coeff_344
  recurrence4B2A4_coeff_345
  recurrence4B2A4_coeff_346

theorem recurrence4QuotientConstant_coeff_0 :
    recurrence4QuotientConstant.coeff 0 =
      (-89170166772306510241792 : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_1 :
    recurrence4QuotientConstant.coeff 1 =
      (-38878748663771705909281792 : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_2 :
    recurrence4QuotientConstant.coeff 2 =
      (3140714422191890578766977899856 : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_3 :
    recurrence4QuotientConstant.coeff 3 =
      (-7766276903466305488313083464663888 : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_4 :
    recurrence4QuotientConstant.coeff 4 =
      (8999669780707250519221842913356447252 : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_5 :
    recurrence4QuotientConstant.coeff 5 =
      (-5976966547481109872690641456066908394692 : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_6 :
    recurrence4QuotientConstant.coeff 6 =
      (1586476323362230869192243052776777445293216 : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_7 :
    recurrence4QuotientConstant.coeff 7 =
      (424696800916543856211907615697379423564274020 : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_8 :
    recurrence4QuotientConstant.coeff 8 =
      (-599530216173719837922080335098935786173288122640 : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_9 :
    recurrence4QuotientConstant.coeff 9 =
      (218518352998789690799172816732981808473525601990736 : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_10 :
    recurrence4QuotientConstant.coeff 10 =
      (29312480052548660017087508916915334500696312472528968 : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_11 :
    recurrence4QuotientConstant.coeff 11 =
      (-61241419608166727289204969747735414697833970232803374119 : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_12 :
    recurrence4QuotientConstant.coeff 12 =
      (28071088242683199725387978772429048441753415650446302303570 : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_13 :
    recurrence4QuotientConstant.coeff 13 =
      (-7174161221827110926616354129596450472159581301387922613747027 : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_14 :
    recurrence4QuotientConstant.coeff 14 =
      (1103407155885751691847013984698991920901180606412758078004853453 : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_15 :
    recurrence4QuotientConstant.coeff 15 =
      (-83302247631569138106597025393429792504705800838451531726123594671 : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_16 :
    recurrence4QuotientConstant.coeff 16 =
      (-5282548033670836802784092718584212832554105756476734336266954795809 : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_17 :
    recurrence4QuotientConstant.coeff 17 =
      (3504497816299343816171894423697251764273688169610481709125257084244233 : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_18 :
    recurrence4QuotientConstant.coeff 18 =
      -((119 * 10 ^ 70 +
        1535624612198654436731761969131902617259121745220777814943924534675930) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_19 :
    recurrence4QuotientConstant.coeff 19 =
      ((38516 * 10 ^ 70 +
        5035799572803755511815377244156742494335742942283069084079377491248567) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_20 :
    recurrence4QuotientConstant.coeff 20 =
      -((10806752 * 10 ^ 70 +
        3536718006001198070500970072059944551881407497752018870739611279796557) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_21 :
    recurrence4QuotientConstant.coeff 21 =
      ((2513914774 * 10 ^ 70 +
        4605491817960198846863871637779556711260778756722016719215164538119670) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_22 :
    recurrence4QuotientConstant.coeff 22 =
      -((487769154737 * 10 ^ 70 +
        1811153814553424168822237880004729351949112273088056716896573216893251) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_23 :
    recurrence4QuotientConstant.coeff 23 =
      ((80136000221608 * 10 ^ 70 +
        8662177107231963725640467426864622255804799942937836792580066441770487) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_24 :
    recurrence4QuotientConstant.coeff 24 =
      -((11270192142035429 * 10 ^ 70 +
        9584133718754156125688538726373613826063546733488396503013002578835234) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_25 :
    recurrence4QuotientConstant.coeff 25 =
      ((1362786842075451886 * 10 ^ 70 +
        5895332249571636941121499105987333937277885355049080402448944315204132) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_26 :
    recurrence4QuotientConstant.coeff 26 =
      -((141192901984636986400 * 10 ^ 70 +
        1588989986447357812859030567080754246113068763546526220068831268522020) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_27 :
    recurrence4QuotientConstant.coeff 27 =
      ((12335148536077425710781 * 10 ^ 70 +
        1985184709745194594975864336333765115836718966015297224422069420310268) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_28 :
    recurrence4QuotientConstant.coeff 28 =
      -((868553565454787480090927 * 10 ^ 70 +
        4998986429034207452532195720408687228082842539665590982325675059523611) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_29 :
    recurrence4QuotientConstant.coeff 29 =
      ((42278722394757669612563608 * 10 ^ 70 +
        5924892459062326209129535481153380308811498317193111058095354513210678) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_30 :
    recurrence4QuotientConstant.coeff 30 =
      -((170583074402867432171892735 * 10 ^ 70 +
        5544813381437267461699020551800464630674274616179154521598531508319852) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_31 :
    recurrence4QuotientConstant.coeff 31 =
      -((263340114506663303719794651945 * 10 ^ 70 +
        8446675676318968257435695656422121690879093926804907490121011509942904) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_32 :
    recurrence4QuotientConstant.coeff 32 =
      ((39292859783763065506680408078097 * 10 ^ 70 +
        5656084712314313425565598718633670637084378380380583466116668660663220) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_33 :
    recurrence4QuotientConstant.coeff 33 =
      -((3978901787068865202299607580362704 * 10 ^ 70 +
        3999681362613366511213241234873026918764949529555900558906319862202512) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_34 :
    recurrence4QuotientConstant.coeff 34 =
      ((329160079466090269091225281906813753 * 10 ^ 70 +
        4124857779025194213969593485310703873423324918630564383363514985684954) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_35 :
    recurrence4QuotientConstant.coeff 35 =
      -((23579280023219038300989854403544981640 * 10 ^ 70 +
        3327162517505505217140201995390277144641281070859832452688151340774743) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_36 :
    recurrence4QuotientConstant.coeff 36 =
      ((1502346578098755629899301659948228880055 * 10 ^ 70 +
        5993993874926173932600295473095637291187901709297733424488196196694394) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_37 :
    recurrence4QuotientConstant.coeff 37 =
      -((86430455341632612691723252633934120623768 * 10 ^ 70 +
        9022684324922337741981959228095261447826622674233232032890889867523896) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_38 :
    recurrence4QuotientConstant.coeff 38 =
      ((4533075881890244369667933174578208092603616 * 10 ^ 70 +
        3111647196396015323236130537055214382523825810458205305417792169034224) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_39 :
    recurrence4QuotientConstant.coeff 39 =
      -((218197916482808369532081314541675669889734152 * 10 ^ 70 +
        9402376821441659849527881106414948754006743942637443874346418272330693) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_40 :
    recurrence4QuotientConstant.coeff 40 =
      ((9686872438960317331872398109510053449523202457 * 10 ^ 70 +
        4420096367279385308126684442061295059953977185098818507181092997682939) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_41 :
    recurrence4QuotientConstant.coeff 41 =
      -((398146352931122064996223610946614457725418901281 * 10 ^ 70 +
        8346416203351536196111421076849211247818976659820820770279672362774739) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_42 :
    recurrence4QuotientConstant.coeff 42 =
      ((15196099144580290904650038292044768011776714623303 * 10 ^ 70 +
        3914551354961074125846781934776669437025405610031461595902552898353834) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_43 :
    recurrence4QuotientConstant.coeff 43 =
      -((539874306599211203387099525818910498822013820755870 * 10 ^ 70 +
        5690740611181476281576866137782720432640927138864721990183634058895928) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_44 :
    recurrence4QuotientConstant.coeff 44 =
      ((17887481477303907050353606039038806283464248775699625 * 10 ^ 70 +
        5772552711006383813172686376970255253864048958921619659334578459654794) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_45 :
    recurrence4QuotientConstant.coeff 45 =
      -((553519656032192614872044259464564359996342049703692936 * 10 ^ 70 +
        9915443677927202992046918069572465234707719532131722797828651192684358) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_46 :
    recurrence4QuotientConstant.coeff 46 =
      ((16013467399705829122467080220328981961865543109154819186 * 10 ^ 70 +
        5345949517389366140894234312160395321070439989773118351990642387960216) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_47 :
    recurrence4QuotientConstant.coeff 47 =
      -((433352841182138337574363118246458583214651256339492416541 * 10 ^ 70 +
        0152641171707269854077831949993600427798475386374553884157249922864239) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_48 :
    recurrence4QuotientConstant.coeff 48 =
      ((10969646879916601778986689527486166799495391945778556967307 * 10 ^ 70 +
        2346510685193284974521442814631946926974957768769605958802817323546322) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_49 :
    recurrence4QuotientConstant.coeff 49 =
      -((259543974043490824223387253724042678976246789691394745099149 * 10 ^ 70 +
        2610233798038201267259524933021570350456391702611968605693849996524574) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_50 :
    recurrence4QuotientConstant.coeff 50 =
      ((5729528484397547587472063678650193479743876566878841511153739 * 10 ^ 70 +
        3903176785937936151253503046503512271499651183343681687921034548976989) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_51 :
    recurrence4QuotientConstant.coeff 51 =
      -((117610745592146458698609655160480403478799065193657851950924226 * 10 ^ 70 +
        9899661082111814849251208149541599539454147472141651159327330069432003) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_52 :
    recurrence4QuotientConstant.coeff 52 =
      ((2231339873809305690960572607844944918920893494704675945846836456 * 10 ^ 70 +
        2087420179072071819783787380941270490703705043760717919415374082866877) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_53 :
    recurrence4QuotientConstant.coeff 53 =
      -((38697961557163889019777621265839811041057857414857295072636565131 * 10 ^ 70 +
        3467892363925724615563719710098390310856763581455728979555141051262123) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_54 :
    recurrence4QuotientConstant.coeff 54 =
      ((600383530727256729512578099226156555003499295642315496344191154546 * 10 ^ 70 +
        9559786023760917349684965880066156611267406194827732619453938060094908) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_55 :
    recurrence4QuotientConstant.coeff 55 =
      -((7931748159635759721400369750943434531785989957766796103938426469078 * 10 ^ 70 +
        3594985322011597015139705276245395149314953953265626991883479153568867) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_56 :
    recurrence4QuotientConstant.coeff 56 =
      ((76416051888623387961359376251510841741356002149055138050864357044107 * 10 ^ 70 +
        4652799045034127829913471511784781413669002156403469108126617059926890) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_57 :
    recurrence4QuotientConstant.coeff 57 =
      -((75909483063784716002521814535661507717702054008388040084165997834648 * 10 ^ 70 +
        0324724336346991890518363622372362679263019144403220258881911730321837) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_58 :
    recurrence4QuotientConstant.coeff 58 =
      -(((2 * 10 ^ 70 +
        0809745959526969753639863683241986389660967150604311482215376117756818) * 10 ^ 70 +
        1963985409469172200962392096119080560758290014903447905016200704640352) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_59 :
    recurrence4QuotientConstant.coeff 59 =
      (((70 * 10 ^ 70 +
        3093233019461886601393914644988310797648671499786004502677203815880038) * 10 ^ 70 +
        8866117460282422002232501835586804859049164060159976543152112731976095) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_60 :
    recurrence4QuotientConstant.coeff 60 =
      -(((1671 * 10 ^ 70 +
        8208903976209440933494771781031050325369538126106401391815756499898790) * 10 ^ 70 +
        1114029376815799916076614182092754748863426215439423896469434482101235) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_61 :
    recurrence4QuotientConstant.coeff 61 =
      (((33708 * 10 ^ 70 +
        4586702526503805717996805097861414015035223547695690263103132132084430) * 10 ^ 70 +
        1118529825254936836228945881572238855046028281048620280255052959440803) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_62 :
    recurrence4QuotientConstant.coeff 62 =
      -(((610179 * 10 ^ 70 +
        8056288362187182768834217019901376695066944818306536487299847228205094) * 10 ^ 70 +
        0434792787086521431115567776778405451593262693975857792101116343468178) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_63 :
    recurrence4QuotientConstant.coeff 63 =
      (((10172283 * 10 ^ 70 +
        1824067698825665877993464560246244330264935709445835120946402741264299) * 10 ^ 70 +
        4362930343375912267094729184199920438169656947076431911904790222150966) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_64 :
    recurrence4QuotientConstant.coeff 64 =
      -(((158351879 * 10 ^ 70 +
        6503932641229393645120509953387275676763433148073942107470205150684827) * 10 ^ 70 +
        9220913098320211662105345299827114961912697096466234324254599752095525) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_65 :
    recurrence4QuotientConstant.coeff 65 =
      (((2321423922 * 10 ^ 70 +
        6268014052362050084923132342743481402964267813640762379829336565072870) * 10 ^ 70 +
        3395269297559049272575248339478422423957472708318390460580311577767659) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_66 :
    recurrence4QuotientConstant.coeff 66 =
      -(((32231278002 * 10 ^ 70 +
        5898004944432721361964044416624401214206104189604467273797422335924298) * 10 ^ 70 +
        6671972087588431562662299091071105344524730248203167671727804607307946) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_67 :
    recurrence4QuotientConstant.coeff 67 =
      (((425554769594 * 10 ^ 70 +
        8548090475616302523023882803197217858087288113976125739277811527508144) * 10 ^ 70 +
        9021026342033390339986347679369687908596646834335534511371493855504243) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_68 :
    recurrence4QuotientConstant.coeff 68 =
      -(((5359394809997 * 10 ^ 70 +
        1286309729236235861192833745786284568927743729745101470717919182999432) * 10 ^ 70 +
        4478485447289146563088601678014916761736656754317344831689665354614784) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_69 :
    recurrence4QuotientConstant.coeff 69 =
      (((64535719007448 * 10 ^ 70 +
        4450418407198394513682301042888208575880056911757012511243795727245911) * 10 ^ 70 +
        9494836630036824796488127657433282297947232110800115527730909183179052) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_70 :
    recurrence4QuotientConstant.coeff 70 =
      -(((744482025741085 * 10 ^ 70 +
        9148891993555034962794842929678607157180372239338684985119095916600610) * 10 ^ 70 +
        3749018271482341306146280649274219658679093346687467750726155615882571) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_71 :
    recurrence4QuotientConstant.coeff 71 =
      (((8241068382017627 * 10 ^ 70 +
        8445379467316794589821283352287925410901121969245713059074062660970313) * 10 ^ 70 +
        9035462451554969581034332252310092826096678168703613781589761008802476) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_72 :
    recurrence4QuotientConstant.coeff 72 =
      -(((87657781941222549 * 10 ^ 70 +
        7830544615782164183604017649793736570300982557850437659807321870843520) * 10 ^ 70 +
        8207360152750330396935722735428660476027762164756029696962317715832691) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_73 :
    recurrence4QuotientConstant.coeff 73 =
      (((897014222406715681 * 10 ^ 70 +
        6329763962347902569891336247841045195363469640916894621128784099989441) * 10 ^ 70 +
        0575567194573159316343085775486253185043430274651341993990911353069445) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_74 :
    recurrence4QuotientConstant.coeff 74 =
      -(((8840433436735135418 * 10 ^ 70 +
        4969792596810136277532260304670915805791669654017829276979211356783393) * 10 ^ 70 +
        6443014154763992101711355257284178958237952152801141740488131202785782) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_75 :
    recurrence4QuotientConstant.coeff 75 =
      (((83990159397534142149 * 10 ^ 70 +
        9400486769669526092540310044135468089463113098579089164764912070230031) * 10 ^ 70 +
        9473407096992892854596532733533026656244907835169968375628297211829138) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_76 :
    recurrence4QuotientConstant.coeff 76 =
      -(((769910127294295685543 * 10 ^ 70 +
        7476642381781239471492416406490532188622562016661812213811820049095825) * 10 ^ 70 +
        5635471347253390054347636584562522871637045332377834680154930986877938) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_77 :
    recurrence4QuotientConstant.coeff 77 =
      (((6814788564449316982555 * 10 ^ 70 +
        0632792008452596934574750201615081373724051702611414171922991765255006) * 10 ^ 70 +
        8872271102417305110676310490003230623778272323871538414117642971960048) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_78 :
    recurrence4QuotientConstant.coeff 78 =
      -(((58288439161021121010166 * 10 ^ 70 +
        6514305372710332434136186706285894446397117421456402575253253838307650) * 10 ^ 70 +
        0545050597889578581457572071844755844530436394258931720224746970934125) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_79 :
    recurrence4QuotientConstant.coeff 79 =
      (((482085616393112439401517 * 10 ^ 70 +
        9785156813514181482137340222665992887925481526455206841335881382550972) * 10 ^ 70 +
        1738653836493079086588634442391010744955424080204325793198889137444146) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_80 :
    recurrence4QuotientConstant.coeff 80 =
      -(((3857908261598109718497888 * 10 ^ 70 +
        4094834722236455700202521442006053638218055232231597239190210431851599) * 10 ^ 70 +
        2807387562936713221900390988904625675440158633871125973893455367581957) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_81 :
    recurrence4QuotientConstant.coeff 81 =
      (((29889774574281280292586133 * 10 ^ 70 +
        7842847870306292709627599245544129181178268537548818211401877126528669) * 10 ^ 70 +
        3781678730247863479196775213385182118851533543050851038011788074293607) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_82 :
    recurrence4QuotientConstant.coeff 82 =
      -(((224325310445996114165622446 * 10 ^ 70 +
        6569301945997786121988438130614340311601975297458313897308858425991049) * 10 ^ 70 +
        7361549313197504074517106123096994056765001564605719148849664180573065) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_83 :
    recurrence4QuotientConstant.coeff 83 =
      (((1631725791290800113578104360 * 10 ^ 70 +
        7081385490243602245982705837242251886089039440229680717982587510287441) * 10 ^ 70 +
        5644816052166122345859054672797205571770013826725496013274962210926503) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_84 :
    recurrence4QuotientConstant.coeff 84 =
      -(((11509211791684575183914219529 * 10 ^ 70 +
        8934684658403355701909152221022045293203473381739789863999528985940610) * 10 ^ 70 +
        2437779839273597169910285465050723199983108035948922033291435846075816) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_85 :
    recurrence4QuotientConstant.coeff 85 =
      (((78755110983578679919095137508 * 10 ^ 70 +
        5201789141791110548960122297016423967185672574410700433047740905552544) * 10 ^ 70 +
        4757888206544438834610865434876342655493971403569948651823498375898638) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_86 :
    recurrence4QuotientConstant.coeff 86 =
      -(((523048446769367767739700634205 * 10 ^ 70 +
        7244308346423984071959862940763899312561012219698148532320810727652176) * 10 ^ 70 +
        6163766051007880618169210524956909960313597256885146254890683569286284) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_87 :
    recurrence4QuotientConstant.coeff 87 =
      (((3373037189726081244092785108602 * 10 ^ 70 +
        8643172983942674384724075895779605801098101770054481379959367482187193) * 10 ^ 70 +
        4187035341330241619425186291632920708982484150353930065803146901170170) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_88 :
    recurrence4QuotientConstant.coeff 88 =
      -(((21129728952045686931293620074837 * 10 ^ 70 +
        5707225320233835516884380504824930790547515466864520679670756596979985) * 10 ^ 70 +
        4331221292514385577009552597884259507615009994766833353807327549511441) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_89 :
    recurrence4QuotientConstant.coeff 89 =
      (((128626350471093313862311661504622 * 10 ^ 70 +
        0507298570667320513133045227267240748159087727556525625726870470487156) * 10 ^ 70 +
        5793672218592445349355689319905719754178784292601138339939603927520166) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_90 :
    recurrence4QuotientConstant.coeff 90 =
      -(((761187171447141293719513967262397 * 10 ^ 70 +
        8545198155947929009073172351416962703245696356941820461977211662327031) * 10 ^ 70 +
        0414383466090715056738827405590326835271888095231310093369411007827484) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_91 :
    recurrence4QuotientConstant.coeff 91 =
      (((4380602168856969834627906570194278 * 10 ^ 70 +
        9684449339657447965606235091083492111432088892192838609361428502488316) * 10 ^ 70 +
        1277348458983110403102709218605034236219038917805998888990127181538279) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_92 :
    recurrence4QuotientConstant.coeff 92 =
      -(((24524820860848402564703301448681348 * 10 ^ 70 +
        6986183630744903830988798360536656587863207015039956283968896927313408) * 10 ^ 70 +
        1770419901044213407344536997614029533063348678530406309195566117159265) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_93 :
    recurrence4QuotientConstant.coeff 93 =
      (((133613466182457048360535282311072228 * 10 ^ 70 +
        6263849321820214465330009185688264035243691217395542952057962642143131) * 10 ^ 70 +
        2945189985106386600158987328713537525880958976254446525205965520019804) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_94 :
    recurrence4QuotientConstant.coeff 94 =
      -(((708604357442016208273131917557554511 * 10 ^ 70 +
        5632105798714035272892404961326387284650966707547389206578393040536149) * 10 ^ 70 +
        2812633673964510275703885694074692316679098798421192276485188214630408) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_95 :
    recurrence4QuotientConstant.coeff 95 =
      (((3659299060259611540326860306884750547 * 10 ^ 70 +
        1473764180453250302555626524519614576229888673073058851044680691808594) * 10 ^ 70 +
        7477924104280636762683158592813667898817347643166672336686908753886153) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_96 :
    recurrence4QuotientConstant.coeff 96 =
      -(((18405960878861986175867670258662426449 * 10 ^ 70 +
        3511249452789311814091196956699088404422833294911808964527934709857960) * 10 ^ 70 +
        6237078675288398232100550192607649320573746682694955174761985454763960) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_97 :
    recurrence4QuotientConstant.coeff 97 =
      (((90200001645372889463783719485808481931 * 10 ^ 70 +
        8960794951847287522242409999239744956236230403220506736906214330532001) * 10 ^ 70 +
        0216987273722705478030711944901038732264711297120291802296287901855767) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_98 :
    recurrence4QuotientConstant.coeff 98 =
      -(((430782622894333121131395754669974912974 * 10 ^ 70 +
        9043952489639608119931196293611609791439645332099820522192703156112713) * 10 ^ 70 +
        6318744565844674132591510476948173408802907209095620626178233238457723) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_99 :
    recurrence4QuotientConstant.coeff 99 =
      (((2005510173804788279433106910885330389827 * 10 ^ 70 +
        6783718870639326995931556703577323072750469125489505656947329147373987) * 10 ^ 70 +
        1205247764085335743227622057423262523595863544273979867027893533439931) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_100 :
    recurrence4QuotientConstant.coeff 100 =
      -(((9103610222168347779655956788274687202512 * 10 ^ 70 +
        3695130122092054216731893102410614584512183417058432168358840877209147) * 10 ^ 70 +
        2615679350977139559375065145677838895962502882873937474359409047799750) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_101 :
    recurrence4QuotientConstant.coeff 101 =
      (((40302063180332342332080691554154671022115 * 10 ^ 70 +
        9926016199057366867501271724976353403350873098725156739746085770120036) * 10 ^ 70 +
        2370868985134124460662479378978194195853728485550420863830805617547632) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_102 :
    recurrence4QuotientConstant.coeff 102 =
      -(((174046128702445153603964548880651606524137 * 10 ^ 70 +
        1121728025634031714337223019380446327847573172941258231910760084523323) * 10 ^ 70 +
        5222816332502979073799476820412605629137327241822010135087742274332007) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_103 :
    recurrence4QuotientConstant.coeff 103 =
      (((733363970155073399455929387701865942424311 * 10 ^ 70 +
        7499636932444773031847779657791417047649173723809818526395102086939929) * 10 ^ 70 +
        6760878146431224202616639739326630797994134928536369085567802992820178) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_104 :
    recurrence4QuotientConstant.coeff 104 =
      -(((3015669198028897954042574252320339666935563 * 10 ^ 70 +
        6392362310893424651152424377810361508170235573121637487663351176640689) * 10 ^ 70 +
        3099216896080578867278719773449877656325468937276029275225989598553420) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_105 :
    recurrence4QuotientConstant.coeff 105 =
      (((12104416872871256587535914422690186911382027 * 10 ^ 70 +
        5410265528936457556421607694281604163257421530189675399507158640819682) * 10 ^ 70 +
        7066456359517691898304878307472514207571621753858446063781302702397758) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_106 :
    recurrence4QuotientConstant.coeff 106 =
      -(((47433330452161064372001787461562936783357291 * 10 ^ 70 +
        9589598701736870252367011245176724156108442715080367658791021679887627) * 10 ^ 70 +
        3973498715376852559720512757359549711200002907626465509120334590306163) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_107 :
    recurrence4QuotientConstant.coeff 107 =
      (((181502667024046650297003993289114098271996214 * 10 ^ 70 +
        3178447581041544349129871545484769823718475833954312316900535877868603) * 10 ^ 70 +
        9039006934635852420892999344118514129763843419259960206007157776845481) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_108 :
    recurrence4QuotientConstant.coeff 108 =
      -(((678295235588815138156334220560327257042803352 * 10 ^ 70 +
        5873258278017485432949460372047270897902052069222647568333369151868644) * 10 ^ 70 +
        2242907911107374960111397307569730965951085341077938305998494360115353) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_109 :
    recurrence4QuotientConstant.coeff 109 =
      (((2476078192503560205207582672757011635284610235 * 10 ^ 70 +
        6105841407782256367750451786116532520153784356048593502137995416915716) * 10 ^ 70 +
        4681638419401552370134903493814883257718999237590194415889794595357059) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_110 :
    recurrence4QuotientConstant.coeff 110 =
      -(((8830597614136652582005607513147627779983448464 * 10 ^ 70 +
        4355920158292079637461014465529667361004295251380600429224206515150769) * 10 ^ 70 +
        8981070233135950162610392983617390726103316916532544288237800371160375) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_111 :
    recurrence4QuotientConstant.coeff 111 =
      (((30772533065908644360488572423164781124128518476 * 10 ^ 70 +
        9515987441520263050534598828866833283212710476544812343324114870163237) * 10 ^ 70 +
        7766486343303014703666247560384829342674118489211678552587229156276367) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_112 :
    recurrence4QuotientConstant.coeff 112 =
      -(((104796817769064034661607949756890758445532731183 * 10 ^ 70 +
        7747924159463508871657975886646348302505739808937493589961632307326297) * 10 ^ 70 +
        5848452204216653908609282644519390575832898610015427479655409808217642) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_113 :
    recurrence4QuotientConstant.coeff 113 =
      (((348823738422722958741147229319520715083414196751 * 10 ^ 70 +
        8731209544348575362969987735833482827216972854820509742775756752660723) * 10 ^ 70 +
        1930138683617891880746584776132325691433950291364885845510357032244542) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_114 :
    recurrence4QuotientConstant.coeff 114 =
      -(((1134999396048484579786139134489794487206143757261 * 10 ^ 70 +
        1020796241893347052787481114898781885343901924823406475769417039557403) * 10 ^ 70 +
        3768984831264280414576324848305542381721060883843355514571315551959714) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_115 :
    recurrence4QuotientConstant.coeff 115 =
      (((3610544567880663032273672059036149151945716136973 * 10 ^ 70 +
        0056827896522114499457347115641769621500513786719979821669506635191452) * 10 ^ 70 +
        7387257068754472717021605915339088906087987297582913813909244882709961) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_116 :
    recurrence4QuotientConstant.coeff 116 =
      -(((11230275267082609402918526786061255484437180835631 * 10 ^ 70 +
        9873848706908890397166133933394098007956055863896801214487156639380873) * 10 ^ 70 +
        6264839210654443013600054288361292353259294049705612198612611672601777) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_117 :
    recurrence4QuotientConstant.coeff 117 =
      (((34158532039416627211975191919977284695701576810382 * 10 ^ 70 +
        7739123351219883925994866955115564779234712752849511021345977075878231) * 10 ^ 70 +
        4737499808466394017194014956299588400839466516036456884494709460167885) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_118 :
    recurrence4QuotientConstant.coeff 118 =
      -(((101612470177093739313753088314244643847850954513891 * 10 ^ 70 +
        1385769235009563890702521757453759904577150436630578411286832755132969) * 10 ^ 70 +
        3952319820310630139285256704050736317591661033516177875748222546568543) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_119 :
    recurrence4QuotientConstant.coeff 119 =
      (((295650892327594659489123602692930203122108073388826 * 10 ^ 70 +
        6651878980923136809964337009582417096485633723329288068485926856087621) * 10 ^ 70 +
        5788915454449068389851202792927298600227289435527404659068071890536764) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_120 :
    recurrence4QuotientConstant.coeff 120 =
      -(((841469933047651557373767696778215104539679706396105 * 10 ^ 70 +
        0327150260521767170058418000206904121571718534460386784207659086013328) * 10 ^ 70 +
        9307583308152724517024174983368740963641550163866298191683811487562696) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_121 :
    recurrence4QuotientConstant.coeff 121 =
      (((2342963898173335472233996068862163003755400672205696 * 10 ^ 70 +
        3380164887959182538391100018156475124115032831400486544576600121232291) * 10 ^ 70 +
        0737978643836046604650864876636339831666932088043546066684698420220343) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_122 :
    recurrence4QuotientConstant.coeff 122 =
      -(((6382606485792640734291064072622900903726264119639908 * 10 ^ 70 +
        1844493223225246159311290070425757764915765357075341821620893428083058) * 10 ^ 70 +
        5053970473387193746233220070970033816429138628114293037211876817808238) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_123 :
    recurrence4QuotientConstant.coeff 123 =
      (((17012629765638539648786947535326800746080591637164166 * 10 ^ 70 +
        6215693204401128170883887826937817802839216011773592986904518672984875) * 10 ^ 70 +
        0052093573887112277670313101828469811111136363280403499169369331231840) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_124 :
    recurrence4QuotientConstant.coeff 124 =
      -(((44372991553019349419394966780737165723445308342368716 * 10 ^ 70 +
        8655286279354303483993045227956280129930473274135848886810470622502227) * 10 ^ 70 +
        8104270230610926020359811470026382342524095141385916874456788958438674) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_125 :
    recurrence4QuotientConstant.coeff 125 =
      (((113258377289194380606969345546790890546886287813283132 * 10 ^ 70 +
        3259365355422272435090529493616891393300753952556169187063528531216045) * 10 ^ 70 +
        6223370335410586184748857130829902521040606836084351803192406380707294) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_126 :
    recurrence4QuotientConstant.coeff 126 =
      -(((282913921402749156905456345527206933879959443195393740 * 10 ^ 70 +
        6224835389632495109763300273138480934059273844714246432440477854427855) * 10 ^ 70 +
        2087279956649804871520862685977922633923489573795135449881152762383782) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_127 :
    recurrence4QuotientConstant.coeff 127 =
      (((691665494819545084460055624734819047511111505805846121 * 10 ^ 70 +
        1259941593086645140786847351731840587494230471841209658056449668344631) * 10 ^ 70 +
        3203151456229364245542983521644205517807317976050622049521052521146609) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_128 :
    recurrence4QuotientConstant.coeff 128 =
      -(((1655078401765708669242544089862815911481411509073649137 * 10 ^ 70 +
        3578856646189253612051979791329147039822866172730407602841290118575979) * 10 ^ 70 +
        6458726621602907364555971855832906245198730552486962051990275325561307) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_129 :
    recurrence4QuotientConstant.coeff 129 =
      (((3876518855401104079204013310454568637806124296710878933 * 10 ^ 70 +
        5271385524099461791455240825674773145278957316314282065200172919045268) * 10 ^ 70 +
        6288176982674427355345489519652828130453419794826466217119537132466135) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_130 :
    recurrence4QuotientConstant.coeff 130 =
      -(((8887580582820292539029853695062989388610323533016813092 * 10 ^ 70 +
        1536872339449861139125212585621789612115000575422471171266246221188287) * 10 ^ 70 +
        0267889456766317880010797610781425873801600659187754478518361627765488) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_131 :
    recurrence4QuotientConstant.coeff 131 =
      (((19946105903511885026647210169356342693369717098722034832 * 10 ^ 70 +
        5463338812210441187361656313014025953930331078133182116724136556190108) * 10 ^ 70 +
        0461778734011522101187818797291306266877720237015103890899626129014002) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_132 :
    recurrence4QuotientConstant.coeff 132 =
      -(((43820488727051308866410882584668249817726352661009265645 * 10 ^ 70 +
        7175917040002607591069820584540869226668783206941163667467957907724477) * 10 ^ 70 +
        8929829534281184735045484144387471488219244288848038696826948610796961) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_133 :
    recurrence4QuotientConstant.coeff 133 =
      (((94243042963046721077384729586618220836882738988964674891 * 10 ^ 70 +
        8911350196128654731792485626340663129129357572376887034541336543134904) * 10 ^ 70 +
        9101735964089848183632218871282020352105686249917229036051586986506804) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_134 :
    recurrence4QuotientConstant.coeff 134 =
      -(((198417278631799007816688963250076152333781563779335082625 * 10 ^ 70 +
        6263593117677320552880288844942273579486300689808122023981443204566796) * 10 ^ 70 +
        6717227069915135955329000035004241216747785299074326203366389746868654) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_135 :
    recurrence4QuotientConstant.coeff 135 =
      (((408949165625223674007138575784455890801166081847182303184 * 10 ^ 70 +
        3318768050547743655332925373341129248319333381633625741838729736588773) * 10 ^ 70 +
        9285187112933942459361662804248394584435199018479575493121129149365376) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_136 :
    recurrence4QuotientConstant.coeff 136 =
      -(((825118846148886897194440168970642889319960815727190024708 * 10 ^ 70 +
        3653861644673971564273114313298186547515325125317870868189827831267928) * 10 ^ 70 +
        0184599304047377053066090482941386813760417804734746954953273858042381) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_137 :
    recurrence4QuotientConstant.coeff 137 =
      (((1629725802380171814053093304288419907410906296671419133380 * 10 ^ 70 +
        6007039506762218514327565055680890593872352529387065835024643631699279) * 10 ^ 70 +
        6487766575712281939158606352692614611130524227205377423653419764235827) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_138 :
    recurrence4QuotientConstant.coeff 138 =
      -(((3151028741628863601095115235704834812423227264532455685954 * 10 ^ 70 +
        9738273638861350093298179714892633365163423438700912891273808316915793) * 10 ^ 70 +
        7029558175852861545944762133507272037671498917576861290144655123364695) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_139 :
    recurrence4QuotientConstant.coeff 139 =
      (((5963673473093916974168097174123008110046880449763480746197 * 10 ^ 70 +
        0500751538911506699485429026982493507479330585706889425082670476779040) * 10 ^ 70 +
        8004512802324237601332338926082900786297941239655625776489857961255369) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_140 :
    recurrence4QuotientConstant.coeff 140 =
      -(((11047837409390654077395367215346936584390000355578450029413 * 10 ^ 70 +
        9578732240922108266887810619104102462366594079203370175400712877964373) * 10 ^ 70 +
        7220287419399108984265768837868291012100009544707940302031794883321557) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_141 :
    recurrence4QuotientConstant.coeff 141 =
      (((20031550137060565607088035124912993237827710892094425543005 * 10 ^ 70 +
        4683851398175777225978533548712405224756948930586590965055001320699949) * 10 ^ 70 +
        6102162278154566526812930541005104728501833215882211608386209676772167) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_142 :
    recurrence4QuotientConstant.coeff 142 =
      -(((35545980476088899857894594057062332952355578127862016429275 * 10 ^ 70 +
        0866080195413613466829822040850097662654472556654818633931674455456277) * 10 ^ 70 +
        0791710013208412694240258799256494932486133076720271680288139031038566) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_143 :
    recurrence4QuotientConstant.coeff 143 =
      (((61725086232300001889408814238874776039226166953036897207975 * 10 ^ 70 +
        1514815580098649047059139715996545187337773137118556239854957656137863) * 10 ^ 70 +
        4497512636685626095342360637578562021644620712645877827313188795139044) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_144 :
    recurrence4QuotientConstant.coeff 144 =
      -(((104875817201590574841252103484145146034037738358230715228303 * 10 ^ 70 +
        6855162125840242692516961412989828630565034755939450585562522349012051) * 10 ^ 70 +
        7293219126766175628905227745039532913397625139398107973350507754552399) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_145 :
    recurrence4QuotientConstant.coeff 145 =
      (((174328197292663517756746137597357759929698828377241042486398 * 10 ^ 70 +
        9484671950544398353898102921267035374128385182435673496002123584329499) * 10 ^ 70 +
        6391013176652293213140361256205625909012421300841881233240385461619255) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_146 :
    recurrence4QuotientConstant.coeff 146 =
      -(((283440424102216147766488055060283592583574701040481680963941 * 10 ^ 70 +
        5346889513711902229622241243143928193435735728936917427489880414823158) * 10 ^ 70 +
        7777252805612371042653803390949867299593286630620010596743460777156302) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_147 :
    recurrence4QuotientConstant.coeff 147 =
      (((450677258303490010984228447333019392689662847344146005522047 * 10 ^ 70 +
        0725197857000553787189586311151707777916720709714256243131810121031323) * 10 ^ 70 +
        8288156506555740687190212845984402472025713573262928591411922639168102) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_148 :
    recurrence4QuotientConstant.coeff 148 =
      -(((700597356426879131952304410074958005346987446925293131365564 * 10 ^ 70 +
        0798110999205490403274049321159097123108062480135989909898271828606233) * 10 ^ 70 +
        0872782415779491901447724421966783144072969747363341621871993394682862) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_149 :
    recurrence4QuotientConstant.coeff 149 =
      (((1064478838365223205374723208458326680106911748360919564559106 * 10 ^ 70 +
        9264044168165126835191339346781771082534203631561863811566008632331326) * 10 ^ 70 +
        0756005747818159303067082525869165797057938189844079755426078714885945) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_150 :
    recurrence4QuotientConstant.coeff 150 =
      -(((1580192645912407107578338127070005075065221398822148602192473 * 10 ^ 70 +
        7026135279120393324611652876288693456223784500625252783169730903891823) * 10 ^ 70 +
        4814402083763059650973400445251111950587375828350641822108003249586829) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_151 :
    recurrence4QuotientConstant.coeff 151 =
      (((2290821817454774805734116238878838455190691959944179711391696 * 10 ^ 70 +
        7687207957400777226882381659053797265093411937108973969726558269243092) * 10 ^ 70 +
        0095306405405672723997457379873175132847789863450637877803920976124906) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_152 :
    recurrence4QuotientConstant.coeff 152 =
      -(((3241455992084100945405079792546408130762236865662182350390219 * 10 ^ 70 +
        6261022156067346569853862485726779756124379703982102454547152151737298) * 10 ^ 70 +
        4752910138914034757783351481446799501922302982688345659911836416266205) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_153 :
    recurrence4QuotientConstant.coeff 153 =
      (((4473609359748931380258120516945552739395757584927672495471620 * 10 ^ 70 +
        7917191713106168471764616640154978271274124693477527147923222430460800) * 10 ^ 70 +
        8710952084887887842869154333231296950478220271247912332978909641476400) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_154 :
    recurrence4QuotientConstant.coeff 154 =
      -(((6016866249955097304473770656815923048537000578136701944583389 * 10 ^ 70 +
        8637055512866986889687362366733762995151187494615845747504513396077281) * 10 ^ 70 +
        0684779315246551393735255543713964184674781052523395297716981978999410) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_155 :
    recurrence4QuotientConstant.coeff 155 =
      (((7877693323279387418025432405989737530653639908360439767595581 * 10 ^ 70 +
        1382089657789832413911468577163835885747399787920948563978122109361340) * 10 ^ 70 +
        6646881382829878374833972796225939549757418098414032579469465500703671) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_156 :
    recurrence4QuotientConstant.coeff 156 =
      -(((10025888494262977009894566364427056396549304914247382921674441 * 10 ^ 70 +
        8003180827348457126252304952237279529259373126701411769643259966328796) * 10 ^ 70 +
        5630383408374489196345073050292281741641552312816124804590136729243029) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_157 :
    recurrence4QuotientConstant.coeff 157 =
      (((12379839518983527141778877809383844449460842773707319975973397 * 10 ^ 70 +
        4805318867173317850092045180925185418182052476557055152171667448073167) * 10 ^ 70 +
        5195189982387117764547736686776245124637443094234988136350477586804681) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_158 :
    recurrence4QuotientConstant.coeff 158 =
      -(((14792557630870983760724945693743294172623205674914359039245630 * 10 ^ 70 +
        8798377331897751648103399277417983331328705402504354987499786340130340) * 10 ^ 70 +
        7155851548856537701922308585578266687393522993321965939044368293383261) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_159 :
    recurrence4QuotientConstant.coeff 159 =
      (((17041189445449630112436392406568357443036341272419615288693766 * 10 ^ 70 +
        1081834844506456525763009293918269565764205932365939945989424301235376) * 10 ^ 70 +
        3186084942496949275398762719196142684376312125826245830915232840248738) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_160 :
    recurrence4QuotientConstant.coeff 160 =
      -(((18823198292731866431243596341988461805757239733176079283684401 * 10 ^ 70 +
        1542285207476950872105873877050658423845730239717889055921617707308722) * 10 ^ 70 +
        3186720687760654089419771321614015964575480577705750525043272387559148) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_161 :
    recurrence4QuotientConstant.coeff 161 =
      (((19762429186987629663852303852003613552480445429057070184721779 * 10 ^ 70 +
        8442502461308736689621583307672690170098659709529798740887058385935260) * 10 ^ 70 +
        1226679069012112933830207652257485055711922033421005357458459620680963) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_162 :
    recurrence4QuotientConstant.coeff 162 =
      -(((19427645280531331929718297626578692950662192050010870363798755 * 10 ^ 70 +
        3666715302617821912567792406686509219466403319715897667516902558339515) * 10 ^ 70 +
        7291777815063555362002015056565256644994156748876446499833192539532139) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_163 :
    recurrence4QuotientConstant.coeff 163 =
      (((17364754758408136419475033162548981538460528796848129036885549 * 10 ^ 70 +
        7788602281559189589392508155168694081392296786268648267296291373544482) * 10 ^ 70 +
        4331177997638529354649962847743680507517925800003142944913814536609781) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_164 :
    recurrence4QuotientConstant.coeff 164 =
      -(((13141891037415855204990386313701300477710171973751514597459225 * 10 ^ 70 +
        9225005821610150803887273876724524891960501745308149140399251021066162) * 10 ^ 70 +
        3847074413330520977051529154819963363612334236894736890361887479946792) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_165 :
    recurrence4QuotientConstant.coeff 165 =
      (((6404003919630894336228403583354170702870588453984821311309053 * 10 ^ 70 +
        3700400784747422342967155752891977497706427863832620587365455948728853) * 10 ^ 70 +
        3277638887142329945827915832220845869762209297770615183708792180730944) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_166 :
    recurrence4QuotientConstant.coeff 166 =
      (((3068920252846333929781593008969079545793461345338990816850648 * 10 ^ 70 +
        7077279770758744780439636304487811736104427870802474577449051808955478) * 10 ^ 70 +
        3836229419115714937132028171579462840022679016857546665761543318115288) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_167 :
    recurrence4QuotientConstant.coeff 167 =
      -(((15307930913237276876730181924437168762773641701998499503369181 * 10 ^ 70 +
        0484419394647059471392313178509933933739350448515223299553650046877236) * 10 ^ 70 +
        6902816647680090483474274457398136605189038548844390491125009260199240) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_168 :
    recurrence4QuotientConstant.coeff 168 =
      (((30114389663159521847660200465333860311613487707245608356155008 * 10 ^ 70 +
        8723051098454841422531159605315574063830140221072178191211675939673476) * 10 ^ 70 +
        7737275264527377504881498729628088390111539486113521555993104714169618) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_169 :
    recurrence4QuotientConstant.coeff 169 =
      -(((47040873397536138912174332945946599015694526921548991542112509 * 10 ^ 70 +
        5439847915412992296229096977052114901705000861106235369622483461419630) * 10 ^ 70 +
        3777675896312076667812619409566567854769152724973895608634298918209333) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_170 :
    recurrence4QuotientConstant.coeff 170 =
      (((65399980388362138275984379900509572553315434702448883842801413 * 10 ^ 70 +
        0263513596181535276863779081604466492888766362864835712799026154274857) * 10 ^ 70 +
        2720047839928448326997545152478102341544641899637604904937003660652215) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_171 :
    recurrence4QuotientConstant.coeff 171 =
      -(((84303675318853510617235780893130519979591605112464141874170705 * 10 ^ 70 +
        9987504503427473353934406550939612791913890109957304467918075563723201) * 10 ^ 70 +
        1692193969009366572832329887896330928787629134503986080129245431466207) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_172 :
    recurrence4QuotientConstant.coeff 172 =
      (((102731197292235025461899535482507829200081014586559056061795320 * 10 ^ 70 +
        8756202368986519185280208137840552015491763469535730534006141325528014) * 10 ^ 70 +
        6465933872141655520546802247917379730049143045146800234494869346072128) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_173 :
    recurrence4QuotientConstant.coeff 173 =
      -(((119618776910451093973917701669479933538500678804803306936659767 * 10 ^ 70 +
        6664536246952567848995860527979382337555774933049185629170629133811300) * 10 ^ 70 +
        6246555797331801564861737393903093995182052660625393316108585503716220) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_174 :
    recurrence4QuotientConstant.coeff 174 =
      (((133960396225112703035619602179985219911274453938233776602731132 * 10 ^ 70 +
        9173348837268620204599646067668156458222134323973221660018938837426172) * 10 ^ 70 +
        1033597592413547977498587693333866380686893724012281814534471472862509) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_175 :
    recurrence4QuotientConstant.coeff 175 =
      -(((144906428670697512960284910036720828585453215338374073816829201 * 10 ^ 70 +
        1760240505567958385433837650216994120981004848055915176120114063178052) * 10 ^ 70 +
        8823628139291320704470487113254821779463412452216853564635772746342747) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_176 :
    recurrence4QuotientConstant.coeff 176 =
      (((151846778030418174775293183245842798644167673137322991893859115 * 10 ^ 70 +
        8227250815819966127082198929318344375005281269706760190917946727713703) * 10 ^ 70 +
        1494302520256591461617007596367973630900739305171923392891057349278617) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_177 :
    recurrence4QuotientConstant.coeff 177 =
      -(((154467224758360097061178532302415653940813896693180726266676299 * 10 ^ 70 +
        8709835464648657498975577919254067649403158421246192693142117455473145) * 10 ^ 70 +
        5200388907804858940585419223763944611478060855700311964622573486999274) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_178 :
    recurrence4QuotientConstant.coeff 178 =
      (((152771732393679446277356186873308067798218342186346420617300579 * 10 ^ 70 +
        1061436062204155289435992688330221403473936520169859164747788926269751) * 10 ^ 70 +
        4118763733834157203765827609783404880262905023911029936857534947407490) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_179 :
    recurrence4QuotientConstant.coeff 179 =
      -(((147068703866752727435551795513605843673122004740255060200434662 * 10 ^ 70 +
        0435183235523850207953088398845464408489135359306173455340079828712788) * 10 ^ 70 +
        9927827374857042987011080952536533112090428159552247795799666434078446) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_180 :
    recurrence4QuotientConstant.coeff 180 =
      (((137924605938213830243485023166660897664006591863376332032579268 * 10 ^ 70 +
        1840095631148244153236280049273023367573285614119671704732350382861175) * 10 ^ 70 +
        9583945655406595115457194257695604336992985279591248060633560340512212) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_181 :
    recurrence4QuotientConstant.coeff 181 =
      -(((126092987526014735419905287364604309091857177224009568258610342 * 10 ^ 70 +
        3828564166092222744588689403114759713625222437433012167593400183058209) * 10 ^ 70 +
        1746370809736224686171668707262460385606620477482728198965638818808293) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_182 :
    recurrence4QuotientConstant.coeff 182 =
      (((112429905066336780202915366878090726412975026544188596512072615 * 10 ^ 70 +
        0860427873792899556811784375472757839597864005022371260241401531758435) * 10 ^ 70 +
        9061653924899102648211318071158106527721300694789172885651223898084953) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_183 :
    recurrence4QuotientConstant.coeff 183 =
      -(((97807712461038520901050221563049484394060683729820303576269473 * 10 ^ 70 +
        8327811866078258726425437277583155838177971766161423189972733866236822) * 10 ^ 70 +
        8406688938574897031014731146492318782073507693932646353303120698629958) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_184 :
    recurrence4QuotientConstant.coeff 184 =
      (((83038092255420988598601899783304950144059672950951550680932742 * 10 ^ 70 +
        6532354183252939150583716447618238130422582951320218420375104271684343) * 10 ^ 70 +
        1653352949595839059053495677172890860354433097563272914710481314583728) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_185 :
    recurrence4QuotientConstant.coeff 185 =
      -(((68812512808185388002026181887808090993773110230354368315404025 * 10 ^ 70 +
        2202856577039687734333690627028703642037829576499445435425445501185368) * 10 ^ 70 +
        3852052169663446568641399457329760932305549041350814889959315294090017) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_186 :
    recurrence4QuotientConstant.coeff 186 =
      (((55664673102997885305476961193273869901718525832389106500311299 * 10 ^ 70 +
        0290399085146959716888015178544806150122553664224173995256769429457769) * 10 ^ 70 +
        3686926514955216654858639988121278244401286394150502700676488495863373) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_187 :
    recurrence4QuotientConstant.coeff 187 =
      -(((43955710757688379510971737121696167734535956874362400076321995 * 10 ^ 70 +
        4783142814773695708540125507811266203573903253191292820425982599887859) * 10 ^ 70 +
        7270933090015590296035647417755057102094774828926883896849309120851691) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_188 :
    recurrence4QuotientConstant.coeff 188 =
      (((33879682975464729215479591267766278636158374857189949663078783 * 10 ^ 70 +
        0951029621847542320199037232330659115785342938109347931354272448976110) * 10 ^ 70 +
        5352018107884387401753208024878593735651796679317046521345928030927070) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_189 :
    recurrence4QuotientConstant.coeff 189 =
      -(((25484554532094470970045463639302636168106547388249259452089316 * 10 ^ 70 +
        2396876463564886135855108286586555644830080861667854221860245447011283) * 10 ^ 70 +
        7821938827379523610259692315827881397842360560257823887704061301561737) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_190 :
    recurrence4QuotientConstant.coeff 190 =
      (((18702838483579642687464110163033917675449067204801072054737990 * 10 ^ 70 +
        0432053701664565279166657767841501343045784960021006647504202420579999) * 10 ^ 70 +
        8729808746528652896967322325884852137746004577187015276108099402130363) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_191 :
    recurrence4QuotientConstant.coeff 191 =
      -(((13386070234399486895060872517444172697158091708289723465092272 * 10 ^ 70 +
        0998131417070047543165019045374853893399892130118321945820644249751843) * 10 ^ 70 +
        7527448435863460487397180553809389987875186343859644866865256325387409) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_192 :
    recurrence4QuotientConstant.coeff 192 =
      (((9338195945860592532453973278142685051728798333302479751948705 * 10 ^ 70 +
        7390161291073139040934230786744580134862267128801660709578499515338557) * 10 ^ 70 +
        1526777067883071805125388341798374176336713403766674830089961015808273) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_193 :
    recurrence4QuotientConstant.coeff 193 =
      -(((6344364804316966671016487547417773991894720724477691691622608 * 10 ^ 70 +
        3350142225630001563974797040558729415683479029098895511314043415724042) * 10 ^ 70 +
        1039504374927644017037303191688454760914192152709756970749287633668818) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_194 :
    recurrence4QuotientConstant.coeff 194 =
      (((4193169686333017608006811906054817166526281112931182179528849 * 10 ^ 70 +
        8632689366091802012711474794119004379913885348413025686008961308010082) * 10 ^ 70 +
        1700037074102230268144160940988652652921278665386539731566720271163859) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_195 :
    recurrence4QuotientConstant.coeff 195 =
      -(((2691788566453710883468461992917871469793439090246046704861449 * 10 ^ 70 +
        4578247448546008629496646173723975643782405928656854685349235759478051) * 10 ^ 70 +
        5342493828986266654668665352495838499959605426784029226181059952716155) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_196 :
    recurrence4QuotientConstant.coeff 196 =
      (((1674553316731671543830380109121116059957905140745298596359899 * 10 ^ 70 +
        1799072145489302412578938238867674900267674273159435495100228093414893) * 10 ^ 70 +
        6931061670392438148683293591887269258760110349314324914411892230977621) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_197 :
    recurrence4QuotientConstant.coeff 197 =
      -(((1006140384878719136792044743553834245182073322743055807956644 * 10 ^ 70 +
        1703825119052300138759542675793398950961362097659464075295108230971589) * 10 ^ 70 +
        3347848476363604876465192168138086180436098468307462942067827788481400) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_198 :
    recurrence4QuotientConstant.coeff 198 =
      (((580860093212189413440378928257649088037091851526804237332940 * 10 ^ 70 +
        9595558460014722918056422418331192503026428581249037855357019265906926) * 10 ^ 70 +
        1559401931624766928086160477522102258895944368712177686319745494747194) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_199 :
    recurrence4QuotientConstant.coeff 199 =
      -(((319499591973266862909270614490531828744944710298675742516641 * 10 ^ 70 +
        1135720258150715073903924660485942385865501709836894355705795599580468) * 10 ^ 70 +
        6602353853444968973682365520157152952825811402441077648040296957259586) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_200 :
    recurrence4QuotientConstant.coeff 200 =
      (((164956000331744348280605492285188350622752252336530899553642 * 10 ^ 70 +
        0518946458487874199566204744040758237456145614423218829318068016820039) * 10 ^ 70 +
        8675694748474857066438718313074296919711484106681536701257563965673822) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_201 :
    recurrence4QuotientConstant.coeff 201 =
      -(((77584879723723166459819616056506575028575185454683412523832 * 10 ^ 70 +
        1170817877781707767122831406537311974124814179952552825303229929223577) * 10 ^ 70 +
        0072910650240730803221686952404764029395552712644460383495456489796201) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_202 :
    recurrence4QuotientConstant.coeff 202 =
      (((30867266524113684010826823987345449894650743597506924648982 * 10 ^ 70 +
        3520753560846934869471180980442345219251636957440715776484189997868241) * 10 ^ 70 +
        8794630121609239168678268698655572205591491955382346676567265756685062) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_203 :
    recurrence4QuotientConstant.coeff 203 =
      -(((7719438929183941025350463102732823857433453687255464663674 * 10 ^ 70 +
        9389486805185642865440222178008402423093424756662398157537261619441292) * 10 ^ 70 +
        8235098912636198592217175936544192572765865520105453783278082152626151) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_204 :
    recurrence4QuotientConstant.coeff 204 =
      -(((2441047969036857663838099399514979529092854762423608898185 * 10 ^ 70 +
        5088007669035787967244268996457819652844507275916483069587088821037121) * 10 ^ 70 +
        1089258604996224319317039197785017164704717747811104622132682162958603) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_205 :
    recurrence4QuotientConstant.coeff 205 =
      (((5897837405699682376220417097481305821537313030448409976637 * 10 ^ 70 +
        7444545032139773557108404718105462424001024083185723078913059864144509) * 10 ^ 70 +
        7119420435744874824087991640124254002958298298192323971885721387703349) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_206 :
    recurrence4QuotientConstant.coeff 206 =
      -(((6207205100077499967450520878698089115248889506502639007896 * 10 ^ 70 +
        0326819996087852816290143585982043362032246754306428358313078333594779) * 10 ^ 70 +
        1202315358825527417198530244629283762113385161687713269132905717949761) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_207 :
    recurrence4QuotientConstant.coeff 207 =
      (((5267805398174696198838756214124534273751233153262542287754 * 10 ^ 70 +
        5203012097802781317828658517668086327142102726751900315311952421185951) * 10 ^ 70 +
        5767217028950419694791751276713230963916587005572790072207836678763986) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_208 :
    recurrence4QuotientConstant.coeff 208 =
      -(((4016790931061247565115453685393580131154946360584593507373 * 10 ^ 70 +
        2932165578967755164420977283385510633055751480424630666170424168041566) * 10 ^ 70 +
        5148110211199627717203105184205886916487882171961793878933032994226810) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_209 :
    recurrence4QuotientConstant.coeff 209 =
      (((2862893153573374942518714785372103855680995236703446919963 * 10 ^ 70 +
        7136941565625291798709623600800434663780957215112761388160364160120060) * 10 ^ 70 +
        7725660679577262647749997148985003968081122516174447702231492350314448) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_210 :
    recurrence4QuotientConstant.coeff 210 =
      -(((1943539337178318456783805768284025197965600612081987022775 * 10 ^ 70 +
        1214527438599080362365875542681645215643702107659778861177463620704711) * 10 ^ 70 +
        1906821250490080450899511357092289355648964927870617469485375557498775) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_211 :
    recurrence4QuotientConstant.coeff 211 =
      (((1269834195528742015581194299145982407676533571497295876508 * 10 ^ 70 +
        0194829492680975686974942818691757882889176828786996082316499525342434) * 10 ^ 70 +
        5215011465148772275364774756966285702617859198602045017569989844898611) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_212 :
    recurrence4QuotientConstant.coeff 212 =
      -(((803450699648785010793872002699182456167640109537027811669 * 10 ^ 70 +
        3628233859244204997199806587740444556395480742201896312663693846346481) * 10 ^ 70 +
        7849610526144884926184016559739027181236271523260305347040147837132291) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_213 :
    recurrence4QuotientConstant.coeff 213 =
      (((494218267307691216815011012301037599505261924184836803320 * 10 ^ 70 +
        4367696883528196663882499642007010953761430901988542663358897471841790) * 10 ^ 70 +
        7935552434811328581075370944359017019441917580368357801941012448101475) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_214 :
    recurrence4QuotientConstant.coeff 214 =
      -(((296283306841707460192359836658807775200156877396778953919 * 10 ^ 70 +
        6395672906801528788704753181048416917841677788333113254037064047966202) * 10 ^ 70 +
        9703176465992693917452275104499351886715047131843789984633272278052946) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_215 :
    recurrence4QuotientConstant.coeff 215 =
      (((173386322384733268678953647896510985334319878594959559170 * 10 ^ 70 +
        7944364776528918829788210333302089786642010069283026860405559620583447) * 10 ^ 70 +
        1843053035872381547538563591066839843675746951451031030241908455236087) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_216 :
    recurrence4QuotientConstant.coeff 216 =
      -(((99144512787817536532165903589892065204275112153241902228 * 10 ^ 70 +
        1294399942008869154647321435098619012525139704652335534063934399765806) * 10 ^ 70 +
        9476933097739557151902856658949327186232797651530603227739371755702871) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_217 :
    recurrence4QuotientConstant.coeff 217 =
      (((55425818351873629365869659954434198347377168603909378529 * 10 ^ 70 +
        6106921580159467983358907580849799122691466711235213978739492587323608) * 10 ^ 70 +
        1031191754665493944312054687042633106827032359118584015006661785880732) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_218 :
    recurrence4QuotientConstant.coeff 218 =
      -(((30301025085757060960534856203478995841012507941401893132 * 10 ^ 70 +
        7795506867915546976623712459039323283095492145225052423841793427682345) * 10 ^ 70 +
        9807336306704006656131293418997737090061776190103533077126645113444606) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_219 :
    recurrence4QuotientConstant.coeff 219 =
      (((16200203091765151802431629840794457677803530505357579533 * 10 ^ 70 +
        0778823999709044420545087012693319873634679305268766388019534070099869) * 10 ^ 70 +
        9031914471817024080903356400408514383537832127879210199376698003088893) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_220 :
    recurrence4QuotientConstant.coeff 220 =
      -(((8469258315787971351011277316312164290943943527443172477 * 10 ^ 70 +
        9917727932373754805825338614875548298651724843799893674331702197640928) * 10 ^ 70 +
        5984031691322471274782901436200163268144407259150881543091731441919469) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_221 :
    recurrence4QuotientConstant.coeff 221 =
      (((4328319522648621949974645968219377047278485985440394741 * 10 ^ 70 +
        8349206751604258298401804153712892276696828895199112336336098159595031) * 10 ^ 70 +
        5070647161706077883725626269348549346685105244007022218033868499216940) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_222 :
    recurrence4QuotientConstant.coeff 222 =
      -(((2161636132844489514636473902984188162176329196162205720 * 10 ^ 70 +
        9944630925668266338558861439684494561838851621660185108457856500290351) * 10 ^ 70 +
        9294261059069768972321741116829503908987531133904945491837566225493295) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_223 :
    recurrence4QuotientConstant.coeff 223 =
      (((1054468694072750563423848014174276310273926677628713741 * 10 ^ 70 +
        0296062521244545623128061896402202391022485256634932629170998588332054) * 10 ^ 70 +
        5143548029949695524166908786215904603816323672914856330284983455836123) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_224 :
    recurrence4QuotientConstant.coeff 224 =
      -(((502146485764440865845058523839625689685592680087179966 * 10 ^ 70 +
        1144336831561789628665205910382669986495003428451509265274883022101160) * 10 ^ 70 +
        1962424875734030940315740998763211624620750605812855532991936263196116) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_225 :
    recurrence4QuotientConstant.coeff 225 =
      (((233285479637079622030957865697908521194987397041777986 * 10 ^ 70 +
        2021219463949872875933292153314250409853666360813373755963029841809909) * 10 ^ 70 +
        2332593415255103249470878614091917795818565064069672086548439898578727) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_226 :
    recurrence4QuotientConstant.coeff 226 =
      -(((105650595787947942443281224993822871739343115108098063 * 10 ^ 70 +
        0096320362438629004252890524145970140044021657832557999630626174821274) * 10 ^ 70 +
        1300358142239843467542671401157988701700407238403904560116933361320715) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_227 :
    recurrence4QuotientConstant.coeff 227 =
      (((46600652393499579120730283222312393768600967585959082 * 10 ^ 70 +
        4241021368682771377105721165821269235286924653171396912339908064098003) * 10 ^ 70 +
        6800084318792081544298169070239407684594354663098958472153215645175466) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_228 :
    recurrence4QuotientConstant.coeff 228 =
      -(((19997974978479774605802549716458252230832478301847792 * 10 ^ 70 +
        4081594246166101941125194789005070100332640797453870848274935408365481) * 10 ^ 70 +
        0615745775448358869907385523770026665764945023392192273660003999538640) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_229 :
    recurrence4QuotientConstant.coeff 229 =
      (((8338802612051514021901845497818730618349815786623931 * 10 ^ 70 +
        7893818328399805513021188981930019289707157128540899129001136330740448) * 10 ^ 70 +
        2858296417587551984565413057850179065824888691410705852695737336634530) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_230 :
    recurrence4QuotientConstant.coeff 230 =
      -(((3373515555377132245279071492586566523880299733523419 * 10 ^ 70 +
        0260652081640231335484823203277798394276556342117471886507130181406315) * 10 ^ 70 +
        3429683455236892000213304425625377720210123249588019028423936290753610) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_231 :
    recurrence4QuotientConstant.coeff 231 =
      (((1321658175296826832902667049726221641460214907034927 * 10 ^ 70 +
        7623705783244919896259953193147779051652751966803118206279633593803266) * 10 ^ 70 +
        3145132026566953558163432258445093881426936372471251951852165815199055) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_232 :
    recurrence4QuotientConstant.coeff 232 =
      -(((500302423494945496053790722361989558671620511439848 * 10 ^ 70 +
        0891872388360072464338408316025425956164769083679091959032957042589392) * 10 ^ 70 +
        8779877448467588870524965755627027152877000376208393539801488524899104) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_233 :
    recurrence4QuotientConstant.coeff 233 =
      (((182487457933491667344416889328414928605161343988571 * 10 ^ 70 +
        1344190419602450034630779878514402943801704812295716605529288483707885) * 10 ^ 70 +
        8106144796096918667229377333139960789473900114879981311853750814273266) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_234 :
    recurrence4QuotientConstant.coeff 234 =
      -(((63931070879772968543037150462991017553062423938141 * 10 ^ 70 +
        7536383360246619227490841091106817551571145393330463406440504619121490) * 10 ^ 70 +
        4948890328473902852232693922388558219730305911984550055907352468332625) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_235 :
    recurrence4QuotientConstant.coeff 235 =
      (((21435290093530260165101837861119933691055341992859 * 10 ^ 70 +
        0840108237495244814033311249562190198977963477686214522404382476904639) * 10 ^ 70 +
        8380807576671450365627935909742381480170992567911960997194145013691151) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_236 :
    recurrence4QuotientConstant.coeff 236 =
      -(((6858070720926600241742433026706277578571876824030 * 10 ^ 70 +
        3023986722216411505573752716072938237356913287833542420191033215893496) * 10 ^ 70 +
        0438643347263847801082001762409430378777577508427467834096451497019352) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_237 :
    recurrence4QuotientConstant.coeff 237 =
      (((2094979102693683933819181320363267047207916480653 * 10 ^ 70 +
        8884115014548990432435886245802984938346007971109346326091375499363203) * 10 ^ 70 +
        1539632722616752288903879958186705059002855264143997881901684493903582) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_238 :
    recurrence4QuotientConstant.coeff 238 =
      -(((618750747113563318139030192510255742896069842003 * 10 ^ 70 +
        1968653265711394638845422126848339279388823827247860712733473665523026) * 10 ^ 70 +
        3356709709436091227235436037155773763610632714876679230555020272045801) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_239 :
    recurrence4QuotientConstant.coeff 239 =
      (((184702350479243572035181645525816309790500013095 * 10 ^ 70 +
        3958170785370777624471128285068208181025598032925148045858552365516833) * 10 ^ 70 +
        0524332694433920243581176156120827476741066850879776105446765478700687) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_240 :
    recurrence4QuotientConstant.coeff 240 =
      -(((61526714564208989540153661696654039983295076856 * 10 ^ 70 +
        6632854656512176750865568095234634665833988559727973437868558047828367) * 10 ^ 70 +
        4940490887143272115698094226703080747409309728805360551306890363559298) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_241 :
    recurrence4QuotientConstant.coeff 241 =
      (((25497165389355112550153875709886030131423472531 * 10 ^ 70 +
        0229457014008995282562184858555928541903410127170926045499509952133276) * 10 ^ 70 +
        9514397510536815662488924027445512078769435065254424853930211183450178) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_242 :
    recurrence4QuotientConstant.coeff 242 =
      -(((12985715047499503613984926792720336171893408639 * 10 ^ 70 +
        4686673470760050067040877049872252242656299028554618300564039732975095) * 10 ^ 70 +
        8682140416039543567100107561127615149550684802750372213733009889020854) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_243 :
    recurrence4QuotientConstant.coeff 243 =
      (((7241104385426111394354124136983159380795341444 * 10 ^ 70 +
        6705748177520369158021191096309809343952512551689099552162085765135504) * 10 ^ 70 +
        5703026787606756461685208577943532873847174010657220216586560711164257) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_244 :
    recurrence4QuotientConstant.coeff 244 =
      -(((4038656858998811600546900324672481547547897963 * 10 ^ 70 +
        6216882886220320568079442821981832559472385485702793171727704535567612) * 10 ^ 70 +
        3922405155851324322081774487176178942153173443292312545845409542686035) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_245 :
    recurrence4QuotientConstant.coeff 245 =
      (((2169362004242977641793952568673526439886351090 * 10 ^ 70 +
        0374693795939636046323192806157788600030135793094142603232407227277980) * 10 ^ 70 +
        2445236626538887047348639117611836234914262127114136385826449264648021) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_246 :
    recurrence4QuotientConstant.coeff 246 =
      -(((1110685146379386276713680182886286074452872086 * 10 ^ 70 +
        2488570225090140549350012424418110109867165410542221090468107597394804) * 10 ^ 70 +
        5761273800096774686843130135804999616735708019622900523858582022167717) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_247 :
    recurrence4QuotientConstant.coeff 247 =
      (((541659076285583000341249472233518887089907783 * 10 ^ 70 +
        5892099575605217100612740023118039190482473637794655551318191292887885) * 10 ^ 70 +
        6817314912288160624495771623033192489702950850432891105001052114545070) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_248 :
    recurrence4QuotientConstant.coeff 248 =
      -(((252066394846134136238202086347313723046991545 * 10 ^ 70 +
        9452788982771450662568780794091356455400086908818088821701500298430377) * 10 ^ 70 +
        9021021739861720532849825098918423881065102154044611077863123299859151) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_249 :
    recurrence4QuotientConstant.coeff 249 =
      (((112130023478299727978372311491547333514605343 * 10 ^ 70 +
        4444884853308635742423574832912018961943835361152379645506248369843721) * 10 ^ 70 +
        9272286178958948399288859883926946437018891059486379784668339625495090) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_250 :
    recurrence4QuotientConstant.coeff 250 =
      -(((47727114679346724378041984603276472758462198 * 10 ^ 70 +
        8478697873701347165354744391181722242629833082994519710356034257391017) * 10 ^ 70 +
        7978547642565685568820834885194452019854706450238481997821149820686505) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_251 :
    recurrence4QuotientConstant.coeff 251 =
      (((19436822707414176797208681602707345518362909 * 10 ^ 70 +
        5732765041382329898058030016340013822609006242739660666282255079970457) * 10 ^ 70 +
        8274571730560196143142329037950150457277654422495113349304693328818759) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_252 :
    recurrence4QuotientConstant.coeff 252 =
      -(((7564980100599329493913220962428025996502343 * 10 ^ 70 +
        5010420758341359504509037528109740875957322104786311312263258810778937) * 10 ^ 70 +
        0939223634618692536909399598021622898783550576861271783741559283335970) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_253 :
    recurrence4QuotientConstant.coeff 253 =
      (((2807266159478469048957355203730518973493789 * 10 ^ 70 +
        2329470682002436437103741469911103596089961929164729462626429619542142) * 10 ^ 70 +
        1399006280622231517479885874557948230604222757035194134344949124004168) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_254 :
    recurrence4QuotientConstant.coeff 254 =
      -(((989360186511478270470998841295855804120126 * 10 ^ 70 +
        5038052694174458431225166032235272998618577280760200595605638048787637) * 10 ^ 70 +
        5831747343736358433529231831795093958669280631023376177775983575033652) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_255 :
    recurrence4QuotientConstant.coeff 255 =
      (((329132623058618787791101831097826433963266 * 10 ^ 70 +
        0525439147623668993807732997888567673015568188515661194726025505637836) * 10 ^ 70 +
        3219269742662568051302988277768736294697472035462015024432260147912850) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_256 :
    recurrence4QuotientConstant.coeff 256 =
      -(((102363259549147115528750552533808384546430 * 10 ^ 70 +
        2569464161281125355812271515754603304385936768353597239278773538778808) * 10 ^ 70 +
        6094140892005101667103771835940439613518092386370068359292605341282290) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_257 :
    recurrence4QuotientConstant.coeff 257 =
      (((29283839670361142994644521815201013178129 * 10 ^ 70 +
        9981161429899178673834981270552413843298753612834667739487368414559532) * 10 ^ 70 +
        4781192273945270533905258747521908268576005613540616259462683175741517) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_258 :
    recurrence4QuotientConstant.coeff 258 =
      -(((7473245415226828296907798092429793602062 * 10 ^ 70 +
        6787540999205231603790035402914015381576797354641243686992698253303278) * 10 ^ 70 +
        4218114242895136125021355236218602100775966918432765678014016594787370) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_259 :
    recurrence4QuotientConstant.coeff 259 =
      (((1584187869438200184009423970790449935962 * 10 ^ 70 +
        0556564358877330039338185058443953249696526381532846935960173140371984) * 10 ^ 70 +
        4016552442882998790618178473583270854461574877938991163608222523562948) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_260 :
    recurrence4QuotientConstant.coeff 260 =
      -(((214939803054132343816910462767861631449 * 10 ^ 70 +
        6193517521388963713334983697385629924851855070971961810181830397428474) * 10 ^ 70 +
        8905638000570983220428727816000134541201950661786110451254946524076440) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_261 :
    recurrence4QuotientConstant.coeff 261 =
      -(((22611780513399393469247775645523761865 * 10 ^ 70 +
        6952840124630484161563497307468716361371719141492342270897837462001989) * 10 ^ 70 +
        8542235673473471636647076950525964930564426017159032994701633298551270) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_262 :
    recurrence4QuotientConstant.coeff 262 =
      (((31478317295914309761538385141917426429 * 10 ^ 70 +
        1743397998900985034797802345329262090723592498600724815132485298290642) * 10 ^ 70 +
        3775752661977441243520203329756156314928932547486419168513398758262533) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_263 :
    recurrence4QuotientConstant.coeff 263 =
      -(((15067014295076954030721001524529519939 * 10 ^ 70 +
        2042046007931336612396231491513456942502112192020876880671000587000701) * 10 ^ 70 +
        1143898377642571877982788092004210096961085411478690094032660017830727) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_264 :
    recurrence4QuotientConstant.coeff 264 =
      (((5331974177053319429232868838381514246 * 10 ^ 70 +
        4107865638344738239817847558454202777033147177769086911127751177219871) * 10 ^ 70 +
        1048412426678321308933251278108860819024359877765157177472453359672144) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_265 :
    recurrence4QuotientConstant.coeff 265 =
      -(((1532011555663304765226184724370569204 * 10 ^ 70 +
        5044886100175931435530593203538212967894193731893477233371112987893809) * 10 ^ 70 +
        2099039606466369951646812764303768422606790644516715169076767971067766) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_266 :
    recurrence4QuotientConstant.coeff 266 =
      (((355641745708891231419126208992129290 * 10 ^ 70 +
        0499503902889194672442597197106823831613772560051848534551417751676238) * 10 ^ 70 +
        7034620814542494347495068844353878032276232844180015065560654034756490) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_267 :
    recurrence4QuotientConstant.coeff 267 =
      -(((61745727683857534635454653649812831 * 10 ^ 70 +
        4781718318112935072067016540934833876632784731383751160267699959102495) * 10 ^ 70 +
        6612580992338797479821475780105763901213124080531908055179094907228812) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_268 :
    recurrence4QuotientConstant.coeff 268 =
      (((6688372547907335494965718098228208 * 10 ^ 70 +
        8416449987964963525114618678305773357031654379432415007552977493847585) * 10 ^ 70 +
        0921908787141904258482405836386794557460508142091652740670199882990140) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_269 :
    recurrence4QuotientConstant.coeff 269 =
      -(((1198437996435518414584131814747886 * 10 ^ 70 +
        0803601367195319489630570129979539458096890921662497095779854051747860) * 10 ^ 70 +
        1652428100311730548017872002703398177423035032597963129486322167432401) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_270 :
    recurrence4QuotientConstant.coeff 270 =
      (((1682440767269081862672787380992806 * 10 ^ 70 +
        5214032398349815887174497012239486223344934591456648810536461105060405) * 10 ^ 70 +
        6297565702324021384391158233039157884319003122574677892971404968122313) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_271 :
    recurrence4QuotientConstant.coeff 271 =
      -(((1587563621770642138361134088341812 * 10 ^ 70 +
        5609217583059261369127322508763316105480669074765821086539955005914677) * 10 ^ 70 +
        2304340087751620177012682212334681514519365679361044698662579036926442) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_272 :
    recurrence4QuotientConstant.coeff 272 =
      (((1063273166977722414526219451881247 * 10 ^ 70 +
        2750019634942749436797820959005075931259747323044762096815739039675448) * 10 ^ 70 +
        2611090012013471121580222811577351289928326195060340280247986378520048) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_273 :
    recurrence4QuotientConstant.coeff 273 =
      -(((586606063819870949502524976197987 * 10 ^ 70 +
        9061834456087721365685607783711086653523076395045807725869225394337288) * 10 ^ 70 +
        1874689365211228140869936388972499236668802533424154578915652085134071) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_274 :
    recurrence4QuotientConstant.coeff 274 =
      (((285954812924427060392331593768883 * 10 ^ 70 +
        2975023370455789047029543700316048776733481145995031253186736567904187) * 10 ^ 70 +
        2373880237319473193869427723309632142774393760322829080177243497472339) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_275 :
    recurrence4QuotientConstant.coeff 275 =
      -(((127673940848278981938800362030610 * 10 ^ 70 +
        5406252757763443805235634093175245093879923832912479310790776990657211) * 10 ^ 70 +
        9169215709539999633712841625783329779310984665908657279842764880379438) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_276 :
    recurrence4QuotientConstant.coeff 276 =
      (((53242652021118468429664598715297 * 10 ^ 70 +
        3796016399783093836016938390780702482578397503072356018895717370582636) * 10 ^ 70 +
        2401723943458365136024700384570141694216027152809464660547935495262228) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_277 :
    recurrence4QuotientConstant.coeff 277 =
      -(((20958915159584167715522357477196 * 10 ^ 70 +
        2928696936746106946383469123334599358826798712612477491115747773624518) * 10 ^ 70 +
        5516860585554922833815087692268813711807169530852021885556337629918910) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_278 :
    recurrence4QuotientConstant.coeff 278 =
      (((7828339366749481260152990529905 * 10 ^ 70 +
        5848511947792854618462991957153307998515718751582533165390068439340909) * 10 ^ 70 +
        8986673943575034345504257164009074576659806843844063671607252819441737) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_279 :
    recurrence4QuotientConstant.coeff 279 =
      -(((2778966327039905134558754458309 * 10 ^ 70 +
        9565262710017474907781095827608042302240591029364776858660954401647457) * 10 ^ 70 +
        3517312192955496458927629253835927010439822421260644529119615648811023) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_280 :
    recurrence4QuotientConstant.coeff 280 =
      (((936889585361091947556236465495 * 10 ^ 70 +
        8622215864022680613612026283905212101146113483368544464397957860798750) * 10 ^ 70 +
        3604119309043637600184021691522397064390343537712610126290921960204851) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_281 :
    recurrence4QuotientConstant.coeff 281 =
      -(((299192500950672592936564189148 * 10 ^ 70 +
        9109794337572236427118819730163987833481995075308243919656263449271945) * 10 ^ 70 +
        8389322553658633884513937435952079794772497706297170348772849392069084) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_282 :
    recurrence4QuotientConstant.coeff 282 =
      (((90101311879542814841245815728 * 10 ^ 70 +
        8305460178884821708484223486285154267703194639185889413534998202746846) * 10 ^ 70 +
        4661018580515596785452567688958060514577580715329928324488092470976402) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_283 :
    recurrence4QuotientConstant.coeff 283 =
      -(((25411364146075255403226050626 * 10 ^ 70 +
        2715599539007859804209273266788568194591102139771322731024814192094503) * 10 ^ 70 +
        6514946229016230376983882723043852527605897488873615609968422677406637) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_284 :
    recurrence4QuotientConstant.coeff 284 =
      (((6638503767564339050756364959 * 10 ^ 70 +
        0222632347003921496754767893766648003875996919049455966549267029181027) * 10 ^ 70 +
        8269998196471984104250938693671110029227539643166823096685350879977856) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_285 :
    recurrence4QuotientConstant.coeff 285 =
      -(((1576071100603504502767252219 * 10 ^ 70 +
        1152449232561845354709777361345119138446144734577597915185853301206610) * 10 ^ 70 +
        9760962242408847596726812493090444793668692693943039390444213555583234) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_286 :
    recurrence4QuotientConstant.coeff 286 =
      (((327227994676950216220294562 * 10 ^ 70 +
        5393683390156156274535015039981989703055478446715135081237033279264470) * 10 ^ 70 +
        8927739251020858302269062982865715710305628374691678263307771335010731) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_287 :
    recurrence4QuotientConstant.coeff 287 =
      -(((53708074869216334983568983 * 10 ^ 70 +
        7444278458214358660954079432213244262736656861341167725541883157864405) * 10 ^ 70 +
        7550703146344224794362049393261022135300710916577997449612256605258033) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_288 :
    recurrence4QuotientConstant.coeff 288 =
      (((4149208219070144523783912 * 10 ^ 70 +
        2680924717749372295388015613134309820738803914523903708265621148369440) * 10 ^ 70 +
        1940518320543718966813021181029896764131382015158820620144164451925044) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_289 :
    recurrence4QuotientConstant.coeff 289 =
      (((1558920429560740108723293 * 10 ^ 70 +
        3215330457583745404909358468010964140012515674543413632315638510987560) * 10 ^ 70 +
        9540381002657165011159945600883983554976766336714903460972184338324726) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_290 :
    recurrence4QuotientConstant.coeff 290 =
      -(((1014412419821291771506494 * 10 ^ 70 +
        5349700927251253890327300701683556550026337353507474317746803025932979) * 10 ^ 70 +
        6675778120037656511373383355217579133178997078468245725292051034852269) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_291 :
    recurrence4QuotientConstant.coeff 291 =
      (((379977316747196139108711 * 10 ^ 70 +
        2444981493666524717889657674515426210777040385959916162692332297764158) * 10 ^ 70 +
        9870516601058395758174220343714527949118697483361503875788064990493878) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_292 :
    recurrence4QuotientConstant.coeff 292 =
      -(((114589907157097893221008 * 10 ^ 70 +
        2024902333156321291680884657881299070073462985235920383242650922288426) * 10 ^ 70 +
        2239373524114955881813986481303956568243861297820009008019275739491164) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_293 :
    recurrence4QuotientConstant.coeff 293 =
      (((30038789887672096959700 * 10 ^ 70 +
        9581249758293747397483461937112784377072473663791213297284006481536881) * 10 ^ 70 +
        6033478917806382372120809731346606003401248488105859001856355545261405) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_294 :
    recurrence4QuotientConstant.coeff 294 =
      -(((7037127286726183422075 * 10 ^ 70 +
        6871125872813222929025473754668237011411334060657941674284643430293098) * 10 ^ 70 +
        2464028886730278901063257433167183187038832655202588022229033663897011) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_295 :
    recurrence4QuotientConstant.coeff 295 =
      (((1489000219003299158234 * 10 ^ 70 +
        7622253965176026750486208783348879390069497837843766754668491328811816) * 10 ^ 70 +
        3374859943524403316866250616345158239538497099327327343558644159380675) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_296 :
    recurrence4QuotientConstant.coeff 296 =
      -(((285145568126419115529 * 10 ^ 70 +
        9247863442157943340639115434224307221302622046249214587471804791549372) * 10 ^ 70 +
        9856250105297122113298622362754383833226431214489734289666899981643578) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_297 :
    recurrence4QuotientConstant.coeff 297 =
      (((49212167773082820785 * 10 ^ 70 +
        5331567244214071267415808623234906968054368061167663387300128003453428) * 10 ^ 70 +
        4108612883852840713194323977444570908006954805763171319897395582207542) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_298 :
    recurrence4QuotientConstant.coeff 298 =
      -(((7568490487452333876 * 10 ^ 70 +
        3580622869727866617917349683787307541208026094118364698117196387607501) * 10 ^ 70 +
        7755599653273388987578121276780899043499602905653310601759735382136560) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_299 :
    recurrence4QuotientConstant.coeff 299 =
      (((1013565350464704090 * 10 ^ 70 +
        1966138475991368193831469818353729053435451926466797732070187834615094) * 10 ^ 70 +
        2059983437824193976180339671696735291315051977631355049219113812436286) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_300 :
    recurrence4QuotientConstant.coeff 300 =
      -(((112337908966791014 * 10 ^ 70 +
        4045999151753827875020288574706146191621403667434451994551757351170038) * 10 ^ 70 +
        5164319032525049412575782375323261529795399287534577013785559844270275) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_301 :
    recurrence4QuotientConstant.coeff 301 =
      (((8864137619307867 * 10 ^ 70 +
        1263768087521295752119164983250036028672266964916439965711081491582626) * 10 ^ 70 +
        2541013995905573490226661251939647794045806968903533487169883232791544) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_302 :
    recurrence4QuotientConstant.coeff 302 =
      -(((113078144405481 * 10 ^ 70 +
        2451015037658861099571554878259801658294624618324835200220076116667518) * 10 ^ 70 +
        6076448168539303184001041605398238592058043322182171429069635893963762) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_303 :
    recurrence4QuotientConstant.coeff 303 =
      -(((124588128864112 * 10 ^ 70 +
        9146922588827796300506477173842573910884464269655958051825871969019044) * 10 ^ 70 +
        7720322186792731267624407622683438529182304940730125116060350614935445) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_304 :
    recurrence4QuotientConstant.coeff 304 =
      (((29668824313356 * 10 ^ 70 +
        8561982175874770321639257886126423872311994971035348219415625261080733) * 10 ^ 70 +
        5367537171119671634934631548418135274597787177797583815555118926953078) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_305 :
    recurrence4QuotientConstant.coeff 305 =
      -(((4526967258137 * 10 ^ 70 +
        5344699795289364752646064005871723596765701881314554971128863350625127) * 10 ^ 70 +
        4380118116538964912738363991891036266660947012603664970004179591088953) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_306 :
    recurrence4QuotientConstant.coeff 306 =
      (((527712924320 * 10 ^ 70 +
        0779842835798914052488053628466052078855914819769466387932742367946251) * 10 ^ 70 +
        2887954930038498649932086951064875989286682361238407387077896326297265) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_307 :
    recurrence4QuotientConstant.coeff 307 =
      -(((47881350888 * 10 ^ 70 +
        0725321518790758668159604200306715741085160300471632252872091745239255) * 10 ^ 70 +
        3200632801448718796735568333501628383203972182168461834399875526962391) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_308 :
    recurrence4QuotientConstant.coeff 308 =
      (((3168936054 * 10 ^ 70 +
        0863988530036404563845414397343452378235042280474391687737307139509102) * 10 ^ 70 +
        5133843568491889497289385705722086228420772055182344257430524269930393) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_309 :
    recurrence4QuotientConstant.coeff 309 =
      -(((109155892 * 10 ^ 70 +
        3771646258193337685628465662304269139135774798853578294491469512935434) * 10 ^ 70 +
        9414466332474553566937989505086186199067101891139029807549198126928046) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_310 :
    recurrence4QuotientConstant.coeff 310 =
      -(((5739600 * 10 ^ 70 +
        7510886836535052838024161519640250973242343658330210082535548951816711) * 10 ^ 70 +
        7084916987193280927514178143267874496200255541074025663691587028195291) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_311 :
    recurrence4QuotientConstant.coeff 311 =
      (((1286907 * 10 ^ 70 +
        8674105236663014124073286272932742024563847304422499090744969952133870) * 10 ^ 70 +
        3651994854606953445913434714416360020434071330141620101427474809109168) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_312 :
    recurrence4QuotientConstant.coeff 312 =
      -(((111713 * 10 ^ 70 +
        8725771261720977783243980793954810147060703795913250797840500179880225) * 10 ^ 70 +
        2955922906710282216515654635465133341163283851569271820627673190035450) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_313 :
    recurrence4QuotientConstant.coeff 313 =
      (((5640 * 10 ^ 70 +
        4663678480211964626647327014326845865671158226986448442453754114525889) * 10 ^ 70 +
        5491858613915622031735129133983886155770530373432262334622324388924584) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_314 :
    recurrence4QuotientConstant.coeff 314 =
      -(((112 * 10 ^ 70 +
        8464958949454882940239179764074233361294283981925960029935793688625895) * 10 ^ 70 +
        5040807549044150761153562246887170257331461570654980398806310607765131) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_315 :
    recurrence4QuotientConstant.coeff 315 =
      -(((6 * 10 ^ 70 +
        2948675408506228652402038993601406968621838298621320046324767092720800) * 10 ^ 70 +
        5646055237168142366665053229186856129870603030703933741097220323567121) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_316 :
    recurrence4QuotientConstant.coeff 316 =
      ((5798168437149540285773620194301016872023492374498948165284330776068994 * 10 ^ 70 +
        9026893878659336355218101778283938388761571414805142759278312086672615) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_317 :
    recurrence4QuotientConstant.coeff 317 =
      -((164070356636393808470154864601372327815893377340064349270760603332629 * 10 ^ 70 +
        9190699954188716407672585809063071734615541572017219200309271949947538) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_318 :
    recurrence4QuotientConstant.coeff 318 =
      -((1261734505882718134909461932327447675266926286440843092891476112887 * 10 ^ 70 +
        8897552823278703271418088480003231309714029534879963861291124344182060) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_319 :
    recurrence4QuotientConstant.coeff 319 =
      ((173253732847401707324802821105438376753658399549667016241039213965 * 10 ^ 70 +
        5183873891825146043520333406524859681561711793278802993608542352419912) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_320 :
    recurrence4QuotientConstant.coeff 320 =
      -((1540158925058299236184350045870168850421379791569876663844327884 * 10 ^ 70 +
        1883680298617813348946275778417990935602041059349971663555663719202024) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_321 :
    recurrence4QuotientConstant.coeff 321 =
      -((69368210809153619281537135842900635157970191940868522699656228 * 10 ^ 70 +
        7875408541977987114399391918367296034302729698023895751707658647947730) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_322 :
    recurrence4QuotientConstant.coeff 322 =
      ((271379954375289688734171121006183951088826767982307806499642 * 10 ^ 70 +
        4032333904008661468116528175140746038282628123443209933774612726057589) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_323 :
    recurrence4QuotientConstant.coeff 323 =
      ((12685471335494975780876326957388477401582928983372289093558 * 10 ^ 70 +
        0826469150861031809584628028921894152827851285316959102029150202357092) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_324 :
    recurrence4QuotientConstant.coeff 324 =
      ((51446709315271880882775724779127196052434786502191794559 * 10 ^ 70 +
        2768786538477179579410356014512017279827902322664156076860881986366922) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_325 :
    recurrence4QuotientConstant.coeff 325 =
      -((375847082529099852924797187160195309462438196162084163 * 10 ^ 70 +
        1145118329762338135194433892122616636088686765119375522307812026351795) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_326 :
    recurrence4QuotientConstant.coeff 326 =
      -((2995266878383790988345051711370668848803890470078272 * 10 ^ 70 +
        4284546374323560720071788912113136813951089999543085256301899281090937) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_327 :
    recurrence4QuotientConstant.coeff 327 =
      -((1892444014083030728452700303995578421104093141252 * 10 ^ 70 +
        0929197238622089078153132865549367994052813139863622648726190420812172) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_328 :
    recurrence4QuotientConstant.coeff 328 =
      ((30510868897605525383605335146113107297913694968 * 10 ^ 70 +
        3767171283704135876987223272941856709753906954121292343844347615990389) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_329 :
    recurrence4QuotientConstant.coeff 329 =
      ((53999733611657102594956714827913064914235815 * 10 ^ 70 +
        9627609271781782118226653866461377078299878311599176012516556612214578) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_330 :
    recurrence4QuotientConstant.coeff 330 =
      -((121061419790347027464505364499345724319492 * 10 ^ 70 +
        2543371471099212029908685898457208847964770617689262294514788084937095) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_331 :
    recurrence4QuotientConstant.coeff 331 =
      -((268396049908815980702240833288221935130 * 10 ^ 70 +
        8631775204421347707377177238063380282933858111314594750706242729034829) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_332 :
    recurrence4QuotientConstant.coeff 332 =
      ((211602280981364092686700843549436803 * 10 ^ 70 +
        2852731210990935808796338308877604423150386722129310956072257350665944) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_333 :
    recurrence4QuotientConstant.coeff 333 =
      ((437983917331852712448286055659507 * 10 ^ 70 +
        4375669129379394693308100426142876807634925243795735318008735424297356) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_334 :
    recurrence4QuotientConstant.coeff 334 =
      -((116393588686419899150181354188 * 10 ^ 70 +
        6888642919111225068770949947269398392757495487553572854727866286081776) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_335 :
    recurrence4QuotientConstant.coeff 335 =
      -((158480136938173074385349311 * 10 ^ 70 +
        6632946439778771160656089214055309596772611877527945373533323801461899) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_336 :
    recurrence4QuotientConstant.coeff 336 =
      ((6771644776801000029589 * 10 ^ 70 +
        5788555378235850466128804262345515487455349567908581758342792976121597) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_337 :
    recurrence4QuotientConstant.coeff 337 =
      ((6563518340534919174 * 10 ^ 70 +
        1043416383916032629322198879786884754818802720301903320218838062967599) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_338 :
    recurrence4QuotientConstant.coeff 338 =
      -((5173539693002 * 10 ^ 70 +
        9406921883776740241107471906396200870245356024738134572108276395787632) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_339 :
    recurrence4QuotientConstant.coeff 339 =
      -((19994356366 * 10 ^ 70 +
        2225016879886564887814949854238895938854655278185192035767850193399825) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_340 :
    recurrence4QuotientConstant.coeff 340 =
      -((26005 * 10 ^ 70 +
        9840178250006986666736999755438658426379020589433874834189803415544062) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_341 :
    recurrence4QuotientConstant.coeff 341 =
      ((2 * 10 ^ 70 +
        6770873701961581975195450129292507541754504829916063295852880365963830) : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_342 :
    recurrence4QuotientConstant.coeff 342 =
      (6759702568464643914662930211573559078704362961582112929964754008 : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_343 :
    recurrence4QuotientConstant.coeff 343 =
      (-69857336366188377519184842829653436956766143109775968938347 : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_344 :
    recurrence4QuotientConstant.coeff 344 =
      (-522429817212141052338639961170393974006216868073984 : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_345 :
    recurrence4QuotientConstant.coeff 345 =
      (734975993110784863738516306301947502670332911 : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_coeff_346 :
    recurrence4QuotientConstant.coeff 346 =
      (-197950142294076144279030129151110841 : ℚ) := by
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  norm_num

theorem recurrence4QuotientConstant_natDegree_le :
    recurrence4QuotientConstant.natDegree ≤ 346 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n h
  unfold recurrence4QuotientConstant
  rw [Polynomial.coeff_sub]
  rw [recurrence4B3A3_coeff_high n (by omega)]
  rw [recurrence4B2A4_coeff_high n (by omega)]
  norm_num

theorem recurrence4QuotientConstant_coeff_high
    (n : ℕ) (h : 346 < n) :
    recurrence4QuotientConstant.coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact lt_of_le_of_lt recurrence4QuotientConstant_natDegree_le h

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA4Square
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupExceptional
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupExceptionalProductPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: ExceptionalProduct coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4A4Square_coeff_205
  recurrence4A4Square_coeff_206
  recurrence4A4Square_coeff_207
  recurrence4A4Square_coeff_208
  recurrence4A4Square_coeff_209
  recurrence4A4Square_coeff_210
  recurrence4A4Square_coeff_211
  recurrence4A4Square_coeff_212
  recurrence4A4Square_coeff_213
  recurrence4A4Square_coeff_214
  recurrence4A4Square_coeff_215
  recurrence4A4Square_coeff_216
  recurrence4A4Square_coeff_217
  recurrence4A4Square_coeff_218
  recurrence4A4Square_coeff_219
  recurrence4A4Square_coeff_220
  recurrence4A4Square_coeff_221
  recurrence4A4Square_coeff_222
  recurrence4A4Square_coeff_223
  recurrence4A4Square_coeff_224
  recurrence4A4Square_coeff_225
  recurrence4A4Square_coeff_226
  recurrence4A4Square_coeff_227
  recurrence4A4Square_coeff_228
  recurrence4A4Square_coeff_229
  recurrence4A4Square_coeff_230
  recurrence4A4Square_coeff_231
  recurrence4A4Square_coeff_232
  recurrence4A4Square_coeff_233
  recurrence4A4Square_coeff_234
  recurrence4A4Square_coeff_235
  recurrence4A4Square_coeff_236
  recurrence4A4Square_coeff_237
  recurrence4A4Square_coeff_238
  recurrence4A4Square_coeff_239
  recurrence4A4Square_coeff_240
  recurrence4A4Square_coeff_241
  recurrence4A4Square_coeff_242
  recurrence4A4Square_coeff_243
  recurrence4A4Square_coeff_244
  recurrence4A4Square_coeff_245
  recurrence4A4Square_coeff_246
  recurrence4A4Square_coeff_247
  recurrence4A4Square_coeff_248
  recurrence4A4Square_coeff_249
  recurrence4A4Square_coeff_250
  recurrence4A4Square_coeff_251
  recurrence4A4Square_coeff_252
  recurrence4A4Square_coeff_253
  recurrence4A4Square_coeff_254
  recurrence4A4Square_coeff_255
  recurrence4A4Square_coeff_256
  recurrence4A4Square_coeff_257
  recurrence4A4Square_coeff_258
  recurrence4A4Square_coeff_259
  recurrence4A4Square_coeff_260
  recurrence4A4Square_coeff_261
  recurrence4A4Square_coeff_262
  recurrence4A4Square_coeff_263
  recurrence4A4Square_coeff_264
  recurrence4A4Square_coeff_265
  recurrence4A4Square_coeff_266
  recurrence4A4Square_coeff_267
  recurrence4A4Square_coeff_268

attribute [local simp]
  recurrence4A4Square_coeff_269
  recurrence4A4Square_coeff_270
  recurrence4A4Square_coeff_271
  recurrence4A4Square_coeff_272
  recurrence4A4Square_coeff_273
  recurrence4A4Square_coeff_274
  recurrence4A4Square_coeff_275
  recurrence4A4Square_coeff_276
  recurrence4A4Square_coeff_277
  recurrence4A4Square_coeff_278
  recurrence4A4Square_coeff_279
  recurrence4A4Square_coeff_280
  recurrence4A4Square_coeff_281
  recurrence4A4Square_coeff_282
  recurrence4A4Square_coeff_283
  recurrence4A4Square_coeff_284
  recurrence4A4Square_coeff_285
  recurrence4A4Square_coeff_286
  recurrence4A4Square_coeff_287
  recurrence4A4Square_coeff_288
  recurrence4A4Square_coeff_289
  recurrence4A4Square_coeff_290
  recurrence4A4Square_coeff_291
  recurrence4A4Square_coeff_292
  recurrence4A4Square_coeff_293
  recurrence4A4Square_coeff_294
  recurrence4A4Square_coeff_295
  recurrence4A4Square_coeff_296
  recurrence4A4Square_coeff_297
  recurrence4A4Square_coeff_298
  recurrence4A4Square_coeff_299
  recurrence4A4Square_coeff_300
  recurrence4A4Square_coeff_301
  recurrence4A4Square_coeff_302
  recurrence4A4Square_coeff_303
  recurrence4A4Square_coeff_304
  recurrence4A4Square_coeff_305
  recurrence4A4Square_coeff_306
  recurrence4A4Square_coeff_307
  recurrence4A4Square_coeff_308
  recurrence4A4Square_coeff_309
  recurrence4A4Square_coeff_310
  recurrence4A4Square_coeff_311
  recurrence4A4Square_coeff_312
  recurrence4A4Square_coeff_313
  recurrence4A4Square_coeff_314
  recurrence4A4Square_coeff_315
  recurrence4A4Square_coeff_316
  recurrence4A4Square_coeff_317
  recurrence4A4Square_coeff_318
  recurrence4A4Square_coeff_319
  recurrence4A4Square_coeff_320
  recurrence4A4Square_coeff_321
  recurrence4A4Square_coeff_322
  recurrence4A4Square_coeff_323
  recurrence4A4Square_coeff_324
  recurrence4A4Square_coeff_325
  recurrence4A4Square_coeff_326
  recurrence4A4Square_coeff_327
  recurrence4A4Square_coeff_328
  recurrence4A4Square_coeff_329
  recurrence4A4Square_coeff_330
  recurrence4A4Square_coeff_331
  recurrence4A4Square_coeff_332

attribute [local simp]
  recurrence4A4Square_coeff_333
  recurrence4A4Square_coeff_334
  recurrence4A4Square_coeff_335
  recurrence4A4Square_coeff_336
  recurrence4A4Square_coeff_337
  recurrence4A4Square_coeff_338
  recurrence4A4Square_coeff_339
  recurrence4A4Square_coeff_340
  recurrence4A4Square_coeff_341
  recurrence4A4Square_coeff_342
  recurrence4A4Square_coeff_343
  recurrence4A4Square_coeff_344
  recurrence4A4Square_coeff_345
  recurrence4A4Square_coeff_346
  recurrence4A4Square_coeff_347
  recurrence4A4Square_coeff_348
  recurrence4A4Square_coeff_349
  recurrence4A4Square_coeff_350
  recurrence4A4Square_coeff_351
  recurrence4A4Square_coeff_352
  recurrence4A4Square_coeff_353
  recurrence4A4Square_coeff_354
  recurrence4A4Square_coeff_355
  recurrence4A4Square_coeff_356
  recurrence4Exceptional_coeff_0
  recurrence4Exceptional_coeff_1
  recurrence4Exceptional_coeff_10
  recurrence4Exceptional_coeff_11
  recurrence4Exceptional_coeff_12
  recurrence4Exceptional_coeff_13
  recurrence4Exceptional_coeff_2
  recurrence4Exceptional_coeff_3
  recurrence4Exceptional_coeff_4
  recurrence4Exceptional_coeff_5
  recurrence4Exceptional_coeff_6
  recurrence4Exceptional_coeff_7
  recurrence4Exceptional_coeff_8
  recurrence4Exceptional_coeff_9

private theorem recurrence4ExceptionalProduct_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 205,
      recurrence4A4Square.coeff x * exceptional4.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (218 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_218 :
    recurrence4ExceptionalProduct.coeff 218 =
      (
        -(((69886646058011959852561131741574439679448072125677808801549 * 10 ^ 70 +
          0305568978238714739187696883211749996794900566599373334647809458115579) * 10 ^ 70 +
          9248848623790723924768241858155881267072673304821249818075775973931163)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 219,
    recurrence4A4Square.coeff x * exceptional4.coeff (218 - x)) = _
  rw [show 219 = 205 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_218_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 206,
      recurrence4A4Square.coeff x * exceptional4.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (219 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_219 :
    recurrence4ExceptionalProduct.coeff 219 =
      (
        (((43887514880954737832116195106121367755515404427619703509356 * 10 ^ 70 +
          5750146263603773421449224593466839946986919999961577111782499620862633) * 10 ^ 70 +
          5137611814651225954358102709139892028328189109685360031324835128909903)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 220,
    recurrence4A4Square.coeff x * exceptional4.coeff (219 - x)) = _
  rw [show 220 = 206 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_219_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 207,
      recurrence4A4Square.coeff x * exceptional4.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (220 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_220 :
    recurrence4ExceptionalProduct.coeff 220 =
      (
        -(((27064331744273554803897277199394365170192810983709676342962 * 10 ^ 70 +
          8213693405946015699979807403441588401138218907278002165237350657709521) * 10 ^ 70 +
          3109519006783717375211950108951034077367456888601258357765033581775001)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 221,
    recurrence4A4Square.coeff x * exceptional4.coeff (220 - x)) = _
  rw [show 221 = 207 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_220_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 208,
      recurrence4A4Square.coeff x * exceptional4.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (221 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_221 :
    recurrence4ExceptionalProduct.coeff 221 =
      (
        (((16388554915167436825325651032988782856428383435594109296277 * 10 ^ 70 +
          8733942365591797183744638104242432288048558976867722274424669783694879) * 10 ^ 70 +
          1607747222109744520295534007582608368673995165777224988587341140037201)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 222,
    recurrence4A4Square.coeff x * exceptional4.coeff (221 - x)) = _
  rw [show 222 = 208 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_221_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 209,
      recurrence4A4Square.coeff x * exceptional4.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (222 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_222 :
    recurrence4ExceptionalProduct.coeff 222 =
      (
        -(((9744243090592749701140151054074591406717432102658694833372 * 10 ^ 70 +
          8767797415779410754013528008014268151262200663827640333466090982579591) * 10 ^ 70 +
          7039093342312844193481612693215173207775625274242238606207053191576276)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 223,
    recurrence4A4Square.coeff x * exceptional4.coeff (222 - x)) = _
  rw [show 223 = 209 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_222_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 210,
      recurrence4A4Square.coeff x * exceptional4.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (223 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_223 :
    recurrence4ExceptionalProduct.coeff 223 =
      (
        (((5688481750460392531783483692340243541613087124603157229602 * 10 ^ 70 +
          4737771816122173019455063980211884555666729442386610866553460167920808) * 10 ^ 70 +
          8041283952130678267046332181103990949370484846393402177256168860363328)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 224,
    recurrence4A4Square.coeff x * exceptional4.coeff (223 - x)) = _
  rw [show 224 = 210 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_223_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 211,
      recurrence4A4Square.coeff x * exceptional4.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (224 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_224 :
    recurrence4ExceptionalProduct.coeff 224 =
      (
        -(((3260332692492335635127307635947034038689378493890474481532 * 10 ^ 70 +
          2279055988821971260362200020517256617413104382347203267840961496065578) * 10 ^ 70 +
          4909304527308813214760411005464137440900289666131915071266123160051049)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 225,
    recurrence4A4Square.coeff x * exceptional4.coeff (224 - x)) = _
  rw [show 225 = 211 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_224_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 212,
      recurrence4A4Square.coeff x * exceptional4.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (225 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_225 :
    recurrence4ExceptionalProduct.coeff 225 =
      (
        (((1834514477508256331093445394447104649878584624590311613796 * 10 ^ 70 +
          4673101383482761146973430642179818594574729028847427140908568094667518) * 10 ^ 70 +
          3607463989876743115641419264026996591084212319306600701833232329114573)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 226,
    recurrence4A4Square.coeff x * exceptional4.coeff (225 - x)) = _
  rw [show 226 = 212 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_225_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 213,
      recurrence4A4Square.coeff x * exceptional4.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (226 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_226 :
    recurrence4ExceptionalProduct.coeff 226 =
      (
        -(((1013329048720287681651383444341114396383082655640179348307 * 10 ^ 70 +
          3078984366220168407558179676185366500127713910236513769141526693285294) * 10 ^ 70 +
          9960272622417941157584645090333315232694640445042831203017442591397029)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 227,
    recurrence4A4Square.coeff x * exceptional4.coeff (226 - x)) = _
  rw [show 227 = 213 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_226_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 214,
      recurrence4A4Square.coeff x * exceptional4.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (227 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_227 :
    recurrence4ExceptionalProduct.coeff 227 =
      (
        (((549448082337460648832435773055829426452908667503452380910 * 10 ^ 70 +
          1918439380833136938343114812350783447197111855378086225300255520197743) * 10 ^ 70 +
          0302106367875140533410962691984222374350903864936083183430385020413219)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 228,
    recurrence4A4Square.coeff x * exceptional4.coeff (227 - x)) = _
  rw [show 228 = 214 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_227_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 215,
      recurrence4A4Square.coeff x * exceptional4.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (228 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_228 :
    recurrence4ExceptionalProduct.coeff 228 =
      (
        -(((292433275837475220399783653868545724059982560599898690246 * 10 ^ 70 +
          1934813752984111118386749775320881946724234733070083405326171416504680) * 10 ^ 70 +
          1993935798083658686018262730984605866938518609343223038131102041683403)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 229,
    recurrence4A4Square.coeff x * exceptional4.coeff (228 - x)) = _
  rw [show 229 = 215 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_228_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 216,
      recurrence4A4Square.coeff x * exceptional4.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (229 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_229 :
    recurrence4ExceptionalProduct.coeff 229 =
      (
        (((152766684207857680210010656924962464153308869739255118227 * 10 ^ 70 +
          3376004292503430864771494051612275578179118580557439644390730554556897) * 10 ^ 70 +
          4042854036971738433664851564526929016140933641508246220986494341179053)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 230,
    recurrence4A4Square.coeff x * exceptional4.coeff (229 - x)) = _
  rw [show 230 = 216 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_229_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 217,
      recurrence4A4Square.coeff x * exceptional4.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (230 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_230 :
    recurrence4ExceptionalProduct.coeff 230 =
      (
        -(((78326883747780991448940884775173845538948646663046757621 * 10 ^ 70 +
          8497900516046200429317762141725281904751188506705162423551462800282253) * 10 ^ 70 +
          3528109251071005977298835184343969380420295335124817112521832654754471)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 231,
    recurrence4A4Square.coeff x * exceptional4.coeff (230 - x)) = _
  rw [show 231 = 217 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_230_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 218,
      recurrence4A4Square.coeff x * exceptional4.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (231 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_231 :
    recurrence4ExceptionalProduct.coeff 231 =
      (
        (((39414218058521005930709921911000595716663798059372120134 * 10 ^ 70 +
          5002002346856291324051272464266329959281537561511625470199216113505348) * 10 ^ 70 +
          7270649114656139029563601134636512175791374238845475855186418678200307)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 232,
    recurrence4A4Square.coeff x * exceptional4.coeff (231 - x)) = _
  rw [show 232 = 218 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_231_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 219,
      recurrence4A4Square.coeff x * exceptional4.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (232 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_232 :
    recurrence4ExceptionalProduct.coeff 232 =
      (
        -(((19464145121048771722635038203863954693355422953231233367 * 10 ^ 70 +
          6143878004613464441208737055870891200753706159888180540817867436166932) * 10 ^ 70 +
          1026932779174643707384217883613457798518335647954921111844618498218811)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 233,
    recurrence4A4Square.coeff x * exceptional4.coeff (232 - x)) = _
  rw [show 233 = 219 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_232_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 220,
      recurrence4A4Square.coeff x * exceptional4.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (233 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_233 :
    recurrence4ExceptionalProduct.coeff 233 =
      (
        (((9432771576587185282038101809820907607988531426261620183 * 10 ^ 70 +
          1418541734133802939044102230418767677567101460060906798780341452851292) * 10 ^ 70 +
          8232520117450212369330260521941927987446574894798173189227261021144543)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 234,
    recurrence4A4Square.coeff x * exceptional4.coeff (233 - x)) = _
  rw [show 234 = 220 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_233_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 221,
      recurrence4A4Square.coeff x * exceptional4.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (234 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_234 :
    recurrence4ExceptionalProduct.coeff 234 =
      (
        -(((4485865262576681696212613504577276585349511201593426618 * 10 ^ 70 +
          3788144700387277403328108685493942633172325193396846122844489201085094) * 10 ^ 70 +
          9006545469796572408088764035682605752843564363489641735996431811589020)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 235,
    recurrence4A4Square.coeff x * exceptional4.coeff (234 - x)) = _
  rw [show 235 = 221 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_234_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 222,
      recurrence4A4Square.coeff x * exceptional4.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (235 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_235 :
    recurrence4ExceptionalProduct.coeff 235 =
      (
        (((2093323575530544623223592872439069049820413557686981606 * 10 ^ 70 +
          7311025994625955454627471039369584751632421380566884221491097430116953) * 10 ^ 70 +
          4176237709479742075875348369581593068214926531848289015714749596106074)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 236,
    recurrence4A4Square.coeff x * exceptional4.coeff (235 - x)) = _
  rw [show 236 = 222 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_235_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 223,
      recurrence4A4Square.coeff x * exceptional4.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (236 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_236 :
    recurrence4ExceptionalProduct.coeff 236 =
      (
        -(((958488298726218348176849614156523174225699880025336641 * 10 ^ 70 +
          6114672162604736361309915945032591389847740076911900009981289822385283) * 10 ^ 70 +
          8895172959594340952930522830649497128159505563407667518109469750677502)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 237,
    recurrence4A4Square.coeff x * exceptional4.coeff (236 - x)) = _
  rw [show 237 = 223 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_236_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 224,
      recurrence4A4Square.coeff x * exceptional4.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (237 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_237 :
    recurrence4ExceptionalProduct.coeff 237 =
      (
        (((430593715317397872540306608504651003472494390432563283 * 10 ^ 70 +
          9180579219872375881541973368779052324287517178797167039177769381998443) * 10 ^ 70 +
          2968731385674228376783496075981096665954346662894218202344700732111174)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 238,
    recurrence4A4Square.coeff x * exceptional4.coeff (237 - x)) = _
  rw [show 238 = 224 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_237_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 225,
      recurrence4A4Square.coeff x * exceptional4.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (238 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_238 :
    recurrence4ExceptionalProduct.coeff 238 =
      (
        -(((14597973938559881044936071953196886938412448238627202 * 10 ^ 70 +
          0057165017167757671721754374507109078842674617621121189308863304695867) * 10 ^ 70 +
          7898905739520599318291153791892884666533238777386681989665142589544251)) /
        (1785787687194522429613 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 239,
    recurrence4A4Square.coeff x * exceptional4.coeff (238 - x)) = _
  rw [show 239 = 225 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_238_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 226,
      recurrence4A4Square.coeff x * exceptional4.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (239 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_239 :
    recurrence4ExceptionalProduct.coeff 239 =
      (
        (((82039947302172037361484018557049377647577110029899716 * 10 ^ 70 +
          2601692025164363101749819801993095250210742405417654714686039844091110) * 10 ^ 70 +
          9599110756557679315885972867203340265413542504143199687141464628960183)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 240,
    recurrence4A4Square.coeff x * exceptional4.coeff (239 - x)) = _
  rw [show 240 = 226 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_239_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 227,
      recurrence4A4Square.coeff x * exceptional4.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (240 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_240 :
    recurrence4ExceptionalProduct.coeff 240 =
      (
        -(((2675391637456406071481047379604221318369856356813813 * 10 ^ 70 +
          9131273174198219790226082320465414266165119667357269668690815225524159) * 10 ^ 70 +
          2496018304491695318197765432760479809793902636085730622611896541292478)) /
        (1785787687194522429613 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 241,
    recurrence4A4Square.coeff x * exceptional4.coeff (240 - x)) = _
  rw [show 241 = 227 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_240_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 228,
      recurrence4A4Square.coeff x * exceptional4.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (241 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_241 :
    recurrence4ExceptionalProduct.coeff 241 =
      (
        (((14453810438788071181812113231116624990274121121027118 * 10 ^ 70 +
          6261716703013013064064030973521373542012460330019722025524245381157200) * 10 ^ 70 +
          6520522063862542056007895679083492795616562453898313964176920345768994)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 242,
    recurrence4A4Square.coeff x * exceptional4.coeff (241 - x)) = _
  rw [show 242 = 228 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_241_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 229,
      recurrence4A4Square.coeff x * exceptional4.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (242 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_242 :
    recurrence4ExceptionalProduct.coeff 242 =
      (
        -(((5884455989146163230653920224692222332839621475292940 * 10 ^ 70 +
          9263957992286761802015782812272474416868424451486363758456822227956258) * 10 ^ 70 +
          8111811359092513440649624828417410798099311002845195590570739585869144)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 243,
    recurrence4A4Square.coeff x * exceptional4.coeff (242 - x)) = _
  rw [show 243 = 229 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_242_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 230,
      recurrence4A4Square.coeff x * exceptional4.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (243 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_243 :
    recurrence4ExceptionalProduct.coeff 243 =
      (
        (((2344554643273329663832004726347776914902576510653397 * 10 ^ 70 +
          0074220561771810811846871955059554117015743059917837558245060854184802) * 10 ^ 70 +
          3352894175638467484373539902774412256780387963715533495725664677621074)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 244,
    recurrence4A4Square.coeff x * exceptional4.coeff (243 - x)) = _
  rw [show 244 = 230 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_243_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 231,
      recurrence4A4Square.coeff x * exceptional4.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (244 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_244 :
    recurrence4ExceptionalProduct.coeff 244 =
      (
        -(((912703703517335475583914326532983293732305686720870 * 10 ^ 70 +
          1358003176483198984485126617037154110129435687507099150026519420390547) * 10 ^ 70 +
          2608537475352331030135981704566308663751088908490213811741441915462645)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 245,
    recurrence4A4Square.coeff x * exceptional4.coeff (244 - x)) = _
  rw [show 245 = 231 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_244_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 232,
      recurrence4A4Square.coeff x * exceptional4.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (245 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_245 :
    recurrence4ExceptionalProduct.coeff 245 =
      (
        (((346220127469598641497137491542351137910578357730651 * 10 ^ 70 +
          0252868497608672661908542426704833833632364509784621996260767760942757) * 10 ^ 70 +
          5542327562577761724822517202864586838531882354913653426002104785706499)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 246,
    recurrence4A4Square.coeff x * exceptional4.coeff (245 - x)) = _
  rw [show 246 = 232 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_245_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 233,
      recurrence4A4Square.coeff x * exceptional4.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (246 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_246 :
    recurrence4ExceptionalProduct.coeff 246 =
      (
        -(((127410942381303566182410771395713106668567893312044 * 10 ^ 70 +
          0463252328451102255707080362824249800028421288299360658123198665184702) * 10 ^ 70 +
          6836526820342897009184956058686524523434230500496381002407382798612543)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 247,
    recurrence4A4Square.coeff x * exceptional4.coeff (246 - x)) = _
  rw [show 247 = 233 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_246_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 234,
      recurrence4A4Square.coeff x * exceptional4.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (247 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_247 :
    recurrence4ExceptionalProduct.coeff 247 =
      (
        (((3472744431429938458569390561128083440884230018978 * 10 ^ 70 +
          7267662039801654268998169928565004665424988088283100189736468849586758) * 10 ^ 70 +
          6335849765444521680514111790131707683331531679068566478272852570298073)) /
        (1785787687194522429613 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 248,
    recurrence4A4Square.coeff x * exceptional4.coeff (247 - x)) = _
  rw [show 248 = 234 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_247_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 235,
      recurrence4A4Square.coeff x * exceptional4.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (248 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_248 :
    recurrence4ExceptionalProduct.coeff 248 =
      (
        -(((15193736111463821544384449803027044439555804163080 * 10 ^ 70 +
          5276528163423568419389175168827649439938602188438419129666870680585611) * 10 ^ 70 +
          1907949095158072795283324216637041266278532381670626350158850676907640)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 249,
    recurrence4A4Square.coeff x * exceptional4.coeff (248 - x)) = _
  rw [show 249 = 235 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_248_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 236,
      recurrence4A4Square.coeff x * exceptional4.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (249 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_249 :
    recurrence4ExceptionalProduct.coeff 249 =
      (
        (((4726518515748588211633965961570770877501806417647 * 10 ^ 70 +
          3799808877253349769842995874726722178082301310226877103438128277735540) * 10 ^ 70 +
          2244621610172996917990708434174432008446365462711637342610989084685820)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 250,
    recurrence4A4Square.coeff x * exceptional4.coeff (249 - x)) = _
  rw [show 250 = 236 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_249_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 237,
      recurrence4A4Square.coeff x * exceptional4.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (250 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_250 :
    recurrence4ExceptionalProduct.coeff 250 =
      (
        -(((1273011856608512648672733146431238897013478525103 * 10 ^ 70 +
          9514285809223147842676100445767118475417288201860777083817950272954954) * 10 ^ 70 +
          7125340658471717339926243351385984254849110574381873477664259535753126)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 251,
    recurrence4A4Square.coeff x * exceptional4.coeff (250 - x)) = _
  rw [show 251 = 237 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_250_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 238,
      recurrence4A4Square.coeff x * exceptional4.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (251 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_251 :
    recurrence4ExceptionalProduct.coeff 251 =
      (
        (((233804116070907692934264152636686248801979794766 * 10 ^ 70 +
          0816513301848728016947634116021590750414912939451091972684475299010897) * 10 ^ 70 +
          3495603746794251632199816568276802359448662274791496471712087649502536)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 252,
    recurrence4A4Square.coeff x * exceptional4.coeff (251 - x)) = _
  rw [show 252 = 238 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_251_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 239,
      recurrence4A4Square.coeff x * exceptional4.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (252 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_252 :
    recurrence4ExceptionalProduct.coeff 252 =
      (
        (((26610275404348096556124621880292309171032173647 * 10 ^ 70 +
          2734170379659362304107168057318600956319711786351799576563414050367433) * 10 ^ 70 +
          7395791969555861452753216609432607436203317681942550826617318054583779)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 253,
    recurrence4A4Square.coeff x * exceptional4.coeff (252 - x)) = _
  rw [show 253 = 239 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_252_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 240,
      recurrence4A4Square.coeff x * exceptional4.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (253 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_253 :
    recurrence4ExceptionalProduct.coeff 253 =
      (
        -(((61918983731461898329563380092313946098431916655 * 10 ^ 70 +
          6113090557038371951710076825831605149321794093687561980255802764622160) * 10 ^ 70 +
          9664632102067702265671100904751721556966122945522202732578291391258603)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 254,
    recurrence4A4Square.coeff x * exceptional4.coeff (253 - x)) = _
  rw [show 254 = 240 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_253_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 241,
      recurrence4A4Square.coeff x * exceptional4.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (254 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_254 :
    recurrence4ExceptionalProduct.coeff 254 =
      (
        (((46143885138499964688445501934415396937753510336 * 10 ^ 70 +
          4182806045592992753955894785990004083703189571670873097135963124637935) * 10 ^ 70 +
          4573697010983423419827754799609104002674805100772501543617866768677013)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 255,
    recurrence4A4Square.coeff x * exceptional4.coeff (254 - x)) = _
  rw [show 255 = 241 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_254_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 242,
      recurrence4A4Square.coeff x * exceptional4.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (255 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_255 :
    recurrence4ExceptionalProduct.coeff 255 =
      (
        -(((27130761225294907837723341902197054048680261630 * 10 ^ 70 +
          4606062781138804445306828575077136961123633507869330565195446898672605) * 10 ^ 70 +
          0824347074760851463598323445969496851553108464595119968440291409038915)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 256,
    recurrence4A4Square.coeff x * exceptional4.coeff (255 - x)) = _
  rw [show 256 = 242 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_255_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 243,
      recurrence4A4Square.coeff x * exceptional4.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (256 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_256 :
    recurrence4ExceptionalProduct.coeff 256 =
      (
        (((1096802216587507720916494341756619276738938791 * 10 ^ 70 +
          1671265623062702446378804832778534468476125733777196293487179506673141) * 10 ^ 70 +
          1724726855279369511023595356539163595200726082448583849672475779859015)) /
        (1785787687194522429613 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 257,
    recurrence4A4Square.coeff x * exceptional4.coeff (256 - x)) = _
  rw [show 257 = 243 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_256_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 244,
      recurrence4A4Square.coeff x * exceptional4.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (257 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_257 :
    recurrence4ExceptionalProduct.coeff 257 =
      (
        -(((6987803938717431250312763381206887382276952165 * 10 ^ 70 +
          5449601012068393309652422168751627944617841562450169068510788382647716) * 10 ^ 70 +
          6160995845777950764676119713075313685767507897658721669190060388061603)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 258,
    recurrence4A4Square.coeff x * exceptional4.coeff (257 - x)) = _
  rw [show 258 = 244 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_257_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 245,
      recurrence4A4Square.coeff x * exceptional4.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (258 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_258 :
    recurrence4ExceptionalProduct.coeff 258 =
      (
        (((3254631499237933406882947885630438238236178066 * 10 ^ 70 +
          6837742938542683444662030894682858310015058246044885436319983131429684) * 10 ^ 70 +
          1292466290387451180739398954875862956928545796109845017973340496476019)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 259,
    recurrence4A4Square.coeff x * exceptional4.coeff (258 - x)) = _
  rw [show 259 = 245 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_258_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 246,
      recurrence4A4Square.coeff x * exceptional4.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (259 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_259 :
    recurrence4ExceptionalProduct.coeff 259 =
      (
        -(((1454686682988748995645904256547823125705548306 * 10 ^ 70 +
          8081341976999022583111272932857666395989092312617423920021297884727526) * 10 ^ 70 +
          8720582224423615412237708466624157512114762336345587705943359876771623)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 260,
    recurrence4A4Square.coeff x * exceptional4.coeff (259 - x)) = _
  rw [show 260 = 246 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_259_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 247,
      recurrence4A4Square.coeff x * exceptional4.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (260 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_260 :
    recurrence4ExceptionalProduct.coeff 260 =
      (
        (((627267413537242762399287446693506762184499421 * 10 ^ 70 +
          1805611242065520845949403508953056619595055163724272035662833936652174) * 10 ^ 70 +
          9899197133935918144724062190209168088061694467280682434887394875457870)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 261,
    recurrence4A4Square.coeff x * exceptional4.coeff (260 - x)) = _
  rw [show 261 = 247 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_260_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 248,
      recurrence4A4Square.coeff x * exceptional4.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (261 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_261 :
    recurrence4ExceptionalProduct.coeff 261 =
      (
        -(((261723757427155828384418495676576222200696492 * 10 ^ 70 +
          7879179598993288977651271647823006257475148789672904036638994167299211) * 10 ^ 70 +
          5506006741306503528531187762023110903921090538493642415457308106190068)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 262,
    recurrence4A4Square.coeff x * exceptional4.coeff (261 - x)) = _
  rw [show 262 = 248 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_261_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 249,
      recurrence4A4Square.coeff x * exceptional4.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (262 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_262 :
    recurrence4ExceptionalProduct.coeff 262 =
      (
        (((105836352391330268130770382041930388821376087 * 10 ^ 70 +
          6839427148675233727072117897387130906248997583313054032831575518812026) * 10 ^ 70 +
          8446041621563692094858994767532318651472790220116708854841941501887720)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 263,
    recurrence4A4Square.coeff x * exceptional4.coeff (262 - x)) = _
  rw [show 263 = 249 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_262_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 250,
      recurrence4A4Square.coeff x * exceptional4.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (263 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_263 :
    recurrence4ExceptionalProduct.coeff 263 =
      (
        -(((41508062634923178461297329643896483169119475 * 10 ^ 70 +
          0309635928427641395696384477765028939512584320394965198915663797752924) * 10 ^ 70 +
          9198500927801996231878470515073289674856460702936728341283580905517104)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 264,
    recurrence4A4Square.coeff x * exceptional4.coeff (263 - x)) = _
  rw [show 264 = 250 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_263_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 251,
      recurrence4A4Square.coeff x * exceptional4.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (264 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_264 :
    recurrence4ExceptionalProduct.coeff 264 =
      (
        (((15788570615422145146999498150583744697936864 * 10 ^ 70 +
          7767070179266999802767321293337334747690926293240499349564669823336023) * 10 ^ 70 +
          6458786613091143505259013589327911317791691607696434042134266532387006)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 265,
    recurrence4A4Square.coeff x * exceptional4.coeff (264 - x)) = _
  rw [show 265 = 251 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_264_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 252,
      recurrence4A4Square.coeff x * exceptional4.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (265 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_265 :
    recurrence4ExceptionalProduct.coeff 265 =
      (
        -(((5820810312960629851633823312388710986470729 * 10 ^ 70 +
          0164302917805493958825601384606476239707517183569357968090261049889571) * 10 ^ 70 +
          5888781627084348002012605660591991672165532240767651906180544061901570)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 266,
    recurrence4A4Square.coeff x * exceptional4.coeff (265 - x)) = _
  rw [show 266 = 252 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_265_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 253,
      recurrence4A4Square.coeff x * exceptional4.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (266 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_266 :
    recurrence4ExceptionalProduct.coeff 266 =
      (
        (((2076837633977206187424514801890942307734696 * 10 ^ 70 +
          5976325946170751071240647138717856925770721715799371142039216940421728) * 10 ^ 70 +
          2149200276134506690753439011853332545142155129650956542621329162787230)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 267,
    recurrence4A4Square.coeff x * exceptional4.coeff (266 - x)) = _
  rw [show 267 = 253 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_266_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 254,
      recurrence4A4Square.coeff x * exceptional4.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (267 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_267 :
    recurrence4ExceptionalProduct.coeff 267 =
      (
        -(((715096368339916674887799831211979201584742 * 10 ^ 70 +
          1154168823779121389341365050737572131403276714827308060045157959916206) * 10 ^ 70 +
          1519833787045512459356582803766132044034471119325848607376314128836778)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 268,
    recurrence4A4Square.coeff x * exceptional4.coeff (267 - x)) = _
  rw [show 268 = 254 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_267_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 255,
      recurrence4A4Square.coeff x * exceptional4.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (268 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_268 :
    recurrence4ExceptionalProduct.coeff 268 =
      (
        (((236361935280038210095083387616118697720217 * 10 ^ 70 +
          5578865551845252169505801005202123874229061989439707939934984447101594) * 10 ^ 70 +
          9335682765057179743487109508035292430867772335223058587537935272930496)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 269,
    recurrence4A4Square.coeff x * exceptional4.coeff (268 - x)) = _
  rw [show 269 = 255 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_268_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 256,
      recurrence4A4Square.coeff x * exceptional4.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (269 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_269 :
    recurrence4ExceptionalProduct.coeff 269 =
      (
        -(((74239441774614575455136183639417135707982 * 10 ^ 70 +
          3767018512681341312124634141017703529210721921539726433653749753381880) * 10 ^ 70 +
          2006956795611085879066059018172300857110604424133398928706456165845624)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 270,
    recurrence4A4Square.coeff x * exceptional4.coeff (269 - x)) = _
  rw [show 270 = 256 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_269_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 257,
      recurrence4A4Square.coeff x * exceptional4.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (270 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_270 :
    recurrence4ExceptionalProduct.coeff 270 =
      (
        (((21695802938023433447204865384779990578311 * 10 ^ 70 +
          2537294312738920411584474941853658783808278347311207805517773403774953) * 10 ^ 70 +
          1754748770068929569305008445201556506616119762267153222823530771315761)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 271,
    recurrence4A4Square.coeff x * exceptional4.coeff (270 - x)) = _
  rw [show 271 = 257 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_270_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 258,
      recurrence4A4Square.coeff x * exceptional4.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (271 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_271 :
    recurrence4ExceptionalProduct.coeff 271 =
      (
        -(((5607323817422790039602981807968298258443 * 10 ^ 70 +
          3923864797312524398115874317594892680149159345272898746157623799217246) * 10 ^ 70 +
          9229608249062050166450961254330210695422302445317378134878858183538827)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 272,
    recurrence4A4Square.coeff x * exceptional4.coeff (271 - x)) = _
  rw [show 272 = 258 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_271_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 259,
      recurrence4A4Square.coeff x * exceptional4.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (272 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_272 :
    recurrence4ExceptionalProduct.coeff 272 =
      (
        (((1083101272528736811762597270807635490467 * 10 ^ 70 +
          9189761321349700141838527026688580138611143695224208159645286902170239) * 10 ^ 70 +
          0895410895207063802911129164322532321262429092967159286053074699103021)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 273,
    recurrence4A4Square.coeff x * exceptional4.coeff (272 - x)) = _
  rw [show 273 = 259 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_272_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 260,
      recurrence4A4Square.coeff x * exceptional4.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (273 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_273 :
    recurrence4ExceptionalProduct.coeff 273 =
      (
        (((1231488935581655016708880521189517635 * 10 ^ 70 +
          1248773358809271876042217174247979255692445999174515325915875268589731) * 10 ^ 70 +
          0053758112299179175330215663990939415073501283210007394155365602484155)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 274,
    recurrence4A4Square.coeff x * exceptional4.coeff (273 - x)) = _
  rw [show 274 = 260 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_273_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 261,
      recurrence4A4Square.coeff x * exceptional4.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (274 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_274 :
    recurrence4ExceptionalProduct.coeff 274 =
      (
        -(((162729346709246405315957705186152936362 * 10 ^ 70 +
          0070965932418186359582639770460490035502752684342549607890095559998984) * 10 ^ 70 +
          0192915403065423750338494031443177159824799244098463243232502828166015)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 275,
    recurrence4A4Square.coeff x * exceptional4.coeff (274 - x)) = _
  rw [show 275 = 261 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_274_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 262,
      recurrence4A4Square.coeff x * exceptional4.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (275 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_275 :
    recurrence4ExceptionalProduct.coeff 275 =
      (
        (((125466944966915597743464522169080679319 * 10 ^ 70 +
          0926779800815934552862962865826414207875565252795137349005701138117206) * 10 ^ 70 +
          7521975527147660707157553328408209972438876287564055076781210247497651)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 276,
    recurrence4A4Square.coeff x * exceptional4.coeff (275 - x)) = _
  rw [show 276 = 262 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_275_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 263,
      recurrence4A4Square.coeff x * exceptional4.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (276 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_276 :
    recurrence4ExceptionalProduct.coeff 276 =
      (
        -(((72419212855997315154362751698956385241 * 10 ^ 70 +
          5601206327450684088447963317757723299079219102335062223350065151822830) * 10 ^ 70 +
          2440689637377020793650756307147835905267863512420201781490394801390101)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 277,
    recurrence4A4Square.coeff x * exceptional4.coeff (276 - x)) = _
  rw [show 277 = 263 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_276_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 264,
      recurrence4A4Square.coeff x * exceptional4.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (277 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_277 :
    recurrence4ExceptionalProduct.coeff 277 =
      (
        (((36946292755724964781756913502053739598 * 10 ^ 70 +
          8118792002365616868419727405232150568026886558631531137965441115517677) * 10 ^ 70 +
          5788631428605859025419636982255603853069418039695986643336528039249933)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 278,
    recurrence4A4Square.coeff x * exceptional4.coeff (277 - x)) = _
  rw [show 278 = 264 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_277_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 265,
      recurrence4A4Square.coeff x * exceptional4.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (278 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_278 :
    recurrence4ExceptionalProduct.coeff 278 =
      (
        -(((17498749150770075574599916255218098431 * 10 ^ 70 +
          8311856205785114568156067792697757694117627544029071682159093785258681) * 10 ^ 70 +
          2146003335316017845904481434715800829796601779668150840126450436924495)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 279,
    recurrence4A4Square.coeff x * exceptional4.coeff (278 - x)) = _
  rw [show 279 = 265 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_278_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 266,
      recurrence4A4Square.coeff x * exceptional4.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (279 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_279 :
    recurrence4ExceptionalProduct.coeff 279 =
      (
        (((7842129244443953356714847039053311663 * 10 ^ 70 +
          2947733325436082252729309770984490428658948625819265813321812919247694) * 10 ^ 70 +
          5959100377203946573358906623853835619201120595925800359780736818169025)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 280,
    recurrence4A4Square.coeff x * exceptional4.coeff (279 - x)) = _
  rw [show 280 = 266 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_279_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 267,
      recurrence4A4Square.coeff x * exceptional4.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (280 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_280 :
    recurrence4ExceptionalProduct.coeff 280 =
      (
        -(((3350835160125798883189501950186544303 * 10 ^ 70 +
          2338113072562915011769625727429321586444222822848046604943122917439404) * 10 ^ 70 +
          2060498165573385704249358643407881996507288586361945021400680361497888)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 281,
    recurrence4A4Square.coeff x * exceptional4.coeff (280 - x)) = _
  rw [show 281 = 267 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_280_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 268,
      recurrence4A4Square.coeff x * exceptional4.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (281 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_281 :
    recurrence4ExceptionalProduct.coeff 281 =
      (
        (((1368104264677417917623721681143129471 * 10 ^ 70 +
          8577349012484626109248227552281700516041923091116618213382114812288437) * 10 ^ 70 +
          5706859257980358180388604266325780014425225359933714874478620489391198)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 282,
    recurrence4A4Square.coeff x * exceptional4.coeff (281 - x)) = _
  rw [show 282 = 268 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_281_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 269,
      recurrence4A4Square.coeff x * exceptional4.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (282 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_282 :
    recurrence4ExceptionalProduct.coeff 282 =
      (
        -(((41021706851070547027141829558398460 * 10 ^ 70 +
          5522122337715404975238367690977930381479450097396547955340688806692945) * 10 ^ 70 +
          3884470086379322248483002170523577964647118461349055004735554849436117)) /
        (1785787687194522429613 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 283,
    recurrence4A4Square.coeff x * exceptional4.coeff (282 - x)) = _
  rw [show 283 = 269 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_282_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 270,
      recurrence4A4Square.coeff x * exceptional4.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (283 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_283 :
    recurrence4ExceptionalProduct.coeff 283 =
      (
        (((197846711342152412092064381842334094 * 10 ^ 70 +
          0474942832220963389029047093077689610590501819492268243883897397415747) * 10 ^ 70 +
          3749942376264673992753351509348198484054492243425918782502820742123405)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 284,
    recurrence4A4Square.coeff x * exceptional4.coeff (283 - x)) = _
  rw [show 284 = 270 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_283_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 271,
      recurrence4A4Square.coeff x * exceptional4.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (284 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_284 :
    recurrence4ExceptionalProduct.coeff 284 =
      (
        -(((69491268349321913430987278509421375 * 10 ^ 70 +
          6172589782610656973104034936909129589087775386993910855118726706516915) * 10 ^ 70 +
          9970672232804861311148633749540149619305325364279128094195433568086281)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 285,
    recurrence4A4Square.coeff x * exceptional4.coeff (284 - x)) = _
  rw [show 285 = 271 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_284_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 272,
      recurrence4A4Square.coeff x * exceptional4.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (285 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_285 :
    recurrence4ExceptionalProduct.coeff 285 =
      (
        (((22915327555697547264272909486730080 * 10 ^ 70 +
          3954544937131242905374963383859500798280112513643658333173786120887709) * 10 ^ 70 +
          0064314661526193296328509467429625306000858625525850188140088621607131)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 286,
    recurrence4A4Square.coeff x * exceptional4.coeff (285 - x)) = _
  rw [show 286 = 272 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_285_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 273,
      recurrence4A4Square.coeff x * exceptional4.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (286 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_286 :
    recurrence4ExceptionalProduct.coeff 286 =
      (
        -(((6997923753761138756139812501938724 * 10 ^ 70 +
          6229676249615510268365563722994162523785332194190735251935362041022516) * 10 ^ 70 +
          9095193867801276002251505229444878494989323676276682916752516117039928)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 287,
    recurrence4A4Square.coeff x * exceptional4.coeff (286 - x)) = _
  rw [show 287 = 273 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_286_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 274,
      recurrence4A4Square.coeff x * exceptional4.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (287 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_287 :
    recurrence4ExceptionalProduct.coeff 287 =
      (
        (((1930491786435161931043571687560141 * 10 ^ 70 +
          8739521579668689633438746127733027572274470766851739862682238656416837) * 10 ^ 70 +
          3244809387517438449382853981482711453863074260914257420344609225175380)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 288,
    recurrence4A4Square.coeff x * exceptional4.coeff (287 - x)) = _
  rw [show 288 = 274 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_287_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 275,
      recurrence4A4Square.coeff x * exceptional4.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (288 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_288 :
    recurrence4ExceptionalProduct.coeff 288 =
      (
        -(((455743324029423693767685657492390 * 10 ^ 70 +
          5388480616974268559127492123680607034330277606358935432482238803146316) * 10 ^ 70 +
          3925558907837532328069788876582506609703815890518273396107190289713106)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 289,
    recurrence4A4Square.coeff x * exceptional4.coeff (288 - x)) = _
  rw [show 289 = 275 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_288_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 276,
      recurrence4A4Square.coeff x * exceptional4.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (289 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_289 :
    recurrence4ExceptionalProduct.coeff 289 =
      (
        (((77829748297836465169531623815428 * 10 ^ 70 +
          2475451328255497213368980023071940091587526136219264472620142143446596) * 10 ^ 70 +
          8336575409629335646086372400813578218039443218210084271201147813939304)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 290,
    recurrence4A4Square.coeff x * exceptional4.coeff (289 - x)) = _
  rw [show 290 = 276 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_289_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 277,
      recurrence4A4Square.coeff x * exceptional4.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (290 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_290 :
    recurrence4ExceptionalProduct.coeff 290 =
      (
        -(((382882784779454811685254646388 * 10 ^ 70 +
          3534473013475035079867567392138403738484668899126805590487298758469770) * 10 ^ 70 +
          4876166994458601106263886962351250963521436540005512659767469322345408)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 291,
    recurrence4A4Square.coeff x * exceptional4.coeff (290 - x)) = _
  rw [show 291 = 277 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_290_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 278,
      recurrence4A4Square.coeff x * exceptional4.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (291 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_291 :
    recurrence4ExceptionalProduct.coeff 291 =
      (
        -(((7588089652248237731889856988152 * 10 ^ 70 +
          9634614515938534774558920265308171779455359575866099678019938801614684) * 10 ^ 70 +
          3000589785455013787712953553826268345079776703377562906871642396128104)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 292,
    recurrence4A4Square.coeff x * exceptional4.coeff (291 - x)) = _
  rw [show 292 = 278 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_291_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 279,
      recurrence4A4Square.coeff x * exceptional4.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (292 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_292 :
    recurrence4ExceptionalProduct.coeff 292 =
      (
        (((4507035680260892206739484086940 * 10 ^ 70 +
          0877557799964430115969010430125297203408785296124287280191226671200191) * 10 ^ 70 +
          0273874438603452704188329687352564277594154647315334872862912827552623)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 293,
    recurrence4A4Square.coeff x * exceptional4.coeff (292 - x)) = _
  rw [show 293 = 279 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_292_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 280,
      recurrence4A4Square.coeff x * exceptional4.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (293 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_293 :
    recurrence4ExceptionalProduct.coeff 293 =
      (
        -(((1890366265648889352745125796491 * 10 ^ 70 +
          8361411606837458149897813596307819294581938047323509299174096027205591) * 10 ^ 70 +
          1050167076660339086226213435647669288928703883072500100225237326388993)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 294,
    recurrence4A4Square.coeff x * exceptional4.coeff (293 - x)) = _
  rw [show 294 = 280 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_293_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 281,
      recurrence4A4Square.coeff x * exceptional4.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (294 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_294 :
    recurrence4ExceptionalProduct.coeff 294 =
      (
        (((661528848219512604827609191042 * 10 ^ 70 +
          5315380521135969676784060515438239120841427274996927726227044057757001) * 10 ^ 70 +
          4934367163814527768309607684576898454093533169469635332339851790465766)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 295,
    recurrence4A4Square.coeff x * exceptional4.coeff (294 - x)) = _
  rw [show 295 = 281 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_294_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 282,
      recurrence4A4Square.coeff x * exceptional4.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (295 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_295 :
    recurrence4ExceptionalProduct.coeff 295 =
      (
        -(((201727108733077883199000020291 * 10 ^ 70 +
          3271845030727420835086152742040142682443238541818233559261443092082076) * 10 ^ 70 +
          2479000044475393865719324620375106190955459558701520067818132789524072)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 296,
    recurrence4A4Square.coeff x * exceptional4.coeff (295 - x)) = _
  rw [show 296 = 282 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_295_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 283,
      recurrence4A4Square.coeff x * exceptional4.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (296 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_296 :
    recurrence4ExceptionalProduct.coeff 296 =
      (
        (((53941908353672256769273705648 * 10 ^ 70 +
          1910019012984160257378370914936754701531371954646563062020218676018965) * 10 ^ 70 +
          0019450998581265904978738672680747158431614619750240734657049122565655)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 297,
    recurrence4A4Square.coeff x * exceptional4.coeff (296 - x)) = _
  rw [show 297 = 283 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_296_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 284,
      recurrence4A4Square.coeff x * exceptional4.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (297 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_297 :
    recurrence4ExceptionalProduct.coeff 297 =
      (
        -(((12381332096689462437759754853 * 10 ^ 70 +
          7852128451710224263471248746550271144259664405344944635463360116480046) * 10 ^ 70 +
          1298101995268241015210163098198030470552613685256338959808829890934985)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 298,
    recurrence4A4Square.coeff x * exceptional4.coeff (297 - x)) = _
  rw [show 298 = 284 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_297_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 285,
      recurrence4A4Square.coeff x * exceptional4.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (298 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_298 :
    recurrence4ExceptionalProduct.coeff 298 =
      (
        (((173902986439005075596718649 * 10 ^ 70 +
          9567488951394783057563154964129673853638009817810838013543839175075064) * 10 ^ 70 +
          3227699621036754319758720700683837053038307196575024564687237485892054)) /
        (1785787687194522429613 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 299,
    recurrence4A4Square.coeff x * exceptional4.coeff (298 - x)) = _
  rw [show 299 = 285 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_298_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 286,
      recurrence4A4Square.coeff x * exceptional4.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (299 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_299 :
    recurrence4ExceptionalProduct.coeff 299 =
      (
        -(((231820094567629903499925519 * 10 ^ 70 +
          4452508325506491211015511957911771734004874068161628118175329277336382) * 10 ^ 70 +
          2414510076932949457572801062352401918384075437234577970559948007738890)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 300,
    recurrence4A4Square.coeff x * exceptional4.coeff (299 - x)) = _
  rw [show 300 = 286 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_299_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 287,
      recurrence4A4Square.coeff x * exceptional4.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (300 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_300 :
    recurrence4ExceptionalProduct.coeff 300 =
      (
        -(((44692291894338848856140465 * 10 ^ 70 +
          6081741315749681471889299734820360614779493983295583440310079538022110) * 10 ^ 70 +
          3249156159766273020927369453579031019472126464181072744330736885173792)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 301,
    recurrence4A4Square.coeff x * exceptional4.coeff (300 - x)) = _
  rw [show 301 = 287 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_300_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 288,
      recurrence4A4Square.coeff x * exceptional4.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (301 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_301 :
    recurrence4ExceptionalProduct.coeff 301 =
      (
        (((2860866287614143091824759 * 10 ^ 70 +
          2140714631129887134210542094504499464187011735210107849552011654818631) * 10 ^ 70 +
          4259028235816749191318110397981492773549305877718619558797419279980110)) /
        (1785787687194522429613 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 302,
    recurrence4A4Square.coeff x * exceptional4.coeff (301 - x)) = _
  rw [show 302 = 288 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_301_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 289,
      recurrence4A4Square.coeff x * exceptional4.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (302 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_302 :
    recurrence4ExceptionalProduct.coeff 302 =
      (
        -(((14674192677679128239564136 * 10 ^ 70 +
          3994964328728338827303078455970874378725386942404853364871510476458119) * 10 ^ 70 +
          5271886444401185113139489571148300770451993202400273569357522190888522)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 303,
    recurrence4A4Square.coeff x * exceptional4.coeff (302 - x)) = _
  rw [show 303 = 289 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_302_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 290,
      recurrence4A4Square.coeff x * exceptional4.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (303 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_303 :
    recurrence4ExceptionalProduct.coeff 303 =
      (
        (((4485290976500026004002884 * 10 ^ 70 +
          0446747731618487387452850510315851438902995295282223310261129855299965) * 10 ^ 70 +
          0903973544800245264596074999930074262194509384208554570527530948821792)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 304,
    recurrence4A4Square.coeff x * exceptional4.coeff (303 - x)) = _
  rw [show 304 = 290 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_303_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 291,
      recurrence4A4Square.coeff x * exceptional4.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (304 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_304 :
    recurrence4ExceptionalProduct.coeff 304 =
      (
        -(((1164454545917582261032784 * 10 ^ 70 +
          3813709689581512434273012797044486748725800289798748408526810500350952) * 10 ^ 70 +
          2173872249528823005218469764025086012833691354020788988060565681415828)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 305,
    recurrence4A4Square.coeff x * exceptional4.coeff (304 - x)) = _
  rw [show 305 = 291 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_304_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 292,
      recurrence4A4Square.coeff x * exceptional4.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (305 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_305 :
    recurrence4ExceptionalProduct.coeff 305 =
      (
        (((264155673700477749120032 * 10 ^ 70 +
          8273633836001124637341165827643878417451601742429526570598291410954574) * 10 ^ 70 +
          4402601541322460100130850773826853745699141821422272535374743385389272)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 306,
    recurrence4A4Square.coeff x * exceptional4.coeff (305 - x)) = _
  rw [show 306 = 292 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_305_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 293,
      recurrence4A4Square.coeff x * exceptional4.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (306 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_306 :
    recurrence4ExceptionalProduct.coeff 306 =
      (
        -(((52597198194667476151104 * 10 ^ 70 +
          4133269092746034143664542767412186890226091459744025379390047221070813) * 10 ^ 70 +
          9446189743769658154643454187780347502587563554604530837493182725191506)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 307,
    recurrence4A4Square.coeff x * exceptional4.coeff (306 - x)) = _
  rw [show 307 = 293 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_306_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 294,
      recurrence4A4Square.coeff x * exceptional4.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (307 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_307 :
    recurrence4ExceptionalProduct.coeff 307 =
      (
        (((9071847955590431087550 * 10 ^ 70 +
          4067745345967109956830645448758007994437646182440284604032850783572302) * 10 ^ 70 +
          9042044616705100966580660902377489323135972804967488129388514642424338)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 308,
    recurrence4A4Square.coeff x * exceptional4.coeff (307 - x)) = _
  rw [show 308 = 294 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_307_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 295,
      recurrence4A4Square.coeff x * exceptional4.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (308 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_308 :
    recurrence4ExceptionalProduct.coeff 308 =
      (
        -(((1300594535596114442714 * 10 ^ 70 +
          8322423963930294036985687340791121475354461472540519838325557852171713) * 10 ^ 70 +
          1483255914339046964078434280094233167474731312589566776288556881886435)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 309,
    recurrence4A4Square.coeff x * exceptional4.coeff (308 - x)) = _
  rw [show 309 = 295 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_308_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 296,
      recurrence4A4Square.coeff x * exceptional4.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (309 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_309 :
    recurrence4ExceptionalProduct.coeff 309 =
      (
        (((136482391915301288655 * 10 ^ 70 +
          2171519659827388444518882475322014178362094447582311827608752470910246) * 10 ^ 70 +
          1064139682533399965422012030535448664742278070598563053150718513763273)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 310,
    recurrence4A4Square.coeff x * exceptional4.coeff (309 - x)) = _
  rw [show 310 = 296 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_309_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 297,
      recurrence4A4Square.coeff x * exceptional4.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (310 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_310 :
    recurrence4ExceptionalProduct.coeff 310 =
      (
        -(((4192711377269820548 * 10 ^ 70 +
          6557676771463800735030325249500245620686562022853436956992514093603067) * 10 ^ 70 +
          1040418553467650196163854695104922943790298964558912375393408462234152)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 311,
    recurrence4A4Square.coeff x * exceptional4.coeff (310 - x)) = _
  rw [show 311 = 297 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_310_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 298,
      recurrence4A4Square.coeff x * exceptional4.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (311 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_311 :
    recurrence4ExceptionalProduct.coeff 311 =
      (
        -(((2493880676629240384 * 10 ^ 70 +
          2497411872166879357672478345887369397423387221879290919179031999159877) * 10 ^ 70 +
          3955632103375839096304564381794391260782626678638396208093531359690608)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 312,
    recurrence4A4Square.coeff x * exceptional4.coeff (311 - x)) = _
  rw [show 312 = 298 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_311_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 299,
      recurrence4A4Square.coeff x * exceptional4.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (312 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_312 :
    recurrence4ExceptionalProduct.coeff 312 =
      (
        (((816199469909118258 * 10 ^ 70 +
          3185091975538752987616343534533319515216593504827853607403864254087429) * 10 ^ 70 +
          9242384219023983007772649339362713462602637510580083584899084269776521)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 313,
    recurrence4A4Square.coeff x * exceptional4.coeff (312 - x)) = _
  rw [show 313 = 299 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_312_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 300,
      recurrence4A4Square.coeff x * exceptional4.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (313 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_313 :
    recurrence4ExceptionalProduct.coeff 313 =
      (
        -(((162402369364696201 * 10 ^ 70 +
          5492612789843376235351748169928067328215428807603533430043118643462540) * 10 ^ 70 +
          5681901329392371748335477503946017508967810466679534332536931159528657)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 314,
    recurrence4A4Square.coeff x * exceptional4.coeff (313 - x)) = _
  rw [show 314 = 300 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_313_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 301,
      recurrence4A4Square.coeff x * exceptional4.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (314 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_314 :
    recurrence4ExceptionalProduct.coeff 314 =
      (
        (((24040550477974307 * 10 ^ 70 +
          0326390436032853165483110742424095877072908425374236418852517620665867) * 10 ^ 70 +
          1559171516679306535070086200888869817135918917379684522801284481594601)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 315,
    recurrence4A4Square.coeff x * exceptional4.coeff (314 - x)) = _
  rw [show 315 = 301 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_314_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 302,
      recurrence4A4Square.coeff x * exceptional4.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (315 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_315 :
    recurrence4ExceptionalProduct.coeff 315 =
      (
        -(((2598847661200229 * 10 ^ 70 +
          1337366990834631960737605944713244030390018151730530765810164160973541) * 10 ^ 70 +
          6964695756995715927990736282703421414398031405776962014165066219406477)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 316,
    recurrence4A4Square.coeff x * exceptional4.coeff (315 - x)) = _
  rw [show 316 = 302 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_315_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 303,
      recurrence4A4Square.coeff x * exceptional4.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (316 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_316 :
    recurrence4ExceptionalProduct.coeff 316 =
      (
        (((151087016429282 * 10 ^ 70 +
          8371279877783150241948371795198514800831184703866135410345946217979292) * 10 ^ 70 +
          4363057656717083991381184617464449840946226530778158206195264299519451)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 317,
    recurrence4A4Square.coeff x * exceptional4.coeff (316 - x)) = _
  rw [show 317 = 303 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_316_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 304,
      recurrence4A4Square.coeff x * exceptional4.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (317 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_317 :
    recurrence4ExceptionalProduct.coeff 317 =
      (
        (((12705243274363 * 10 ^ 70 +
          7213670106579995489195058586068349944285910579318963781373010869080761) * 10 ^ 70 +
          8181723208348217469192594126078387405098376749364208401787164823387411)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 318,
    recurrence4A4Square.coeff x * exceptional4.coeff (317 - x)) = _
  rw [show 318 = 304 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_317_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 305,
      recurrence4A4Square.coeff x * exceptional4.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (318 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_318 :
    recurrence4ExceptionalProduct.coeff 318 =
      (
        -(((5305791620469 * 10 ^ 70 +
          2079862676720835416409376219987828441866859227116327819932280348315290) * 10 ^ 70 +
          5682755391225293865724661842331786175731978512137109694323214916760223)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 319,
    recurrence4A4Square.coeff x * exceptional4.coeff (318 - x)) = _
  rw [show 319 = 305 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_318_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 306,
      recurrence4A4Square.coeff x * exceptional4.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (319 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_319 :
    recurrence4ExceptionalProduct.coeff 319 =
      (
        (((902823501243 * 10 ^ 70 +
          9562895680835705136983126181072684753697387885154213248371980050594556) * 10 ^ 70 +
          9936000984369675833832269141586257732866898875574100617891244118591775)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 320,
    recurrence4A4Square.coeff x * exceptional4.coeff (319 - x)) = _
  rw [show 320 = 306 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_319_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 307,
      recurrence4A4Square.coeff x * exceptional4.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (320 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_320 :
    recurrence4ExceptionalProduct.coeff 320 =
      (
        -(((102401984983 * 10 ^ 70 +
          6499483282201645755651707554408552464936251160365689226273893462446363) * 10 ^ 70 +
          2206213499934507283436559450479099854447179943808549203555213469813176)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 321,
    recurrence4A4Square.coeff x * exceptional4.coeff (320 - x)) = _
  rw [show 321 = 307 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_320_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 308,
      recurrence4A4Square.coeff x * exceptional4.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (321 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_321 :
    recurrence4ExceptionalProduct.coeff 321 =
      (
        (((7440999220 * 10 ^ 70 +
          9678489660510904623657837263171654196500893321660589788854583637349747) * 10 ^ 70 +
          1242325532826200314725017765955841881118096028292390777687832028176362)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 322,
    recurrence4A4Square.coeff x * exceptional4.coeff (321 - x)) = _
  rw [show 322 = 308 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_321_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 309,
      recurrence4A4Square.coeff x * exceptional4.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (322 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_322 :
    recurrence4ExceptionalProduct.coeff 322 =
      (
        -(((123423553 * 10 ^ 70 +
          1697010248510206018946033555176429945165291959889418529002163734105178) * 10 ^ 70 +
          5392687289441658443770789755811042315948175955784782204867595652210252)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 323,
    recurrence4A4Square.coeff x * exceptional4.coeff (322 - x)) = _
  rw [show 323 = 309 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_322_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 310,
      recurrence4A4Square.coeff x * exceptional4.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (323 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_323 :
    recurrence4ExceptionalProduct.coeff 323 =
      (
        -(((54464979 * 10 ^ 70 +
          0750349072241738717363335798198427558616144913851443947014338997958613) * 10 ^ 70 +
          0224898762615133720089706989097992755090380986268584131619177974469036)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 324,
    recurrence4A4Square.coeff x * exceptional4.coeff (323 - x)) = _
  rw [show 324 = 310 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_323_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 311,
      recurrence4A4Square.coeff x * exceptional4.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (324 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_324 :
    recurrence4ExceptionalProduct.coeff 324 =
      (
        (((8969934 * 10 ^ 70 +
          9444014785440220484132682075676228960235641551877137131373806545799689) * 10 ^ 70 +
          3248411459251673388035205515949519886270856580019767453780357090233149)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 325,
    recurrence4A4Square.coeff x * exceptional4.coeff (324 - x)) = _
  rw [show 325 = 311 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_324_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 312,
      recurrence4A4Square.coeff x * exceptional4.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (325 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_325 :
    recurrence4ExceptionalProduct.coeff 325 =
      (
        -(((758249 * 10 ^ 70 +
          2476353429158907726749065682550169229304699527851685193294767136524436) * 10 ^ 70 +
          1166090924958647046564331591651686093741060255769188558280616782008461)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 326,
    recurrence4A4Square.coeff x * exceptional4.coeff (325 - x)) = _
  rw [show 326 = 312 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_325_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 313,
      recurrence4A4Square.coeff x * exceptional4.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (326 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_326 :
    recurrence4ExceptionalProduct.coeff 326 =
      (
        (((27974 * 10 ^ 70 +
          7314855296190445315519623906677203991987608402181083064323445624573736) * 10 ^ 70 +
          7533537242221479646211581380888247289063696496717155928387678238700453)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 327,
    recurrence4A4Square.coeff x * exceptional4.coeff (326 - x)) = _
  rw [show 327 = 313 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_326_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 314,
      recurrence4A4Square.coeff x * exceptional4.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (327 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_327 :
    recurrence4ExceptionalProduct.coeff 327 =
      (
        (((1826 * 10 ^ 70 +
          1792830057825722012770119566369939497678078269923222909950625838813394) * 10 ^ 70 +
          6055075825184865601580828974287156626319770712815705622235837549050579)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 328,
    recurrence4A4Square.coeff x * exceptional4.coeff (327 - x)) = _
  rw [show 328 = 314 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_327_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 315,
      recurrence4A4Square.coeff x * exceptional4.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (328 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_328 :
    recurrence4ExceptionalProduct.coeff 328 =
      (
        -(((356 * 10 ^ 70 +
          3098171552660061039963813219577718204093103800601589546428636177314807) * 10 ^ 70 +
          9239515960687600828218737874529312817584197546908962725083708461965354)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 329,
    recurrence4A4Square.coeff x * exceptional4.coeff (328 - x)) = _
  rw [show 329 = 315 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_328_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 316,
      recurrence4A4Square.coeff x * exceptional4.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (329 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_329 :
    recurrence4ExceptionalProduct.coeff 329 =
      (
        (((24 * 10 ^ 70 +
          1705446657698240295867832227881393298301318333678677010652610579043507) * 10 ^ 70 +
          9055972040886518701433497430932734057472575575312882908011196431894928)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 330,
    recurrence4A4Square.coeff x * exceptional4.coeff (329 - x)) = _
  rw [show 330 = 316 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_329_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 317,
      recurrence4A4Square.coeff x * exceptional4.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (330 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_330 :
    recurrence4ExceptionalProduct.coeff 330 =
      (
        -((4045409487042539365662762655891560062370498946856553387985011204549543 * 10 ^ 70 +
          2447406570751648463795644725028615925737864019862287682957322699452589)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 331,
    recurrence4A4Square.coeff x * exceptional4.coeff (330 - x)) = _
  rw [show 331 = 317 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_330_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 318,
      recurrence4A4Square.coeff x * exceptional4.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (331 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_331 :
    recurrence4ExceptionalProduct.coeff 331 =
      (
        -((678545163019267294047609311548680653215643689396263642279199555135833 * 10 ^ 70 +
          9983099576087378552549648403857251449720727553213931421841210832746173)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 332,
    recurrence4A4Square.coeff x * exceptional4.coeff (331 - x)) = _
  rw [show 332 = 318 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_331_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 319,
      recurrence4A4Square.coeff x * exceptional4.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (332 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_332 :
    recurrence4ExceptionalProduct.coeff 332 =
      (
        ((59138388352650006526952605699652045651356858665160765731716232572338 * 10 ^ 70 +
          2484534136849150461522553399004027382252333182372848036887788757605816)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 333,
    recurrence4A4Square.coeff x * exceptional4.coeff (332 - x)) = _
  rw [show 333 = 319 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_332_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 320,
      recurrence4A4Square.coeff x * exceptional4.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (333 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_333 :
    recurrence4ExceptionalProduct.coeff 333 =
      (
        -((1235738173013932260405478532855007224274060726933460540892401358854 * 10 ^ 70 +
          6621844641921827400395896904879538231663187514688429525097399290269386)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 334,
    recurrence4A4Square.coeff x * exceptional4.coeff (333 - x)) = _
  rw [show 334 = 320 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_333_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 321,
      recurrence4A4Square.coeff x * exceptional4.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (334 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_334 :
    recurrence4ExceptionalProduct.coeff 334 =
      (
        -((102475862449916617940607564541762019997197075033722280493777165234 * 10 ^ 70 +
          9947529474010204488912701639263604450312738324321854383433222942168463)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 335,
    recurrence4A4Square.coeff x * exceptional4.coeff (334 - x)) = _
  rw [show 335 = 321 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_334_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 322,
      recurrence4A4Square.coeff x * exceptional4.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (335 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_335 :
    recurrence4ExceptionalProduct.coeff 335 =
      (
        ((7023551497187639312705219817011689230901848947754074108129620218 * 10 ^ 70 +
          3647170294028669892283257549892279950632047495553736490006260058024373)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 336,
    recurrence4A4Square.coeff x * exceptional4.coeff (335 - x)) = _
  rw [show 336 = 322 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_335_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 323,
      recurrence4A4Square.coeff x * exceptional4.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (336 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_336 :
    recurrence4ExceptionalProduct.coeff 336 =
      (
        -((11144641333523938307951797646658801365297877615931631810295383 * 10 ^ 70 +
          7540058545696402386144922025571281146580742800389646486468100137644617)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 337,
    recurrence4A4Square.coeff x * exceptional4.coeff (336 - x)) = _
  rw [show 337 = 323 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_336_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 324,
      recurrence4A4Square.coeff x * exceptional4.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (337 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_337 :
    recurrence4ExceptionalProduct.coeff 337 =
      (
        -((12147242991376545362738335946837849930561002111559030133300067 * 10 ^ 70 +
          6879804251706536065699733549604872742373991868730969163758390501838643)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 338,
    recurrence4A4Square.coeff x * exceptional4.coeff (337 - x)) = _
  rw [show 338 = 324 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_337_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 325,
      recurrence4A4Square.coeff x * exceptional4.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (338 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_338 :
    recurrence4ExceptionalProduct.coeff 338 =
      (
        ((207387065673429225914951535571491978618906878513190523134759 * 10 ^ 70 +
          7342635332684190475123526983395710442028213696733985975071155854939409)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 339,
    recurrence4A4Square.coeff x * exceptional4.coeff (338 - x)) = _
  rw [show 339 = 325 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_338_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 326,
      recurrence4A4Square.coeff x * exceptional4.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (339 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_339 :
    recurrence4ExceptionalProduct.coeff 339 =
      (
        ((14016039202355344247617025225479641812200283303692057990697 * 10 ^ 70 +
          1041617037393355071096788394043671251785385203909940942490164792882315)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 340,
    recurrence4A4Square.coeff x * exceptional4.coeff (339 - x)) = _
  rw [show 340 = 326 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_339_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 327,
      recurrence4A4Square.coeff x * exceptional4.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (340 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_340 :
    recurrence4ExceptionalProduct.coeff 340 =
      (
        -((240523470145893701833403862365697556418563547198698414726 * 10 ^ 70 +
          8113604915795637563874486938114876335032403196960696150373827436348902)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 341,
    recurrence4A4Square.coeff x * exceptional4.coeff (340 - x)) = _
  rw [show 341 = 327 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_340_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 328,
      recurrence4A4Square.coeff x * exceptional4.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (341 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_341 :
    recurrence4ExceptionalProduct.coeff 341 =
      (
        -((14511698153612793395897361799650561710458029775776074052 * 10 ^ 70 +
          6802682579884205006961691461027681883017713694980584079670564732621994)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 342,
    recurrence4A4Square.coeff x * exceptional4.coeff (341 - x)) = _
  rw [show 342 = 328 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_341_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 329,
      recurrence4A4Square.coeff x * exceptional4.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (342 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_342 :
    recurrence4ExceptionalProduct.coeff 342 =
      (
        ((2703140668386333977944702603497853729050887420816070 * 10 ^ 70 +
          4863512434676561772100990561220178192946226295019424046970396514237398)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 343,
    recurrence4A4Square.coeff x * exceptional4.coeff (342 - x)) = _
  rw [show 343 = 329 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_342_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 330,
      recurrence4A4Square.coeff x * exceptional4.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (343 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_343 :
    recurrence4ExceptionalProduct.coeff 343 =
      (
        ((9618633377299758380214482654033111199915046092098360 * 10 ^ 70 +
          2661462636115492558431165746610445445909084899401637080012860157219332)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 344,
    recurrence4A4Square.coeff x * exceptional4.coeff (343 - x)) = _
  rw [show 344 = 330 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_343_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 331,
      recurrence4A4Square.coeff x * exceptional4.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (344 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_344 :
    recurrence4ExceptionalProduct.coeff 344 =
      (
        ((242562299227934852608725118711470301734879122574540 * 10 ^ 70 +
          4960124379885997650350200061664557564401075215728055056497962691705799)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 345,
    recurrence4A4Square.coeff x * exceptional4.coeff (344 - x)) = _
  rw [show 345 = 331 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_344_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 332,
      recurrence4A4Square.coeff x * exceptional4.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (345 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_345 :
    recurrence4ExceptionalProduct.coeff 345 =
      (
        ((3178635942296279089575538291930584070948731265941 * 10 ^ 70 +
          6093613488105893597557496267102846016255863246577662020447346743181913)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 346,
    recurrence4A4Square.coeff x * exceptional4.coeff (345 - x)) = _
  rw [show 346 = 332 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_345_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 333,
      recurrence4A4Square.coeff x * exceptional4.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (346 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_346 :
    recurrence4ExceptionalProduct.coeff 346 =
      (
        ((26082386447021662966742795223324378780348508096 * 10 ^ 70 +
          2544916205016814318227808585228386290740464894219195617645823068938619)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 347,
    recurrence4A4Square.coeff x * exceptional4.coeff (346 - x)) = _
  rw [show 347 = 333 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_346_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 334,
      recurrence4A4Square.coeff x * exceptional4.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (347 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_347 :
    recurrence4ExceptionalProduct.coeff 347 =
      (
        ((139771649371163815329780447147038045140119581 * 10 ^ 70 +
          1855498749405076830008217228704323324364847286596433820108861392158725)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 348,
    recurrence4A4Square.coeff x * exceptional4.coeff (347 - x)) = _
  rw [show 348 = 334 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_347_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 335,
      recurrence4A4Square.coeff x * exceptional4.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (348 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_348 :
    recurrence4ExceptionalProduct.coeff 348 =
      (
        ((36340475338671621827127463079330542861748 * 10 ^ 70 +
          7804518064094593899470828316653671209479473349804597232430925048521340)) /
        (1785787687194522429613 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 349,
    recurrence4A4Square.coeff x * exceptional4.coeff (348 - x)) = _
  rw [show 349 = 335 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_348_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 336,
      recurrence4A4Square.coeff x * exceptional4.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (349 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_349 :
    recurrence4ExceptionalProduct.coeff 349 =
      (
        ((809121908777517545538873822146218224604 * 10 ^ 70 +
          0487818103133649954768884643376873879583248262172084120077860940143828)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 350,
    recurrence4A4Square.coeff x * exceptional4.coeff (349 - x)) = _
  rw [show 350 = 336 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_349_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 337,
      recurrence4A4Square.coeff x * exceptional4.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (350 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_350 :
    recurrence4ExceptionalProduct.coeff 350 =
      (
        -((501515607410007070836942572358536025 * 10 ^ 70 +
          6845404740988331202583086005342293385758710827016337537892838070081774)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 351,
    recurrence4A4Square.coeff x * exceptional4.coeff (350 - x)) = _
  rw [show 351 = 337 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_350_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 338,
      recurrence4A4Square.coeff x * exceptional4.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (351 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_351 :
    recurrence4ExceptionalProduct.coeff 351 =
      (
        -((6143253772144016114045435461139341 * 10 ^ 70 +
          0384746796461986970879412918602342095986191152443556606609798078017012)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 352,
    recurrence4A4Square.coeff x * exceptional4.coeff (351 - x)) = _
  rw [show 352 = 338 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_351_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 339,
      recurrence4A4Square.coeff x * exceptional4.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (352 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_352 :
    recurrence4ExceptionalProduct.coeff 352 =
      (
        -((13571499325701123685664816927600 * 10 ^ 70 +
          9509797971068411647404258674525297588967744723882977851748421247007976)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 353,
    recurrence4A4Square.coeff x * exceptional4.coeff (352 - x)) = _
  rw [show 353 = 339 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_352_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 340,
      recurrence4A4Square.coeff x * exceptional4.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (353 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_353 :
    recurrence4ExceptionalProduct.coeff 353 =
      (
        -((9385368228832451656800454447 * 10 ^ 70 +
          5895679715695998238794545857810958687798735523928553275922739014792544)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 354,
    recurrence4A4Square.coeff x * exceptional4.coeff (353 - x)) = _
  rw [show 354 = 340 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_353_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 341,
      recurrence4A4Square.coeff x * exceptional4.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (354 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_354 :
    recurrence4ExceptionalProduct.coeff 354 =
      (
        ((15605784080542096358892968 * 10 ^ 70 +
          6919566361561289662065792144363968706028859687337005424428871683276432)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 355,
    recurrence4A4Square.coeff x * exceptional4.coeff (354 - x)) = _
  rw [show 355 = 341 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_354_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 342,
      recurrence4A4Square.coeff x * exceptional4.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (355 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_355 :
    recurrence4ExceptionalProduct.coeff 355 =
      (
        ((43069931929735688278834 * 10 ^ 70 +
          7270516978981124629581488818804402338633709071932663278549805723125738)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 356,
    recurrence4A4Square.coeff x * exceptional4.coeff (355 - x)) = _
  rw [show 356 = 342 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_355_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 343,
      recurrence4A4Square.coeff x * exceptional4.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (356 - x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_356 :
    recurrence4ExceptionalProduct.coeff 356 =
      (
        ((45597069595604097286 * 10 ^ 70 +
          6725499158148420771052445963277796812271559229676050904594090036666935)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 357,
    recurrence4A4Square.coeff x * exceptional4.coeff (356 - x)) = _
  rw [show 357 = 343 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_356_prefix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 344,
      recurrence4A4Square.coeff x * exceptional4.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (357 - x) (by
    omega)]
  norm_num

private theorem recurrence4ExceptionalProduct_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4A4Square.coeff (357 + x) *
        exceptional4.coeff (357 - (357 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4Square_coeff_high (357 + x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_357 :
    recurrence4ExceptionalProduct.coeff 357 =
      (
        ((26519512858685447 * 10 ^ 70 +
          0751895881513564956592321382383796326522306741936568194056599326098341)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 358,
    recurrence4A4Square.coeff x * exceptional4.coeff (357 - x)) = _
  rw [show 358 = 344 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 13 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4ExceptionalProduct_coeff_357_suffix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 345,
      recurrence4A4Square.coeff x * exceptional4.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (358 - x) (by
    omega)]
  norm_num

private theorem recurrence4ExceptionalProduct_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence4A4Square.coeff (357 + x) *
        exceptional4.coeff (358 - (357 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4Square_coeff_high (357 + x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_358 :
    recurrence4ExceptionalProduct.coeff 358 =
      (
        ((8937269629167 * 10 ^ 70 +
          4416961109840904666312062200896625901472901710744211272069648318962343)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 359,
    recurrence4A4Square.coeff x * exceptional4.coeff (358 - x)) = _
  rw [show 359 = 345 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 12 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4ExceptionalProduct_coeff_358_suffix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 346,
      recurrence4A4Square.coeff x * exceptional4.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (359 - x) (by
    omega)]
  norm_num

private theorem recurrence4ExceptionalProduct_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence4A4Square.coeff (357 + x) *
        exceptional4.coeff (359 - (357 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4Square_coeff_high (357 + x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_359 :
    recurrence4ExceptionalProduct.coeff 359 =
      (
        ((1738113101 * 10 ^ 70 +
          8097775087365227140511678753191384274788257261051133485854221575598133)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 360,
    recurrence4A4Square.coeff x * exceptional4.coeff (359 - x)) = _
  rw [show 360 = 346 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 11 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4ExceptionalProduct_coeff_359_suffix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 347,
      recurrence4A4Square.coeff x * exceptional4.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (360 - x) (by
    omega)]
  norm_num

private theorem recurrence4ExceptionalProduct_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence4A4Square.coeff (357 + x) *
        exceptional4.coeff (360 - (357 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4Square_coeff_high (357 + x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_360 :
    recurrence4ExceptionalProduct.coeff 360 =
      (
        ((189289 * 10 ^ 70 +
          0078317951773017524590747017398383231721773631238714423212447604826426)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 361,
    recurrence4A4Square.coeff x * exceptional4.coeff (360 - x)) = _
  rw [show 361 = 347 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 10 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4ExceptionalProduct_coeff_360_suffix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 348,
      recurrence4A4Square.coeff x * exceptional4.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (361 - x) (by
    omega)]
  norm_num

private theorem recurrence4ExceptionalProduct_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence4A4Square.coeff (357 + x) *
        exceptional4.coeff (361 - (357 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4Square_coeff_high (357 + x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_361 :
    recurrence4ExceptionalProduct.coeff 361 =
      (
        ((11 * 10 ^ 70 +
          1009464229048848137243668332927625178111781846702999716178597956661138)) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 362,
    recurrence4A4Square.coeff x * exceptional4.coeff (361 - x)) = _
  rw [show 362 = 348 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 9 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4ExceptionalProduct_coeff_361_suffix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 349,
      recurrence4A4Square.coeff x * exceptional4.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (362 - x) (by
    omega)]
  norm_num

private theorem recurrence4ExceptionalProduct_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence4A4Square.coeff (357 + x) *
        exceptional4.coeff (362 - (357 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4Square_coeff_high (357 + x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_362 :
    recurrence4ExceptionalProduct.coeff 362 =
      (
        (3292644832739261628811456125415571697666036236417031119085333146408) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 363,
    recurrence4A4Square.coeff x * exceptional4.coeff (362 - x)) = _
  rw [show 363 = 349 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 8 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4ExceptionalProduct_coeff_362_suffix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 350,
      recurrence4A4Square.coeff x * exceptional4.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (363 - x) (by
    omega)]
  norm_num

private theorem recurrence4ExceptionalProduct_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence4A4Square.coeff (357 + x) *
        exceptional4.coeff (363 - (357 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4Square_coeff_high (357 + x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_363 :
    recurrence4ExceptionalProduct.coeff 363 =
      (
        (46751881819213323252754794931439660838490049027739114506910490) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 364,
    recurrence4A4Square.coeff x * exceptional4.coeff (363 - x)) = _
  rw [show 364 = 350 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 7 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4ExceptionalProduct_coeff_363_suffix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 351,
      recurrence4A4Square.coeff x * exceptional4.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (364 - x) (by
    omega)]
  norm_num

private theorem recurrence4ExceptionalProduct_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence4A4Square.coeff (357 + x) *
        exceptional4.coeff (364 - (357 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4Square_coeff_high (357 + x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_364 :
    recurrence4ExceptionalProduct.coeff 364 =
      (
        (282205639995319306412748762628103752386358718218540213505) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 365,
    recurrence4A4Square.coeff x * exceptional4.coeff (364 - x)) = _
  rw [show 365 = 351 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 6 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4ExceptionalProduct_coeff_364_suffix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 352,
      recurrence4A4Square.coeff x * exceptional4.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (365 - x) (by
    omega)]
  norm_num

private theorem recurrence4ExceptionalProduct_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence4A4Square.coeff (357 + x) *
        exceptional4.coeff (365 - (357 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4Square_coeff_high (357 + x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_365 :
    recurrence4ExceptionalProduct.coeff 365 =
      (
        (688572124533553278150475357840205733640480943592043) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 366,
    recurrence4A4Square.coeff x * exceptional4.coeff (365 - x)) = _
  rw [show 366 = 352 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 5 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4ExceptionalProduct_coeff_365_suffix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 353,
      recurrence4A4Square.coeff x * exceptional4.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (366 - x) (by
    omega)]
  norm_num

private theorem recurrence4ExceptionalProduct_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence4A4Square.coeff (357 + x) *
        exceptional4.coeff (366 - (357 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4Square_coeff_high (357 + x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_366 :
    recurrence4ExceptionalProduct.coeff 366 =
      (
        (510090730919448538541504811305581829392568035) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 367,
    recurrence4A4Square.coeff x * exceptional4.coeff (366 - x)) = _
  rw [show 367 = 353 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 4 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4ExceptionalProduct_coeff_366_suffix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 354,
      recurrence4A4Square.coeff x * exceptional4.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (367 - x) (by
    omega)]
  norm_num

private theorem recurrence4ExceptionalProduct_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence4A4Square.coeff (357 + x) *
        exceptional4.coeff (367 - (357 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4Square_coeff_high (357 + x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_367 :
    recurrence4ExceptionalProduct.coeff 367 =
      (
        (121790272911401983334556953402217632025) /
        (23215239933528791584969 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 368,
    recurrence4A4Square.coeff x * exceptional4.coeff (367 - x)) = _
  rw [show 368 = 354 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 3 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4ExceptionalProduct_coeff_367_suffix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 355,
      recurrence4A4Square.coeff x * exceptional4.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (368 - x) (by
    omega)]
  norm_num

private theorem recurrence4ExceptionalProduct_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence4A4Square.coeff (357 + x) *
        exceptional4.coeff (368 - (357 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4Square_coeff_high (357 + x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_368 :
    recurrence4ExceptionalProduct.coeff 368 =
      (
        (21405978559284137049) /
        (152365481437 : ℚ)
      ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 369,
    recurrence4A4Square.coeff x * exceptional4.coeff (368 - x)) = _
  rw [show 369 = 355 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 2 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4ExceptionalProduct_coeff_368_suffix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

private theorem recurrence4ExceptionalProduct_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 356,
      recurrence4A4Square.coeff x * exceptional4.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4Exceptional_coeff_high (369 - x) (by
    omega)]
  norm_num

private theorem recurrence4ExceptionalProduct_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence4A4Square.coeff (357 + x) *
        exceptional4.coeff (369 - (357 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A4Square_coeff_high (357 + x) (by
    omega)]
  norm_num

theorem recurrence4ExceptionalProduct_coeff_369 :
    recurrence4ExceptionalProduct.coeff 369 =
      (1 : ℚ) := by
  unfold recurrence4ExceptionalProduct
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 370,
    recurrence4A4Square.coeff x * exceptional4.coeff (369 - x)) = _
  rw [show 370 = 356 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 1 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence4ExceptionalProduct_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4ExceptionalProduct_coeff_369_suffix_zero]
  simp only [Finset.sum_range_succ, orderSevenCoefficient]; norm_num

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

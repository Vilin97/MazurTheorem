/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA3
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: B2A3 coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/

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

private theorem recurrence5B2A3_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (218 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (218 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_218 :
    recurrence5B2A3.coeff 218 =
      ((((16693 * 10 ^ 70 +
        4111356529401431157921229186743009128074467097272857615376374379844950) * 10 ^ 70 +
        7610200159132735692438523866982373104834512798727008966263729961457582) * 10 ^ 70 +
        8837082924762066433853892240346871728710907782205998416838373714146779) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 219 = 54 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 28 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_218_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_218_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 55,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (219 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (219 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_219 :
    recurrence5B2A3.coeff 219 =
      -((((7303 * 10 ^ 70 +
        8201564871956665786565812301783610332476376730937760114355854407519147) * 10 ^ 70 +
        8272664604770562745303241762155293352638667760704241930882527826747891) * 10 ^ 70 +
        4675634579226356282175718001486629125114733380242926667990343959980710) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 220 = 55 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 27 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_219_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_219_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 56,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (220 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (220 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_220 :
    recurrence5B2A3.coeff 220 =
      ((((3075 * 10 ^ 70 +
        6893052526572052926124841661385842967539823941741854268395366976808781) * 10 ^ 70 +
        3972815772731290297468200211542591991744693462753323283766201572496127) * 10 ^ 70 +
        5800008468264202767287929201455395393176384097809292277460877121566453) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 221 = 56 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 26 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_220_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_220_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 57,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (221 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (221 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_221 :
    recurrence5B2A3.coeff 221 =
      -((((1247 * 10 ^ 70 +
        7652263882136714018684707816376011414526423921459154472462927382085062) * 10 ^ 70 +
        4658364842346547911902826239775831624476807080660752475703463829064536) * 10 ^ 70 +
        7159446925051159889382052201261546727388122358517593193013573758308739) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 222 = 57 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 25 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_221_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_221_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 58,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (222 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (222 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_222 :
    recurrence5B2A3.coeff 222 =
      ((((487 * 10 ^ 70 +
        7897516646932099496105446269894720364330091085327160649312689038956594) * 10 ^ 70 +
        3359067849466256850305658809755209346624344912200235970998916000977684) * 10 ^ 70 +
        5310089113619714428251176694572980773275359017502863997239990336008839) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 223 = 58 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 24 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_222_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_222_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 59,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (223 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (223 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_223 :
    recurrence5B2A3.coeff 223 =
      -((((183 * 10 ^ 70 +
        6487233132699722019764106669975978278397906330401612613870776248961163) * 10 ^ 70 +
        0397492164893615274549925166884262147756629312606845194331126113085912) * 10 ^ 70 +
        7305585174473444838091031016559855213306059003706366522726518848899082) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 224 = 59 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 23 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_223_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_223_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 60,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (224 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (224 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_224 :
    recurrence5B2A3.coeff 224 =
      ((((66 * 10 ^ 70 +
        4805067697323113278097910480981455446855801370087296852377168718791710) * 10 ^ 70 +
        7938403878206202961090491208602797341844346826891428681021855739115282) * 10 ^ 70 +
        1607418798235665299432482464330849630683045523597519113028828468777627) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 225 = 60 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 22 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_224_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_224_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 61,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (225 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (225 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_225 :
    recurrence5B2A3.coeff 225 =
      -((((23 * 10 ^ 70 +
        0710535905253184248937059962009084372674153994695171600326800736436427) * 10 ^ 70 +
        9237985652015848257393838612147072337451863328547584225024700653438886) * 10 ^ 70 +
        8924920162580287437393042942484687182560339994405152504140231238507310) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 226 = 61 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 21 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_225_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_225_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 62,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (226 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (226 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_226 :
    recurrence5B2A3.coeff 226 =
      ((((7 * 10 ^ 70 +
        6386404700743127576011180206224233594046486763556436385041774939131338) * 10 ^ 70 +
        2529635180821945512827760894965779606703524191399622052679836171288463) * 10 ^ 70 +
        4695344934035401886991603737929203399605480901599672575034718760563692) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 227 = 62 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 20 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_226_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_226_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 63,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (227 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (227 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_227 :
    recurrence5B2A3.coeff 227 =
      -((((2 * 10 ^ 70 +
        3944192731882255287563695231602301464075188628977855421286866532147277) * 10 ^ 70 +
        0495850519993546195715820109788567865318900415821809084191552183006697) * 10 ^ 70 +
        9705951830811221051569388179754893658847206948112264991767403499444109) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 228 = 63 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 19 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_227_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_227_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 64,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (228 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (228 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_228 :
    recurrence5B2A3.coeff 228 =
      (((7015659687336382374457579040535430723840245781317358980830187790516085 * 10 ^ 70 +
        2518183560081095346549723709939317805893136055735414936184057184068227) * 10 ^ 70 +
        2757491967355695608457236601688937508346265595781657309223061908073049) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 229 = 64 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 18 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_228_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_228_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 65,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (229 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (229 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_229 :
    recurrence5B2A3.coeff 229 =
      -(((1876982827617314100120492070273098465319273812569911666579506727504859 * 10 ^ 70 +
        6726624072913506659756512278375213193153388191490581889555768830574230) * 10 ^ 70 +
        7366169638396086385137881739219449995602518677262892864937482388987610) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 230 = 65 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 17 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_229_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_229_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (230 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (230 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_230 :
    recurrence5B2A3.coeff 230 =
      (((435750833826197449826475196094972737429416829138114219691046060062141 * 10 ^ 70 +
        7828087403568431578564503868437951559577895380380493473823227720005268) * 10 ^ 70 +
        1597496039536590221049947120933747899854111903188594198069452500109106) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 231 = 66 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 16 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_230_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_230_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (231 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (231 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_231 :
    recurrence5B2A3.coeff 231 =
      -(((75112647360059848111844564559264931652279445602715874470411506413715 * 10 ^ 70 +
        8603914948510396600363326546379543206495870416560680164429022072301970) * 10 ^ 70 +
        7947865724214729531046564262640427821914383720791559881733725878953602) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 232 = 67 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 15 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_231_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_231_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (232 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (232 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_232 :
    recurrence5B2A3.coeff 232 =
      (((1452148910187265514212847998199617466582328953845994350391471495990 * 10 ^ 70 +
        0776903749082371612030311220561527718244107628272486019208261398613718) * 10 ^ 70 +
        0255222136166749972200453499636115370271114034298729436609357914599575) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 233 = 68 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 14 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_232_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_232_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (233 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (233 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_233 :
    recurrence5B2A3.coeff 233 =
      (((6736860419126748197069495513837266234946982782757384291922001030204 * 10 ^ 70 +
        7040933878131643664465334310461524125035900663951641019273819636561724) * 10 ^ 70 +
        5616777012900044234875679868327867999403175310363462174643740708346691) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 234 = 69 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 13 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_233_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_233_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (234 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (234 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_234 :
    recurrence5B2A3.coeff 234 =
      -(((4227775537378530051198908798926324889666587613391155992832414371242 * 10 ^ 70 +
        4482541888591023730097859645383336897624236180643251710660714565436947) * 10 ^ 70 +
        5823664376064934338365816683297196292048191361849407059619958336149616) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 235 = 70 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 12 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_234_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (235 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (235 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_235 :
    recurrence5B2A3.coeff 235 =
      (((1874235901269294229145571734931422435067409425150951725998035913427 * 10 ^ 70 +
        7905688977040129662336353748454663725743055863703821908342306779056022) * 10 ^ 70 +
        3837868450060396771050914762801389928202925284321991575805632012533580) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 236 = 71 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 11 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_235_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (236 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (236 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_236 :
    recurrence5B2A3.coeff 236 =
      -(((703002827691833788639809366349743638846953873869175552650749902355 * 10 ^ 70 +
        0976706994177380724885871779069252314804333990244053893208997954758925) * 10 ^ 70 +
        6682087880150208052404624672564582271148010098242283031224054977082166) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 237 = 72 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 10 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_236_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (237 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 92,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (237 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_237 :
    recurrence5B2A3.coeff 237 =
      (((233094381522530729226076402586446808235133940896985483787668699564 * 10 ^ 70 +
        6203404148901878572173677094245018971923809732695649003824156503533917) * 10 ^ 70 +
        7698105171026362404126732792600342647727458788546304417302830203198433) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 238 = 73 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 9 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_237_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (238 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 93,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (238 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_238 :
    recurrence5B2A3.coeff 238 =
      -(((68150734461920570907517511846108596782894572619695413452717878882 * 10 ^ 70 +
        8252153369502275728372050879597498309243781071305231490369971029434298) * 10 ^ 70 +
        2499311184841639819867024467730195895718628750483374060455739856912511) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 239 = 74 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 8 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_238_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (239 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 94,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (239 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_239 :
    recurrence5B2A3.coeff 239 =
      (((16615331225985531838091105971699200417414572353003328835438167990 * 10 ^ 70 +
        5844906523910499373185297322855230539953297546796861042801681122925284) * 10 ^ 70 +
        6235714307978179231439413834596464141072137314045115188779579460943891) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 240 = 75 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 7 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_239_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (240 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 95,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (240 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_240 :
    recurrence5B2A3.coeff 240 =
      -(((2606786093312924645947509993903148834217804144614130237278563686 * 10 ^ 70 +
        2478189952986102971685871655579309008054326605707996392081271091965002) * 10 ^ 70 +
        4775026610850667293123605734271592725171024597450170968512217884695478) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 241 = 76 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 6 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_240_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (241 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 96,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (241 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_241 :
    recurrence5B2A3.coeff 241 =
      -(((372107304811180494298763346069304853331938391305629040909956352 * 10 ^ 70 +
        9614389979906458097809480372469283865869967617607010694328977379533676) * 10 ^ 70 +
        4855549327221531492656423195961892183183006863039302764349116357601502) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 242 = 77 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 5 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_241_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (242 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 97,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (242 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_242 :
    recurrence5B2A3.coeff 242 =
      (((609847396187572116610581028421224905463483867311292111261406106 * 10 ^ 70 +
        3763466295940162736641632125613177058820420638047939620492964634374014) * 10 ^ 70 +
        0009891390656916244629828313815129875863288616910392139294582810263407) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 243 = 78 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 4 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_242_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (243 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 98,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (243 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_243 :
    recurrence5B2A3.coeff 243 =
      -(((382420224203540197519319026384322470822321898390338177684789689 * 10 ^ 70 +
        4203168793659039693412759290957390306101683993930222721336920276211414) * 10 ^ 70 +
        5678555948335774960559982914067426058449662659570390594401007896049044) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 244 = 79 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 3 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_243_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (244 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 99,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (244 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_244 :
    recurrence5B2A3.coeff 244 =
      (((190080638573161079730022059259217998349154299998548255447920148 * 10 ^ 70 +
        7756127181601803415665438021133876810058510610136363546174279521237261) * 10 ^ 70 +
        5068663287200328383951004522915861508430209313115612467900245196470898) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 245 = 80 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 2 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_244_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (245 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 100,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (245 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_245 :
    recurrence5B2A3.coeff 245 =
      -(((84084474943034166098542127199153276567139248661284948779417390 * 10 ^ 70 +
        8973829125404653825519114056655938196100899182760370617594320433078871) * 10 ^ 70 +
        2960116508339549753663593296004069149228954631010836719678368258697211) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 246 = 81 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 1 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_245_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (246 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 101,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (246 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_246 :
    recurrence5B2A3.coeff 246 =
      (((34483998853563872809908093804431405457473667516581251619917849 * 10 ^ 70 +
        4714293927681413745193067660323674435063558702006246586868390327548693) * 10 ^ 70 +
        1473284136565613740338330760310915313386676756574747916910809767149663) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 247 = 82 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_246_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (247 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 102,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (247 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_247 :
    recurrence5B2A3.coeff 247 =
      -(((13360240874557270442993378068876465597813416853687659080589625 * 10 ^ 70 +
        7766550537798360366500280238567534487969812487358754762090050732987505) * 10 ^ 70 +
        8572641074251067775643707952689304653703320156257650963047714726329357) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 248 = 83 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 31 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_247_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (248 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 103,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (248 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_248 :
    recurrence5B2A3.coeff 248 =
      (((4938403953460857513977524315553407022088363783812810404223817 * 10 ^ 70 +
        8553156582951290873905189453525839009098842354088025439878005679227854) * 10 ^ 70 +
        2741834954284277175514939996819145721600935306256787306436318074761294) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 249 = 84 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 30 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_248_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (249 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 104,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (249 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_249 :
    recurrence5B2A3.coeff 249 =
      -(((1751017584249474355915265410718548560959754367730164432335350 * 10 ^ 70 +
        5360968735000592467971304961593498682088663583309567850793024235527270) * 10 ^ 70 +
        5115410975149129701212831765173724206409492717202794441647827549783002) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 250 = 85 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 29 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_249_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (250 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 105,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (250 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_250 :
    recurrence5B2A3.coeff 250 =
      (((597276838862391469942837073490379202602529224397220924819628 * 10 ^ 70 +
        4345452419090475497449370070218748098323905727040541573753222290774883) * 10 ^ 70 +
        8322925191624438247522935706116871295435428288727271011329330127973417) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 251 = 86 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 28 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_250_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (251 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 106,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (251 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_251 :
    recurrence5B2A3.coeff 251 =
      -(((196236707572347987085604115409971859528581299679478670000235 * 10 ^ 70 +
        7969767456272024922525972595487392281516437688816388224537402601738228) * 10 ^ 70 +
        7533633296074237101231313118981396005511262907814069042284457537757973) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 252 = 87 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 27 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_251_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_251_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (252 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 107,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (252 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_252 :
    recurrence5B2A3.coeff 252 =
      (((62110495426971300381306234594588769728145031617590966623994 * 10 ^ 70 +
        3547213232769182967770373490429955403478733156691846382917426370641334) * 10 ^ 70 +
        7462631598926751219651243165114289899564720299359006350203425434999901) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 253 = 88 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 26 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_252_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_252_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (253 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 108,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (253 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_253 :
    recurrence5B2A3.coeff 253 =
      -(((18927784846763359532908459178707808246080514928519922404201 * 10 ^ 70 +
        7278749029617859098340539619659306397099401126417282649476808072906158) * 10 ^ 70 +
        2704299755844933680560140810699107665029946115294225345746403020065083) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 254 = 89 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 25 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_253_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (254 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 109,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (254 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_254 :
    recurrence5B2A3.coeff 254 =
      (((5549402654558440100568686101448569829942660373352136793236 * 10 ^ 70 +
        1277270950761511854407495395110321693832872236265370457323471309325095) * 10 ^ 70 +
        0243986389015246941178370257507826946378622913658608334707673769980243) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 255 = 90 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 24 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_254_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (255 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 110,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (255 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_255 :
    recurrence5B2A3.coeff 255 =
      -(((1564350050016517104312246379829176891638675811468172394539 * 10 ^ 70 +
        5686497958000275964633873713415870389289635507714844741448322145893254) * 10 ^ 70 +
        5520419241937665790567003479673468946442685941834387364531639716676370) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 256 = 91 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 23 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_255_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (256 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 111,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (256 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_256 :
    recurrence5B2A3.coeff 256 =
      (((423924534070801909912286619779797276280517683336815277618 * 10 ^ 70 +
        2652264037212529558234982360476026603019142922542140782315565208783815) * 10 ^ 70 +
        4971633245919205624780123804720639712534658929259329339911468945389627) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 257 = 92 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 22 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_256_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (257 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 112,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (257 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_257 :
    recurrence5B2A3.coeff 257 =
      -(((110467568428404791705972877587883424398230717435662745547 * 10 ^ 70 +
        8510124988178932266765601539158779880569254880805289038545409374040427) * 10 ^ 70 +
        8468187357215231607455834809283607339244758735876734062058206893807793) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 258 = 93 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 21 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_257_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (258 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 113,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (258 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_258 :
    recurrence5B2A3.coeff 258 =
      (((27687137380522326405024333727788443785338312899766793971 * 10 ^ 70 +
        7676809598392084685961177057936870086371967842105389656356713857193449) * 10 ^ 70 +
        5763371836906343559612584646493248130334364571862996608085057347098505) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 259 = 94 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 20 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_258_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (259 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 114,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (259 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_259 :
    recurrence5B2A3.coeff 259 =
      -(((6667874261771299440645911622469306227176319277794053333 * 10 ^ 70 +
        0742344839785867133186520551565028737162418543278569918537762484739907) * 10 ^ 70 +
        5902702199138835359073376634831682621244199248216998584621343297455197) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 260 = 95 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 19 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_259_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (260 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 115,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (260 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_260 :
    recurrence5B2A3.coeff 260 =
      (((1536640895718523693187929548176258359243867471689447880 * 10 ^ 70 +
        6364476205021731360052233322904427451364718457848452945746411231473381) * 10 ^ 70 +
        7275736117390053967636366367784751854662065653285814168859531878613708) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 261 = 96 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 18 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_260_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (261 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 116,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (261 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_261 :
    recurrence5B2A3.coeff 261 =
      -(((335576344839130426214467539885940940449345056789638709 * 10 ^ 70 +
        6508318354258600648716579537501749181741203448487021525750028981055612) * 10 ^ 70 +
        5297029521645968895234033182809196974284592082394852608748838010093284) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 262 = 97 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 17 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_261_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (262 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 117,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (262 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_262 :
    recurrence5B2A3.coeff 262 =
      (((68140590326394272504617709348230240024985409849297633 * 10 ^ 70 +
        8488373116270797803370711265231932745946945436856439373147390462186811) * 10 ^ 70 +
        7074745916028696008913312084128949568628774114654078456544563060010903) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 263 = 98 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 16 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_262_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (263 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 118,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (263 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_263 :
    recurrence5B2A3.coeff 263 =
      -(((12413918291228995925034269344216916615929889745475223 * 10 ^ 70 +
        1064602055894295913286179800006908282297529277417980830653478171026021) * 10 ^ 70 +
        4332379231838389845195322653448956414172280936341758816597265851314799) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 264 = 99 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 15 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_263_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (264 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 119,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (264 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_264 :
    recurrence5B2A3.coeff 264 =
      (((1877008210290334882708220473320612766447773929554440 * 10 ^ 70 +
        1026327442211936629215830237873736845091200000411503728061689061473959) * 10 ^ 70 +
        0775830475078108327732020144682538741051920606805652552945319676443511) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 265 = 100 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 14 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_264_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (265 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 120,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (265 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_265 :
    recurrence5B2A3.coeff 265 =
      -(((180025412787013870855251374863036319919100986136751 * 10 ^ 70 +
        2403323129324229479589813983262847037605674964012542271361444268168655) * 10 ^ 70 +
        1896756817982069992951835774174409130695966650147901745246085465140877) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 266 = 101 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 13 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_265_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (266 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 121,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (266 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_266 :
    recurrence5B2A3.coeff 266 =
      -(((13407515729990856752138718817325119507024304344516 * 10 ^ 70 +
        4394165740385975562901160075940133260873039111524169246123556395637663) * 10 ^ 70 +
        9556508302146683120860245638469604651698212763493619443401076262406008) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 267 = 102 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 12 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_266_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (267 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 122,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (267 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_267 :
    recurrence5B2A3.coeff 267 =
      (((12633454102324746758534040570856720401468755573653 * 10 ^ 70 +
        1975716290528625963461633904761157416658637381697001579404009209999782) * 10 ^ 70 +
        6041711051074638054401574661647609925846152321864794812641992969034073) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 268 = 103 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 11 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_267_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (268 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 123,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (268 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_268 :
    recurrence5B2A3.coeff 268 =
      -(((3988015154314737472825823788363290898433084126476 * 10 ^ 70 +
        8484243177028717421199180712828711114885357042044380153557568226784993) * 10 ^ 70 +
        3814105170317233545642746751667424276398574365153299165373761663571853) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 269 = 104 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 10 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_268_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (269 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 124,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (269 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_269 :
    recurrence5B2A3.coeff 269 =
      (((884096402456744597860029583361395903683736996297 * 10 ^ 70 +
        5219752805914330541361879387765846324663870161575742230155717916113306) * 10 ^ 70 +
        5526305348394447455727013693084657170505697077204128256923987476384510) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 270 = 105 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 9 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_269_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (270 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 125,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (270 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_270 :
    recurrence5B2A3.coeff 270 =
      -(((144175563803592012456706300663402923076384190854 * 10 ^ 70 +
        8476548717533050179050708467036271155022147587554735963275637917300219) * 10 ^ 70 +
        2839140294487007447235950211382087748111574550781904124099867081260820) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 271 = 106 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 8 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_270_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (271 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 126,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (271 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_271 :
    recurrence5B2A3.coeff 271 =
      (((14109523240114645639070807992829770454378916678 * 10 ^ 70 +
        2879066533059221681058013572140663878484332633523586970130453820850805) * 10 ^ 70 +
        2629369713819055564238131906923679231199935235211644386596620836885042) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 272 = 107 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 7 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_271_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (272 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 127,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (272 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_272 :
    recurrence5B2A3.coeff 272 =
      (((751712370621071236892694526708164014802676708 * 10 ^ 70 +
        3661354857348807699381914292418904522141485446830806269624465528776717) * 10 ^ 70 +
        1006903140383369570842282597733185167941612152021264776496348356143698) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 273 = 108 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 6 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_272_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (273 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 128,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (273 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_273 :
    recurrence5B2A3.coeff 273 =
      -(((742596012715101668180121080612369959494196579 * 10 ^ 70 +
        4599747522927140295279146097559236943278155795303545255517033699614440) * 10 ^ 70 +
        5937470738325353186845271758374865770684716194220065297560273753386799) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 274 = 109 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 5 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_273_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 110,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (274 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 129,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (274 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_274 :
    recurrence5B2A3.coeff 274 =
      (((206987248452131958758825718987345383799492645 * 10 ^ 70 +
        2748313226611879575822861592538846224332992556794716607676686871010616) * 10 ^ 70 +
        3670337044145492263973230565003655242666636439196692150689866305346069) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 275 = 110 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 4 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_274_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 111,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (275 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 130,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (275 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_275 :
    recurrence5B2A3.coeff 275 =
      -(((39934803844003054178005319638272952307537013 * 10 ^ 70 +
        6931378180669988670290142309849319939129454527050253738163460574718409) * 10 ^ 70 +
        5754779207721971618746643173367829438745309522203997482264105062573954) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 276 = 111 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 3 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_275_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (276 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 131,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (276 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_276 :
    recurrence5B2A3.coeff 276 =
      (((5936693106171337959198058522093005013457949 * 10 ^ 70 +
        5884804706327172093519130994476009967893654134670247041127751134293748) * 10 ^ 70 +
        2949302576133629121450164315733675520807342392672303687398822381409537) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 277 = 112 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 2 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_276_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (277 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 132,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (277 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_277 :
    recurrence5B2A3.coeff 277 =
      -(((686840481128940684632784757557129028619818 * 10 ^ 70 +
        3444920639037895704466236904293796886410221817815731625189273444783952) * 10 ^ 70 +
        2597311853251958798986212896891008217350641722338455107630872765143280) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 278 = 113 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 1 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_277_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (278 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 133,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (278 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_278 :
    recurrence5B2A3.coeff 278 =
      (((58807464890362283527441382232166532881684 * 10 ^ 70 +
        6888227821097738248072514685024715921446346077765866109938716927462671) * 10 ^ 70 +
        5629201908039046198853116334031326947202551309847097082062233068616564) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 279 = 114 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_278_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (279 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 134,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (279 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_279 :
    recurrence5B2A3.coeff 279 =
      -(((3024546340947104787322458598887898132997 * 10 ^ 70 +
        3973722404411679542999270076154869724016416886723488781132028571461144) * 10 ^ 70 +
        1891116458321873274227768494025039375902852446904261868508945328275141) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 280 = 115 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 31 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_279_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (280 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 135,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (280 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_280 :
    recurrence5B2A3.coeff 280 =
      -(((38399691254034170442620943779603885431 * 10 ^ 70 +
        6873214653897787393834769047074817003930823914766703925572012553921001) * 10 ^ 70 +
        1537024808313266372347783752097079571780141311212483285297687795919159) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 281 = 116 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 30 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_280_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (281 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 136,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (281 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_281 :
    recurrence5B2A3.coeff 281 =
      (((25751630150240390325844235320854854039 * 10 ^ 70 +
        4135431580730239888420717825923457149130182473416613850917170691900806) * 10 ^ 70 +
        6859653455334144137895360674524251023809541407048705420609997141539809) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 282 = 117 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 29 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_281_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (282 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 137,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (282 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_282 :
    recurrence5B2A3.coeff 282 =
      -(((2727457516191637195188562662742710990 * 10 ^ 70 +
        8397130902142466072930034611847740880054810608054084674411597229110965) * 10 ^ 70 +
        2850600336994429110912082958641173350908635087343687434080575841001493) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 283 = 118 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 28 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_282_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (283 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 138,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (283 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_283 :
    recurrence5B2A3.coeff 283 =
      (((154996696695594187824517760901087328 * 10 ^ 70 +
        4251666093653747811173749020373930312907979409817063196281253612520332) * 10 ^ 70 +
        5714004089637561810848722793217456211822388622828642892355587493384944) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 284 = 119 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 27 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_283_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (284 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 139,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (284 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_284 :
    recurrence5B2A3.coeff 284 =
      -(((3848870321508211267731086275158339 * 10 ^ 70 +
        7539547934385749056072434412083945461569061632936801364224037312817004) * 10 ^ 70 +
        1892057625783966587464955636961373250390499292873867226834416451966962) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 285 = 120 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 26 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_284_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (285 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 140,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (285 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_285 :
    recurrence5B2A3.coeff 285 =
      -(((86724349149485785721479766228865 * 10 ^ 70 +
        8894673320668243673452335473339971012343323295462251270467170484460774) * 10 ^ 70 +
        2487459375076124001463007507397576836586234007249244259473011384136649) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 286 = 121 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 25 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_285_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (286 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 141,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (286 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_286 :
    recurrence5B2A3.coeff 286 =
      (((8289209665602542532325834173478 * 10 ^ 70 +
        7317662408815244272296186937667017941072714223862125981321862882470430) * 10 ^ 70 +
        7567354201063270097632237835050268613560036165135296642084505381729102) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 287 = 122 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 24 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_286_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (287 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 142,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (287 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_287 :
    recurrence5B2A3.coeff 287 =
      -(((118940211514190040095155839478 * 10 ^ 70 +
        6490227751684490519350471969998932185650612176914154657106201912970631) * 10 ^ 70 +
        6925207456535516485564063323307878495238958922228569521720324191904523) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 288 = 123 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 23 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_287_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (288 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 143,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (288 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_288 :
    recurrence5B2A3.coeff 288 =
      -(((2819891874363770582975333381 * 10 ^ 70 +
        9398167970244767844000849779574761027954706037563935550143393388332203) * 10 ^ 70 +
        2476702525005906486313387869546262167238516980269689111614366952245287) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 289 = 124 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 22 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_288_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 144,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (289 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_289 :
    recurrence5B2A3.coeff 289 =
      (((25463444655023966774717387 * 10 ^ 70 +
        4794455433627505974566208215106050370743706697266650208307567201097725) * 10 ^ 70 +
        3589504188543493855408262986302807754645892686413146482465438116151905) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 290 = 125 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 21 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_289_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 145,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (290 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_290 :
    recurrence5B2A3.coeff 290 =
      (((433906456760591289412345 * 10 ^ 70 +
        7707486948754950685927348483526229694036477735555445029850015998675463) * 10 ^ 70 +
        1395209125435730742785023175262341746701364945679580421841597039795488) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 291 = 126 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 20 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_290_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (291 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 146,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (291 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_291 :
    recurrence5B2A3.coeff 291 =
      (((212047891261002068987 * 10 ^ 70 +
        6614008385524315487478734260485611915668098797641674648522362928999301) * 10 ^ 70 +
        1232733906029912546091777237463543768791129178517481064842161960095683) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 292 = 127 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 19 +
      146 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_291_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (292 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 147,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (292 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_292 :
    recurrence5B2A3.coeff 292 =
      -(((13518408639844330333 * 10 ^ 70 +
        4287295760434546308407793749925481283810741518749685405359012507757775) * 10 ^ 70 +
        0315770001514796050926908506572736886602015194820943115034359577534593) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 293 = 128 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 18 +
      147 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_292_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (293 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 148,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (293 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_293 :
    recurrence5B2A3.coeff 293 =
      -(((33226796052068817 * 10 ^ 70 +
        8650685262001787930223461494354360896969953253256532601886055163020384) * 10 ^ 70 +
        0536238348567624821425054050836959724916836142999611057271609152287909) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 294 = 129 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 17 +
      148 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_293_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (294 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 149,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (294 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_294 :
    recurrence5B2A3.coeff 294 =
      (((115939093188888 * 10 ^ 70 +
        3252904050868142392310800599099042677834481357144689873692820457908652) * 10 ^ 70 +
        0541745556940109938183368115744654391209797158636859656199881138803386) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 295 = 130 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 16 +
      149 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_294_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (295 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 150,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (295 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_295 :
    recurrence5B2A3.coeff 295 =
      (((345495533642 * 10 ^ 70 +
        4945079459995286747957287153734273847696402534191440414913205128481896) * 10 ^ 70 +
        7800124057079819371692834737946686648078121442838776326349827525851545) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 296 = 131 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 15 +
      150 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_295_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 132,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (296 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 151,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (296 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_296 :
    recurrence5B2A3.coeff 296 =
      -(((504363852 * 10 ^ 70 +
        6791424008057756101522817923971393406476791753198516350277832860503506) * 10 ^ 70 +
        2917078978997013238288016798944716777206531770883093050897857668817610) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 297 = 132 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 14 +
      151 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_296_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 133,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (297 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 152,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (297 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_297 :
    recurrence5B2A3.coeff 297 =
      -(((1207317 * 10 ^ 70 +
        3788100994155306779424877000782852596244807487668003621482898313119298) * 10 ^ 70 +
        1625874016889579818950231786412316373192360130433754683042113135500217) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 298 = 133 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 13 +
      152 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_297_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 134,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (298 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 153,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (298 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_298 :
    recurrence5B2A3.coeff 298 =
      (((1310 * 10 ^ 70 +
        9098849070668636309147327716639100963684329901389085700375849105551109) * 10 ^ 70 +
        5345717743997164937257596950351371619606779468637679352772238479132577) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 299 = 134 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 12 +
      153 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_298_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 135,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (299 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 154,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (299 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_299 :
    recurrence5B2A3.coeff 299 =
      ((8951339088841467914644878784506154822385514855991002260329596100524233 * 10 ^ 70 +
        9146120525868919543766865723479458228116616993928799968270200369976910) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 300 = 135 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 11 +
      154 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_299_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 136,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (300 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 155,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (300 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_300 :
    recurrence5B2A3.coeff 300 =
      -((6728118100740322612864188019863958007441804742355505221892662241619 * 10 ^ 70 +
        2016853200722501091551018024328007081019374240132651166459265290188189) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 301 = 136 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 10 +
      155 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_300_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 137,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (301 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 156,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (301 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_301 :
    recurrence5B2A3.coeff 301 =
      -((249064310112960556473423077599439495063463349104725234760057321 * 10 ^ 70 +
        9832967718950954697129273699824113685124855830703076031294641410338122) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 302 = 137 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 9 +
      156 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_301_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 138,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 157,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (302 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_302 :
    recurrence5B2A3.coeff 302 =
      ((180393885932545700309053067866379235540490420201272077197215 * 10 ^ 70 +
        5812504730409037702652760565720575799627211236073578071011782301377810) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 303 = 138 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 8 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_302_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 139,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 158,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (303 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_303 :
    recurrence5B2A3.coeff 303 =
      -((2426852626663974412487691834743716741164874475667190770 * 10 ^ 70 +
        3044172133252466244212738176505640746374030426195730553263822825515064) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 304 = 139 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 7 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_303_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 140,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 159,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (304 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_304 :
    recurrence5B2A3.coeff 304 =
      -((143878255635506536330830636521589905468773759682062 * 10 ^ 70 +
        0158339181508382232387578101846913438852755992778470433986209034721099) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 305 = 140 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 6 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_304_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 141,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 160,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (305 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_305 :
    recurrence5B2A3.coeff 305 =
      ((741114523802669245212167159580587433600289499 * 10 ^ 70 +
        0142823489141709913029834099925950711517116535446495729388054300755106) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 306 = 141 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 5 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_305_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 142,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 161,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (306 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_306 :
    recurrence5B2A3.coeff 306 =
      ((1402682626580096834937252990138841574574 * 10 ^ 70 +
        3433116323786234661290594071312924290357215016035187528880876374181271) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 307 = 142 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 4 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_306_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 143,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (307 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 162,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (307 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_307 :
    recurrence5B2A3.coeff 307 =
      -((1126625880180929358338937166496102 * 10 ^ 70 +
        7323701329534353496615714702246744963665555468769230319742889837114922) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 308 = 143 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 3 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_307_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 144,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (308 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 163,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (308 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_308 :
    recurrence5B2A3.coeff 308 =
      -((55320214875044707932456221 * 10 ^ 70 +
        9966177261641144618850906993931715385802085855417811871517770279883629) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 309 = 144 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 2 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_308_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5B2A3_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 145,
      remainder6Coefficient2.coeff x * remainder5Coefficient3.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A3_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 164,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient3.coeff (309 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A3_coeff_309 :
    recurrence5B2A3.coeff 309 =
      ((2401281935794764849 * 10 ^ 70 +
        1317265882802248857700354994805798043618403265673332774640179025005930) : ℚ) := by
  unfold recurrence5B2A3
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 310 = 145 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 1 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A3_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A3_coeff_309_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

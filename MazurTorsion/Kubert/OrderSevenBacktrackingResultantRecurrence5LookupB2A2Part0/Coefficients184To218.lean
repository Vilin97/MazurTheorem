/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB2
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB2A2Part0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: B2A2 coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
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
  recurrence5A2_coeff_0
  recurrence5A2_coeff_1
  recurrence5A2_coeff_2
  recurrence5A2_coeff_3
  recurrence5A2_coeff_4
  recurrence5A2_coeff_5
  recurrence5A2_coeff_6
  recurrence5A2_coeff_7
  recurrence5A2_coeff_8
  recurrence5A2_coeff_9
  recurrence5A2_coeff_10
  recurrence5A2_coeff_11
  recurrence5A2_coeff_12
  recurrence5A2_coeff_13
  recurrence5A2_coeff_14
  recurrence5A2_coeff_15
  recurrence5A2_coeff_16
  recurrence5A2_coeff_17
  recurrence5A2_coeff_18
  recurrence5A2_coeff_19
  recurrence5A2_coeff_20
  recurrence5A2_coeff_21
  recurrence5A2_coeff_22
  recurrence5A2_coeff_23
  recurrence5A2_coeff_24
  recurrence5A2_coeff_25
  recurrence5A2_coeff_26
  recurrence5A2_coeff_27
  recurrence5A2_coeff_28
  recurrence5A2_coeff_29
  recurrence5A2_coeff_30
  recurrence5A2_coeff_31
  recurrence5A2_coeff_32
  recurrence5A2_coeff_33
  recurrence5A2_coeff_34
  recurrence5A2_coeff_35
  recurrence5A2_coeff_36
  recurrence5A2_coeff_37
  recurrence5A2_coeff_38
  recurrence5A2_coeff_39
  recurrence5A2_coeff_40
  recurrence5A2_coeff_41
  recurrence5A2_coeff_42
  recurrence5A2_coeff_43
  recurrence5A2_coeff_44
  recurrence5A2_coeff_45

attribute [local simp]
  recurrence5A2_coeff_46
  recurrence5A2_coeff_47
  recurrence5A2_coeff_48
  recurrence5A2_coeff_49
  recurrence5A2_coeff_50
  recurrence5A2_coeff_51
  recurrence5A2_coeff_52
  recurrence5A2_coeff_53
  recurrence5A2_coeff_54
  recurrence5A2_coeff_55
  recurrence5A2_coeff_56
  recurrence5A2_coeff_57
  recurrence5A2_coeff_58
  recurrence5A2_coeff_59
  recurrence5A2_coeff_60
  recurrence5A2_coeff_61
  recurrence5A2_coeff_62
  recurrence5A2_coeff_63
  recurrence5A2_coeff_64
  recurrence5A2_coeff_65
  recurrence5A2_coeff_66
  recurrence5A2_coeff_67
  recurrence5A2_coeff_68
  recurrence5A2_coeff_69
  recurrence5A2_coeff_70
  recurrence5A2_coeff_71
  recurrence5A2_coeff_72
  recurrence5A2_coeff_73
  recurrence5A2_coeff_74
  recurrence5A2_coeff_75
  recurrence5A2_coeff_76
  recurrence5A2_coeff_77
  recurrence5A2_coeff_78
  recurrence5A2_coeff_79
  recurrence5A2_coeff_80
  recurrence5A2_coeff_81
  recurrence5A2_coeff_82
  recurrence5A2_coeff_83
  recurrence5A2_coeff_84
  recurrence5A2_coeff_85
  recurrence5A2_coeff_86
  recurrence5A2_coeff_87
  recurrence5A2_coeff_88
  recurrence5A2_coeff_89
  recurrence5A2_coeff_90
  recurrence5A2_coeff_91
  recurrence5A2_coeff_92
  recurrence5A2_coeff_93
  recurrence5A2_coeff_94
  recurrence5A2_coeff_95
  recurrence5A2_coeff_96
  recurrence5A2_coeff_97
  recurrence5A2_coeff_98
  recurrence5A2_coeff_99
  recurrence5A2_coeff_100
  recurrence5A2_coeff_101
  recurrence5A2_coeff_102
  recurrence5A2_coeff_103
  recurrence5A2_coeff_104
  recurrence5A2_coeff_105
  recurrence5A2_coeff_106
  recurrence5A2_coeff_107
  recurrence5A2_coeff_108
  recurrence5A2_coeff_109

attribute [local simp]
  recurrence5A2_coeff_110
  recurrence5A2_coeff_111
  recurrence5A2_coeff_112
  recurrence5A2_coeff_113
  recurrence5A2_coeff_114
  recurrence5A2_coeff_115
  recurrence5A2_coeff_116
  recurrence5A2_coeff_117
  recurrence5A2_coeff_118
  recurrence5A2_coeff_119
  recurrence5A2_coeff_120
  recurrence5A2_coeff_121
  recurrence5A2_coeff_122
  recurrence5A2_coeff_123
  recurrence5A2_coeff_124
  recurrence5A2_coeff_125
  recurrence5A2_coeff_126
  recurrence5A2_coeff_127
  recurrence5A2_coeff_128
  recurrence5A2_coeff_129
  recurrence5A2_coeff_130
  recurrence5A2_coeff_131
  recurrence5A2_coeff_132
  recurrence5A2_coeff_133
  recurrence5A2_coeff_134
  recurrence5A2_coeff_135
  recurrence5A2_coeff_136
  recurrence5A2_coeff_137
  recurrence5A2_coeff_138
  recurrence5A2_coeff_139
  recurrence5A2_coeff_140
  recurrence5A2_coeff_141
  recurrence5A2_coeff_142
  recurrence5A2_coeff_143
  recurrence5A2_coeff_144
  recurrence5A2_coeff_145
  recurrence5A2_coeff_146
  recurrence5A2_coeff_147
  recurrence5A2_coeff_148
  recurrence5A2_coeff_149
  recurrence5A2_coeff_150
  recurrence5A2_coeff_151
  recurrence5A2_coeff_152
  recurrence5A2_coeff_153
  recurrence5A2_coeff_154
  recurrence5A2_coeff_155
  recurrence5A2_coeff_156
  recurrence5A2_coeff_157
  recurrence5A2_coeff_158
  recurrence5A2_coeff_159
  recurrence5A2_coeff_160
  recurrence5A2_coeff_161
  recurrence5A2_coeff_162
  recurrence5A2_coeff_163
  recurrence5A2_coeff_164
  recurrence5A2_coeff_165
  recurrence5A2_coeff_166
  recurrence5A2_coeff_167
  recurrence5A2_coeff_168

private theorem recurrence5B2A2_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (184 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (184 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_184 :
    recurrence5B2A2.coeff 184 =
      -((((12300755274771914 * 10 ^ 70 +
        0773549778073779754782156440503565832839496730514381348443784341132046) * 10 ^ 70 +
        5202030591022399759534305826521551862384867722740679954276815087900606) * 10 ^ 70 +
        5532253652458754273339951555036255059972869829010510017505298246932055) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 185 = 16 +
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
    rw [show 41 = 2 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_184_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_184_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (185 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (185 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_185 :
    recurrence5B2A2.coeff 185 =
      ((((7986123934412801 * 10 ^ 70 +
        5249809862509781274820046353052095991970048982332784069415133010532798) * 10 ^ 70 +
        2694864182723050885246666739863689537466730212519680683835568115200714) * 10 ^ 70 +
        8116051061763147361838889201248450642582697522068413617438387485387956) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 186 = 17 +
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
    rw [show 41 = 1 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_185_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_185_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (186 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (186 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_186 :
    recurrence5B2A2.coeff 186 =
      -((((4876981231128202 * 10 ^ 70 +
        7952229015421207882351175623568758903257908162667346914670316602827589) * 10 ^ 70 +
        6413256610186174375837756533637923218984987949806831955773195847844193) * 10 ^ 70 +
        9066441165026698262478225729809739034994035324907728541086245391697088) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 187 = 18 +
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
  rw [recurrence5B2A2_coeff_186_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_186_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (187 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (187 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_187 :
    recurrence5B2A2.coeff 187 =
      ((((2808416905908046 * 10 ^ 70 +
        8046504023116676255196032412800884678091942562677980129484715740990676) * 10 ^ 70 +
        7416230599115222567201322978879920914665215457437085063373562337025768) * 10 ^ 70 +
        0811081449573121192706320895476252048567168727801157233928413668937047) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 188 = 19 +
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
    rw [show 73 = 31 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_187_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_187_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (188 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (188 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_188 :
    recurrence5B2A2.coeff 188 =
      -((((1523782745061185 * 10 ^ 70 +
        9433752033819035189544732442045598987449626892072162656134198950263142) * 10 ^ 70 +
        1171343845806203372916661914849100038830618295896153527119081972415592) * 10 ^ 70 +
        5968915934789675641199844395496615101097762621006015636170615901357522) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 189 = 20 +
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
    rw [show 73 = 30 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_188_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_188_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (189 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (189 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_189 :
    recurrence5B2A2.coeff 189 =
      ((((775373658596855 * 10 ^ 70 +
        9911840754142006586886974561506533734936350496948348734126450448534224) * 10 ^ 70 +
        4879065328683247276595111058831938366689665278414041016531213929449175) * 10 ^ 70 +
        3024824872050628420569710902336750971768625429696690718100555454605231) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 190 = 21 +
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
    rw [show 73 = 29 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_189_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_189_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (190 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (190 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_190 :
    recurrence5B2A2.coeff 190 =
      -((((366045271063706 * 10 ^ 70 +
        5301614061242744641284347227785795795761830507644429864571573338555997) * 10 ^ 70 +
        1840970003739199195163098367878677565943049849155421751501237048622024) * 10 ^ 70 +
        1623091265252511717082588382661612775268510260197174332731456574732715) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 191 = 22 +
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
    rw [show 73 = 28 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_190_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_190_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (191 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (191 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_191 :
    recurrence5B2A2.coeff 191 =
      ((((156620874784390 * 10 ^ 70 +
        9016221990547509264601205227270591153530240910975066833534297209985692) * 10 ^ 70 +
        9710033654988713955934391982885375041136464949505724803401496844429839) * 10 ^ 70 +
        9159442614766484171980632079913036591655392104515898400354267888491316) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 192 = 23 +
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
    rw [show 73 = 27 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_191_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_191_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (192 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (192 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_192 :
    recurrence5B2A2.coeff 192 =
      -((((57372470679003 * 10 ^ 70 +
        2416168296729820651261964451492616813862137978036865452076478162617708) * 10 ^ 70 +
        6545817133343137779682736355570759697194100980928270331156407461049928) * 10 ^ 70 +
        5960830632825832706977038240657468728869755955259101914024984417061622) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 193 = 24 +
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
    rw [show 73 = 26 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_192_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_192_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (193 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (193 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_193 :
    recurrence5B2A2.coeff 193 =
      ((((14762980637724 * 10 ^ 70 +
        3343713799975189522870451094830888685915520098866014317899625181742772) * 10 ^ 70 +
        3520011419676396833255028866702593349702310952128460126895806051360532) * 10 ^ 70 +
        1477783399893821138148406162745441194795509132802560732893089187053387) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 194 = 25 +
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
    rw [show 73 = 25 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_193_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_193_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (194 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (194 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_194 :
    recurrence5B2A2.coeff 194 =
      ((((926838118679 * 10 ^ 70 +
        1621674819103230374755103664286570166602661395866507812698649584654396) * 10 ^ 70 +
        9584923818633413829397011021871893820681356701189292774437247383289234) * 10 ^ 70 +
        2342079103814933796231213413454027666060723892955486915028822046658859) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 195 = 26 +
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
    rw [show 73 = 24 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_194_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_194_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (195 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (195 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_195 :
    recurrence5B2A2.coeff 195 =
      -((((5035049523063 * 10 ^ 70 +
        1474860024413424603842087335248576294967666574590648883891570087915775) * 10 ^ 70 +
        7318264782397813862634219158046881375015279347019878261005697325216254) * 10 ^ 70 +
        2168828615133992396623799194597021793467863711219934040543346736411148) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 196 = 27 +
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
    rw [show 73 = 23 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_195_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_195_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (196 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (196 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_196 :
    recurrence5B2A2.coeff 196 =
      ((((4864820857674 * 10 ^ 70 +
        6327304163678910930840768752712778830569294996242874437043771817210953) * 10 ^ 70 +
        0339621201133139452459554971700744231942362263220073707047708715924132) * 10 ^ 70 +
        5802156161962280106284987662071833217422306685595531125214208915501995) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 197 = 28 +
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
    rw [show 73 = 22 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_196_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_196_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (197 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (197 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_197 :
    recurrence5B2A2.coeff 197 =
      -((((3560575761375 * 10 ^ 70 +
        7545061087900235785769878228088506705780721327117179384816418173367554) * 10 ^ 70 +
        4205044426375571952654741274067606809630762956620856171555515715847019) * 10 ^ 70 +
        4791365462502584151467692514997027856711436046255517712090669019800738) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 198 = 29 +
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
    rw [show 73 = 21 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_197_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_197_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (198 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (198 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_198 :
    recurrence5B2A2.coeff 198 =
      ((((2285443885359 * 10 ^ 70 +
        1762474966093986580299110903944119314328033123873830611305258297268661) * 10 ^ 70 +
        4233497518293514374722219822122315830883016332722816895649629014807353) * 10 ^ 70 +
        0382675709912755159841400163228343243188582750891626305187140171034073) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 199 = 30 +
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
    rw [show 73 = 20 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_198_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_198_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (199 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (199 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_199 :
    recurrence5B2A2.coeff 199 =
      -((((1350066374832 * 10 ^ 70 +
        7672537792436582192859047736791132790271442941319577955045291634721438) * 10 ^ 70 +
        0157784987479396921611796024843090884561934548619849347534723239275373) * 10 ^ 70 +
        8670323835419176116819483478678153409717478082524861330173415916333374) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 200 = 31 +
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
    rw [show 73 = 19 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_199_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_199_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (200 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (200 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_200 :
    recurrence5B2A2.coeff 200 =
      ((((749922265896 * 10 ^ 70 +
        9783972970695111304254912848725586565197430397697088562423816467998835) * 10 ^ 70 +
        0520111662090799646391436188744130063445416488685685217166503441227861) * 10 ^ 70 +
        6409720475696111438985726455109617124958214022755972043675781487353178) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 201 = 32 +
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
    rw [show 73 = 18 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_200_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_200_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (201 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (201 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_201 :
    recurrence5B2A2.coeff 201 =
      -((((396021321552 * 10 ^ 70 +
        1624090457182165553956083876418317270398298034044260263432844285826823) * 10 ^ 70 +
        2794185737729759182602568941460854706630484735302649805436241223177686) * 10 ^ 70 +
        6659572754505534257571857390359795994730261625917042633039003725318669) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 202 = 33 +
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
    rw [show 73 = 17 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_201_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_201_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (202 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (202 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_202 :
    recurrence5B2A2.coeff 202 =
      ((((199990934371 * 10 ^ 70 +
        8579816350872286951759798621605796316406549031729708043528874202864449) * 10 ^ 70 +
        4745833928512846770010525194796090749784892284005732015871147316829103) * 10 ^ 70 +
        0023867833522789702960292143609296208705288693823292634757039171965696) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 203 = 34 +
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
    rw [show 73 = 16 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_202_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_202_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (203 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (203 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_203 :
    recurrence5B2A2.coeff 203 =
      -((((96882200578 * 10 ^ 70 +
        1588918730944041244007279853872088409822822109015258322463977767522818) * 10 ^ 70 +
        7883769683144272853536884451595000466664655094818719675143105915046049) * 10 ^ 70 +
        8021148991779649773642155302913710018949845551588333108232548742923743) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 204 = 35 +
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
    rw [show 73 = 15 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_203_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_203_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (204 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (204 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_204 :
    recurrence5B2A2.coeff 204 =
      ((((45095998087 * 10 ^ 70 +
        0654748396423518033346466196690611842800797616266267939186082308904772) * 10 ^ 70 +
        5499466148741165790830781361562348614372183599587019800247887846757014) * 10 ^ 70 +
        7612416783437328958204734009797349341006926232938132145353026717908192) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 205 = 36 +
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
    rw [show 73 = 14 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_204_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_204_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (205 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (205 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_205 :
    recurrence5B2A2.coeff 205 =
      -((((20193090205 * 10 ^ 70 +
        9208895522717874912979048111147950454846780190784841966338988894897220) * 10 ^ 70 +
        5869393619631180568804511301295304792567301628614154239290395106369332) * 10 ^ 70 +
        7049003293205371672248278203885701581168037793485604457247946827500219) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 206 = 37 +
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
    rw [show 73 = 13 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_205_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_205_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (206 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (206 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_206 :
    recurrence5B2A2.coeff 206 =
      ((((8713958196 * 10 ^ 70 +
        0581956740052625359952754917729140405485645055254408877398505563101758) * 10 ^ 70 +
        2173552878437949450461707740018559338921840817261889034886811208629170) * 10 ^ 70 +
        8126957807415872661385241445718514604885262727524511206037522136101982) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 207 = 38 +
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
    rw [show 73 = 12 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_206_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_206_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (207 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (207 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_207 :
    recurrence5B2A2.coeff 207 =
      -((((3638451110 * 10 ^ 70 +
        3819455266539707516798397339704652339835330941538523877611180433967520) * 10 ^ 70 +
        6992410071625239835097269615894249924302758316029008937250565493234207) * 10 ^ 70 +
        8686810411685391803559347850045438520959714540909637903155528682198568) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 208 = 39 +
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
    rw [show 73 = 11 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_207_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_207_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (208 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (208 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_208 :
    recurrence5B2A2.coeff 208 =
      ((((1482901119 * 10 ^ 70 +
        5137307402736299368543665082945612562626578471194868887241116199479477) * 10 ^ 70 +
        2052603951684510479126473946245244916554986996681441003194127260621842) * 10 ^ 70 +
        7816264802055906542050791941865869239166911129980050116987879370630395) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 209 = 40 +
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
    rw [show 73 = 10 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_208_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_208_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (209 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (209 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_209 :
    recurrence5B2A2.coeff 209 =
      -((((600059408 * 10 ^ 70 +
        5848271850398435053496476615168691271615181726817267632813999624266358) * 10 ^ 70 +
        0297701987511513011579325393703619461875905110675277256845053283412505) * 10 ^ 70 +
        5246642838529942840676069711941935529813903246094526564449316495341999) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 210 = 41 +
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
    rw [show 73 = 9 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_209_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_209_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (210 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (210 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_210 :
    recurrence5B2A2.coeff 210 =
      ((((247885641 * 10 ^ 70 +
        9047867546805332994879224618090751018174572422910416851581088829199894) * 10 ^ 70 +
        2961797582109563226375258582845993096419924721730301369008603848163704) * 10 ^ 70 +
        4672558445610376012476183600778930013102150244791162591336273626174565) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 211 = 42 +
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
    rw [show 73 = 8 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_210_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_210_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (211 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (211 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_211 :
    recurrence5B2A2.coeff 211 =
      -((((108198585 * 10 ^ 70 +
        4003513648956427930146443826751983978189205376952784381040250050419839) * 10 ^ 70 +
        8475569976969962023767348878010026922573292061324912730316205389774537) * 10 ^ 70 +
        3388779969689048403539736180439595049427997443686813936792304393693873) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 212 = 43 +
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
    rw [show 73 = 7 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_211_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_211_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (212 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (212 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_212 :
    recurrence5B2A2.coeff 212 =
      ((((51140293 * 10 ^ 70 +
        4149118097948932432832327017549686514277583219826746698516741339361305) * 10 ^ 70 +
        3368086344791214124663446929677417781867886641075176839108901477476686) * 10 ^ 70 +
        6989496318166930397895778822350987147682781117119296155799576475318553) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 213 = 44 +
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
    rw [show 73 = 6 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_212_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_212_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (213 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (213 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_213 :
    recurrence5B2A2.coeff 213 =
      -((((26093137 * 10 ^ 70 +
        8028767684640936788405204868071664462923179748677733855849546993454635) * 10 ^ 70 +
        5927814075767490002579851450062927423310875535901162097919120669935275) * 10 ^ 70 +
        8882754949640865374790576925316127938909058233172508967894973067251441) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 214 = 45 +
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
    rw [show 73 = 5 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_213_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_213_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (214 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (214 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_214 :
    recurrence5B2A2.coeff 214 =
      ((((13972647 * 10 ^ 70 +
        3331651994033822976802760675330865757762094294773313530415375763413547) * 10 ^ 70 +
        1576685413445754622211718820879015842857802038321700159529143876460966) * 10 ^ 70 +
        7225603812760674547331437989580047148200499731917196846175080924964609) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 215 = 46 +
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
    rw [show 73 = 4 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_214_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_214_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (215 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (215 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_215 :
    recurrence5B2A2.coeff 215 =
      -((((7591928 * 10 ^ 70 +
        9112224572006329232883775314492392905557961267431999048466133774639442) * 10 ^ 70 +
        2988904043615760646735377572415698823299100763830011049508520295902461) * 10 ^ 70 +
        1420432701814508840683762637050945521920433467329862011379611187404063) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 216 = 47 +
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
    rw [show 73 = 3 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_215_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_215_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (216 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (216 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_216 :
    recurrence5B2A2.coeff 216 =
      ((((4080720 * 10 ^ 70 +
        4635169006861128124330566316879262231981660277696960630579444277720180) * 10 ^ 70 +
        9957254030079069876849123707152713540184228442859854050941780808763342) * 10 ^ 70 +
        8535979515447568265146109180827767383075720355937129235507743509529618) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 217 = 48 +
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
    rw [show 73 = 2 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_216_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_216_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (217 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (217 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_217 :
    recurrence5B2A2.coeff 217 =
      -((((2138209 * 10 ^ 70 +
        9650294636940918179219992111564715796039557231636253725608273810935978) * 10 ^ 70 +
        9244322056940981662461603325221450532174962909634222414764452769423703) * 10 ^ 70 +
        1199027910198775580765507764122974548575544959341441737257852466537079) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 218 = 49 +
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
    rw [show 73 = 1 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence5B2A2_coeff_217_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_217_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5B2A2_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder6Coefficient2.coeff x * remainder5Coefficient2.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A2_coeff_high (218 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5B2A2_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder6Coefficient2.coeff (146 + x) *
        remainder5Coefficient2.coeff (218 - (146 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2_coeff_high (146 + x) (by omega)]
  norm_num

theorem recurrence5B2A2_coeff_218 :
    recurrence5B2A2.coeff 218 =
      ((((1084478 * 10 ^ 70 +
        8390634276571582110446119613246659977137250091826670798989827898350256) * 10 ^ 70 +
        0601515074645328491605291287255157739805954603256811799323215994006974) * 10 ^ 70 +
        2851893576141108519636235154487074467623267124670294770444037193121103) : ℚ) := by
  unfold recurrence5B2A2
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 219 = 50 +
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
  rw [recurrence5B2A2_coeff_218_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5B2A2_coeff_218_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

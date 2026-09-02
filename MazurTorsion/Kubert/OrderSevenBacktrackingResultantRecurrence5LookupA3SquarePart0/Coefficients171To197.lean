/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA3SquarePart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: A3Square coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
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

attribute [local simp]
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

attribute [local simp]
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

private theorem recurrence5A3Square_coeff_171_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (171 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (171 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (171 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_171 :
    recurrence5A3Square.coeff 171 =
      (((45414444956533158455779373736567845608226336209056793012278886942 * 10 ^ 70 +
        9632146029959315114680679517444604917678977877426118513304142852704316) * 10 ^ 70 +
        5227861124245574758038502023845617505954395542301272023543523739028134) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 172 = 7 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 30 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_171_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_171_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_172_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (172 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (172 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (172 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_172 :
    recurrence5A3Square.coeff 172 =
      (((22525141907092053402660785404837884414702147497527944229781793785 * 10 ^ 70 +
        2781251723554891782971941667065372558159640463091428321097514245344798) * 10 ^ 70 +
        5088502037912418898041588740546418888968234756701526725671330262005091) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 173 = 8 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 29 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_172_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_172_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (173 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (173 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_173 :
    recurrence5A3Square.coeff 173 =
      -(((66618530425766791120096630457718427015145937217432369863819838718 * 10 ^ 70 +
        0568300084663008477477473782740142429702956664141804932507035729263011) * 10 ^ 70 +
        8287016987060671877834712397837658609497092728773177944333754258094820) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 174 = 9 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 28 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_173_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_173_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (174 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (174 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_174 :
    recurrence5A3Square.coeff 174 =
      (((90144666026527989555547934906854821629906272996804774247712167623 * 10 ^ 70 +
        7377597772058183663756238623445306127050336719688241354398404899590317) * 10 ^ 70 +
        9416248525240046521788102760107513287662533128250054818554445442139610) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 175 = 10 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 27 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_174_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_174_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (175 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (175 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_175 :
    recurrence5A3Square.coeff 175 =
      -(((97594312156446209732460989547409350471316446003993429131655522930 * 10 ^ 70 +
        8981142330140553183985689988790996516192936106800456577968528967899750) * 10 ^ 70 +
        3422688766371698016709815840315038351680222914821601431695642674504620) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 176 = 11 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 26 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_175_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_175_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (176 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (176 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_176 :
    recurrence5A3Square.coeff 176 =
      (((93759782940891402868351736704197845356217844441083034948706090488 * 10 ^ 70 +
        8051900139711289180750271005753135322628529208618899162247437208663651) * 10 ^ 70 +
        8031567490954005926602621140571084329282287679205930833728927155261302) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 177 = 12 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 25 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_176_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_176_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (177 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (177 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_177 :
    recurrence5A3Square.coeff 177 =
      -(((83053442329299933801673203942571470787989281113116832495944316625 * 10 ^ 70 +
        8334350170688637862291087110891419166067341792611353068167534880874709) * 10 ^ 70 +
        8835811249583853969454141105501540267518695912076035997721606793564330) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 178 = 13 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 24 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_177_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_177_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (178 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (178 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_178 :
    recurrence5A3Square.coeff 178 =
      (((69092074754004621748465050817926119887220607789414352059075923005 * 10 ^ 70 +
        2368994417668275352121844554854229628161654927558325266482513165496862) * 10 ^ 70 +
        7635385671048378620263788784989540224792898139681290424382888503457227) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 179 = 14 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 23 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_178_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_178_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (179 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (179 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_179 :
    recurrence5A3Square.coeff 179 =
      -(((54527662505134348048755481403345343475135112273963252246306297071 * 10 ^ 70 +
        5867139428658354816568186691845009164464602107855429120716645338990863) * 10 ^ 70 +
        0841060017061043969902944023637287700582006812569890751776800048224854) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 180 = 15 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 22 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_179_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_179_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (180 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (180 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_180 :
    recurrence5A3Square.coeff 180 =
      (((41069334904829665223429420691885354147690383822646332439204146434 * 10 ^ 70 +
        1274583547075494602820521096612911775918549939854693055255903553532871) * 10 ^ 70 +
        7974908353985676960792199046252432258208517452186321151587928736623548) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 181 = 16 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 21 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_180_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_180_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (181 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (181 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_181 :
    recurrence5A3Square.coeff 181 =
      -(((29627179825165827780785859958084825598820914877394685035577634931 * 10 ^ 70 +
        1141340996096814057190369508276311840812290425131973919232863150188079) * 10 ^ 70 +
        0203531675740674464201093523288140401920010244632339135525187422967060) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 182 = 17 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 20 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_181_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_181_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (182 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (182 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_182 :
    recurrence5A3Square.coeff 182 =
      (((20512082050075401465402704132563630919865096411408404633327304953 * 10 ^ 70 +
        5894315194534747975228346261928155999066676801706866216765034148423815) * 10 ^ 70 +
        2754633670650918571360208115167007003605698661644078046836031472048544) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 183 = 18 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 19 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_182_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_182_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (183 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (183 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_183 :
    recurrence5A3Square.coeff 183 =
      -(((13640151924655458478605124992121883098498735849394152004177450278 * 10 ^ 70 +
        1108969284404221450689836428488261314845148372916771293560357675034849) * 10 ^ 70 +
        4384541785221592780803345029984723074298410898124611286738801400584026) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 184 = 19 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 18 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_183_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_183_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (184 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (184 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_184 :
    recurrence5A3Square.coeff 184 =
      (((8708899677694449368390884871933188124987861981658393337181060605 * 10 ^ 70 +
        0671706148296579093767836037980950247935637062337371194964556646093085) * 10 ^ 70 +
        2026697372434093491869433423960042365947375907117122480119527763686449) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 185 = 20 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 17 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_184_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_184_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (185 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (185 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_185 :
    recurrence5A3Square.coeff 185 =
      -(((5329857611244955750094269894261024700221815681923578375374932014 * 10 ^ 70 +
        2445288203463178085755156069027111210561443759377683743548472495428993) * 10 ^ 70 +
        1946982518501859720299883256776095169405118614131255081120456674979630) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 186 = 21 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 16 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_185_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_185_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (186 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (186 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_186 :
    recurrence5A3Square.coeff 186 =
      (((3115781803338343378749910981530944617448471166692068149122411109 * 10 ^ 70 +
        5542822601127559208601321230759416156987576400403077751850073233040472) * 10 ^ 70 +
        2672809582429015881171832469266087244673885081700007448448922546660769) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 187 = 22 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 15 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_186_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_186_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (187 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (187 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_187 :
    recurrence5A3Square.coeff 187 =
      -(((1728864879779653182642533572085641520282383296963250946203179442 * 10 ^ 70 +
        1196052238766766462240552552642168425120683034872981813696319288138777) * 10 ^ 70 +
        6185499813309192304744914537940610880819968339474682645488020591615410) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 188 = 23 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 14 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_187_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_187_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (188 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (188 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_188 :
    recurrence5A3Square.coeff 188 =
      (((900039877845548416690007908005419183714681244503497258028229643 * 10 ^ 70 +
        1163526285230190291330789993758878015690936697130327572284210549262924) * 10 ^ 70 +
        6721404678688055428925964799154507652240406217152833519762210848584983) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 189 = 24 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 13 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_188_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_188_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (189 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (189 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_189 :
    recurrence5A3Square.coeff 189 =
      -(((429712233199633839991567293363439365139532470445696674062340781 * 10 ^ 70 +
        1266080421415402396014443132396550435974585103110738532959311604829995) * 10 ^ 70 +
        5488963517010354888201163563854527455213849092513384386559782951416072) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 190 = 25 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 12 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_189_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_189_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (190 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (190 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_190 :
    recurrence5A3Square.coeff 190 =
      (((178554888260308744798605351965166093713191465780846669387654255 * 10 ^ 70 +
        1932855898491804881767894909025224494921709035648160131941557785913763) * 10 ^ 70 +
        3081809341175198990974473162624653973840552685051314099683159627887249) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 191 = 26 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 11 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_190_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_190_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (191 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (191 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_191 :
    recurrence5A3Square.coeff 191 =
      -(((54550356320818597438313412533021651033068850470973022003055685 * 10 ^ 70 +
        6851165584780857508574054735426056336397454108972425173765766917419896) * 10 ^ 70 +
        2592832681028403285712879691308962779731925453896005595910323154106704) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 192 = 27 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 10 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_191_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_191_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (192 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (192 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_192 :
    recurrence5A3Square.coeff 192 =
      (((79947986079124818781411508187643733264007354146059326235826 * 10 ^ 70 +
        8788641382508637812167172088113913542853935351261498657428237994829208) * 10 ^ 70 +
        8383355844330055557577817296688410381994863836563461300715694302074870) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 193 = 28 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 9 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_192_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_192_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (193 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (193 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_193 :
    recurrence5A3Square.coeff 193 =
      (((19033585229871521603635727455854202438437269180620431995229184 * 10 ^ 70 +
        6887226835084185243990397228568769895764039907375549617772294725447126) * 10 ^ 70 +
        7733711428957881454155092267570076416130860253939500444169016806327422) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 194 = 29 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 8 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_193_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_193_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (194 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (194 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_194 :
    recurrence5A3Square.coeff 194 =
      -(((21908149269648278913052561826394292426415896710593631842298270 * 10 ^ 70 +
        7565396811212562719419877134326117000322586212972673598492327025181976) * 10 ^ 70 +
        9220873766674773731400734255703854588622606299268753445166094278595146) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 195 = 30 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 7 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_194_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_194_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (195 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (195 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_195 :
    recurrence5A3Square.coeff 195 =
      (((18525154999457191607976867945439538629780998034019553937159367 * 10 ^ 70 +
        3399246308375386732823591470794107201397977864713150157160542741290606) * 10 ^ 70 +
        0541550666544015390877695442926669895765494946888180752712087473334776) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 196 = 31 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 6 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_195_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_195_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (196 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (196 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_196 :
    recurrence5A3Square.coeff 196 =
      -(((13642155493564864168801327951141252711060597176702372943301745 * 10 ^ 70 +
        1372836877418335030369345481056357285541438473873664775315050696012610) * 10 ^ 70 +
        8428952499319725181187355720474458726530280358329790169220372948614205) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 197 = 32 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 5 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_196_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_196_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5A3Square_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (197 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5A3Square_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (197 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A3_coeff_high (165 + x) (by omega)]
  norm_num

theorem recurrence5A3Square_coeff_197 :
    recurrence5A3Square.coeff 197 =
      (((9222556739430457217591477642043334320190993912415588673929429 * 10 ^ 70 +
        8761117695608078945469975531605396282759945780590815082813037157635986) * 10 ^ 70 +
        8110621472275898222800497071759086378856074107190639038055011012874822) : ℚ) := by
  unfold recurrence5A3Square
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 198 = 33 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 4 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence5A3Square_coeff_197_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5A3Square_coeff_197_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

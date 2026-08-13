/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquarePart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: LeadingSquare coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4B3_coeff_0
  recurrence4B3_coeff_1
  recurrence4B3_coeff_10
  recurrence4B3_coeff_100
  recurrence4B3_coeff_101
  recurrence4B3_coeff_102
  recurrence4B3_coeff_103
  recurrence4B3_coeff_104
  recurrence4B3_coeff_105
  recurrence4B3_coeff_106
  recurrence4B3_coeff_107
  recurrence4B3_coeff_108
  recurrence4B3_coeff_109
  recurrence4B3_coeff_11
  recurrence4B3_coeff_110
  recurrence4B3_coeff_111
  recurrence4B3_coeff_112
  recurrence4B3_coeff_113
  recurrence4B3_coeff_114
  recurrence4B3_coeff_115
  recurrence4B3_coeff_116
  recurrence4B3_coeff_117
  recurrence4B3_coeff_118
  recurrence4B3_coeff_119
  recurrence4B3_coeff_12
  recurrence4B3_coeff_120
  recurrence4B3_coeff_121
  recurrence4B3_coeff_122
  recurrence4B3_coeff_123
  recurrence4B3_coeff_124
  recurrence4B3_coeff_125
  recurrence4B3_coeff_126
  recurrence4B3_coeff_127
  recurrence4B3_coeff_128
  recurrence4B3_coeff_129
  recurrence4B3_coeff_13
  recurrence4B3_coeff_130
  recurrence4B3_coeff_131
  recurrence4B3_coeff_132
  recurrence4B3_coeff_133
  recurrence4B3_coeff_134
  recurrence4B3_coeff_135
  recurrence4B3_coeff_136
  recurrence4B3_coeff_137
  recurrence4B3_coeff_138
  recurrence4B3_coeff_139
  recurrence4B3_coeff_14
  recurrence4B3_coeff_140
  recurrence4B3_coeff_141
  recurrence4B3_coeff_142
  recurrence4B3_coeff_143
  recurrence4B3_coeff_144
  recurrence4B3_coeff_145
  recurrence4B3_coeff_146
  recurrence4B3_coeff_147
  recurrence4B3_coeff_148
  recurrence4B3_coeff_149
  recurrence4B3_coeff_15
  recurrence4B3_coeff_150
  recurrence4B3_coeff_151
  recurrence4B3_coeff_152
  recurrence4B3_coeff_153
  recurrence4B3_coeff_154
  recurrence4B3_coeff_155

attribute [local simp]
  recurrence4B3_coeff_156
  recurrence4B3_coeff_157
  recurrence4B3_coeff_158
  recurrence4B3_coeff_159
  recurrence4B3_coeff_16
  recurrence4B3_coeff_160
  recurrence4B3_coeff_161
  recurrence4B3_coeff_162
  recurrence4B3_coeff_163
  recurrence4B3_coeff_164
  recurrence4B3_coeff_17
  recurrence4B3_coeff_18
  recurrence4B3_coeff_19
  recurrence4B3_coeff_2
  recurrence4B3_coeff_20
  recurrence4B3_coeff_21
  recurrence4B3_coeff_22
  recurrence4B3_coeff_23
  recurrence4B3_coeff_24
  recurrence4B3_coeff_25
  recurrence4B3_coeff_26
  recurrence4B3_coeff_27
  recurrence4B3_coeff_28
  recurrence4B3_coeff_29
  recurrence4B3_coeff_3
  recurrence4B3_coeff_30
  recurrence4B3_coeff_31
  recurrence4B3_coeff_32
  recurrence4B3_coeff_33
  recurrence4B3_coeff_34
  recurrence4B3_coeff_35
  recurrence4B3_coeff_36
  recurrence4B3_coeff_37
  recurrence4B3_coeff_38
  recurrence4B3_coeff_39
  recurrence4B3_coeff_4
  recurrence4B3_coeff_40
  recurrence4B3_coeff_41
  recurrence4B3_coeff_42
  recurrence4B3_coeff_43
  recurrence4B3_coeff_44
  recurrence4B3_coeff_45
  recurrence4B3_coeff_46
  recurrence4B3_coeff_47
  recurrence4B3_coeff_48
  recurrence4B3_coeff_49
  recurrence4B3_coeff_5
  recurrence4B3_coeff_50
  recurrence4B3_coeff_51
  recurrence4B3_coeff_52
  recurrence4B3_coeff_53
  recurrence4B3_coeff_54
  recurrence4B3_coeff_55
  recurrence4B3_coeff_56
  recurrence4B3_coeff_57
  recurrence4B3_coeff_58
  recurrence4B3_coeff_59
  recurrence4B3_coeff_6
  recurrence4B3_coeff_60
  recurrence4B3_coeff_61
  recurrence4B3_coeff_62
  recurrence4B3_coeff_63
  recurrence4B3_coeff_64
  recurrence4B3_coeff_65

attribute [local simp]
  recurrence4B3_coeff_66
  recurrence4B3_coeff_67
  recurrence4B3_coeff_68
  recurrence4B3_coeff_69
  recurrence4B3_coeff_7
  recurrence4B3_coeff_70
  recurrence4B3_coeff_71
  recurrence4B3_coeff_72
  recurrence4B3_coeff_73
  recurrence4B3_coeff_74
  recurrence4B3_coeff_75
  recurrence4B3_coeff_76
  recurrence4B3_coeff_77
  recurrence4B3_coeff_78
  recurrence4B3_coeff_79
  recurrence4B3_coeff_8
  recurrence4B3_coeff_80
  recurrence4B3_coeff_81
  recurrence4B3_coeff_82
  recurrence4B3_coeff_83
  recurrence4B3_coeff_84
  recurrence4B3_coeff_85
  recurrence4B3_coeff_86
  recurrence4B3_coeff_87
  recurrence4B3_coeff_88
  recurrence4B3_coeff_89
  recurrence4B3_coeff_9
  recurrence4B3_coeff_90
  recurrence4B3_coeff_91
  recurrence4B3_coeff_92
  recurrence4B3_coeff_93
  recurrence4B3_coeff_94
  recurrence4B3_coeff_95
  recurrence4B3_coeff_96
  recurrence4B3_coeff_97
  recurrence4B3_coeff_98
  recurrence4B3_coeff_99

private theorem recurrence4LeadingSquare_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (190 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (190 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_190 :
    recurrence4LeadingSquare.coeff 190 =
      (((178554888260308744798605351965166093713191465780846669387654255 * 10 ^ 70 +
        1932855898491804881767894909025224494921709035648160131941557785913763) * 10 ^ 70 +
        3081809341175198990974473162624653973840552685051314099683159627887249) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 191,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (190 - x)) = _
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
  rw [recurrence4LeadingSquare_coeff_190_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_190_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (191 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (191 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_191 :
    recurrence4LeadingSquare.coeff 191 =
      -(((54550356320818597438313412533021651033068850470973022003055685 * 10 ^ 70 +
        6851165584780857508574054735426056336397454108972425173765766917419896) * 10 ^ 70 +
        2592832681028403285712879691308962779731925453896005595910323154106704) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 192,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (191 - x)) = _
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
  rw [recurrence4LeadingSquare_coeff_191_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_191_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (192 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (192 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_192 :
    recurrence4LeadingSquare.coeff 192 =
      (((79947986079124818781411508187643733264007354146059326235826 * 10 ^ 70 +
        8788641382508637812167172088113913542853935351261498657428237994829208) * 10 ^ 70 +
        8383355844330055557577817296688410381994863836563461300715694302074870) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 193,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (192 - x)) = _
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
  rw [recurrence4LeadingSquare_coeff_192_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_192_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (193 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (193 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_193 :
    recurrence4LeadingSquare.coeff 193 =
      (((19033585229871521603635727455854202438437269180620431995229184 * 10 ^ 70 +
        6887226835084185243990397228568769895764039907375549617772294725447126) * 10 ^ 70 +
        7733711428957881454155092267570076416130860253939500444169016806327422) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 194,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (193 - x)) = _
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
  rw [recurrence4LeadingSquare_coeff_193_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_193_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (194 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (194 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_194 :
    recurrence4LeadingSquare.coeff 194 =
      -(((21908149269648278913052561826394292426415896710593631842298270 * 10 ^ 70 +
        7565396811212562719419877134326117000322586212972673598492327025181976) * 10 ^ 70 +
        9220873766674773731400734255703854588622606299268753445166094278595146) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 195,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (194 - x)) = _
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
  rw [recurrence4LeadingSquare_coeff_194_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_194_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (195 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (195 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_195 :
    recurrence4LeadingSquare.coeff 195 =
      (((18525154999457191607976867945439538629780998034019553937159367 * 10 ^ 70 +
        3399246308375386732823591470794107201397977864713150157160542741290606) * 10 ^ 70 +
        0541550666544015390877695442926669895765494946888180752712087473334776) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 196,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (195 - x)) = _
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
  rw [recurrence4LeadingSquare_coeff_195_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_195_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (196 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (196 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_196 :
    recurrence4LeadingSquare.coeff 196 =
      -(((13642155493564864168801327951141252711060597176702372943301745 * 10 ^ 70 +
        1372836877418335030369345481056357285541438473873664775315050696012610) * 10 ^ 70 +
        8428952499319725181187355720474458726530280358329790169220372948614205) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 197,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (196 - x)) = _
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
  rw [recurrence4LeadingSquare_coeff_196_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_196_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (197 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (197 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_197 :
    recurrence4LeadingSquare.coeff 197 =
      (((9222556739430457217591477642043334320190993912415588673929429 * 10 ^ 70 +
        8761117695608078945469975531605396282759945780590815082813037157635986) * 10 ^ 70 +
        8110621472275898222800497071759086378856074107190639038055011012874822) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 198,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (197 - x)) = _
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
  rw [recurrence4LeadingSquare_coeff_197_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_197_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (198 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (198 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_198 :
    recurrence4LeadingSquare.coeff 198 =
      -(((5854962965970539960692350176768358415929564648006178317720213 * 10 ^ 70 +
        2151694220550362963030388092244548740823084130472979477337000291908761) * 10 ^ 70 +
        5336156219102710445194773345608836187031711829284945181457539884581333) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 199,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (198 - x)) = _
  rw [show 199 = 34 +
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
    rw [show 37 = 3 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_198_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_198_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (199 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (199 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_199 :
    recurrence4LeadingSquare.coeff 199 =
      (((3529650839839117481991085417492177795523181220181161657000982 * 10 ^ 70 +
        3549561976029487334648673230148105351152485047431662457157357290520295) * 10 ^ 70 +
        8400904228185774956077976613627476572191493761961954980054012501116194) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 200,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (199 - x)) = _
  rw [show 200 = 35 +
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
    rw [show 37 = 2 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_199_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_199_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (200 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (200 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_200 :
    recurrence4LeadingSquare.coeff 200 =
      -(((2031425359192790476137600652948868417244070351281947479769261 * 10 ^ 70 +
        3496580799191041603442544040164916236768682212680808682257678932317979) * 10 ^ 70 +
        7519199766932589848777544837018274491704959293867659652336132368579047) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 201,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (200 - x)) = _
  rw [show 201 = 36 +
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
    rw [show 37 = 1 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_200_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_200_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (201 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (201 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_201 :
    recurrence4LeadingSquare.coeff 201 =
      (((1118101446674178105072408813795805097084767864609131291870959 * 10 ^ 70 +
        2718483571752904253766009209419277003658275579916106770685716697832346) * 10 ^ 70 +
        8101380399521506760754572810318784663493725641029629761994161692993156) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 202,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (201 - x)) = _
  rw [show 202 = 37 +
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
  rw [recurrence4LeadingSquare_coeff_201_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_201_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (202 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (202 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_202 :
    recurrence4LeadingSquare.coeff 202 =
      -(((587776085034489181742722704362152415022671325208888741659143 * 10 ^ 70 +
        7407647591709426007324830850478747383931326856565915243108546491158947) * 10 ^ 70 +
        5770382269619844225999035064787523851079132422340502912342917328363400) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 203,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (202 - x)) = _
  rw [show 203 = 38 +
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
    rw [show 69 = 31 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_202_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_202_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (203 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (203 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_203 :
    recurrence4LeadingSquare.coeff 203 =
      (((293724495020284414742646707318533091051348636003840799794347 * 10 ^ 70 +
        0848957046153631202925748598011923816653635632768907748713825389404190) * 10 ^ 70 +
        9587573184102620602297883228382699756718449048510737060829855276623504) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 204,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (203 - x)) = _
  rw [show 204 = 39 +
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
    rw [show 69 = 30 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_203_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_203_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (204 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (204 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_204 :
    recurrence4LeadingSquare.coeff 204 =
      -(((138146235916756014185233960276830315276604659227619718950042 * 10 ^ 70 +
        5621815214009538176359639016930255616691817302773722261190002112407061) * 10 ^ 70 +
        3301498636217317506355315237792281465266561878775536786081262567223106) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 205,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (204 - x)) = _
  rw [show 205 = 40 +
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
    rw [show 69 = 29 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_204_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_204_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (205 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (205 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_205 :
    recurrence4LeadingSquare.coeff 205 =
      (((59931615319374241767326672524370710038306975290437454049528 * 10 ^ 70 +
        7440097757870403308896179313275423597982904468841654785735738144888850) * 10 ^ 70 +
        7760579398933309833241004641828713496709220593672530267603798516292862) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 206,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (205 - x)) = _
  rw [show 206 = 41 +
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
    rw [show 69 = 28 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_205_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_205_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (206 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (206 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_206 :
    recurrence4LeadingSquare.coeff 206 =
      -(((22914586769981557950246554087972311189008050161231720830279 * 10 ^ 70 +
        7926597319396733789269471782790881428292590685695793556198707163180052) * 10 ^ 70 +
        0319661169039109044608324629669152682338070708565897518853734000876014) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 207,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (206 - x)) = _
  rw [show 207 = 42 +
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
    rw [show 69 = 27 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_206_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_206_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (207 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (207 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_207 :
    recurrence4LeadingSquare.coeff 207 =
      (((6731369246930313602685835123634922289792745043722707048388 * 10 ^ 70 +
        0732706282695275527434783660026488741324047999644938363481640863482616) * 10 ^ 70 +
        9749892902928182452770237320994581283328814298508179892579379576435278) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 208,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (207 - x)) = _
  rw [show 208 = 43 +
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
    rw [show 69 = 26 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_207_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_207_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (208 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (208 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_208 :
    recurrence4LeadingSquare.coeff 208 =
      -(((467110432716333619273927970094717356228540193505189280638 * 10 ^ 70 +
        0073280821615806920862195282976508134186585692154920159147302227396376) * 10 ^ 70 +
        0127659044095977391138687251443728738735081071148392406371533227781138) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 209,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (208 - x)) = _
  rw [show 209 = 44 +
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
    rw [show 69 = 25 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_208_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_208_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (209 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (209 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_209 :
    recurrence4LeadingSquare.coeff 209 =
      -(((1429763217149544081871020217819506377314314363194472312655 * 10 ^ 70 +
        2704442104185773581299873302702121986794469920239816070555035238922577) * 10 ^ 70 +
        3161167998444256910652466351806593018932792193090182120058384057647620) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 210,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (209 - x)) = _
  rw [show 210 = 45 +
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
    rw [show 69 = 24 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_209_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_209_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (210 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (210 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_210 :
    recurrence4LeadingSquare.coeff 210 =
      (((1617307332044024782745970452879310057193144124250651412839 * 10 ^ 70 +
        4444739749277732709266995631056153579859771368344941770327622469415568) * 10 ^ 70 +
        6441966623150463089491583774186506059060430442014504040101632580208630) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 211,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (210 - x)) = _
  rw [show 211 = 46 +
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
    rw [show 69 = 23 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_210_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_210_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (211 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (211 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_211 :
    recurrence4LeadingSquare.coeff 211 =
      -(((1273576612115461003392454228112259966788798432688880640597 * 10 ^ 70 +
        6936558912361851468075072141823349206288764675865241186365954613516729) * 10 ^ 70 +
        2714362406862929629431234780658842875655134603132655628125589694632496) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 212,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (211 - x)) = _
  rw [show 212 = 47 +
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
    rw [show 69 = 22 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_211_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_211_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (212 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (212 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_212 :
    recurrence4LeadingSquare.coeff 212 =
      (((864229645484271579707317395321720879462866700144347582286 * 10 ^ 70 +
        5833979170191483996272174138365220131189731496669862554024512242952481) * 10 ^ 70 +
        3831928111162587755099597829505962832883481591195493878552608970892129) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 213,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (212 - x)) = _
  rw [show 213 = 48 +
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
    rw [show 69 = 21 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_212_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_212_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (213 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (213 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_213 :
    recurrence4LeadingSquare.coeff 213 =
      -(((537291077426076647307224153769029499729321498364986281415 * 10 ^ 70 +
        1308785514056070383626003157641489046357813296420328598683772479834389) * 10 ^ 70 +
        7985421111113724447875094722186302111529392023559604933013360383889956) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 214,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (213 - x)) = _
  rw [show 214 = 49 +
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
    rw [show 69 = 20 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_213_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_213_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (214 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (214 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_214 :
    recurrence4LeadingSquare.coeff 214 =
      (((314118366479036277206287405150093316606508846496231224643 * 10 ^ 70 +
        3499099353601243422945060497297648483885625698913192331188199818615048) * 10 ^ 70 +
        2359436178444118264332469906364503507120249635808556086920529378139176) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 215,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (214 - x)) = _
  rw [show 215 = 50 +
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
    rw [show 69 = 19 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_214_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_214_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (215 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (215 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_215 :
    recurrence4LeadingSquare.coeff 215 =
      -(((175012018588993423799011552077475955944490310495376031350 * 10 ^ 70 +
        6273256964686908273041603041432356335896946979170196605165649000144141) * 10 ^ 70 +
        2299682090664432159306488312650284856947184979346659261620976485988898) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 216,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (215 - x)) = _
  rw [show 216 = 51 +
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
    rw [show 69 = 18 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_215_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_215_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4LeadingSquare_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (216 - x) (by
    omega)]
  norm_num

private theorem recurrence4LeadingSquare_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder5Coefficient3.coeff (165 + x) *
        remainder5Coefficient3.coeff (216 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B3_coeff_high (165 + x) (by
    omega)]
  norm_num

theorem recurrence4LeadingSquare_coeff_216 :
    recurrence4LeadingSquare.coeff 216 =
      (((93624237253306707627581667445594295377018896745704616653 * 10 ^ 70 +
        7153373162677362050465416334983490579363535999500776248494433248403253) * 10 ^ 70 +
        8216001819229903372954493649727480499353752440603151321264818795449888) : ℚ) := by
  unfold recurrence4LeadingSquare
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 217,
    remainder5Coefficient3.coeff x * remainder5Coefficient3.coeff (216 - x)) = _
  rw [show 217 = 52 +
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
    rw [show 69 = 17 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence4LeadingSquare_coeff_216_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4LeadingSquare_coeff_216_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate

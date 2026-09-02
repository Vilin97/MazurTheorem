import sympy as sp

r, s = sp.symbols("r s")
ZZ = sp.ZZ


def poly(value):
    return sp.Poly(value, r, s, domain=ZZ)


R = poly(r)
S = poly(s)
A = poly(r - s)
B = poly(s - 1)
C = poly(r * s - 2 * r + 1)
K = poly(r - s**2 + s - 1)
D = poly(r**2 - r * s**3 + 3 * r * s**2 - 4 * r * s + s)
E = poly(r**2 * s - 3 * r**2 + r * s + 3 * r - s**2 - 1)
G = poly(r * s**2 - 3 * r * s + r + s**2)
L = poly(
    r**3 - r**2 * s**4 + 5 * r**2 * s**3 - 9 * r**2 * s**2
    + 4 * r**2 * s - 2 * r**2 - r * s**3 + 6 * r * s**2
    - 3 * r * s + r - s**3
)
J = poly(
    r**3 * s**2 - 4 * r**3 * s + 2 * r**3 + 3 * r**2 * s**2
    + 2 * r**2 * s - 2 * r**2 - r * s**5 + 4 * r * s**4
    - 10 * r * s**3 + 6 * r * s**2 - 3 * r * s + r + s**4
)
T = poly(
    r**2 * s**3 - 5 * r**2 * s**2 + 6 * r**2 * s - r**2
    + r * s**4 - 3 * r * s**3 + 6 * r * s**2 - 7 * r * s + r + s
)
M = poly(
    r**4 * s**3 - 6 * r**4 * s**2 + 9 * r**4 * s - r**4
    + r**3 * s**5 - 7 * r**3 * s**4 + 20 * r**3 * s**3
    - 19 * r**3 * s**2 - 8 * r**3 * s + r**3 + r**2 * s**4
    - 11 * r**2 * s**3 + 28 * r**2 * s**2 + r * s**4
    - 5 * r * s**3 - 8 * r * s**2 + s**4 + s**3 + s**2
)
N = R * A * K**3 - S * C**3 * G
P9 = D**3 * L - R * S * B**3 * G * E**3

F = poly(
    r**10
    + (-s**10 + 17*s**9 - 123*s**8 + 494*s**7 - 1205*s**6
       + 1836*s**5 - 1732*s**4 + 968*s**3 - 294*s**2 + 35*s - 5) * r**9
    + (-6*s**10 + 74*s**9 - 345*s**8 + 690*s**7 - 185*s**6
       - 1659*s**5 + 3051*s**4 - 2320*s**3 + 840*s**2 - 105*s + 10) * r**8
    + (-21*s**10 + 161*s**9 - 351*s**8 - 144*s**7 + 1289*s**6
       - 789*s**5 - 1551*s**4 + 2166*s**3 - 996*s**2 + 126*s - 10) * r**7
    + (s**15 - 18*s**14 + 151*s**13 - 770*s**12 + 2655*s**11
       - 6558*s**10 + 11834*s**9 - 15408*s**8 + 14630*s**7
       - 11195*s**6 + 7227*s**5 - 2441*s**4 - 388*s**3
       + 555*s**2 - 70*s + 5) * r**6
    + (s**15 - 15*s**14 + 90*s**13 - 245*s**12 + 90*s**11
       + 1587*s**10 - 6145*s**9 + 12270*s**8 - 15060*s**7
       + 12520*s**6 - 8214*s**5 + 3660*s**4 - 685*s**3
       - 120*s**2 + 15*s - 1) * r**5
    + (s**15 - 12*s**14 + 48*s**13 - 49*s**12 - 165*s**11
       + 609*s**10 - 433*s**9 - 1623*s**8 + 4299*s**7
       - 4615*s**6 + 3435*s**5 - 1740*s**4 + 455*s**3) * r**4
    + (s**15 - 9*s**14 + 25*s**13 - 35*s**12 + 45*s**11
       - 181*s**10 + 569*s**9 - 705*s**8 + 5*s**7 + 470*s**6
       - 540*s**5 + 340*s**4 - 105*s**3) * r**3
    + (s**15 - 6*s**14 + 21*s**13 - 56*s**12 + 126*s**11
       - 231*s**10 + 266*s**9 - 126*s**8 + 96*s**7 - 91*s**6
       + 75*s**5 - 45*s**4 + 15*s**3) * r**2
    + (6*s**10 - 28*s**9 + 21*s**8 - 15*s**7 + 10*s**6
       - 6*s**5 + 3*s**4 - s**3) * r
    + s**10
)

# This is the cleared Brunault numerator after removing the visibly common
# factor B^2 D^2 E^2 T.  Signs include uNum = -A L T and vNum = -xTwoNum.
H = (
    A**4 * L**4 * T**5 * R**2 * K**6 * M**2 * N**2 * S**2 * C**6 * J**2 * P9**2
    + R**3 * K**9 * M**3 * N**3 * A**3 * L**3 * S * C**3 * J * P9
      * B**2 * D * E**2 * T**5
    - R**2 * K**6 * M**2 * N**2 * A**3 * L**3 * S**2 * C**6 * J**2 * P9**2
      * B * D**2 * E * T**4
    - 3 * R**3 * K**9 * M**3 * N**3 * A**2 * L**2 * S * C**3 * J * P9
      * B**3 * D**3 * E**3 * T**4
    - R**2 * K**6 * M**2 * N**2 * A**2 * L**2 * S**2 * C**6 * J**2 * P9**2
      * B**2 * D**4 * E**2 * T**3
    + 2 * R * K**3 * M * N * A**2 * L**2 * S**3 * C**9 * J**3 * P9**3
      * B * D**5 * E * T**2
    - R**4 * K**12 * M**4 * N**4 * A * L * B**5 * D**4 * E**5 * T**4
    + 4 * R**2 * K**6 * M**2 * N**2 * A * L * S**2 * C**6 * J**2 * P9**2
      * B**3 * D**6 * E**3 * T**2
    + R * K**3 * M * N * A * L * S**3 * C**9 * J**3 * P9**3
      * B**2 * D**7 * E**2 * T
    + A * L * S**4 * C**12 * J**4 * P9**4 * B * D**8 * E
    + R**3 * K**9 * M**3 * N**3 * S * C**3 * J * P9
      * B**5 * D**7 * E**5 * T**2
)

Q, remainder = sp.div(H, F, domain=ZZ)
assert remainder.is_zero
assert Q.degree(r) == 72 and Q.degree(s) == 105

T0 = (
    A**4 * L**4 * T**5 * R**2 * K**6 * M**2 * N**2 * S**2 * C**6
    * J**2 * P9**2
)

X = R * K**3 * M * N
U = A * L
V = S * C**3 * J * P9

POWER_DATA = {
    "X": X,
    "X2": X**2,
    "X3": X**3,
    "X4": X**4,
    "U": U,
    "U2": U**2,
    "U3": U**3,
    "U4": U**4,
    "V": V,
    "V2": V**2,
    "V3": V**3,
    "V4": V**4,
    **{f"B{i}": B**i for i in range(2, 6)},
    **{f"D{i}": D**i for i in range(2, 9)},
    **{f"E{i}": E**i for i in range(2, 6)},
    **{f"T{i}": T**i for i in range(2, 6)},
}

# Primitive-first intermediate tables used only to emit the staged X^4 and
# V^4 certificates.  The generator itself is not part of the checked proof;
# every emitted table is linked to the previous one by a Lean equality.
POWER_DATA.update({
    "X4R": X**3 * R,
    "X4K1": X**3 * R * K,
    "X4K2": X**3 * R * K**2,
    "X4K3": X**3 * R * K**3,
    "X4M": X**3 * R * K**3 * M,
    "V4S": V**3 * S,
    "V4C1": V**3 * S * C,
    "V4C2": V**3 * S * C**2,
    "V4C3": V**3 * S * C**3,
    "V4J": V**3 * S * C**3 * J,
})

X4_M_STAGE = X**3 * R * K**3 * M
V4_J_STAGE = V**3 * S * C**3 * J

POWER_DATA.update({
    "X4NLR": X4_M_STAGE * R,
    "X4NLA": X4_M_STAGE * R * A,
    "X4NLK1": X4_M_STAGE * R * A * K,
    "X4NLK2": X4_M_STAGE * R * A * K**2,
    "X4NLK3": X4_M_STAGE * R * A * K**3,
    "X4NRS": X4_M_STAGE * S,
    "X4NRC1": X4_M_STAGE * S * C,
    "X4NRC2": X4_M_STAGE * S * C**2,
    "X4NRC3": X4_M_STAGE * S * C**3,
    "X4NRG": X4_M_STAGE * S * C**3 * G,
    "V4PLD1": V4_J_STAGE * D,
    "V4PLD2": V4_J_STAGE * D**2,
    "V4PLD3": V4_J_STAGE * D**3,
    "V4PLL": V4_J_STAGE * D**3 * L,
    "V4PRR": V4_J_STAGE * R,
    "V4PRS": V4_J_STAGE * R * S,
    "V4PRB1": V4_J_STAGE * R * S * B,
    "V4PRB2": V4_J_STAGE * R * S * B**2,
    "V4PRB3": V4_J_STAGE * R * S * B**3,
    "V4PRG": V4_J_STAGE * R * S * B**3 * G,
    "V4PRE1": V4_J_STAGE * R * S * B**3 * G * E,
    "V4PRE2": V4_J_STAGE * R * S * B**3 * G * E**2,
    "V4PRE3": V4_J_STAGE * R * S * B**3 * G * E**3,
})


def dense_row(source, index, inner_bound):
    coefficients = [
        int(source.coeff_monomial(r**index * s**j))
        for j in range(inner_bound)
    ]
    while coefficients and coefficients[-1] == 0:
        coefficients.pop()
    return coefficients


def lean_row(source, index, inner_bound):
    values = dense_row(source, index, inner_bound)
    chunks = []
    line = ""
    for value in values:
        text = str(value)
        candidate = text if not line else line + ", " + text
        if len(candidate) > 92:
            chunks.append(line)
            line = text
        else:
            line = candidate
    if line:
        chunks.append(line)
    if not chunks:
        return "[]"
    if len(chunks) == 1:
        return "[" + chunks[0] + "]"
    return "[" + chunks[0] + ",\n    " + ",\n    ".join(chunks[1:]) + "]"


def division_zero_tail_theorem(n, j):
    d = j - 15
    lines = [
        f"private theorem divisionRow{n}_column{j} :",
        "    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData "
        f"{n} {j} =",
        "      windowCoeff (rectangularize 83 121 divisionReducedData) "
        f"{n} {j} := by",
    ]
    if n < 10:
        lines.extend([
            f"  rw [show {j} = {d} + 15 by omega,",
            "    mulCoeffTwo_dropInner_window divisionSutherlandPolynomial",
            f"      divisionQuotientData {n} {d} 15 "
            "divisionSutherland_innerSupport]",
            "  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 "
            f"{n} 15 (by decide) (by omega)]",
        ])
    else:
        outer = n - 10
        lines.extend([
            f"  rw [show {n} = {outer} + 10 by omega, "
            f"show {j} = {d} + 15 by omega,",
            "    mulCoeffTwo_window divisionSutherlandPolynomial "
            "divisionQuotientData",
            f"      {outer} 10 {d} 15",
            "      (by rw [divisionSutherland_outerSupport])",
            "      divisionSutherland_innerSupport]",
            "  rw [mulCoeffTwo_take_drop_outer_split _ _ 5 10 15 "
            "(by decide) (by omega)]",
        ])
    lines.extend([
        "  have hReduced :",
        "      windowCoeff (rectangularize 83 121 divisionReducedData) "
        f"{n} {j} = 0 := by",
        f"    rw [show {j} = {d} + 15 by omega,",
        "      windowCoeff_rectangularize_window 83 121 "
        "divisionReducedData",
        f"        {n} {d} 15 (by omega) (by omega)]",
        "    decide",
        "  rw [hReduced]",
        "  decide",
    ])
    return "\n".join(lines)


def rewrite_division_zero_tails(path):
    import pathlib
    import re

    target = pathlib.Path(path)
    text = target.read_text()
    for n in range(9, 17):
        first_zero = len(dense_row(H, n, 121))
        for j in range(first_zero, 121):
            pattern = re.compile(
                rf"private theorem divisionRow{n}_column{j} :\n.*?"
                rf"(?=\nprivate theorem )",
                re.S,
            )
            text, count = pattern.subn(
                division_zero_tail_theorem(n, j) + "\n", text, count=1
            )
            if count != 1:
                raise RuntimeError(f"expected one theorem for row {n}, column {j}")
    target.write_text(text)


def division_nonzero_scalar_theorem(n, j):
    outer = n - 10
    d = j - 15
    return "\n".join([
        f"private theorem divisionRow{n}_column{j} :",
        "    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData "
        f"{n} {j} =",
        "      windowCoeff (rectangularize 83 121 divisionReducedData) "
        f"{n} {j} := by",
        f"  rw [show {n} = {outer} + 10 by omega, "
        f"show {j} = {d} + 15 by omega,",
        "    mulCoeffTwo_window divisionSutherlandPolynomial "
        "divisionQuotientData",
        f"      {outer} 10 {d} 15",
        "      (by rw [divisionSutherland_outerSupport])",
        "      divisionSutherland_innerSupport]",
        "  decide",
    ])


def division_band_theorem(n, lo, hi):
    outer = n - 10
    lines = [
        f"private theorem divisionRow{n}_columns{lo}To{hi - 1}",
        f"    (j : ℕ) (hLower : {lo} ≤ j) (hUpper : j < {hi}) :",
        "    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData "
        f"{n} j =",
        "      windowCoeff (rectangularize 83 121 divisionReducedData) "
        f"{n} j := by",
    ]
    if lo == 0:
        lines.extend([
            f"  rw [show {n} = {outer} + 10 by omega,",
            "    mulCoeffTwo_outerDrop_window divisionSutherlandPolynomial",
            f"      divisionQuotientData {outer} 10 j",
            "      (by rw [divisionSutherland_outerSupport])]",
        ])
    else:
        lines.extend([
            "  have hSplit : j = (j - 15) + 15 := by omega",
            f"  rw [show {n} = {outer} + 10 by omega, hSplit,",
            "    mulCoeffTwo_window divisionSutherlandPolynomial "
            "divisionQuotientData",
            f"      {outer} 10 (j - 15) 15",
            "      (by rw [divisionSutherland_outerSupport])",
            "      divisionSutherland_innerSupport]",
        ])
    if hi - lo == 1:
        lines.extend(["  interval_cases j", "  decide"])
    else:
        lines.append("  interval_cases j <;> decide")
    return "\n".join(lines)


def division_row_block(n):
    support = len(dense_row(H, n, 121))
    band_limit = min(support, 95)
    bands = []
    for lo in range(0, 95, 15):
        if lo >= band_limit:
            break
        bands.append((lo, min(lo + 15, band_limit)))

    declarations = [division_band_theorem(n, lo, hi) for lo, hi in bands]
    scalar_start = bands[-1][1]
    for j in range(scalar_start, 121):
        if j < support:
            declarations.append(division_nonzero_scalar_theorem(n, j))
        else:
            declarations.append(division_zero_tail_theorem(n, j))

    dispatch = [
        f"private theorem divisionRow{n}_windowCoefficients",
        "    (j : ℕ) (hj : j < 121) :",
        "    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData "
        f"{n} j =",
        "      windowCoeff (rectangularize 83 121 divisionReducedData) "
        f"{n} j := by",
    ]
    for lo, hi in bands:
        dispatch.extend([
            f"  by_cases h{hi} : j < {hi}",
            f"  · exact divisionRow{n}_columns{lo}To{hi - 1} j (by omega) h{hi}",
        ])
    for j in range(scalar_start, 120):
        dispatch.extend([
            f"  by_cases h{j + 1} : j < {j + 1}",
            f"  · have hj{j} : j = {j} := by omega",
            "    subst j",
            f"    exact divisionRow{n}_column{j}",
        ])
    dispatch.extend([
        "  have hj120 : j = 120 := by omega",
        "  subst j",
        f"  exact divisionRow{n}_column120",
    ])

    if n < 21:
        target_support = ["      decide"]
    elif n < 42:
        local = n - 21
        target_support = [
            f"      rw [show {n} = 21 + {local} by omega,",
            "        ← getD_drop_window divisionReducedData 21 "
            f"{local} []]",
            "      change",
            "        ((ReducedDataMidLow ++ ReducedDataMidHigh ++ "
            "ReducedDataHigh).getD",
            f"          {local} []).length ≤ 121",
            "      rw [← getD_drop_window",
            "        (ReducedDataMidLow ++ ReducedDataMidHigh ++ "
            "ReducedDataHigh)",
            f"        {local} 0 []]",
            "      decide",
        ]
    elif n < 63:
        local = n - 42
        target_support = [
            f"      rw [show {n} = 42 + {local} by omega,",
            "        ← getD_drop_window divisionReducedData 42 "
            f"{local} []]",
            "      change",
            "        ((ReducedDataMidHigh ++ ReducedDataHigh).getD",
            f"          {local} []).length ≤ 121",
            "      rw [← getD_drop_window",
            "        (ReducedDataMidHigh ++ ReducedDataHigh) "
            f"{local} 0 []]",
            "      decide",
        ]
    else:
        local = n - 63
        target_support = [
            f"      rw [show {n} = 63 + {local} by omega,",
            "        ← getD_drop_window divisionReducedData 63 "
            f"{local} []]",
            "      change (ReducedDataHigh.getD "
            f"{local} []).length ≤ 121",
            "      rw [← getD_drop_window ReducedDataHigh "
            f"{local} 0 []]",
            "      decide",
        ]

    target_support_declaration = [
        f"private theorem divisionRow{n}_targetSupport :",
        f"    (divisionReducedData.getD {n} []).length ≤ 121 := by",
        *(line[4:] for line in target_support),
    ]

    outer = n - 10
    tail = [
        f"private theorem divisionRow{n}_coefficients (j : ℕ) "
        "(hj : j < 121) :",
        "    mulCoeffTwo divisionSutherlandPolynomial divisionQuotientData "
        f"{n} j =",
        "      ((rectangularize 83 121 divisionReducedData).getD "
        f"{n} []).getD j 0 := by",
        "  rw [← windowCoeff_eq_getD]",
        f"  exact divisionRow{n}_windowCoefficients j hj",
        "",
        *target_support_declaration,
        "",
        f"private theorem divisionRow{n}_spec :",
        "    padOne 121 (mulRow divisionSutherlandPolynomial "
        f"divisionQuotientData {n}) =",
        "      (rectangularize 83 121 divisionReducedData).getD "
        f"{n} [] := by",
        "  apply padOne_mulRow_eq_of_coefficients 121 "
        "divisionSutherlandPolynomial",
        f"    divisionQuotientData {n}",
        "    ((rectangularize 83 121 divisionReducedData).getD "
        f"{n} [])",
        f"  · rw [show {n} = {outer} + 10 by omega,",
        "      mulRow_drop_window divisionSutherlandPolynomial "
        "divisionQuotientData",
        f"        {outer} 10 (by rw [divisionSutherland_outerSupport])]",
        "    decide",
        "  · have hTargetSupport :",
        f"        (divisionReducedData.getD {n} []).length ≤ 121 := by",
        f"      exact divisionRow{n}_targetSupport",
        "    rw [getD_rectangularize 83 121 divisionReducedData "
        f"{n} (by omega)]",
        "    simp only [padOne, List.length_append, List.length_replicate]",
        "    omega",
        f"  · exact divisionRow{n}_coefficients",
    ]
    return "\n\n".join(declarations + ["\n".join(dispatch), "\n".join(tail)])


def generate_division_rows(path, lo, hi, suffix):
    import pathlib

    header = "\n".join([
        "/-",
        "Copyright (c) 2026 Vasily Ilin. All rights reserved.",
        "Released under Apache 2.0 license as described in the file LICENSE.",
        "Authors: Vasily Ilin",
        "-/",
        "",
        "import MazurTorsion.Kubert."
        "OrderTwentyFiveBrunaultRawPolynomialDivisionData",
        "import MazurTorsion.Kubert."
        "OrderTwentyFiveBrunaultRawPolynomialWindow",
        "import Mathlib.Tactic.IntervalCases",
        "",
        "/-!",
        f"# Rows {lo} through {hi - 1} of the raw order-twenty-five "
        "division certificate",
        "",
        "Every finite coefficient is checked through bounded outer and inner "
        "windows.",
        "Padded zero tails additionally split the outer scalar sum into "
        "kernel-checked halves.",
        "-/",
        "",
        "namespace MazurTorsion.Kubert."
        "OrderTwentyFiveRawPolynomialCertificate.Internal",
        "",
        "open OrderTwentyFiveDensePolynomial",
        "open OrderTwentyFiveDensePolynomialRectangular",
        "open OrderTwentyFiveDensePolynomialRowCertificate",
    ])
    blocks = [division_row_block(n) for n in range(lo, hi)]
    facade = [
        f"/-- The complete exact-division certificates for rows {lo} through "
        f"{hi - 1}. -/",
        f"theorem divisionRows{suffix}_spec (n : ℕ)",
        f"    (hLower : {lo} ≤ n) (hUpper : n < {hi}) :",
        "    padOne 121 (mulRow divisionSutherlandPolynomial "
        "divisionQuotientData n) =",
        "      (rectangularize 83 121 divisionReducedData).getD n [] := by",
        "  interval_cases n",
    ]
    facade.extend(f"  · exact divisionRow{n}_spec" for n in range(lo, hi))
    footer = "\n".join([
        "",
        "end MazurTorsion.Kubert."
        "OrderTwentyFiveRawPolynomialCertificate.Internal",
    ])
    output = header + "\n\n" + "\n\n".join(blocks) + "\n\n"
    output += "\n".join(facade) + footer + "\n"
    pathlib.Path(path).write_text(output)


if __name__ == "__main__":
    import sys
    if sys.argv[1] == "REWRITE_DIVISION_ZERO_TAILS":
        rewrite_division_zero_tails(sys.argv[2])
        raise SystemExit(0)
    if sys.argv[1] == "GENERATE_DIVISION_ROWS":
        generate_division_rows(
            sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
        )
        raise SystemExit(0)
    if sys.argv[1] == "BATCH":
        requested = []
        for item in sys.argv[2:]:
            source_name, lo, hi = item.split(":")
            requested.append((source_name, int(lo), int(hi)))
    else:
        requested = [(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]))]
    basic = {
        "Q": (Q, "quotientRow", 106),
        "H": (H, "reducedRow", 121),
        "T0": (T0, "termZeroRow", 121),
    }
    for source_name, lo, hi in requested:
        print(f"@@@BEGIN:{source_name}@@@")
        if source_name in basic:
            source, prefix, inner_bound = basic[source_name]
            assemble = False
        else:
            source = POWER_DATA[source_name]
            prefix = source_name.lower() + "Row"
            inner_bound = source.degree(s) + 1
            assemble = True
        for i in range(lo, hi):
            print(f"def {prefix}{i} : One :=")
            print("  " + lean_row(source, i, inner_bound).replace("\n", "\n  "))
            print()
        if assemble:
            rows = ", ".join(f"{prefix}{i}" for i in range(lo, hi))
            print(f"def {source_name}Data : Two :=")
            print(f"  [{rows}]")
        print(f"@@@END:{source_name}@@@")

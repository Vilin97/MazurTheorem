#!/usr/bin/env python3

from pathlib import Path
import os
import re
import sympy as sp


SOURCE = Path(
    "/data/codex-scratch/MazurTheorem-o25-poly-cert-agent/"
    "MazurTorsion/Kubert/OrderTwentyFiveBrunaultOrbitRelationZeroCertificateData.lean"
)
TEXT = SOURCE.read_text(encoding="utf-8")
r, s = sp.symbols("r s")


def body(name: str) -> str:
    match = re.search(
        rf"(?:private )?def {name} \([^\n]*\) : ℚ :=\n"
        rf"(.*?)(?=\n(?:private )?(?:def|theorem)|\ntheorem )",
        TEXT,
        re.DOTALL,
    )
    if match is None:
        raise RuntimeError(f"definition {name} not found")
    return " ".join(match.group(1).strip().replace("^", "**").split())


def parse(name: str, variables: dict[str, sp.Expr]) -> sp.Expr:
    return sp.expand(eval(body(name), {"__builtins__": {}}, variables))


values: dict[str, sp.Expr] = {"r": r, "s": s}
for name in ("A", "B", "C", "K", "D", "E", "L", "J", "T", "M", "N", "P6", "P9"):
    values[name] = parse(name, values)

A, B, C, K, D, E, L, J, T, M, N, P6_expanded, P9_expanded = (
    values[name]
    for name in ("A", "B", "C", "K", "D", "E", "L", "J", "T", "M", "N", "P6", "P9")
)
G = sp.expand(r * s**2 - 3 * r * s + r + s**2)
P6 = sp.expand(D**2 * A * K - C**2 * s * B * G * E)
P9 = sp.expand(D**3 * L - r * s * B**3 * G * E**3)
assert sp.expand(P6 - P6_expanded) == 0
assert sp.expand(P9 - P9_expanded) == 0

raw_coefficients = [parse(f"rawFC{i}", values) for i in range(11)]
raw_f = sp.Poly(sum(raw_coefficients[i] * r**i for i in range(11)), r, s, domain=sp.QQ)

y1 = C * L * J / (r * B**2 * K**2 * E**2)
y2 = -(r * B**3 * C * K * M) / (A**2 * P6)
y4 = -(r * A * B * K**2 * E * T) / (C * D**2 * J)
y8 = -(A * B * E) / L
y9 = -(K * D * M * N) / (s * A * C**2 * P9)

relation_terms = {
    0: (y1, -y9, -(y1 * y8 * y2), y1**2 * y8),
    2: (y4, -y2, -(y4 * y1 * y8), y4**2 * y1),
    3: (y8, -y4, -(y8 * y2 * y9), y8**2 * y2),
    4: (y9, -y8, -(y9 * y4 * y1), y9**2 * y4),
    5: (y1 * y2 * y4 * y8 * y9, -sp.Integer(1)),
}

base_symbols = {
    name: sp.Symbol(name)
    for name in ("A", "B", "C", "K", "D", "E", "G", "L", "J", "T", "M", "N", "P6", "P9")
}
AS, BS, CS, KS, DS, ES, GS, LS, JS, TS, MS, NS, P6S, P9S = (
    base_symbols[name]
    for name in ("A", "B", "C", "K", "D", "E", "G", "L", "J", "T", "M", "N", "P6", "P9")
)
y1_symbolic = CS * LS * JS / (r * BS**2 * KS**2 * ES**2)
y2_symbolic = -(r * BS**3 * CS * KS * MS) / (AS**2 * P6S)
y4_symbolic = -(r * AS * BS * KS**2 * ES * TS) / (CS * DS**2 * JS)
y8_symbolic = -(AS * BS * ES) / LS
y9_symbolic = -(KS * DS * MS * NS) / (s * AS * CS**2 * P9S)
symbolic_relation_terms = {
    0: (y1_symbolic, -y9_symbolic, -(y1_symbolic * y8_symbolic * y2_symbolic), y1_symbolic**2 * y8_symbolic),
    2: (y4_symbolic, -y2_symbolic, -(y4_symbolic * y1_symbolic * y8_symbolic), y4_symbolic**2 * y1_symbolic),
    3: (y8_symbolic, -y4_symbolic, -(y8_symbolic * y2_symbolic * y9_symbolic), y8_symbolic**2 * y2_symbolic),
    4: (y9_symbolic, -y8_symbolic, -(y9_symbolic * y4_symbolic * y1_symbolic), y9_symbolic**2 * y4_symbolic),
    5: (y1_symbolic * y2_symbolic * y4_symbolic * y8_symbolic * y9_symbolic, -sp.Integer(1)),
}


def poly_terms(expr: sp.Expr, variables=(r, s)):
    return sp.Poly(sp.expand(expr), *variables, domain=sp.QQ).terms()


def lean_monomial(coefficient: sp.Rational, exponents: tuple[int, ...], variables: tuple[str, ...]) -> str:
    coefficient = abs(coefficient)
    factors: list[str] = []
    if coefficient != 1 or not any(exponents):
        factors.append(str(coefficient.p) if coefficient.q == 1 else f"({coefficient.p} / {coefficient.q} : ℚ)")
    for variable, exponent in zip(variables, exponents):
        if exponent == 1:
            factors.append(variable)
        elif exponent > 1:
            factors.append(f"{variable} ^ {exponent}")
    return " * ".join(factors) if factors else "1"


def lean_poly(expr: sp.Expr, variables=(r, s), indent="  ") -> str:
    terms = poly_terms(expr, variables)
    variable_names = tuple(str(variable) for variable in variables)
    if not terms:
        return indent + "0"
    lines: list[str] = []
    for position, (exponents, coefficient) in enumerate(terms):
        sign = "-" if coefficient < 0 else "+"
        monomial = lean_monomial(coefficient, exponents, variable_names)
        if position == 0:
            prefix = "-" if coefficient < 0 else ""
        else:
            prefix = f"{sign} "
        lines.append(indent + prefix + monomial)
    return "\n".join(lines)


def coefficient_list(expr: sp.Expr) -> list[sp.Expr]:
    polynomial = sp.Poly(sp.expand(expr), r, domain=sp.QQ.frac_field(s))
    return [sp.expand(polynomial.nth(i)) for i in range(polynomial.degree() + 1)]


def emit_def(lines: list[str], name: str, args: str, expr: sp.Expr, variables=(r, s)) -> None:
    lines.append(f"private def {name} {args} : ℚ :=")
    lines.append(lean_poly(expr, variables))
    lines.append("")


def unary_args(expr: sp.Expr) -> str:
    return "(s : ℚ)" if s in expr.free_symbols else "(_s : ℚ)"


def binary_args(expr: sp.Expr) -> str:
    r_name = "r" if r in expr.free_symbols else "_r"
    s_name = "s" if s in expr.free_symbols else "_s"
    return f"({r_name} {s_name} : ℚ)"


def lean_symbolic(expr: sp.Expr) -> str:
    result = sp.sstr(sp.factor(expr)).replace("**", " ^ ")
    for name in sorted(base_symbols, key=len, reverse=True):
        result = re.sub(rf"\b{name}\b", f"{name} r s", result)
    result = result.replace("*", " * ").replace("/", " / ")
    result = re.sub(r"\s+", " ", result)
    return result.strip()


def emit_symbolic_def(lines: list[str], name: str, expr: sp.Expr) -> None:
    lines.append(f"private def {name} (r s : ℚ) : ℚ :=")
    lines.append("  " + lean_symbolic(expr))
    lines.append("")


def emit_r_polynomial(lines: list[str], name: str, coeff_prefix: str, degree: int) -> None:
    lines.append(f"private def {name} (r s : ℚ) : ℚ :=")
    summands = []
    for exponent in range(degree, -1, -1):
        base = f"{coeff_prefix}{exponent} s"
        if exponent == 1:
            base += " * r"
        elif exponent > 1:
            base += f" * r ^ {exponent}"
        summands.append(base)
    lines.append("  " + "\n    + ".join(summands))
    lines.append("")


index = int(os.environ.get("YREL_INDEX", "2"))
terms = relation_terms[index]
symbolic_terms = symbolic_relation_terms[index]
relation = sum(terms)
together_numerator, together_denominator = sp.fraction(sp.together(relation))
canceled_numerator, canceled_denominator = sp.fraction(sp.cancel(relation))
candidate_terms = [sp.cancel(canceled_denominator * term) for term in terms]
if all(sp.fraction(term)[1] == 1 for term in candidate_terms):
    common_denominator = canceled_denominator
    cleared_terms = candidate_terms
    certificate_numerator = canceled_numerator
else:
    common_denominator = together_denominator
    cleared_terms = [sp.cancel(common_denominator * term) for term in terms]
    certificate_numerator = together_numerator
quotient, remainder = sp.div(sp.Poly(certificate_numerator, r, s, domain=sp.QQ), raw_f)
assert remainder.is_zero

assert all(sp.fraction(term)[1] == 1 for term in cleared_terms)
assert sp.expand(sum(cleared_terms) - certificate_numerator) == 0

symbolic_denominator = sp.fraction(sp.together(sum(symbolic_terms)))[1]
symbolic_cleared_terms = [sp.cancel(symbolic_denominator * term) for term in symbolic_terms]
assert all(sp.fraction(term)[1] == 1 for term in symbolic_cleared_terms)
symbol_to_expression = {
    AS: A, BS: B, CS: C, KS: K, DS: D, ES: E, GS: G, LS: L,
    JS: J, TS: T, MS: M, NS: N, P6S: P6, P9S: P9,
}
for symbolic_term, cleared_term in zip(symbolic_cleared_terms, cleared_terms):
    assert sp.expand(symbolic_term.subs(symbol_to_expression) - cleared_term) == 0

term_coefficients = [coefficient_list(term) for term in cleared_terms]
numerator_coefficients = coefficient_list(certificate_numerator)
quotient_coefficients = coefficient_list(quotient.as_expr())
target_degree = max(
    max(len(coefficients) - 1 for coefficients in term_coefficients),
    (len(raw_coefficients) - 1) + (len(quotient_coefficients) - 1),
    len(numerator_coefficients) - 1,
)
numerator_coefficients.extend(
    [sp.Integer(0)] * (target_degree + 1 - len(numerator_coefficients))
)

lines = [
    "/- Generated scratch certificate; all declarations are private. -/",
    "import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitCertificate",
    "import Mathlib.Tactic.FieldSimp",
    "import Mathlib.Tactic.LinearCombination",
    "import Mathlib.Tactic.Ring",
    "",
    f"namespace ScratchYRelation{index}",
    "",
]

base_expressions = {
    "A": A,
    "B": B,
    "C": C,
    "K": K,
    "D": D,
    "E": E,
    "G": G,
    "L": L,
    "J": J,
    "T": T,
    "M": M,
    "N": N,
}
for name, expression in base_expressions.items():
    emit_def(lines, name, binary_args(expression), expression)

lines.extend([
    "private def P6 (r s : ℚ) : ℚ :=",
    "  D r s ^ 2 * A r s * K r s -",
    "    C r s ^ 2 * s * B r s * G r s * E r s",
    "",
    "private def P9 (r s : ℚ) : ℚ :=",
    "  D r s ^ 3 * L r s - r * s * B r s ^ 3 * G r s * E r s ^ 3",
    "",
    "private def y1 (r s : ℚ) : ℚ :=",
    "  C r s * L r s * J r s / (r * B r s ^ 2 * K r s ^ 2 * E r s ^ 2)",
    "",
    "private def y2 (r s : ℚ) : ℚ :=",
    "  -(r * B r s ^ 3 * C r s * K r s * M r s) / (A r s ^ 2 * P6 r s)",
    "",
    "private def y4 (r s : ℚ) : ℚ :=",
    "  -(r * A r s * B r s * K r s ^ 2 * E r s * T r s) /",
    "    (C r s * D r s ^ 2 * J r s)",
    "",
    "private def y8 (r s : ℚ) : ℚ :=",
    "  -(A r s * B r s * E r s) / L r s",
    "",
    "private def y9 (r s : ℚ) : ℚ :=",
    "  -(K r s * D r s * M r s * N r s) / (s * A r s * C r s ^ 2 * P9 r s)",
    "",
])

for i, coefficient in enumerate(raw_coefficients):
    emit_def(lines, f"fC{i}", unary_args(coefficient), coefficient, variables=(s,))
emit_r_polynomial(lines, "F", "fC", len(raw_coefficients) - 1)

for term_index, (term, symbolic_term, coefficients) in enumerate(
    zip(cleared_terms, symbolic_cleared_terms, term_coefficients)
):
    emit_symbolic_def(lines, f"term{term_index}", symbolic_term)
    for exponent, coefficient in enumerate(coefficients):
        emit_def(lines, f"term{term_index}C{exponent}", unary_args(coefficient), coefficient, variables=(s,))
    emit_r_polynomial(lines, f"term{term_index}Expanded", f"term{term_index}C", len(coefficients) - 1)
    direct_names = {str(symbol) for symbol in symbolic_term.free_symbols} & set(base_expressions | {"P6": P6, "P9": P9})
    dependency_names = set(direct_names)
    if "P6" in dependency_names:
        dependency_names.update(("A", "B", "C", "K", "D", "E", "G"))
    if "P9" in dependency_names:
        dependency_names.update(("B", "D", "E", "G", "L"))
    simp_names = [f"term{term_index}", f"term{term_index}Expanded"] + [
        f"term{term_index}C{exponent}" for exponent in range(len(coefficients))
    ] + [name for name in list(base_expressions) + ["P6", "P9"] if name in dependency_names]
    lines.extend([
        f"private theorem term{term_index}_expansion (r s : ℚ) :",
        f"    term{term_index} r s = term{term_index}Expanded r s := by",
        "  simp only [" + ", ".join(simp_names) + "]",
        "  ring",
        "",
    ])

for exponent, coefficient in enumerate(numerator_coefficients):
    emit_def(lines, f"nC{exponent}", unary_args(coefficient), coefficient, variables=(s,))
emit_r_polynomial(lines, "numerator", "nC", len(numerator_coefficients) - 1)

for exponent in range(len(numerator_coefficients)):
    summands = [
        f"term{term_index}C{exponent} s"
        for term_index, coefficients in enumerate(term_coefficients)
        if exponent < len(coefficients)
    ]
    lines.extend([
        f"private def lhsC{exponent} (s : ℚ) : ℚ :=",
        f"  {' + '.join(summands)}",
        "",
        f"private theorem lhs_coefficient_{exponent} (s : ℚ) :",
        f"    lhsC{exponent} s = nC{exponent} s := by",
        "  simp only [" + ", ".join(
            [f"lhsC{exponent}"]
            + [f"term{term_index}C{exponent}" for term_index, coefficients in enumerate(term_coefficients) if exponent < len(coefficients)]
            + [f"nC{exponent}"]
        ) + "]",
        "  ring",
        "",
    ])

emit_r_polynomial(lines, "lhs", "lhsC", len(numerator_coefficients) - 1)
term_sum = " + ".join(f"term{i} r s" for i in range(len(terms)))
lines.extend([
    "private theorem terms_eq_lhs (r s : ℚ) :",
    f"    {term_sum} = lhs r s := by",
    "  rw [" + ", ".join(f"term{i}_expansion" for i in range(len(terms))) + "]",
    "  simp only [" + ", ".join(
        [f"term{i}Expanded" for i in range(len(terms))]
        + ["lhs"]
        + [f"lhsC{exponent}" for exponent in range(len(numerator_coefficients))]
    ) + "]",
    "  ring",
    "",
    "private theorem lhs_eq_numerator (r s : ℚ) :",
    "    lhs r s = numerator r s := by",
    "  simp only [lhs, numerator, " + ", ".join(
        f"lhs_coefficient_{exponent}" for exponent in range(len(numerator_coefficients))
    ) + "]",
    "",
    "private theorem terms_eq_numerator (r s : ℚ) :",
    f"    {term_sum} = numerator r s := by",
    "  rw [terms_eq_lhs, lhs_eq_numerator]",
    "",
])

for exponent, coefficient in enumerate(quotient_coefficients):
    emit_def(lines, f"qC{exponent}", unary_args(coefficient), coefficient, variables=(s,))
emit_r_polynomial(lines, "Q", "qC", len(quotient_coefficients) - 1)

convolution_coefficients: list[sp.Expr] = []
for exponent in range(target_degree + 1):
    pairs = [
        (i, exponent - i)
        for i in range(len(raw_coefficients))
        if 0 <= exponent - i < len(quotient_coefficients)
    ]
    convolution = sum(raw_coefficients[i] * quotient_coefficients[j] for i, j in pairs)
    convolution_coefficients.append(sp.expand(convolution))
    pair_expr = " + ".join(f"fC{i} s * qC{j} s" for i, j in pairs) or "0"
    lines.extend([
        f"private def convC{exponent} {'(s : ℚ)' if pairs else '(_s : ℚ)'} : ℚ :=",
        f"  {pair_expr}",
        "",
        f"private theorem conv_coefficient_{exponent} (s : ℚ) :",
        f"    convC{exponent} s = nC{exponent} s := by",
        ("  rfl" if not pairs else "  simp only [" + ", ".join(
            [f"convC{exponent}"]
            + [f"fC{i}" for i, _ in pairs]
            + [f"qC{j}" for _, j in pairs]
            + [f"nC{exponent}"]
        ) + "]"),
        *( [] if not pairs else ["  ring"] ),
        "",
    ])

assert len(convolution_coefficients) == len(numerator_coefficients)
assert all(sp.expand(lhs - rhs) == 0 for lhs, rhs in zip(convolution_coefficients, numerator_coefficients))
emit_r_polynomial(lines, "convolution", "convC", len(convolution_coefficients) - 1)
lines.extend([
    "private theorem F_mul_Q_eq_convolution (r s : ℚ) :",
    "    F r s * Q r s = convolution r s := by",
    "  simp only [F, Q, convolution, " + ", ".join(f"convC{i}" for i in range(len(convolution_coefficients))) + "]",
    "  ring",
    "",
    "private theorem convolution_eq_numerator (r s : ℚ) :",
    "    convolution r s = numerator r s := by",
    "  simp only [convolution, numerator, " + ", ".join(
        f"conv_coefficient_{i}" for i in range(len(convolution_coefficients))
    ) + "]",
    "",
    "private theorem polynomial_certificate (r s : ℚ) :",
    f"    {term_sum} = F r s * Q r s := by",
    "  rw [terms_eq_numerator, F_mul_Q_eq_convolution, convolution_eq_numerator]",
    "",
])

all_nonzero_args = {
    "hr": "(hr : r ≠ 0)", "hs": "(hs : s ≠ 0)",
    "hA": "(hA : A r s ≠ 0)", "hB": "(hB : B r s ≠ 0)",
    "hC": "(hC : C r s ≠ 0)", "hK": "(hK : K r s ≠ 0)",
    "hD": "(hD : D r s ≠ 0)", "hE": "(hE : E r s ≠ 0)",
    "hL": "(hL : L r s ≠ 0)", "hJ": "(hJ : J r s ≠ 0)",
    "hP6": "(hP6 : P6 r s ≠ 0)", "hP9": "(hP9 : P9 r s ≠ 0)",
}
needed_nonzero = {
    0: ("hr", "hs", "hA", "hB", "hC", "hK", "hE", "hL", "hP6", "hP9"),
    2: ("hr", "hA", "hB", "hC", "hK", "hD", "hE", "hL", "hJ", "hP6"),
    3: ("hs", "hA", "hC", "hD", "hL", "hJ", "hP6", "hP9"),
    4: ("hr", "hs", "hA", "hB", "hC", "hK", "hD", "hE", "hL", "hJ", "hP9"),
    5: tuple(all_nonzero_args),
}[index]
nonzero_args = [all_nonzero_args[name] for name in needed_nonzero]
y_names = {
    0: ("y1", "y2", "y8", "y9"),
    2: ("y1", "y2", "y4", "y8"),
    3: ("y2", "y4", "y8", "y9"),
    4: ("y1", "y4", "y8", "y9"),
    5: ("y1", "y2", "y4", "y8", "y9"),
}[index]
relation_lean = {
    0: "y1 r s - y9 r s - y1 r s * y8 r s * (y2 r s - y1 r s)",
    2: "y4 r s - y2 r s - y4 r s * y1 r s * (y8 r s - y4 r s)",
    3: "y8 r s - y4 r s - y8 r s * y2 r s * (y9 r s - y8 r s)",
    4: "y9 r s - y8 r s - y9 r s * y4 r s * (y1 r s - y9 r s)",
    5: "y1 r s * y2 r s * y4 r s * y8 r s * y9 r s - 1",
}[index]
lines.extend([
    f"theorem relation_{index}",
    "    (r s : ℚ) " + " ".join(nonzero_args),
    "    (hF : F r s = 0) :",
    f"    {relation_lean} = 0 := by",
    f"  have hpoly : {term_sum} = 0 := by",
    "    rw [polynomial_certificate, hF]",
    "    ring",
    "  simp only [" + ", ".join(y_names) + "]",
    "  field_simp [" + ", ".join(needed_nonzero) + "]",
    "  simp only [" + ", ".join(f"term{i}" for i in range(len(terms))) + "] at hpoly",
    "  linear_combination hpoly",
    "",
    f"end ScratchYRelation{index}",
    "",
])

output = Path(f"ScratchYRelation{index}.lean")
output.write_text("\n".join(lines), encoding="utf-8")
print(
    f"wrote {output}: relation terms={len(poly_terms(certificate_numerator))}, "
    f"quotient terms={len(poly_terms(quotient.as_expr()))}, "
    f"r degrees numerator={len(numerator_coefficients)-1}, quotient={len(quotient_coefficients)-1}"
)

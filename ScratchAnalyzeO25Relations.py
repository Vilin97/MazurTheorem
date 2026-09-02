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

A, B, C, K, D, E, L, J, T, M, N, P6, P9 = (
    values[name] for name in ("A", "B", "C", "K", "D", "E", "L", "J", "T", "M", "N", "P6", "P9")
)
raw_coefficients = [parse(f"rawFC{i}", values) for i in range(11)]
raw_f = sp.Poly(sum(raw_coefficients[i] * r**i for i in range(11)), r, s, domain=sp.QQ)

a = -(A * L * T) / (B * D**2 * E)
b = r * B**4 * C * K * M * E / (A * P6 * L)
c = r * B * K**3 * E * T * M * N / (s * C**3 * D * J * P9)
d = -(A * C * J) / (r * B * K**2 * E)
e = r * B**3 * K**2 * D * M**2 * N / (s * A**3 * C * P6 * P9)

relations = (
    a - c - a * (b - d),
    b - d - b * (c - e),
    c - e - c * (d - a),
    d - a - d * (e - b),
    e - b - e * (a - c),
    a * b * c * d * e - 1,
)


def factored(label: str, expression: sp.Expr) -> sp.Expr:
    result = sp.factor(sp.cancel(expression))
    print(f"{label}={result}", flush=True)
    return result


x2 = r * s * (r - 1)
x3 = s * (r - 1)
x4 = r * (r - 1)
x6 = s * (r - 1) * A / B**2
G = r * s**2 - 3 * r * s + r + s**2
x7 = r * s * (r - 1) * B * C / A**2
x8 = r * (r - 1) * A * K / C**2
x9 = s * (r - 1) * C * G / K**2
x11 = r * s * (r - 1) * B * G * E / D**2
x12 = (r - 1) * D * L / (B**2 * E**2)
y1 = factored("y1", ((x7 - x9) / (x7 - x4)) * ((-x12) / (-x3)))
y2 = factored("y2", (x2 / (x2 - x6)) * ((x11 - x7) / (x11 - x8)))
y4 = factored("y4", ((x4 - x2) / (x4 - x12)) * ((x3 - x11) / (x3 - x9)))
y8 = factored("y8", ((x8 - x4) / x8) * ((x6 - x3) / (x6 - x7)))
y9 = factored("y9", ((x9 - x8) / (x9 - x2)) * ((x12 - x6) / (x12 - x11)))
print(f"orbit coordinate checks={[sp.cancel(lhs-rhs) == 0 for lhs, rhs in ((y1*y4,a),(y2*y8,b),(y4*y9,c),(y8*y1,d),(y9*y2,e))]}", flush=True)
y_relations = (
    y1 - y9 - y1 * y8 * (y2 - y1),
    y2 - y1 - y2 * y9 * (y4 - y2),
    y4 - y2 - y4 * y1 * (y8 - y4),
    y8 - y4 - y8 * y2 * (y9 - y8),
    y9 - y8 - y9 * y4 * (y1 - y9),
    y1 * y2 * y4 * y8 * y9 - 1,
)
selected_yrelations = (
    [int(os.environ["YREL_ONLY"])] if "YREL_ONLY" in os.environ
    else list(range(len(y_relations)))
)
for index in selected_yrelations:
    relation = y_relations[index]
    numerator, denominator = sp.fraction(sp.cancel(relation))
    together_numerator, together_denominator = sp.fraction(sp.together(relation))
    extra = sp.cancel(together_numerator / numerator)
    numerator_poly = sp.Poly(numerator, r, s, domain=sp.QQ)
    quotient, remainder = sp.div(numerator_poly, raw_f)
    coefficient, factors = sp.factor_list(quotient.as_expr()) if remainder.is_zero else (0, [])
    print(
        f"yrelation {index}: degree={numerator_poly.total_degree()} terms={len(numerator_poly.terms())} "
        f"divisible={remainder.is_zero} quotient_degree={quotient.total_degree()} "
        f"quotient_terms={len(quotient.terms())} quotient_factors={[(sp.Poly(f,r,s).total_degree(),n) for f,n in factors]} "
        f"coefficient={coefficient} denominator={sp.factor(denominator)}",
        flush=True,
    )
    print(
        f"yrelation {index}: together_extra={sp.factor(extra)} "
        f"together_denominator_over_canceled={sp.factor(together_denominator / denominator)}",
        flush=True,
    )

if "YREL_ONLY" in os.environ:
    raise SystemExit(0)

print(f"F total_degree={raw_f.total_degree()} terms={len(raw_f.terms())}", flush=True)
for index, relation in enumerate(relations):
    print(f"relation {index}: clearing", flush=True)
    numerator, denominator = sp.fraction(sp.cancel(relation))
    numerator_poly = sp.Poly(numerator, r, s, domain=sp.QQ)
    print(
        f"relation {index}: numerator degree={numerator_poly.total_degree()} "
        f"terms={len(numerator_poly.terms())}",
        flush=True,
    )
    quotient, remainder = sp.div(numerator_poly, raw_f)
    print(
        f"relation {index}: divisible={remainder.is_zero} "
        f"quotient_degree={quotient.total_degree()} terms={len(quotient.terms())} "
        f"denominator={sp.factor(denominator)}",
        flush=True,
    )
    if remainder.is_zero:
        coefficient, factors = sp.factor_list(quotient.as_expr())
        print(
            f"relation {index}: quotient_factor_coefficient={coefficient} "
            f"factor_degrees={[((sp.Poly(f, r, s).total_degree()), n) for f, n in factors]}",
            flush=True,
        )

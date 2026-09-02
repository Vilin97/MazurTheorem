from pathlib import Path
import re
import os

root = Path(__file__).parent
target = root / "MazurTorsion/Kubert/OrderTwentyFiveNormalizedModel.lean"
source = (root / "ScratchYRelation2.lean").read_text()


def wrap_generated_lines(source_text: str) -> str:
    output = []
    for line in source_text.splitlines():
        if len(line) <= 100:
            output.append(line)
            continue
        indent = line[:len(line) - len(line.lstrip())]
        stripped = line.strip()
        if stripped.startswith("simp only [") and stripped.endswith("]"):
            items = stripped[len("simp only ["):-1].split(", ")
            prefix = indent + "simp only ["
            continuation = indent + "  "
            current = prefix
            for item_index, item in enumerate(items):
                token = item + ("," if item_index + 1 < len(items) else "]")
                addition = token if current.endswith("[") else " " + token
                if len(current) + len(addition) > 100 and current != prefix:
                    output.append(current)
                    current = continuation + token
                else:
                    current += addition
            output.append(current)
            continue
        if " + " in stripped:
            terms = stripped.split(" + ")
            current = indent + terms[0]
            for term in terms[1:]:
                addition = " + " + term
                if len(current) + len(addition) > 100:
                    output.append(current)
                    current = indent + "  + " + term
                else:
                    current += addition
            output.append(current)
            continue
        if stripped.startswith("(") and ") (" in stripped:
            groups = re.findall(r"\([^()]*\)", stripped)
            current = indent
            for group in groups:
                addition = group if current == indent else " " + group
                if len(current) + len(addition) > 100 and current != indent:
                    output.append(current)
                    current = indent + group
                else:
                    current += addition
            output.append(current)
            continue
        if " * " in stripped:
            factors = stripped.split(" * ")
            current = indent + factors[0]
            for factor in factors[1:]:
                addition = " * " + factor
                if len(current) + len(addition) > 100:
                    output.append(current)
                    current = indent + "  * " + factor
                else:
                    current += addition
            output.append(current)
            continue
        raise RuntimeError(f"unhandled long generated line: {line}")
    return "\n".join(output) + "\n"

base_start = source.index("private def A ")
base_end = source.index("private def term0 ")
base = source[base_start:base_end].rstrip()

relations = []
localized = {}
module_names = {
    0: "Zero", 2: "Two", 3: "Three", 4: "Four", 5: "Five"
}
names = {0: "RelationZero", 2: "RelationTwo", 3: "RelationThree",
         4: "RelationFour", 5: "RelationFive"}
for index, namespace in names.items():
    text = (root / f"ScratchYRelation{index}.lean").read_text()
    start = text.index("private def term0 ")
    theorem_start = text.index(f"theorem relation_{index}")
    end = text.index(f"\nend ScratchYRelation{index}")
    helper = text[start:theorem_start].rstrip()
    local_lines = []
    for line in helper.splitlines():
        if line.startswith("private def "):
            line = "let " + line[len("private def "):]
        elif line.startswith("private theorem "):
            line = "have " + line[len("private theorem "):]
        local_lines.append(("  " + line).rstrip())
    local_helper = "\n".join(local_lines)
    theorem = text[theorem_start:end].rstrip()
    theorem = theorem.replace(
        f"theorem relation_{index}", "private theorem relation", 1)
    proof_start = theorem.index(":= by\n") + len(":= by\n")
    body = theorem[:proof_start] + local_helper + "\n\n" + theorem[proof_start:]
    localized[index] = (namespace, body)
    certificate_body = text[start:end].rstrip()
    certificate_name = f"orderTwentyFiveUnitRelation{module_names[index]}Certificate"
    certificate_body = certificate_body.replace(
        f"theorem relation_{index}",
        "/-- Internal exact coefficient certificate consumed by the\n"
        "actual-coordinate order-25 orbit proof. -/\n"
        f"theorem {certificate_name}",
        1,
    )
    production = f"""/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitCertificate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# An internal coefficient certificate for the order-25 unit relation

The polynomial tables below are exact division and convolution witnesses.
They remain private; the single internal theorem is consumed by the checked
actual-coordinate orbit proof in `OrderTwentyFiveNormalizedModel`.
-/

namespace MazurTorsion.Kubert.Internal

{base}

{certificate_body}

end MazurTorsion.Kubert.Internal
"""
    production_path = root / (
        f"MazurTorsion/Kubert/OrderTwentyFiveUnitRelation{module_names[index]}Certificate.lean"
    )
    production_path.write_text(wrap_generated_lines(production))
    relations.append(
        f"private namespace {namespace}\n\n{body}\n\nend {namespace}"
    )

raw_source = (root / "ScratchRawYFactors.lean").read_text()
raw_start = raw_source.index("private theorem x7_sub_x9 ")
raw_end = raw_source.index("\nend ScratchRawYFactors")
raw_factors = raw_source[raw_start:raw_end].rstrip()
raw_names = {
    "x2": "orderTwentyFiveRawXTwo",
    "x3": "orderTwentyFiveRawXThree",
    "x4": "orderTwentyFiveRawXFour",
    "x6": "orderTwentyFiveRawXSix",
    "x7": "orderTwentyFiveRawXSeven",
    "x8": "orderTwentyFiveRawXEight",
    "x9": "orderTwentyFiveRawXNine",
    "x11": "orderTwentyFiveRawXEleven",
    "x12": "orderTwentyFiveRawXTwelve",
    "rawY1": "orderTwentyFiveRawYSeven",
    "rawY2": "orderTwentyFiveRawYTwo",
    "rawY4": "orderTwentyFiveRawYFour",
    "rawY8": "orderTwentyFiveRawYEight",
    "rawY9": "orderTwentyFiveRawYNine",
}
for old, new in sorted(raw_names.items(), key=lambda item: -len(item[0])):
    raw_factors = re.sub(rf"\b{old}\b", new, raw_factors)
raw_factors = raw_factors.replace(
    "theorem rawY1_eq", "private theorem rawYSeven_eq_y1", 1)
raw_factors = raw_factors.replace(
    "theorem rawY2_eq", "private theorem rawYTwo_eq_y2", 1)
raw_factors = raw_factors.replace(
    "theorem rawY4_eq", "private theorem rawYFour_eq_y4", 1)
raw_factors = raw_factors.replace(
    "theorem rawY8_eq", "private theorem rawYEight_eq_y8", 1)
raw_factors = raw_factors.replace(
    "theorem rawY9_eq", "private theorem rawYNine_eq_y9", 1)

block = """
/- BEGIN generated order-25 unit relation bridge.  The large exact coefficient
tables live in five separately checked internal modules so their elaboration
does not accumulate in one process.  The shared chart and every raw-coordinate
bridge below remain private. -/
namespace OrderTwentyFiveUnitRelationCertificate

{base}

private theorem F_eq_rawSutherlandPolynomial (r s : ℚ) :
    F r s = orderTwentyFiveRawSutherlandPolynomial r s := by
  simp only [F, fC0, fC1, fC2, fC3, fC4, fC5, fC6, fC7, fC8, fC9, fC10,
    orderTwentyFiveRawSutherlandPolynomial,
    orderTwentyFiveRawSutherlandPolynomialChunk0,
    orderTwentyFiveRawSutherlandPolynomialChunk1,
    orderTwentyFiveRawSutherlandPolynomialChunk2,
    orderTwentyFiveRawSutherlandPolynomialChunk3,
    orderTwentyFiveRawSutherlandPolynomialChunk4,
    orderTwentyFiveRawSutherlandPolynomialChunk5]
  ring

/- Small factorized cross-difference lemmas connect the checked raw Tate
chart to the five rational functions used by the certificates. -/
{raw_factors}

end OrderTwentyFiveUnitRelationCertificate
/- END generated order-25 unit relation bridge. -/
""".format(base=base, relations="\n\n".join(relations), raw_factors=raw_factors)

text = target.read_text()
if "import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitCertificate" not in text:
    text = text.replace(
        "import MazurTorsion.Kubert.OrderTwentyFiveBrunault\n",
        "import MazurTorsion.Kubert.OrderTwentyFiveBrunault\n"
        "import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitCertificate\n"
        "import Mathlib.Tactic.FieldSimp\n"
        "import Mathlib.Tactic.LinearCombination\n",
        1,
    )
certificate_imports = "\n".join(
    f"import MazurTorsion.Kubert.OrderTwentyFiveUnitRelation{name}Certificate"
    for name in module_names.values()
)
if "import MazurTorsion.Kubert.OrderTwentyFiveUnitRelationZeroCertificate" not in text:
    anchor = "import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitCertificate\n"
    text = text.replace(anchor, anchor + certificate_imports + "\n", 1)

begin = text.find("/- BEGIN generated order-25 unit relation")
if begin != -1:
    end_candidates = [
        "/- END generated order-25 unit relation certificates. -/",
        "/- END generated order-25 unit relation bridge. -/",
    ]
    end_marker = next(marker for marker in end_candidates if marker in text[begin:])
    end = text.index(end_marker, begin) + len(end_marker)
    text = text[:begin] + text[end:]

closing = "\nend MazurTorsion.Kubert\n"
assert text.endswith(closing)
endpoint_anchor = "open OrderTwentyFiveUnitRelationCertificate"
if endpoint_anchor in text:
    insert_at = text.index(endpoint_anchor)
    text = text[:insert_at] + block.strip() + "\n\n" + text[insert_at:]
else:
    text = text[:-len(closing)] + "\n" + block.strip() + closing
target.write_text(text)

if os.environ.get("WRITE_LOCAL_SCRATCH"):
    for index, (namespace, body) in localized.items():
        scratch = f"""import MazurTorsion.Kubert.OrderTwentyFiveBrunaultOrbitCertificate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace ScratchYRelation{index}Local

{base}

private namespace {namespace}

{body}

end {namespace}

end ScratchYRelation{index}Local
"""
        (root / f"ScratchYRelation{index}Local.lean").write_text(scratch)

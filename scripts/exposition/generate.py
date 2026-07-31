#!/usr/bin/env python3
"""Generate a small, deterministic static index of the checked Lean sources."""

from __future__ import annotations

import argparse
import html
import json
import re
import shutil
from dataclasses import dataclass
from pathlib import Path
from urllib.parse import quote, urlsplit


SOURCE_GLOBS = (
    "MazurTorsion.lean",
    "MazurTorsion/**/*.lean",
    "EllipticCurves.lean",
    "EllipticCurves/**/*.lean",
)
DECLARATION_PATTERN = re.compile(
    r"^\s*(?:(?:@\[[^\]\n]*\]|private|protected|noncomputable|nonrec|"
    r"irreducible|local|scoped|public)\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|structure|class|inductive|"
    r"coinductive|instance|opaque)\s+(?P<name>[^\s:({\[]+)",
    re.MULTILINE,
)
IMPORT_PATTERN = re.compile(r"^\s*import\s+(.+)$", re.MULTILINE)
FORBIDDEN_PATTERN = re.compile(r"\b(sorry|admit|native_decide)\b")
OUTPUT_SENTINEL = ".generated-by-mazur-exposition"


@dataclass(frozen=True)
class Declaration:
    """A declaration found by the lightweight source scanner."""

    kind: str
    name: str
    line: int


def strip_comments_and_strings(source: str) -> str:
    """Mask comments and strings while preserving newlines and byte positions."""

    output = list(source)
    index = 0
    block_depth = 0
    in_line_comment = False
    in_string = False
    escaped = False

    while index < len(source):
        pair = source[index : index + 2]
        character = source[index]

        if in_line_comment:
            if character == "\n":
                in_line_comment = False
            else:
                output[index] = " "
            index += 1
            continue

        if block_depth:
            if pair == "/-":
                output[index] = output[index + 1] = " "
                block_depth += 1
                index += 2
            elif pair == "-/":
                output[index] = output[index + 1] = " "
                block_depth -= 1
                index += 2
            else:
                if character != "\n":
                    output[index] = " "
                index += 1
            continue

        if in_string:
            if character != "\n":
                output[index] = " "
            if escaped:
                escaped = False
            elif character == "\\":
                escaped = True
            elif character == '"':
                in_string = False
            index += 1
            continue

        if pair == "--":
            output[index] = output[index + 1] = " "
            in_line_comment = True
            index += 2
        elif pair == "/-":
            output[index] = output[index + 1] = " "
            block_depth = 1
            index += 2
        elif character == '"':
            output[index] = " "
            in_string = True
            index += 1
        else:
            index += 1

    return "".join(output)


def source_files(repository_root: Path) -> list[Path]:
    """Return each checked Lean source exactly once."""

    files: set[Path] = set()
    for pattern in SOURCE_GLOBS:
        files.update(repository_root.glob(pattern))
    return sorted(path for path in files if path.is_file())


def module_name(repository_root: Path, source_path: Path) -> str:
    """Translate a Lean source path to its module name."""

    return ".".join(source_path.relative_to(repository_root).with_suffix("").parts)


def line_number(source: str, offset: int) -> int:
    """Return the one-based line number at an offset."""

    return source.count("\n", 0, offset) + 1


def scan_module(
    repository_root: Path,
    source_path: Path,
    repository: str,
    commit: str,
) -> dict[str, object]:
    """Extract stable, intentionally shallow metadata from one module."""

    source = source_path.read_text(encoding="utf-8")
    masked = strip_comments_and_strings(source)
    declarations = [
        Declaration(
            kind=match.group("kind"),
            name=match.group("name"),
            line=line_number(masked, match.start("kind")),
        )
        for match in DECLARATION_PATTERN.finditer(masked)
    ]
    imports: list[str] = []
    for match in IMPORT_PATTERN.finditer(masked):
        imports.extend(match.group(1).split())

    relative_path = source_path.relative_to(repository_root).as_posix()
    encoded_path = quote(relative_path, safe="/")
    source_url = f"https://github.com/{repository}/blob/{commit}/{encoded_path}"
    return {
        "module": module_name(repository_root, source_path),
        "path": relative_path,
        "source_url": source_url,
        "lines": len(source.splitlines()),
        "imports": imports,
        "declarations": [
            {
                "kind": declaration.kind,
                "name": declaration.name,
                "line": declaration.line,
                "source_url": f"{source_url}#L{declaration.line}",
            }
            for declaration in declarations
        ],
        "forbidden_holes": len(FORBIDDEN_PATTERN.findall(masked)),
    }


def stylesheet() -> str:
    """Return the shared static stylesheet."""

    return """
:root { color-scheme: dark; --ink:#f2efe8; --muted:#aaa79f; --line:#373633;
  --panel:#1c1b1a; --accent:#f0a15a; --link:#8ec8ff; }
* { box-sizing: border-box; }
body { margin:0; background:#11110f; color:var(--ink);
  font:16px/1.55 ui-sans-serif,system-ui,-apple-system,sans-serif; }
main { width:min(1120px,calc(100% - 2rem)); margin:0 auto; padding:4rem 0; }
h1 { font:700 clamp(2.3rem,7vw,5rem)/.98 ui-serif,Georgia,serif; margin:.3rem 0 1rem; }
h2 { font:650 1.55rem/1.2 ui-serif,Georgia,serif; }
.eyebrow { color:var(--accent); text-transform:uppercase; letter-spacing:.12em;
  font-size:.78rem; font-weight:750; }
.lede { max-width:760px; color:var(--muted); font-size:1.15rem; }
.grid { display:grid; grid-template-columns:repeat(auto-fit,minmax(180px,1fr));
  gap:1rem; margin:2.5rem 0; }
.card { border:1px solid var(--line); background:var(--panel); padding:1.2rem;
  border-radius:.45rem; }
.metric { display:block; font:700 2rem/1 ui-monospace,SFMono-Regular,monospace; }
.label { color:var(--muted); }
a { color:var(--link); }
nav { display:flex; flex-wrap:wrap; gap:1.1rem; margin:1.5rem 0 3rem; }
table { width:100%; border-collapse:collapse; margin-top:1rem; }
th,td { border-bottom:1px solid var(--line); padding:.65rem .45rem; text-align:left; }
th { color:var(--muted); font-size:.8rem; text-transform:uppercase; letter-spacing:.06em; }
td.num { text-align:right; font-variant-numeric:tabular-nums; }
code { font-family:ui-monospace,SFMono-Regular,monospace; font-size:.88em; }
.commit { overflow-wrap:anywhere; }
""".strip()


def landing_page(index: dict[str, object]) -> str:
    """Build the Pages landing page."""

    totals = index["totals"]
    assert isinstance(totals, dict)
    repository = html.escape(str(index["repository"]))
    commit = html.escape(str(index["commit"]))
    roadmap_url = html.escape(str(index["roadmap_url"]))
    cards = "".join(
        f'<div class="card"><span class="metric">{totals[key]:,}</span>'
        f'<span class="label">{label}</span></div>'
        for key, label in (
            ("modules", "Lean modules"),
            ("lines", "lines of Lean"),
            ("declarations", "declarations"),
            ("imports", "import edges"),
        )
    )
    return f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport"
content="width=device-width,initial-scale=1"><title>Mazur Theorem formalization</title>
<meta name="description" content="A collaborative Lean 4 formalization of Mazur's torsion theorem.">
<meta property="og:title" content="Mazur Theorem formalization">
<meta property="og:description" content="Roadmap, blueprint, and checked Lean source inventory.">
<meta property="og:image" content="og.png">
<meta name="twitter:card" content="summary_large_image">
<link rel="stylesheet" href="assets/site.css"></head><body><main>
<p class="eyebrow">Collaborative Lean 4 formalization</p>
<h1>Mazur Theorem</h1>
<p class="lede">Build status and machine-generated source inventory for the
formalization of Mazur's torsion theorem over the rational numbers.</p>
<nav><a href="{roadmap_url}">Live roadmap</a>
<a href="blueprint/">Blueprint</a><a href="docs/">API documentation</a>
<a href="exposition/">Source exposition</a>
<a href="https://github.com/{repository}">GitHub repository</a></nav>
<section class="grid">{cards}</section>
<p class="label commit">Generated from commit <code>{commit}</code>.</p>
</main></body></html>
"""


def exposition_page(index: dict[str, object]) -> str:
    """Build the module inventory page."""

    rows = []
    for module in index["modules"]:
        assert isinstance(module, dict)
        declarations = module["declarations"]
        imports = module["imports"]
        assert isinstance(declarations, list)
        assert isinstance(imports, list)
        rows.append(
            "<tr>"
            f'<td><a href="{html.escape(str(module["source_url"]))}"><code>'
            f'{html.escape(str(module["module"]))}</code></a></td>'
            f'<td class="num">{int(module["lines"]):,}</td>'
            f'<td class="num">{len(declarations):,}</td>'
            f'<td class="num">{len(imports):,}</td>'
            "</tr>"
        )
    return f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport"
content="width=device-width,initial-scale=1"><title>Source exposition · Mazur Theorem</title>
<link rel="stylesheet" href="../assets/site.css"></head><body><main>
<p class="eyebrow">Machine-generated inventory</p>
<h1>Source exposition</h1>
<p class="lede">A commit-pinned map of checked Lean modules. Declaration-level
metadata is available in <a href="data/index.json">JSON</a>.</p>
<nav><a href="../">Overview</a><a href="../blueprint/">Blueprint</a>
<a href="../docs/">API documentation</a></nav>
<table><thead><tr><th>Module</th><th>Lines</th><th>Declarations</th>
<th>Imports</th></tr></thead><tbody>{''.join(rows)}</tbody></table>
</main></body></html>
"""


def validate_output(output_root: Path, expected_commit: str) -> None:
    """Fail if a generated artifact is incomplete or internally inconsistent."""

    required = (
        "index.html",
        ".nojekyll",
        OUTPUT_SENTINEL,
        "assets/site.css",
        "exposition/index.html",
        "exposition/data/index.json",
    )
    missing = [path for path in required if not (output_root / path).is_file()]
    if missing:
        raise RuntimeError(f"generated site is missing: {', '.join(missing)}")
    data = json.loads(
        (output_root / "exposition/data/index.json").read_text(encoding="utf-8")
    )
    if data.get("commit") != expected_commit:
        raise RuntimeError("generated exposition commit does not match requested commit")
    if data.get("totals", {}).get("modules") != len(data.get("modules", [])):
        raise RuntimeError("generated exposition module total is inconsistent")


def generate(
    repository_root: Path,
    output_root: Path,
    repository: str,
    commit: str,
    roadmap_url: str,
) -> None:
    """Generate the complete lightweight site."""

    parsed_roadmap_url = urlsplit(roadmap_url)
    if parsed_roadmap_url.scheme != "https" or not parsed_roadmap_url.netloc:
        raise ValueError("--roadmap-url must be an absolute HTTPS URL")

    modules = [
        scan_module(repository_root, path, repository, commit)
        for path in source_files(repository_root)
    ]
    totals = {
        "modules": len(modules),
        "lines": sum(int(module["lines"]) for module in modules),
        "declarations": sum(
            len(module["declarations"])  # type: ignore[arg-type]
            for module in modules
        ),
        "imports": sum(
            len(module["imports"])  # type: ignore[arg-type]
            for module in modules
        ),
        "forbidden_holes": sum(int(module["forbidden_holes"]) for module in modules),
    }
    index: dict[str, object] = {
        "schema_version": 1,
        "repository": repository,
        "commit": commit,
        "roadmap_url": roadmap_url,
        "totals": totals,
        "modules": modules,
    }

    if output_root.exists() and not (output_root / OUTPUT_SENTINEL).is_file():
        raise RuntimeError(
            f"refusing to replace non-generator directory: {output_root}"
        )
    if output_root.exists():
        shutil.rmtree(output_root)
    (output_root / "assets").mkdir(parents=True)
    (output_root / "exposition/data").mkdir(parents=True)
    (output_root / OUTPUT_SENTINEL).write_text(
        "Generated by scripts/exposition/generate.py.\n",
        encoding="utf-8",
    )
    (output_root / ".nojekyll").touch()
    (output_root / "assets/site.css").write_text(stylesheet() + "\n", encoding="utf-8")
    (output_root / "index.html").write_text(landing_page(index), encoding="utf-8")
    (output_root / "exposition/index.html").write_text(
        exposition_page(index), encoding="utf-8"
    )
    (output_root / "exposition/data/index.json").write_text(
        json.dumps(index, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    validate_output(output_root, commit)


def parse_arguments() -> argparse.Namespace:
    """Parse command-line arguments."""

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--commit", required=True)
    parser.add_argument("--repository", default="Vilin97/MazurTheorem")
    parser.add_argument(
        "--roadmap-url",
        default="https://github.com/Vilin97/MazurTheorem",
        help="Primary roadmap URL, normally the production Sites deployment.",
    )
    return parser.parse_args()


def main() -> None:
    """Run the generator."""

    arguments = parse_arguments()
    generate(
        arguments.repo_root.resolve(),
        arguments.out.resolve(),
        arguments.repository,
        arguments.commit,
        arguments.roadmap_url,
    )


if __name__ == "__main__":
    main()

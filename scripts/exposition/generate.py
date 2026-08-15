#!/usr/bin/env python3
"""Generate a small, deterministic static index of the checked Lean sources."""

from __future__ import annotations

import argparse
import ast
import html
import json
import re
import shutil
from dataclasses import dataclass
from functools import cache
from pathlib import Path
from typing import Any
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
IMPORT_PATTERN = re.compile(
    r"^[ \t]*(?:public[ \t]+)?(?:meta[ \t]+)?import(?:[ \t]+all)?[ \t]+"
    r"(?P<module>[A-Za-z0-9_'.]+)[ \t]*$",
    re.MULTILINE,
)
FORBIDDEN_PATTERN = re.compile(r"\b(sorry|admit|native_decide)\b")
OUTPUT_SENTINEL = ".generated-by-mazur-exposition"
PROGRAMME_PATH = Path("coordination/program.json")
CACHE_POLICY_PATH = Path("scripts/lean_regular_cache.py")

CACHE_PARTITION_LABELS = {
    "regular-base": "Regular base cache/source",
    "regular-downstream": "Regular downstream cache/source",
    "specialized-heavy": "Specialized certificate cache/source",
    "audit-only": "Exhaustive-audit-only source",
}
NAVIGATION_GROUPS = (
    (
        "roadmap",
        "Roadmap-linked modules",
        "Modules named by at least one canonical ledger artifact.",
    ),
    (
        "supporting",
        "Supporting source",
        "Checked modules not named directly by a ledger artifact.",
    ),
    (
        "certificate-envelope",
        "Unlinked cache-heavy certificate modules",
        "Certificate internals assigned to the specialized generated-proof cache and "
        "not named by a roadmap artifact; collapsed in the human index but retained "
        "declaration-by-declaration in JSON.",
    ),
)


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


def scan_imports(masked_source: str) -> list[str]:
    """Return imports with Lean 4's optional ``public``, ``meta``, and ``all`` modifiers."""

    return [match.group("module") for match in IMPORT_PATTERN.finditer(masked_source)]


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
    imports = scan_imports(masked)

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


def load_json_object(path: Path) -> dict[str, Any]:
    """Load a JSON object or fail with the source path in the diagnostic."""

    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"{path} must contain a JSON object")
    return value


def require_string(value: object, location: str) -> str:
    """Return a nonempty string from canonical metadata."""

    if not isinstance(value, str) or not value:
        raise ValueError(f"{location} must be a nonempty string")
    return value


def roadmap_metadata(
    programme: dict[str, Any],
    modules_by_name: dict[str, dict[str, object]],
) -> tuple[list[dict[str, object]], dict[str, list[dict[str, str]]]]:
    """Join canonical ledger artifacts to their checked source modules.

    The ledger is authoritative: artifacts without a recorded ``module`` stay
    explicitly unmapped, while every recorded module must resolve to a source
    scanned into this exposition.
    """

    raw_nodes = programme.get("nodes")
    if not isinstance(raw_nodes, list):
        raise ValueError("coordination/program.json.nodes must be a list")

    links_by_module = {name: [] for name in modules_by_name}
    roadmap_nodes: list[dict[str, object]] = []
    seen_node_ids: set[str] = set()
    for node_index, raw_node in enumerate(raw_nodes):
        location = f"coordination/program.json.nodes[{node_index}]"
        if not isinstance(raw_node, dict):
            raise ValueError(f"{location} must be an object")
        node_id = require_string(raw_node.get("id"), f"{location}.id")
        if node_id in seen_node_ids:
            raise ValueError(f"duplicate roadmap node id {node_id}")
        seen_node_ids.add(node_id)
        node_title = require_string(raw_node.get("title"), f"{location}.title")
        node_status = require_string(raw_node.get("status"), f"{location}.status")
        node_stage = require_string(raw_node.get("stage"), f"{location}.stage")
        raw_artifacts = raw_node.get("artifacts", [])
        if not isinstance(raw_artifacts, list):
            raise ValueError(f"{location}.artifacts must be a list")

        artifacts: list[dict[str, object]] = []
        for artifact_index, raw_artifact in enumerate(raw_artifacts):
            artifact_location = f"{location}.artifacts[{artifact_index}]"
            if not isinstance(raw_artifact, dict):
                raise ValueError(f"{artifact_location} must be an object")
            artifact_name = require_string(
                raw_artifact.get("name"), f"{artifact_location}.name"
            )
            artifact_kind = require_string(
                raw_artifact.get("kind"), f"{artifact_location}.kind"
            )
            artifact_state = require_string(
                raw_artifact.get("state"), f"{artifact_location}.state"
            )
            artifact: dict[str, object] = {
                "name": artifact_name,
                "kind": artifact_kind,
                "state": artifact_state,
            }
            recorded_module = raw_artifact.get("module")
            if recorded_module is not None:
                artifact_module = require_string(
                    recorded_module, f"{artifact_location}.module"
                )
                source_module = modules_by_name.get(artifact_module)
                if source_module is None:
                    raise ValueError(
                        f"{artifact_location}.module names unindexed source "
                        f"{artifact_module}"
                    )
                artifact.update(
                    {
                        "module": artifact_module,
                        "module_path": source_module["path"],
                        "source_url": source_module["source_url"],
                    }
                )
                links_by_module[artifact_module].append(
                    {
                        "node_id": node_id,
                        "node_title": node_title,
                        "node_status": node_status,
                        "artifact_name": artifact_name,
                        "artifact_kind": artifact_kind,
                        "artifact_state": artifact_state,
                    }
                )
            artifacts.append(artifact)

        roadmap_nodes.append(
            {
                "id": node_id,
                "title": node_title,
                "status": node_status,
                "stage": node_stage,
                "artifacts": artifacts,
            }
        )

    return roadmap_nodes, links_by_module


def cache_policy_literals(
    path: Path,
) -> tuple[tuple[str, ...], tuple[str, ...], set[str], str]:
    """Read cache classification constants without rescanning every source."""

    syntax = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
    values: dict[str, object] = {}
    wanted = {"ROOT_MODULES", "HEAVY_PREFIXES", "EXPECTED_DOWNSTREAM"}
    import_pattern: str | None = None
    for statement in syntax.body:
        if not isinstance(statement, ast.Assign) or len(statement.targets) != 1:
            continue
        target = statement.targets[0]
        if isinstance(target, ast.Name) and target.id in wanted:
            values[target.id] = ast.literal_eval(statement.value)
        elif isinstance(target, ast.Name) and target.id == "IMPORT_RE":
            value = statement.value
            if (
                isinstance(value, ast.Call)
                and value.args
                and isinstance(value.args[0], ast.Constant)
                and isinstance(value.args[0].value, str)
            ):
                import_pattern = value.args[0].value
    missing = sorted(wanted - values.keys())
    if missing or import_pattern is None:
        raise ValueError(f"cache policy omits literal constants: {missing}")

    root_modules = values["ROOT_MODULES"]
    heavy_prefixes = values["HEAVY_PREFIXES"]
    expected_downstream = values["EXPECTED_DOWNSTREAM"]
    if not (
        isinstance(root_modules, tuple)
        and all(isinstance(value, str) for value in root_modules)
        and isinstance(heavy_prefixes, tuple)
        and all(isinstance(value, str) for value in heavy_prefixes)
        and isinstance(expected_downstream, set)
        and all(isinstance(value, str) for value in expected_downstream)
    ):
        raise ValueError("cache policy classification constants have invalid types")
    return root_modules, heavy_prefixes, expected_downstream, import_pattern


def cache_partitions(
    repository_root: Path, modules_by_name: dict[str, dict[str, object]]
) -> tuple[dict[str, str], dict[str, str]]:
    """Read the existing cache policy as navigation metadata only."""

    module_names = set(modules_by_name)
    roots, heavy_prefixes, expected_downstream, cache_import_pattern = cache_policy_literals(
        repository_root / CACHE_POLICY_PATH
    )
    cache_import_re = re.compile(cache_import_pattern, re.MULTILINE)
    local_imports = {
        name: {
            imported
            for imported in cache_import_re.findall(
                (repository_root / str(module["path"])).read_text(encoding="utf-8")
            )
            if imported in module_names
        }
        for name, module in modules_by_name.items()
    }
    unknown_roots = sorted(set(roots) - module_names)
    if unknown_roots:
        raise ValueError(f"cache policy names unknown root modules: {unknown_roots}")

    root_modules: set[str] = set()
    pending = list(roots)
    while pending:
        name = pending.pop()
        if name in root_modules:
            continue
        root_modules.add(name)
        pending.extend(local_imports[name] - root_modules)
    heavy_modules = {
        name
        for name in root_modules
        if any(name.startswith(prefix) for prefix in heavy_prefixes)
    }

    visiting: set[str] = set()

    @cache
    def reaches_heavy(name: str) -> bool:
        if name in visiting:
            raise ValueError(f"source import cycle reaches {name}")
        visiting.add(name)
        result = name in heavy_modules or any(
            reaches_heavy(imported) for imported in local_imports[name]
        )
        visiting.remove(name)
        return result

    downstream_modules = {
        name
        for name in root_modules - heavy_modules
        if reaches_heavy(name)
    } | (heavy_modules & expected_downstream)
    if downstream_modules != expected_downstream:
        missing = sorted(expected_downstream - downstream_modules)
        extra = sorted(downstream_modules - expected_downstream)
        raise ValueError(
            "exposition/cache downstream partitions differ; "
            f"missing={missing}, extra={extra}"
        )

    partitions: dict[str, str] = {}
    heavy_family: dict[str, str] = {}
    for name in module_names:
        if name not in root_modules:
            partitions[name] = "audit-only"
        elif name in downstream_modules:
            partitions[name] = "regular-downstream"
        elif name in heavy_modules:
            partitions[name] = "specialized-heavy"
        elif name in root_modules:
            partitions[name] = "regular-base"
        else:
            raise ValueError(f"cache policy does not classify {name}")
        matching_prefixes = [
            prefix for prefix in heavy_prefixes if name.startswith(prefix)
        ]
        if name in heavy_modules:
            if len(matching_prefixes) != 1:
                raise ValueError(f"heavy module has ambiguous cache family: {name}")
            heavy_family[name] = matching_prefixes[0]
        elif matching_prefixes:
            raise ValueError(f"cache prefix classifies non-heavy module: {name}")
    return partitions, heavy_family


def navigation_group(module: dict[str, object]) -> str:
    """Place each module in one non-overlapping human-navigation group."""

    links = module["roadmap_artifacts"]
    if not isinstance(links, list):
        raise TypeError("roadmap_artifacts must be a list")
    if links:
        return "roadmap"
    if module["cache_partition"] == "specialized-heavy":
        return "certificate-envelope"
    return "supporting"


def compact_search_index(index: dict[str, object]) -> dict[str, object]:
    """Build a compact, complete search index without repeated source URLs.

    Short record keys keep this browser-facing projection substantially smaller
    than the full exposition JSON.  The projection deliberately includes every
    module, including modules collapsed into a cache-heavy family in the HTML.
    """

    raw_modules = index.get("modules")
    if not isinstance(raw_modules, list):
        raise TypeError("exposition modules must be a list")

    search_modules: list[dict[str, object]] = []
    declaration_count = 0
    import_count = 0
    artifact_count = 0
    for module_index, raw_module in enumerate(raw_modules):
        if not isinstance(raw_module, dict):
            raise TypeError(f"exposition module {module_index} must be an object")
        declarations = raw_module.get("declarations")
        imports = raw_module.get("imports")
        artifacts = raw_module.get("roadmap_artifacts")
        if not isinstance(declarations, list):
            raise TypeError(f"exposition module {module_index} declarations must be a list")
        if not isinstance(imports, list) or not all(
            isinstance(imported, str) for imported in imports
        ):
            raise TypeError(f"exposition module {module_index} imports must be strings")
        if not isinstance(artifacts, list):
            raise TypeError(f"exposition module {module_index} artifacts must be a list")

        compact_declarations: list[list[object]] = []
        for declaration_index, declaration in enumerate(declarations):
            if not isinstance(declaration, dict):
                raise TypeError(
                    f"exposition module {module_index} declaration "
                    f"{declaration_index} must be an object"
                )
            compact_declarations.append(
                [
                    require_string(
                        declaration.get("kind"),
                        f"modules[{module_index}].declarations[{declaration_index}].kind",
                    ),
                    require_string(
                        declaration.get("name"),
                        f"modules[{module_index}].declarations[{declaration_index}].name",
                    ),
                    int(declaration["line"]),
                ]
            )

        compact_artifacts: list[list[str]] = []
        for artifact_index, artifact in enumerate(artifacts):
            if not isinstance(artifact, dict):
                raise TypeError(
                    f"exposition module {module_index} artifact "
                    f"{artifact_index} must be an object"
                )
            compact_artifacts.append(
                [
                    require_string(
                        artifact.get("artifact_name"),
                        f"modules[{module_index}].artifacts[{artifact_index}].name",
                    ),
                    require_string(
                        artifact.get("node_id"),
                        f"modules[{module_index}].artifacts[{artifact_index}].node_id",
                    ),
                    require_string(
                        artifact.get("artifact_state"),
                        f"modules[{module_index}].artifacts[{artifact_index}].state",
                    ),
                ]
            )

        search_modules.append(
            {
                "m": require_string(
                    raw_module.get("module"), f"modules[{module_index}].module"
                ),
                "p": require_string(
                    raw_module.get("path"), f"modules[{module_index}].path"
                ),
                "d": compact_declarations,
                "i": list(imports),
                "a": compact_artifacts,
            }
        )
        declaration_count += len(compact_declarations)
        import_count += len(imports)
        artifact_count += len(compact_artifacts)

    module_count = len(search_modules)
    return {
        "schema_version": 1,
        "repository": require_string(index.get("repository"), "repository"),
        "commit": require_string(index.get("commit"), "commit"),
        "totals": {
            "modules": module_count,
            "declarations": declaration_count,
            "imports": import_count,
            "mapped_roadmap_artifacts": artifact_count,
            "entries": module_count
            + declaration_count
            + import_count
            + artifact_count,
        },
        "modules": search_modules,
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
details { border:1px solid var(--line); border-radius:.45rem; margin:1.5rem 0;
  padding:.9rem 1rem; }
summary { cursor:pointer; font-weight:700; }
.section-note { color:var(--muted); max-width:850px; }
.roadmap-ref { display:block; white-space:nowrap; }
.state { color:var(--muted); font-size:.82rem; }
.wide-table { overflow-x:auto; }
.search-panel { border:1px solid var(--line); background:var(--panel);
  border-radius:.45rem; margin:2.5rem 0; padding:1.2rem; }
.search-label { display:block; font-weight:700; margin:.9rem 0 .35rem; }
.search-input { width:100%; border:1px solid #55524d; border-radius:.35rem;
  background:#11110f; color:var(--ink); font:inherit; padding:.7rem .8rem; }
.search-input:focus { border-color:var(--link); outline:2px solid #8ec8ff55;
  outline-offset:1px; }
.search-status { color:var(--muted); min-height:1.55rem; margin:.55rem 0 0; }
.search-results { list-style:none; margin:1rem 0 0; padding:0; }
.search-result { border-top:1px solid var(--line); padding:.7rem 0; }
.search-result:first-child { border-top:0; }
.search-result a { overflow-wrap:anywhere; }
.search-kind { color:var(--accent); display:inline-block; font-size:.72rem;
  font-weight:750; letter-spacing:.07em; margin-right:.55rem;
  text-transform:uppercase; }
.search-context { color:var(--muted); display:block; font-size:.86rem;
  overflow-wrap:anywhere; }
""".strip()


def search_javascript() -> str:
    """Return the dependency-free, bounded browser search implementation."""

    return r'''"use strict";
(() => {
  const MAX_QUERY_LENGTH = 120;
  const RESULT_LIMIT = 100;
  const normalize = (value) => String(value).toLowerCase();
  const compareText = (left, right) => left < right ? -1 : left > right ? 1 : 0;

  function matchScore(value, query) {
    const normalized = normalize(value);
    const offset = normalized.indexOf(query);
    if (offset < 0) return null;
    if (normalized === query) return 0;
    if (offset === 0) return 1;
    if ("._/- ".includes(normalized[offset - 1])) return 2;
    return 3;
  }

  function encodedPath(path) {
    return String(path).split("/").map(encodeURIComponent).join("/");
  }

  function sourceUrl(path, line) {
    const repository = String(searchIndex.repository)
      .split("/").map(encodeURIComponent).join("/");
    const commit = encodeURIComponent(String(searchIndex.commit));
    const anchor = line === null ? "" : `#L${Number(line)}`;
    return `https://github.com/${repository}/blob/${commit}/${encodedPath(path)}${anchor}`;
  }

  function addMatch(matches, order, typeRank, kind, label, context, path, line, query) {
    const score = matchScore(label, query);
    if (score === null) return order;
    matches.push({score, order, typeRank, kind, label, context, path, line});
    return order + 1;
  }

  function collectMatches(index, query) {
    const matches = [];
    let order = 0;
    for (const record of index.modules) {
      order = addMatch(
        matches, order, 0, "Module", record.m, record.p,
        record.p, null, query
      );
      for (const declaration of record.d) {
        order = addMatch(
          matches, order, 1, declaration[0], declaration[1], record.m,
          record.p, declaration[2], query
        );
      }
      for (const imported of record.i) {
        order = addMatch(
          matches, order, 2, "Import", imported, `Imported by ${record.m}`,
          record.p, null, query
        );
      }
      for (const artifact of record.a) {
        order = addMatch(
          matches, order, 3, "Roadmap artifact", artifact[0],
          `${artifact[1]} · ${artifact[2]} · ${record.m}`,
          record.p, null, query
        );
      }
    }
    matches.sort((left, right) =>
      left.score - right.score ||
      left.typeRank - right.typeRank ||
      compareText(normalize(left.label), normalize(right.label)) ||
      compareText(normalize(left.context), normalize(right.context)) ||
      left.order - right.order
    );
    return matches;
  }

  if (typeof module !== "undefined" && module.exports) {
    module.exports = {collectMatches, matchScore, MAX_QUERY_LENGTH, RESULT_LIMIT};
  }
  if (typeof document === "undefined") return;

  const input = document.getElementById("source-search");
  const status = document.getElementById("source-search-status");
  const results = document.getElementById("source-search-results");
  if (!(input instanceof HTMLInputElement) || !status || !results) return;

  let searchIndex = null;
  let framePending = false;
  const number = (value) => new Intl.NumberFormat("en-US").format(value);

  function renderResult(match) {
    const item = document.createElement("li");
    item.className = "search-result";
    const kind = document.createElement("span");
    kind.className = "search-kind";
    kind.textContent = match.kind;
    const link = document.createElement("a");
    link.href = sourceUrl(match.path, match.line);
    link.textContent = match.label;
    const context = document.createElement("span");
    context.className = "search-context";
    context.textContent = match.context;
    item.append(kind, link, context);
    return item;
  }

  function render() {
    framePending = false;
    if (!searchIndex) return;
    const query = normalize(input.value.trim()).slice(0, MAX_QUERY_LENGTH);
    results.replaceChildren();
    if (!query) {
      status.textContent = `Search ${number(searchIndex.totals.entries)} names across ` +
        `${number(searchIndex.totals.modules)} modules. Results are limited to ` +
        `${RESULT_LIMIT}; query length is limited to ${MAX_QUERY_LENGTH} characters.`;
      return;
    }
    const matches = collectMatches(searchIndex, query);
    const visible = matches.slice(0, RESULT_LIMIT);
    results.append(...visible.map(renderResult));
    const capped = matches.length > RESULT_LIMIT
      ? ` Showing the first ${RESULT_LIMIT}.`
      : "";
    status.textContent = `${number(matches.length)} matching entries; ` +
      `query ${query.length}/${MAX_QUERY_LENGTH} characters.${capped}`;
  }

  function scheduleRender() {
    if (framePending) return;
    framePending = true;
    window.requestAnimationFrame(render);
  }

  input.addEventListener("input", scheduleRender);
  fetch("data/search.json")
    .then((response) => {
      if (!response.ok) throw new Error(`HTTP ${response.status}`);
      return response.json();
    })
    .then((value) => {
      searchIndex = value;
      input.disabled = false;
      render();
    })
    .catch(() => {
      status.textContent = "Search could not load. The complete JSON index remains available.";
    });
})();'''


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


def module_rows(modules: list[dict[str, object]], include_roadmap: bool) -> str:
    """Render source inventory rows with optional canonical-ledger links."""

    rows: list[str] = []
    for module in modules:
        assert isinstance(module, dict)
        declarations = module["declarations"]
        imports = module["imports"]
        assert isinstance(declarations, list)
        assert isinstance(imports, list)
        roadmap_cell = ""
        if include_roadmap:
            raw_links = module["roadmap_artifacts"]
            assert isinstance(raw_links, list)
            rendered_links = "".join(
                f'<span class="roadmap-ref"><code>{html.escape(str(raw_link["artifact_name"]))}</code> '
                f'<span class="state">{html.escape(str(raw_link["artifact_state"]))} · '
                f'{html.escape(str(raw_link["node_id"]))}</span></span>'
                for raw_link in sorted(
                    raw_links,
                    key=lambda link: (str(link["node_id"]), str(link["artifact_name"])),
                )
                if isinstance(raw_link, dict)
            )
            roadmap_cell = f"<td>{rendered_links}</td>"
        rows.append(
            "<tr>"
            f'<td><a href="{html.escape(str(module["source_url"]))}"><code>'
            f'{html.escape(str(module["module"]))}</code></a></td>'
            f'<td class="num">{int(module["lines"]):,}</td>'
            f'<td class="num">{len(declarations):,}</td>'
            f'<td class="num">{len(imports):,}</td>'
            f"{roadmap_cell}"
            "</tr>"
        )
    return "".join(rows)


def module_table(modules: list[dict[str, object]], include_roadmap: bool) -> str:
    """Render one module table."""

    roadmap_header = "<th>Roadmap artifacts</th>" if include_roadmap else ""
    return (
        '<div class="wide-table"><table><thead><tr><th>Module</th>'
        "<th>Lines</th><th>Declarations</th><th>Imports</th>"
        f"{roadmap_header}</tr></thead><tbody>"
        f"{module_rows(modules, include_roadmap)}</tbody></table></div>"
    )


def certificate_family_table(modules: list[dict[str, object]]) -> str:
    """Summarize cache-heavy internals without emitting thousands of rows."""

    families: dict[str, list[dict[str, object]]] = {}
    for module in modules:
        family = module.get("cache_heavy_family")
        if not isinstance(family, str):
            raise TypeError("certificate-envelope module has no cache family")
        families.setdefault(family, []).append(module)
    rows = "".join(
        "<tr>"
        f"<td><code>{html.escape(family)}*</code></td>"
        f'<td class="num">{len(family_modules):,}</td>'
        f'<td class="num">{sum(int(module["lines"]) for module in family_modules):,}</td>'
        f'<td class="num">{sum(len(module["declarations"]) for module in family_modules):,}</td>'
        f'<td class="num">{sum(len(module["imports"]) for module in family_modules):,}</td>'
        "</tr>"
        for family, family_modules in sorted(families.items())
    )
    return (
        '<div class="wide-table"><table><thead><tr><th>Cache-heavy family</th>'
        "<th>Modules</th><th>Lines</th><th>Declarations</th><th>Imports</th>"
        f"</tr></thead><tbody>{rows}</tbody></table></div>"
    )


def exposition_page(index: dict[str, object]) -> str:
    """Build the module inventory page."""

    raw_modules = index["modules"]
    assert isinstance(raw_modules, list)
    modules = [module for module in raw_modules if isinstance(module, dict)]
    grouped = {
        group_id: [
            module for module in modules if module["navigation_group"] == group_id
        ]
        for group_id, _, _ in NAVIGATION_GROUPS
    }
    group_cards = "".join(
        f'<div class="card"><span class="metric">{len(grouped[group_id]):,}</span>'
        f'<span class="label">{html.escape(label)}</span></div>'
        for group_id, label, _ in NAVIGATION_GROUPS
    )
    roadmap_modules = grouped["roadmap"]
    supporting_modules = grouped["supporting"]
    certificate_modules = grouped["certificate-envelope"]
    totals = index["totals"]
    assert isinstance(totals, dict)
    mapped_artifacts = int(totals["mapped_roadmap_artifacts"])
    roadmap_artifacts = int(totals["roadmap_artifacts"])
    return f"""<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport"
content="width=device-width,initial-scale=1"><title>Source exposition · Mazur Theorem</title>
<link rel="stylesheet" href="../assets/site.css"></head><body><main>
<p class="eyebrow">Machine-generated inventory</p>
<h1>Source exposition</h1>
<p class="lede">A commit-pinned map from canonical roadmap artifacts to checked
Lean modules. Complete declaration, import, roadmap-state, and cache-partition
metadata is available in <a href="data/index.json">JSON</a>.</p>
<nav><a href="../">Overview</a><a href="../blueprint/">Blueprint</a>
<a href="../docs/">API documentation</a></nav>
<section class="grid">{group_cards}</section>
<section class="search-panel" aria-labelledby="source-search-heading">
<h2 id="source-search-heading">Search every source name</h2>
<p class="section-note">Search all {int(totals["modules"]):,} modules,
declaration names, import names, and mapped roadmap artifacts. This includes
the cache-heavy modules collapsed in the tables below.</p>
<label class="search-label" for="source-search">Module, declaration, import,
or roadmap artifact</label>
<input class="search-input" id="source-search" type="search" maxlength="120"
autocomplete="off" spellcheck="false" aria-controls="source-search-results"
aria-describedby="source-search-status" disabled>
<p class="search-status" id="source-search-status" role="status"
aria-live="polite">Loading the compact search index…</p>
<ol class="search-results" id="source-search-results"></ol>
</section>
<h2>Roadmap-linked modules</h2>
<p class="section-note">These modules are named by canonical artifacts in
<code>coordination/program.json</code>. States shown here are artifact states,
not inferred from source text. {mapped_artifacts:,} of {roadmap_artifacts:,}
artifacts currently record an indexed local module; proposed artifacts without
a module remain visible in the complete JSON roadmap index.</p>
{module_table(roadmap_modules, include_roadmap=True)}
<details><summary>{len(supporting_modules):,} supporting modules</summary>
<p class="section-note">Checked support modules not named directly by a
canonical ledger artifact.</p>
{module_table(supporting_modules, include_roadmap=False)}
</details>
<details><summary>{len(certificate_modules):,} cache-heavy certificate modules</summary>
<p class="section-note">The existing cache policy assigns these internals to
the specialized generated-proof partition. They are collapsed only in this
human view; every module, path, import, and declaration remains in the
<a href="data/index.json">JSON index</a>.</p>
{certificate_family_table(certificate_modules)}
</details>
<script src="assets/search.js" defer></script>
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
        "exposition/assets/search.js",
        "exposition/data/index.json",
        "exposition/data/search.json",
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
    module_names = {module.get("module") for module in data.get("modules", [])}
    if None in module_names or len(module_names) != len(data.get("modules", [])):
        raise RuntimeError("generated exposition module names are not unique")
    roadmap = data.get("roadmap")
    if not isinstance(roadmap, dict) or not isinstance(roadmap.get("nodes"), list):
        raise RuntimeError("generated exposition roadmap index is missing")
    for module in data.get("modules", []):
        if module.get("cache_partition") not in CACHE_PARTITION_LABELS:
            raise RuntimeError("generated exposition cache partition is invalid")
        if module.get("navigation_group") not in {
            group_id for group_id, _, _ in NAVIGATION_GROUPS
        }:
            raise RuntimeError("generated exposition navigation group is invalid")
    search = json.loads(
        (output_root / "exposition/data/search.json").read_text(encoding="utf-8")
    )
    if search != compact_search_index(data):
        raise RuntimeError("generated compact search index is inconsistent")
    javascript = (output_root / "exposition/assets/search.js").read_text(
        encoding="utf-8"
    )
    if ".innerHTML" in javascript or "textContent" not in javascript:
        raise RuntimeError("generated search must render results as DOM text")


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

    modules: list[dict[str, object]] = [
        scan_module(repository_root, path, repository, commit)
        for path in source_files(repository_root)
    ]
    modules_by_name = {str(module["module"]): module for module in modules}
    if len(modules_by_name) != len(modules):
        raise ValueError("source scanner produced duplicate module names")
    programme = load_json_object(repository_root / PROGRAMME_PATH)
    roadmap_nodes, roadmap_links = roadmap_metadata(programme, modules_by_name)
    partitions, heavy_families = cache_partitions(
        repository_root, modules_by_name
    )
    for name, module in modules_by_name.items():
        module["roadmap_artifacts"] = roadmap_links[name]
        module["cache_partition"] = partitions[name]
        module["cache_partition_label"] = CACHE_PARTITION_LABELS[partitions[name]]
        if name in heavy_families:
            module["cache_heavy_family"] = heavy_families[name]
        module["navigation_group"] = navigation_group(module)

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
        "roadmap_nodes": len(roadmap_nodes),
        "roadmap_artifacts": sum(
            len(node["artifacts"])  # type: ignore[arg-type]
            for node in roadmap_nodes
        ),
        "mapped_roadmap_artifacts": sum(len(links) for links in roadmap_links.values()),
    }
    navigation = [
        {
            "id": group_id,
            "label": label,
            "description": description,
            "modules": sum(
                module["navigation_group"] == group_id for module in modules
            ),
            "lines": sum(
                int(module["lines"])
                for module in modules
                if module["navigation_group"] == group_id
            ),
        }
        for group_id, label, description in NAVIGATION_GROUPS
    ]
    index: dict[str, object] = {
        "schema_version": 2,
        "repository": repository,
        "commit": commit,
        "roadmap_url": roadmap_url,
        "roadmap": {
            "source": PROGRAMME_PATH.as_posix(),
            "schema_version": programme.get("schema_version"),
            "nodes": roadmap_nodes,
        },
        "cache_policy_source": CACHE_POLICY_PATH.as_posix(),
        "cache_partitions": CACHE_PARTITION_LABELS,
        "navigation_groups": navigation,
        "totals": totals,
        "modules": modules,
    }
    search_index = compact_search_index(index)

    if output_root.exists() and not (output_root / OUTPUT_SENTINEL).is_file():
        raise RuntimeError(
            f"refusing to replace non-generator directory: {output_root}"
        )
    if output_root.exists():
        shutil.rmtree(output_root)
    (output_root / "assets").mkdir(parents=True)
    (output_root / "exposition/assets").mkdir(parents=True)
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
    (output_root / "exposition/assets/search.js").write_text(
        search_javascript() + "\n", encoding="utf-8"
    )
    (output_root / "exposition/data/index.json").write_text(
        json.dumps(index, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (output_root / "exposition/data/search.json").write_text(
        json.dumps(
            search_index,
            ensure_ascii=False,
            separators=(",", ":"),
            sort_keys=True,
        )
        + "\n",
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

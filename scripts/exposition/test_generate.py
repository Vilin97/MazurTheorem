#!/usr/bin/env python3
"""Focused tests for the lightweight Lean source exposition generator."""

from __future__ import annotations

import json
import subprocess
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from generate import (
    compact_search_index,
    navigation_group,
    roadmap_metadata,
    scan_imports,
    search_javascript,
    strip_comments_and_strings,
)


class ImportScannerTests(unittest.TestCase):
    def test_plain_public_meta_and_all_imports(self) -> None:
        source = """
module
import Alpha.One
public import Beta.Two
import all Gamma.Three
meta import Delta.Four
public meta import Epsilon.Five
meta import all Zeta.Six
"""
        self.assertEqual(
            scan_imports(source),
            [
                "Alpha.One",
                "Beta.Two",
                "Gamma.Three",
                "Delta.Four",
                "Epsilon.Five",
                "Zeta.Six",
            ],
        )

    def test_rejects_multiple_modules_on_one_import(self) -> None:
        self.assertEqual(scan_imports("import Alpha.One Beta.Two\n"), [])

    def test_masked_noncommands_do_not_match(self) -> None:
        source = """
-- public import Commented.Out
/- import Blocked.Out -/
def prose := "import String.Out"
public import Visible.Module
"""
        self.assertEqual(
            scan_imports(strip_comments_and_strings(source)), ["Visible.Module"]
        )


class RoadmapMetadataTests(unittest.TestCase):
    def setUp(self) -> None:
        self.modules = {
            "Checked.Module": {
                "module": "Checked.Module",
                "path": "Checked/Module.lean",
                "source_url": "https://example.test/Checked/Module.lean",
            }
        }
        self.programme = {
            "nodes": [
                {
                    "id": "MT-TEST",
                    "title": "Test node",
                    "status": "blocked",
                    "stage": "foundations",
                    "artifacts": [
                        {
                            "name": "Checked.Module.endpoint",
                            "kind": "theorem",
                            "state": "contract",
                            "module": "Checked.Module",
                        },
                        {
                            "name": "Future.endpoint",
                            "kind": "theorem",
                            "state": "proposed",
                        },
                    ],
                }
            ]
        }

    def test_joins_only_recorded_modules(self) -> None:
        nodes, links = roadmap_metadata(self.programme, self.modules)
        artifacts = nodes[0]["artifacts"]
        self.assertEqual(artifacts[0]["module_path"], "Checked/Module.lean")
        self.assertNotIn("module", artifacts[1])
        self.assertEqual(links["Checked.Module"][0]["artifact_state"], "contract")

    def test_rejects_unknown_recorded_module(self) -> None:
        self.programme["nodes"][0]["artifacts"][0]["module"] = "Missing.Module"
        with self.assertRaisesRegex(ValueError, "unindexed source Missing.Module"):
            roadmap_metadata(self.programme, self.modules)


class NavigationTests(unittest.TestCase):
    def test_roadmap_link_takes_precedence_over_cache_envelope(self) -> None:
        module = {
            "roadmap_artifacts": [{"node_id": "MT-TEST"}],
            "cache_partition": "specialized-heavy",
        }
        self.assertEqual(navigation_group(module), "roadmap")

    def test_unlinked_heavy_module_is_collapsed(self) -> None:
        module = {
            "roadmap_artifacts": [],
            "cache_partition": "specialized-heavy",
        }
        self.assertEqual(navigation_group(module), "certificate-envelope")


class SearchIndexTests(unittest.TestCase):
    def setUp(self) -> None:
        self.index = {
            "repository": "Owner/Repository",
            "commit": "0123456789abcdef",
            "modules": [
                {
                    "module": "Checked.Module",
                    "path": "Checked/Module.lean",
                    "navigation_group": "roadmap",
                    "declarations": [
                        {
                            "kind": "theorem",
                            "name": "checked_endpoint",
                            "line": 17,
                            "source_url": "https://example.test/source#L17",
                        }
                    ],
                    "imports": ["Support.Module"],
                    "roadmap_artifacts": [
                        {
                            "artifact_name": "Checked.Module.checked_endpoint",
                            "node_id": "MT-TEST",
                            "artifact_state": "contract",
                        }
                    ],
                },
                {
                    "module": "Heavy.Collapsed.Module",
                    "path": "Heavy/Collapsed/Module.lean",
                    "navigation_group": "certificate-envelope",
                    "declarations": [
                        {
                            "kind": "def",
                            "name": "hidden_certificate_term",
                            "line": 9,
                            "source_url": "https://example.test/heavy#L9",
                        }
                    ],
                    "imports": ["Heavy.Foundation"],
                    "roadmap_artifacts": [],
                },
            ],
        }

    def test_covers_all_searchable_names_including_collapsed_modules(self) -> None:
        search = compact_search_index(self.index)
        self.assertEqual(search["totals"]["modules"], 2)
        self.assertEqual(search["totals"]["entries"], 7)
        self.assertEqual(
            [record["m"] for record in search["modules"]],
            ["Checked.Module", "Heavy.Collapsed.Module"],
        )
        self.assertEqual(search["modules"][0]["d"][0][1], "checked_endpoint")
        self.assertEqual(search["modules"][0]["i"], ["Support.Module"])
        self.assertEqual(
            search["modules"][0]["a"][0][0],
            "Checked.Module.checked_endpoint",
        )
        self.assertEqual(
            search["modules"][1]["d"][0][1], "hidden_certificate_term"
        )

    def test_projection_omits_repeated_source_urls(self) -> None:
        encoded = json.dumps(compact_search_index(self.index), sort_keys=True)
        self.assertNotIn("source_url", encoded)
        self.assertNotIn("https://example.test", encoded)

    def test_browser_search_is_bounded_and_uses_safe_dom_text(self) -> None:
        javascript = search_javascript()
        self.assertIn("const RESULT_LIMIT = 100", javascript)
        self.assertIn("const MAX_QUERY_LENGTH = 120", javascript)
        self.assertIn("textContent", javascript)
        self.assertIn("replaceChildren", javascript)
        self.assertNotIn(".innerHTML", javascript)
        self.assertNotIn("data/index.json", javascript)

    def test_node_executes_search_logic_across_every_entry_kind(self) -> None:
        search = compact_search_index(self.index)
        assertions = f"""
const assert = require("node:assert/strict");
const api = module.exports;
const index = {json.dumps(search, separators=(",", ":"))};
assert.equal(api.RESULT_LIMIT, 100);
assert.equal(api.MAX_QUERY_LENGTH, 120);
assert.equal(api.collectMatches(index, "heavy.collapsed.module")[0].kind, "Module");
assert.equal(api.collectMatches(index, "hidden_certificate_term")[0].kind, "def");
assert.equal(api.collectMatches(index, "support.module")[0].kind, "Import");
assert.equal(
  api.collectMatches(index, "checked.module.checked_endpoint")[0].kind,
  "Roadmap artifact"
);
"""
        result = subprocess.run(
            ["node"],
            input=search_javascript() + "\n" + assertions,
            text=True,
            capture_output=True,
            check=False,
            timeout=10,
        )
        self.assertEqual(result.returncode, 0, result.stderr)


if __name__ == "__main__":
    unittest.main()

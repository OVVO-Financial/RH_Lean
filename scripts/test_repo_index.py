#!/usr/bin/env python3
"""Regression tests for occurrence identity, imports, search, refs and freshness."""

import os
import tempfile
import unittest
from pathlib import Path

import repo_index as index


class RepositoryIndexTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.git("init", "-q")
        self.git("config", "user.name", "Index Test")
        self.git("config", "user.email", "index-test@example.invalid")
        self.write(".gitignore", "repo-index.json\n")
        self.write("lakefile.lean", "import Lake\n")
        self.write("RHLean/Base.lean", "namespace Shared\n@[simp] theorem duplicate : True := by trivial\nend Shared\n")
        self.write("research/Child.lean", "import RHLean.Base\nnamespace Shared\n/-- a unique documentation needle -/\ntheorem duplicate : True := by trivial\ntheorem deepStatement\n    (h : True) :\n    True := by\n  have proofBodyNeedle := h\n  exact proofBodyNeedle\nend Shared\n")
        self.write("research/Parent.lean", "/- import research.Fake /- nested -/ -/\nimport «research.Child» RHLean.Base\nnamespace Test\ndef parent := True\nend Test\n")
        self.write("export_test/lakefile.lean", "import Lake\n")
        self.write("export_test/RHLean/Base.lean", "namespace Shared\ntheorem duplicate : True := by trivial\nend Shared\n")
        self.write("export_test/RHLean/Consumer.lean", "import RHLean.Base\n")
        self.write("docs/Route.md", "# Route\nSigned boundary and reciprocal contraction.\n")
        self.write("scripts/probe.py", "print('numerical diagnostic needle')\n")
        self.git("add", ".")
        self.git("commit", "-qm", "initial sources")

    def git(self, *args):
        return index.git(self.root, *args).decode().strip()

    def write(self, path, text):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)

    def build(self, refs=()):
        return index.build_index(index.snapshots(self.root, list(refs)))

    def test_occurrences_are_not_merged_by_name(self):
        data = self.build()
        twins = [d for d in data["declarations"] if d["name"] == "Shared.duplicate"]
        self.assertEqual(len(twins), 3)
        self.assertEqual(len({d["id"] for d in twins}), 3)
        self.assertEqual({data["files"][d["file_id"]]["scope"] for d in twins}, {"library", "research", "exports"})

    def test_quoted_multiple_imports_and_export_isolation(self):
        data = self.build()
        edges = data["module_import_graph"]
        self.assertEqual(edges["worktree:.:research.Parent"], ["worktree:.:RHLean.Base", "worktree:.:research.Child"])
        self.assertEqual(edges["worktree:export_test:RHLean.Consumer"], ["worktree:export_test:RHLean.Base"])
        self.assertEqual(data["cyclic_components"], [])
        self.assertEqual(index.imports_from('def text := "\nimport Fake\n"'), [])
        self.assertEqual(index.imports_from("-- import Fake\nimport A B -- trailing comment\n"), ["A", "B"])

    def test_full_source_documentation_and_evidence_lines(self):
        data = self.build()
        hits = index.search(data, "proofBodyNeedle", kind="declaration", scope="research")
        self.assertEqual([h["name"] for h in hits], ["Shared.deepStatement"])
        self.assertEqual(hits[0]["line"], 8)
        docs = index.search(data, "unique documentation needle", kind="declaration")
        self.assertEqual([h["name"] for h in docs], ["Shared.duplicate"])
        self.assertEqual(docs[0]["line"], 4)
        self.assertIn("attached doc", docs[0]["evidence"])
        self.assertEqual(index.search(data, "reciprocal signed", scope="docs")[0]["path"], "docs/Route.md")
        self.assertEqual(index.search(data, r"proofBodyN\w+", regex=True, kind="declaration")[0]["line"], 8)

    def test_content_changes_invalidate_even_with_preserved_mtime(self):
        data = self.build()
        cache = self.root / "repo-index.json"
        index.write_json(cache, data)
        source = self.root / "research/Child.lean"
        stamp = source.stat().st_mtime_ns
        self.write("research/Child.lean", source.read_text() + "-- changed\n")
        os.utime(source, ns=(stamp, stamp))
        with self.assertRaisesRegex(ValueError, "stale index"):
            index.load_index(self.root, cache, [])
        fresh = index.load_index(self.root, None, [])
        self.assertNotEqual(data["input_fingerprint"], fresh["input_fingerprint"])

    def test_new_research_facets_are_searchable(self):
        self.write("research/VF_MID_SECTOR_SIX_OWNER_TWO.lean", "theorem vfMidSectorSixOwnerTwoValue : (1 : Nat) = 1 := rfl\n")
        data = self.build()
        for carrier in ("vf-mid", "sector-six", "owner-two"):
            hits = index.search(data, "Value", scope="research", carrier=carrier, role="exact-equality")
            self.assertEqual([h["name"] for h in hits], ["vfMidSectorSixOwnerTwoValue"])
            self.assertTrue(hits[0]["dirty"])
            self.assertEqual(len(hits[0]["source_sha256"]), 64)

    def test_statement_beyond_preview_length_is_searchable(self):
        self.write("research/Long.lean", "theorem longStatement\n    -- " + "padding " * 150 + "\n    (longStatementNeedle : True) : True := by exact longStatementNeedle\n")
        data = self.build()
        declaration = next(d for d in data["declarations"] if d["name"] == "longStatement")
        self.assertGreater(declaration["statement"].index("longStatementNeedle"), 700)
        hits = index.search(data, "longStatementNeedle", kind="declaration")
        self.assertEqual([h["name"] for h in hits], ["longStatement"])

    def test_pr_ref_has_commit_provenance_without_checkout(self):
        self.git("branch", "pr-source")
        self.write("research/OnlyOnPR.lean", "theorem branchOnlyNeedle : True := by trivial\n")
        self.git("add", ".")
        self.git("commit", "-qm", "add PR source")
        self.git("branch", "-f", "pr-source", "HEAD")
        self.git("reset", "--hard", "HEAD~1")
        head = self.git("rev-parse", "HEAD")
        data = self.build(["pr-source"])
        hits = index.search(data, "branchOnlyNeedle", kind="declaration")
        self.assertEqual(len(hits), 1)
        self.assertEqual(hits[0]["view"], "pr-source")
        self.assertEqual(hits[0]["commit"], self.git("rev-parse", "pr-source"))
        self.assertEqual(self.git("rev-parse", "HEAD"), head)
        self.assertFalse((self.root / "research/OnlyOnPR.lean").exists())
        cache = self.root / "repo-index.json"
        index.write_json(cache, data)
        self.git("branch", "-f", "pr-source", "HEAD")
        with self.assertRaisesRegex(ValueError, "stale index"):
            index.load_index(self.root, cache, [])

    def test_cycles_and_omissions_are_reported(self):
        self.write("research/A.lean", "import research.B\n")
        self.write("research/B.lean", "import research.A\n")
        (self.root / "docs/binary.txt").write_bytes(b"a\0b")
        data = self.build()
        self.assertEqual(len(data["cyclic_components"]), 1)
        self.assertEqual(data["omitted"][0]["path"], "docs/binary.txt")
        self.assertIn("Import cycles: 1", index.report(data))
        with self.assertRaisesRegex(ValueError, "empty"):
            index.search(data, " ")

    def test_invalid_filters_and_refs_fail_clearly(self):
        data = self.build()
        for options in ({"carrier": "typo"}, {"role": "typo"}, {"view": "not-indexed"}, {"kind": "file", "carrier": "vf-mid"}):
            with self.assertRaises(ValueError):
                index.search(data, "True", **options)
        with self.assertRaises(ValueError):
            self.build(["not-a-fetched-ref"])

    def test_ignored_generated_outputs_do_not_enter_the_corpus(self):
        before = self.build()
        self.write("repo-index.json", "{\"generated\": true}\n")
        after = self.build()
        self.assertNotIn("worktree:repo-index.json", after["files"])
        self.assertEqual(before["input_fingerprint"], after["input_fingerprint"])


if __name__ == "__main__":
    unittest.main()

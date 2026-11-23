#!/usr/bin/env python3
"""Regression tests for Lean source names and strict exact-graph coverage."""

import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import decl_graph
import rhlean_kg as kg


class DeclarationScopeTests(unittest.TestCase):
    def parse(self, source):
        return kg.parse_module(Path("RHLean/ScopeFixture.lean"), source)

    def test_rooted_declaration_names_bypass_current_namespace(self):
        declarations = self.parse("""\
namespace Current.Nested
theorem _root_.Export.result : True := by trivial
theorem relative.result : True := by trivial
end Current.Nested
""")
        self.assertEqual(
            [declaration.name for declaration in declarations],
            ["Export.result", "Current.Nested.relative.result"],
        )
        # Naming a declaration at the root does not change its body scope.
        self.assertEqual(declarations[0].namespace, "Current.Nested")
        self.assertEqual(declarations[0].line, 2)

    def test_noncomputable_section_does_not_close_enclosing_namespace(self):
        declarations = self.parse("""\
namespace Outer
open Kept
noncomputable section
open Temporary
def inside : Nat := 1
section Inner
def nested : Nat := inside
end Inner
end
theorem after : inside = inside := rfl
namespace Child
def child : Nat := inside
end Child
def last : Nat := inside
end Outer
def root : Nat := 0
""")
        self.assertEqual(
            [declaration.name for declaration in declarations],
            ["Outer.inside", "Outer.nested", "Outer.after", "Outer.Child.child",
             "Outer.last", "root"],
        )
        self.assertEqual(declarations[0].opens, ("Kept", "Temporary"))
        self.assertEqual(declarations[2].opens, ("Kept",))
        self.assertEqual(declarations[-1].opens, ())

    def test_rooted_references_bypass_namespace_shadowing(self):
        declarations = self.parse("""\
namespace Export
def result : Nat := 1
end Export
namespace Scope
namespace Export
def result : Nat := 2
end Export
def rooted : Nat := _root_.Export.result
def relative : Nat := Export.result
end Scope
""")
        table = kg.NameTable(declarations)
        kg.resolve_references(declarations, table)
        by_name = {declaration.name: declaration for declaration in declarations}
        self.assertEqual(by_name["Scope.rooted"].proof_refs, ["Export.result"])
        self.assertEqual(by_name["Scope.relative"].proof_refs, ["Scope.Export.result"])


class ElaboratedCoverageTests(unittest.TestCase):
    SOURCE = """\
namespace Scope
noncomputable section
theorem inside : True := by trivial
end
theorem after : True := inside
theorem _root_.Export.result : True := after
end Scope
"""
    NAMES = ("Scope.inside", "Scope.after", "Export.result")

    def ingest(self, names):
        # Synthetic extractor records exercise name matching, not kernel validity.
        records = [
            {"name": name, "module": "RHLean.ScopeFixture", "kind": "theorem",
             "typeRefs": [], "valueRefs": []}
            for name in names
        ]
        with tempfile.TemporaryDirectory() as temp:
            jsonl = Path(temp) / "declarations.jsonl"
            jsonl.write_text(
                "".join(json.dumps(record) + "\n" for record in records),
                encoding="utf-8",
            )
            with patch.object(kg, "load_sources", return_value=[
                (Path("RHLean/ScopeFixture.lean"), self.SOURCE),
            ]), patch.object(kg, "load_facets", return_value={"facets": {}, "roles": {}}):
                return decl_graph.build_graph_from_lean(jsonl)

    def test_exact_graph_retains_every_normalized_source_declaration(self):
        graph = self.ingest(self.NAMES)
        self.assertEqual(set(graph["declarations"]), set(self.NAMES))
        self.assertEqual(graph["stats"]["declarations"], 3)
        self.assertEqual(graph["stats"]["named_proofs"], 3)

    def test_exact_graph_still_rejects_a_missing_source_declaration(self):
        with self.assertRaisesRegex(ValueError, "missing 1 source declarations: Export.result"):
            self.ingest(self.NAMES[:-1])


if __name__ == "__main__":
    unittest.main()

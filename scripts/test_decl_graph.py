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


class PropositionClosureTests(unittest.TestCase):
    """Status regressions; synthetic extractor records are not Lean receipts."""

    def graph(self, source, elaborated):
        path = Path("RHLean/ClosureFixture.lean")
        with patch.object(kg, "load_sources", return_value=[(path, source)]), \
                patch.object(kg, "load_facets", return_value={"facets": {}, "roles": {}}):
            if not elaborated:
                return decl_graph.build_graph()["declarations"]
            declarations, _ = kg.build_declarations()
            records = [
                {"name": d.name, "module": d.module,
                 "kind": "inductive" if d.kind == "structure" else d.kind,
                 "typeRefs": d.statement_refs, "valueRefs": d.proof_refs}
                for d in declarations
            ]
            with tempfile.TemporaryDirectory() as temp:
                jsonl = Path(temp) / "declarations.jsonl"
                jsonl.write_text("".join(json.dumps(r) + "\n" for r in records))
                return decl_graph.build_graph_from_lean(jsonl)["declarations"]

    def test_restatement_retains_premise_in_binders_and_arrows(self):
        for elaborated in (False, True):
            for statement in (
                "theorem reuse (h : P) : P := h",
                "theorem reuse {h : P} : P := h",
                "theorem reuse : P → P := fun h => h",
            ):
                with self.subTest(elaborated=elaborated, statement=statement):
                    nodes = self.graph("def P : Prop := False\n" + statement, elaborated)
                    self.assertEqual(nodes["P"]["status"], kg.STATUS_OPEN)
                    self.assertEqual(nodes["reuse"]["hypothesis_refs"], ["P"])
                    self.assertEqual(nodes["reuse"]["conclusion_refs"], ["P"])
                    self.assertEqual(nodes["reuse"]["closed_assumes"], ["P"])
                    self.assertEqual(nodes["reuse"]["status"], kg.STATUS_REDUCED)

    def test_mentions_in_tautological_conclusions_do_not_prove_p(self):
        source = """\
def P : Prop := False
theorem equality : P = P := rfl
theorem disjunction : P ∨ True := Or.inr trivial
theorem quantified : ∀ (h : P), P := fun h => h
theorem parenthesized : (P → P) := fun h => h
"""
        for elaborated in (False, True):
            with self.subTest(elaborated=elaborated):
                nodes = self.graph(source, elaborated)
                self.assertEqual(nodes["P"]["status"], kg.STATUS_OPEN)
                for name in ("equality", "disjunction", "quantified", "parenthesized"):
                    self.assertNotIn("establishes_prop", nodes[name])

    def test_unconditional_proof_and_named_premise_propagation(self):
        source = """\
def A : Prop := True
def B : Prop := A
def C : Prop := B
theorem seed : A := trivial
theorem step (h : A) : B := h
theorem arrow : B → C := fun h => h
"""
        for elaborated in (False, True):
            with self.subTest(elaborated=elaborated):
                nodes = self.graph(source, elaborated)
                for name in ("A", "B", "C", "seed", "step", "arrow"):
                    self.assertEqual(nodes[name]["status"], kg.STATUS_PROVED)
                self.assertEqual(nodes["step"]["closed_assumes"], ["A"])

    def test_exact_equivalence_needs_an_independent_seed(self):
        source = """\
def A : Prop := True
def B : Prop := A
theorem transport : A ↔ B := Iff.rfl
"""
        for elaborated in (False, True):
            for seeded in (False, True):
                with self.subTest(elaborated=elaborated, seeded=seeded):
                    nodes = self.graph(source + ("theorem seed : A := trivial\n" if seeded else ""), elaborated)
                    for name in ("A", "B"):
                        self.assertEqual(nodes[name]["status"], kg.STATUS_PROVED if seeded else kg.STATUS_OPEN)

    def test_named_universe_arguments_preserve_premise_propagation(self):
        source = """\
universe u v
def A : Prop := ∀ (α : Sort u) (x : α), x = x
def B : Prop := ∀ (α : Sort u) (_β : Sort v) (x : α), x = x
theorem seed : A.{u} := fun _ _ => rfl
theorem step (h : A.{u}) : B.{u, v} := fun α _ x => h α x
"""
        for elaborated in (False, True):
            with self.subTest(elaborated=elaborated):
                nodes = self.graph(source, elaborated)
                self.assertEqual(nodes["B"]["status"], kg.STATUS_PROVED)
                self.assertEqual(nodes["step"]["closed_assumes"], ["A"])

    def test_false_empty_data_and_external_premises_block_closure(self):
        cases = (
            "def P : Prop := False\ntheorem escape (h : False) : P := h",
            "def P : Prop := False\ntheorem escape (i : Fin 0) : P := Fin.elim0 i",
            "def P : Prop := RiemannHypothesis\ntheorem escape (h : RiemannHypothesis) : P := h",
            "opaque Hidden : Prop := False\ndef P : Prop := Hidden\ntheorem escape (h : Hidden) : P := h",
            "def P : Prop := False\nstructure Certificate where\n  proof : P\ntheorem escape (c : Certificate) : P := c.proof",
        )
        for elaborated in (False, True):
            for source in cases:
                with self.subTest(elaborated=elaborated, source=source):
                    nodes = self.graph(source, elaborated)
                    self.assertEqual(nodes["P"]["status"], kg.STATUS_OPEN)
                    self.assertTrue(nodes["escape"]["hard_blocked"])
                    self.assertNotIn("establishes_prop", nodes["escape"])

    def test_conditional_refutation_waits_for_its_premise(self):
        source = """\
def A : Prop := True
def P : Prop := False
theorem notP (h : A) : ¬ P := fun p => p
"""
        for elaborated in (False, True):
            for seeded in (False, True):
                with self.subTest(elaborated=elaborated, seeded=seeded):
                    nodes = self.graph(source + ("theorem seed : A := trivial\n" if seeded else ""), elaborated)
                    self.assertEqual(nodes["P"]["status"], kg.STATUS_REFUTED if seeded else kg.STATUS_OPEN)
            nodes = self.graph("def P : Prop := True\ntheorem notP (h : False) : ¬ P := False.elim h", elaborated)
            self.assertEqual(nodes["P"]["status"], kg.STATUS_OPEN)
            self.assertTrue(nodes["notP"]["hard_blocked"])

    def test_unconditional_refutation_is_preserved(self):
        for elaborated in (False, True):
            nodes = self.graph("def P : Prop := False\ntheorem notP : ¬ P := fun p => p", elaborated)
            self.assertEqual(nodes["P"]["status"], kg.STATUS_REFUTED)


if __name__ == "__main__":
    unittest.main()

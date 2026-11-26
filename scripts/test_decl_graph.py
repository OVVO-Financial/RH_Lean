#!/usr/bin/env python3
"""Regression tests for Lean source names and strict exact-graph coverage."""

import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import decl_graph
import proof_inventory
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

    def ingest(self, names, *, kinds=None, source=None):
        # Synthetic extractor records exercise name matching, not kernel validity.
        records = [
            {"name": name, "module": "RHLean.ScopeFixture", "kind": (kinds or {}).get(name, "theorem"),
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
                (Path("RHLean/ScopeFixture.lean"), self.SOURCE if source is None else source),
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

    def test_inventory_accounts_for_each_source_proof_and_kernel_theorem(self):
        source = """\
namespace Scope
private theorem witness : True := by trivial
lemma _root_.Export.result : True := witness
instance proofInst : Nonempty Unit := ⟨()⟩
instance dataInst : Inhabited Unit := ⟨()⟩
end Scope
"""
        kinds = {"_private.RHLean.ScopeFixture.0.Scope.witness": "theorem",
                 "Export.result": "theorem", "Scope.proofInst": "theorem", "Scope.dataInst": "def"}
        graph = self.ingest(kinds, kinds=kinds, source=source)
        inventory = {
            "proofs": [{"kind": kind, "name": name, "module": "RHLean.ScopeFixture",
                        "path": "RHLean/ScopeFixture.lean", "line": line}
                       for kind, name, line in [("theorem", "witness", 2),
                                                ("lemma", "_root_.Export.result", 3)]],
            "named_proofs": {"total_theorem_plus_lemma": 2},
        }
        check = proof_inventory.check_elaborated_proofs
        self.assertEqual(check(inventory, graph), ["Scope.proofInst"])
        self.assertEqual(graph["stats"]["named_proofs"], 3)

        nodes = graph["declarations"]
        with patch.dict(nodes["Scope.proofInst"], {"source_kind": "def"}):
            with self.assertRaisesRegex(ValueError, "unaccounted def Scope.proofInst"):
                check(inventory, graph)
        # Swapping a lemma and a data instance preserves the total kernel count.
        with patch.dict(nodes["Export.result"], {"kind": "def"}), \
                patch.dict(nodes["Scope.dataInst"], {"kind": "theorem"}):
            with self.assertRaisesRegex(ValueError, "expected lemma Export.result"):
                check(inventory, graph)
        with patch.dict(inventory["proofs"][1], {"name": "_root_.Export.wrong"}):
            with self.assertRaisesRegex(ValueError, "expected lemma Export.wrong"):
                check(inventory, graph)
        del nodes["Export.result"]
        with self.assertRaisesRegex(ValueError, "missing kernel declarations.*Export.result"):
            check(inventory, graph)


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



class KernelTypeAuditTests(unittest.TestCase):
    def graph(self, source, overrides):
        path = Path("RHLean/KernelTypeFixture.lean")
        with patch.object(kg, "load_sources", return_value=[(path, source)]), \
                patch.object(kg, "load_facets", return_value={"facets": {}, "roles": {}}):
            declarations, _ = kg.build_declarations()
            records = []
            for d in declarations:
                record = {"name": d.name, "module": d.module, "kind": d.kind,
                          "typeRefs": d.statement_refs, "valueRefs": d.proof_refs}
                if d.name in overrides:
                    record["kernelTypeAudit"] = overrides[d.name]
                records.append(record)
            with tempfile.TemporaryDirectory() as temp:
                jsonl = Path(temp) / "declarations.jsonl"
                jsonl.write_text("".join(json.dumps(r) + "\n" for r in records))
                return decl_graph.build_graph_from_lean(jsonl)["declarations"]

    @staticmethod
    def audit(binders=0, premises=(), form="", targets=(), closed=False, blocked=False,
              returns_rh=False, exact_rh=False):
        return dict(binders=binders, premises=list(premises), form=form,
                    targets=list(targets), closedProp=closed, blocked=blocked,
                    returnsRH=returns_rh, exactRH=exact_rh)

    def test_actual_hidden_section_argument_overrides_source_guess(self):
        source = "def P : Prop := False\nsection\nvariable (h : P)\ninclude h\ntheorem t : P := h\nend\n"
        nodes = self.graph(source, {"P": self.audit(closed=True),
            "t": self.audit(1, ("P",), "named", ("P",))})
        self.assertEqual(nodes["P"]["status"], kg.STATUS_OPEN)
        self.assertEqual(nodes["t"]["status"], kg.STATUS_REDUCED)
        self.assertEqual(nodes["t"]["hypothesis_refs"], ["P"])
        self.assertEqual(nodes["t"]["status_evidence"], "kernel-type")

    def test_opaque_external_premise_and_universe_block(self):
        source = "def P : Prop := False\ntheorem t : P := someProof\n"
        for audit in (self.audit(1, ("False",), "named", ("P",)),
                      self.audit(0, (), "named", ("P",), blocked=True)):
            nodes = self.graph(source, {"P": self.audit(closed=True), "t": audit})
            self.assertEqual(nodes["P"]["status"], kg.STATUS_OPEN)
            self.assertTrue(nodes["t"]["hard_blocked"])

    def test_genuine_closed_seed_still_propagates(self):
        source = "def P : Prop := True\ntheorem t : P := trivial\n"
        nodes = self.graph(source, {"P": self.audit(closed=True),
            "t": self.audit(form="named", targets=("P",))})
        self.assertEqual(nodes["P"]["status"], kg.STATUS_PROVED)

    def test_direct_rh_consumer_marked_conditional(self):
        source = "theorem t (h : RiemannHypothesis) : RiemannHypothesis := h\n"
        nodes = self.graph(source, {"t": self.audit(1, ("RiemannHypothesis",),
            "named", ("RiemannHypothesis",), returns_rh=True)})
        self.assertTrue(nodes["t"]["kernel_returns_rh"])
        self.assertFalse(nodes["t"]["kernel_exact_rh"])
        self.assertEqual(nodes["t"]["status"], kg.STATUS_REDUCED)


if __name__ == "__main__":
    unittest.main()

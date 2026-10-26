#!/usr/bin/env python3
"""Structural and status-consistency tests for the proof-obligation DAG."""

import copy
import json
import unittest

import proof_obligation_dag as dag


def load():
    return json.loads(dag.REGISTRY.read_text(encoding="utf-8"))


def node(reg, i):
    return next(n for n in reg["nodes"] if n["id"] == i)


def edge(reg, i):
    return next(e for e in reg["edges"] if e["id"] == i)


class ProofObligationDagTests(unittest.TestCase):
    def setUp(self):
        self.reg = load()

    def errors(self, mutate):
        reg = copy.deepcopy(self.reg)
        mutate(reg)
        return "\n".join(dag.validate(reg))

    def assertRejects(self, mutate, needle):
        self.assertIn(needle, self.errors(mutate))

    def test_registry_is_valid_and_generated_docs_are_current(self):
        self.assertEqual(dag.validate(self.reg), [])
        self.assertEqual(dag.sync(self.reg, write=False), [])

    def test_ten_routes_and_seven_agents(self):
        self.assertEqual(tuple(r["id"] for r in self.reg["routes"]), dag.ROUTE_IDS)
        self.assertEqual(tuple(a["role"] for a in self.reg["agents"]), dag.AGENT_ROLES)
        self.assertRejects(lambda r: r["routes"].pop(), "routes must be exactly")

    def test_von_koch_milestone_is_first_class_and_separated(self):
        vk = node(self.reg, "MILESTONE-VONKOCH-VF-LEAN")
        self.assertEqual(vk["classification"], "FORMALIZED_CANONICAL_VONKOCH_REDUCTION")
        self.assertIn("The Riemann Hypothesis", vk["does_not_prove"])
        self.assertEqual(node(self.reg, "IFACE-CLASSICAL-VONKOCH")["formal_status"], "EXPLICIT_LEAN_INTERFACE")
        self.assertEqual(node(self.reg, "OPEN-VF-ACTUAL-PRIME")["logical_status"], "OPEN")
        self.assertRejects(lambda r: node(r, "MILESTONE-VONKOCH-VF-LEAN").update(classification="RH"),
                           "classification")
        self.assertRejects(lambda r: node(r, "IFACE-CLASSICAL-VONKOCH").update(formal_status="PROVED_IN_LEAN_ON_MAIN"),
                           "IFACE-CLASSICAL-VONKOCH")

    def test_declaration_links_are_checked(self):
        def typo(r):
            node(r, "MILESTONE-VONKOCH-VF-LEAN")["lean"][0]["name"] += "X"
        self.assertRejects(typo, "not found in research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean")

    def test_duplicate_and_dangling_references(self):
        self.assertRejects(lambda r: r["nodes"].append(copy.deepcopy(node(r, "RH"))), "duplicate node id RH")
        self.assertRejects(lambda r: edge(r, "E-MERTENS-RH").update(to="NOWHERE"), "unknown node NOWHERE")

    def test_dropping_the_classical_interface_is_a_silent_omission(self):
        def drop(r):
            edge(r, "E-VF-CAN-RH").update(type="PROVED_IMPLICATION", conditions=[])
        self.assertRejects(drop, "silently omitted prerequisite")

    def test_route_unpaid_inputs_must_match_the_path(self):
        def forget(r):
            r["routes"][0]["paths"][1]["unpaid_inputs"] = ["OPEN-VF-ACTUAL-PRIME"]
        self.assertRejects(forget, "declared unpaid inputs")

    def test_proving_an_open_premise_is_caught(self):
        def prove(r):
            node(r, "PROP-PRIME-LI-VONKOCH").update(
                logical_status="PROVED", evidence_class="PROVED_IN_LEAN_ON_MAIN",
                formal_status="PROVED_IN_LEAN_ON_MAIN", open_obligation=False)
        self.assertRejects(prove, "mixes proved and unproved")

    def test_reverse_implication_must_be_labelled_equivalence(self):
        def reverse(r):
            r["edges"].append({"id": "E-BAD", "from": "PROP-MERTENS-ENERGY", "type": "PROVED_IMPLICATION",
                               "to": "OPEN-FINITE-AC", "certified_by": "CONSUMER-MERTENS-ENERGY-RH",
                               "conditions": []})
        self.assertRejects(reverse, "dependency cycle")

    def test_non_equivalences_cannot_collapse(self):
        def merge(r):
            r["edges"].append({"id": "E-BAD", "from": "OPEN-CORR4", "type": "PROVED_EQUIVALENCE",
                               "to": "OPEN-FINITE-AC", "certified_by": "THM-FINITE-A-IFF-LEGAL-GRAM",
                               "conditions": []})
        self.assertRejects(merge, "non-equivalence violated: OPEN-CORR4 and OPEN-FINITE-AC")

    def test_block_stays_refuted(self):
        self.assertRejects(lambda r: r["routes"][3].update(disposition="OPEN"), "BLOCK must remain REFUTED")
        self.assertRejects(lambda r: node(r, "CE-BLOCK-R549").update(reproducer="scripts/check_documentation.py"),
                           "R = 549 regression")

    def test_paper_and_numerical_results_are_not_lean_certificates(self):
        self.assertRejects(lambda r: node(r, "NOGO-CORR4-FRAME-ONLY").update(formal_status="PROVED_IN_LEAN_ON_MAIN"),
                           "NOGO-CORR4-FRAME-ONLY")
        self.assertRejects(lambda r: node(r, "FINITE-CORR4-CENSUS").update(formal_status="PROVED_IN_LEAN_ON_MAIN"),
                           "promoted to a Lean certificate")

    def test_pr_status_comes_from_the_dated_snapshot(self):
        for number in (1021, 1022, 1023, 1024):
            ev = next(e for e in self.reg["evidence"] if e.get("number") == number)
            self.assertEqual(ev["state"], "merged")
            self.assertEqual(ev["checks"]["pending"], 0)
            self.assertEqual(ev["checks"]["failed"], 0)
        for name in ("PR1022-ZERO-MODE", "PR1023-FRAME-B7"):
            self.assertEqual(node(self.reg, name)["formal_status"], "PROVED_IN_LEAN_ON_MAIN")

        def reopen(r):
            next(e for e in r["evidence"] if e.get("number") == 1023).update(state="open", merged_at=None)
        self.assertRejects(reopen, "on-main status but PR #1023 is not merged")
        self.assertEqual(next(e for e in self.reg["evidence"] if e.get("number") == 1019)["state"], "merged")

    def test_corr4_power_gate_is_conditional_not_an_exponent_proof(self):
        self.assertEqual(node(self.reg, "MILESTONE-CORR4-POWER-IFF")["logical_status"], "PROVED")
        self.assertEqual(node(self.reg, "OPEN-CORR4-MIXED-TAIL-POWER")["logical_status"], "OPEN")
        self.assertEqual(node(self.reg, "CONSUMER-CORR4-MIXED-TAIL-POWER-IMPROVEMENT")["hypotheses"],
                         ["OPEN-CORR4-MIXED-TAIL-POWER"])
        self.assertEqual(edge(self.reg, "E-CORR4-MIXED-TAIL-IMPROVES-78")["certified_by"],
                         "CONSUMER-CORR4-MIXED-TAIL-POWER-IMPROVEMENT")
        self.assertEqual(node(self.reg, "OPEN-CORR4-RELAXED-REMAINDER")["logical_status"], "OPEN")
        self.assertEqual(node(self.reg, "IFACE-CLASSICAL-VONKOCH")["formal_status"], "EXPLICIT_LEAN_INTERFACE")
        def falsely_pay(r):
            node(r, "OPEN-CORR4-MIXED-TAIL-POWER").update(logical_status="PROVED",
                formal_status="PROVED_IN_LEAN_ON_MAIN", evidence_class="PROVED_IN_LEAN_ON_MAIN",
                open_obligation=False)
        self.assertRejects(falsely_pay, "every hypothesis is proved")

    def test_proved_nodes_cannot_require_open_inputs(self):
        def require(r):
            r["edges"].append({"id": "E-BAD", "from": "MILESTONE-VF-LI-O1", "type": "REQUIRES",
                               "to": "OPEN-VF-ACTUAL-PRIME", "conditions": []})
        self.assertRejects(require, "requires unproved OPEN-VF-ACTUAL-PRIME")

    def test_no_route_proves_rh(self):
        for route in self.reg["routes"]:
            for path in route["paths"]:
                self.assertTrue(path["unpaid_inputs"], path["id"])

        def pay(r):
            path = r["routes"][6]["paths"][0]
            node(r, "OPEN-FINITE-AC").update(logical_status="PROVED", evidence_class="PROVED_IN_LEAN_ON_MAIN",
                                             formal_status="PROVED_IN_LEAN_ON_MAIN", open_obligation=False)
            path["unpaid_inputs"] = []
        self.assertRejects(pay, "proved premise OPEN-FINITE-AC implies non-proved PROP-MERTENS-ENERGY")
        self.assertRejects(lambda r: node(r, "RH").update(logical_status="PROVED"), "RH: PROVED node flagged")

    def test_historical_frontier_registry_is_preserved(self):
        frontier = json.loads(dag.FRONTIER.read_text(encoding="utf-8"))
        self.assertEqual(frontier["schema"], "rhlean-research-frontier/1")
        self.assertEqual(set(self.reg["historical_tracks"]), {str(t["pr"]) for t in frontier["tracks"]})


if __name__ == "__main__":
    unittest.main()

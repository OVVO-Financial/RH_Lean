#!/usr/bin/env python3
"""Validate and render the mathematical proof-obligation DAG.

The registry docs/proof-obligations.json is Layer A of the knowledge graph:
propositions, typed mathematical edges and RH routes. This script checks its
internal logic (statuses, equivalence collapse, acyclicity, route premises,
Lean declaration links, dated PR evidence) and regenerates the marked tables
in docs/PROOF_DEPENDENCY_DAG.md and docs/FORMALIZATION_MILESTONES.md.

It is navigation and status bookkeeping, not a proof checker: a passing run
proves no open input, and a Lean link is checked lexically (optionally against
the repository index), not compiled.
"""

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REGISTRY = ROOT / "docs/proof-obligations.json"
FRONTIER = ROOT / "docs/research-frontier.json"
SCHEMA = "rhlean-proof-obligations/1"
ROUTE_IDS = ("VF-LOW", "SAT", "CODIV", "BLOCK", "OAI-NNS", "JOH",
             "FINITE-AC", "CORR4", "MU-LIFT", "NYMAN")
AGENT_ROLES = ("RH | Research Coordinator", "RH | Owner Payment",
               "RH | Adversarial Referee", "RH | Prime Census Laboratory",
               "RH | Analytic Type II", "RH | Finite Wheel & Incidence",
               "RH | Lean Verification")
LEAN_FORMAL = {"PROVED_IN_LEAN_ON_MAIN", "LEAN_STATEMENT_ONLY",
               "EXPLICIT_LEAN_INTERFACE", "LEAN_DEFINITION_ON_MAIN"}
PR_ONLY_FORMAL = {"PROVED_IN_LEAN_PR_GREEN_UNMERGED", "LEAN_PR_HEAD_NOT_GREEN"}
SYMMETRIC = {"PROVED_EQUIVALENCE", "EXACT_IDENTITY"}
TRUSTED = {"PROVED", "ESTABLISHED_LITERATURE"}
# Required first-class von Koch entries: id -> {field: expected value}.
VON_KOCH = {
    "HISTORICAL-VONKOCH-1901": {"logical_status": "ESTABLISHED_LITERATURE",
                                "formal_status": "EXPLICIT_LEAN_INTERFACE"},
    "IFACE-CLASSICAL-VONKOCH": {"formal_status": "EXPLICIT_LEAN_INTERFACE",
                                "discharged_by": "CLASSICAL_VONKOCH_CRITERION_FORMAL_IMPORT_OR_PROOF"},
    "CLASSICAL_VONKOCH_CRITERION_FORMAL_IMPORT_OR_PROOF": {
        "type": "formalization_task", "obligation_kind": "FORMALIZATION_COMPLETENESS"},
    "MILESTONE-VF-CANONICAL": {"formal_status": "PROVED_IN_LEAN_ON_MAIN", "pr": 932},
    "MILESTONE-VF-LI-O1": {"formal_status": "PROVED_IN_LEAN_ON_MAIN", "pr": 932},
    "MILESTONE-VONKOCH-VF-LEAN": {"formal_status": "PROVED_IN_LEAN_ON_MAIN", "pr": 932,
                                  "classification": "FORMALIZED_CANONICAL_VONKOCH_REDUCTION"},
    "OPEN-VF-ACTUAL-PRIME": {"logical_status": "OPEN", "obligation_kind": "ARITHMETIC"},
    "RH-CONDITIONAL-CONSUMER": {"type": "conditional_consumer"},
    "RH": {"logical_status": "OPEN"},
}
VON_KOCH_DECLS = {
    "MILESTONE-VONKOCH-VF-LEAN": ("research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean",
                                  "vfCanonicalSquareVonKoch_iff_primeLiVonKoch"),
    "IFACE-CLASSICAL-VONKOCH": ("research/VF_MID_VON_KOCH_BRIDGE.lean",
                                "ClassicalVonKochRHCriterion"),
    "OPEN-VF-ACTUAL-PRIME": ("research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean",
                             "VFCanonicalSquareVonKochStatement"),
}


class Graph:
    """Registry indexes plus the equivalence quotient."""

    def __init__(self, reg):
        self.reg = reg
        self.nodes = {n["id"]: n for n in reg["nodes"]}
        self.edges = {e["id"]: e for e in reg["edges"]}
        self.parent = {i: i for i in self.nodes}
        for e in reg["edges"]:
            if self.collapses(e):
                self.union(e["from"], e["to"])

    def collapses(self, e):
        cert = self.nodes.get(e.get("certified_by"), {})
        return (e["type"] in SYMMETRIC and e["from"] in self.nodes
                and e["to"] in self.nodes
                and cert.get("logical_status") in TRUSTED)

    def find(self, i):
        while self.parent[i] != i:
            self.parent[i] = self.parent[self.parent[i]]
            i = self.parent[i]
        return i

    def union(self, a, b):
        ra, rb = self.find(a), self.find(b)
        if ra != rb:
            self.parent[max(ra, rb)] = min(ra, rb)

    def classes(self):
        out = {}
        for i in self.nodes:  # registry order
            out.setdefault(self.find(i), []).append(i)
        return out

    def support_edges(self):
        """Quotient edges oriented from what is known/assumed to what it informs."""
        out = []
        for e in self.reg["edges"]:
            if e["type"] in SYMMETRIC:
                continue
            a, b = e["from"], e["to"]
            if e["type"] in ("REQUIRES", "REFUTED_BY"):
                a, b = b, a
            out.append((a, b, e["type"], e["id"]))
            for c in e.get("conditions", []):
                out.append((c, e["to"], "CONDITION", e["id"]))
        return out


def lean_declared(path, name, cache):
    if path not in cache:
        file = ROOT / path
        cache[path] = file.read_text(encoding="utf-8") if file.is_file() else None
    text = cache[path]
    if text is None:
        return False
    pattern = (r"(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|"
               r"nonrec|partial)\s+)*(?:theorem|lemma|def|structure|abbrev|"
               r"instance|class|inductive)\s+" + re.escape(name) + r"(?![\w.'])")
    return re.search(pattern, text) is not None


def is_path(ref):
    return isinstance(ref, str) and " " not in ref and ":" not in ref and "/" in ref


def validate(reg, root=ROOT, frontier_path=None):
    """Return a list of error strings; empty means the registry is coherent."""
    errors = []
    err = errors.append
    if reg.get("schema") != SCHEMA:
        return [f"unsupported schema {reg.get('schema')!r}"]
    vocab = reg["vocabulary"]
    ids = [n["id"] for n in reg["nodes"]]
    for dup in sorted({i for i in ids if ids.count(i) > 1}):
        err(f"duplicate node id {dup}")
    eids = [e["id"] for e in reg["edges"]]
    for dup in sorted({i for i in eids if eids.count(i) > 1}):
        err(f"duplicate edge id {dup}")
    if errors:
        return errors
    g = Graph(reg)
    N = g.nodes
    evidence = {ev["id"]: ev for ev in reg["evidence"]}
    prs = {ev["number"]: ev for ev in reg["evidence"] if ev.get("kind") == "pr"}

    def ref(owner, i):
        if i not in N:
            err(f"{owner}: unknown node {i}")
            return False
        return True

    # ---- node vocabulary and status coherence
    cache = {}
    for n in reg["nodes"]:
        i = n["id"]
        for field, allowed in (("type", "node_types"), ("logical_status", "logical_status"),
                               ("formal_status", "formal_status"), ("provenance", "provenance")):
            if n.get(field) not in vocab[allowed]:
                err(f"{i}: invalid {field} {n.get(field)!r}")
        ls, fs, ec, t = n.get("logical_status"), n.get("formal_status"), n.get("evidence_class"), n.get("type")
        if t == "carrier":
            if ls != "DEFINITION" or ec is not None:
                err(f"{i}: carriers are definitions without an evidence class")
        elif ec not in vocab["evidence_class"]:
            err(f"{i}: invalid evidence_class {ec!r}")
        elif ls == "DEFINITION":
            err(f"{i}: only carriers may have logical_status DEFINITION")
        if not n.get("statement"):
            err(f"{i}: missing statement")
        if n.get("open_obligation") and n.get("obligation_kind") not in vocab["obligation_kind"]:
            err(f"{i}: open obligation needs an obligation_kind")
        if ls == "OPEN":
            if ec not in ("UNKNOWN", "TARGET_EQUIVALENT"):
                err(f"{i}: OPEN node cannot carry evidence class {ec}")
            if not n.get("open_obligation"):
                err(f"{i}: OPEN node must be flagged open_obligation")
            if fs not in ("LEAN_STATEMENT_ONLY", "NOT_FORMALIZED"):
                err(f"{i}: OPEN node cannot be formally proved ({fs})")
        if ls == "PROVED":
            if n.get("open_obligation"):
                err(f"{i}: PROVED node flagged as an open obligation")
            if fs == "NOT_FORMALIZED" and not (
                    ec == "INDEPENDENTLY_REVIEWED_PAPER_PROOF"
                    or (t == "counterexample" and ec == "FINITE_COMPUTATION")):
                err(f"{i}: unformalized PROVED node needs independent review or an exact counterexample")
            if t == "counterexample" and not n.get("reproducer"):
                err(f"{i}: counterexample without reproducer")
        if ls == "ESTABLISHED_LITERATURE":
            if not n.get("literature"):
                err(f"{i}: literature status without a reference")
            if n.get("provenance") not in ("LITERATURE_EXPLICIT_INTERFACE", "LITERATURE_NOT_FORMALIZED"):
                err(f"{i}: literature node with provenance {n.get('provenance')}")
            if fs not in ("EXPLICIT_LEAN_INTERFACE", "NOT_FORMALIZED"):
                err(f"{i}: literature node cannot be {fs}")
        if ls == "CLAIMED":
            if ec != "PAPER_PROOF_NEEDS_REVIEW" or fs not in ("NOT_FORMALIZED", "LEAN_PR_HEAD_NOT_GREEN"):
                err(f"{i}: CLAIMED node must be an unreviewed, uncertified paper claim")
            if n.get("obligation_kind") != "REVIEW":
                err(f"{i}: CLAIMED node must carry obligation_kind REVIEW")
        if ls == "FINITE_EVIDENCE" and (ec != "FINITE_COMPUTATION" or not n.get("reproducer")):
            err(f"{i}: finite evidence needs FINITE_COMPUTATION and a reproducer")
        if ls == "REFUTED":
            if ec != "REFUTED":
                err(f"{i}: REFUTED node must use evidence class REFUTED")
            if not any(e["from"] == i and e["type"] == "REFUTED_BY" for e in reg["edges"]):
                err(f"{i}: REFUTED node has no REFUTED_BY edge")
        if ec in ("PAPER_PROOF_NEEDS_REVIEW", "FINITE_COMPUTATION") and fs in (
                "PROVED_IN_LEAN_ON_MAIN", "PROVED_IN_LEAN_PR_GREEN_UNMERGED"):
            err(f"{i}: paper/numerical evidence promoted to a Lean certificate")
        if ec in ("PROVED_IN_LEAN_ON_MAIN", "PROVED_IN_LEAN_PR_GREEN_UNMERGED") and fs != ec:
            err(f"{i}: evidence {ec} disagrees with formal status {fs}")
        if t == "conditional_consumer":
            hyps = n.get("hypotheses", [])
            if ls != "PROVED" or ec != "CONDITIONAL" or not hyps:
                err(f"{i}: conditional consumer must be a PROVED implication with CONDITIONAL evidence and hypotheses")
            if all(ref(i, h) and N[h]["logical_status"] == "PROVED" for h in hyps):
                err(f"{i}: every hypothesis is proved; this is not a conditional consumer")
        elif ec == "CONDITIONAL":
            err(f"{i}: CONDITIONAL evidence is reserved for conditional consumers")
        # Layer B links
        if fs in LEAN_FORMAL and not n.get("lean"):
            err(f"{i}: Lean status {fs} without a declaration link")
        if fs in LEAN_FORMAL:
            for d in n.get("lean", []):
                if not lean_declared(d["file"], d["name"], cache):
                    err(f"{i}: declaration {d['name']} not found in {d['file']}")
        if fs in PR_ONLY_FORMAL:
            snap = prs.get(n.get("pr"))
            if snap is None or snap.get("state") != "open":
                err(f"{i}: {fs} requires an open PR in the evidence snapshot")
            else:
                checks = snap.get("checks") or {}
                green = checks.get("failed") == 0 and checks.get("pending") == 0 and checks.get("success", 0) > 0
                if (fs == "PROVED_IN_LEAN_PR_GREEN_UNMERGED") != green:
                    err(f"{i}: {fs} contradicts PR #{n.get('pr')} checks at {snap.get('head_sha')}")
        if fs == "PROVED_IN_LEAN_ON_MAIN" and n.get("pr") is not None:
            if prs.get(n["pr"], {}).get("state") != "merged":
                err(f"{i}: on-main status but PR #{n['pr']} is not merged in the snapshot")
        for path in [n.get("source_file"), n.get("reproducer")]:
            if is_path(path) and not (root / path).exists():
                err(f"{i}: missing file {path}")
        for e in n.get("evidence", []):
            if e not in evidence:
                err(f"{i}: unknown evidence {e}")
        for field in ("realizes", "discharged_by", "represented_by"):
            if field in n:
                ref(i, n[field])
        if t == "explicit_interface" and n.get("discharged_by") not in N:
            err(f"{i}: explicit interface must name the task that would discharge it")

    # ---- edges
    for e in reg["edges"]:
        i, t = e["id"], e["type"]
        if t not in vocab["edge_types"]:
            err(f"{i}: invalid edge type {t}")
            continue
        if not (ref(i, e["from"]) and ref(i, e["to"])):
            continue
        a, b = N[e["from"]], N[e["to"]]
        if e["from"] == e["to"]:
            err(f"{i}: self-loop")
        conds = e.get("conditions", [])
        for c in conds:
            ref(i, c)
        cert = N.get(e.get("certified_by")) if e.get("certified_by") else None
        if e.get("certified_by") and cert is None:
            err(f"{i}: unknown certifier {e['certified_by']}")
        if t in ("PROVED_EQUIVALENCE", "PROVED_IMPLICATION"):
            if conds:
                err(f"{i}: {t} cannot carry conditions; use CONDITIONAL_IMPLICATION")
            if not ((cert and cert["logical_status"] in TRUSTED) or e.get("elementary")):
                err(f"{i}: {t} needs a PROVED certifier or an elementary justification")
            if "carrier" in (a["type"], b["type"]):
                err(f"{i}: {t} connects propositions, not carriers")
        if t == "EXACT_IDENTITY" and not cert:
            err(f"{i}: EXACT_IDENTITY needs a certifier")
        if t == "CONDITIONAL_IMPLICATION":
            if not conds:
                err(f"{i}: CONDITIONAL_IMPLICATION without conditions")
            if not cert:
                err(f"{i}: CONDITIONAL_IMPLICATION needs a certifier")
            elif cert["logical_status"] not in TRUSTED and cert["id"] not in conds:
                err(f"{i}: unreviewed certifier {cert['id']} must itself be listed as a condition")
        if cert and cert["type"] == "conditional_consumer" and t in (
                "PROVED_IMPLICATION", "CONDITIONAL_IMPLICATION"):
            if set(cert["hypotheses"]) != {e["from"], *conds}:
                err(f"{i}: premises {sorted({e['from'], *conds})} differ from consumer "
                    f"{cert['id']} hypotheses {sorted(cert['hypotheses'])} (silently omitted prerequisite?)")
        if t == "WEIGHTED_PROJECTION" and not e.get("loses"):
            err(f"{i}: a weighted projection must state what it loses")
        if t == "REFUTED_BY":
            if a["logical_status"] != "REFUTED":
                err(f"{i}: REFUTED_BY source {a['id']} is not REFUTED")
            if b["logical_status"] not in TRUSTED or b["type"] not in (
                    "counterexample", "literature_theorem", "no_go", "proved_lemma"):
                err(f"{i}: refutation must cite a proved counterexample or established theorem")
        if t == "REQUIRES" and a["logical_status"] == "PROVED" and a["type"] != "conditional_consumer" \
                and b["logical_status"] != "PROVED":
            err(f"{i}: proved node {a['id']} requires unproved {b['id']}")
        if t == "INDEPENDENT_ARITHMETIC_GAIN":
            if a["type"] != "arithmetic_mechanism" or b["logical_status"] != "OPEN" or not e.get("gain"):
                err(f"{i}: arithmetic-gain edges run from a mechanism to an OPEN target and state the gain")
        if t in ("PROVED_IMPLICATION",) and a["logical_status"] == "PROVED" and b["logical_status"] != "PROVED":
            err(f"{i}: proved premise {a['id']} implies non-proved {b['id']}")
        if t == "PROVED_IMPLICATION" and b["logical_status"] == "REFUTED" and a["logical_status"] != "REFUTED":
            err(f"{i}: {a['id']} implies refuted {b['id']} but is not refuted")
        if t == "CONDITIONAL_IMPLICATION" and all(
                N.get(x, {}).get("logical_status") == "PROVED" for x in [e["from"], *conds]) \
                and b["logical_status"] != "PROVED":
            err(f"{i}: all premises proved but {b['id']} is not")
    if errors:
        return errors

    # ---- equivalence classes
    classes = g.classes()
    for members in classes.values():
        statuses = {N[m]["logical_status"] for m in members}
        if statuses & TRUSTED and statuses & {"OPEN", "REFUTED", "CLAIMED"}:
            err(f"equivalence class {members} mixes proved and unproved statuses {sorted(statuses)}")
    for ne in reg["non_equivalences"]:
        if ref("non_equivalence", ne["a"]) and ref("non_equivalence", ne["b"]):
            if g.find(ne["a"]) == g.find(ne["b"]):
                err(f"non-equivalence violated: {ne['a']} and {ne['b']} collapsed into one class")
    # ---- acyclicity of the quotient
    out = {}
    for a, b, t, i in g.support_edges():
        ca, cb = g.find(a), g.find(b)
        if ca != cb:
            out.setdefault(ca, set()).add(cb)
    state = {}

    def visit(c, stack):
        state[c] = 1
        stack.append(c)
        for d in sorted(out.get(c, ())):
            if state.get(d) == 1:
                cyc = stack[stack.index(d):] + [d]
                err("dependency cycle after equivalence collapse (unlabelled equivalence?): "
                    + " -> ".join(cyc))
            elif d not in state:
                visit(d, stack)
        stack.pop()
        state[c] = 2

    for c in sorted(classes):
        if c not in state:
            visit(c, [])

    # ---- routes
    rh = g.find("RH") if "RH" in N else None
    if rh is None:
        err("missing RH node")
    routes = {r["id"]: r for r in reg["routes"]}
    if tuple(r["id"] for r in reg["routes"]) != ROUTE_IDS:
        err(f"routes must be exactly {ROUTE_IDS} in order")
    for r in reg["routes"]:
        rid = r["id"]
        for f in ("missing_mathematics", "quantitative_target", "best_source",
                  "largest_unpaid_term", "next_action", "status_label"):
            if not r.get(f):
                err(f"route {rid}: missing {f}")
        for x in r.get("falsifiers", []) + r.get("mechanism_nodes", []) + r.get("intermediate_targets", []):
            ref(f"route {rid}", x)
        if not r.get("paths"):
            err(f"route {rid}: no RH path")
        for p in r.get("paths", []):
            pid = p["id"]
            es = [g.edges.get(x) for x in p["edges"]]
            if None in es or not es:
                err(f"{pid}: unknown or empty edge list")
                continue
            for x in es:
                if x["type"] not in ("PROVED_IMPLICATION", "CONDITIONAL_IMPLICATION"):
                    err(f"{pid}: {x['id']} is not an implication edge")
            for x, y in zip(es, es[1:]):
                if g.find(x["to"]) != g.find(y["from"]):
                    err(f"{pid}: {x['id']} does not connect to {y['id']}")
            if g.find(es[-1]["to"]) != rh:
                err(f"{pid}: path does not end at RH")
            premises = {es[0]["from"]} | {c for x in es for c in x.get("conditions", [])}
            computed = {m for m in premises if N[m]["logical_status"] != "PROVED"}
            if computed != set(p["unpaid_inputs"]):
                err(f"{pid}: declared unpaid inputs {sorted(p['unpaid_inputs'])} != computed {sorted(computed)}")
            if not computed:
                err(f"{pid}: no unpaid input — this registry would claim RH is proved")
            if r["disposition"] == "REFUTED" and N[es[0]["from"]]["logical_status"] != "REFUTED":
                err(f"{pid}: refuted route must start from a refuted premise")
            if r["disposition"] == "OPEN" and N[es[0]["from"]]["logical_status"] == "REFUTED":
                err(f"{pid}: open route starts from a refuted premise")
        if r["disposition"] not in ("OPEN", "REFUTED"):
            err(f"route {rid}: invalid disposition {r['disposition']}")
    if routes.get("BLOCK", {}).get("disposition") != "REFUTED":
        err("BLOCK must remain REFUTED (R = 549)")
    block = N.get("REFUTED-BLOCK-UNIVERSAL", {})
    if block.get("logical_status") != "REFUTED" or not any(
            e["from"] == "REFUTED-BLOCK-UNIVERSAL" and e["to"] == "CE-BLOCK-R549"
            and e["type"] == "REFUTED_BY" for e in reg["edges"]):
        err("BLOCK universal capture must be REFUTED_BY CE-BLOCK-R549")
    if N.get("CE-BLOCK-R549", {}).get("reproducer") != "scripts/vf_block_capture_counterexample_549.py":
        err("CE-BLOCK-R549 must cite the permanent R = 549 regression script")
    if rh is not None and N["RH"]["logical_status"] != "OPEN":
        err("RH must remain OPEN")

    # ---- first-class von Koch milestone
    for i, fields in VON_KOCH.items():
        if i not in N:
            err(f"missing von Koch milestone node {i}")
            continue
        for f, v in fields.items():
            if N[i].get(f) != v:
                err(f"{i}: expected {f}={v!r}, found {N[i].get(f)!r}")
    for i, (path, name) in VON_KOCH_DECLS.items():
        if i in N and {"file": path, "name": name} not in N[i].get("lean", []):
            err(f"{i}: must link {name} in {path}")
    consumer = N.get("RH-CONDITIONAL-CONSUMER", {})
    if not {"IFACE-CLASSICAL-VONKOCH", "OPEN-VF-ACTUAL-PRIME"} <= set(consumer.get("hypotheses", [])):
        err("RH-CONDITIONAL-CONSUMER must keep both the classical interface and the actual-prime bound")
    if "Acta Mathematica" not in " ".join(N.get("HISTORICAL-VONKOCH-1901", {}).get("literature", [])):
        err("HISTORICAL-VONKOCH-1901 needs its Acta Mathematica reference")

    # ---- evidence snapshot (Layer C)
    for ev in reg["evidence"]:
        if ev.get("grade") not in vocab["evidence_grades"]:
            err(f"{ev['id']}: invalid grade {ev.get('grade')!r}")
        if not ev.get("observed_at"):
            err(f"{ev['id']}: undated evidence")
        if ev.get("kind") == "pr":
            if ev.get("state") == "merged" and not ev.get("merged_at"):
                err(f"{ev['id']}: merged PR without merged_at")
            if ev.get("state") == "open" and not (ev.get("head_sha") and ev.get("checks")):
                err(f"{ev['id']}: open PR needs head_sha and observed checks")
        elif is_path(ev.get("ref")) and not (root / ev["ref"]).exists():
            err(f"{ev['id']}: missing file {ev['ref']}")

    # ---- historical registry reconciliation
    frontier = json.loads((frontier_path or (root / "docs/research-frontier.json")).read_text())
    tracks = {str(t["pr"]) for t in frontier["tracks"]}
    if set(reg["historical_tracks"]) != tracks:
        err(f"historical_tracks keys {sorted(reg['historical_tracks'])} != research-frontier PRs {sorted(tracks)}")
    for pr, targets in reg["historical_tracks"].items():
        if not targets:
            err(f"historical track #{pr} maps to no node")
        for x in targets:
            ref(f"historical track #{pr}", x)

    # ---- frontier and agents
    for f in reg["frontier"]:
        for x in f["targets"] + [f["lens"]]:
            ref(f"frontier {f['rank']}", x)
        for r in f["routes"]:
            if r not in routes:
                err(f"frontier {f['rank']}: unknown route {r}")
    if tuple(a["role"] for a in reg["agents"]) != AGENT_ROLES:
        err(f"agents must be exactly the seven roles {AGENT_ROLES}")
    deliverables = [a["next_deliverable"] for a in reg["agents"]]
    if len(set(deliverables)) != len(deliverables):
        err("agents need distinct deliverables")
    for a in reg["agents"]:
        for x in a["target_nodes"]:
            ref(f"agent {a['agent']}", x)
    return errors


def check_repo_index(reg):
    """Cross-check Layer A declaration links against the repository index (Layer B)."""
    sys.path.insert(0, str(ROOT / "scripts"))
    import repo_index
    data = repo_index.load_index(repo_index.ROOT, None, [])
    paths = {key: m["path"] for key, m in data["modules"].items() if m["view"] == "worktree"}
    names = {}
    for d in data["declarations"]:
        path = paths.get(d["module_id"])
        if path:
            names.setdefault(path, set()).add(d["name"])
    errors = []
    for n in reg["nodes"]:
        if n["formal_status"] not in LEAN_FORMAL:
            continue
        for d in n.get("lean", []):
            known = names.get(d["file"], set())
            if not any(x == d["name"] or x.endswith("." + d["name"]) for x in known):
                errors.append(f"{n['id']}: repository index has no {d['name']} in {d['file']}")
    return errors


# ------------------------------------------------------------------ render
def cell(text):
    return str(text).replace("|", "\\|").replace("\n", " ")


def label(n):
    return f"`{n['id']}`"


def render(reg):
    g = Graph(reg)
    N = g.nodes
    heads = {ev["number"]: ev.get("head_sha") for ev in reg["evidence"] if ev.get("kind") == "pr"}

    def lean_link(n, d):
        if n["formal_status"] in PR_ONLY_FORMAL and heads.get(n.get("pr")):
            base = f"https://github.com/OVVO-Financial/RH_Lean/blob/{heads[n['pr']]}/"
            return f"[`{d['name']}`]({base}{d['file']})"
        return f"[`{d['name']}`](../{d['file']})"

    out = {}
    kinds = {"OPEN": "arithmetic open", "ESTABLISHED_LITERATURE": "classical theorem, not proved in Lean",
             "CLAIMED": "review pending", "FINITE_EVIDENCE": "finite, outside Lean",
             "REFUTED": "refuted premise"}

    lines = ["| Route | Disposition | Exact missing mathematics | Quantitative target | Best source | "
             "Largest unpaid term | Falsifiers | Next proof action |", "|" + " --- |" * 8]
    for r in reg["routes"]:
        lines.append("| **{}** | {} | {} | {} | {} | {} | {} | {} |".format(
            r["id"], cell(r["status_label"]), cell(r["missing_mathematics"]), cell(r["quantitative_target"]),
            cell(r["best_source"]), cell(r["largest_unpaid_term"]),
            ", ".join(f"`{x}`" for x in r.get("falsifiers", [])) or "none recorded", cell(r["next_action"])))
    out["scoreboard"] = "\n".join(lines)

    lines = ["| Route path | Edges to RH | Unpaid inputs (kind) | Meaning |", "| --- | --- | --- | --- |"]
    for r in reg["routes"]:
        for p in r["paths"]:
            unpaid = "; ".join(f"`{u}` ({kinds.get(N[u]['logical_status'], N[u]['logical_status'])})"
                               for u in p["unpaid_inputs"])
            lines.append(f"| `{p['id']}` | {' → '.join(f'`{x}`' for x in p['edges'])} | {unpaid} | {cell(p['description'])} |")
    out["paths"] = "\n".join(lines)

    classes = g.classes()
    order = {c: k for k, c in enumerate(classes)}

    def mermaid(types, title):
        used, rows = set(), []
        for a, b, t, i in g.support_edges():
            if t not in types:
                continue
            ca, cb = g.find(a), g.find(b)
            if ca == cb:
                continue
            used.update((ca, cb))
            e = g.edges[i]
            cert = N.get(e.get("certified_by"), {})
            solid = t in ("PROVED_IMPLICATION", "REQUIRES") or (
                t == "WEIGHTED_PROJECTION" and cert.get("logical_status") in TRUSTED)
            arrow = "-->" if solid else "-.->"
            tag = {"CONDITION": "condition", "REQUIRES": "required by", "REFUTED_BY": "refutes"}.get(t, t)
            rows.append(f"  c{order[ca]} {arrow}|{tag}| c{order[cb]}")
        head = [f"%% {title}", "flowchart LR"]
        for c in classes:
            if c in used:
                body = "<br/>".join(classes[c])
                head.append(f'  c{order[c]}["{body}"]')
        return "```mermaid\n" + "\n".join(head + rows) + "\n```"

    out["mermaid-routes"] = mermaid({"PROVED_IMPLICATION", "CONDITIONAL_IMPLICATION", "CONDITION",
                                     "INDEPENDENT_ARITHMETIC_GAIN", "REQUIRES"}, "RH routes (quotient by proved equivalence)")
    out["mermaid-carriers"] = mermaid({"WEIGHTED_PROJECTION", "EXACT_IDENTITY", "REFUTED_BY"},
                                      "carriers, projections and refutations")

    lines = ["| Class | Members (proved equivalent) | Status |", "| --- | --- | --- |"]
    for c, members in classes.items():
        if len(members) > 1:
            lines.append(f"| `{c}` | {', '.join(f'`{m}`' for m in members)} | {N[c]['logical_status']} |")
    out["classes"] = "\n".join(lines)

    lines = ["| Not equivalent | Reason |", "| --- | --- |"]
    for ne in reg["non_equivalences"]:
        lines.append(f"| `{ne['a']}` ≠ `{ne['b']}` | {cell(ne['reason'])} |")
    out["non-equivalences"] = "\n".join(lines)

    lines = ["| ID | Type | Logical | Formal | Evidence | Lean / source | PR | Statement |",
             "|" + " --- |" * 8]
    for n in reg["nodes"]:
        src = "<br/>".join(lean_link(n, d) for d in n.get("lean", []))
        if not src and n.get("source_file"):
            src = f"[{Path(n['source_file']).name}](../{n['source_file']})"
        pr = f"[#{n['pr']}](https://github.com/OVVO-Financial/RH_Lean/pull/{n['pr']})" if n.get("pr") else ""
        lines.append(f"| {label(n)} | {n['type']} | {n['logical_status']} | {n['formal_status']} | "
                     f"{n.get('evidence_class') or '—'} | {src} | {pr} | {cell(n['statement'])} |")
    out["nodes"] = "\n".join(lines)

    lines = ["| Edge | From | Type | To | Conditions | Certified by | Note |", "|" + " --- |" * 7]
    for e in reg["edges"]:
        note = e.get("note") or e.get("loses") or e.get("gain") or e.get("elementary") or ""
        if e.get("elementary"):
            note = f"elementary: {e['elementary']}"
        lines.append(f"| `{e['id']}` | `{e['from']}` | {e['type']} | `{e['to']}` | "
                     f"{', '.join(f'`{c}`' for c in e.get('conditions', [])) or ''} | "
                     f"{('`' + e['certified_by'] + '`') if e.get('certified_by') else ''} | {cell(note)} |")
    out["edges"] = "\n".join(lines)

    lines = [f"Snapshot `{reg['baseline']['verified_at']}`, main `{reg['baseline']['main_sha']}`, "
             f"`{reg['baseline']['lean_toolchain']}`. Refresh from GitHub before relying on any open-PR row.", "",
             "| PR | State | Head | Observed checks | Grade |", "| --- | --- | --- | --- | --- |"]
    for ev in reg["evidence"]:
        if ev.get("kind") != "pr":
            continue
        checks = ev.get("checks")
        seen = (f"{checks.get('success', 0)}/{checks.get('jobs', '?')} jobs green"
                + (f", {checks['failed']} failed" if checks.get("failed") else "")
                + (f", {checks['pending']} pending" if checks.get("pending") else "")) if checks else "not re-audited"
        state = ev["state"] + (" (draft)" if ev.get("draft") else "")
        if ev.get("merged_at"):
            state += f" {ev['merged_at'][:10]}"
        head = f"`{ev['head_sha'][:12]}`" if ev.get("head_sha") else ""
        lines.append(f"| [#{ev['number']}](https://github.com/OVVO-Financial/RH_Lean/pull/{ev['number']}) | "
                     f"{state} | {head} | {seen} | {ev['grade']} |")
    out["evidence"] = "\n".join(lines)

    lines = ["| Rank | Frontier | Routes | Target nodes | Falsification lens | Task |", "|" + " --- |" * 6]
    for f in reg["frontier"]:
        lines.append(f"| {f['rank']} | {cell(f['title'])} | {', '.join(f['routes'])} | "
                     f"{', '.join(f'`{x}`' for x in f['targets'])} | `{f['lens']}` | {cell(f['task'])} |")
    out["frontier"] = "\n".join(lines)

    lines = ["| Agent | Owns | Next distinct deliverable | Target nodes |", "| --- | --- | --- | --- |"]
    for a in reg["agents"]:
        lines.append(f"| {a['agent']}. {a['role']} | {cell(a['owns'])} | {cell(a['next_deliverable'])} | "
                     f"{', '.join(f'`{x}`' for x in a['target_nodes'])} |")
    out["agents"] = "\n".join(lines)

    lines = ["| Order | Date | Milestone | Status | Lean declarations | PR | Does not prove |", "|" + " --- |" * 7]
    ms = sorted((n for n in reg["nodes"] if n.get("milestone")), key=lambda n: n["milestone"]["order"])
    for n in ms:
        m = n["milestone"]
        decls = "<br/>".join(lean_link(n, d) for d in n.get("lean", []))
        pr = f"[#{m['pr']}](https://github.com/OVVO-Financial/RH_Lean/pull/{m['pr']})" if m.get("pr") else "—"
        lines.append(f"| {m['order']} | {m['date']} | `{n['id']}` — {cell(n['title'])} | {n['formal_status']} | "
                     f"{decls or '—'} | {pr} | {cell('; '.join(n.get('does_not_prove', []))) or '—'} |")
    out["milestones"] = "\n".join(lines)
    return out


TARGETS = {
    "docs/PROOF_DEPENDENCY_DAG.md": ("scoreboard", "paths", "mermaid-routes", "mermaid-carriers", "classes",
                                     "non-equivalences", "frontier", "agents", "nodes", "edges", "evidence"),
    "docs/FORMALIZATION_MILESTONES.md": ("milestones",),
}


def splice(text, name, body):
    begin = f"<!-- BEGIN GENERATED: {name} -->"
    end = f"<!-- END GENERATED: {name} -->"
    pattern = re.compile(re.escape(begin) + r".*?" + re.escape(end), re.S)
    if not pattern.search(text):
        raise ValueError(f"missing generated block {name}")
    return pattern.sub(lambda _: f"{begin}\n{body}\n{end}", text)


def sync(reg, write, root=ROOT):
    sections, stale = render(reg), []
    for rel, names in TARGETS.items():
        path = root / rel
        text = path.read_text(encoding="utf-8")
        new = text
        for name in names:
            new = splice(new, name, sections[name])
        if new != text:
            stale.append(rel)
            if write:
                path.write_text(new, encoding="utf-8")
    return stale


def write_dot(reg, path):
    g = Graph(reg)
    classes = g.classes()
    order = {c: k for k, c in enumerate(classes)}
    lines = ["digraph proof_obligations {", "  rankdir=LR;"]
    for c, members in classes.items():
        lines.append(f'  c{order[c]} [label="' + "\\n".join(members) + '"];')
    for a, b, t, i in g.support_edges():
        ca, cb = g.find(a), g.find(b)
        if ca != cb:
            style = "solid" if t in ("PROVED_IMPLICATION", "REQUIRES") else "dashed"
            lines.append(f'  c{order[ca]} -> c{order[cb]} [label="{t}", style={style}];')
    path.write_text("\n".join(lines + ["}"]) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--registry", type=Path, default=REGISTRY)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true", help="fail if generated Markdown blocks are stale")
    mode.add_argument("--write", action="store_true", help="rewrite generated Markdown blocks")
    parser.add_argument("--repo-index", action="store_true",
                        help="also confirm Lean links against scripts/repo_index.py declarations")
    parser.add_argument("--dot", type=Path, help="write the equivalence-quotient graph as Graphviz DOT")
    args = parser.parse_args()
    reg = json.loads(args.registry.read_text(encoding="utf-8"))
    errors = validate(reg)
    if not errors and args.repo_index:
        errors = check_repo_index(reg)
    if errors:
        raise SystemExit("proof-obligation DAG invalid:\n  " + "\n  ".join(errors))
    if args.write or args.check:
        stale = sync(reg, write=args.write)
        if stale and args.check:
            raise SystemExit("generated blocks are stale; run python3 scripts/proof_obligation_dag.py --write: "
                             + ", ".join(stale))
    if args.dot:
        write_dot(reg, args.dot)
    g = Graph(reg)
    open_inputs = sorted({u for r in reg["routes"] for p in r["paths"] for u in p["unpaid_inputs"]
                          if g.nodes[u]["logical_status"] == "OPEN"})
    print(f"PASS: {len(reg['nodes'])} nodes, {len(reg['edges'])} typed edges, "
          f"{len(g.classes())} equivalence classes, {len(reg['routes'])} routes; "
          f"RH open; {len(open_inputs)} open arithmetic route inputs")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""CI smoke checks for the ten-route/seven-agent research instructions.

Validates source routing and role prompts, not any Riemann Hypothesis claim.
"""
import json
from pathlib import Path

import proof_obligation_dag

ROOT = Path(__file__).resolve().parents[1]
MILESTONE_TITLE = ("## Major Formalization Milestone: von Koch (1901) and the "
                   "Canonical VF Prime-Counting Criterion")

def read(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")

def main() -> None:
    portfolio = read("docs/RH_PROOF_ATTACK_PORTFOLIO_20261024.md")
    agent_policy = read("AGENTS.md")
    dynamic = read("docs/DYNAMIC_RESEARCH_AGENTS.md")
    proof_contract = read("CURRENT_PROOF_CONTRACT.md")
    setup = read("docs/CHATGPT_AGENT_STUDIO_RH_SETUP_2026_10_12.md")
    prompts = read("docs/AGENT_STUDIO_20261024_SEVEN_PROMPTS.md")
    overlap = read("docs/RH_PROOF_OVERLAP_AND_SEVEN_EIGHTHS_AUDIT_20261024.md")
    for route in ("VF-LOW", "SAT", "CODIV", "BLOCK", "OAI-NNS", "JOH",
                  "FINITE-AC", "CORR4", "MU-LIFT", "NYMAN"):
        assert "**" + route + "**" in portfolio, f"missing route {route}"
    for i, role in enumerate((
        "RH | Research Coordinator",
        "RH | Owner Payment",
        "RH | Adversarial Referee",
        "RH | Prime Census Laboratory",
        "RH | Analytic Type II",
        "RH | Finite Wheel & Incidence",
        "RH | Lean Verification",
    ), start=1):
        assert f"### Agent {i} — {role}" in prompts, f"missing Studio Agent {i}"
    assert prompts.count("### Agent ") == 7, "exactly seven role sections required"
    assert "REFUTED" in portfolio and "R=549" in portfolio
    assert "human-only merge" in portfolio.lower()
    assert "one scheduled invocation" in portfolio.lower()
    assert "report-only" in prompts
    # PR state comes from the dated, typed evidence snapshot, never from words in prose.
    registry = json.loads(read("docs/proof-obligations.json"))
    errors = proof_obligation_dag.validate(registry)
    assert not errors, "proof-obligation DAG invalid:\n" + "\n".join(errors)
    snapshot = {ev["number"]: ev for ev in registry["evidence"] if ev.get("kind") == "pr"}
    for number in (932, 987, 1017, 1019, 1020):
        assert snapshot[number]["state"] == "merged" and snapshot[number]["merged_at"], number
    for number in (1021, 1022, 1023):  # open at the 2026-10-25 snapshot; may later merge
        record = snapshot[number]
        assert record["state"] in ("open", "merged", "closed"), number
        assert record["state"] != "open" or (record["head_sha"] and record["checks"]), number
    assert [r["id"] for r in registry["routes"]] == [
        "VF-LOW", "SAT", "CODIV", "BLOCK", "OAI-NNS", "JOH",
        "FINITE-AC", "CORR4", "MU-LIFT", "NYMAN"]
    readme = read("README.md")
    assert MILESTONE_TITLE in readme, "README lost the von Koch milestone section"
    for needle in ("research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean",
                   "ClassicalVonKochRHCriterion", "pull/932",
                   "docs/PROOF_DEPENDENCY_DAG.md", "docs/FORMALIZATION_MILESTONES.md"):
        assert needle in readme, f"README missing {needle}"
    for label, path in (("INDEX", "docs/DOCUMENTATION_INDEX.md"), ("AGENTS", "AGENTS.md"),
                        ("CONTRACT", "CURRENT_PROOF_CONTRACT.md")):
        doc = read(path)
        assert "PROOF_DEPENDENCY_DAG.md" in doc and "FORMALIZATION_MILESTONES.md" in doc, label
    for label, doc in (("AGENTS", agent_policy), ("DYNAMIC", dynamic),
                       ("CONTRACT", proof_contract), ("STUDIO", setup)):
        assert "RH_PROOF_ATTACK_PORTFOLIO_20261024.md" in doc, label
    assert "AGENT_STUDIO_20261024_SEVEN_PROMPTS.md" in setup
    assert "EXACT IDENTITY" in overlap and "EXACT WEIGHTED PROJECTION" in overlap
    assert "INDEPENDENT ARITHMETIC GAIN" in overlap and "CORR-4" in overlap
    assert "7/8" in overlap and "m(B)" in overlap, "missing baseline power audit"
    for label, doc in (("AGENTS", agent_policy), ("DYNAMIC", dynamic),
                       ("CONTRACT", proof_contract), ("PORTFOLIO", portfolio),
                       ("STUDIO PROMPTS", prompts)):
        assert "RH_PROOF_OVERLAP_AND_SEVEN_EIGHTHS_AUDIT_20261024.md" in doc, label
    for path in (
        "AGENTS.md",
        "CURRENT_PROOF_CONTRACT.md",
        "docs/DYNAMIC_RESEARCH_AGENTS.md",
        "docs/RH_PROOF_ATTACK_PORTFOLIO_20261024.md",
        "docs/AGENT_STUDIO_20261024_SEVEN_PROMPTS.md",
        "docs/RESEARCH_FRONTIER_DAG.md",
        "docs/RH_PROOF_OVERLAP_AND_SEVEN_EIGHTHS_AUDIT_20261024.md",
        "docs/PROOF_DEPENDENCY_DAG.md",
        "docs/FORMALIZATION_MILESTONES.md",
        "README.md",
    ):
        assert (chr(92) + chr(96)) not in read(path), f"escaped Markdown backtick in {path}"
    print("PASS: 10 routes; 7 Studio roles; rigorously labelled equivalence and 7/8 gates; "
          "proof DAG and von Koch milestone present; PR states from dated snapshot")


if __name__ == "__main__":
    main()

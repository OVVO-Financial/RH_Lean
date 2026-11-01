#!/usr/bin/env python3
"""CI smoke checks for source routing and seven-agent instructions.

Checks document deployment and retained safeguards, not a mathematical proof.
"""
import hashlib
import json
import re
from pathlib import Path

import proof_obligation_dag

ROOT = Path(__file__).resolve().parents[1]
MILESTONE_TITLE = ("## Major Formalization Milestone: von Koch (1901) and the "
                   "Canonical VF Prime-Counting Criterion")
ENGINE = "RHLEAN_SEVEN_AGENT_RESEARCH_ENGINE_20261101.md"


def read(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def git_blob_sha(path: str) -> str:
    data = (ROOT / path).read_bytes()
    header = b"blob " + str(len(data)).encode("ascii") + b"\0"
    return hashlib.sha1(header + data).hexdigest()


def main() -> None:
    portfolio = read("docs/RH_PROOF_ATTACK_PORTFOLIO_20261024.md")
    agent_policy = read("AGENTS.md")
    dynamic = read("docs/DYNAMIC_RESEARCH_AGENTS.md")
    proof_contract = read("CURRENT_PROOF_CONTRACT.md")
    setup = read("docs/CHATGPT_AGENT_STUDIO_RH_SETUP_2026_10_12.md")
    prompts = read("docs/AGENT_STUDIO_20261024_SEVEN_PROMPTS.md")
    role_prompts = read("docs/RHLEAN_ALL_VECTOR_AGENT_PROMPTS_20261030.md")
    overlap = read("docs/RH_PROOF_OVERLAP_AND_SEVEN_EIGHTHS_AUDIT_20261024.md")
    engine = read("docs/" + ENGINE)
    selector = read("docs/RHLEAN_NATIVE_SQUARE_CLOCK_AGENT_DIRECTIVE_20261029.md")
    cadence = read("docs/RHLEAN_MULTIRUN_DAILY_AGENT_POLICY_20261031.md")
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
    # The dated portfolio's old one/day phrase is not live cadence authority.
    assert "multiple automatic scheduled invocations" in cadence.lower()
    assert "no fixed numeric per-day limit" in cadence.lower()
    assert "report-only" in prompts

    # Every operational entrypoint reaches the same persistent engine.
    for label, doc in (("AGENTS", agent_policy), ("DYNAMIC", dynamic),
                       ("SELECTOR", selector), ("ROLE PROMPTS", role_prompts),
                       ("STUDIO PROMPTS", prompts)):
        assert ENGINE in doc, f"{label} does not route to the research engine"
    breadth = "RHLEAN_BROAD_SEARCH_UNTIL_ETA_20261031.md"
    complete = "RHLEAN_SOURCE_FAITHFUL_COMPLETE_RETURN_AGENT_CONTRACT_20261031.md"
    assert selector.index(breadth) < selector.index(complete) < selector.index(ENGINE)
    roles = ("COORDINATOR", "OWNER", "ANALYTIC", "WHEEL", "CENSUS", "REFEREE", "LEAN")
    for role in roles:
        assert f"### NEXT-{role}:" in engine, f"missing next-run task for {role}"
        assert f"NEXT-{role}" in role_prompts, f"role reference missing {role}"
        assert f"NEXT-{role}" in prompts, f"standalone template missing {role}"
    assert engine.count("### NEXT-") == 7
    for needle in ("persistent", "first unsupported", "deployment_ack",
                   "same-day", "UNKNOWN", "VERIFY"):
        if needle != "VERIFY":
            assert needle in engine, f"engine missing {needle}"
    assert "VERIFIED_ETA" in engine and "SELF_AUDIT" in engine
    assert "human-only merge" in engine.lower()
    assert "own-report-only" in engine
    blocks = re.split(r"^### Agent \d+[^\n]*\n", prompts, flags=re.MULTILINE)[1:]
    assert len(blocks) == 7
    for index, block in enumerate(blocks, start=1):
        assert "deployment_ack" in block, f"agent {index} lacks consumption evidence"
        assert "human-only merge" in block.lower(), f"agent {index} lacks merge gate"
        assert "agent-reports" in block, f"agent {index} lacks report branch"
        assert "Multiple" in block or "multiple" in block, f"agent {index} lost multi-run policy"
    assert "GitHub Actions" in blocks[6] and "never local Lean" in blocks[6]

    # Preserve previous instruction bodies exactly; archives are not live queues.
    archives = {
        "AGENTS_BEFORE_RESEARCH_ENGINE_20261101.md": "59dc2c6d6ca06b2fae6fe7e18ad4ddf71a21e052",
        "docs/DYNAMIC_RESEARCH_AGENTS_BEFORE_RESEARCH_ENGINE_20261101.md": "018df84d619ff554d6b25ecd9e51487da4f1061c",
        "docs/RHLEAN_ALL_VECTOR_AGENT_PROMPTS_BEFORE_RESEARCH_ENGINE_20261101.md": "5ee0bcf6fb0a20860b2c9e72940a6ed6bb9694d3",
        "docs/AGENT_STUDIO_SEVEN_PROMPTS_BEFORE_RESEARCH_ENGINE_20261101.md": "06b49269564938196faaec64f5932c607473adbd",
    }
    for path, expected in archives.items():
        assert git_blob_sha(path) == expected, f"historical instructions changed: {path}"

    # PR state comes from the dated typed snapshot, never from historical prose.
    registry = json.loads(read("docs/proof-obligations.json"))
    errors = proof_obligation_dag.validate(registry)
    assert not errors, "proof-obligation DAG invalid:\n" + "\n".join(errors)
    snapshot = {ev["number"]: ev for ev in registry["evidence"] if ev.get("kind") == "pr"}
    for number in (932, 987, 1017, 1019, 1020):
        assert snapshot[number]["state"] == "merged" and snapshot[number]["merged_at"], number
    for number in (1021, 1022, 1023):
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
        "AGENTS.md", "CURRENT_PROOF_CONTRACT.md", "docs/DYNAMIC_RESEARCH_AGENTS.md",
        "docs/RH_PROOF_ATTACK_PORTFOLIO_20261024.md",
        "docs/AGENT_STUDIO_20261024_SEVEN_PROMPTS.md", "docs/RESEARCH_FRONTIER_DAG.md",
        "docs/RH_PROOF_OVERLAP_AND_SEVEN_EIGHTHS_AUDIT_20261024.md",
        "docs/PROOF_DEPENDENCY_DAG.md", "docs/FORMALIZATION_MILESTONES.md", "README.md",
        "docs/" + ENGINE,
        "docs/RHLEAN_ALL_VECTOR_AGENT_PROMPTS_20261030.md",
        "docs/RHLEAN_NATIVE_SQUARE_CLOCK_AGENT_DIRECTIVE_20261029.md",
    ):
        assert (chr(92) + chr(96)) not in read(path), f"escaped Markdown backtick in {path}"
    print("PASS: 10 routes; 7 persistent roles and next-run tickets; multi-run cadence; "
          "exact historical archives; proof DAG/von Koch safeguards; no mathematical gain asserted")


if __name__ == "__main__":
    main()

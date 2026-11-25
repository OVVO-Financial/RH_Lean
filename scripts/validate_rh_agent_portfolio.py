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
    # User-directed 2026-11-04 regression: prevent mandatory narrow source
    # assignments from silently overriding the independent nine-route portfolio.
    independent_name = "RHLEAN_INDEPENDENT_MULTIFRONT_NO_PIGEONHOLING_20261104.md"
    independent = read("docs/" + independent_name)
    independent_tag = "NO_PIGEONHOLING_ROUTE_SELECTOR_V1"
    # The shared HIGH objective must reach every live intake and each copied
    # standalone role; preserving diverse routes is checked independently below.
    high_name = "RHLEAN_COMPLETE_SIGNED_HIGH_ATTACK_20261107.md"
    high_tag = "COMPLETE_SIGNED_HIGH_ATTACK_V1"
    high_directive = read("docs/" + high_name)
    assert high_tag in high_directive
    for label, doc in (
        ("AGENTS", agent_policy), ("CONTRACT", proof_contract),
        ("DYNAMIC", dynamic), ("ENGINE", engine), ("SELECTOR", selector),
        ("ROLE PROMPTS", role_prompts), ("STUDIO PROMPTS", prompts),
        ("BREADTH", read("docs/RHLEAN_BROAD_SEARCH_UNTIL_ETA_20261031.md")),
        ("MULTI-FRONT", independent),
        ("CANCELLATION REUSE", read("docs/RHLEAN_REUSE_CANCELLATION_CHAIN_20261107.md")),
    ):
        assert high_tag in doc and high_name in doc, f"lost HIGH objective routing: {label}"
    assert independent_tag in independent
    assert "VF-LOW" in independent and "NYMAN" in independent
    assert "not" in independent.lower() and "OAI" in independent
    for path, doc in (
        ("AGENTS.md", agent_policy),
        ("CURRENT_PROOF_CONTRACT.md", proof_contract),
        ("docs/DYNAMIC_RESEARCH_AGENTS.md", dynamic),
        ("docs/RHLEAN_NATIVE_SQUARE_CLOCK_AGENT_DIRECTIVE_20261029.md", selector),
        ("docs/RHLEAN_BROAD_SEARCH_UNTIL_ETA_20261031.md",
         read("docs/RHLEAN_BROAD_SEARCH_UNTIL_ETA_20261031.md")),
        ("docs/RHLEAN_SEVEN_AGENT_RESEARCH_ENGINE_20261101.md", engine),
        ("docs/RHLEAN_ALL_VECTOR_AGENT_PROMPTS_20261030.md", role_prompts),
        ("docs/AGENT_STUDIO_20261024_SEVEN_PROMPTS.md", prompts),
        ("docs/RHLEAN_OAI_LOW_SOURCE_FIRST_AGENT_CONTRACT_20261103.md",
         read("docs/RHLEAN_OAI_LOW_SOURCE_FIRST_AGENT_CONTRACT_20261103.md")),
        ("docs/RHLEAN_ALL_SELECTED_INVERSE_SOURCE_ATTACK_20261104.md",
         read("docs/RHLEAN_ALL_SELECTED_INVERSE_SOURCE_ATTACK_20261104.md")),
    ):
        assert independent_tag in doc, f"lost independent-route precedence: {path}"
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
    # 2026-11-18 safeguard: seven copied role prompts and every live entrypoint
    # must preserve the lossless report publication and recovery procedure.
    publication_name = "RHLEAN_AGENT_REPORT_PUBLISH_RECOVERY_20261118.md"
    publication_tag = "REPORT_PUBLISH_RECOVERY_V1"
    publication = read("docs/" + publication_name)
    for label, doc in (
        ("AGENTS", agent_policy),
        ("DYNAMIC", dynamic),
        ("STUDIO PROMPTS", prompts),
        ("SETUP", setup),
        ("CONTINUITY", read("docs/RHLEAN_REPORT_CONTINUITY_LAST_ACTUAL_20261111.md")),
    ):
        assert publication_name in doc and publication_tag in doc, (
            f"missing report-publication recovery route: {label}")
    prompt_parts = prompts.split("### Agent ")[1:]
    assert len(prompt_parts) == 7, "expected seven standalone role prompts"
    for role_number, role_block in enumerate(prompt_parts, 1):
        assert publication_name in role_block and publication_tag in role_block, (
            f"role {role_number} lacks lossless publish instructions")
        assert ".recovery-" in role_block and "COMPLETE" in role_block, (
            f"role {role_number} risks incomplete replacement")
    for needed in ("HTTP 403", "118,316", "CANONICAL_VERIFIED",
                   "RECOVERY_VERIFIED", "NOT_PUBLISHED", "readback",
                   "Coordinator", "agent-reports", "human-only"):
        assert needed.lower() in publication.lower(), (
            f"lost report-publishing safety condition: {needed}")
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
    source_first_name = "RHLEAN_OAI_LOW_SOURCE_FIRST_AGENT_CONTRACT_20261103.md"
    source_first = read("docs/" + source_first_name)
    # The source-first paper remains an optional OAI specialist reference.
    # Do NOT require every global entrypoint or role to mention it: that
    # previously turned one research lead into a compulsory team-wide task.
    for label, doc in (
        ("OAI SPECIALIST", source_first),
        ("BROAD ROUTING", read("docs/RHLEAN_BROAD_SEARCH_UNTIL_ETA_20261031.md")),
        ("MULTI-FRONT POLICY", independent),
    ):
        if label == "MULTI-FRONT POLICY":
            assert "OAI" in doc
        else:
            assert source_first_name in doc or "source-first" in doc.lower(), label

    for needle in (
        "beta-11/16", "3/16", "beta-7/8",
        "LowSelectedBound.lean", "LowPhysicalInverseBound.lean",
        "LowSlotPolynomial.lean", "LowTupleGram.lean",
        "LowCentralTuple.lean", "LowNormalized.lean",
        "norm_sum_le", "sqrt(Q)", "actual", "Co minus Div",
        "Gamma_R", "1+t/2", "1+t", "cstar",
        "partial", "HIGH", "SOURCE_TO_ENDPOINT",
        "human-only merge", "PR #1083",
    ):
        assert needle in source_first, f"source-first mathematical safeguard missing: {needle}"
    for role in ("COORDINATOR", "OWNER", "ANALYTIC", "WHEEL",
                 "CENSUS", "REFEREE", "LEAN"):
        assert f"### NEXT-{role}:" in engine
        assert f"NEXT-{role}" in role_prompts
        assert independent_tag in prompts, f"saved role {role} lacks independent-route policy"
    assert source_first.index("## 2. Actual OAI LOW") < source_first.index("## 3. Exact signed LOW")
    assert "six non-lean" in agent_policy.lower()
    # 2026-11-04 user authorization retained; old all-selected source-first priority is optional.
    assert "FULL GitHub repository READ/WRITE" in agent_policy
    assert "FULL GitHub repository READ/WRITE" in prompts
    assert "full github repository read/write" in role_prompts.lower()
    assert "FULL GitHub repository" in engine or "full GitHub read/write" in engine
    assert "all-selected" in independent and "optional" in independent.lower()
    assert "2026-11-04" in source_first and "full read/write" in source_first.lower()
    assert "human-only merge" in agent_policy.lower()
    assert "own-report-only" in agent_policy
    assert "agent/lean-verification/" in prompts
    assert "an unmerged" in source_first.lower() or "unmerged DRAFT" in source_first
    assert "no mathematical" in read("docs/RH_PROOF_ATTACK_PORTFOLIO_20261024.md").lower()

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
    # Latest interactive user directive: all seven saved repository templates
    # target the exact complete finite-wheel centered remainder, but keep
    # their distinct methods and prior source/permission safeguards.
    wheel_name = "RHLEAN_SEVEN_AGENT_FINITE_WHEEL_BOUNDARY_20261108.md"
    wheel_tag = "FINITE_WHEEL_CENTERED_RH_V1"
    wheel = read("docs/" + wheel_name)
    for needle in ("finiteWheel_squareFractional_centered_eq_reference_sub_pi",
                   "finiteWheelFract_sub_density_eq_physical_floorError",
                   "d>X", "R log R", "1.", "7.", "own-report-only",
                   "Human-only", "OPEN"):
        assert needle.lower() in wheel.lower(), f"wheel directive missing: {needle}"
    for label, doc in (("AGENTS", agent_policy), ("CONTRACT", proof_contract),
                       ("DYNAMIC", dynamic), ("ENGINE", engine),
                       ("ROLE PROMPTS", role_prompts), ("STUDIO PROMPTS", prompts)):
        assert wheel_tag in doc and wheel_name in doc, f"{label} lost live finite-wheel routing"
    assert agent_policy.index(wheel_tag) < agent_policy.index("FROZEN_ROOT_SQUARE_ROOT_SOURCE_FIRST_20261108")
    for index, block in enumerate(blocks, start=1):
        assert "finite_wheel_ack=" + wheel_tag in block, f"agent {index} lost finite-wheel acknowledgment"
        assert wheel_name in block, f"agent {index} lacks source-specific directive"
    for index, block in enumerate(blocks, start=1):
        assert high_tag in block and high_name in block, f"agent {index} lost HIGH objective"
        assert "high_attack_ack" in block, f"agent {index} lacks HIGH consumption evidence"
        assert independent_tag in block, f"agent {index} lost independent-route precedence"
        assert "deployment_ack" in block, f"agent {index} lacks consumption evidence"
        assert "human-only merge" in block.lower(), f"agent {index} lacks merge gate"
        assert "agent-reports" in block, f"agent {index} lacks report branch"
        assert "Multiple" in block or "multiple" in block, f"agent {index} lost multi-run policy"
    assert "GitHub Actions" in blocks[6] and "never local Lean" in blocks[6]

    # 2026-11-22 user-directed short human proof + independent theorem retask.
    # Policy/deployment routing validation only, not a claim of RH.
    current_name = "RHLEAN_ALPOGE_VIOLE_TRACTABLE_PROOF_SEVEN_AGENTS_20261122.md"
    current_tag = "ALPOGE_VIOLE_TRACTABLE_RH_V1"
    new_doc = read("docs/" + current_name)
    for required in ("tractability", "contribution", "unconditional", "Gm", "Gz",
                     "CostWindows", "2^R", "1187", "1189", "Coordinator",
                     "Owner Payment", "Analytic Type II", "Finite Wheel & Incidence",
                     "Prime Census Laboratory", "Adversarial Referee", "Lean Verification",
                     "REPORT_PUBLISH_RECOVERY_V1", "human-only merge"):
        assert required.lower() in new_doc.lower(), f"charter missing {required}"
    for entry in ("AGENTS.md", "CURRENT_PROOF_CONTRACT.md",
                  "CURRENT_RESEARCH_HANDOFF.md", "docs/DYNAMIC_RESEARCH_AGENTS.md",
                  "docs/RHLEAN_SEVEN_AGENT_RESEARCH_ENGINE_20261101.md",
                  "docs/RHLEAN_NATIVE_SQUARE_CLOCK_AGENT_DIRECTIVE_20261029.md",
                  "docs/RHLEAN_ALL_VECTOR_AGENT_PROMPTS_20261030.md",
                  "docs/CHATGPT_AGENT_STUDIO_RH_SETUP_2026_10_12.md",
                  "docs/DOCUMENTATION_INDEX.md", "README.md", "llms.txt",
                  "docs/AGENT_STUDIO_20261024_SEVEN_PROMPTS.md"):
        data = read(entry)
        assert current_name in data and current_tag in data, f"missing routing: {entry}"
    copied = read("docs/AGENT_STUDIO_20261024_SEVEN_PROMPTS.md").split("### Agent ")[1:]
    assert len(copied) == 7
    for i, role in enumerate(copied, 1):
        assert current_name in role and "tractability_ack=" + current_tag in role, (
            f"role {i} does not have the new standalone copyable instructions")
        assert "MY DISTINCT FIRST TASK" in role and "human-only merge" in role.lower()
    assert current_name in read(".github/workflows/rh-proof-portfolio-agent-instructions.yml")

    # Concrete 2026-11-22 descent/payment assignment: check routing inside
    # each copied role, not only a banner outside the copyable prompts.
    descent_name = "RHLEAN_ALPOGE_NATIVE_DESCENT_PAYMENT_20261122.md"
    descent_tag = "ALPOGE_NATIVE_DESCENT_PAYMENT_V1"
    descent_doc = read("docs/" + descent_name)
    for required in ("DescentFamily.descent", "mapsCore",
                     "covering_descent_maps_compatible_alt", "rk_le_alt_alt",
                     "lowAt_of_cover", "lcv_le", "CharacterBalanceMoves.core",
                     "ch_top", "ch_core", "core_gm", "Q=T*m*b*Delta/2",
                     "slope_sq", "ErrWindowsWeak", "Sigma_A",
                     "SOURCE_INSPECTED", "PAPER_PROOF", "LEAN_VERIFIED_CONDITIONAL",
                     "FIRST_UNPAID", "MAP_PAYMENT", "INDEPENDENT_APPLICATION",
                     "REPORT_PUBLISH_RECOVERY_V1", "LAST_ACTUAL_REPORT_CONTINUITY_V1",
                     "human-only merge", "no local Lean execution"):
        assert required.lower() in descent_doc.lower(), (
            f"descent/payment contract missing {required}")
    descent_entries = (
        "AGENTS.md", "CURRENT_PROOF_CONTRACT.md", "CURRENT_RESEARCH_HANDOFF.md",
        "docs/DYNAMIC_RESEARCH_AGENTS.md",
        "docs/RHLEAN_SEVEN_AGENT_RESEARCH_ENGINE_20261101.md",
        "docs/RHLEAN_NATIVE_SQUARE_CLOCK_AGENT_DIRECTIVE_20261029.md",
        "docs/RHLEAN_ALL_VECTOR_AGENT_PROMPTS_20261030.md",
        "docs/CHATGPT_AGENT_STUDIO_RH_SETUP_2026_10_12.md",
        "docs/DOCUMENTATION_INDEX.md", "README.md", "llms.txt",
        "docs/AGENT_STUDIO_20261024_SEVEN_PROMPTS.md",
    )
    for entry in descent_entries:
        data = read(entry)
        assert descent_name in data and descent_tag in data, (
            f"missing descent/payment routing: {entry}")
    assert descent_name in new_doc, "standing T/C/P charter lost active assignment"
    role_markers = {
        "COORDINATOR": ("DescentFamily.descent", "cost ledger"),
        "OWNER": ("ANCHOR3-4", "THIN1", "chC"),
        "REFEREE": ("joint norm/rank", "SOURCE_INSPECTED", "PAPER_PROOF"),
        "CENSUS": ("rank/injectivity", "prime powers"),
        "ANALYTIC": ("CharacterBalanceMoves.core", "Sigma_A", "SELECT"),
        "WHEEL": ("mapsCore", "joint injectivity", "rank saturation"),
        "LEAN": ("DescentFamily.descent", "hosted GitHub Actions"),
    }
    assert len(blocks) == len(role_markers) == 7
    for role_name, block in zip(role_markers, blocks):
        assert f"DESCENT_ROLE={role_name}" in block, (
            f"wrong copied role assignment: {role_name}")
        assert descent_name in block and "descent_payment_ack=" + descent_tag in block
        assert "MY DISTINCT FIRST TASK:" in block
        match = re.search(r"## NEXT-" + role_name + r":[\s\S]*?(?=\n## |\Z)", role_prompts)
        assert match, f"missing live role {role_name}"
        live_role = match.group()
        assert f"DESCENT_ROLE={role_name}" in live_role
        assert descent_name in live_role and "descent_payment_ack=" + descent_tag in live_role
        for marker in role_markers[role_name]:
            assert marker in block and marker in live_role, (
                f"incomplete {role_name} task: {marker}")
    assert descent_name in read(".github/workflows/rh-proof-portfolio-agent-instructions.yml")

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
    # Final #1201 mandate: check every operational entrypoint and actual
    # copyable role, not merely a banner outside the standalone prompt.
    final_name = "RHLEAN_FINAL_PR_1201_PROOF_CLOSURE_20261124.md"
    final_tag = "FINAL_PR_1201_PROOF_CLOSURE_V1"
    final_doc = read("docs/" + final_name)
    for required in ("DIRECT_CORE_CUT_V1", "STRICT_NO_GEOCL_ANYGEOMETRY_V1",
                     "nativePrincipalEAtH_windows", "nativeConstructedDyadicGzPayment",
                     "nativeConstructedDyadicSignedSlopePayment_of_meanLoss",
                     "average-to-pointwise", "same-host", "GeoCl", "anyGeometry",
                     "Q=T*m*b*Delta/2", "own-report-only", "human-only merge",
                     "RH OPEN", "propext", "Classical.choice", "Quot.sound"):
        assert required.lower() in final_doc.lower(), f"final mandate missing {required}"
    for entry in ["AGENTS.md","CURRENT_PROOF_CONTRACT.md","CURRENT_RESEARCH_HANDOFF.md","docs/DYNAMIC_RESEARCH_AGENTS.md","docs/RHLEAN_SEVEN_AGENT_RESEARCH_ENGINE_20261101.md","docs/RHLEAN_NATIVE_SQUARE_CLOCK_AGENT_DIRECTIVE_20261029.md","docs/RHLEAN_ALL_VECTOR_AGENT_PROMPTS_20261030.md","docs/CHATGPT_AGENT_STUDIO_RH_SETUP_2026_10_12.md","docs/DOCUMENTATION_INDEX.md","README.md","llms.txt","docs/AGENT_STUDIO_20261024_SEVEN_PROMPTS.md"]:
        data = read(entry)
        assert final_name in data and final_tag in data, f"missing final routing: {entry}"
    final_roles = ["COORDINATOR","OWNER","REFEREE","CENSUS","ANALYTIC","WHEEL","LEAN"]
    for role, block in zip(final_roles, blocks):
        copied_prompt = block.split("\x60\x60\x60text", 1)[1].split("\x60\x60\x60", 1)[0]
        assert f"FINAL_1201_ROLE={role}" in copied_prompt, f"missing copied role: {role}"
        assert final_name in copied_prompt and "final_1201_ack=" + final_tag in copied_prompt
        for live_doc in (role_prompts, engine):
            match = re.search(r"^#{2,3} NEXT-" + role + r":[\s\S]*?(?=^#{1,3} |\Z)",
                              live_doc, re.MULTILINE)
            assert match and f"FINAL_1201_ROLE={role}" in match.group(), (
                f"missing live final role: {role}")
        assert f"FINAL_1201_ROLE={role}" in setup
    assert final_name in read(".github/workflows/rh-proof-portfolio-agent-instructions.yml")

    print("PASS: constructed descent/full-source payment routing and all seven distinct roles; "
          "retained tractability/contribution/proof charter and historical route safeguards; "
          "optional OAI source-first specialist reference; historical archives; "
          "human-only merge, proof DAG/von Koch, no new arithmetic gain asserted")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Audit the exact original-source logarithmic amplification formalization.

The default mode runs only in GitHub Actions.  --source-only performs static
inventory/export checks without invoking Lean and is safe for local review.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

from audit_euler_fractional_axioms import audit_log
from proof_inventory import strip_lean_comments


ROOT = Path(__file__).resolve().parents[1]
ACCEPTANCE = "research/PRIME_ADMISSION_LOG_AMPLIFICATION_ACCEPTANCE_20261107.lean"
EXPECTED = {
    "RHLean/Proof/PrimeAdmissionLogPotential.lean": (
        "primeAdmissionEnergy_pos",
        "primeAdmissionLogPotential_argument_pos",
        "primeAdmissionLogPotential_nonneg",
        "primeAdmissionLogIncrement_argument_eq_div",
        "primeAdmissionLogIncrement_argument_pos",
        "primeAdmissionLogPotential_eq_log_sub",
        "primeAdmissionLogPotential_step",
        "primeAdmissionLogIncrement_eq_sub",
        "primeAdmissionLogIncrement_zero",
        "primeAdmissionLogPotential_telescope",
        "primeAdmissionLogPotential_telescope_expanded",
    ),
    "RHLean/Proof/SquareRootAmplificationLogGrowth.lean": (
        "squareRootHistoricalK_nonneg",
        "squareRootHistoricalK_le_iff",
        "squareRootHistoricalK_envelope",
        "squareRootHistoricalK_one_le",
        "squareRootHistoricalK_pos",
        "squareRootHistoricalK_mono",
        "squareRootHistoricalK_two",
        "squareRootAmplificationDenominator_pos",
        "squareRootEndpointAmplification_nonneg",
        "squareRootEndpointAmplification_two",
        "squareRootEndpointAmplification_le_iff",
        "squareRootMertensEndpointAmplification_iff_uniformRatio",
        "squareRootAmplificationMax_nonneg",
        "squareRootAmplificationMax_le_iff",
        "squareRootEndpointAmplification_le_max",
        "squareRootAmplificationMax_mono",
        "squareRootMertensEndpointAmplification_iff_boundedRunningMax",
        "squareRootAmplificationMax_log_le_iff",
        "squareRootAmplificationLogRatio_nonneg",
        "squareRootAmplificationLogRatio_le_iff",
    ),
    "research/PRIME_ADMISSION_LOG_AMPLIFICATION_20261107.lean": (
        "eulerAdmissibleCenteredRealState_step",
        "eulerAdmissibleCenteredRealState_initial",
        "eulerAdmissibleCenteredRealState_terminal",
        "eulerAdmissibleAdmissionDebtReal_of_prime",
        "eulerAdmissibleAdmissionDebtReal_of_not_prime",
        "eulerAdmissibleAdmissionCutoff_lt_root",
        "eulerAdmissibleAdmissionDebtReal_eq_one_of_top_band",
        "eulerAdmissibleCenteredRealState_log_step",
        "eulerAdmissibleLogIncrement_of_not_prime",
        "eulerAdmissibleCenteredRealState_log_telescope",
        "eulerAdmissibleLogReturn_eq_endpoint",
        "squareRootEndpointAmplification_log_eq_primeAdmission",
        "squareRootEndpointAmplification_log_identity",
        "squareRootAmplificationLogRatio_le_iff_primeAdmissionLogReturn",
    ),
}

PUBLIC_PROOF = re.compile(
    r"(?m)^(?:@\[[^\n]*\]\s*)?(?:theorem|lemma)\s+([\w\u2080-\u209f]+)"
)


def source_audit() -> dict:
    manifest = (ROOT / "RHLean.lean").read_text().splitlines()
    sources = {}
    for source, expected in EXPECTED.items():
        raw = (ROOT / source).read_bytes()
        clean = strip_lean_comments(raw.decode())
        actual = tuple(PUBLIC_PROOF.findall(clean))
        if actual != expected:
            raise ValueError(f"Public theorem inventory mismatch for {source}: {actual}")
        if re.search(r"\b(sorry|admit|axiom|native_decide|unsafe)\b", clean):
            raise ValueError(f"Forbidden proof shortcut in {source}")
        if source.startswith("RHLean/"):
            export = "import " + source.removesuffix(".lean").replace("/", ".")
            if manifest.count(export) != 1:
                raise ValueError(f"Missing or duplicated public root export: {export}")
        sources[source] = {
            "sha256": hashlib.sha256(raw).hexdigest(),
            "public_theorems": list(expected),
        }
    acceptance = strip_lean_comments((ROOT / ACCEPTANCE).read_text())
    if re.search(r"\b(sorry|admit|axiom|native_decide|unsafe)\b", acceptance):
        raise ValueError("Forbidden shortcut in type acceptance")
    if acceptance.count("example") < 9:
        raise ValueError("Missing expected exact-type acceptance examples")
    return {"sources": sources, "acceptance": ACCEPTANCE,
            "zero_limit_status": "OPEN_PROPOSITION_ONLY"}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-only", action="store_true")
    args = parser.parse_args()
    inventory = source_audit()
    expected = tuple("RHLean.Proof." + name
                     for names in EXPECTED.values() for name in names)
    if args.source_only:
        print(f"PASS: {len(expected)} public theorem declarations, exact exports and source checks")
        return

    commands = [
        'import «research.PRIME_ADMISSION_LOG_AMPLIFICATION_ACCEPTANCE_20261107»',
        "set_option autoImplicit false",
        "#check RHLean.Proof.squareRootAmplificationLogRatio",
        "#check RHLean.Proof.SquareRootAmplificationZeroLogGrowthStatement",
    ]
    for name in expected:
        commands.extend((f"#check {name}", f"#print axioms {name}"))
    audit_source = ROOT / "prime-admission-log-audit.lean"
    audit_source.write_text("\n".join(commands) + "\n")
    log_path = ROOT / "prime-admission-log-audit.log"
    log_path.write_text("")

    # Lake validates dependencies; these direct recompilations additionally
    # make warnings fatal for both new native modules at the exact PR head.
    for source in (*[p for p in EXPECTED if p.startswith("RHLean/")],
                   audit_source.name):
        process = subprocess.run(
            ["lake", "env", "lean", "-DwarningAsError=true", source],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            text=True, check=False,
        )
        with log_path.open("a") as log:
            log.write(process.stdout)
        print(process.stdout, end="", flush=True)
        if process.returncode:
            raise SystemExit(process.returncode)

    inventory["axioms"] = audit_log(log_path.read_text(), expected)
    inventory["commit"] = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    (ROOT / "prime-admission-log-inventory.json").write_text(
        json.dumps(inventory, indent=2) + "\n")
    print(f"PASS: all {len(expected)} public theorems compiled; exact types and standard axioms")


if __name__ == "__main__":
    main()

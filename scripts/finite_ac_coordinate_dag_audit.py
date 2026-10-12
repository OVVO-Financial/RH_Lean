#!/usr/bin/env python3
"""Full-source cross-coordinate audit for the finite-A/C and actual-VF seams.

This is a source/import index, NOT a kernel certificate or an RH argument.
The existing repo_index reads all Lean modules, research files and exports.
"""
from __future__ import annotations

import argparse
import json
import re
from collections import Counter, deque
from pathlib import Path

import repo_index

ROOT = Path(__file__).resolve().parents[1]

# Name plus exact path prevents confusing independent export copies and
# historical source occurrences with the current actual-prime result.
ANCHORS = [
    ("finite-A premise", "RHLean/Proof/SquareRootMertensEndpointAmplification.lean", "SquareRootMertensEndpointAmplificationStatement", "OPEN"),
    ("A equals legal Gram", "RHLean/Proof/SquareRootMertensEndpointAmplification.lean", "squareRootMertensEndpointAmplification_iff_legalAncestryGram", "equivalence only"),
    ("signed ancestry numerator", "RHLean/Proof/SquareRootLegalAncestryGramReduction.lean", "sourceRootPrefix_sub_sourceSuccessorPrefix_eq_mertensInt_sub_one", "exact"),
    ("parent fibre counting", "RHLean/Proof/SquareRootAncestryParentFibres.lean", "sourceSuccessorPrefix_eq_sum_multiplicity_mul_weight", "exact"),
    ("wheel-to-ancestry ledger", "RHLean/Proof/WheelToLedgerPushforward.lean", "squareRootRootSuccessorCrossLedger_eq_orderedWheelCrossLedger", "exact"),
    ("sequential shell finite-A", "RHLean/Proof/LowWheelAncestryCrossLedgerBridge.lean", "squareRootSequentialCrossLedgerCoercivity_iff_mertensEndpointAmplification", "equivalence only"),
    ("cross-ledger endpoint slack", "RHLean/Proof/LowWheelAncestryCrossLedgerBridge.lean", "squareRootSequentialCrossLedgerCoercivityMargin_eq_endpointSlack", "exact"),
    ("owner-2 signed polarization", "research/OWNER_TWO_UPPER_HALF_POLARIZATION.lean", "squareEndpointMertensEnergyReal_eq_smooth_transport_polarization", "exact"),
    ("dyadic annulus equals M", "research/DYADIC_SMOOTH_HIGH_JOINT_PACKET.lean", "squareRootDyadicJointPacket_eq_squarePrefixMertens", "exact"),
    ("true VF dyadic run", "research/VF_MID_DYADIC_PREFIX_OWNER.lean", "vfMidPrimeError_sq_sub_sq_eq_prefixError_sub_lateCorrection", "exact"),
    ("run native tracking", "research/VF_MID_FIRST_BAD_LOWER_RUN_CAPACITOR.lean", "vfMidDyadicVFTrackingDefect_eq_frozenSafe_add_lowerTransport", "exact"),
    ("late survivor semiprime sign", "research/VF_MID_DYADIC_OWNER_EXACT.lean", "vfMidSquareBandPrefixComposite_moebius_eq_one_of_subdoubling", "exact"),
    ("first-bad source-payment", "research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean", "VFMid915FirstBadSourcePaymentStatement", "OPEN"),
    ("first-bad conditional consumer", "research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean", "vfMid915FirstBad_closed_of_sourcePayment", "conditional"),
    ("actual VF weighted source", "research/VF_MID_FIRST_BAD_WEIGHTED_OWNER_FUBINI.lean", "vfMidOneBlockActivePhysicalSite", "exact physical site"),
    ("actual VF clipped x admitted", "research/VF_MID_FIRST_BAD_ACTIVE_RAW_PARENT_SPLICE.lean", "vfMidActiveReturnedPairCarrier", "exact carrier"),
    ("actual VF six boundaries", "research/VF_MID_FIRST_BAD_ACTIVE_RAW_PARENT_SPLICE.lean", "vfMidActiveCellGram_eq_sixOrientedBoundary", "exact VF-weighted"),
    ("actual VF three-boundary", "research/VF_MID_FIRST_BAD_FINAL_AGGREGATE_CONTRACTION.lean", "vfMidFirstBadAnchoredCoDivExcess_eq_activeResidual_add_threeBoundaryExcess", "exact VF-weighted"),
    ("heat is equivalent to unpaid inlet", "research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean", "vfMidActiveResidual_sharpTransport_iff_sourceInlet", "equivalence only"),
    ("different admitted pair carrier", "research/GLOBAL_RETURNED_CORE_UNIQUE_OWNER_CONTINUATION_LEDGER.lean", "lowOwnerFirstOwnerAdmittedPositivePairCarrier", "exact carrier"),
    ("dirichlet six-sector split", "research/VF_MID_CENTERED_GREATEST_OWNER_RANK_TELESCOPE.lean", "lowOwnerFirstOwnerSignedCellTelescope_eq_noPersistenceSafe_add_sectorSix", "exact; different weight"),
    ("one pair rank descent", "research/VF_MID_FIRST_BAD_LOWER_RUN_CAPACITOR.lean", "vfMidNoPersistenceCapacitor_forces_sectorSixDescent", "conditional local capacity"),
    ("no internal square-run prime cube", "RHLean/Analysis/SquareRunFreshPrimeCubeBoundary.lean", "squareRunFreshPrimeOwner_cube_straddles", "exact boundary"),
    ("single prime leaf is RH-equivalent", "RHLean/Analysis/SquareRunTopEscapeClassification.lean", "squareRunPrimeLeafTopEscapeBounded_iff_mertensEnergy", "NO-GO"),
    ("prime averaging is RH-equivalent", "RHLean/Analysis/PrimeAveragedCubeEnergy.lean", "primeAveragedFrontierEnergyBounded_iff_mertensEnergyBounded", "NO-GO"),
    ("long range cofactor root is not injective", "research/DYADIC_LONG_RANGE_TETHER_AUDIT.lean", "squareRootLongRangeRoot_not_injective_at_56", "NO-GO"),
    ("low quotient necessary work", "research/VF_QUOTIENT_VARIATION_FIRSTBAD_ATTACK.lean", "vfVarSquareMertens_norm_le_four_lowVariation_add_two_shortMass", "exact reduction"),
    ("OAI physical centered moment", "research/VF_SHARP_OAI_SIGNED_MOMENT_ATTACK.lean", "vfSharpOAIActualGram_le_of_physical_centered_moment", "conditional"),
    ("actual chronological prime-comb response", "RHLean/Proof/PrimeCombVisualizationDynamics.lean", "primeCombTailSignedDelta_eq", "exact per-prime"),
    ("actual dyadic high-prime fibre", "RHLean/Proof/DyadicSurvivorMertensInvariant.lean", "dyadicLargePrimeSurvivorMass_eq_neg_mertens", "exact per-prime"),
    ("already proved prime-comb/dyadic fibre equality", "RHLean/Proof/DyadicSurvivorMertensInvariant.lean", "dyadicLargePrimeSurvivorMass_eq_primeCombLargePrimeFamilyMass", "exact"),
    ("new occurrence-preserving per-prime chrono/dyadic bridge", "research/FINITE_A_C_PRIME_COMB_DYADIC_OCCURRENCE_WELD.lean", "primeCombTailSignedDelta_eq_two_plus_dyadicSurvivor", "new exact, pending Lean"),
    ("new global signed chronological/dyadic bridge", "research/FINITE_A_C_PRIME_COMB_DYADIC_OCCURRENCE_WELD.lean", "primeCombPostRootSignedDeltaTotal_eq_primeNumber_add_dyadicSurvivor", "new exact, pending Lean"),
    ("square-root endpoint off-by-one lemma", "research/FINITE_A_C_PRIME_COMB_DYADIC_OCCURRENCE_WELD.lean", "squareRootEndpoint_natSqrt_eq_pred", "new endpoint identity, pending Lean"),
    ("physical generic/canonical root prime boundary correction", "research/FINITE_A_C_PRIME_COMB_DYADIC_OCCURRENCE_WELD.lean", "dyadicPostRootSurvivorMass_squareEndpoint_eq_transport_add_rootPacket", "new exact boundary correction, pending Lean"),
    ("original sign rule equivalent to no first bad", "research/VF_MID_FIRST_BAD_ACTUAL_ADMISSIBILITY_CERTIFICATE.lean", "vfV2ActualPrime_signedOwnerRule_iff_noFirstBad", "NO-GO"),
    ("owner-two compensated interior bound is already unconditional", "research/GLOBAL_RETURNED_CORE_OWNER_TWO_CLIPPED_EXIT.lean", "ownerTwoCompensatedInterior_fourEnergyBound_unconditional", "NO-GO"),
]
SEARCH = {
    "original first bad": r"FirstBad.*(source|payment|balance|budget)",
    "amplification or Gram": r"(amplification|legalAncestryGram|smoothAntiAlignment)",
    "chronological dyadic owner": r"(dyadic|chronological).*(owner|correction|packet)",
    "signed raw Fubini": r"(returned|signed|firstOwner).*(Fubini|transport|boundary|polarization)",
    "coercivity or contraction": r"(coerciv|contract|quarter).*(ledger|owner|square|reciproc)",
    "counterexamples and no-go": r"(NoGo|not_injective|iff_mertensEnergy|cannot|obstruction)",
    "OAI physical kernel": r"(OAI|principal|Hecke).*(physical|source|moment|ideal)",
    "run descent": r"(Run|run).*(descen|firstBad|capacitor|lateOwner)",
    "prime-comb vs dyadic": r"(primeComb|dyadic).*(Mertens|survivor|signedDelta|familyMass)",
}
COMPARE = [
    ("research/VF_MID_FIRST_BAD_ACTIVE_RAW_PARENT_SPLICE.lean",
     "research/VF_MID_CENTERED_GREATEST_OWNER_RANK_TELESCOPE.lean",
     "VF clipped/admitted vs Dirichlet admitted/admitted"),
    ("research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean",
     "research/VF_MID_CENTERED_GREATEST_OWNER_RANK_TELESCOPE.lean",
     "original first-bad source vs generic sector-six"),
    ("RHLean/Proof/LowWheelAncestryCrossLedgerBridge.lean",
     "research/DYADIC_SMOOTH_HIGH_JOINT_PACKET.lean",
     "finite-A ancestry vs physical dyadic annulus"),
    ("research/VF_MID_FIRST_BAD_LOWER_RUN_CAPACITOR.lean",
     "research/VF_MID_FIRST_BAD_ACTIVE_EXCESS_LEDGER.lean",
     "nonnegative scalar child count vs signed original VF pairs"),
]

def reaches(graph, a, b):
    if a == b:
        return True
    found = {a}
    queue = deque([a])
    while queue:
        u = queue.popleft()
        for v in graph.get(u, ()):
            if v == b:
                return True
            if v not in found:
                queue.append(v)
                found.add(v)
    return False

def audit(data):
    named = {}
    for d in data["declarations"]:
        file = data["files"][d["file_id"]]
        if file["view"] == "worktree":
            named.setdefault((file["path"], d["name"].split(".")[-1]), []).append(d)
    anchors = []
    for label,path,name,status in ANCHORS:
        d = named.get((path,name), [])
        anchors.append({"label":label,"path":path,"name":name,
                        "line":d[0]["line"] if d else None,
                        "kind":d[0]["kind"] if d else None,
                        "status":status})
    modules = {v["path"]:k for k,v in data["modules"].items()
               if v["view"]=="worktree" and v["project"]=="."}
    pairs=[]
    for path_a,path_b,label in COMPARE:
        a=modules.get(path_a)
        b=modules.get(path_b)
        pairs.append({"label":label,"a":path_a,"b":path_b,
                      "a_imports_b":bool(a and b and reaches(data["module_import_graph"],a,b)),
                      "b_imports_a":bool(a and b and reaches(data["module_import_graph"],b,a))})
    search={}
    for label,regex in SEARCH.items():
        hits=repo_index.search(data,regex,kind="declaration",regex=True,view="worktree")
        hits=[h for h in hits if h["scope"] in ("library","research")]
        search[label]={"declarations":len(hits),"top":[{"path":h["path"],"line":h["line"],"name":h["name"]}
                        for h in hits[:12]]}
    files=Counter(v["scope"] for v in data["files"].values() if v["view"]=="worktree")
    return {"source":data["provenance"],"counts":{"files":sum(files.values()),
            "modules":sum(1 for x in data["modules"].values() if x["view"]=="worktree"),
            "declarations":sum(1 for x in data["declarations"]
                               if data["files"][x["file_id"]]["view"]=="worktree"),
            "cycles":len(data["cyclic_components"])},
            "anchors":anchors,"comparisons":pairs,"search":search}

def render(a):
    stamp=a["source"]["views"][0]["commit"]
    lines=["# Finite A/C and actual-prime VF cross-coordinate source audit",
           "","Source commit: "+stamp,
           "SOURCE INDEX ONLY: not a Lean certificate or bound.",
           "",
           "Files: %s, modules: %s, declarations: %s, cycles: %s" %
           (a["counts"]["files"],a["counts"]["modules"],
            a["counts"]["declarations"],a["counts"]["cycles"]),
           "","## Exact declaration anchors",
           "","| Source coordinate | Declaration | Path:line | Evidence |",
           "| --- | --- | --- | --- |"]
    for d in a["anchors"]:
        at=d["path"]+":"+str(d["line"] or "MISSING")
        lines.append("| "+d["label"]+" | "+d["name"]+" | "+at+" | "+d["status"]+" |")
    lines += ["","## Import-reachability probes",
              "","Import reachability is not a physical-carrier identification.",
              "","| Probe | A imports B | B imports A |","| --- | --- | --- |"]
    for d in a["comparisons"]:
        lines.append("| "+d["label"]+" | "+str(d["a_imports_b"])+" | "+str(d["b_imports_a"])+" |")
    lines+=["","## Whole repository declaration searches",
            "","| Theme | declaration hits in research and library | top locations |",
            "| --- | ---: | --- |"]
    for label,d in a["search"].items():
        files=", ".join(x["path"] for x in d["top"][:3])
        lines.append("| "+label+" | "+str(d["declarations"])+" | "+files+" |")
    lines+=["","## Critical literal carrier obstruction",
        "","The ACTUAL VF weighted returned pair carrier in the first-bad active raw-parent splice is",
        "clippedBase(R+1,p,sig) x admittedBase(R+1,p,sig).",
        "The #903 recursive greatest-owner sector starts on admittedBase x admittedBase.",
        "The two supports are DISJOINT in the original p-cell: the same first coordinate",
        "cannot satisfy p*a > squareRootEndpoint(R+1) and p*a <= squareRootEndpoint(R+1).",
        "This proves a same-cell identity or ordinary inclusion CANNOT transfer the",
        "actual VF three-boundary charge into the existing #903 admitted sector-six charge.",
        "A bridge must be an ACTUAL historical-return / boundary-crossing map, preserving",
        "site-dependent VF weights and all original index multiplicities.",
        "",
        "## Status and necessary new mathematics",
        "",
        "The weighted VF source-to-its-own three/six oriented clipped boundary is ALREADY",
        "exact in the source. The #903 no-independent-persistence split and strict",
        "one-child PAIR rank descent are ALREADY exact, on a different Dirichlet carrier.",
        "A quantitative supercritical lower-child RUN bound and a literal signed",
        "cross-carrier transfer have NOT been established. The sharpened heat inequality",
        "is proved equivalent to the original unproved first-bad payment.",
        "",
        "Finite A/C are an independently sufficient alternative. Their endpoint scalar",
        "coercivity margin is exactly A*R^2*K-(M(R^2-1)-1)^2. Changing from ancestry,",
        "wheel, Othello, prime shell, or owner-two norm to that margin is NOT an estimate.",
        "The odd dyadic annulus is an existing escape wall, not a newly cancellable",
        "interior. A linear density/count does NOT upper-bound a quadratic pair Gram.",
        "No unconditional finite A, finite C or RH bound is claimed.",
        ""]
    return "\n".join(lines)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--strict",action="store_true")
    ap.add_argument("--markdown",type=Path,default=Path("finite-ac-coordinate-audit.md"))
    ap.add_argument("--json",type=Path,default=Path("finite-ac-coordinate-audit.json"))
    args=ap.parse_args()
    data=repo_index.load_index(ROOT,None,[])
    report=audit(data)
    args.markdown.write_text(render(report),encoding="utf-8")
    args.json.write_text(json.dumps(report,ensure_ascii=False,indent=2)+"\n",encoding="utf-8")
    missing=[x["name"] for x in report["anchors"] if x["line"] is None]
    print("Repository indexed:",report["counts"])
    print("Exact declarations located:",len(report["anchors"])-len(missing),"/",len(report["anchors"]))
    if missing:
        print("Missing:",missing)
    if args.strict and missing:
        return 1
    return 0

if __name__=="__main__":
    raise SystemExit(main())

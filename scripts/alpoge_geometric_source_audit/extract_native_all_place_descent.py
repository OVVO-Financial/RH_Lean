#!/usr/bin/env python3
"""Extract the actual all-place integral-map descent proof, without geometric imports.

This script does not run Lean.  It copies the exact supplying import closure,
changes only project namespaces/imports, restores original project options,
and applies the explicitly listed source-level pruning substitutions below.
Hosted Lean compilation is the required acceptance gate.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess


PREFIX = "RHLean.Geometry.AlpogeAllPlace."
PIN = "7cbf7a0c32fca1badf05931879a37c3f8a2b03b4"
ROOTS = [
    "Formalism.MeanHeightDescent.AverageDegreeBounds.DescentSlope",
    "Formalism.MeanHeightDescent.AverageDegreeBounds.SpanMuMin",
    "Formalism.BranchSandwichDivisors.BranchIsometryProofs.OrthSum",
    "Formalism.HarderNarasimhan.HarderNarasimhanProofs.QuotRealize",
]
GRAM = "Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart"
POINTS = "Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.PDescentCutA"
DESCENT = "Development.AbelianVarietyTheory.Proofs.DivisorProofs.HtMapLeOfPoints"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    checkout = args.source.resolve()
    source = checkout / "src"
    if subprocess.check_output(["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True).strip() != PIN:
        raise SystemExit("Wrong upstream commit")
    target = args.output.resolve()
    target.mkdir(parents=True, exist_ok=True)
    files = {}
    selected = {}
    pending = list(ROOTS)
    while pending:
        mod = pending.pop()
        if mod in selected:
            continue
        path = source / (mod.replace(".", "/") + ".lean")
        if not path.exists():
            if mod == "Mathlib" or mod.startswith("Mathlib."):
                continue
            raise SystemExit("Unexpected external dependency: " + mod)
        text = path.read_text()
        selected[mod] = text
        pending.extend(re.findall(r"(?m)^import\s+(\S+)", text))

    original_count = len(selected)
    original_lines = sum(len(text.splitlines()) for text in selected.values())

    # Keep precisely the general Gram/slope definitions and their coordinate-
    # independence proof.  Later theta, section, and measure data are unused.
    gram_text = (source / (GRAM.replace(".", "/") + ".lean")).read_text()
    gram_body = gram_text[gram_text.index("noncomputable section"):]
    gram_body = gram_body[:gram_body.index("theorem slopeMax_slopeMin_eq")]
    selected[GRAM] = (
        "import Formalism.HarderNarasimhan.ShiftInvariance\n"
        "import Formalism.HarderNarasimhan.HarderNarasimhanProofs.QuotRealize\n\n" +
        gram_body + "\nend Indep\nend Gram\nend GlobalTheory.AllWt\n"
    )

    # The dense complex-place operator-norm argument needs just the definitions.
    # The original broad imports are unrelated to the proof body.
    point_text = (source / (POINTS.replace(".", "/") + ".lean")).read_text()
    selected[POINTS] = "import Mathlib\nimport Formalism.HarderNarasimhan.StatementPl\n\n" + \
        point_text[point_text.index("open Module NumberField"):]

    # Keep the actual jointly injective integral family theorem.  Replace only
    # reexport aliases by their proven suppliers, and avoid a 300-line import
    # for the elementary positive-rank step already supplied by MapScale.
    descent_text = (source / (DESCENT.replace(".", "/") + ".lean")).read_text()
    descent_body = descent_text[descent_text.index("open Module NumberField"):]
    descent_body = descent_body.replace("Formalism.ExtensionFiltration.spanMuMin",
                                        "Formalism.ExtensionFiltration.span_min_slope")
    descent_body = descent_body.replace("Formalism.ExtensionFiltration.descentSlope",
                                        "Formalism.ExtensionFiltration.descent_slope")
    descent_body = descent_body.replace(
        "Formalism.BranchingDeterminantCap.PrismTransfer.blockDiag_det (X' v) (hX' v)",
        "Matrix.isUnit_det_of_right_inverse (Formalism.BranchingDeterminantCap.OrthogonalSumAlt.blockInv X' hX' n v)")
    old_positive = "Nat.pos_of_ne_zero (Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.rkK_ne_zero b A hA0)"
    if old_positive not in descent_body:
        raise SystemExit("Upstream positive-rank proof changed")
    descent_body = descent_body.replace(old_positive,
        "Formalism.BranchingDeterminantCap.ms_rkK_pos b hA0")
    selected[DESCENT] = "\n".join("import " + mod for mod in
        [GRAM, ROOTS[0], ROOTS[1], ROOTS[2], POINTS]) + "\n\n" + descent_body

    # Explicitly rename EVERY upstream project declaration root, including the
    # two tiny Bl lemmas, so native declarations cannot shadow upstream names.
    rename = re.compile(r"\b(Formalism|GlobalTheory|Bl|Lemmata|Development)\b")
    options = (
        "set_option autoImplicit false\n"
        "set_option relaxedAutoImplicit false\n"
        "set_option maxSynthPendingDepth 3\n"
        "set_option maxHeartbeats 4000000\n"
    )
    for mod, text in sorted(selected.items()):
        old_path = "src/" + mod.replace(".", "/") + ".lean"
        original = (checkout / old_path).read_bytes()
        rewritten = rename.sub(lambda match: PREFIX + match.group(1), text)
        # Mathlib 4.34 separates the real nonnegative-product inequality from
        # the ordered-monoid inequality.  Preserve both original hypotheses.
        if mod == "Formalism.MeanHeightDescent.AverageDegreeBounds.SpanMuMin":
            rewritten = rewritten.replace("Finset.prod_le_prod (fun v _ => by positivity)",
                                            "Finset.prod_le_prod₀ (fun v _ => by positivity)")
        # Native options are file scoped; upstream supplied these in lakefile.
        lines = rewritten.splitlines(keepends=True)
        split = max(index for index, line in enumerate(lines) if line.startswith("import ")) + 1
        rewritten = "".join(lines[:split]) + "\n" + options + "".join(lines[split:])
        path = target / (PREFIX + mod).replace(".", "/")
        path = path.with_suffix(".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(rewritten)
        files[str(path.relative_to(target))] = {
            "upstream_path": old_path,
            "upstream_git_blob": hashlib.sha1(b"blob " + str(len(original)).encode() + b"\0" + original).hexdigest(),
            "upstream_sha256": hashlib.sha256(original).hexdigest(),
            "native_sha256": hashlib.sha256(rewritten.encode()).hexdigest(),
            "native_lines": len(rewritten.splitlines()),
            "kind": ("source_body_pruning" if mod in [GRAM, POINTS, DESCENT] else
                     "namespace_options_and_product_api" if mod == "Formalism.MeanHeightDescent.AverageDegreeBounds.SpanMuMin" else
                     "namespace_and_options_only"),
        }

    # Stable native entry point, with the complete original statement visible.
    signature = descent_body.split("theorem descent : ", 1)[1].split(" := by", 1)[0]
    signature = rename.sub(lambda match: PREFIX + match.group(1), signature)
    entry = "import " + PREFIX + DESCENT + "\n\n" + options + "\n"
    entry += "/-! Actual all-place integral-family slope descent, ported from the pinned source.\n"
    entry += "The joint norm and near rank saturation hypotheses retain their original constants.\n"
    entry += "Every infinite place and the original O_K submodules remain in the statement. -/\n\n"
    entry += "open NumberField " + PREFIX + "GlobalTheory.AllWt\n\nnamespace RHLean.Geometry\n\n"
    entry += "theorem nativeAllPlaceDescent : " + signature + " :=\n  " + PREFIX + "GlobalTheory.DescentFamily.descent\n\nend RHLean.Geometry\n"
    entry_path = target / "RHLean/Geometry/NativeAllPlaceDescent.lean"
    entry_path.parent.mkdir(parents=True, exist_ok=True)
    entry_path.write_text(entry)
    files[str(entry_path.relative_to(target))] = {"kind": "explicit_native_alias",
        "native_sha256": hashlib.sha256(entry.encode()).hexdigest(), "native_lines": len(entry.splitlines())}

    manifest = {
        "upstream_commit": PIN,
        "status": "source_extracted_hosted_compile_pending",
        "module_prefix": PREFIX,
        "unmodified_body_supplier_modules": original_count,
        "unmodified_body_supplier_lines": original_lines,
        "total_native_modules": len(files),
        "total_native_lines": sum(value["native_lines"] for value in files.values()),
        "entry_module": "RHLean.Geometry.NativeAllPlaceDescent",
        "entry_theorem": "RHLean.Geometry.nativeAllPlaceDescent",
        "axiom_targets": ["RHLean.Geometry.nativeAllPlaceDescent",
            PREFIX + "GlobalTheory.DescentFamily.descent",
            PREFIX + "Formalism.ExtensionFiltration.descent_slope",
            PREFIX + "Formalism.ExtensionFiltration.span_min_slope",
            PREFIX + "Formalism.BranchingDeterminantCap.power_slope_mu"],
        "pruning": ["IsProbabilityMeasureMuPart: retain Gram section through slope_sq_eq",
            "PDescentCutA: retain proofs; import only Mathlib and StatementPl; no linter suppression",
            "HtMapLeOfPoints: replace reexport wrappers by descent_slope/span_min_slope",
            "HtMapLeOfPoints: block matrix determinant from actual blockInv",
            "HtMapLeOfPoints: positive rank from already imported ms_rkK_pos"],
        "native_api_updates": ["SpanMuMin: Finset.prod_le_prod to prod_le_prod₀, retaining both nonnegativity/comparison arguments"],
        "files": files,
    }
    (target / "native_all_place_descent_manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps({key: value for key, value in manifest.items() if key != "files"}, indent=2))


if __name__ == "__main__":
    main()

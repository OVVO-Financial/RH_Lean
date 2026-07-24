from pathlib import Path

seq_path = Path("FORMALIZATION_SEQUENCE.md")
chk_path = Path("FORMALIZATION_CHECKLIST.md")
seq = seq_path.read_text()
chk = chk_path.read_text()


def replace_once(text: str, old: str, new: str, label: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f"{label}: expected one match, found {count}")
    return text.replace(old, new, 1)


seq = replace_once(
    seq,
    "The root library imports forty-seven theorem modules.",
    "The root library imports forty-eight theorem modules.",
    "module count",
)

inventory_anchor = """47. `RHLean.Proof.CompleteHighFamilyDecomposition`
    - defines retained new-prime bases, their injective tripled-child image, and every remaining high channel as an explicit unpaired channel;
    - proves the exact disjoint support decomposition `high = bases ⊔ children ⊔ unpaired`;
    - proves the corresponding generic finite-sum decomposition without collapsing ordered orientations;
    - defines complete all-mode transport contributions for channels, retained raw pairs, retained signed defects, child multiplicity correction, and unpaired channels;
    - proves that the raw once-per-channel retained pair sum is the weighted signed-defect sum minus one child copy;
    - proves the complete high-family identity with every retained defect, child correction, and unmatched contribution visible before any norm or Gram estimate.
"""
inventory_new = inventory_anchor + """
48. `RHLean.Proof.ConcreteHighFamilyJointGram`
    - proves every concrete transport packet vanishes away from its assigned source shell;
    - proves the shell/channel Farey-mode sum is exactly the complete channel contribution at that source shell and zero elsewhere;
    - proves the concrete transport `actualResidual` is exactly the once-per-channel, all-mode complete high-family contribution;
    - instantiates the full shell/cofactor/mode/row signed joint Gram identity for the concrete family;
    - proves the PR #56 defect-minus-child-correction-plus-unpaired recombination has that same exact joint Gram energy;
    - exposes the remaining pointwise and uniform analytic control propositions without asserting that the estimate is proved.
"""
seq = replace_once(seq, inventory_anchor, inventory_new, "inventory")

history_anchor = """PR #56 completes the finite high-family bookkeeping. Retained new-prime bases and their injective tripled children form a disjoint paired support, every remaining high channel is retained explicitly, and the raw once-per-channel pair contribution is identified as the weighted PR #55 defect minus one child copy. Thus the full family is decomposed exactly without pretending that the factor-of-two transport identity is an ordinary set-pair cancellation.
"""
history_new = history_anchor + """
PR #57 supplies the missing concrete Gram realization. The transport-data `actualResidual` is proved equal to the complete PR #56 family, so the existing joint Gram theorem now applies to the exact concrete shell/channel/Farey-mode/residual-row index. This corrects the dependency order: the concrete identity must precede, and is not itself, the still-open uniform analytic estimate.
"""
seq = replace_once(seq, history_anchor, history_new, "history")

checkpoint = "The concrete square-prefix Mertens value now has an exact normalized ordered-channel realization, an exact low/high signal partition at `|Y| ≤ Λ n`, finite reduced Farey modes with canonical modulus `2r`, concrete source-entry residual data, contiguous transport data, and a complete exact tripling identity whose defect is the finite boundary prefix plus the explicit phase mismatch on the common window. The complete finite high support is now split exactly into retained new-prime bases, their injective tripled children, and explicit unpaired channels; at contribution level, the full all-mode family is the retained signed defects minus the one-copy child multiplicity correction plus the unpaired contribution."
seq = replace_once(
    seq,
    checkpoint,
    checkpoint + " The concrete transport residual is now proved equal to that complete family, and its energy is exactly the single four-coordinate signed joint Gram expression retaining every cross-shell, cross-channel, cross-mode, and cross-row interaction.",
    "checkpoint",
)

phase_old = """- [x] **30. Complete tripling-pair/unpaired-channel decomposition and exact multiplicity correction** — PR #56.
- [ ] **31. Uniform full-family signed Gram estimate with all cross interactions retained**.
"""
phase_new = """- [x] **30. Complete tripling-pair/unpaired-channel decomposition and exact multiplicity correction** — PR #56.
- [x] **31. Concrete complete-family joint Gram realization** — PR #57.
- [ ] **32. Uniform full-family signed Gram estimate with all cross interactions retained**.
"""
seq = replace_once(seq, phase_old, phase_new, "phase IX")

seq = replace_once(
    seq,
    "complete bases/children/unpaired decomposition + multiplicity correction\n        ↓\nfull-family signed Gram estimate",
    "complete bases/children/unpaired decomposition + multiplicity correction\n        ↓\nconcrete complete-family joint Gram realization\n        ↓\nfull-family signed Gram estimate",
    "dependency spine",
)
seq = replace_once(
    seq,
    "retained defect - child correction + unpaired recombination\n        ↓\nfull signed shell/cofactor/mode/row Gram estimate",
    "retained defect - child correction + unpaired recombination\n        ↓\nconcrete full signed shell/cofactor/mode/row Gram identity\n        ↓\nuniform full-family signed Gram estimate",
    "analytic spine",
)

ledger = "- [x] **#56** — Decomposed the complete high support into retained new-prime bases, injective tripled children, and explicit unpaired channels; proved the raw-family multiplicity correction and complete all-mode contribution identity.\n"
chk = replace_once(
    chk,
    ledger,
    ledger + "- [x] **#57** — Proved the concrete transport residual equals the complete high family and instantiated its exact shell/cofactor/mode/row signed joint Gram identity; kept the uniform analytic estimate explicit and open.\n",
    "ledger",
)
chk = replace_once(chk, phase_old, phase_new, "checklist phase IX")

checkpoint_anchor = "The exact normalized channel arithmetic, high/low partition, finite Farey support, source-entry realization, contiguous transport windows, one-pair all-mode signed defect, and complete finite high-family decomposition are now compiled. The all-mode norm is taken only after signed recombination, and the weighted `base + 2 * child` law remains distinct from the raw once-per-channel family sum.\n"
checkpoint_block = """Principal definitions in `RHLean.Proof.ConcreteHighFamilyJointGram`:

- `squarePrefixHighFullFamilyJointGramEnergy`;
- `SquarePrefixHighFullFamilyJointGramEstimateAt`;
- `SquarePrefixHighFullFamilyJointGramBoundedBy`.

Principal theorems added by PR #57:

- `actualResidualPacket_squarePrefixHighTransportData_offShell`;
- `squarePrefixHighTransportModeSum_eq`;
- `actualResidual_squarePrefixHighTransportData_eq_familyContribution`;
- `squarePrefixHighTransportFamily_energy_eq_jointGram`;
- `squarePrefixHighFullDecomposition_energy_eq_jointGram`;
- `squarePrefixHighTransportFamily_energy_le_of_jointGramEstimate`;
- `squarePrefixHighTransportFamily_energy_le_of_uniform_jointGramControl`.

The exact normalized channel arithmetic, high/low partition, finite Farey support, source-entry realization, contiguous transport windows, one-pair all-mode signed defect, complete finite high-family decomposition, and concrete complete-family joint Gram realization are now compiled. The all-mode norm is taken only after signed recombination, the weighted `base + 2 * child` law remains distinct from the raw once-per-channel family sum, and the actual uniform Gram estimate remains an explicit open proposition.
"""
chk = replace_once(chk, checkpoint_anchor, checkpoint_block, "checkpoint details")

seq_path.write_text(seq)
chk_path.write_text(chk)

Path(".github/workflows/lean.yml").write_text(
    """name: Lean verification

on:
  pull_request:
  push:
    branches: [main]
  workflow_dispatch:

permissions:
  contents: read

concurrency:
  group: lean-${{ github.workflow }}-${{ github.ref }}
  cancel-in-progress: true

jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - name: Check out repository
        uses: actions/checkout@v4

      - name: Audit unfinished proofs and axioms
        run: bash scripts/audit_assumptions.sh

      - name: Build Lean project
        uses: leanprover/lean-action@v1
        with:
          use-mathlib-cache: true
          build: true
          build-args: \"RHLean --wfail\"
          test: false
          lint: false
"""
)

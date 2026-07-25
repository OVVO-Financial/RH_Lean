from pathlib import Path

seq_path = Path("FORMALIZATION_SEQUENCE.md")
chk_path = Path("FORMALIZATION_CHECKLIST.md")
seq = seq_path.read_text()
chk = chk_path.read_text()

seq = seq.replace(
    "The root library imports forty-nine theorem modules.",
    "The root library imports fifty-two theorem modules.",
)

anchor = """49. `RHLean.Proof.CanonicalHighSectorBridge`
    - defines the unique largest-prime-factor canonical point `q_m=P⁺(m)`, `c_m=m/q_m` and signed doubled height `q_m^2-c_m^2`;
    - defines the exact square blocks, native canonical low/high increments, and cumulative square-prefix values;
    - proves exact blockwise and cumulative low/high recombination;
    - proves the complete canonical block prefix is exactly `squarePrefixMertens` at `X_n=(n+1)^2-1`;
    - packages the manuscript's elementary uniform low-increment estimate as the explicit typed input `CanonicalLowIncrementControl` and derives the required pointwise low-energy bound;
    - defines the native unresolved statement `CanonicalHighUniformLocalBoundedStatement Λ` at scale `H N^(2+ε)`;
    - proves the native canonical high criterion is equivalent to the total square-prefix local criterion and, from `ClassicalMertensRHCriterion`, to `RiemannHypothesisStatement`;
    - does not prove the low-block occupancy theorem, `(HS)`, or the classical Mertens↔RH theorem.
"""
addition = anchor + """
50. `RHLean.Proof.CanonicalHighSectorCovariance`
    - defines the finite-window sum, mean, coherent mean energy, and centered covariance energy;
    - proves the exact identity `local energy = coherent mean energy + centered covariance energy`;
    - proves the centered term vanishes at `H=1`, so one-point control is entirely coherent;
    - proves the canonical high-sector criterion is exactly the conjunction of coherent and centered control;
    - preserves both analytic estimates as explicit open propositions and derives the conditional RH bridge without introducing an operator realization.

51. `RHLean.Proof.SquareBlockSmoothTransportGram`
    - defines the exact canonical smooth contribution and sign-reversed large-prime transport contribution in each square block;
    - proves blockwise and cumulative `smooth - transport` recombination from the common origin;
    - proves the cumulative residual is exactly `squarePrefixMertens`;
    - defines both diagonal energies and the complete signed smooth/transport interaction before forming the joint Gram energy;
    - proves the joint Gram energy is exactly the cumulative residual local energy and hence the existing square-prefix local energy;
    - exposes `SquareBlockSmoothTransportGramBound` as an ordinary open premise equivalent to the existing local criterion and, conditionally, to RH.

52. `RHLean.Proof.SquareBlockIncrementEnergy`
    - defines the stronger global increment-energy premise at the corrected scale `K^(1+ε)`;
    - proves the cumulative residual is the finite sum of the exact smooth-minus-transport increments;
    - applies finite Cauchy–Schwarz to obtain the RH-scale cumulative pointwise estimate;
    - reuses the existing pointwise-to-uniform-local theorem to derive the repository's minimal cumulative criterion;
    - derives the smooth/transport Gram premise and the conditional RH implication;
    - does not prove the strong increment estimate or replace the weaker minimal cumulative criterion.
"""
assert anchor in seq
seq = seq.replace(anchor, addition, 1)

corr_anchor = """PR #60 corrects the identification of the minimal bridge. The Phase VIII/IX construction is an exact normalized all-ordered-pair/Farey transport family and remains a possible sufficient proof strategy, but it is not definitionally the paper's unique largest-prime-factor decomposition. The new native module defines one canonical point per source, proves exact recombination with `squarePrefixMertens`, and isolates `CanonicalHighUniformLocalBoundedStatement Λ` as the single analytic bridge statement. The manuscript's elementary low-increment estimate remains an explicit typed input until separately transcribed into Lean.
"""
corr_add = corr_anchor + """
PR #62 decomposes every finite local high-sector energy exactly into a coherent mean contribution and a centered covariance contribution. The `H=1` specialization proves that the centered term vanishes identically, so covariance control alone cannot discharge the pointwise burden. No source-level operator or analytic estimate is inferred from the algebraic decomposition.

PR #63 defines the exact canonical smooth-minus-transport square-block split and retains the complete signed interaction in the joint Gram energy. The cumulative residual is proved equal to `squarePrefixMertens`, so the new typed Gram premise is definitionally the existing cumulative local criterion rather than a separate diagonal estimate.

PR #64 corrects the proposed increment-energy exponent: a global second moment sufficient for RH must be `O(K^(1+ε))`, not `O(K^(2+ε))`. The new layer formalizes that stronger premise and proves by finite Cauchy–Schwarz that it implies the existing cumulative pointwise and uniform-local criteria, while leaving the strong arithmetic estimate explicit and unproved.
"""
assert corr_anchor in seq
seq = seq.replace(corr_anchor, corr_add, 1)

native_chain = """where the last equivalence is still supplied as the ordinary typed argument `ClassicalMertensRHCriterion`.
"""
chain_add = native_chain + """
The smooth/transport and increment-energy layers add the following compiled sufficient hierarchy:

```text
SquareBlockIncrementEnergyBoundedStatement
  → SquarePrefixCurrentPointwiseBoundedStatement
  → SquarePrefixUniformLocalBoundedStatement
  ↔ SquareBlockSmoothTransportGramBound
  ↔ MertensEnergyBoundedStatement
  ↔ RiemannHypothesisStatement,
```

where the first implication uses finite Cauchy–Schwarz at the corrected `K^(1+ε)` increment-energy scale and the last equivalence remains the ordinary typed classical criterion. The increment-energy premise is stronger than, and does not replace, the minimal cumulative local criterion.
"""
assert native_chain in seq
seq = seq.replace(native_chain, chain_add, 1)

seq = seq.replace(
    """- optionally connect the normalized Farey/transport family to the native canonical sequence and use its full signed Gram estimate as a route to `(HS)`.
""",
    """- optionally connect the normalized Farey/transport family to the native canonical sequence and use its full signed Gram estimate as a route to `(HS)`;
- optionally prove `SquareBlockIncrementEnergyBoundedStatement` as a stronger sufficient route, keeping its `K^(1+ε)` scale distinct from the minimal cumulative criterion.
""",
    1,
)

phase_old = """### Phase X — native canonical bridge

- [x] **33. Native largest-prime-factor low/high realization and exact conditional RH bridge** — PR #60.
- [ ] **34. Concrete canonical low-increment control with the manuscript nontrivial-source bound `⌊Λ⌋` and the isolated `m=1` endpoint handled explicitly**.
- [ ] **35. Native canonical uniform local high-sector estimate `(HS)`**.
"""
phase_new = """### Phase X — native canonical bridge and cumulative smooth/transport hierarchy

- [x] **33. Native largest-prime-factor low/high realization and exact conditional RH bridge** — PR #60.
- [x] **34. Canonical coherent-mean and centered-covariance decomposition** — PR #62.
- [x] **35. Exact square-block smooth/transport joint Gram realization** — PR #63.
- [ ] **36. Strong square-block increment-energy sufficient hierarchy** — PR #64.
- [ ] **37. Concrete canonical low-increment control with the manuscript nontrivial-source bound `⌊Λ⌋` and the isolated `m=1` endpoint handled explicitly**.
- [ ] **38. Native canonical uniform local high-sector estimate `(HS)`**.
"""
assert phase_old in seq
seq = seq.replace(phase_old, phase_new, 1)

ledger_anchor = "- [x] **#60** — Added the native largest-prime-factor canonical square-block decomposition, exact recombination with `squarePrefixMertens`, explicit low-increment control interface, and the conditional `(HS) ↔ RH` theorem.\n"
ledger_add = ledger_anchor + """- [x] **#62** — Proved the exact coherent-mean and centered-covariance decomposition of canonical high-sector local energy, including the `H=1` collapse and the conditional conjunction↔RH bridge.
- [x] **#63** — Added the exact square-block smooth-minus-transport decomposition, cumulative Mertens realization, complete signed joint Gram energy, and conditional criterion↔RH bridge.
- [ ] **#64** — Adds the corrected `K^(1+ε)` increment-energy premise and proves its finite-Cauchy–Schwarz hierarchy to the existing cumulative local criterion, Gram premise, and conditional RH statement.
"""
assert ledger_anchor in chk
chk = chk.replace(ledger_anchor, ledger_add, 1)

chk_phase_old = """### Phase X — native canonical bridge

- [x] **33. Native largest-prime-factor low/high realization and exact conditional RH bridge** — PR #60.
- [ ] **34. Concrete canonical low-increment control with the manuscript nontrivial-source bound `⌊Λ⌋` and the isolated `m=1` endpoint handled explicitly**.
- [ ] **35. Native canonical uniform local high-sector estimate `(HS)`**.
"""
chk_phase_new = """### Phase X — native canonical bridge and cumulative smooth/transport hierarchy

- [x] **33. Native largest-prime-factor low/high realization and exact conditional RH bridge** — PR #60.
- [x] **34. Canonical coherent-mean and centered-covariance decomposition** — PR #62.
- [x] **35. Exact square-block smooth/transport joint Gram realization** — PR #63.
- [ ] **36. Strong square-block increment-energy sufficient hierarchy** — PR #64.
- [ ] **37. Concrete canonical low-increment control with the manuscript nontrivial-source bound `⌊Λ⌋` and the isolated `m=1` endpoint handled explicitly**.
- [ ] **38. Native canonical uniform local high-sector estimate `(HS)`**.
"""
assert chk_phase_old in chk
chk = chk.replace(chk_phase_old, chk_phase_new, 1)

checkpoint_anchor = """The native largest-prime-factor canonical sequence is now compiled separately from the normalized ordered-pair/Farey family. Its exact block increments and cumulative low/high prefixes recombine to `squarePrefixMertens`, and `CanonicalHighUniformLocalBoundedStatement Λ` is proved equivalent to the total local criterion and, from the ordinary `ClassicalMertensRHCriterion` argument, to RH. No project axiom is introduced.
"""
checkpoint_insert = """Principal definitions in `RHLean.Proof.CanonicalHighSectorCovariance`:

- `localWindowSum`;
- `localWindowMean`;
- `localCoherentMeanEnergy`;
- `localCenteredCovarianceEnergy`;
- `SequenceUniformLocalBoundedStatement`;
- `CoherentMeanUniformLocalBoundedStatement`;
- `CenteredCovarianceUniformLocalBoundedStatement`;
- `CanonicalHighCoherentMeanUniformLocalBoundedStatement`;
- `CanonicalHighCenteredCovarianceUniformLocalBoundedStatement`.

Principal theorems added by PR #62:

- `localSequenceEnergy_eq_coherentMean_add_centeredCovariance`;
- `localCenteredCovarianceEnergy_one`;
- `localCoherentMeanEnergy_one`;
- `sequenceUniformLocalBounded_iff_coherentMean_and_centeredCovariance`;
- `canonicalHighUniformLocalBounded_iff_coherentMean_and_centeredCovariance`;
- `canonicalHighCoherentMean_and_centeredCovariance_iff_riemannHypothesis`.

Principal definitions in `RHLean.Proof.SquareBlockSmoothTransportGram`:

- `squareBlockSmoothIncrement`;
- `squareBlockTransportIncrement`;
- `squareBlockSmoothPrefix`;
- `squareBlockTransportPrefix`;
- `squareBlockSmoothTransportResidual`;
- `squareBlockLocalSmoothEnergy`;
- `squareBlockLocalTransportEnergy`;
- `squareBlockLocalSmoothTransportInteraction`;
- `squareBlockSmoothTransportJointEnergy`;
- `SquareBlockSmoothTransportGramBound`.

Principal theorems added by PR #63:

- `canonicalTotalIncrement_eq_smooth_sub_transport`;
- `canonicalTotalPrefix_eq_smooth_sub_transport`;
- `squareBlockSmoothTransportResidual_eq_squarePrefixMertens`;
- `squareBlockSmoothTransportJointEnergy_eq_localResidualEnergy`;
- `squareBlockSmoothTransportJointEnergy_eq_squarePrefixLocalEnergy`;
- `squareBlockSmoothTransportJointEnergy_eq_coherentMean_add_centeredCovariance`;
- `squareBlockSmoothTransportGramBound_iff_squarePrefixUniformLocalBounded`;
- `squareBlockSmoothTransportGramBound_iff_riemannHypothesis`.

Principal definition in `RHLean.Proof.SquareBlockIncrementEnergy`:

- `SquareBlockIncrementEnergyBoundedStatement`.

Principal theorems added by PR #64:

- `squareBlockSmoothTransportResidual_eq_sum_increment`;
- `norm_squareBlockSmoothTransportResidual_sq_le_of_incrementEnergy`;
- `squarePrefixCurrentPointwiseBounded_of_incrementEnergy`;
- `squarePrefixUniformLocalBounded_of_incrementEnergy`;
- `squareBlockSmoothTransportGramBound_of_incrementEnergy`;
- `riemannHypothesis_of_squareBlockIncrementEnergy`.

""" + checkpoint_anchor
assert checkpoint_anchor in chk
chk = chk.replace(checkpoint_anchor, checkpoint_insert, 1)

chk = chk.replace(
    """- optionally prove an exact realization from the normalized Farey/transport family to the native canonical high sequence, then establish its full signed Gram estimate as a sufficient route to `(HS)`.
""",
    """- optionally prove an exact realization from the normalized Farey/transport family to the native canonical high sequence, then establish its full signed Gram estimate as a sufficient route to `(HS)`;
- optionally prove `SquareBlockIncrementEnergyBoundedStatement` at the corrected `K^(1+ε)` scale as a stronger sufficient route to the existing cumulative criterion.
""",
    1,
)

seq_path.write_text(seq)
chk_path.write_text(chk)

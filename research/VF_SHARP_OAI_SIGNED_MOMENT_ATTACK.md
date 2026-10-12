# Analytic attack A — genuine sharp VF owner-two signed moment

**Stack:** based on PR #919 (\`vf-seven-eighths-analytic-zero-free-bridge\`).
This branch is a sibling of the arithmetic variation attack; it must not
be merged to \`main\` until #919's coefficient-map prerequisites land.

## What is proved on this branch

The new Lean module
\`research/VF_SHARP_OAI_SIGNED_MOMENT_ATTACK.lean\` takes the **original**
native AMP p=2 parent and returned-child site weights, including the
different \`n\` and \`2*n\` cutoffs, and constructs the literal centered
physical norm row

\[
Z_R=\sum_{m\le X_R}a^{(6)}(m)
  \mathcal K_{X_R}[w_R^{\mathrm{parent}}-
                   w_R^{\mathrm{returned}}](m),
\quad X_R=R^2-1.
\]

The unconditional coefficient map in #919 and linearity give

\[
Z_R=H_R-J_R
\]

with both \(H_R,J_R\) the **actual** physical native amplitudes. Then
exact complex polarization gives

\[
\boxed{2G_R=|Z_R|^2-|H_R|^2-|J_R|^2\le |Z_R|^2.}
\]

This is the correctly **one-sided** analytic inlet. A sufficiently small
uniform bound on the actual centered row's norm square would upper-bound
the signed owner-two Gram without assuming its sign.

**Nothing here proves that \(Z_R\) is a single admissible OAI
\`normalized_input_difference\` row or that its norm square has the
required bound.** The rank-three witness in #919 already rules out one
unmasked occurrencewise rectangle.

## Numerical representation stress test

\`scripts/vf_sharp_oai_row_rank_probe.py\` constructs the exact rational
native AMP weight \(w_R(n)\) and centered difference \(w_R(n)-w_R(2n)\)
on odd squarefree semiprime occurrence grids. Gaussian elimination is
exact rational arithmetic, with no tolerance.

| R | grid | parent rank | centered rank | min unmasked centered rectangles |
|---:|---:|---:|---:|---:|
| 317 | 10 × 10 | 9 | 9 | 5 |
| 548 | 16 × 16 | 10 | 13 | 7 |
| 1027 | 16 × 16 | 13 | 14 | 7 |
| 3000 | 16 × 16 | 12 | 15 | 8 |

A sum of \(q\) unmasked separable differences
\(\sum_{j=1}^q(f_j(a)g_j(b)-u_j(a)v_j(b))\) has rank at most \(2q\).
The table therefore gives **finite lower bounds only for this restricted
occurrencewise model**. It does **not** rule out OpenAI's genuine coupled
ideal masks, selected-prime tuple multiplicities, or norm-fiber sums,
which can alter rank. Nor does it prove that required rank grows without
bound as \(R\to\infty\).

## Open analytic work, with exact acceptance conditions

1. **Actual ideal semantics.** Import/port OpenAI's
   \`normFiberCoeff_baseChange_eq_pairInverseCoeff\` and prove equality
   with #919's constructed \(a^{(6)}\), including inert norm four,
   ramified norm three, split prime-label multiplicities, and the
   zero-norm convention. OpenAI's Lean 4.34 toolchain is incompatible
   with this repository's Lean 4.24 without a port.
2. **Sharp row admissibility.** Prove a factorization-preserving
   representation of \(Z_R\) by actual OAI/ProofCouncil masked sources
   with all same-profile/prime-slot/product-normalization hypotheses.
   Alternatively, prove a **new signed moment estimate** for the
   physical moving reciprocal-weighted divisor comb itself. A single
   unmasked centered rectangle is excluded by #919.
3. **Uniformity.** Quantify the losses from the \(R\)-dependent
   half-integer sharp/smooth window and its seminorms. The existing
   exact window equality does not give uniform analytic constants.
4. **One-sided payment.** Prove \(|Z_R|^2\le B_R\) with \(B_R\) no larger
   than the actual first-bad owner-two budget. A generic large
   second-moment or a \(7/8\)-scale bound is insufficient for the
   \(R\log R\) endpoint objective.
5. **Historical weld.** Reassemble all other original VF Sector Six
   owners and mixed terms, once only. The native owner-two Gram is
   not the complete historical Sector Six payment.

**No new zero-free region is claimed.** The work attacks transfer of
analytic cancellation to the original VF signed Gram. The proof
obligation is quantitative, not a conditional restatement presented
as a closure.

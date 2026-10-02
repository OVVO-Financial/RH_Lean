# VF-mid Monte Carlo dependence note

The finite `NNS.meboot` experiment is recorded under `numerics/vf_mid_meboot/`.

Its purpose is theorem discovery, not certification. The direct proof target remains

\[
|\pi(R^2)-VF_{\rm mid}(R^2)|=O(R\log R).
\]

For the standardized block error

\[
z_R=\frac{P_R-V_R}{\sqrt{R w_R(1-w_R)}},
\qquad w_R=V_R/R,
\]

the observed data on `56 <= R < 3162` have lag-1 correlation `-0.138284` and lag-2 correlation `-0.093832`.

A 4611-path maximum-entropy bootstrap suite was then run:

1. 3582 paths targeting Pearson/Spearman correlation to the actual `z_R` over `rho = -0.95,...,0.95`;
2. 1029 serial-stress paths formed by rank-reordering the empirical marginal onto AR(1) templates through `phi=0.99`, then applying `nns_meboot` at target Spearman `0.95`.

The main finite findings are:

- actual `max_{R>=1000} |D_R|/(R log R) = 0.0197851`;
- maximum over the ordinary dependence sweep: `0.216552`;
- maximum over the serial-persistence stress suite: `0.477751`;
- every one of the 4611 paths remained below `1` on that finite diagnostic;
- actual proposed variance-inflation constant
  `max C_R^2 / ((log R)^3 B_R) = 0.00579161`;
- serial-stress 99th percentile for that constant: `0.849714`;
- serial-stress maximum: `1.078695`;
- 99.611% of serial-stress paths satisfy the diagnostic with `K <= 1`.

At latent `phi=0.99`, the realized median lag-1 correlation is `0.925596` and the maximum realized lag-1 correlation is `0.969942`, yet the median RH-normalized maximum is only `0.244605` and the finite maximum is `0.477751`.

## Consequence for the proof search

The numerics do **not** prove any asymptotic statement about primes. They do, however, rule out the numerical premise that the VF route requires near-independence or near-zero serial correlation.

The useful theorem-discovery message is weaker and more actionable:

> A deterministic proof need only exclude sufficiently extreme *persistent positive coherence*; it need not prove random-prime behavior.

That aligns with the existing exact arithmetic structure:

- prefix-wheel upper bounds on `P_R`;
- exact signed-seat identity `V_R-P_R`;
- chronological late-owner decomposition;
- cross-owner recursive-child injectivity;
- square-root phase control of spatial midpoint bias;
- fresh-prime sign-reversal transport above the square-root frontier.

A natural deterministic sufficient target remains

\[
C_R^2\le K(\log R)^3B_R,
\]

or an equivalent positive-Gram-overlap bound on the signed owner tree. The Monte Carlo suite suggests that such a theorem can tolerate far more positive dependence than independence heuristics would indicate.

See `numerics/vf_mid_meboot/README.md` for the exact setup, caveats, source version, and reproduction command.

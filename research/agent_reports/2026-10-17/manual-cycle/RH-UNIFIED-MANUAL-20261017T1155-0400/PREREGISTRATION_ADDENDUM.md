# Census pre-registration addendum — continuation of run RH-UNIFIED-MANUAL-20261017T1155-0400

Timestamp (America/New_York): 2026-10-17T17:21-04:00. Written **before** any Part A–D computation of this continuation was executed.

**Why there is an addendum.** The first execution of this run timed out after publishing the Phase 1 checkpoint, `PREREGISTRATION.md` (unchanged, sha256 `610704afc6fda454671403e0e99debacaebb0297331657e0d73b431600caf706` as recorded in the checkpoint) and draft PR #967. No Part A–C result from that execution was published, so none is reused. This continuation runs Parts A–C exactly as pre-registered, fixes one ambiguous operationalization (C-growth, below) before seeing data, and adds Part D for a new Wheel hypothesis formulated in this continuation.

## C-growth operationalization (ambiguity in Part C fixed before execution)

`PREREGISTRATION.md` says "max |S_q(R)| / (R/log R) grows by a factor >= 3 between 10^6 and 10^8". Fixed reading: with `w(R) = |S_q(R)| log R / R`, compare `W_end = max_{R in [5*10^7, 10^8]} w(R)` and `W_start = max_{R in [10^6, 2*10^6]} w(R)` (equal log-width windows, every integer R). Growth factor `W_end / W_start`. The decade-window ratio `max_[10^7,10^8] / max_[10^6,10^7)` is reported as a secondary statistic only. Correlation in Part C uses 20,000 log-uniform sample points of R in [10^6, 10^8]; the zero prediction uses the first 50 zeta zeros, no fitted parameter.

## Part D — bucket-level greatest-prime renormalization (Wheel hypothesis H-REN)

Root cutoff `y = floor(sqrt X)`. Split every quotient bucket by greatest prime: `B^sm_X(t)` = sum of `a6(m)` over `floor(X/m) = t` with `P+(m) <= y`; the rest have a unique prime `q > y`, necessarily split.

- **D1 (exact identity, H-REN):** for every `t >= 1`,
  `B_X(t) = B^sm_X(t) - 2 * sum_(1<=u<=y) c_X(u) * B_u(t)`, with `c_X(u) = pi_split(floor(X/u)) - pi_split(max(y, floor(X/(u+1))))` and `B_u(t) = 0` for `t > u`.
  Test set: every X in [12, 5000], X in {380, 10^4, 10^5, 10^6}, all t <= X. Any single integer failure refutes H-REN as stated and is reported with its witness.
- **D2 (relocation versus restriction):** prediction R1 (relocation): the two populations' separate low variations `V^sm_low(X) = sum_(t<=y)|B^sm_X(t)-B^sm_X(t+1)|` and `V^lp_low(X)` (same for `B - B^sm`) are each at least 10 * V_low(X) at X in {10^5, 10^6, 10^7}, i.e. the identity relocates signed mass rather than restricting it. Rival R0: one of them is comparable to V_low (ratio < 3), which would make it a candidate restriction. Report the ratios and their normalization by `X/log^2 X`.
- **D3 (finite face of H-L, exact):** `V_low(X) >= |C6(X) - C6(floor(X/2))| - |B_X(r+1)|` at every X of Part A's set (this inequality follows from telescoping; a failure would mean an implementation error).

Numerical agreement is evidence about finite arithmetic only, never proof.

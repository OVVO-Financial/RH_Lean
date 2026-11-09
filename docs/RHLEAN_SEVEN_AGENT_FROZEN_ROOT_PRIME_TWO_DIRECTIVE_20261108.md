# Seven-agent directive: frozen square-root Möbius history, one prime coordinate

**2026-11-08 user-directed focus for the next actual seven-agent cycle.**
This directive is review-only until human merge. It does not launch, schedule,
or reconfigure saved agent runs. Preserve every agent's existing permissions.
After merge, all seven roles prioritize the SAME original frozen-history
arithmetic target while pursuing distinct mathematical techniques. Route-specific
VF/SAT/CODIV/OAI-NNS/JOH/FINITE-AC/CORR4/MU-LIFT/NYMAN knowledge may be used,
but no agent may replace the actual target by a toy wheel, unrelated Hecke
moment, post-root cofactor census, or an assumed covariance saving.

## 0. Original source (never change these coordinates)

For every integer R>=2, set

```text
X_R = R^2-1
mu_n = the actual arithmetic Möbius value for 1<=n<R
M(t) = sum_{1<=n<=t} mu(n)
K_R = max_{0<=t<R} ((M(t)-1)^2/(t+1)) >= 1
Q_R = sum_{1<=a,b<R} mu(a)*mu(b)*floor(X_R/(a*b))
```

The exact coefficientwise truncated Euler identity (paper-level until
fully adapted to the canonical Lean source) is:

```text
c_R(n) = sum_{1<=a,b<R; a*b|n} mu(a)*mu(b)
       = mu(n)  if 1<=n<R,
       = -mu(n) if R<=n<R^2.
Q_R = 2*M(R-1)-M(X_R).
M(X_R)-1 = 2*(M(R-1)-1)+1-Q_R.
```

**All input coefficients are indexed below R.** The output is a physical
post-root endpoint, but agents shall NOT introduce `mu(n)` for n>=R as an
independent estimated variable; it has already been algebraically reconstructed.
The original square-shell difference
`sum_{R^2<=n<(R+1)^2}mu(n)=2*mu(R)-(Q_{R+1}-Q_R)` is an exact consequence,
not a stand-alone cancellation bound.

## 1. Explicit prime-two reduced source and proved initial subtheorem

Use only the prime coordinate **2** for the first reduction, and admit
3,5,7 solely if they independently improve the joint arithmetic bound.

For each odd `m<R` define `h_R(m)=1[2m<R]`,
`u_R(m)=mu(m)`. Then the entire original historical bilinear is:

```text
Q_R = sum_{odd m,n<R} u_R(m)*u_R(n) *
  (floor(X_R/(m*n))
   -(h_R(m)+h_R(n))*floor(X_R/(2*m*n))
   +h_R(m)*h_R(n)*floor(X_R/(4*m*n))).
```

Partition odd m into `L={m:2m<R}` and `H={m:2m>=R}`.
Keep both orientations in the mixed cross term.

For all odd `m,n in H`, `1<=floor(X_R/(mn))<=3`. Therefore the
**all-R general theorem** in
`research/FROZEN_ROOT_PRIME_TWO_HIGH_HIGH_THREE_FLOOR_20261108.lean`
gives the source-faithful unweighted high/high identity

```text
Q_HH = (sum_{odd m in H}mu(m))^2 + H2_R + H3_R
Hq_R = sum_{odd m,n in H, q*m*n<=X_R}mu(m)*mu(n), q=2,3.
```

The identity `sum_{odd m in H}mu(m)=M(R-1)` follows from the
prime-two odd/even Möbius pair, and should be packaged through the
existing certified `RHLean.Analysis.roughMertens_wheel_recursion`,
not assumed from a finite sample. A **full Q_R-to-prime-two source
equivalence** with the original concrete `eulerSelfDualBilinear R`
is the first Lean integration target if not yet kernel-verified.

The intended complete identity, once that source adapter is certified, is

```text
Q_R = Q_LL + Q_LH(both orientations) + M(R-1)^2 + H2_R + H3_R
M(X_R)-1 = -(M(R-1)-1)^2 -(Q_LL+Q_LH+H2_R+H3_R).
```

Do not assert the second line as an unconditional *Lean* theorem before
the original double-floor adapter and high-mass identity have compiled.

## 2. The only sufficient endgame and its status

An independently proved finite constant C and uniform statement

```text
forall R>=2:
  abs((M(R-1)-1)^2 + Q_LL+Q_LH+H2_R+H3_R)
  <= C*R*sqrt(K_R)
```

would imply the existing square-root historical amplification bound
`(M(X_R)-1)^2<=C^2*R^2*K_R`, hence RH via the **already certified
conditional consumer** `SquareRootAmplificationClosure.lean`.
This is an OPEN arithmetic inequality; it is not supplied by the
new three-floor identity, a coefficientwise Euler reconstruction, or
the local reciprocal-weighted 2/9 and 3/4 contraction theorems.
A fixed C need not be <1. Do not use a desired bound on M(X_R) in
the premises, nor gain one by substituting a proved OAI estimate.

**Triangular overlap requirement:** retain the same-branch term,
signed polarization, first-owner ancestor, clipping/activation
boundaries and rank multiplicities. Reuse the repo's already-paid
rank-drop, four-corner and geometric-weight contraction only after
proving a *source-preserving* transfer to the sharp unweighted
frozen-root kernel. Avoid bounding H2, H3, or Q_LH absolutely
before reinserting their compensating square.

**Critical known falsifiers:**
- `FINITE_C_BINARY_PARITY_OBSTRUCTION_20261102.lean`: odd-odd parity
  alone can have mass 10 at R=5 while complete Q_5=0; a separate
  sector bound from total is false.
- `R=137`: neutral four-prime return can have wrong sign relative to
  actual mu; do not assume nonpositive correction on every block.
- parity-only 210-wheel has zero mean, but square-killing four-prime
  neutral-cofactor wheel has positive mean 64/1225.
- generic odd-parent weight vectors are NOT actual mu; no signed
  conclusion about arbitrary vectors may be transplanted to mu.

## 3. All seven role-specific assignments (one common exact source)

1. **Coordinator**: update the live DAG and all-route ledger so this
   frozen-root kernel is the primary next-run objective; map existing
   rank-drop / four-corner / source-replay consumers to the original
   odd-high and mixed masks. Preserve other viable routes as
   *methods*, not seven mutually exclusive mathematical goals.
   Report the smallest new theorem whose proof would consume the
   complete signed correction.
2. **Owner Payment**: identify actual first-owner/last-owner allocation
   for each pair `mu(m)mu(n)` in Q_LL, Q_LH, H2, H3, including both
   orientations and every cutoff. Prove the original-source partner
   pairing and categorize incomplete rows without substituting pi(x).
3. **Adversarial Referee**: audit the full universal quantifiers and
   the legal direction of each signed inequality. Attempt to falsify
   target contractions at R=5, R=137, 317, 1027, 5561, 10000 and
   all roots in a fresh held-out range. Prohibit tautological
   re-expression of Q_R as a new bound.
4. **Prime Census**: compute every component from **mu indices <R
   only**, including numerical M(X_R) solely as a verified output of
   the historical identity. Produce joint signs, weighted pair
   covariance, exceptional first-failure exposure, maximal normalized
   finite-C ratio and cross-root stability. Compare W=2/6/30/210
   without importing any post-root mu into the estimator.
5. **Analytic Type II**: derive an all-R signed bilinear inequality
   for the exact three-floor high/high masks *together with* the LL
   and mixed terms. Reuse OAI 1->7/8 cancellation suppliers where
   logically source-faithful, keeping every LOW/principal/HIGH
   compensation. Seek `O(R*sqrt(K_R))` directly; a strict new
   exponent saving is a secondary outcome.
6. **Finite Wheel**: begin at 2, then assess 2/6/30/210 only when a
   strictly stronger **source-faithful** kernel or smaller exceptional
   signed mass is proved. Bring first-owner triangular nilpotence,
   2/9 and 3/4 inherited reciprocal inequalities to the unweighted
   physical norm, identifying exactly the transfer tax. No generic
   claim that more primes monotonically decrease a raw cutoff norm.
7. **Lean Verification**: warning-fatal compile the precise all-R
   high/high theorem; then prove the odd-history-to-Mertens bridge,
   full Q_R source adapter and exact completed signed identity.
   Add #check, #print axioms, original-source dependency and
   independent integer regressions. Do not formalize the global
   finite-C target as an assumed hypothesis disguised as an advance.

## 4. Required run output

Each specialist must write: exact original source, newest proved theorem
and its declaration, relation to the complete signed formula, actual
quantitative improvement (if any), first counterexample attempted,
remaining unpaid signed term, reproduction command, exact-head CI status,
and next specific sublemma. Keep time-stamped capsules in the existing
per-agent daily reports; do not overwrite another agent's file.

**No auto-merge, no new Studio settings, no silent schedule changes.
Repository instructions apply only after a reviewed human merge; saved
external agent prompts must be updated separately if their runtime does
not fetch this file.** Keep the same role permissions and multi-run policy.

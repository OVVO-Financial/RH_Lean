# Euler Abel smooth-drift audit: use the PRE-EXISTING global no-drift theorem

2026-10-27. This is the strictly original Möbius quotient-indexed
extension of #1039, stacked on #1038/#1037/#1036. No new RH bound, finite-C
hypothesis, or eta-saving is asserted. Exact-head Lean warning-fatal CI is
the certification gate.

## 1. Already established and correctly reused

research/MOBIUS_INVERSION_GLOBAL_CANCELLATION.lean contains the Lean theorem

    sum_mertensSummatory_floor_div_eq_one (N) (hN: 1<=N):
       sum_(q=1)^N M(floor(N/q)) = 1.

The theorem is merely the full summatory Mobius inversion
mu * 1 = delta, and predates the recent Euler quotient-bucket PRs.

The fixed-wheel periodic cancellation of all centered small-prime square
blocks in research/VF_MID_915_HISTORICAL_COMPRESSION_CRT_FIXED_OWNER_SAVING.md
is ALSO valid, but concerns a different physical wheel coordinate.
Neither result asserts the vanishing of an independently truncated
moving-owner or large-q Mertens sum. Distinguish the two mechanisms.

## 2. Our Abel smooth drift is a compensated, NOT independent, sum

Put N=R-1, L=R+1, X=N*L, Q in [1,N], and r_q=floor(N/q).

The smooth term of the proposed endpoint-interior Abel identity is

    - d * sum_(q=1)^(Q-1) M(r_(q+1)),  d=L/b.

By the EXISTING complete inversion theorem,

    sum_(q=1)^(Q-1) M(r_(q+1))
        = 1 - M(N) - sum_(q=Q+1)^N M(r_q).

This is the exact historical no-drift **head/tail compensation**.
No uniform bound of the head alone is implied by this identity.
The complementary tail must be carried into the singleton-carrier
recombination, not thrown out.

The tail has the exact original-Mobius Fubini form

    sum_(q=Q+1)^N M(floor(N/q))
      = sum_(a=1)^floor(N/(Q+1))
           mu(a) * (floor(N/a) - Q).

All a are strictly historical. For Q≈sqrt(N) there are O(sqrt(N))
such a, but individual weights can be as large as N-Q (the a=1 term).
THEREFORE neither small support nor global inversion independently
proves a square-root bound on the truncated tail.

Equivalently, using the #1039 Q-tail small-a partition,

    sum_(q=1)^(Q-1) M(r_(q+1))
      = 1 - M(N) + M(r_Q)
        - sum_(a=1)^r_Q mu(a)*(floor(N/a)-Q+1).

Both versions are exact. The second coordinates directly with the
certified high-q singleton-carrier collapse.

## 3. The endpoint identity must use indexed quotients, even on empty Q bucket

Define E_q(b)=floor(Y_b/r_q) - L*q/b and A_q=floor(Y_b/r_q),
Y_b=floor(X/b). The exact difference

    E_(q+1)-E_q = (A_(q+1)-A_q) - L/b

holds for every q with q and q+1 in range. At Q=Q0 minimal with
Q(Q+1)>=N the bucket I_Q can be empty, and then floor(N/r_Q)
need NOT equal Q. Do not replace E_Q with T_R(r_Q,b) in that case.

For q(q+1)<N, #1040 proves I_q nonempty, hence the original endpoint
kernel T_R(r_q,b) does equal E_q(b).

## 4. Exact Abel coupling: discontinuous cost removed, smooth drift retained

For genuine q buckets 1<=q<Q, let delta_q be the divisor-row punch,
M_q=M(r_q), V_q=sum_(j in (A_q,A_(q+1)]) M(floor(Y_b/j))
and W_q=A_(q+1)-A_q.

The combined endpoint plus strict-interior source is

    sum_(q=1)^(Q-1)[
      E_q*(M_q-M_(q+1)-delta_q)+V_q-W_q*M_(q+1)].

Finite Abel summation yields EXACTLY

    E_1*M(N)-E_Q*M(r_Q)
       +sum_(q=1)^(Q-1)[V_q-(L/b)*M_(q+1)-E_q*delta_q].

The floor window length W_q has canceled, but the deterministic
smooth drift -(L/b)*sum_(q<Q) M_(q+1) MUST NOT be claimed to have
vanished. The already-proved full-inversion identity substitutes

    -(L/b)*sum_(q<Q) M_(q+1)
     =(L/b)*[-1+M(N)+sum_(q>Q)M(r_q)].

This recouples the drift with the small-a high-q tail and the
endpoint boundary. The resulting expression is NOT yet a signed
power-saving bound; the final composite correlations still matter.

The q-window V_q values concatenate over (A_1,A_Q] with no internal
gap, and A_1=floor(L/b). The complete m-axis has its own Mobius
inversion identity at Y_b, but any truncated window must keep
its complementary terms.

## 5. Boundaries and no-go clauses

- The fixed-wheel theorem rules out unbounded *centered fixed-wheel*
  run drift, NOT general unbounded moving-owner drift.
- The complete quotient Mertens sum is identically 1, NOT each
  truncated head.
- The centered combined smooth+transport norm in
  RHLean/Analysis/SquareRootCombinedSignedResidual.lean is a separate
  exact object. That module prohibits taking separate norms without
  losing the large correlated cancellation.
- Counting O(sqrt N) quotient buckets or small a is not an independent
  fixed eta estimate.
- Never identify the #1040 terminal indexed E_Q with the original
  endpoint kernel T_R(r_Q,b) when I_Q is empty.

## 6. Lean provenance

- Already certified, reusable:
  research/MOBIUS_INVERSION_GLOBAL_CANCELLATION.lean
  ::sum_mertensSummatory_floor_div_eq_one
- Prior original source:
  research/EULER_ENDPOINT_CARRIER_SPARSITY_20261027.lean
- New exact identities:
  research/EULER_COUPLED_HEAD_NO_DRIFT_20261027.lean

No sorry/admit/new axiom. The stand-alone stronger historical
endpoint-indexed Abel identity is the next exact lemma; it must preserve
the Q-boundary and original divisor-row punch.

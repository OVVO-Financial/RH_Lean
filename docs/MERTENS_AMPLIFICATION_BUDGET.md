# Mertens amplification: subpower loss and subcritical budget dependence

**Research steering and paper-level conditional analysis, updated 2026-10-16 after merged #961 and the unified manual cycle.** Original subpower relaxation remains unchanged; new exact `K1/K2/K3` anatomy and fixed-g calibration are paper claims, not gain theorems. Subordinate to [AGENTS.md](../AGENTS.md), [the proof contract](../CURRENT_PROOF_CONTRACT.md) and the [live mechanism brief](FACTOR_DEPTH_RESEARCH_BRIEF.md).

**Status:** the recurrence implications below have elementary paper proofs. This change adds no Lean theorem. The independent arithmetic amplification inequality remains OPEN. A conditional recurrence theorem can be formalized honestly as a consumer, but must not be counted as having proved its genuine-Mobius premise.

## 1. The acceptance threshold is not constant gain

For integers B>=2 use the actual full-prefix budget

```text
E(B) = max_(1<=n<B) |M(n)| / sqrt(n),
M(n) = sum_(1<=m<=n) mu(m).
```

This is finite, nondecreasing in B, and at least 1 because M(1)=1. Fix an integer B_0>=2 and define B_j=B_0^(2^j), E_j=E(B_j).

A sufficient arithmetic estimate is

```text
E_(j+1) <= G_j * E_j^r,
1 <= r < 2 fixed, G_j >= 1,
g_j := log(G_j)/log(B_j) -> 0.
```

It need hold only for all sufficiently large j on this one square-growing chain. A bound for every sufficiently large integer B is stronger and also sufficient. Do not impose every-B uniformity as an unnecessary gate when one complete chain and full-prefix control already suffice. A finite initial segment is absorbed by beginning at a later genuine prefix; no small seed constant or unit square-root envelope is required.

The gain may exceed every fixed power of log B. Examples allowed by the asymptotic criterion are `C*(1+log B)^A`, `exp(sqrt(log B))`, and `exp(log B/log(log B))` for sufficiently large B, with fixed C>=1,A>=0 where applicable. A fixed power `B^delta`, delta>0, does not have vanishing normalized cost and does not by itself give the half-exponent conclusion.

## 2. Paper proof of exponent-budget contraction

Define u_j=log(E_j)/log(B_j)>=0. Taking logarithms of the displayed recurrence yields

```text
u_(j+1) <= (r/2)*u_j + g_j/2.
```

Put rho=r/2<1. If g_j<=eta for every j>=J, induction gives

```text
u_(J+m) <= rho^m*u_J + eta/(2-r)*(1-rho^m).
```

The initial term tends to zero. Since eta>0 can be arbitrarily small, limsup u_j<=0; nonnegativity gives u_j->0. The contraction is due to log(B_(j+1))=2*log(B_j), not critical-strip reflection. Here u_j describes an arithmetic prefix budget, not an individual zeta-zero coordinate.

**All-natural-cutoff passage:** for n>=B_0 choose J>=1 with B_(J-1)<=n<B_J. By the full-prefix definition,

```text
max(1,|M(n)|) <= sqrt(n)*E_J,
log(max(1,|M(n)|))/log(n) <= 1/2 + 2*u_J.
```

Thus every positive epsilon eventually gives a unit n^(1/2+epsilon) envelope; a finite initial maximum supplies its global constant. This proves the conditional conclusion `MertensGrowthAtMost (1/2)`. It controls every natural cutoff, not only the sparse endpoints.

The existing [Mertens identification](../research/MERTENS_CONVERSE_IDENTIFICATION.lean), especially `growthAtMost_half_iff_criticalZeros`, supplies the critical-line implication once this arithmetic input is proved. The upper estimate itself gives lambda_M<=1/2. Identifying its value as exactly 1/2 additionally uses nontrivial-zero existence/critical-line zeros, not a finite amplitude sample. The classical existence fact is described in [DLMF 25.10](https://dlmf.nist.gov/25.10); importing it into a formal chain requires the actual Lean theorem, not a citation substituted for a proof.

## 3. Explicit polylogarithmic special case

For r=1 and G_j=C*(1+log B_j)^A with fixed C>=1,A>=0, write L_0=log B_0. Since 1+2^j*L_0<=2^j*(1+L_0), iteration gives

```text
E_J <= E_0 * [C*(1+L_0)^A]^J * 2^(A*J*(J-1)/2).
```

Hence log(E_J)=O(J^2), not E_J=O(J^2). Full-prefix interpolation yields

```text
|M(n)| <= sqrt(n)*exp(O((log(log n))^2)).
```

The logarithmic square is o(log n), so this is sufficient. For a fixed 1<r<2 with the same polylogarithmic forcing, the logarithmic recurrence instead gives log(E_J)=O(r^J), and hence the sufficient envelope

```text
|M(n)| <= sqrt(n)*exp(O((log n)^(log(r)/log(2)))).
```

The latter exponent of log n is strictly below one. Do not carry the r=1 rate O((log log n)^2) over to superlinear dependence without redoing the accumulation.

## 4. The actual-gain formulation is target-equivalent

For r=1 the actual ratio `G_j=E_(j+1)/E_j` is at least 1. Its subpower property is equivalent to critical Mertens growth, not an independently available estimate.

The forward direction is Section 2. Conversely, critical Mertens growth implies that for every epsilon>0 there is C_epsilon>=1 with E(B_j^2)<=C_epsilon*B_j^(2*epsilon). Since E_j>=1,

```text
1 <= G_j <= C_epsilon*B_j^(2*epsilon).
```

Divide logarithms by log B_j, take limsup and let epsilon decrease to zero. For any fixed 1<=r<2, the same equivalence holds for the minimal clipped gain

```text
G_(j,r)^min = max(1, E_(j+1)/E_j^r).
```

Therefore a mechanism card must name the new arithmetic restriction proving a suitable majorant, not merely define the actual gain, assume it is subpower, and call the premise a smaller solved lemma. Polylogarithmic gain is a stronger sufficient hypothesis, not the only acceptable one. This logical audit does not forbid seeking a proof through this formulation.

## 5. Exact signed inequality to attack

For positive integer N define the genuine floor-kernel form

```text
Q_N(X) = sum_(1<=i,j<=N) mu(i)*mu(j)*floor(X/(i*j)).
```

At integer cutoffs N<=X<(N+1)^2 the exact short-Mobius identity is

```text
M(X) = 2*M(N) - Q_N(X).
```

It follows by summing the genuine truncated Newton convolution: its coefficients agree with mu below (N+1)^2, and the two linear truncated sums each equal M(N) once X>=N. This classical identity family is discussed by [Huxley and Watt, arXiv:1807.05890](https://arxiv.org/abs/1807.05890). The native convolution-to-hyperbola reindexings are on main; do not invent an additional compiled theorem for a particular optimized double loop unless its actual declaration exists.

With N=B-1, the research target is an independently justified estimate

```text
|2*M(B-1)-Q_(B-1)(X)| <= G(B)*E(B)^r*sqrt(X)
for every integer B<=X<B^2,
```

on all sufficiently large members B of the chosen chain, with fixed 1<=r<2, G(B)>=1 and log G(B)/log B->0. The old prefix contributes E(B); since G(B)*E(B)^r>=E(B), this whole-new-interval estimate implies the full-prefix recurrence. An estimate only at X=B^2-1 does not imply it without a separately proved interpolation/covering bound.

Preserve both signed linear terms, the complete floor weights, original truncations, all overlap/cross-row terms and genuine mu constraints. Large finite cancellation factors or a large seed budget are not automatic disqualifiers; judge the final asymptotic loss and input-budget power. Conversely, a row decomposition or a finite normalized-gain plot does not prove that loss vanishes.

## 5A. Post-cycle exact signed anatomy and proposed corner: full scope required

**PAPER_PROOF / IDENTITY_ONLY (2026-10-16 Analytic claim 1):** with `N=B-1`, integer `B<=X<B^2`, `psi(t)={t}-1/2` and signed genuine `mu(i)mu(j)`,
```text
M(X)=2 M(N) - Q_N(X) = 2 M(N)+K1_N(X)-K2_N(X)+K3_N(X)
K1 = (1/2) sum_(i,j<=N; ij<=X) mu(i)mu(j)
K2 = X sum_(i,j<=N; ij<=X) mu(i)mu(j)/(ij)
K3 = sum_(i,j<=N; ij<=X) mu(i)mu(j) psi(X/(ij)).
```
Do not silently replace the truncated `ij<=X` ranges by all pairs or ignore the complementary `ij>X` pairs when using the alternative full-pair formula. The `K1-K2+K3` cancellation is exact bookkeeping, not an independently proved amplitude estimate.

**Finite-support synthetic control (PAPER_PROOF):** for any finitely supported `a`, the Newton-lift summatory count satisfies `sum_(n<=X)T(a)(n)=-X*(sum a(n)/n)^2+O_a(1)` for `X` beyond its support, hence bounded iff that *fixed-control* weighted sum vanishes. This does not give a uniform bound for growing genuine Mobius prefixes or independently prove `m_N=sum_(n<=N)mu(n)/n` is small enough. Preserve original signed rows and all overlap.

**Candidate Type II task:** define a real or integer `H>1` and the exact signed corner
```text
K3_corner(N,X,H) = sum_(i,j<=N; X/H<ij<=X)
                        mu(i)mu(j)*psi(X/(ij)).
```
A bound `|K3_corner| <= G(B) E(B)^r sqrt(X)`, with `r<2` and `G=B^o(1)`, is only **one potential ingredient**. The rest of `K3`, both `K1,K2`, `2M(N)`, `H` and its possible dependence on B/X, admissibility masks, hyperbola boundary and the whole interval `B<=X<B^2` must still be controlled before inferring the genuine MU-LIFT recurrence. A reflection `ij -> X/(ij)` does not generally map integer pairs to integer pairs; a claimed symmetry must give an exact map/weighted identity, multiplicities, Mobius signs and explicit error. A shorter sum with unchanged difficult signed size is not an improved bound.

**PAPER_PROOF / CONDITIONALLY STRONG CALIBRATION (2026-10-16 Analytic claim 3):** suppose along `B_(j+1)=B_j^2` we *independently prove*, for fixed `0<=r<2`, `g>=0` and C, an all-`X` interval estimate
```text
|M(X)| <= C B_j^g E(B_j)^r sqrt(X),  B_j<=X<B_j^2.
```
Then the paper recurrence gives `limsup log(E(B_j))/log B_j <= g/(2-r)`; with the direct interval factor, the all-integer exponent is at most `1/2+2g/(2-r)+epsilon` and the zero-free half-plane is `Re s>1/2+2g/(2-r)`. If the same uniform inequality is proved for **every** large B, the implication improves to `Re s>1/2+g/(2-r)`. Thus fixed `g<(2-r)/4` on the chain, or `g<(2-r)/2` for every B, would already imply a nontrivial zero-free strip of fixed width. This is a **conditional strength warning**, not a proved gain or a reason to reject correctly quantified subpower `g_j->0`. The original subpower acceptance criterion, `r<2`, full prefix and signed source fidelity remain in force.

**Notation protection:** `E(B)` in this document is the **Mertens summatory normalized envelope**. The October 16 Owner uses `E_prime(y)=sum_(p<=y)1/p-log(log y)-M_Meissel` for the prime-reciprocal error. These are completely different functions. Its band no-go cannot be applied directly to this `E(B)` or this `K3` carrier.

**Evidence:** [2026-10-16 Analytic report](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-10-16/20-analytic-type-ii.md), same-session [Referee self-audit](https://github.com/OVVO-Financial/RH_Lean/blob/agent-reports/research/agent_reports/2026-10-16/50-adversarial-referee.md). Independent re-review is still needed before treating the strongest analytic implications as separately accepted. **No new unconditional exponent or RH proof.**

## 6. Higher-order relaxation supplied by the #954 interface

The original source [MERTENS_HEATH_BROWN_SIGNED.lean](../research/MERTENS_HEATH_BROWN_SIGNED.lean), blob `bb028fc18b8228412dafa21f990eeb84dc376b95` at the reviewed main, proves `heathBrownLift_agrees_below_power` for every integral k: a genuine prefix below B reconstructs coefficients below B^k. It also proves the signed geometric form and exact defect power. [MERTENS_SIGNED_HYPERBOLA.lean](../research/MERTENS_SIGNED_HYPERBOLA.lean) supplies the complete signed convolution/hyperbola split. None of these identities is an amplification bound.

For a **fixed** integer k>=2, let B_j=B_0^(k^j). A independently proved whole-prefix estimate

```text
E_(j+1) <= G_j*E_j^r,
1<=r<k fixed, log(G_j)/log(B_j)->0
```

gives `u_(j+1)<=(r/k)*u_j+g_j/k`. The proof above works with rho=r/k and tail bound eta/(k-r). The all-cutoff interpolation factor becomes k. Thus quadratic historical-budget dependence r=2 is subcritical for a genuine cubic-scale estimate k=3.

**No free improvement:** one may not relabel a B-to-B^2 estimate as a B-to-B^3 estimate, or assume a kth-order lift has a budget power below k. Prove the full larger interval bound and account for all alternating families. Constants may depend on a fixed chosen k; selecting k=k(B) requires a new uniform analysis. Support extension alone proves no contraction.

## 7. Boundary and normalization regressions

- **Critical power:** the synthetic monotone budget E(B)=B^delta, delta>0, obeys E(B^k)=E(B)^k with gain 1 and keeps a positive excess exponent. The threshold r=k does not force contraction. This is a countermodel to the abstract implication, not a counterexample about actual Mertens values.
- **Vanishing gap:** even r_j<2 at every square lift is insufficient without more control. For the same synthetic budget take r_j=2-1/(j+2) and G_j=B_j^(delta/(j+2)). Then g_j->0 and every r_j<2, but u_j=delta forever. A fixed r<2, or a proved uniform gap from two, avoids this example. Other varying-gap criteria require their own proof.
- **Consistent powers:** if an energy argument ends with E_(j+1)^2<=H_j*E_j^p, convert first to G_j=sqrt(H_j) and r=p/2. The square-scale screen is p<4, not p<2. Squaring both sides is not itself a failure. Report the power in the final amplitude inequality.
- **Sparse artificial prefix:** #954's a(1)=1,a(2)=-1,a(n)=0 otherwise has bounded scalar prefix sums but a large lifted summatory output. It rejects arguments for arbitrary bounded-prefix inputs, not an estimate proved using genuine Mobius arithmetic. A positive claim must explain the arithmetic condition excluding this control.
- **Finite guard failure:** retain #951's unit-0.45 failure as finite evidence against automatic perpetual preservation; do not misread it as rejecting all admissible subpower-gain laws.

## 8. Required outputs by specialty

**Coordinator:** rank a candidate by (scale power k, final budget power r, normalized loss g, covered interval), not whether its gain is constant or polylogarithmic. Keep factor-depth and inverse mechanisms alive when independent; this broadens MU-LIFT, not monopolizes all roles.

**Analytic:** seek a genuine signed inequality of the form in Section 5 or its fixed-k analogue. Record exact loss, final r, uniformity and the independent arithmetic input. A useful partial bound is retained at its actual strength even if its g does not yet vanish.

**Owner / Wheel:** identify arithmetic sign, incidence or factor restrictions that improve the final budget dependence or normalized gain while preserving every term. Do not require termwise cancellation, and do not discard a large finite loss before assessing its asymptotic scale.

**Census:** for declared fixed r and chain, measure `log(max(1,E_(j+1)/E_j^r))/log B_j`, full-prefix maximizing locations and the predicted majorant. The exact maximum E(B)^2 is max M(n)^2/n, so integer cross-multiplication can certify which prefix point maximizes it. Logs remain diagnostics unless rigorously bounded. Distinguish prefix-derived predictions from future-data validation and all-cutoff certificates from sparse samples. No numerical trend certifies g_j->0.

**Referee:** check chain coverage, r<k with a uniform gap, constants, all-prefix interpolation, genuine arithmetic versus arbitrary-sequence controls, the actual-gain equivalence and every omitted signed term. Do not reject a provable gain solely for exceeding all fixed log powers.

**Lean:** a scoped generic contraction plus full-prefix consumer is a valid conditional formalization candidate after duplicate search and proof review. Keep its gain hypothesis explicit, and separately identify the unproved arithmetic theorem. Search existing `SquareRootAmplificationClosure` and Mertens modules first; reuse instead of duplicating. This Markdown update does not certify a new Lean result.

Every MU-LIFT report states: **k; r; G; g; interval/chain; fixed constants; accumulated loss; independent arithmetic input; exact evidence status.** Schedules, permissions, canonical VF, native NNS normalization and human-only merge remain unchanged.

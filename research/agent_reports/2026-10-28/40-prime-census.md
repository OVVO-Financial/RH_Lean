# RH_Lean agent daily report - 2026-10-28 / RH | Prime Census Laboratory

**Status:** COMPLETED
**Invocation:** scheduled run begun 2026-10-28T01:51:00-04:00
**Final authority refresh:** 2026-10-28T01:54:51-04:00
**Pinned RH_Lean main:** `904f056ea039e7938587a8254125b18eab45cfd0`
**New claim:** `20261028-census-1`
**Evidence:** `PAPER_PROOF` for the exact zero-kernel characterization; `FINITE_COMPUTATION` for the phase census; `REFUTED` for sign-definite or separately payable phase bands; `NO_FIXED_ETA_GAIN`; `NO_RH`.
**Registry disposition:** informs the post-#1035 Euler lane and proposed `MECH-EULER-CARRY-PHASE-INCIDENCE`; no registry edit is authorized or made.

## A. Main result

### Claim `20261028-census-1`: Wheel sparsity counts exact kernel zeros, while the genuine saving is cross-phase compensation

Put
```text
N=R-1, L=R+1, X=N*L,
q=floor(N/a), t=N mod a, rho=(L*q) mod b,
C=floor((a*rho+L*t)/(a*b)).
```
For `1<=a,b<=N`, the original rank-one kernel from draft #1036 is
```text
T_R(a,b)=floor(X/(a*b))-(L/b)*floor(N/a)=C-rho/b.       (1)
```
The two formulas were evaluated independently at every tested site.

Because `C` is a nonnegative integer and `0<=rho/b<1`,
```text
T_R(a,b)=0  iff  C=0 and rho=0.                         (2)
```
This is an exact paper proof from Euclidean division. Thus today's Wheel claim
`20261028-wheel-1` bounds the support of **exact zero entries** of the original
kernel. Its divisor-sparse simultaneous-zero locus is not a cancellation
estimate; its complement is a dense nonzero carrier.

On the zero-phase sector itself, `rho=0 iff b | Lq`, and
```text
T_R(a,b)=floor(L*(N mod a)/(a*b)).
```
Hence its complete genuine-Mobius contribution is exactly
```text
Z_R = sum_q sum_(a in I_q) mu(a)
        sum_(b<=N, b|Lq) mu(b) floor(L*(N mod a)/(a*b)).       (3)
```
The sparse subset from Wheel is the part of (3) with floor value zero, so it
contributes literally nothing. The remaining divisor-incidence terms can be
large and have no fixed sign.

## B. Preregistered question and competing hypotheses

**Mystery.** Does exact carry/phase sparsity isolate a small payable exceptional
set, or is the observed small residual created only after restoring interactions
between all phase classes?

**H1 (local phase payment).** The zero or near-zero modular phase classes have a
stable sign or are individually comparable to the complete residual.

**H2 (global phase compensation).** Individual phase classes are large and
sign-indefinite; only their complete signed recombination is small.

The discriminator fixed before scaling was the exact partition by
```text
d(rho,b)=min(rho,b-rho)/b:
zero, (0,1/16], (1/16,1/8], (1/8,1/4], (1/4,1/2].
```
For each band I retained every genuine squarefree occurrence and coefficient
`mu(a)mu(b)`, then required the five band totals to reconstruct the complete
rank-one residual exactly.

H1 predicted individually controlled or sign-stable phase totals. H2 predicted
large opposite-signed totals and a small recombined value. A mismatch with the
direct floor bilinear would have falsified the implementation.

## C. Exact carrier and conservation checks

The computation used the literal carrier `1<=a,b<=R-1`, genuine integer
Mobius coefficients, `X=R^2-1`, exact quotient buckets and endpoint
conventions. No owner deduplication, random prime model, floating floor, mask,
or omitted cross term was used.

For every tested root,
```text
sum_(a,b<=N) mu(a)mu(b) T_R(a,b)
 = Q_R - L*S_N,
Q_R=sum_(a,b<=N) mu(a)mu(b) floor(X/(a*b)),
S_N=sum_(b<=N) mu(b)/b.                                  (4)
```
Python used `fractions.Fraction` for (1), the direct floor formula, every
selected band, `S_N`, and (4). It also checked the pointwise equality between
the carry-phase and direct-floor kernels. A separate C++17 program used a
linear sieve, direct integer floors, and long-double accumulation; it agreed
with all displayed totals through at least 15 significant digits.

This independently reconstructs the source relation certified by draft #1036
blob `e482711a3f55c1f59fc771f108671477f51732f2`. The carry definitions were
read from draft #1037 blob
`4a25d5ea0edca51dd91e718cb209f9a8e18b048a`.

## D. Results and falsifiers

### 1. Smallest sign reversal in the zero-phase signed contribution

The scan over every integer `2<=R<=600` found:

```text
R=4:  zero-phase contribution = -2,
      complete residual = -11/6.

R=17: zero-phase contribution = +1,
      complete residual = 19553/5005 = 3.906693306693...
```

Therefore the natural universal claims “zero phase is nonpositive” and “zero
phase is nonnegative” are both `REFUTED`. The positive sign first occurs at
`R=17` in this exhaustive range, while the first negative sign occurs at
`R=4`.

### 2. Strongest observed cross-band cancellation through R=600

At `R=442`, `N=441`, the direct integer bilinear is `Q_R=-3`. Exact
rational arithmetic gives the complete rank-one residual
```text
Q_R-L*S_N = 1.808997105011723...
```
while the five signed phase totals are
```text
zero             -1894.000000000000
(0,1/16]           -57.088633305217
(1/16,1/8]        +393.353631974237
(1/8,1/4]         -946.916904592850
(1/4,1/2]        +2506.460903028843
                         ----------------
complete             +1.808997105012
```
Their signed-band `l1` total is `5797.820072901151`, which is
`3204.991349539121` times the complete residual magnitude. The zero-phase
term alone is `1046.988961316563` times the complete magnitude.

At `R=466`, the two nearest nonzero phase bands sum to
`488.395190336881`, while the complete residual is
`2.027811501479352`, a ratio of `240.848417113961`.

These are exact finite counterexamples to any proposed estimate that first
takes absolute values band by band with constants below the stated ratios.
They do not disprove the existence of a larger universal constant. They do
show that the numerically observed saving lives in cross-phase interaction,
not the sparse exact-zero locus.

### 3. Factor-preserving randomized reference

For an exploratory reference only, I kept the same squarefree support and
kernel but randomized all nonzero Mobius signs except `mu(1)=1`, using 128
deterministic trials.

```text
R=442: genuine residual 1.8090; randomized RMS 5222.80,
       randomized range [-11724.73, 24283.84].
R=466: genuine residual 2.0278; randomized RMS 5354.73,
       randomized range [-11796.55, 25995.10].
```

This supports investigation of a Mobius-specific global constraint destroyed
by sign randomization. It is not evidence of independence, a tail bound, or an
all-scale rate.

## E. Mechanism decision and proof impact

**H1 is refuted on the tested carrier. H2 survives.** Exact-zero incidence
sparsity is a valid structural restriction, but it identifies where the kernel
vanishes. The large zero-phase, near-phase, and far-phase signed masses reverse
sign and compensate only after full recombination.

This directly reinforces the source warning in draft #1041: after the coupled
q-Abel identity, individual phases must not be estimated independently. The
mathematically credible target is the complete four-term unpaid source
```text
U_R = sum_(b<=B) mu(b) [
        V_b + (L/b)T_Q - E_Q(b)M(r_Q)
        + sum_(a<=r_Q, a not|N) mu(a)T_R(a,b) ],
```
with terminal bucket, divisor puncture, small-a tail, and all cross terms
retained. The finite phase census supplies no fixed `eta` estimate for
`U_R`.

A useful inverse theorem candidate is:

> If the complete rank-one residual is small while one phase band is large,
> then another explicitly different phase band must carry an opposite-signed
> amount of comparable size.

The tautological triangle version is immediate; the open arithmetic task is to
identify a Mobius/divisor constraint forcing that compensation uniformly
without defining the exceptional condition by the residual itself.

## F. Reproducibility

Local probe hashes:

- Python exact/reference implementation:
  `7cc7e987416c28ae87349585cdd64b500e7c687d45625cce1f1a14f4941040e0`;
- independent C++17 implementation:
  `60b81badc5f4bcefbdc006b026043ea6b7ce74c829f6c57c7ba9793ec46cb24c`.

Environment: Python 3.12.14; g++ 13.3.0; exact integers and
`fractions.Fraction`; randomized seeds `20261028+R`.

Executed commands:
```text
python /workspace/euler_phase_census.py 2 --scan 600
python /workspace/euler_phase_census.py 4 17 442 466 --exact
python /workspace/euler_phase_census.py 442 466 --random-trials 128
g++ -O2 -std=c++17 -Wall -Wextra -pedantic   /workspace/euler_phase_census.cpp -o /workspace/euler_phase_census_cpp
/workspace/euler_phase_census_cpp 4 17 57 317 442 466
```

Coverage: exhaustive roots `2<=R<=600` for the float band search, exact
rational reconstruction at `R=4,17,442,466`, and additional exact fixtures
`R=9,21,57,100,317`. The float scan was used only to select extrema; every
reported decisive root was recomputed exactly. No numerical uncertainty
affects the sign reversals or reconstruction identities.

## G. Authority, continuity, and source status

Authority retrieved through the GitHub connector:

- `main@904f056ea039e7938587a8254125b18eab45cfd0`, merged PR #1035;
- `AGENTS.md` blob `d11dea7ea8f2206ed5147f0231846d0a4652f8e9`;
- `CURRENT_PROOF_CONTRACT.md` blob
  `24bd727096001b68c76b28fe70c99b8d548d7bfe`;
- merged #1035 source blobs: pointwise
  `c327c556f39ee7014fd774b24d0f95a1ece050e0`, finite convolution
  `e97561ef330a9996fd807d8910369f0698147b01`, audit
  `5dc146b7ad0e0dd246110042a8775ebdb750e707`;
- external handoffs blob
  `038018145c0fddb2f6306c0712373adf9cd1ea52`; no entry newer than
  2026-10-18 changes this lane.

Today, Wheel report blob
`27dd840bb424d551f2dce0beebd7b0d2f66622f0`, claim
`20261028-wheel-1`, was consumed. Coordinator, Owner, Analytic, Referee and
Lean Verification were `TODAY=PENDING` at intake.

The complete 2026-10-27 set was consumed as `YESTERDAY=CARRY_FORWARD`:

- Coordinator mirrors, identical blob
  `b12989910667ec44b7cb5cb9e7395a6a5602f560`, claim
  `20261027-coordinator-1`;
- Owner `a559d88d6974ba3b9bd8f9a026058b15f2879309`, claim
  `20261027-owner-1`;
- Analytic `0ab3dbac7df59b6fb4c1f35a29c010160cc42f3e`, claim
  `20261027-analytic-1`;
- Wheel `8318a17434501b49d5a948c6dc750790dcdb0183`, claim
  `20261027-wheel-1`;
- Census `842d50e673d5b6967b79835807a05b2d7bef49f8`, claim
  `20261027-census-1`;
- Referee `f7e86621f16ef102520c133287717b0b1aec79e0`, claims
  `20261027-referee-1..2`;
- Lean `2e1c4f807055c964f07b3e6c344d156d803bbc7f`, claim
  `20261027-lean-1`.

Open/draft PRs #1036-#1042 were inspected at their actual heads. They certify
or propose exact Euler identities but no fixed-`eta`, finite-C, canonical VF,
or RH estimate. PR #1042 is open and non-draft; all others are open drafts.
No PR, issue, Lean source, branch, workflow, or report owned by another agent
was modified.

## H. Ranked hypothesis portfolio and continuation checkpoint

1. **Complete cross-phase compensation in `U_R` — CONTINUE.**
   The (R=442) cancellation is strong finite evidence that the complete
   four-term source, not a phase band, is the right carrier.
2. **Mobius inverse-divisor constraint as the hidden variable — CONTINUE.**
   Random sign surrogates destroy the observed cancellation; test conditioning
   by `gcd(b,Lq)`, divisor ancestry, and terminal-window membership.
3. **Exact-zero sparsity as a quantitative payment — SUSPEND.**
   It counts kernel zeros and does not control the nonzero signed mass.
4. **Separate absolute estimates for phase bands — REJECT.**
   Exact finite ratios above show catastrophic loss before recombination.

Next run should not repeat the `R<=600` scan. Reconstruct the full #1041
four-term `U_R` exactly on the same roots and partition **jointly** by
`gcd(b,Lq)` and terminal-window membership. The preregistered discriminator
is whether the compensating opposite phase bands share a common divisor
ancestry class. A positive result must produce a carrier-defined inverse
condition; a negative result should give the smallest exact counterexample.

**Canonical `VFCanonicalSquareVonKochStatement`: OPEN.**
**Euler finite-C statement: OPEN.**
**RH: OPEN.**

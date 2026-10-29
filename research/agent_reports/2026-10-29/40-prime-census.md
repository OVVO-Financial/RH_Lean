# RH_Lean agent daily report - 2026-10-29 / RH | Prime Census Laboratory

**Status:** COMPLETED  
**Invocation:** scheduled run begun 2026-10-29 01:51 America/New_York  
**Final authority refresh:** 2026-10-29 01:54 America/New_York  
**Pinned main:** `a59d351aa33c3cc071ab7b9221f765dc89a2012c`  
**Authority blobs:** `AGENTS.md` `4bc5e5bacd333be41ca9334fa6eaf8e29b9bd1c8`; `CURRENT_PROOF_CONTRACT.md` `24bd727096001b68c76b28fe70c99b8d548d7bfe`  
**Material main blob:** `research/EULER_FRACTIONAL_COUPLED_20261027.lean` `e6c4b1690e497760d366e36b28a1f7aa60e19f85`  
**External handoffs blob:** `038018145c0fddb2f6306c0712373adf9cd1ea52`  
**New claim:** `20261029-census-1`  
**Evidence classes:** `FINITE_COMPUTATION`, `CONJECTURE`, `NO_FIXED_ETA_GAIN`, `NO_RH`.

## A. Main result

### Claim `20261029-census-1`: principal compensation is genuinely cross-ancestry and changes sign repeatedly

For
[
 f_d(R)=((R^2-1)mod d)/d,qquad
 m_d=d^{-1}sum_{rmod d}f_d(r),
]
retain today's Analytic coefficient
[
 alpha_d=mu(t)2^{omega(t)-1}
]
when uniquely (d=s^2t), (s,t) are squarefree, ((s,t)=1), and (t>1), and put (alpha_d=0) otherwise. The exact low-conductor principal reconstruction omitted by centering is
[
 P(Q)=2sum_{2le dle Q}alpha_d m_d.
]

The census gives three decisive finite facts.

1. The first composite compensation occurs at (d=6). Before it,
   (P(5)=-157/90); since (alpha_6=2), (m_6=13/36), the increment
   is (13/9), leaving (P(6)=-3/10).

2. The first full sign reversal is at (Q=10). The (d=10) mode has
   (alpha_{10}=2), (m_{10}=9/20), increment (9/5), and changes
   (P(9)=-61/70) into (P(10)=13/14).

3. Shared-factor ancestry immediately reverses that conclusion.
   The (d=12=2^2cdot3) mode has (alpha_{12}=-1),
   (m_{12}=25/72), increment (-25/36), changing
   (P(11)=31/154) into (P(12)=-1367/2772).

Thus the coherent negative prime principal mode from
`20261029-wheel-1` is neither negligible nor globally one-signed after
source-faithful recombination. Squarefree composite modes compensate it,
while repeated-prime ancestry can reverse the compensation. A proof may
not retain only one of these populations.

## B. Mathematical mystery and preregistered hypotheses

Today's Wheel report requested the smallest exact composite compensation
and a classification by (d=s^2t). The competing explanations were:

- **H1, squarefree compensation:** composite squarefree product modes
  compensate the negative prime debt, while shared-factor modes are lower
  order.
- **H2, ancestry exchange:** the principal bill is paid nonlocally between
  the (s=1) and (s>1) populations, so neither population has a stable
  sign or can be discarded.
- **Falsifier for both:** one population retains a fixed sign and dominates
  uniformly through the held-out interval.

The observable discriminator was the exact prefix (P(Q)), its decomposition
(P_1(Q)+P_{>1}(Q)) by (s=1) versus (s>1), sign-reversal locations, and
the prime/composite decomposition.

The result supports H2 only as a finite mechanism. It refutes any fixed-sign
or negligible-shared-ancestry inference on the tested domain, but proves no
all-scale cancellation theorem.

## C. Exact carrier and two independent reconstructions

The carrier is the literal principal mean of the original
`2*eulerFractionOffQ` low-product sector, not a randomized or centered
surrogate. Endpoints are (2le dle Q), residues are (0le r<d), and all
arithmetic is exact integer/rational arithmetic.

Implementation A:

1. sieve exact Möbius values;
2. reconstruct the unique cubefree representation (d=s^2t);
3. compute (alpha_d=mu(t)2^{omega(t)-1});
4. compute (m_d=d^{-2}sum_{r=0}^{d-1}((r^2-1)mod d)).

Implementation B independently enumerates every original unordered pair
(1le a<b), (mu(a)mu(b)
e0), (able Q), groups by (d=ab) and
(s=(a,b)), and attaches the same directly enumerated residue mean (m_{ab}).

At every (dle10000), the two coefficient arrays agreed exactly. Their
square-part totals also agreed exactly. The domain contained 8,258 nonzero
product moduli and 21,495 original physical unordered pairs. The compact
exact square-part/final-total checksum was
`3ed4a3fdb5c26337a242fff8beb04baf53be477a442d2c0a37c44b7db3878177`.

Environment: CPython 3.12.14; reference script SHA-256
`71e24226279d80efadf0043cb3dc6ee0035dd55684f8ad4c78810331c30fc630`.
The calculation uses no floating point for claims; decimals below are display
approximations of exact fractions.

## D. Results and exceptional configurations

There were 220 prefix sign reversals for (2le Qle10000). The first
twenty begin at
[
10,12,14,18,22,30,34,42,57,68,69,70,87,105,143,154,155,170,210,212.
]
This rules out extrapolating the prime-row sign or the first composite
compensation to the complete principal carrier.

Selected exact-prefix decimal diagnostics:

| (Q) | (P(Q)) | (P_1(Q)) | (P_{>1}(Q)) |
|---:|---:|---:|---:|
| 100 | 5.687375 | 13.978606 | -8.291230 |
| 1,000 | 7.298207 | -3.964594 | 11.262801 |
| 3,000 | -44.535289 | -77.721627 | 33.186338 |
| 5,000 | -0.022765 | -50.909139 | 50.886374 |
| 7,000 | -124.999036 | -152.129273 | 27.130236 |
| 8,000 | 18.440067 | -83.169340 | 101.609407 |
| 10,000 | -152.655294 | -177.937576 | 25.282282 |

At (Q=1000) and (Q=8000), the (s>1) population reverses the sign of
the squarefree population. At (Q=5000), the two are almost exactly opposed,
but the held-out range destroys any conservation claim: (P(7000)) and
(P(10000)) are strongly negative.

The prime/composite split is equally nonlocal. At (Q=5000), the prime
contribution is approximately (-655.796097), while all composite modes
contribute (+655.773332). At (Q=10000), these are approximately
(-1212.327190) and (+1059.671896), respectively. The near equality at
5000 is therefore not an invariant.

The strongest excursions through 10000 were
[
 min P(Q)=P(9889)approx-215.130411,qquad
 max P(Q)=P(8511)approx149.737043.
]
The maximum observed (|P(Q)|/sqrt Q) was approximately (2.163345) at
(Q=9889).

## E. Falsification and conjecture

**Refuted finite inference:** “the prime principal debt remains one-signed
after adding composite product modes” fails first at (Q=10).

**Refuted finite inference:** “shared-factor product modes are negligible
for the sign of the principal reconstruction” fails at (Q=1000), where
(P_1approx-3.965), (P_{>1}approx11.263), and the complete total is
positive. The smallest individual shared-factor sign reversal is already
(d=12).

**Candidate only:**
for every (arepsilon>0),
[
 |P(Q)|ll_arepsilon Q^{1/2+arepsilon}.
]
Discovery used (Qle5000); the fixed exponent was then tested without
revision on (5001le Qle10000). It survived, with the displayed maximum
normalized excursion, but no universal constant or theorem is claimed.
The conjecture is meaningful because it would pay the low-conductor
principal reconstruction at square-root scale; it still would not control
the high-conductor complement or low/high mixed energy.

A plausible proof route is to exploit the exact convolution identity
(2alpha_d=(mu*mu)(d)-1_{{d=u^2}}mu(u)^2) together with the
quadratic-residue structure of (m_d), rather than bounding ancestry
classes separately. The data specifically warn that separate absolute
payment of (s=1) and (s>1) loses the observed compensation.

## F. Proof impact

This advances proposed node
`MECH-EULER-LOW-CONDUCTOR-SHARED-GCD-MOMENT` only as a source-preservation
and hypothesis-generation result. It supplies the missing finite answer to
the Wheel handoff: composite compensation begins at (d=6), first wins at
(Q=10), and shared-factor ancestry first reverses it at (d=12).

It does not prove the Analytic centered-moment claim, a fixed-(eta) sharp
shell estimate, finite A/C, an exponent below (7/8), the canonical
`VFCanonicalSquareVonKochStatement`, or RH. The evidence status of
`20261029-census-1` is `FINITE_COMPUTATION`; the square-root statement is
`CONJECTURE`.

The next mathematical lemma worth attacking is a uniform estimate for the
complete principal convolution
[
 sum_{dle Q}igl((mu*mu)(d)-1_{{d=u^2}}mu(u)^2igr)m_d,
]
with (m_d) retained exactly. A theorem for only prime, squarefree, or
shared-factor modes is structurally insufficient.

## G. Authority, continuity, and GitHub state

Today's consumed reports:

- Analytic Type II blob
  `0c0a7af4266e0b374ad40d36ddf01e0f0fbe25dc`,
  claim `20261029-analytic-1`;
- Finite Wheel blob
  `27b957207d399a1d6c4187b6bfab72433be5a52d`,
  claim `20261029-wheel-1`;
- Coordinator, Owner, Referee, Lean Verification:
  `TODAY=PENDING` at final intake.

The available 2026-10-28 Coordinator, Owner, Wheel, Census, Referee and Lean
reports were consumed as `YESTERDAY=CARRY_FORWARD`. The 2026-10-28 Analytic
report was absent. The external inbox has no entry newer than 2026-10-18.

At final refresh, main remained
`a59d351aa33c3cc071ab7b9221f765dc89a2012c`. Open PRs #1048-#1051 were
unmerged and mergeable at their observed heads: #1048 `179655dd`, #1049
`24b6490c`, #1050 `8930575b`, #1051 `3d687adf`. Green PR evidence
certifies only the declarations at those exact heads, not this census.

No main source, proof branch, PR, issue, workflow, schedule, permission, or
another agent's report was modified.

## H. Ranked portfolio and continuation checkpoint

1. **Complete principal convolution at square-root scale — CONTINUE.**
   Test analytic representations of (m_d) that preserve CRT/shared-factor
   structure; do not split ancestry classes before cancellation.
2. **Low-conductor centered moment — CONTINUE WITH REVIEW.**
   Today's Analytic paper proof is independent progress, but principal and
   mixed bills remain.
3. **Prime-only principal sign as global payment — REJECT.**
   Exact smallest counterexample: (Q=10).
4. **Negligible shared-factor principal modes — REJECT.**
   Smallest individual reversal: (d=12); aggregate sign reversals at
   (Q=1000) and (Q=8000).
5. **Near conservation seen at (Q=5000) — REJECT.**
   Held-out (Q=7000) and (Q=10000) destroy it.

Next run should not repeat the (Qle10000) prefix census. Derive or
falsify a multiplicative/character formula for (m_{s^2t}), then test the
fixed square-root conjecture on a segmented range beyond 10000 using that
formula. The first discrepancy between a formula and direct residue
enumeration is the stopping condition.

**Canonical theorem:** OPEN.  
**Fixed-(eta) Euler source payment:** OPEN.  
**RH:** OPEN.

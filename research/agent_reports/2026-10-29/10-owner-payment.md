# RH_Lean agent daily report - 2026-10-29 / RH | Owner Payment

**Status:** COMPLETED
**Invocation:** scheduled run begun 2026-10-29 20:43 America/New_York
**Final authority refresh:** 2026-10-29 America/New_York
**Pinned main:** `d6b59b3fac72e5813145bc1955151e1c8e93e4c6`
**Main tree:** `0d9fa6039871e5e0e5242ded77f771a6eaa88a25`
**Authority blobs:** `AGENTS.md` `d30a5c4320bec77a510932e72ce7f17d98a68e51`; `CURRENT_PROOF_CONTRACT.md` `7a067ec0423a998e1079e37494061346d8ee02b0`; square-clock directive `d275035a5a7de919b31948d58f0341627a877461`.
**New claim:** `20261029-owner-1`
**Result classes:** `PAPER_PROOF / EXACT MOVING-ANCESTRY IDENTITY`, `PAPER_PROOF / HIGH-PRIME PACKET ENERGY FLOOR`, `COUNTEREXAMPLE_TO_SECTORWISE_PAYMENT / INFINITE FAMILY`, `FINITE_COMPUTATION`, `NO_NEW_GLOBAL_QUANTITATIVE_BOUND`, `NO_RH`.

## A. Most important mathematical development

### Claim `20261029-owner-1`: high products have an exact divisor window, and the high-prime packet cannot be paid separately

The original high-product coefficient has a source-exact formula. If a nonzero product modulus is written uniquely as
```text
d = s^2*t,  s,t squarefree, gcd(s,t)=1,
```
then at root `R` its strict unordered coefficient is
```text
alpha_R(d)
 = mu(t) * #{v | t : v^2>t and s*v<R}.                    (1)
```
It is zero outside this cubefree form and when `t=1`. Thus repeated-prime ancestry is not an error term: it is the square part `s), and the moving `a<b<R` boundary is literally the upper divisor window `v<R/s`.

On a dyadic root interval `H<=R<2H`, every modulus `d<H` is static: all its factor pairs are admitted and (1) reduces to the accepted
```text
alpha_d = mu(t)*2^(omega(t)-1).
```
Hence the high complement at `Q=floor(sqrt H)` splits exactly into a static intermediate range `Q<d<H` and a genuinely moving top range `d>=H`.

The static intermediate range already contains a compulsory coherent packet. For integers `H,D` with `2D<=H/2), define the literal original prime-pair row
```text
V_(H,D)(R) = -2 * sum_(D<p<=2D, p prime) f_p(R),
f_p(R)=((R^2-1) mod p)/p.
```
Then
```text
sum_(H<=R<2H) V_(H,D)(R)^2
  >= H * (pi(2D)-pi(D))^2 / 81.                           (2)
```
For `D` of order `H^(3/4)`, the prime number theorem makes (2)
```text
>> H^(5/2)/log^2 H.                                       (3)
```
Therefore, for every fixed `eta>0`, this one original high-product ancestry sector is not `O_epsilon(H^(5/2-eta+epsilon))` when `epsilon<eta`. Any successful fixed-`eta` source proof must combine the prime packet with composite-product principal compensation before taking a norm. Prime-by-prime, ancestry-by-ancestry, or positive-energy payment is impossible at the required scale.

This is a source-faithful no-go for a proof architecture, not a lower bound for the complete high row: composite modes may cancel the packet.

## B. Current authoritative objective

At live `main@d6b59b3f`, the canonical theorem remains
```text
exists C>=0, forall R>=2,
  |pi(R^2)-VF_can(R^2)| <= C*R*log R.
```
The nearer open benchmark is, for some fixed `eta>0`,
```text
sum_(H<=R<2H) |Delta_R|^2
  <<_(eta,epsilon) H^(5/2-eta+epsilon),
Delta_R=sum_(R^2<=n<(R+1)^2) mu(n).
```
The accepted centered low-product moment `20261029-analytic-1` and Coordinator corollary `20261029-coordinator-1` pay the complete uncentered `d<=sqrt H` row at `O_epsilon(H^(2+epsilon))). The first unbounded source bill is the exact `d>sqrt H` complement, followed by restoration of the floor/fractional triad and sharp endpoint difference.

Material main blobs inspected:

- `research/EULER_FRACTIONAL_COUPLED_20261027.lean`: `e6c4b1690e497760d366e36b28a1f7aa60e19f85`;
- centered coprime covariance: `83c83502e815d15c06d2eda8c1890022adbca119`;
- quadratic shift orthogonality: `a0c2817d7ae43e4cf67d5d7a3f3bccc9a5f6c285`;
- sharp OAI/Euler localization: `1f5b2e57f24e44e5b7b5cea80d437ac8350365b0`.

The compiled exact triad is
```text
eulerFloorBilinearQ
 = X_R*(sum_(a<R)mu(a)/a)^2
   - eulerFractionDiagonalQ
   - 2*eulerFractionOffQ,
```
and the diagonal is kernel-bounded between `0` and `R-1`. No term in this identity is silently discarded below.

## C. Structural hypothesis investigated

**Hypothesis.** The high product might be payable by bounding prime, squarefree-composite, and repeated-prime ancestry sectors separately, then summing their energies.

**Verdict: REFUTED.** Equation (3) shows the prime sector alone saturates the reference `H^(5/2)` scale, up to logarithms, in the static high range. The Census sign reversals at `d=6,10,12` are not incidental: composite and repeated-prime principal modes are mathematically required counterterms.

**Surviving mechanism.** Joint dyadic product layers, retaining the complete principal convolution and centered shared-frequency covariance, may cancel before norms. This is a substantially narrower and falsifiable architecture.

## D. Mathematical derivation

### Exact moving ancestry

A nonzero original pair has squarefree `a,b`. Put
```text
s=gcd(a,b), a=s*u, b=s*v.
```
Then `s,u,v` are pairwise coprime and squarefree,
```text
d=ab=s^2*u*v=s^2*t,  t=u*v,
mu(a)mu(b)=mu(t).
```
The strict order `a<b` is `u<v), hence `v^2>t); the moving admission is exactly `s*v<R`. Conversely every divisor `v|t` satisfying these two inequalities gives one original pair. This proves (1), including multiplicity and sign.

The boundary derivative is also exact:
```text
alpha_(R+1)(d)-alpha_R(d)
 = mu(t) * 1_{s|R, (R/s)|t, (R/s)^2>t}.                  (4)
```
For `d<H<=R), every larger factor is at most `d<R), so all complementary pairs are admitted and the coefficient is static.

Consequently,
```text
2*eulerFractionOffQ(R)
 = 2*sum_(2<=d<R^2) alpha_R(d)*f_d(R),                   (5)
```
with no cloned occurrence. Splitting (5) at `Q` is an exact partition of the original strict off-diagonal.

### High-prime energy floor

For every odd prime, the elementary square-residue support argument in `20261029-wheel-1` gives `m_p>=1/9), where
```text
m_p=(1/p)*sum_(r mod p) f_p(r).
```
The function `f_p` is nonnegative and `p`-periodic. Any interval of `H` consecutive roots contains `floor(H/p)` complete periods, so
```text
sum_(H<=R<2H) f_p(R)
 >= floor(H/p)*p*m_p
 >= (H-p)/9
 >= H/18                                                       (6)
```
when `p<=2D<=H/2`.

Let `N=pi(2D)-pi(D)`. Since `V_(H,D)(R)<=0), summing (6) gives
```text
sum_R |V_(H,D)(R)| >= H*N/9.
```
Cauchy-Schwarz over exactly `H` roots yields (2). Taking, for example, an integer `D asymp H^(3/4)/8`, PNT gives `N asymp D/log D`, proving (3). For large `H`, this packet satisfies `sqrt H<D<2D<H), so it belongs literally to the static high complement after the Coordinator split.

## E. Quantitative consequence

The result establishes no upper bound on the complete high product and no new Mertens exponent.

It does establish an independently proved inverse restriction on any successful estimate:

> At product scale `D asymp H^(3/4)`, a fixed-`eta` gain cannot arise from separately positive bounds on the prime packet and its complement. The full layer must contain a negative cross term or principal cancellation of order at least `H D^2/log^2 D`.

Equivalently, if `W_(H,D)` is the exact composite remainder of the same layer, then any bound `||V+W||_2^2=o(||V||_2^2)` forces
```text
2*<V,W> <= -||V||_2^2 + o(||V||_2^2),
```
after retaining `||W||_2^2`. This is a necessary configuration, not a proved compensation theorem.

The diagonal term remains `O(H)` per root under the compiled bound, but the continuous reciprocal square, the complete high fractional row, their square-endpoint differences, and all sharp-shell cross terms remain unpaid.

## F. Falsification and circularity review

1. **Exact carrier:** (1) was independently enumerated for every `3<=R<=30` and every `2<=d<R^2`; direct original pairs agreed with the divisor-window formula.
2. **Exact rational packet checks:** (2) passed at `(H,D)=(64,12),(128,20),(256,32),(512,48),(1024,80)`. These checks are regression evidence, not the universal proof.
3. **No independence:** the proof uses periodicity, nonnegativity, a proved mean floor, and Cauchy-Schwarz.
4. **No cloned history:** each divisor `v` in (1) corresponds to exactly one unordered original pair.
5. **Repeated-prime masks retained:** `s>1` is explicit; non-cubefree products have zero coefficient.
6. **Moving boundary retained:** (4) identifies the exact new occurrence at `b=R`.
7. **No global lower-bound overclaim:** cancellation by composite modes is allowed and is the point of the obstruction.
8. **No target equivalence:** (1)-(3) do not assume a Mertens or shell envelope. PNT is used only to size the admitted prime population.
9. **Full-statistic warning:** (5) is only the fractional off-diagonal. The compiled diagonal/reciprocal-square triad and endpoint transfer remain separate.
10. **Compatibility:** `20261029-coordinator-1` pays `d<=sqrt H`; this packet has `d>sqrt H`. `20261029-referee-2` concerns an uncentered low-prime strengthening and is consistent with the same coherent principal phenomenon.

## G. Conceptual interpretation

The high complement is not uniformly “moving.” It has two arithmetically different regimes:

- `sqrt H<d<H`: static cubefree coefficients, but long square-clock periods and coherent principal packets;
- `d>=H`: genuinely moving factor admission governed by the divisor window (1) and boundary law (4).

The first obstruction appears before the moving cutoff becomes active. Thus improving only incomplete-period cancellation or boundary combinatorics cannot pay the full high source. Composite principal compensation is required already in the static intermediate range.

This also explains why the low principal prefix changes sign in Census: the source needs cross-ancestry exchange. Treating prime, squarefree composite, and repeated-prime modes as independent positive bills destroys the only available cancellation mechanism.

## H. Competing mechanisms

- **CONTINUE:** complete dyadic principal convolution `sum alpha_d*m_d`, without separating `s=1` and `s>1`.
- **CONTINUE:** centered full-layer shared-frequency analysis, with incomplete periods and 2-adic resonances.
- **PROMOTE:** the exact static/moving split at `d=H` as the high-source ledger.
- **ABANDON:** prime-only, ancestry-only, or positive sectorwise energy payment at the sharp-shell scale.
- **KEEP DISTINCT:** MU-LIFT, direct VF/JOH, CORR4, FINITE-AC, CODIV, and NYMAN; this result neither advances nor refutes them.

## I. Specialist handoffs

**Coordinator:** record `20261029-owner-1` as a no-go for sectorwise high payment. The first high layer is not merely an incomplete-period problem; its prime principal packet saturates the reference scale.

**Analytic Type II:** decompose a static dyadic layer `D<d<=2D<H` into its complete principal convolution and centered remainder. Any upper bound must exhibit the composite-prime cross term; a sum of separate norms cannot gain fixed `eta`.

**Finite Wheel:** formalize the divisor-window coefficient (1) and boundary law (4), including the 2-adic cases. Seek a combinatorial pairing between prime `d=p` and composite `d` modes in the same static layer.

**Prime Census:** compute exact rational `P_D=2 sum_(D<d<=2D)alpha_d*m_d` and centered layer energy for held-out `D` near `H^(3/4)`. Measure the cross term with the prime packet, not the packet alone.

**Adversarial Referee:** audit constants in (2), the PNT passage to (3), and the claim that `d<H` makes every factor pair uniformly admitted. Try to construct a full-layer packet where composite modes fail to compensate.

**Lean Verification:** the suitable independent formal targets are (1), (4), and the finite-period inequality (2) with the prime-count factor left exact. Do not encode the asymptotic PNT corollary as a high-source upper bound.

## J. First independently missing lemma

The smallest new arithmetic statement is a dyadic principal-convolution estimate on the exact static high carrier:
```text
P_D = 2*sum_(D<d<=2D)
        alpha_d*m_d
    = sum_(D<d<=2D)
        ((mu*mu)(d)-1_{d=u^2}*mu(u)^2)*m_d,

|P_D| <<_epsilon D^(1/2+epsilon).                          (7)
```
Equation (7) is consistent with the October 29 Census conjecture but unproved. It is not sufficient for the shell theorem: after (7), the centered static layer, the genuinely moving `d>=H` range, the triad, and endpoint transfer remain. It is nevertheless independently testable and would pay the coherent principal packet only through the required composite ancestry compensation.

## K. Next-run resume capsule

- Main: `d6b59b3fac72e5813145bc1955151e1c8e93e4c6`; tree `0d9fa6039871e5e0e5242ded77f771a6eaa88a25`.
- Claim: `20261029-owner-1`, equations (1)-(7).
- Accepted input: `20261029-analytic-1`, centered low moment `HQ^(1+epsilon)+Q^(4+epsilon)`.
- Coordinator input: `20261029-coordinator-1`, complete uncentered `d<=sqrt H` energy `O_epsilon(H^(2+epsilon))`.
- New structural result: exact moving divisor-window ancestry and static/moving split at `d=H`.
- New no-go: the static high prime packet at `D asymp H^(3/4)` has energy `>>H^(5/2)/log^2H`.
- First missing lemma: (7), followed by a centered full-layer theorem.
- Today consumed: Coordinator `a6b758112539d0841472082a69da3a4ce49d79cb`; Analytic `0c0a7af4266e0b374ad40d36ddf01e0f0fbe25dc`; Wheel `27b957207d399a1d6c4187b6bfab72433be5a52d`; Census `00de1c235982179677834940d270357999b75d42`; Referee `9c0e84cb7b7303d501c33550697b45c5ded3a46a`; Lean `7296e00bf6e606a53af8acc35a11f24a5a99a58f`.
- Yesterday Owner: `af67eace39fb00261953a92de1f7067489be7546`, `YESTERDAY=CARRY_FORWARD`.
- External inbox: `038018145c0fddb2f6306c0712373adf9cd1ea52`, no newer handoff.
- Live PR search: no open or draft pull requests. #1051 and #1052 are merged; #1053 is documentation/routing only.
- Canonical theorem OPEN; strict exponent below `7/8` OPEN; RH OPEN.

## Publication verification

Early `IN_PROGRESS` checkpoint: commit `d65f717dcf155ef81160da527fca7c2ea6a02948`, read back as blob `91269b6460af76325da28cfe8f5549dc5c3c9fd7`.

Completed mathematical synthesis: commit `772f8d2ab5d084e5fef6d9c3970a72ff676e264f`, read back as blob `3f1dd68aaa75c08bd6551d6cf060665387834055` (14,086 characters; `COMPLETED`, claim `20261029-owner-1`, equation (7), and no non-whitespace control characters verified). This receipt update changes no mathematics.

# RH_Lean agent daily report - 2026-10-29 / RH | Analytic Type II

**Status:** COMPLETED
**Invocation:** scheduled run begun 2026-10-28 22:26 America/New_York
**Final authority refresh:** 2026-10-29 America/New_York
**Pinned main:** `a59d351aa33c3cc071ab7b9221f765dc89a2012c`
**Main tree:** `ca27a57919b217ae7875df8fe092dd7fe0724136`
**Authority blobs:** `AGENTS.md` `4bc5e5bacd333be41ca9334fa6eaf8e29b9bd1c8`; `CURRENT_PROOF_CONTRACT.md` `24bd727096001b68c76b28fe70c99b8d548d7bfe`
**Material main blobs:** `EULER_FRACTIONAL_COUPLED_20261027.lean` `e6c4b1690e497760d366e36b28a1f7aa60e19f85`; `EULER_SQUARE_WINDOW_SHARED_GCD_20261028.md` `7ad1718d78a6afaac87f32ad9e1cc5a45f822164`; `OAI_PAIRED_SHARP_EULER_SQUARE_LOCALIZATION_20261028.lean` `1f5b2e57f24e44e5b7b5cea80d437ac8350365b0`
**External handoffs blob:** `038018145c0fddb2f6306c0712373adf9cd1ea52`
**Continuity:** no earlier 2026-10-29 or 2026-10-28 Analytic report existed at intake, so 2026-10-27 blob `0ab3dbac7df59b6fb4c1f35a29c010160cc42f3e` was `YESTERDAY=CARRY_FORWARD`.
**New claim:** `20261029-analytic-1`
**Result classes:** `PAPER_PROOF_NEEDS_REVIEW / NEW UNCONDITIONAL LOW-CONDUCTOR MOMENT`, `FINITE_COMPUTATION`, `PROVED_IN_LEAN_PR_GREEN_UNMERGED` for inputs only, `NO_FIXED_ETA_GAIN`, `NO_RH`.

## A. Most important analytic result

### Claim `20261029-analytic-1`: all low product moduli, including shared primes, have a Q-linear centered moment

For integers (d >= 2), define the actual square-clock fractional column and its principal mean by

```text
f_d(R) = ((R^2 - 1) mod d) / d,
m_d = (1/d) sum_(r mod d) f_d(r),
F_d(R) = f_d(R) - m_d.
```

For (d=s^2t), where (s,t) are squarefree and coprime, define

```text
alpha_d = mu(t) * 2^(omega(t)-1)  if t>1,
alpha_d = 0                       if t=1 or d is not cubefree.
```

Then for every (R>Q),

```text
2 sum_(2<=d<=Q) alpha_d f_d(R)
```

is exactly the part of `2*eulerFractionOffQ(R)` formed by every original pair (1<=a<b<R) with (ab<=Q). Thus the centered low-conductor physical source is

```text
L_Q(R) = 2 sum_(2<=d<=Q) alpha_d F_d(R).
```

The new theorem is: for every real epsilon (>0), there is an effective constant (C_epsilon) such that, uniformly for all integers (H,Q>=2),

```text
sum_(H<=R<2H) |L_Q(R)|^2
  <= C_epsilon * (H*Q^(1+epsilon) + Q^(4+epsilon)).       (1)
```

In particular, when (Q^3<=H),

```text
sum_(H<=R<2H) |L_Q(R)|^2
  <= C_epsilon * H*Q^(1+epsilon).                         (2)
```

This extends PR #1051's first-prime-row estimate to the complete centered low-conductor original off-diagonal source. It includes all cubefree composite product moduli and does not erase shared-prime covariance.

## B. Exact coefficient grouping

Because both original coefficients are Mobius coefficients, nonzero pairs have squarefree (a,b). Write (d=ab=s^2t), where (s=gcd(a,b)), (t) is squarefree and coprime to (s). Then (a=su), (b=sv), (uv=t), and ((u,v)=1).

If (t=1), then (a=b=s), excluded from the strict off-diagonal. If (t>1), there are exactly (2^(omega(t)-1)) unordered complementary pairs (u<v). Every pair has the same sign

```text
mu(a)mu(b)=(-1)^omega(t)=mu(t).
```

This proves the displayed `alpha_d` formula. Since (d<=Q<R), every factor pair lies inside the original ranges. No cutoff or coefficient has been replaced.

## C. Shared-frequency covariance theorem

Use normalized Fourier coefficients

```text
hat F_d(h) = (1/d) sum_(r mod d) F_d(r) exp(-2*pi*i*h*r/d).
```

Let

```text
A(d) = (1+log d) * sigma_(-1/2)(d) / sqrt(d).
```

The following pointwise estimate is unconditional:

```text
|hat F_d(h)| <= A(d)   for every h mod d.                 (3)
```

For (h=0) it is zero by centering. For (h!=0), expand the sawtooth (n/d) in additive characters. Its nonzero coefficient at (k) has magnitude

```text
1 / (d*|1-exp(-2*pi*i*k/d)|).
```

The complete quadratic sum
`G(k,-h;d)=sum_(r mod d) exp(2*pi*i*(k*r^2-h*r)/d)`
satisfies

```text
|G(k,-h;d)|^2 <= d*gcd(2k,d) <= 2*d*gcd(k,d).             (4)
```

Indeed, squaring and setting (u=x-y) leaves an inner geometric sum that vanishes unless (d|2ku); at most (gcd(2k,d)) residues (u) survive. Pairing (k) with (d-k), using
(sin(pi*k/d)>=2k/d) for (1<=k<=d/2), and grouping by (delta=gcd(k,d)) gives (3) with the safe constant shown.

Now put (g=gcd(d,e)), (D=operatorname{lcm}(d,e)). Fourier orthogonality on a complete (D)-period shows that only common frequencies (t/g) survive:

```text
(1/D) sum_(R mod D) F_d(R)F_e(R)
 = sum_(1<=t<g) hat F_d(t*d/g) * hat F_e(-t*e/g).          (5)
```

Consequently,

```text
|complete covariance|
 <= g*A(d)*A(e).                                           (6)
```

This is the new quantitative shared-gcd restriction. The prior exact conditional-mean formula allowed either sign but gave only the trivial bound one. Equation (6) gains essentially (g/sqrt(de)); if (d=ga,e=gb), this is (1/sqrt(ab)), so a large common factor is not itself fatal.

## D. Incomplete-window and energy accounting

The product (F_dF_e) is (D)-periodic and has magnitude below one. Splitting an interval of (H) roots into complete periods plus a remainder gives

```text
|sum_(H<=R<2H) F_d(R)F_e(R)|
 <= H*g*A(d)*A(e) + 2*lcm(d,e).                           (7)
```

For (d=e), use the sharper diagonal bound (H). Expanding (L_Q^2) before absolute values therefore gives the explicit finite estimate

```text
E(H,Q) <= 4H sum_(d<=Q) alpha_d^2
 + 4 sum_(d!=e<=Q) |alpha_d alpha_e|
     * (H*gcd(d,e)*A(d)*A(e) + 2*lcm(d,e)).                (8)
```

To deduce (1), use the elementary divisor bounds, for each fixed positive epsilon,

```text
|alpha_d| <= tau(d) <= C_epsilon*d^epsilon,
sigma_(-1/2)(d) <= tau(d) <= C_epsilon*d^epsilon.
```

The complete shared-factor sum is Q-linear up to logarithms:

```text
sum_(d,e<=Q) gcd(d,e)/sqrt(de)
 <= sum_(g<=Q) (sum_(a<=Q/g) a^(-1/2))^2
 <= 4Q(1+log Q).                                           (9)
```

The incomplete-period bill satisfies

```text
sum_(d,e<=Q) |alpha_d alpha_e| lcm(d,e)
 <= (sum_(d<=Q) |alpha_d|d)^2
 <= C_epsilon Q^(4+epsilon).                               (10)
```

Equations (8)-(10), with epsilon rescaled, prove (1). No Mertens envelope, OAI exponent, prime-density model, or random-sign input is used.

## E. Quantitative relevance and limitations

The result saves a full factor (Q^{1-o(1)}) against the pointwise triangle estimate (H Q^{2+o(1)}) for the complete centered low-conductor product source. Under (Q^3<=H), the long-period remainder is paid and the moment is (HQ^{1+o(1)}).

This is not a strict improvement of the Mertens (7/8) exponent:

1. It controls only (ab<=Q), while the original source has moduli up to order (H^2).
2. It controls the centered columns (F_d), not the principal bill (2 sum alpha_d m_d).
3. It does not control mixed energy between this paid sector and the high-conductor complement.
4. The required sharp shell moment remains
   `sum |Delta_R|^2 << H^(5/2-eta+epsilon)` for some fixed eta (>0).
5. The diagonal term (H sum alpha_d^2 = H Q^{1+o(1)}) shows that no universal improvement below Q-linear energy should be expected from this mechanism alone.

Thus the theorem is an independently proved source estimate, not a renamed target, but it does not activate the canonical consumer.

## F. Falsification and finite checks

The proof retains both known obstructions:

- Shared-prime complete covariance may have either sign; (6) bounds its magnitude rather than assuming independence.
- When (operatorname{lcm}(d,e)>H), the (Q^4) remainder remains. No complete-period argument is applied outside its range.

An exact arithmetic check verified the product coefficient formula for every (2<=d<250). A separate exact rational check verified (6) for every (2<=d,e<60); the bound was respected, and nonzero shared-factor covariances remained present. These are `FINITE_COMPUTATION`, not the proof of (1).

The strongest surviving next problem is an incomplete quadratic-sum estimate replacing the (2*lcm(d,e)) term for (d,e) beyond (H^(1/3)), followed by a source-faithful recombination of principal, low/high mixed, and rank-one terms.

## G. Authority, reports, PRs, and CI

Consumed the 2026-10-28 Coordinator, Owner Payment, Finite Wheel, Prime Census, Adversarial Referee, and Lean Verification reports:

- `20261028-coordinator-1`, blob `162f82242e8eb84f4ed21c1e59342edf3400b6cd`;
- `20261028-owner-1`, blob `af67eace39fb00261953a92de1f7067489be7546`;
- `20261028-wheel-1`, blob `27dd840bb424d551f2dce0beebd7b0d2f66622f0`;
- `20261028-census-1`, blob `dca77bca7ed46d5d9fccbd05a565ed10c000a6c8`;
- `20261028-referee-1..2`, blob `fabec6a00f43ded6139256072d228024d62a015c`;
- `20261028-lean-1`, blob `9698f817e44105033409f90d98b2e018cf727ac8`.

The own prior carry-forward was `20261027-analytic-1`; its (R^{5/3}K_R^{1/3}) bound remains valid but insufficient. The external handoff index has no entry newer than 2026-10-18.

At final refresh, open PRs #1048-#1051 were unmerged and mergeable. Exact heads #1048 `179655dd`, #1049 `24b6490c`, #1050 `8930575b`, and #1051 `3d687adf` had respectively 13/13, 13/13, 12/12, and 13/13 fetched PR-triggered workflows completed successfully. PR #1051's Lean source blobs are `83c83502e815d15c06d2eda8c1890022adbca119` and the first-prime paper blob is `17fd5a56e16f8f9d8fd14a64acbebdfc6bce832d`. Green CI certifies its named coprime covariance declarations and regressions, not claim `20261029-analytic-1`.

## H. Specialist handoff and next-run capsule

**Adversarial Referee:** check the quadratic Gauss bound (4), the common-frequency identity (5), the cubefree coefficient `alpha_d`, and the epsilon accounting in (8)-(10). In particular, audit even moduli and the factor two in the incomplete remainder.

**Lean Verification:** formalize only after referee acceptance. The highest-value declarations are the exact `alpha_d` grouping and finite shared-frequency covariance bound (8), with the principal mean visibly excluded.

**Coordinator:** proposed node `MECH-EULER-LOW-CONDUCTOR-SHARED-GCD-MOMENT`; logical status `PAPER_PROOF_NEEDS_REVIEW`, formal status `NOT_FORMALIZED`, carrier the centered (ab<=Q) part of the original `eulerFractionOffQ). It advances the source program but has no edge claiming fixed eta.

**Next run:** seek a uniform incomplete quadratic-correlation bound for the same physical (R^2-1) clock when (H<lcm(d,e)), first on dyadic (d,e) ranges with explicit gcd dependence. Any proposed theorem must be tested against the adjacent coprime long-period resonance in `EULER_SQUARE_WINDOW_SHARED_GCD_20261028.md`.

**Final mathematical status:** one new unconditional low-conductor centered moment is paper-proved; no principal/high-conductor closure, no strict exponent below (7/8), canonical theorem open, RH open.


## I. Publication verification

The early `IN_PROGRESS` checkpoint was created by commit `e14ba710c8ab21dbbfb2d143f6f06d3f369c1e4b`. The completed synthesis was published by commit `45315d2c36cac8692d89871b2018a5ddc6bd78cb` and read back as blob `5945c441015b084d2aeaf8e19a48e2a08fc2a9d6`. The readback contained `COMPLETED`, claim `20261029-analytic-1`, bound (1), and no non-whitespace control characters. This receipt changes no mathematics.


---

## Scheduled continuation - 2026-10-29 22:26 America/New_York

**Status:** IN_PROGRESS
**Pinned live main:** `d6b59b3fac72e5813145bc1955151e1c8e93e4c6`
**Authority blobs:** `AGENTS.md` `d30a5c4320bec77a510932e72ce7f17d98a68e51`; `CURRENT_PROOF_CONTRACT.md` `7a067ec0423a998e1079e37494061346d8ee02b0`; square-clock directive `d275035a5a7de919b31948d58f0341627a877461`.
**Material source blobs:** `EULER_FRACTIONAL_COUPLED_20261027.lean` `e6c4b1690e497760d366e36b28a1f7aa60e19f85`; centered coprime covariance `83c83502e815d15c06d2eda8c1890022adbca119`; quadratic shift orthogonality `a0c2817d7ae43e4cf67d5d7a3f3bccc9a5f6c285`; sharp localization `1f5b2e57f24e44e5b7b5cea80d437ac8350365b0`.
**Continuity consumed:** all 2026-10-29 specialist reports, including Coordinator `a6b7581`, Owner `86f69ec`, prior Analytic `0c0a7af`, Wheel `27b9572`, Census `00de1c2`, Referee `9c0e84c`, Lean `7296e00`; all 2026-10-28 reports as carry-forward; external inbox `0380181` (no item newer than 2026-10-18).

**Research question.** Repair the incomplete-window term in claim `20261029-analytic-1` on the genuine centered square-clock carrier. The candidate mechanism is common-period Fourier completion: for `D=lcm(d,e)`, every frequency of `F_dF_e` has exactly `gcd(d,e)` lifts, so the accepted pointwise Fourier/Gauss bound may reduce the per-pair remainder from `O(D)` to `O(sqrt(de) polylog(de))`. The normalization, shared-frequency zero mode, 2-adic costs, aggregate `Q` exponent, and adjacent/shared-factor falsifiers are under active audit. No new inequality is classified as proved at this checkpoint.


### Final continuation synthesis

**Final status:** COMPLETED  
**New claim:** `20261029-analytic-2`  
**Evidence classes:** `PAPER_PROOF_NEEDS_INDEPENDENT_REVIEW / NEW INCOMPLETE-WINDOW INEQUALITY`, `FINITE_COMPUTATION`, `NO_COMPLETE_SOURCE_BOUND`, `NO_FIXED_ETA_SHELL_GAIN`, `NO_RH`.

#### A. Main theorem: harmonic Fourier completion lowers Q^4 to Q^3

Retain the exact centered physical column and coefficient from claim `20261029-analytic-1`:

```text
f_d(R) = ((R^2-1) mod d)/d,
m_d = d^(-1) sum_(r mod d) f_d(r),
F_d(R) = f_d(R)-m_d,
L_Q(R) = 2 sum_(2<=d<=Q) alpha_d F_d(R).
```

Here `alpha_d=mu(t)2^(omega(t)-1)` when uniquely `d=s^2t`, with squarefree coprime `s,t` and `t>1`, and is zero otherwise. For `Q<R`, this is exactly the centered part of every original strict pair `1<=a<b<R` with `ab<=Q`.

Define the normalized Fourier coefficient on `Z/dZ` and the explicit envelope

```text
hat F_d(h) = d^(-1) sum_(r mod d) F_d(r) exp(-2*pi*i*h*r/d),
A(d) = (1+log d)*sigma_(-1/2)(d)/sqrt(d).
```

The accepted Gauss calculation gives `hat F_d(0)=0` and

```text
|hat F_d(h)| <= A(d)                                      (11)
```

for every frequency, including every even modulus. The new finite theorem is the following. Put `g=gcd(d,e)`, `D=lcm(d,e)),

```text
C(d,e) = D^(-1) sum_(R mod D) F_d(R)F_e(R).
```

For every interval `I` of exactly `H` consecutive integers,

```text
|sum_(R in I) F_d(R)F_e(R) - H*C(d,e)|
 <= d*e*A(d)*A(e)*(1+log D).                              (12)
```

Also

```text
|C(d,e)| <= g*A(d)*A(e).                                  (13)
```

Consequently, for every `epsilon>0` there is an effective `C_epsilon`, uniformly for integers `H,Q>=2),

```text
sum_(H<=R<2H) |L_Q(R)|^2
 <= C_epsilon*(H*Q^(1+epsilon)+Q^(3+epsilon)).             (14)
```

For the original physical admission, retain `2<=Q<H`. Equation (14) improves the prior incomplete-period bill `Q^(4+epsilon)` by one full power of `Q`. In particular, `Q^2<=H` already gives the clean centered estimate `O_epsilon(HQ^(1+epsilon))`; the old proof required `Q^3<=H`.

#### B. Proof of the incomplete-window theorem

Lift both Fourier expansions to the common period `D`. Write `d=ga`, `e=gb), with `(a,b)=1`, so `D=gab`. A product frequency `n mod D` is obtained from pairs

```text
(h,k) in Z/dZ x Z/eZ,
        b*h + a*k = n mod D.                              (15)
```

The homomorphism in (15) is onto because `(a,b)=1`. Its domain has `de=gD` elements, so every frequency has exactly `g` preimages. Therefore every normalized Fourier coefficient of the `D`-periodic product `F_dF_e` has magnitude at most

```text
g*A(d)*A(e).                                               (16)
```

At frequency zero, (16) is exactly (13); no shared-frequency resonance is discarded. For `n!=0 mod D`, the interval character sum obeys

```text
|sum_(R in I) exp(2*pi*i*nR/D)|
 <= D/(2*min(n,D-n)).                                      (17)
```

Summing (17) over every nonzero residue gives at most `D(1+log D)`. Multiplying by (16), and using the exact identity `gD=de`, proves (12). Thus the claimed square-root-size scale is not assumed: after substituting (11), the right side of (12) is

```text
sqrt(d*e)*(1+log d)*(1+log e)
 *sigma_(-1/2)(d)*sigma_(-1/2)(e)*(1+log D).
```

The apparent `sqrt(de)` comes from the already-derived quadratic Gauss saving in each individual column; the incomplete interval itself is handled by exact finite Fourier completion.

Expanding `|L_Q|^2`, applying (12)-(13), and taking absolute values only after the full pair covariance gives

```text
E(H,Q) <= 4H sum_(d,e<=Q) |alpha_d alpha_e| gcd(d,e)A(d)A(e)
 + 4 sum_(d,e<=Q) |alpha_d alpha_e| d*e*A(d)A(e)
       *(1+log lcm(d,e)).                                  (18)
```

The first double sum is `O_epsilon(Q^(1+epsilon))` by writing `d=gu,e=gv` and using

```text
sum_(d,e<=Q) gcd(d,e)/sqrt(de) <= 4Q(1+log Q).
```

For the second sum,

```text
sum_(d<=Q) |alpha_d|*sqrt(d)*(1+log d)*sigma_(-1/2)(d)
 <<_epsilon Q^(3/2+epsilon),
```

so its square, including the final logarithm, is `O_epsilon(Q^(3+epsilon))`. This proves (14), with all implied constants effective and dependent only on `epsilon`.

#### C. Independent even-modulus and Gauss audit

The only parity loss in (11) is explicit. Expanding the residue sawtooth into nonzero additive characters produces the complete quadratic sum

```text
G(k,-h;d) = sum_(r mod d) exp(2*pi*i*(k*r^2-h*r)/d).
```

Squaring and changing variables leaves at most `gcd(2k,d)` surviving shifts, hence

```text
|G(k,-h;d)|^2 <= d*gcd(2k,d) <= 2d*gcd(k,d).
```

Pairing `k` with `d-k`, using `sin(pi*k/d)>=2k/d` for `k<=d/2`, and grouping by `delta=gcd(k,d)` gives (11) with the displayed `sigma_(-1/2)(d)`. No odd-modulus premise, primitive-character premise, or unrecorded 2-adic exception is used. The constant is deliberately coarse; only its uniformity matters for (14).

#### D. Quantitative source payoff and remaining bills

Restoring the low principal constant

```text
P_Q = 2 sum_(2<=d<=Q) alpha_d m_d
```

with only `0<=m_d<1` and `sum_(d<=Q)tau(d)<=Q(1+log Q)` gives

```text
sum_(H<=R<2H)|L_Q(R)+P_Q|^2
 <<_epsilon H*Q^(2+epsilon)+Q^(3+epsilon).                 (19)
```

Thus, for any proposed shell saving `0<eta<1/2`, the complete original uncentered `ab<=Q` row is affordable at the target `H^(5/2-eta+epsilon)` up to

```text
Q = H^(3/4-eta/2-kappa)                                   (20)
```

for any fixed margin `kappa>0`, after choosing the epsilon margin consistently. Before (14), the `Q^4` remainder restricted this same ledger to roughly `Q<=H^(5/8-eta/4)`. The new theorem therefore moves the low/high split to the genuine principal-mode barrier rather than merely improving a cosmetic term.

This does not pay the complete source. Still open are:

1. the exact `ab>Q` high-product complement with moving coefficient `alpha_R(d)`;
2. the complete high principal and centered interaction, including Owner claim `20261029-owner-1`'s coherent prime packet near `D asymp H^(3/4)`;
3. the continuous reciprocal square, fractional diagonal, and their signed cross terms in the compiled Euler triad;
4. endpoint differencing from the fractional/floor source to the sharp shell `Delta_R`;
5. the full sharp moment `H^(5/2-eta+epsilon)`, any strict Mertens exponent below `7/8`, the canonical VF theorem, and RH.

In particular, (19) pays the low vector by a Hilbert-space bound; it does not claim favorable low/high mixed sign. Owner's prime-only high-energy floor is not contradicted: the boundary scale `H^(3/4)` remains precisely where the crude low principal bill saturates.

#### E. Falsification and finite verification

The proof was challenged against adjacent coprime long periods, shared factors, and even moduli. Exact rational recomputation gave:

| H | d | e | D=lcm(d,e) | C(d,e) | exact remainder |
|---:|---:|---:|---:|---:|---:|
| 128 | 192 | 193 | 37056 | 0 | `-48953/222336` |
| 512 | 768 | 769 | 590592 | 0 | `-3581735/3543552` |
| 100 | 36 | 42 | 252 | `1187/54432` | `-170/1701` |
| 100 | 32 | 48 | 96 | `157/6144` | `-235/1152` |
| 34 | 2 | 5 | 10 | 0 | `-7/20` |

Here “remainder” is exactly `sum_(H<=R<2H)F_d(R)F_e(R)-H*C(d,e)`. All satisfy (12). An independent numerical DFT sweep for every `2<=d<=100` found maximum `|hat F_d(h)|/A(d)=0.14536...`; an exhaustive interval sweep for `2<=d,e<=45` over ten held-out lengths found maximum observed remainder/bound ratio `0.003071`. These are finite checks, not the proof.

The known adverse configurations survive with their correct interpretation:

- shared factors create nonzero `C(d,e)`, retained as the zero mode in (13);
- adjacent coprime long periods can have coherent incomplete correlation, but (12) bounds their total Fourier remainder rather than declaring it zero;
- the uncentered primorial counterexample remains valid because (14) is centered and (19), not `O(HQ)`, is the restored physical estimate;
- sectorwise prime payment remains impossible at the reference scale; no positive-energy decomposition of the high layer is asserted.

#### F. Novelty and specialist handoff

Repository search found the crude period split `O(lcm(d,e))`, the complete coprime covariance zero, and the paper shared-GCD zero-mode bound. It did not find the exact `gcd(d,e)`-fiber product-frequency completion (12), the aggregate `Q^3` moment (14), or the enlarged physical split (20). The new ingredient is the nonzero-frequency completion of the already source-admitted columns, not another coordinate identity.

**Adversarial Referee:** independently audit (15)-(18), especially surjectivity and kernel size of the product-frequency map, the normalized Fourier convention, the even-modulus Gauss factor, and the epsilon reparameterization. Attempt a counterexample using adjacent coprime and high-gcd even packets.

**Lean Verification:** after referee acceptance, formalize the finite product-frequency fiber theorem, the geometric-kernel harmonic bound, and the explicit finite form (18). Keep (14) as paper-level until all divisor estimates and source admission are compiled.

**Coordinator:** register `20261029-analytic-2` as a new centered low-source inequality and update the exponent ledger from `Q^4` to `Q^3`. The result reaches the crude-principal barrier but supplies no edge from the high product to the sharp shell.

**Owner Payment:** use (20) as the new exact low/high partition. The first unpaid static layer is now near `H^(3/4-eta/2)`; composite principal compensation and the moving `d>=H` range remain compulsory.

**Finite Wheel / Census:** test the exact Fourier fiber multiplicity and even shared-gcd packets; future computation should focus on the first high layer above (20), not rerun the completed low-column sweep.

#### G. Final authority and verification record

Final live main remains `d6b59b3fac72e5813145bc1955151e1c8e93e4c6`; current PR search returned no open or draft pull requests. Merged #1051 proof head `3d687adfbfd080167e6eedbd5c0185640428f39f` has 13/13 fetched PR-triggered workflows successful. Merged #1052 proof head `4028785b234ae342ac2259d446bae4751c4351f4` has 13/13 successful. These workflows certify their named Lean declarations, not claim `20261029-analytic-2`.

**Next-run first missing lemma:** a source-faithful dyadic bound for the complete high-product layer immediately above (20), with its principal convolution, centered covariance, shared gcd, parity, and moving ancestry retained. After that, restore the reciprocal/diagonal triad and prove the sharp-shell endpoint transfer quantitatively.

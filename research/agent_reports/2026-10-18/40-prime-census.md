# RH_Lean Prime Census Laboratory - 2026-10-18

**Status:** COMPLETED  
**Run:** 2026-10-18T01:51-04:00 scheduled invocation  
**Canonical objective:** `VFCanonicalSquareVonKochStatement` remains OPEN  
**Evidence:** `FINITE_COMPUTATION`, exact finite falsification, `CONJECTURE`; `NO_NEW_QUANTITATIVE_RESULT`

## A. Bottom line

This run tested the first locally cancelling class left by Wheel claim `20261018-wheel-1`: genuine square-shell pairs whose unshared factor set has exactly three primes. They are the first opposite-sign Boolean antichains, but they do **not** form a self-contained cancellation mechanism.

For squarefree `a<b` in one strict shell, put `g=gcd(a,b)` and

```
t(a,b)=omega(a/g)+omega(b/g).
```

Then the original sign is exactly `mu(a)mu(b)=(-1)^t`. The complete shell covariance is therefore the alternating sum of every `t`-class, without omitted cross-orbit pairs.

The `t=3` class is large and negative. Yet after all higher classes are restored, the dyadic shell covariance changes sign: it is `-167` on `64<=r<128`, `+3870` on `128<=r<256`, and `-4650` on the held-out `256<=r<512`. A direct `M,D` reconstruction gives another sign reversal, `+4417`, on `512<=r<1024`. Thus the proposed assertion that first-available three-face cancellation forces nonpositive complete dyadic covariance is **REFUTED** at `H=128` (and again at `H=512`). The true mechanism, if any, is an all-depth parity balance across `t=2,3,4,...`, not a three-face local fold.

No `kappa>0`, shell `5/2-kappa` estimate, weighted covariance theorem below `eps=3/8`, canonical endpoint bound, or RH proof is claimed.

## B. Authority and continuity

Final authority refresh:

- `main@5b218172f995afa8c10f062622c009d490d3b2b2`.
- `AGENTS.md` blob `aef9d6f7a7d3a091f947effd38e9ad42a63e8445`.
- `CURRENT_PROOF_CONTRACT.md` blob `873ec6f70525e1e9ba1defecf8b0951ebe155069`.
- Signed covariance contract blob `8d846d6ee5d559065687b2ed5144aeb7ca3e1850`.
- Merged ancestry/covariance Lean blob `39ef1181fed1bf217fb4409c9ec3cdb96500ce18`.
- Companion paper blob `f61a337fb79e2f1d74da6f7094d256f8eb379b16`.
- Native ancestry-root source `SquareRootAncestryRoot.lean` blob `1b1bc51a6561a192b9e6375ae8df7a36079c4c50`.
- External inbox blob `3cd80e68cec54cc9ce1e00a384cfe37a3a3babc0`.

The 2026-10-17 reports were consumed as `YESTERDAY=CARRY_FORWARD`: Coordinator `9a797b07...`, Owner `6980422d...`, Analytic `08e96ac3...`, Wheel `dbaefd40...`, Census `9efa34cd...`, Referee `a3867e19...`, Lean `1a03815f...`. Today Coordinator/Owner/Analytic/Referee/Lean were `TODAY=PENDING` at intake. Today's Wheel report was consumed from immutable blob `62da494755501409879e894779d026aed70835f8`; its path was no longer present on the branch at the final fetch, so execution is not inferred beyond that retrieved artifact.

Open PR #975 is a #974-to-#915 carrier audit. Its final head is reported CI-green, but it explicitly does not prove child-run descent or a signed arithmetic saving. It does not change this experiment's carrier or conclusion.

## C. Preregistered question and carriers

**Mystery.** Wheel proved that one- and two-prime within-orbit toggles cannot cancel inside a strict square shell, while three-prime mixed-parity antichains can. Does the first available `t=3` class explain the small complete shell increment?

**Hypothesis H1 (three-face mechanism).** The negative `t=3` cohort is stable enough that complete dyadic within-shell covariance remains nonpositive and is controlled by this first cancelling face.

**Hypothesis H2 (all-depth compensation).** The `t=3` cohort is a large signed slice, but even `t>=4` and odd `t>=5` classes compensate it at the same scale; its sign does not predict the complete covariance.

**Discriminator.** For
`I_r={r^2+1,...,r^2+2r}`, enumerate every squarefree site and every unordered physical pair. Let `A_t(r)` count pairs with unshared depth `t`. Exact squarefree parity gives

```
Delta_r = sum_(n in I_r) mu(n)
Delta_r^2 = D_r + 2 sum_(t>=2) (-1)^t A_t(r).
```

No squareful site, diagonal, cross-base pair, or higher-depth class is dropped. Discovery bands were `H=64,128`; `H=256` was held out. Required roots `7,13,103,317,1027,5561` plus `2053,4093`, and nonsquares `380,100003,1000003`, were preregistered checks.

## D. Exact results

Dyadic totals:

| shell range | squarefree D | energy sum Delta^2 | complete C_shell | A2 | A3 | A4 | A5 |
|---|---:|---:|---:|---:|---:|---:|---:|
| 64<=r<128 | 7,471 | 7,137 | -167 | 22,309 | 95,234 | 155,448 | 121,273 |
| 128<=r<256 | 29,882 | 37,622 | +3,870 | 137,969 | 629,718 | 1,141,589 | 1,043,316 |
| 256<=r<512 (held out) | 119,516 | 110,216 | -4,650 | 875,567 | 4,221,545 | 8,309,563 | 8,595,227 |

All `t=6,7,...` classes were also retained in the reconstruction. At the three bands, `A3` is respectively 42.44%, 35.00%, and 29.24% of total negative-class mass. Yet the final covariance signs are `-,+,-`.

The truncation through three faces is not even a nonnegative energy:

```
D + 2(A2-A3) =
  -138379, -953616, -6572440
```

on the three bands. The corresponding true energies are `7137,37622,110216`. Hence the omitted `t>=4` interactions are mathematically load-bearing, not a small correction.

Selected single shells also passed exact reconstruction:

| r | D_r | Delta_r | C_r | A3 |
|---:|---:|---:|---:|---:|
| 103 | 126 | 2 | -61 | 1,626 |
| 317 | 387 | 11 | -133 | 11,924 |
| 1027 | 1,252 | -20 | -426 | 89,249 |
| 4093 | 4,977 | -1 | -2,488 | 1,118,419 |
| 5561 | 6,756 | 58 | -1,696 | 1,873,270 |

These values show an enormous negative three-face cohort coexisting with either sign of the complete dyadic total and with very small shell increments.

**Classification:** finite assertion `complete dyadic C_shell<=0 because t=3 is the first cancelling face` is `REFUTED`. Broader all-scale shell gain remains `OPEN`.

## E. Global covariance and normalization audit

The independent prefix enumerator checked `M(N)^2=D(N)+2C(N)` exactly at every snapshot.

| N | M | D | C | 2C/D | pair average 2C/[D(D-1)] |
|---:|---:|---:|---:|---:|---:|
| 380 | -3 | 229 | -110 | -0.960699 | -0.00421359 |
| 100,003 | -47 | 60,797 | -29,294 | -0.963666 | -1.58508e-5 |
| 1,000,003 | 211 | 607,929 | -281,704 | -0.926766 | -1.52447e-6 |
| 30,924,720 | -2,544 | 18,799,988 | -6,164,026 | -0.655748 | -3.48802e-8 |

This is the denominator trap in exact arithmetic: `2C/D` may look near `-1`, while the actual average over physical squarefree pairs is tiny.

At `T=100003`, 50-decimal `Decimal` recomputation gave

```
C_0.25(T)  = -0.471634918373832727914883...
C_0.375(T) = -0.302954246146969754977850...
C_0.40(T)  = -0.281722444775050139660982...
```

and independently matched the C++ long-double values to at least 16 decimal places. At `T=30924720`, long-double diagnostics were `-0.473365748926512842`, `-0.303022156814101831`, and `-0.281758374672019552`. These finite apparently stable values do not prove boundedness, especially at or below the benchmark endpoint.

The native ancestry-root definition was reconstructed directly as

```
U_R = - sum_(q prime, q<=R^2-1)
        M(min(q-1,floor((R^2-1)/q))),
V_R = M(R^2-1)-1-U_R.
```

At `R=5561` this gives the contract witness exactly:

```
U=125204, V=-127749, U+V=-2545,
rho=2UV/(U^2+V^2)=-0.999797566706933392.
```

Also `(1+rho)(U^2+V^2)=2545^2=6477025` within long-double rounding. A naive largest-prime split instead gives `(-126918,+124373)`: same total, different coordinates and rho. This independently confirms that largest-prime smooth/high membership is not the native root/smooth Gram carrier and must not be substituted.

## F. Methods and independent checks

- C++17 linear sieve through `30,924,720`; exact integer Möbius values, factor depths, gcds, all unordered squarefree shell pairs, native root transform, and prefix covariance.
- Build: `g++ -O3 -std=c++17 -Wall -Wextra -Werror`.
- Main pair census: 3.56 s wall time in this container. Global/root/weighted census: 6.53-7.6 s.
- Python used a distinct prime-multiple Möbius sieve and direct pair loops for roots `7,13,64,103,127`; every histogram and exact identity agreed.
- Python `Decimal` at precision 50 independently recomputed all three weighted sums through `100003`.
- No random seed, floating decision boundary, or approximate primality test was used. Floating arithmetic appears only in reported `C_eps` and rho diagnostics; all signs and identities were integer-certified.

## G. Proof impact and hypothesis portfolio

1. **Rejected:** two-prime within-orbit cancellation (Wheel paper theorem) and three-prime-first-face sign control (this finite falsifier).
2. **Highest-ranked surviving mechanism:** complete unshared-depth parity balance
   `sum_t (-1)^t A_t(r)`, with a theorem that retains all `t`, cross-base pairs, and shell boundaries before norms.
3. **Precise next conjecture (`CONJECTURE`):** for each dyadic H, the large `t=3` cohort is compensated at leading scale by the complete `t>=4` tail; any proof of a `H^(5/2-kappa+eta)` shell-energy bound must establish a quantitative alternating-depth relation, not a bound on `A3` alone. A useful falsifiable formulation is to seek a signed recurrence for `A_t(H)=sum_(H<=r<2H)A_t(r)` whose truncation error after a growing depth cutoff is `O(H^(5/2-kappa+eta))`.
4. The experiment supplies no candidate `kappa`; it narrows the structural target and prevents a false local mechanism from consuming another cycle.

## H. Continuation checkpoint

Do not rerun the 317/1027 tensor or these three bands unchanged. Next run should derive or falsify a recurrence between adjacent unshared-depth populations `A_t(H)` and `A_(t+1)(H)`, using a held-out band `512<=r<1024` and preserving exact pair multiplicities. A successful theorem must quantify the full alternating tail and then show its strict implication to the shell `5/2-kappa` input.

No RH proof claim.


---

## Continuation update - 2026-10-18T13:16-04:00

**Status:** COMPLETED  
**Claim:** `20261018-census-2`  
**Evidence:** `FINITE_COMPUTATION / HELD-OUT FALSIFICATION / MECHANISM RESTRICTION`; `NO_NEW_QUANTITATIVE_RESULT`

### I. Refreshed authority and new assignment

Authority was refreshed after the morning report. Live `main` is
`5ae5a524ca447d1936e351bbbe4b134c068a1a13`, the merge of PR #979; no PR is
open. Governing blobs are `AGENTS.md`
`4c66a1d462df98c84deebf0069ad11f904039858`,
`CURRENT_PROOF_CONTRACT.md`
`2fa9931dcdc1fc8a816aefb8aa348db12ee9a384`, the PNT-first contract
`e8acbeff24942d1f8ee0079f715afff2ddda2c33`, and the two-scale attack plan
`0606d764ffebb4639cc0abb52ccbef30546b7764`.

The exact source declarations inspected at this head are
`TwoABScaleTransfer.lean` blob
`fae76878063583322a48a329810cc1cc7b037ee7`,
`SquareRootMatchedTransport.lean`
`e9ab3bff6b8819182c39721f92859679d250002e`,
`SquareRootSmoothRenewalInstantiation.lean`
`9a63c8c2f9e42a64c0010721a78101c1f56858b1`, and
`SquareBlockSmoothTransportGram.lean`
`09f5e0108eb254a2f20fa2fd694d69cb455b2857`. They prove exact
smooth-minus-transport and PNT decompositions, not a signed estimate.

All named October 18 reports were consumed at their current blobs: Coordinator
`c9337407...`, Owner `4655c437...`, Analytic `f7b98195...`, Wheel
`62da4947...`, Census `08d80d6...`, Referee `096513f9...`, Lean
`0ed62011...`. The complete October 17 set remains
`YESTERDAY=CARRY_FORWARD`. External inbox blob
`038018145c0fddb2f6306c0712373adf9cd1ea52` was re-read.

Analytic claim `20261018-analytic-1` proves the proposed same-shell outer-prime
tile is rank one. Its requested discriminator is therefore the cross-shell
cofactor response itself, not a nonexistent mean-zero outer-prime mode.

### J. Preregistered question

For
\[
e_r(c)=\mu(c)P_r(c)-a_r^{\rm inc}(c),\qquad
G_{r,C}=\sum_{C\le c<2C,\ c\le r}e_r(c),
\]
does the Li shell increment explain the sign and scale of
\(\sum Q_rG_{r,C}\), or do the exact prime discrepancy and omitted cofactor
complement remain load-bearing?

The discovery block was \(H=2048\); the frozen held-out block was
\(4096\le r<8192\). Bands were fixed before the held-out run:
\(c=1,2,3\), \([8,16)\), \([64,128)\), \([512,1024)\), and
\([4096,8192)\). The union and its complete complement were both retained.
Failure criterion: opposite signs for the exact and Li terms, or a complement
carrying a comparable share of the exact mixed term.

### K. Exact held-out results at \(H=4096\)

The sieve covered every integer through \(2^{26}-1=67,108,863\), with
3,957,809 primes. For every one of the 4,096 shells,
\[
\sum_{c\le r}e_r(c)=-\delta_r
\]
held exactly. The block totals were
\(\sum\delta_r=118\), \(\mathcal E(H)=30,291,950\), and therefore the complete
response had \(\sum G_{\rm all}=-118\).

| response | \(\sum G\) | \(V_{H,2H}(G)\) | exact \(\sum Q_rG_r\) | Li part | discrepancy part |
|---|---:|---:|---:|---:|---:|
| all cofactors | -118 | 391,878 | 2,796,235 | -149,681.6334 | 2,945,916.6334 |
| \(c=1,2,3\) compensated | -21,496 | 179,898 | -14,721,285 | -15,198,254.6520 | 476,969.6520 |
| \(c\ge4\) complement | 21,378 | 431,456 | 17,517,520 | 15,048,573.0186 | 2,468,946.9814 |
| prescribed-band union | -1,250 | 342,302 | 404,921 | -856,465.3054 | 1,261,386.3054 |
| prescribed complement | 1,132 | 395,926 | 2,391,314 | 706,783.6720 | 1,684,530.3280 |

Thus the complete exact mixed term is positive while its Li component is
negative. The prime-discrepancy component is 1.0535 times the exact total and
reverses the sign. The complement of the prescribed bands supplies 85.52% of
the exact total. This held-out finite hypothesis, “Li main term plus the named
bands predicts the complete response,” is **REFUTED**. This does not refute a
future all-band Type I/II theorem.

The independent anchor check gives
\[
(\sum P_r(1),\sum P_r(2),\sum P_r(3))
=(2,879,938,1,499,526,1,024,271),
\]
hence \(\sum A_r^{\rm anchor}=-356,141\) and
\(A^{\rm anchor}\log H/H^2=-0.176566693805551159\). At \(H=2048\), the same
implementation exactly reproduced Coordinator's published
\((781,924,408,552,279,728,-93,644)\) row.

Individual prescribed bands were also sign-incoherent. Their exact
\(\sum QG\) values were \(38,849,594\), \(-30,321,027\),
\(-23,249,852\), \(15,665,712\), \(-408,308\), \(-872,017\), and
\(740,819\), in the order declared above. No local band has been promoted to a
universal sign law.

### L. Algorithms, independent checks and numerical control

The primary C++17 code used an exact linear Möbius/largest-prime-factor sieve,
binary-search prime counts at the literal endpoints
\[
P_r(c)=\pi(\lfloor((r+1)^2-1)/c\rfloor)-\pi(\lfloor r^2/c\rfloor),
\]
direct shell multiples for \(B_r(d)\), and the literal finite inversion for
\(a_r^{\rm inc}(c)\). Build:
`g++ -O3 -std=c++17 -Wall -Wextra -Werror` with GCC 13.3.0.
Source SHA-256:
`a88cedb0c2fbcd8ce471210cb389a6741c8944dbe372c5dc18b0d1ede7e4ae91`.

A structurally separate Python 3.12.14 checker enumerated divisors of each
smooth squarefree shell integer, rather than scanning shell multiples. At
\(H=32\), both implementations gave
\(\sum\delta=-15\), \(\sum G_{\rm all}=15\), zero identity failures, and
\(\sum QG_{\rm all}=553\). Checker SHA-256:
`6d51288788e2d9ffae198e8eeb29b00ade1d1b4ae7a399496edafa609deb111a`.

Only the Li column is approximate: long-double 128-panel composite Simpson
integration of \(dt/\log t\) on each shell. Repeating with 64 panels left every
displayed value unchanged through at least 15 significant decimal digits.
All signs, counts, variations, complements, Möbius identities, and exact mixed
terms are integer-certified.

### M. Proof impact and continuation checkpoint

The experiment confirms Analytic's rank-one diagnosis and adds a finite
mechanism restriction: neither the smooth Li increment nor a sparse menu of
cofactor scales can replace the complete arithmetic response. The
prime-location discrepancy is not a perturbative remainder on this block, and
the \(c\ge4\) complement is essential to the sign.

The first useful new theorem must therefore control a complete cross-shell
cofactor/divisor transform with the Li term, exact prime discrepancy, \(c=1\),
and every complementary band restored. A promising next discriminator is to
decompose the discrepancy contribution by arithmetic cofactor class
(squarefree sign, least/greatest prime factor, and endpoint birth/death) on a
development block, freeze one deterministic class statement, and test it at
\(H=8192\). Do not rerun the full \(H=4096\) table unchanged.

No \(\eta>0\), shell-energy exponent improvement, canonical VF estimate, or RH
proof is claimed.

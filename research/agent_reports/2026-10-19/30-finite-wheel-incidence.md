# RH_Lean agent daily report - 2026-10-19 / RH | Finite Wheel & Incidence

**Status:** COMPLETED
**Run ID:** 2026-10-19T00:09:01-04:00, scheduled invocation
**Canonical objective:** `VFCanonicalSquareVonKochStatement` remains OPEN
**Result classes:** `PAPER_PROOF` (exact moving-window lag/gcd kernel and uniform large-shared-gcd tail), `FINITE_COMPUTATION`, `PARTIAL_QUANTITATIVE_REDUCTION`, `NO_NEW_GLOBAL_BOUND`

## A. Bottom line

This run followed the latest Coordinator assignment after merged PR #981: expand the localized moving-window energy by genuine additive shifts, squarefree gates and unshared-prime parity, then identify a multiplicative subkernel with a proved small complement.

The new exact restriction is that every nonzero shifted pair has a unique shared ancestry

```text
g = gcd(n,n+h) = gcd(n,h),
n = g*a,  n+h = g*b,  gcd(a,b)=gcd(g,a*b)=1,
mu(n)mu(n+h) = mu(a)mu(b).
```

Thus the common factor `g` divides the short lag `h` and disappears from the sign; all sign is carried by the two coprime unshared quotients. This sign formula was already anticipated in the factor-depth brief. The new work is its exact insertion into the translated-window overlap kernel and a uniform absolute budget for the entire large-`g` off-diagonal.

For `1 <= T <= H/2` and integer `2 <= G <= H`, the diagonal plus every shifted pair with shared gcd at least `G` is

```text
O((2T+1) * (H^3/G + H^2 log H)).
```

At the localized Stage-A scaling

```text
T = floor(H^(3/4-eta/2)),
G = ceil(H^(1/2+eta)),     0 < eta < 1/2,
```

this is `O_eta(H^(13/4-3eta/2) + H^(11/4-eta/2) log H)`, hence it fits the exact moving-window target `H^(13/4-3eta/2+epsilon)`. The diagonal fits as well. The first genuinely unpaid piece is now the low-shared-gcd signed correlation `gcd(n,n+h)<G`, with every translated boundary retained.

This is a real partial quantitative reduction, but it proves no estimate for that low-gcd piece and therefore no shell-energy exponent, Mertens gain, canonical VF bound or RH.

## B. Authority, continuity, and live state

Final authority at research intake:

- `main@28a270195167530615c2b182f8c9ffd86855b1f6`, merge of PR #981.
- `AGENTS.md` blob `4c66a1d462df98c84deebf0069ad11f904039858`.
- `CURRENT_PROOF_CONTRACT.md` blob `2fa9931dcdc1fc8a816aefb8aa348db12ee9a384`.
- PNT-first contract blob `e8acbeff24942d1f8ee0079f715afff2ddda2c33`.
- Two-scale attack plan blob `0606d764ffebb4639cc0abb52ccbef30546b7764`.
- Dynamic protocol blob `bd1189617c069565a881c2a5c5dbd9a138bc48c1`.
- Factor-depth brief blob `2ba74e64be864f31e5696318fe3423f229e14e4c`.
- Merged localized moving-window note blob `c17798891f475fd78a2f51cbddd5d585f81d3eb2`.
- Existing generic overlap-kernel Lean source blob `22cab57fb65110494d47c97c9e8777b371e04a6a`.
- External inbox blob `038018145c0fddb2f6306c0712373adf9cd1ea52`; `EXT-20261018-PNT-1..3` retain exact-identity, finite-falsifier and source-no-go scopes.

The `2026-10-19` report directory was absent at intake, so all same-day upstream stages are `TODAY=PENDING`. The complete `2026-10-18` set was read as `YESTERDAY=CARRY_FORWARD`: Coordinator `4510607938e185534ba6074f58b2c3bb51a0f368`, Owner `84fdf8ec488848eb033e7ac3d882ec43051d5b88`, Analytic `fd182e0de5e703aa62738a426b80db483dfc967c`, Wheel-incidence `1f2e83a07d2d277f1137fd0239109f3abea5cbee`, earlier Wheel `62da494755501409879e894779d026aed70835f8`, Census `701b74c281d01f6727669808566d76b1e8758b26`, Referee `c0360eaa56c34198f21f9387113fd565a19b542f`, and Lean `bff111a9448b17061f4dc2be760ea8422245a3f6`.

PR #981 is merged and its frozen data are finite evidence only. Draft PR #982 appeared after main was read and was moving during this run. At the last pre-publication inspection it was open/draft at head `dd182118350f0cfcf1532e71da34ab9d6cd6777f`; Documentation checks had succeeded, most workflows were pending, and two were in progress. Its exact trapezoid/long-lag files are not current-main authority and its stated complete smoothed-energy input remains open. No PR or CI mutation was performed here.

## C. Claim `20261019-wheel-1`: exact translated lag and ancestry kernel

For integers `H>=2`, `1<=T<=H/2`, `H<=r<2H`, set

```text
S_r(t) = sum_(j=1..2r) mu(r^2+t+j),   |t|<=T,
W(H;T) = sum_r sum_(|t|<=T) S_r(t)^2.
```

For `h>=0` and `x` integral define

```text
kappa_(r,T,h)(x)
 = max(0, min(T,x-1) - max(-T,x+h-2r) + 1).
```

This is exactly the number of translated windows containing both `n=r^2+x` and `n+h`. Finite Fubini gives

```text
W(H;T)
 = D(H;T)
 + 2 * sum_(H<=r<2H) sum_(1<=h<2r)
       sum_(1-T<=x<=2r+T-h)
       kappa_(r,T,h)(x) mu(r^2+x)mu(r^2+x+h),              (LK)

D(H;T)
 = sum_r sum_(1-T<=x<=2r+T)
       kappa_(r,T,0)(x) mu(r^2+x)^2.
```

No pair with `h>=2r` can occur in one length-`2r` window. The support interval has length `L_r=2r+2T`, and every coefficient is between zero and `2T+1`. Negative translations import the preceding square block and positive translations import the following block exactly as Owner claim `20261018-owner-4` requires; no occurrence is silently treated as a new physical #915 cell.

If one term in (LK) is nonzero, put

```text
g=gcd(n,n+h)=gcd(n,h),   a=n/g,   b=(n+h)/g.
```

When both Mobius values are nonzero, `g,a,b` are squarefree and pairwise coprime, `b-a=h/g`, and

```text
mu(n)mu(n+h)=mu(g)^2 mu(a)mu(b)=mu(a)mu(b)
              = (-1)^(omega(a)+omega(b)).                 (UP)
```

Conversely these conditions reconstruct the pair uniquely. Thus common ancestry is geometrically constrained by `g|h`, while the sign depends only on the unshared coprime quotients. This does not assign a favorable sign: the known positive and negative parity sectors remain.

**Classification:** `PAPER_PROOF / EXACT SOURCE-PRESERVING REPRESENTATION`. The generic overlap Gram exists on main; the explicit lag formula and its use below are new relative to the searched moving-window sources.

## D. Claim `20261019-wheel-2`: uniform large-shared-gcd tail

Let `O_geG(H;T)` be the off-diagonal part of (LK) restricted to pairs with `gcd(n,n+h)>=G`, with all signs retained. Then

```text
|O_geG(H;T)|
 <= (2T+1) H *
    [25 H^2/(G-1) + H(14+10 log(4H))].                    (HG)
```

Also

```text
0 <= D(H;T) <= 5(2T+1)H^2.                                (DG)
```

### Proof

For fixed `r`, every contributing pair lies in an interval of length
`L_r=2r+2T<=5H` and has difference below `2r`. If its exact gcd is `g`, then `g` divides the nonzero difference, hence `G<=g<2r`. The number of unordered pairs in the interval with exact gcd `g` is at most the number of pairs of multiples of `g`, namely

```text
binom(M_(r,g),2),   M_(r,g)<=L_r/g+1.
```

Summing this upper bound over `G<=g<2r`, using

```text
sum_(g>=G) 1/g^2 <= 1/(G-1),
sum_(G<=g<2r) 1/g <= 1+log(4H),
#{g:G<=g<2r} <= 4H,
```

and multiplying by the overlap bound `2T+1` and by the factor two in (LK) proves (HG). The diagonal has at most `L_r` supported sites per shell, each with coefficient at most `2T+1`, proving (DG). The estimate is uniform in every Mobius sign and does not use PNT, a correlation hypothesis or the target energy.

For the localized choice

```text
T=floor(H^(3/4-eta/2)),
G=ceil(H^(1/2+eta)),     0<eta<1/2,
```

(HG) and (DG) are within `O_(eta,epsilon)(H^(13/4-3eta/2+epsilon))`. Therefore a bound of that size for the remaining low-gcd signed term is sufficient for the complete localized `W(H;T)` bound, with the diagonal and high-gcd complement already paid. Combined with the accepted Lipschitz envelope, this would imply the Stage-A shell-energy gain, but that low-gcd theorem is still OPEN.

**Classification:** `PAPER_PROOF / NEW UNIFORM ABSOLUTE TAIL / PARTIAL QUANTITATIVE REDUCTION`. It is not a global signed estimate.

## E. Finite wheel gate and exact checks

For any finite prime set `P`, put `Q=product_(p in P) p^2`. The number of residue classes `x mod Q` for which neither `x` nor `x+h` is divisible by any `p^2` is exactly

```text
product_(p in P, p^2|h)    (p^2-1)
* product_(p in P, p^2 not|h) (p^2-2).                    (CRT)
```

For each prime, the two forbidden residues `0` and `-h mod p^2` coincide exactly when `p^2|h`; CRT multiplies the local counts. This is the exact squarefree-support wheel for each lag. It restricts occupancy but does not control the unshared parity sign in (UP), so it supplies no cancellation by itself.

An independent exact linear Mobius sieve checked (LK) and the high/low gcd partition at `(H,T,G)=(8,3,4),(16,5,8),(32,8,16),(64,22,32)`. The reconstructed `W` values were respectively `1355,5004,31010,324610`; the last matches merged PR #981's frozen value. At `H=64`,

```text
D=334410,  offdiag=-9800,
high-gcd signed contribution=19104,
low-gcd signed contribution=-28904.
```

The sign of the high-gcd sector changed across the four checks (`-,-,+,+`), confirming that (HG) must be an absolute budget rather than a guessed negative-covariance law. Exact checks validate endpoints and implementation; the all-scale proof is the counting argument above.

## F. Novelty, no-circularity, and source scope

Repository search found the pre-existing statement that shared gcd factors drop out of a squarefree pair sign, and the generic overlap Gram. It did not find the explicit translated lag kernel together with the uniform large-shared-gcd tail (HG) or its localized exponent budget. Novelty is therefore the paid complement and reduction, not the basic multiplicativity identity.

The reduction is noncircular: (HG) bounds a proper, explicitly defined subset of pairs by divisor geometry alone. It assumes neither `W`, shell energy, Mertens growth, a PNT error, nor the desired low-gcd estimate. The low-gcd complement can still contain the entire difficult signed mode, so no exponent credit is claimed until it is bounded.

This carrier is genuine unweighted Mobius moving-window energy. It is not the original masked/clipped #915 native source. Owner's overlap multiplicities and raw-transfer cone remain active vetoes against a direct VF transfer.

## G. Strategy decision and handoffs

- **SHIFT-L2 / localized windows:** CONTINUE. Replace the vague all-pair task by the exact low-gcd kernel from (LK), after subtracting the proved diagonal and `g>=G` budgets.
- **Large shared ancestry:** PAID at the required localized exponent for every fixed `0<eta<1/2`; do not spend another census enlarging this tail.
- **Low shared ancestry:** OPEN and highest-value multiplicative question. Any estimate must retain the CRT squarefree gates, exact overlap weight, both translated square boundaries, and all unshared-parity classes. A fixed-depth or favorable-sign truncation remains invalid.
- **Cofactor profile:** RETAIN as a comparator. The earlier `d=1` obstruction concerns divisor-profile recombination; (HG) instead removes a proper high-gcd subset of the translated pair kernel and does not delete the low-gcd constant mode.
- **Direct VF:** SEPARATE. No occurrence admission, native weight or historical payment follows from (LK).
- **Analytic:** seek a uniform upper bound for the complete low-gcd signed sum, perhaps by a dispersion theorem in the coprime variables `a,b` with `g<G`; state conductor and boundary costs and restore the CRT support.
- **Census:** if testing this reduction, report low/high gcd signed and absolute overlap mass at the frozen localized radii. The small checks already show no stable sign.
- **Referee:** audit the interval length, `g<2r` consequence, exact-gcd overcount, constants, and the `eta<1/2` exponent calculation.
- **Lean:** after independent acceptance and duplicate search, (LK) and (HG) are exact formalization candidates. Attach no low-gcd estimate as an assumption advertised as arithmetic progress.

## H. Resume capsule

- Authority: `main@28a270195167530615c2b182f8c9ffd86855b1f6`; PR #981 merged.
- New claims: `20261019-wheel-1` exact translated lag/unshared-parity kernel; `20261019-wheel-2` uniform large-shared-gcd tail.
- Quantitative consequence: at localized `T=H^(3/4-eta/2)`, `g>=H^(1/2+eta)` plus the diagonal is inside the required moving-window budget for `0<eta<1/2`.
- First missing lemma: a genuine signed estimate for the full low-gcd complement with exact overlap, squarefree gates, boundaries and unshared parity.
- Live draft #982 is non-authoritative and was CI-pending at the observed head; refresh before using it.
- No shell-energy gain, Mertens exponent improvement, finite A/C, original #915 payment, canonical VF bound or RH proof.

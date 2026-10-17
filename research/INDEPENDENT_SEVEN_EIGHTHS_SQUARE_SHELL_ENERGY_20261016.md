# Independent 7/8 programme: square-shell signed energy

**Date:** 2026-10-16. **Status:** exact finite identities (paper and already-existing Lean), independently reproduced finite census, **NEW CONDITIONAL SUFFICIENT GATE**, **NO NEW UNCONDITIONAL EXPONENT BOUND**. Initial authority: `main@b9105f19fbbf25742a6909a6e8c995e6a9ddeddb`. No OpenAI seven-eighths theorem is used anywhere in the *proposed arithmetic proof*; the established external theorem is a benchmark, not an input.

This note redirects an independent attack away from the tautological original raw `A_R+B_R=L_R` mismatch. The smallest proposed **new** quantitative input is a **one-sided dyadic, signed, full-shell Mobius second-moment estimate**. It is stronger than the desired 7/8 zero-free conclusion, but weaker by 3/2 powers of the root than the pre-existing RH-scale increment-energy premise. The implication is elementary; the input remains open.

## 1. Exact existing physical carrier

For integers `r >= 2`, put `I_r = { n in N : r^2 < n < (r+1)^2 }` and

```text
delta_r = sum_(n in I_r) mu(n)
        = M((r+1)^2) - M(r^2).
E(K) = sum_(2 <= r < K) delta_r^2.
```

The equality includes no square correction because `mu(r^2)=0` for every `r>=2`. Each integer atom occurs in exactly one shell, and squareful sites have zero Mobius weight. The existing `canonicalSquareBlock r = [r^2,(r+1)^2)` is equivalent at `r>=2` because the left square also has zero weight. **Do not introduce a second, competing canonical block definition.**

Existing native declarations at baseline:
- `RHLean/Proof/SquareBlockSmoothTransportGram.lean` (blob `09f5e0108eb254a2f20fa2fd694d69cb455b2857`): `squareBlockSmoothIncrement`, `squareBlockTransportIncrement`, and `canonicalTotalIncrement_eq_smooth_sub_transport`.
- `RHLean/Proof/SquareBlockIncrementEnergy.lean` (blob `5a90b8faf4fbc07dfd352362be1e566ca8b83920`): a *much stronger* **assumed** `sum delta_r^2 = O_epsilon(K^(1+epsilon))` with a conditional RH consumer; the premise is not established.
- `RHLean/Analysis/BlockCovarianceDecomposition.lean` (blob `42dd692634a0c44855803f8bc33df4d5f6e4e413`): the compiled signed within-block/cross-block expansions.
- `research/MERTENS_CONVERSE_IDENTIFICATION.lean` (blob `c15bdfcb0b050b26e3f0ea54775d8fd61d8af8bb`): genuine-Mobius growth boundary equals the rightmost zeta-zero boundary.

For each shell, partition by greatest prime factor:

```text
s_r = sum_(n in I_r, P+(n) <= r) mu(n)
t_r = -sum_(n in I_r, P+(n) > r) mu(n)
delta_r = s_r - t_r.
```

If `q=P+(n)>r` then `q>=r+1` and `n < (r+1)^2 <= q^2`, so `n=q*a` with `a<q`, hence `mu(q*a)=-mu(a)`. No shell contains a square of a prime `q>r`. It follows, with `M(0)=0`,

```text
t_r = sum_(r < q < (r+1)^2, q prime)
          [M(floor(((r+1)^2-1)/q)) - M(floor(r^2/q))].
```

This is a complete, once-only **signed Euler extension**; it includes even cofactors, odd cofactors, zero Mobius sites, all owner classes and both strict shell walls. The transport cofactor intervals are physical, not arbitrary statistical samples. This is a different carrier from the original VF raw prime-minus-midpoint ledger and from the clipped returned cells of #915; bridge claims must be explicit.

The corresponding literal squared source is

```text
delta_r^2 = s_r^2 + t_r^2 - 2*s_r*t_r.
E(K) = sum_r s_r^2 + sum_r t_r^2 - 2*sum_r s_r*t_r.
```

**Do not** assume `s_r*t_r >= 0`: some real shells have opposite-signed components and therefore amplify instead of cancel.

## 2. New independent arithmetic gate (OPEN)

For every epsilon>0, seek a constant `C_epsilon` such that for **every dyadic integer H >= 2**,

```text
(SB-7/8)
sum_(H <= r < 2*H) |s_r - t_r|^2
   = sum_(H <= r < 2*H) delta_r^2
   <= C_epsilon * H^(5/2 + epsilon).
```

All powers refer to the **root** coordinate H. No imported seven-eighths estimate, Mertens `x^(7/8+epsilon)` growth assumption, assumed zero-free theorem, modeled independence or stochastic sign law is permitted when proving (SB-7/8). A proposed proof must identify a new arithmetic reason for the upper bound, such as a rigorously estimated additive correlation or a complete owner/factor-parity dispersion identity. `E(K)` being nonnegative is not such a reason.

### Elementary implication (PAPER PROOF, conditional on the open input)

Dyadic decomposition of `[2,K)` and (SB-7/8) imply

```text
E(K) <= C'_epsilon K^(5/2+epsilon).
```

Cauchy-Schwarz, retaining every square shell, gives

```text
|M(K^2)|
 <= |M(4)| + |sum_(2<=r<K)delta_r|
 <= 1 + sqrt(K-2)*sqrt(E(K))
 = O_epsilon(K^(7/4+epsilon/2)).
```

For `K^2 <= x < (K+1)^2`, the unresolved final partial shell contributes at most `2K+1` in absolute value because `|mu(n)|<=1`. Thus

```text
M(x) = O_eta(x^(7/8+eta))    for every eta>0.
```

The already-compiled `MERTENS_CONVERSE_IDENTIFICATION` then yields `lambda_M <= 7/8` and `zeta(s) != 0` on `Re(s)>7/8`. The standard explicit-formula prime-counting transfer, followed by the separately compiled `VF_can - Li_2=O(1)` all-real quadrature, gives the original canonical defect `D_can(R)=O(R^(7/4) log R)`; an **end-to-end Lean** explicit-formula/VF transfer is still missing. This chain would be an **independent explanation** of the seven-eighths exponent *if and only if the open dyadic arithmetic estimate is independently established*.

More generally, a dyadic shell energy exponent `5/2-delta` (for a fixed `0<delta<3/2`, with arbitrary epsilon loss) yields `lambda_M <= 7/8-delta/4`. The remaining all-real within-shell error `O(sqrt(x))` does not spoil this range. The earlier `O(K^(1+epsilon))` RH-level input is significantly stronger than (SB-7/8), not a prerequisite.

**Strength audit:** (SB-7/8) is a sufficient, *stronger-than-7/8* criterion, not an equivalence. A sequence with alternating full-size signed square-shell increments may have small cumulative sums while its square-shell energy is order `K^3`; hence endpoint information alone cannot pay this energy bound. A proof must exploit genuine Mobius arithmetic and quantify all dyadic shells.

## 3. Exact zero-target pair/covariance form

Expanding every block *before* applying an absolute value,

```text
delta_r^2
 = sum_(n in I_r) mu(n)^2
   + 2 * sum_(m<n, m,n in I_r) mu(m)*mu(n).
```

Let `D(H)` be the total diagonal squarefree population on `H<=r<2H`, and `C(H)` the second signed term, including **all** off-diagonal physical pairs and all common-prime/nonshared-prime possibilities. Then

```text
E(H,2H) = D(H) + C(H),      D(H) <= O(H^2).
```

The exact new payable task can therefore be posed as the **one-sided**, all-off-diagonal covariance estimate

```text
C(H) <= C_epsilon H^(5/2+epsilon).
```

This is logically sufficient because the diagonal is only `O(H^2)`; it is not a new theorem, and a positive/negative pair count by itself does not prove it. If squarefree `m,n` share `d=gcd(m,n)`, then `mu(m)mu(n)=mu(m/d)mu(n/d)`: the common prime factors **drop out of the pair's sign**. Shared ancestry alone does not supply negative covariance. The parity of the *unshared* factors is a concrete conditioning candidate.

### Exact shifted-Mobius interpretation (PAPER IDENTITY; a more specific input)

On the open physical shell `I_r`, the integer sites are exactly `r^2+1, ..., r^2+2r`. Thus the **complete** signed off-diagonal covariance of the dyadic shell family is the *arithmetic shifted-correlation sum*

```text
C(H)
 = 2 * sum_(r=H..2H-1) sum_(h=1..2r-1)
       sum_(m=r^2+1..r^2+2r-h) mu(m)*mu(m+h).
```

It has `sum_(r=H..2H-1) r*(2r-1) = Theta(H^3)` unordered physical pair occurrences. The available purely termwise bound is therefore `|C(H)|=O(H^3)`. The exact diagonal is `sum_(r,n in I_r)mu(n)^2 <= sum_(r=H..2H-1)2r=3H^2-H`. This reveals the **required nontrivial source of saving**: cancellation among the genuine, square-centered *shifted two-point Mobius products* after all shifts `h<2r` and all shells `r in [H,2H)` are recombined. For (SB-7/8), an upper (not absolute two-sided) signed estimate `C(H)=O_upper(H^(5/2+epsilon))` suffices. Because `C(H)>=-D(H)`, a bound `|C(H)|<=...` would be equivalent at the relevant scale, but there is no assumed sign rule for individual `h`, `r` or cofactor families.

This gives a concrete **additive–multiplicative junction** for an independent proof: Euler greatest-prime ownership provides the exact multiplicative decomposition of each site, while its constrained *additive* coincidence at shifts `m -> m+h` is the missing arithmetic estimate. Factor `d=gcd(m,m+h)` must divide `h`; for squarefree `m,m+h`, `mu(m)mu(m+h)=mu(m/d)mu((m+h)/d)` after cancelling their common squarefree factors. Conditioning on the *unshared* prime factors, not merely shared ancestry, is the right object to investigate. This is not an invocation of an unproved Chowla conjecture: a proposed proof must supply its own **uniform averaged** estimate for precisely this square-shell triangular weight and its `Theta(H^3)` physical pairs. Random signs or an almost-all-x theorem with no transfer to squares do not meet this test.

This is a **new shell-energy carrier** for the zero-target statistic, not an unproved assertion that it is exactly the original #915 normalized first-bad covariance. Consumer is the genuine-Mobius growth boundary, with an explicitly separate bridge to the canonical VF objective.

## 4. Independently recomputed exact census

Reproducer: `python3 scripts/mertens_square_shell_energy_probe.py --root 3162`. It builds genuine `mu`, largest-prime factors and the shell populations by a linear sieve through `3162^2=9,998,244`; separately checks the upper-prime-cofactor interval formula on specified shell witnesses. **All energy and diagonal numbers are integer exact**; only the displayed ratios are floating point. No OpenAI bound or modeled prime/Li baseline is used.

| Dyadic H | Shell energy E(H,2H) | Squarefree diagonal D(H) | Signed off-diagonal C(H) | E/H^(5/2) |
|---:|---:|---:|---:|---:|
| 16 | 451 | 467 | -16 | 0.440430 |
| 32 | 1,789 | 1,867 | -78 | 0.308841 |
| 64 | 7,137 | 7,471 | -334 | 0.217804 |
| 128 | 37,622 | 29,882 | +7,740 | 0.202963 |
| 256 | 110,216 | 119,516 | -9,300 | 0.105110 |
| 512 | 486,935 | 478,101 | +8,834 | 0.082091 |
| 1,024 | 1,723,387 | 1,912,373 | -188,986 | 0.051361 |
| 1,530 (non-dyadic control) | 3,999,544 | 4,269,310 | -269,766 | 0.043680 |

Witnesses: `r=14` has `(s_r,t_r,delta_r)=(1,-8,9)`, `r=137` has `(2,-42,44)`, and `r=1110` has `(15,-102,117)`. These **falsify any universal nonpositive signed cross term**. At `r=2000`, `(-23,-26,3)` instead shows marked cancellation. The largest tested `|delta_r|/r^(3/4)` is `1.24350198` at `r=14` for `2<=r<3162`.

Finite declines in `E/H^(5/2)` cannot establish a uniform all-H bound. Existing short-interval Mobius results do not automatically apply with a polynomial saving to **all of these exact square-root-length shells**; any such literature transfer needs a checked uniformity argument, rather than an almost-all-x assumption.

## 5. Exact division of outstanding work

1. **Analytic / independent power saving:** produce a valid unconditional dyadic upper bound on the *entire* signed off-diagonal pair sum. Try a Ramaré/factor-extraction plus short-interval bilinear dispersion approach, but check every remainder and whether its hypothesis covers the square-root-length family. Even a strictly smaller exponent than the trivial `H^3` is interesting; `5/2` is the seven-eighths gate.
2. **Owner / Wheel:** expand the physical pair sum using the already-proved smooth/transport split, preserving `s^2+t^2-2st`, all squareful zeros, all even/odd cofactors and the strict square walls. A signed common-prime vs unshared-prime decomposition is meaningful only if it yields a provable aggregate upper bound.
3. **Census:** independently reproduce the integer table from a different implementation and predeclare held-out dyadic ranges or counterexamples before enlarging the scan. Track `E/H^(5/2)`, `E/H^3`, diagonal and signed cross separately. Do not infer an asymptotic exponent from a finite regression.
4. **Adversarial referee:** test whether the proposed covariance input merely restates (SB-7/8), whether a claimed factorization changes the carrier, whether square-root-length uniformity is missing, and whether the real signed matrix has unresolved positive modes.
5. **Lean verification:** reuse `canonicalTotalIncrement_eq_smooth_sub_transport` and the existing energy algebra; formalize the **conditional** 5/2-exponent consumer only when useful and label its arithmetic hypothesis openly. No status upgrade on RH, lambda_M or the canonical defect until the genuinely new dyadic arithmetic theorem is proved without importing OAI 7/8.

**Decision: CONTINUE as a distinct candidate with a measurable new signed arithmetic gate.** This does not retire #919's genuine Hecke moment route, the complete signed K1/K2/K3 hyperbola route, or Nyman's Hilbert route. It avoids the already-audited tautology `A_R+B_R=L_R` and gives a direct, independently testable, square-clock route to the exact requested seven-eighths benchmark.

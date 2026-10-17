# Independent 7/8 Hecke cutoffs: from seven layers to an exact two-layer root-wall identity

**Date:** 2026-10-16. **Authority:** `main@b9105f19fbbf25742a6909a6e8c995e6a9ddeddb`. **Status:** `PAPER_PROOF` (finite identities and elementary large-square bound), `FINITE_COMPUTATION` (independent exact linear sieve, one million and ten million), `OPEN` (uniform signed core cancellation). **No external OpenAI 7/8 theorem, Mertens power bound, or RH hypothesis is used in the construction.** This is a research note, not a new Lean theorem or an independent fixed-power saving.

The earlier [independent dyadic square-shell energy candidate](INDEPENDENT_SEVEN_EIGHTHS_SQUARE_SHELL_ENERGY_20261016.md) is a different, stronger sufficient bound. The Hecke cutoff core below is **target-equivalent** once the paid tail is removed; this note does not promote that tautology into a quantitative theorem.

## 1. Original #919 coefficients, with actual local Euler factors

Use precisely the already compiled `VF_MID_919_OAI_PRINCIPAL_COEFFICIENT_MAP.lean` objects:

```text
chi(n) = chi_{-3}(n), a = mu * (chi *pointwise* mu),
a6(n) = 1_(gcd(n,6)=1) a(n),
K(t) = C_chi(t)-C_chi(floor(t/3))-C_chi(floor(t/4))
       +C_chi(floor(t/12)),
C_chi(t) = 1_(t mod 3 = 1).
M(X) = sum_(1<=m<=X) a6(m) K(floor(X/m))     (X>=12).
```

The kernel is **period 36 in its quotient**, mean zero in a full period, and `-2<=K(t)<=1`; in particular `|K|<=2` and `K(1)=1`. None of this asserts mean zero under the physical norm coefficient distribution. The module also provides an Abel return using a bounded primitive; use it only with the actual signed quotient buckets.

For every prime `p>=5`, the **true finite** local polynomials of `a6` are:

```text
p == 1 mod 3 (split): (1 - z)^2 = 1 - 2z + z^2;
  a6(p)=-2, a6(p^2)=+1, a6(p^e)=0 for e>=3.
p == 2 mod 3 (inert): (1-z)(1+z) = 1 - z^2;
  a6(p)=0, a6(p^2)=-1, a6(p^e)=0 for e>=3.
p=2,3: excluded by the a6 mask.
```

**Important analytical constraint:** `chi_{-3}` on a surviving first-power prime `p>y` is **identically +1**, because inert primes have coefficient zero. Thus the surviving large-prime factor `-2` is coherent, not an oscillatory high-conductor character phase. The character supplies a congruence-class *selector*. A large sieve cannot obtain the missing gain from this fixed mod-3 selector alone. Genuine multi-character Hecke rows and quantitative masked/normalized moment estimates would be additional arithmetic information.

## 2. An entire cutoff family, not a distinguished exponent 1/8

For any integer `y>=2`, let `b_y(m)=a6(m)` when `p^2\nmid m` for every prime `p>y`, and `0` otherwise. Define `CORE_y(X)` using `b_y`, and `BAD_y(X)` using `a6-b_y`, both paired against the **same actual quotient kernel** `K(floor(X/m))`. Then exactly

```text
M(X)=CORE_y(X)+BAD_y(X).
```

The large-square tail is **unconditionally payable**. If `p>y` occurs squared with nonzero `a6`, its exponent is exactly two; the coefficient contributed by `p^2` is `+1` (split) or `-1` (inert). Multiplicativity gives `|a6(p^2u)|<=tau(u)` for `p\nmid u`, while `p^3|m` has zero coefficient. Union-bound only the large squares, not the signed core:

```text
|BAD_y(X)|
 <= 2 * sum_(prime p>y) sum_(u<=X/p^2) tau(u)
 <= 2X(1+log X)*sum_(prime p>y) p^(-2)
 <= 2X(1+log X)/y.
```

For `y=floor(X^alpha)`, `X^alpha>=2`, it is `<=4 X^(1-alpha)(1+log X)`. This is a valid `O(X^(7/8)log X)` independent bound at `alpha=1/8`, but **the exponent arises from choosing the cutoff**. A separately reported VF raw squareful tail of `O(R^(7/4)/log R)` uses the genuine positive physical VF weights and is a different carrier: do not claim its numerical constant 10 is kernel-proved or transfer it to the signed Hecke ledger without a bridge.

For `y=floor(X^alpha)`, each surviving large factor `p>y` is split and appears to the first power; the number `k` of such factors satisfies `k<1/alpha`. With `s` made of prime-to-6 primes `<=y`, define

```text
P_k(X;y)=sum_(y<p1<...<pk, each prime ==1 mod 3)
            sum_(s>=1, P+(s)<=y, gcd(s,6)=1, s*p1*...*pk<=X)
                a6(s)*K(floor(X/(s*p1*...*pk))).
CORE_y(X)=sum_(0<=k<1/alpha) (-2)^k P_k(X;y).
```

`P_0` includes `s=1`; floor divisions are literal integer divisions, not a smooth Li replacement. Inert large primes can still affect `BAD_y` through their square factor, but are absent to first power from every `P_k`.

| Cutoff `y` | Maximum large split-prime depth | Paid large-square error |
|---|---:|---|
| `floor(X^(1/8))` | 7 | `<=4 X^(7/8)(1+log X)` |
| `floor(X^(1/4))` | 3 | `<=4 X^(3/4)(1+log X)` |
| `floor(X^(1/3))` | 2 | `<=4 X^(2/3)(1+log X)` |
| `floor(sqrt X)` | 1 | **exactly ZERO**: `p>sqrt X => p^2>X` |

### Root-wall consequence: EXACT two-layer identity, with no tail

At `y=floor(sqrt X)`, the complete identity simplifies to

```text
M(X) = P_0(X;y) - 2 P_1(X;y).
P_1(X;y) = sum_(sqrt X<q<=X, prime q==1 mod 3)
               sum_(1<=s<=floor(X/q))
                   a6(s)*K(floor(X/(s*q))).
```

The restriction `P+(s)<=y` is now automatic in `P_1`: `s<=X/q<sqrt X`. The `P_0` part still includes **every** prime-to-6 `y`-smooth norm coefficient up to `X`, including its permitted square factors. The difficulty has **moved into that large smooth population**; a two-layer identity is not easier *without an additional arithmetic bound*.

This exact cofactor-prime bilinear coupling is naturally aligned with RH_Lean's existing square-root greatest-owner/fibre and physical Gram machinery. Unlike `X^(1/8)`, the root cutoff removes all large-square tails and eliminates the need for a seven-fold large-prime multilinear form. It is the recommended **primary structural interface to test**, with quarter-power and eighth-power cutoffs retained as independent controls.

## 3. Exact nonlocal prime-extension recurrence

Let `F_y(t)=sum_(s<=t, P+(s)<=y, gcd(s,6)=1) a6(s)K(floor(t/s))`, taking `F_y(0)=0`. For each split prime `q>y`, let `T_q f(t)=f(floor(t/q))`, and let `C_{y,Q}(t)` be the core after adjoining only split primes `y<q<=Q` once. The **finite Euler polynomial**, not a heuristic, gives

```text
C_(y,Q)(t) = product_(y<q<=Q, q==1 mod 3 prime) (I - 2T_q) F_y(t).

C_(y,q)(t) = C_(y,q^-)(t) - 2 C_(y,q^-)(floor(t/q)).
```

Here `q^-` means immediately before adjoining the prime `q`. All `T_q` commute by the integer floor-of-floor identity; repeated use of one q is prohibited in the product. Expanding generates the exact `(-2)^k P_k` layers. This recurrence supplies a **true literal source/consumer for the cross-layer response**, not a quantitative estimate.

At `X/2<q<=X`, `floor(X/q)=1` and `C_(y,q^-)(1)=F_y(1)=K(1)=1`, so each split upper-half prime injects exactly `-2` into the core. Those primes have no distinct local upper-face pairing below `X`, consistent with the compiled `TopPrimeReplacementIsolation.lean` and `AdaptivePrimeMatching.lean` obstructions. Their order-`X/log X` contribution must be paid **nonlocally**, through older cofactor/depth/owner response; an absolute sum of unmatched faces cannot reach `X^(7/8)`.

**Quantitative payment still OPEN:** a one-sided signed correlation or multi-row moment theorem for this complete prime-extension response, or an arithmetic bilinear bound retaining the full `P_0-2P_1` coupling, is required. Merely squaring the exact identity, bounding each `P_k` separately, or summing local favorable toggles is a target-equivalent or false shortcut. The previously compiled rank-3 native coefficient obstruction excludes a single unmasked centered two-factor rectangle at `R=317`; it does NOT prohibit masked multi-row or properly factored Hecke representations.

## 4. Independent exact census and useful failure controls

Reproduce with `g++ -O3 -std=c++17 scripts/vf919_hecke_cutoff_sweep.cpp -o /tmp/hecke_cutoffs && /tmp/hecke_cutoffs 10000000`. The program independently builds the genuine integer Mobius sequence, `a6` via its exact local Euler factors, and the genuine period-36 quotient kernel; it does not call an OAI theorem. Every sum is exact integer arithmetic and `CORE+BAD=M` is checked. Output for `X=10,000,000`:

| Cutoff | Signed depth-0 | Depth-1 | Depth-2 | Depth-3 | Depth-4 | BAD | M(X) |
|---|---:|---:|---:|---:|---:|---:|---:|
| `y=7` (1/8) | 1 | -121,742 | +205,280 | -92,712 | +10,320 | -110 | +1,037 |
| `y=56` (1/4) | +124 | -70,628 | +93,716 | -22,152 | 0 | -23 | +1,037 |
| `y=215` (1/3) | +3,895 | -55,524 | +52,656 | 0 | 0 | +10 | +1,037 |
| `y=3162` (1/2) | -47,157 | +48,194 | 0 | 0 | 0 | **0** | +1,037 |

At `y=7`, the absolute sums of the four nontrivial signed depth totals already exceed `430,000`, against core `+1,147`; **the cancellation is across depth**, not the character phase of a single split-prime slot. At `y=3162`, two opposite-sign totals of approximately 48,000 leave `+1,037`. Both are exact finite facts only. The same independently verified program at `X=1,000,000` gives `M=212`, `CORE_5=303`, `BAD_5=-91`.

Neither the large-square bound nor the two-layer reduction proves even a fixed positive improvement over the elementary global Mertens exponent. With the paid tail removed, a bound on the completed `CORE` is **equivalent up to that tail** to the 7/8 Mertens estimate. The square-shell second-moment `SB-7/8` is instead a distinct, stronger sufficient inequality whose own uniform estimate is also open.

## 5. Next genuinely independent mechanism / adversarial tests

1. **Owner and Finite Wheel:** formalize/check the cutoff-family factorization and prime-extension recursion against native #919 a6 coefficients and both actual square/floor walls; relate the root-cutoff `P_1` cofactor-prime sum to the existing once-only greatest-owner physical charges, with a separate bridge for the original VF weighted and #915 masked/clipped carriers.
2. **Analytic:** find a real uniform bilinear (or admissible multi-Hecke-row) estimate on the complete `P_0-2P_1` response that does *not* assume Mertens growth or rely on the fixed mod-3 selector as a pseudo-random character. Identify and subtract the principal order-`X/log X` mode before taking norms, preserving all off-diagonal owner/quotient interactions, row masks, sharp/smooth errors and conductor dependence.
3. **Census:** compare the `1/8,1/4,1/3,1/2` cutoffs on predeclared held-out `X`, tracking signed layers, physical coefficients, full quotient buckets and cancellation factors. A smaller number of layers or nicer finite ratio by itself is not improvement.
4. **Referee:** independently verify the elementary constant 4 for BAD, any stated constant in the *separate* VF large-square estimate, the local split/inert coefficients, (k<1/alpha), the zero-BAD square-root case and the operator recurrence. Falsify any assertion that `K`-mean-zero or `chi=+1` supplies character cancellation. Test a multi-row proposal against the actual rank witness and exact source admissibility.
5. **Lean:** reuse #919 compiled coefficient and quotient-kernel identities; do not duplicate their finite proofs. Only formalize a genuinely nonduplicate cutoff/operator identity or independently proved saving, with exact-head compilation, standard axioms, and explicit hypotheses.

**Decision:** `CONTINUE / REVISE`. Make the **zero-tail, two-layer root-wall bilinear** the simplest concrete representation to test first, with all four cutoffs as control. The final **unconditional quantitative signed cancellation theorem is OPEN**. Keep Hecke multi-row, MU-LIFT K1/K2/K3, Nyman and square-shell energy as genuinely distinct candidates rather than seven aliases for the same unproved core bound.

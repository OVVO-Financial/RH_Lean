# Universal reciprocal-prime partition maxima: exact all-x extrema, root-wheel populations, and the new sign target

**11 October 2026.** This note uses precisely ONE action: sequentially admit the next genuine prime to the smooth-only signed Euler/Mobius population. Exact claims are valid for every x in their stated ranges, not extrapolated from a census. The global post-root maximum below is a numerical conjecture. Finite C/A and RH remain OPEN.

## 1. Universal state and all-x one-prime update

Write
\[
S_y(x)=\sum_{\substack{1\le n\le x\\P^+(n)\le y}}\mu(n),\qquad P^+(1)=1,
\]
with the smooth-only Euler convention: new squarefree products of a fresh prime p and existing cofactors are added with sign opposite to that cofactor. For ANY integer x and the next genuine prime p,
\[
\boxed{S_p(x)-S_{p^-}(x)=-S_{p^-}(\lfloor x/p\rfloor).}\tag{1}
\]
If \(r=\lfloor\sqrt{x}\rfloor\) and \(p>r\), all cofactors \(c\le \lfloor x/p\rfloor\) have already been completely reconstructed, so
\[
\boxed{\Delta_p S=-M(\lfloor x/p\rfloor).}\tag{2}
\]
This is the same literal operation for all x. The square-root restriction changes only which historical coefficients have become final.

## 2. Every reciprocal partition has exact extrema at its boundaries

For k>=1 define the genuine post-root prime population
\[
H_k(x)=\pi(\lfloor x/k\rfloor)
       -\pi(\max(r,\lfloor x/(k+1)\rfloor)),
\quad r=\lfloor\sqrt{x}\rfloor.
\]
This counts exactly primes \(p>r\) with \(\lfloor x/p\rfloor=k\); the max in the lower cutoff matters for k=r near non-square endpoints.

All primes in the kth band create the SAME net signed amount \(-M(k)\). Consequently
\[
\boxed{\Delta_k S=-M(k)H_k(x).}\tag{3}
\]
Inside each band, the state is monotone. Thus maxima and minima of the completed post-root walk are attained at reciprocal-band boundaries. There are at most r bands to check, regardless of the number of new primes.

More precisely, for x>=9 and t<=r,
\[
\boxed{
S_{\lfloor x/(t+1)\rfloor}(x)
=
S_{\lfloor x/3\rfloor}(x)
+\sum_{k=3}^{t}M(k)H_k(x),
}\tag{4}
\]
provided the left cutoff is not below r; at the final root-clipped band use the cutoff r rather than floor(x/(r+1)). Every band interior lies between its endpoint states.

## 3. A strict universal terminal peak, not merely finite numerics

The genuinely historical finite Mertens coefficients obey
\(M(k)\le0\) for **every 3<=k<=93**, \(M(94)=1\), \(M(95)=2\).
These facts follow by exact finite evaluation of the ordinary Mobius function.

Therefore, for EVERY x>=9:
- When \(p>\max(r,x/94)\) and \(p\le x/3\), \(3\le k_p\le93\), so \(\Delta_p=-M(k_p)\ge0\).
- When \(x/3<p\le x/2\), \(k_p=2\), so \(\Delta_p=-M(2)=0\); the new p (-1) and 2p (+1) cancel *within the single-prime insertion*.
- When \(x/2<p\le x\), \(k_p=1\), so \(\Delta_p=-M(1)=-1\).

Thus **the terminal post-root Euler population is exactly unimodal for all x**: nondecreasing from \(\max(r,x/94)\) to x/3, flat through x/2, nonincreasing through x. The stage at x/3 is a genuine terminal maximum:
\[
\boxed{\max_{y\ge x/3} S_y(x)=S_{\lfloor x/3\rfloor}(x).}\tag{5}
\]
The negative minimum for y>=x/3 is the final state M(x). A one-sided maximum is NOT necessarily a maximum of absolute value: at x=20, S_(floor(x/3))(20)=1 while M(20)=-3.

This terminal theorem covers the ENTIRE post-root walk whenever x<=94^2, since then x/94<=sqrt(x). More generally it proves the x/3 maximum throughout the final p>x/94 portion of every larger endpoint.

The FIRST POSSIBLE negative *canonical smooth-only* post-root update is x=94*97=9118, p=97: k=94, M(94)=1, delta=-1. This is distinct from the prime-*candidate* convention's first negative correction at x=95*97=9215; the candidate seeding changes the visible update but not the completed Mobius coefficients.

## 4. Stronger falsifiable all-x maximum conjecture

The complete sequential census gives the stronger, not-yet-proved prediction
\[
\boxed{\forall x\ge9,\quad
S_y(x)\le S_{\lfloor x/3\rfloor}(x)\quad\text{for all integer }y\ge\lfloor\sqrt{x}\rfloor.}\tag{Hmax}
\]
By the universal monotone-within-band law, it is equivalent to the exact finite family
\[
\boxed{\forall x\ge9,\quad
\forall\,3\le t\le\lfloor\sqrt{x}\rfloor,\quad
\sum_{k=3}^t M(k)H_k(x)\le0.}\tag{6}
\]
The final k=r band is clipped to primes p>r by the definition of H_k.

An independent exact Mobius/prime-count sieve tested:
* **Every 5,999 square roots R=2..6000**, x=R^2-1, no violation.
* **Every one of the 199,992 integers x=9..200000**, no violation.
* Every within-band state is covered by its endpoints, so this is not merely a scan of sparse prime cutoffs.

Sample exact states:

| x | prior peak S_(floor(x/3)) | top-half prime population | completed M(x) | earlier cutoff maximum above prior peak |
|---:|---:|---:|---:|---:|
| 20 | 1 | 4 | -3 | 0 |
| 317 | 25 | 29 | -4 | 0 |
| 1027 | 72 | 75 | -3 | 0 |
| 100488 | 4446 | 4474 | -28 | 0 |
| 999999 | 37172 | 36960 | +212 | 0 |
| 35999999 | 1055151 | 1052895 | +2256 | 0 |

Hmax is NOT implied by arbitrary nonnegative replacement band weights H_k: setting every weight to zero except H_94>0 violates it because M(94)=1. An all-x proof must use actual prime availability, not the sign of M alone.

### Historical reciprocal reference (not yet a universal theorem)
The signed harmonically weighted prefixes
\[
\sum_{k=3}^{t}\frac{M(k)}{k(k+1)}
\]
were negative throughout t=3..6000; their largest observed value was exactly -1/12 at t=3. This suggests an analytic strategy through the prime band distribution, but replacing H_k(x) by x/[k(k+1)log x] is NOT exact and by itself would not establish Hmax.

## 5. The future primes are already determined by the earlier root-wheel sieve

This is the key arithmetic dependence to preserve. Define
\[
W_r(n)=\prod_{\substack{q\le r\\q\ \mathrm{prime}}}
(1-\mathbf1_{q\mid n})
=\sum_{\substack{d\mid n\\P^+(d)\le r}}\mu(d).
\]

For EVERY x and every integer r<n<=x with r=floor(sqrt x),
\[
\boxed{W_r(n)=\mathbf1_{\{n\ \mathrm{prime}\}}.}\tag{7}
\]
Proof: each composite n<=x has a prime factor <=sqrt(n)<=r, so root-wheel elimination necessarily kills it; any prime >r survives. Thus the locations of **every** post-root prime are fixed by the earlier prime coordinates, with no stochastic independence.

Therefore the genuine band counts are themselves root-wheel survivor populations:
\[
\boxed{H_k(x)=
\sum_{\substack{r<n\le x\\x/(k+1)<n\le x/k}}W_r(n).}\tag{8}
\]
In particular, the final singleton-prime count is the exact top-half root-wheel population:
\[
\begin{aligned}
P(x)&=\pi(x)-\pi(\lfloor x/2\rfloor)
=\sum_{x/2<n\le x}W_r(n)\\
&=\sum_{\substack{d\le x\\P^+(d)\le r}}\mu(d)
\left(\left\lfloor\frac xd\right\rfloor
-\left\lfloor\frac{x}{2d}\right\rfloor\right).
\end{aligned}\tag{9}
\]
This was independently checked by marking exactly the multiples of every prime <=r in the top-half window for all six sample endpoints in the table. The survivor counts are respectively 4,29,75,4474,36960,1052895, matching true prime populations exactly.

**Crucial:** the apparently 'unknown' last-prime population is already completely determined at the root sieve stage. It is NOT an external independent variable. This is the promised universal, finite, sequential common source for both the prior signed peak and the future terminal population.

## 6. Exact all-x peak-minus-population discrepancy and what maximums still do not prove

Every x>=9 satisfies
\[
\boxed{
M(x)=A(x)-P(x),\quad
A(x)=S_{\lfloor x/3\rfloor}(x),\quad
P(x)=\#\{x/2<n\le x:W_r(n)=1\}.
}\tag{10}
\]
From x/3 to x/2, S is constant A; after x/2 it decreases by exactly one at each true prime and finishes at A-P. Hence the precise terminal range is
\[
\boxed{\min_{y\ge x/3} S_y(x)=A-P,\quad
\max_{y\ge x/3} S_y(x)=A,\quad
\max_{y\ge x/3}|S_y(x)|=\max(|A|,|A-P|).}\tag{11}
\]

This is a genuine MAXIMUM/MINIMUM theorem for EVERY x, not a relative density estimate. Nevertheless A and P both have order x/log x. Their leading asymptotic matching is an unconditional PNT consequence and does not give the much smaller necessary residual.

For a universal square-root amplification criterion, the additional missing theorem is, in the SAME physical root-wheel coordinates,
\[
\boxed{
|A(x)-P(x)|\le C\sqrt{xK_{\lfloor\sqrt{x}\rfloor+1}}
\quad\text{for every x},\quad C<\infty.
}\tag{12}
\]
This is the original Mobius amplification bound (and implies RH through the existing conditional chain), not a newly proved conclusion. A fixed *percentage* mismatch between A and P would still be of order x/log x, much too large.

**Next non-circular target:** use the exact root-wheel survivor constraints (7)-(9), and sign/owner information created by each earlier prime, first to prove the weighted maximality condition (6), then to establish an independent, signed coupling between the peak A and top-half survivor population P with residual O(sqrt(x K)). Neither the process rule nor Hmax alone supplies that final coupling.

## Reproducible experiment

[experiments/PrimePopulationCutoff/prime_band_population_maxima.cpp](../experiments/PrimePopulationCutoff/prime_band_population_maxima.cpp)

\`\`\`sh
g++ -O3 -std=c++17 -Wall -Wextra -Werror experiments/PrimePopulationCutoff/prime_band_population_maxima.cpp -o /tmp/band_audit
/tmp/band_audit 6000 200000
\`\`\`

The program independently constructs actual primes, the Mobius function, its signed prefixes, actual reciprocal-band populations, and true top-half survivor counts via the root wheel. It exits nonzero if it finds a counterexample to the global numerical hypothesis. None of these new statements are claimed as newly Lean-compiled.


## 7. Exact terminal prime-rank matching: a quantitative first-crossing contract

Enumerate the *actual root-wheel survivors* in the top half as
\(x/2<p_1<\cdots<p_P\le x\). The terminal scalar state is precisely
\[
\boxed{S_{p_j}(x)=A(x)-j\quad(0\le j\le P).}\tag{13}
\]
This is a deterministic one-credit-per-prime matching, valid for every x>=9. No stochastic population independence is used: each p_j is already certified by W_r.

If \(0\le A(x)\le P(x)\), the first nonpositive crossing occurs at prime rank A (or the state starts at zero when A=0), and exactly \(P-A=-M(x)\) high-prime singletons remain thereafter. If \(A>P\), no crossing occurs and exactly \(A-P=M(x)\) unmatched positive credits remain. Hence the **terminal unmatched population** is always \(|A-P|=|M(x)|\); for x where A<0, the terminal walk begins negative and has residual P-A.

An all-x square-root amplification bound would follow if the certified root-wheel and prior Euler population jointly imposed
\[
\boxed{
P(x)-C\sqrt{xK_{r+1}}\le A(x)
\le P(x)+C\sqrt{xK_{r+1}}.
}\tag{14}
\]
This is a TWO-sided finite-rank restriction. One-sided maximality Hmax does not imply either inequality: it locates the peak without restricting how many terminal prime ranks remain after the peak is spent. The proof must derive (14) from the earlier-prime root-wheel incidence and signed cofactor information, not from choosing C retrospectively or replacing P with an independent prime model.

Numerical unmatched populations from the exact prior table are respectively 3, 4, 3, 28, 212, and 2256 at x=20,317,1027,100488,999999,35999999. This gives a direct finite test for future proposed pairing/classifier lemmas at EACH actual cutoff while keeping the all-x proof target fixed.

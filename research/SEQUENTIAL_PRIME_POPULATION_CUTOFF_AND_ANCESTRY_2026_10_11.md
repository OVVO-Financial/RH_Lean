# Fixed-endpoint sequential prime-population cutoff and shared ancestry

**Date:** 2026-10-11. **Status:** Exact finite sieve and combinatorial identities, independently checked numerics; **finite C/A and RH remain unproved**.

## 1. Question and two genuinely different frozen-prime fields

Fix `x` and process primes `p=2,3,5,...` in increasing order. Keep the endpoint x fixed throughout. The correct animated **prime-candidate field** is

\[
J_y(n)=\begin{cases}
1,&n=1,\\
0,&q^2\mid n\text{ for some processed prime }q\le y,\\
-1,&n\ge2\text{ and no processed prime divides }n,\\
(-1)^{\#\{q\le y:q\text{ prime},q\mid n\}},&\text{otherwise}.
\end{cases}
\]

Write `J_y(x)=sum_{n<=x} J_y(n)`. Its seed is `J_1(x)=2-x`. This is exactly the state machine in `RHLean/Proof/PrimeCombVisualizationFrames.lean`, **not** the all-plus Euler product. Also record the distinct **smooth-only signed Euler population**
\[
T_y(x)=\sum_{\substack{n\le x\\P^+(n)\le y}}\mu(n),
\]
with `P+(1)=1`. Confusing these two stages gives the wrong prime cutoff: `J_y(x)` is eventually constant at `y>x/2`, but `T_y(x)` continues changing because every high prime singleton enters with sign -1 until the last prime <=x.

Exact completed Mobius prefix: `M(x)=sum_{n<=x} mu(n)`. At square endpoints `x=R^2-1`, the **original** finite-C kernel is `Q_R=2M(R-1)-M(x)` with `K_R=max_{0<=z<R}(M(z)-1)^2/(z+1)`. Do not substitute the incomplete `J_y(x)` into the original C theorem.

## 2. The four exact cutoff regimes

For fixed x let `r=floor(sqrt(x))`.

1. **Prime-square cutoff:** after all primes <=r have been processed, every squareful zero is already correct; no later prime can kill a site.
2. **Post-root historical feedback:** each prime p>r, with `k=floor(x/p)`, changes the candidate total by
   \[
   \boxed{\Delta_p=2(1-M(k)).}
   \]
   All changed sites are precisely the `sum_{c=2}^k mu(c)^2` squarefree proper multiples `cp`, and each changes from `mu(c)` to `-mu(c)`. Thus pointwise agreement increases monotonically after the root cutoff.
3. **One-child regime:** if `x/3<p<=x/2`, then `k=2`, `M(2)=0`, and **every** new prime contributes exactly **+2**, flipping the unique child `2p`. Therefore
   \[
   \boxed{M(x)-J_{\lfloor x/3\rfloor}(x)=2[\pi(\lfloor x/2\rfloor)-\pi(\lfloor x/3\rfloor)].}
   \]
4. **Inert regime:** if `p>x/2`, no proper multiple is available; the candidate field never changes again. Its exact and stable reconstruction cutoff is **the largest prime <=x/2**. The smooth-only Euler population, by contrast, still needs all prime singletons through x.

**Directional cutoff:** since `M(k)<=1` for every k<=94 and the first counterexample is `M(95)=2`, every prime satisfying `p>max(sqrt(x),x/95)` contributes a nonnegative update. At `x=9215=96^2-1` the prime `p=97` first realizes `k=95`, giving the **first possible negative post-root prime-comb increment** `Delta_97=-2`. `x=9214` has no negative post-root increment. More primes do not always mean a monotone whole-stage signed total: pre-root stages and sufficiently large endpoints can contain negative increments.

## 3. Exact sequential results

| Fixed x | Last zero-killing prime | Correct sites then | Signed candidate J then | Actual M(x) | Last active candidate prime | Negative post-root steps |
|---:|---:|---:|---:|---:|---:|---:|
| 30 | 5 | 26/30 | -11 | -3 | 13 | 0 |
| 210 | 13 | 156/210 | -81 | -1 | 103 | 0 |
| 288 | 13 | 204/288 | -111 | -7 | 139 | 0 |
| **317** | **17** | **231/317** | **-120** | **-4** | **157** | **0** |
| 1023 | 31 | 716/1023 | -342 | -4 | 509 | 0 |
| **1027** | **31** | **719/1027** | **-343** | **-3** | **509** | **0** |
| 3135 | 53 | 2089/3135 | -946 | +6 | 1567 | 0 |
| 9999 | 97 | 6516/9999 | -2633 | -23 | 4999 | 0 |
| 100488 | 313 | 63934/100488 | -20940 | -28 | 50231 | 9 |
| 999999 | 997 | 623596/999999 | -169582 | +212 | 499979 | 102 |

The smooth-only Euler totals at the root cutoff are -3 and -12 for x=317 and 1027 respectively; at the candidate-complete cutoff x/2 these smooth-only totals are +25 and +72 (the remaining *prime singletons* above x/2 must still contribute -29 and -75 respectively). This is why the two definitions must not be interchanged.

### The forced last layer

| x | Last inserted p <= x/3 | Candidate sum there | Number of remaining active primes | Their exact 2p correction | Final M(x) |
|---:|---:|---:|---:|---:|---:|
| 317 | 103 | -24 | 10 | +20 | -4 |
| 1027 | 337 | -61 | 29 | +58 | -3 |
| 9999 | 3331 | -421 | 199 | +398 | -23 |
| 100488 | 33493 | -3170 | 1571 | +3142 | -28 |
| 999999 | 333331 | -25534 | 12873 | +25746 | +212 |

For example, the final 1,571 two-child prime insertions at x=100488 contribute +3142 while the full original `Q_317` is only +22. The fraction of already-correct sites does **not** control the signed amplitude at the finite-C scale.

## 4. Exact shared-factor ancestry test at every prime cutoff

For each fresh post-root prime p, its proper-composite cofactor channel is
`b(k_p)=M(k_p)-1`, `k_p=floor(x/p)<p`.

Let `y` be the highest processed large prime and define the nested prime-extension availability
\[
N_{x,y}(d)=\#\{p\text{ prime}:r<p\le y,\ p\le x/d\}.
\]
For squarefree cofactors `2<=c<d<=r` define **unordered signed ancestry overlaps**
\[
S_{x,y}=\sum_{\substack{2\le c<d\le r\\\gcd(c,d)>1}}\mu(c)\mu(d)N_{x,y}(d),\qquad
B_{x,y}=\sum_{\substack{2\le c<d\le r\\\gcd(c,d)=1}}\mu(c)\mu(d)N_{x,y}(d).
\]
Define `D_{x,y}=sum_{c=2}^r mu(c)^2 N_{x,y}(c)`.

**Fubini identity (exact for every x and y):**
\[
\boxed{\sum_{\substack{r<p\le y\\p\text{ prime}}}(M(\lfloor x/p\rfloor)-1)^2
=D_{x,y}+2S_{x,y}+2B_{x,y}.}
\]
This is the sum of **individual prime-insertion squared cofactor amplitudes**. It is **not** the square of their sum, and is **not** the full finite-C kernel.

| x | First persistent negative shared-overlap cutoff | Final shared overlap S | Final coprime overlap B | Diagonal D | Total squared cofactor amplitudes |
|---:|---:|---:|---:|---:|---:|
| 317 | 19 | -20 | +43 | 86 | 132 |
| 1027 | 43 | -62 | +106 | 308 | 396 |
| 3135 | 149 | -157 | +221 | 1046 | 1174 |
| 9215 | 733 | -253 | +145 | 3216 | 3000 |
| 9999 | 877 | -240 | +76 | 3483 | 3155 |
| 100488 | 317 | -4181 | -975 | 36554 | 26242 |
| 999999 | 1009 | -103721 | +23569 | 376403 | 216099 |

**Warning:** first persistent negative means the specific simulated shared-overlap prefix remains strictly negative from that prime onward; it is **not** a proved universal threshold formula. For x=1027, the shared overlap is +1 at first new prime 37, zero at 41, and -1 at prime 43. For x=3135 it remains positive as late as 139; for x=9215 it remains positive through prime 727. At x=9999, there is **no negative individual post-root prime correction** despite k=95 being arithmetically possible: its relevant reciprocal prime band contains no prime. This demonstrates the joint role of Mobius parity *and prime availability*.

### Exhaustive square-root scans

- An independently reconstructed full prime-ancestry Gram for **all 999 square roots 2<=R<=1000** yields shared overlap **negative at 993 roots**, zero at six roots, positive at zero roots.
- The earlier full Möbius census `cofactor_conditioning_experiment/root_features.csv` through **R=6000**, separately cross-checked against the 999-root reconstruction, yields shared overlap negative at **5993** of 5999 square roots, zero at six, positive at zero. That earlier table counts **ordered** pair cross-terms (`2*S`); this note uses **unordered** `S`.
- Nevertheless, **232 of the 999 roots** have *some positive intermediate shared-overlap value*. At `R=244`, the intermediate overlap reaches **+432**, remains positive through prime **3677**, and becomes permanently nonpositive starting with prime **3691**; its completed signed shared overlap is **-1682**. Therefore “negative shared overlap after every individual prime addition” is *false*. Only the **completed square-endpoint pattern** survived the finite test.

The full-cutoff sign pattern is a **numerical conjecture candidate**, not an all-root theorem. Even if proved for all roots, controlling this overlap alone would not prove finite C: the remaining coprime cross-terms, correlation with the pre-root candidate field, and inter-prime coherent square of the *total* correction have not been bounded.

## 5. The exact point of contact with finite C

For `x=R^2-1`, define *only as a diagnostic*
\[
Q_R(y)=2M(R-1)-J_y(x).
\]
At full reconstruction, `Q_R(y)=Q_R`. For the final one-child strip `x/3<=y<=x/2`, we have **exactly**
\[
\boxed{Q_R(y)=Q_R+2[\pi(\lfloor x/2\rfloor)-\pi(\lfloor y\rfloor)].}
\]
This is an exact deterministic outstanding-prime budget. It shows the **truncated** C proxy can be enormous even if the completed original C is small. At x=100488, p just below x/3 leaves `Q_317(y)=3164`, a normalized proxy of about **8.15**, while actual `Q_317=22`, actual `C_317=0.056665`. At x=999999 the cutoff just below x/3 leaves proxy `Q_1000(y)=25538`, normalized about **20.85**, while actual `Q_1000=-208`, `C_1000=0.169831`.

For a *chosen diagnostic threshold* C0=1.5, first prime cutoffs at which the proxy stays below that threshold in the tested square-endpoint examples are:

| Square root R | x=R^2-1 | Stable diagnostic prime cutoff for C0=1.5 | Completion cutoff |
|---:|---:|---:|---:|
| 17 | 288 | 83 | 139 |
| 32 | 1023 | 331 | 509 |
| 56 | 3135 | 1153 | 1567 |
| 100 | 9999 | 4297 | 4999 |
| 317 | 100488 | 47297 | 50231 |
| 1000 | 999999 | 486833 | 499979 |

**This does not establish a universal C0=1.5:** the threshold is an explicitly marked finite-root *proxy*, and it is not the original C theorem until every relevant prime has been processed.

The research target remains
\[
\boxed{\exists C<\infty\quad\forall R\ge2:\quad
|Q_R|\le CR\sqrt{K_R}.}
\]
A fixed finite C gives finite A and hence RH via `SquareRootAmplificationClosure.lean` and `MertensEnergyRHForward.lean`. The exact one-prime feedback, the gcd-conditioned squared-cofactor ledger, and the terminal two-child shell **do not yet imply a bound on the signed combined square**.

## 6. Next falsifiable arithmetic theorem

**Candidate** (supported but not proved by this finite census): at every *completed physical square endpoint* the unordered gcd-sharing cofactor-extension overlap satisfies `S_{R^2-1, floor((R^2-1)/2)} <=0`. This is nontrivial because the *same expression at intermediate prime cutoffs* is sometimes positive. The proof, if true, should use actual reciprocal-band prime counts `N_R(c)` and factor parity, **not** a bare claim of random independence.

Then independently bound the full pair interaction after combining the root-prepared candidate field with every post-root correction. A theorem controlling only `sum_p (M(floor(x/p))-1)^2`, even with negative gcd-sharing cross-terms, does not control `(sum_p Delta_p)^2` or the original `Q_R^2`.

**Reproduction:** `python3 prime_cutoff_audit.py`, `python3 prime_ancestry_cutoff.py`, `python3 all_square_endpoint_shared_ancestry.py`, `python3 all_square_overlap_crossings.py`, and `python3 make_prime_cutoff_figures.py`. All use actual integer primes and Mobius signs. The first two explicitly verify their Fubini and complete-reconstruction identities; no random simulation or independence premise is used. Full stage CSVs and figures are included in the archive.
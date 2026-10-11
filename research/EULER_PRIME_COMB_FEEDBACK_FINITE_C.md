# Exact sequential Euler-prime feedback at the square root

**Research date:** 2026-10-11. **Status:** Unconditional finite identities and a classical-PNT asymptotic theorem. Neither finite \(C\), finite \(A\), nor RH has been established by this note.

The objective remains exactly
\[
X_R=R^2-1,\quad K_R=\max_{0\le y<R}\frac{(M(y)-1)^2}{y+1},\quad
Q_R=\sum_{a,b<R}\mu(a)\mu(b)\lfloor X_R/(ab)\rfloor,
\]
\[
\boxed{\exists C<\infty\ \forall R\ge2:\ |Q_R|\le C R\sqrt{K_R}.}
\]
The exact identity \(Q_R=2M(R-1)-M(X_R)\) then gives \(A\le(C+\sqrt2+1/2)^2\). See [the Euler-to-C-to-A proof map](EULER_PRODUCT_SQUARE_ROOT_FINITE_C_A.md).

## 1. The actual animation has an exact post-root update law

Use the **prime-candidate seed**, not independent random signs: initialize \(J(1)=1\), \(J(n)=-1\) for \(n\ge2\). Process actual primes in increasing order. A prime acts only on proper multiples: its first hit recognizes a composite, later distinct-prime hits reverse parity, and prime-square hits kill.

For \(p\ge R\) and \(X=X_R\) we have \(p^2>X\). Every \(n=cp\le X\) has \(c<R\), so its cofactor is already completed. Thus an added prime has **no square-kill channel** and its signed increment is exactly
\[
\boxed{\Delta_p(X)=2\bigl(1-M(\lfloor X/p\rfloor)\bigr).}\tag{1}
\]
This is the physical update in RHLean/Proof/PrimeCombReciprocalBandCancellation.lean, not a modeled packet.

Primes \(p>X/2\) have quotient 1 and increment zero. Let \(N_R=\pi(\lfloor X/2\rfloor)-\pi(R-1)\), the count of active primes, and \(J_R\) the signed prime-candidate field after every prime below \(R\) has acted. The exact endpoint reconstruction is
\[
\boxed{M(X)=J_R+\sum_{\substack{R\le p\le X/2\\p\ \mathrm{prime}}}\Delta_p(X).}\tag{2}
\]
The initial field is itself an exact finite prime-comb state, not an adjustable fit. On squarefree support it equals \(\mu(n)\) for root-smooth integers and isolated high primes, but \(-\mu(n)\) for composites with one high prime and a lower cofactor.

**Important:** this seed is not the all-\(+1\) Euler field. With the all-\(+1\) seed the high-prime step is \(-2M(\lfloor X/p\rfloor)\); the candidate seed has already put \(-1\) at untouched prime seats. Mixing these two fields produces a spurious prime-count term.

## 2. Exact quotient bands, with actual primes only

Put \(b(k)=1-M(k)=-\sum_{n=2}^k\mu(n)\). For \(2\le k<R\), the actual active primes with quotient \(k\) are those in
\[
X/(k+1)<p\le X/k,
\quad h_R(k)=\pi(\lfloor X/k\rfloor)-\pi(\lfloor X/(k+1)\rfloor).
\]
Therefore
\[
\boxed{M(X)=J_R+2\sum_{k=2}^{R-1}b(k)h_R(k).}\tag{3}
\]
All \(b(k)\) are **strictly historical**, and all arrival multiplicities \(h_R(k)\) are genuine prime counts. This is precisely sequential prime insertion, reindexed without discarding occurrence multiplicity.

The arithmetic coefficients obey the finite **exact** harmonic identity
\[
\boxed{
\sum_{k=2}^{N}\frac{b(k)}{k(k+1)}
=1-\sum_{n=1}^{N}\frac{\mu(n)}n+\frac{M(N)-1}{N+1}.}\tag{4}
\]
Proof: interchange the finite sums
\(b(k)=-\sum_{n=2}^k\mu(n)\) and use
\(\sum_{k=n}^{N}1/[k(k+1)]=1/n-1/(N+1)\).
The classical PNT consequence \(\sum_{n\ge1}\mu(n)/n=0\) and \(M(N)=o(N)\) gives
\[
\boxed{\sum_{k=2}^\infty b(k)/[k(k+1)]=1.}\tag{5}
\]
Equivalently, the historical **centered** signal has zero harmonic mean:
\[
\boxed{
\sum_{k=2}^\infty\frac{M(k)+1}{k(k+1)}=0.}\tag{6}
\]

## 3. Every-root terminal monotonicity from only 94 historical coefficients

An exact finite sieve shows \(M(k)\le1\) for every \(1\le k\le94\), and \(M(95)=2\) is the first value exceeding 1. Hence for **every** \(X\) and prime \(p\) with
\[
p>\max(\sqrt X,X/95),\quad p\le X/2,
\]
we have \(\lfloor X/p\rfloor\le94\), and so \(\Delta_p(X)\ge0\).

**Unconditional theorem:** the terminal prime-comb path after this threshold is nondecreasing. This explains the monotone late phase in the \(X=210\) visualization: \(\lfloor\sqrt{210}\rfloor<95\). Global step-by-step monotonicity is *false*: at \(R=317\), \(X=100488\), \(p=439\), the cofactor is \(228\), \(M(228)=3\), so \(\Delta_{439}=-4\).

## 4. Exact PNT distribution of the historical quotient bands

For any **fixed** \(k\ge2\), as \(R\to\infty\), \(X=R^2-1\),
\[
\frac{h_R(k)}{N_R}\longrightarrow\frac{2}{k(k+1)}.\tag{7}
\]
This follows directly from PNT at the two endpoints \(X/k\) and \(X/(k+1)\), together with \(N_R\sim X/(2\log X)\). The probabilities sum to 1. The tail \(k>K\) has probability tending to \(2/(K+1)\), so this distribution is tight **without any independence assumption**.

Equation (7) proves the asymptotic proportions of positive, negative and zero **actual prime steps**:
\[
P_+=2\sum_{\substack{k\ge2\\M(k)<1}}\frac1{k(k+1)},\quad
P_-=2\sum_{\substack{k\ge2\\M(k)>1}}\frac1{k(k+1)},\quad
P_0=2\sum_{\substack{k\ge2\\M(k)=1}}\frac1{k(k+1)}.\tag{8}
\]
The tails of each of these positive-weight series after \(k=N\) are bounded by **\(2/(N+1)\)**, unconditionally. An independent exact Möbius sieve through \(N=20{,}000{,}000\) gave:
\[
P_+=0.9955302357\pm10^{-7},\quad
P_-=0.0023867719\pm10^{-7},\quad
P_0=0.0020828924\pm10^{-7}.
\]
The errors are rigorous tail caps conditional only on the finite sieve enumeration. In particular, all quotient classes \(k<95\) give nonnegative steps; **at least \(1-2/95=97.8947\%\)** of active primes lie in the eventually monotone terminal sector.

### Quantitative result: average correction tends to +4

PNT together with the standard Brun–Titchmarsh prime-count upper bound and the unconditional \(M(y)\ll_B y/(\log y)^B\) (any fixed \(B\)) lets us pass from (7) to the **unbounded** step weight \(2b(k)\):
\[
\boxed{
\lim_{R\to\infty}\frac{1}{N_R}
\sum_{\substack{R\le p\le X/2\\p\ \mathrm{prime}}}\Delta_p(X)
=4\sum_{k=2}^\infty\frac{b(k)}{k(k+1)}=4.}\tag{9}
\]
For a rigorous tail argument, split at \(k=X^{1/4}\). For \(K<k\le X^{1/4}\), Brun–Titchmarsh bounds the count of primes in the \(k\)-band by \(O(X/(k^2\log X))\). Its contribution after normalization is at most a constant times \(\sum_{k>K}|b(k)|/k^2\), which tends to zero by quantitative PNT. For \(k>X^{1/4}\), primes satisfy \(R\le p<X^{3/4}\); the bound on \(M(X/p)\) and the bounded reciprocal-prime sum over this range give \(O_B(X/(\log X)^B)=o(X/\log X)\) for \(B>1\). This justifies (9) without a random-sign hypothesis.

It follows that the **total post-root correction** is \(\sim 2X/\log X\). Combining this with quantitative PNT \(M(X)=o(X/\log X)\) in (2) shows
\[
\boxed{J_R\sim-2X/\log X,\qquad
\sum_{p\ {\rm active}}\Delta_p\sim+2X/\log X.}\tag{10}
\]
This is a new explicit arithmetic explanation of leading signed compensation in the prime-candidate animation. It is a PNT-scale theorem, **not finite \(C\)**.

## 5. Actual full ledger and the residual needing control

| R | Candidate field \(J_R\) | Active primes | Positive step count | Negative step count | Sum of updates | Final \(M(X)\) |
|---:|---:|---:|---:|---:|---:|---:|
| 56 | -946 | 231 | 231 | 0 | +952 | +6 |
| 317 | -20,940 | 5,092 | 5,068 | 9 | +20,912 | -28 |
| 1,000 | -169,582 | 41,370 | 41,160 | 102 | +169,794 | +212 |
| 5,561 | -4,073,166 | 997,847 | 992,007 | 3,159 | +4,070,622 | -2,544 |
| 10,000 | -12,230,578 | 2,999,905 | 2,982,696 | 9,357 | +12,232,506 | +1,928 |
| 20,000 | -45,093,849 | 11,076,675 | 11,013,469 | 34,786 | +45,092,250 | -1,599 |

These data show why independent random-sign modeling or cancellation **among the late prime steps** is the wrong mechanism: almost all those steps have the same sign! The decisive cancellation is **between the candidate field and its sequential correction ledger**.

Center the empirical mean at its **rigorously proved limiting value 4**. The exact finite identity is
\[
\boxed{
M(X)=(J_R+4N_R)+\sum_{p\ {\rm active}}(\Delta_p-4).}\tag{11}
\]
At \(R=10{,}000\), the two centered contributions are \(-230{,}958\) and \(+232{,}886\), leaving \(M(X)=1{,}928\). At \(R=5{,}561\), they are \(-81{,}778\) and \(+79{,}234\), leaving \(-2{,}544\).

**Do not separately norm these two centered pieces.** Their cancellation remains large and essential. The exact target, with no change of premise, is
\[
\boxed{
|2M(R-1)-(J_R+4N_R)-\sum_{p\ {\rm active}}(\Delta_p-4)|
\le C R\sqrt{K_R}.}\tag{12}
\]
This is the same \(Q_R\) bound, not an independently solved estimate.

## 6. An unconditional pointwise bound for **actual prime-update diagonal energy**

This is a genuinely quantitative theorem at the **correct RH-scale normalization**, not an asymptotic matching identity.

Let the active high-prime set be \(P_R=\{p\text{ prime}:R\le p\le X/2\}\) and \(y_p=\lfloor X/p\rfloor\). Every \(y_p<R\), so the strict historical envelope gives
\[
(M(y_p)-1)^2\le (y_p+1)K_R.
\]
The exact physical increment is \(\Delta_p=-2(M(y_p)-1)\), whence
\[
\sum_{p\in P_R}\Delta_p^2
\le4K_R\sum_{p\in P_R}(y_p+1)
\le4K_R\left(X\sum_{R\le p<R^2}\frac1p+\#P_R\right).
\]
The all-root reciprocal-prime estimate already certified in the companion Euler research manuscript is
\(\sum_{R\le p<R^2}1/p\le5/6\); trivially \(\#P_R\le X/2\). Consequently
\[
\boxed{\forall R\ge2:\quad
\sum_{p\in P_R}\Delta_p^2
\le \frac{16}{3}X K_R
<\frac{16}{3}R^2K_R.}\tag{13}
\]
This is an unconditional **uniform bound on the squared genuine prime-candidate updates**, with no independence, probabilistic, RH, or finite-A assumption.

For the centered steps \(Z_p=\Delta_p-4=-2(M(y_p)+1)\), the elementary inequality
\(Z_p^2\le2\Delta_p^2+32\) gives
\[
\boxed{\sum_{p\in P_R} Z_p^2
\le\frac{80}{3}R^2K_R.}\tag{14}
\]
These are actual physical diagonal bounds, not just a frequency-averaged norm.

Independent C++ audit:

| R | Exact \(\sum\Delta_p^2\) | \(\sum\Delta_p^2/(R^2K_R)\) | Exact \(\sum Z_p^2\) | \(\sum Z_p^2/(R^2K_R)\) |
|---:|---:|---:|---:|---:|
| 56 | 4,696 | 0.99830 | 776 | 0.16497 |
| 317 | 104,968 | 0.69638 | 19,144 | 0.12701 |
| 1,000 | 864,396 | 0.57626 | 167,964 | 0.11198 |
| 5,561 | 21,208,300 | 0.45720 | 4,608,876 | 0.09936 |
| 10,000 | 64,309,436 | 0.42873 | 14,447,868 | 0.09632 |
| 20,000 | 239,198,548 | 0.39866 | 55,687,348 | 0.09281 |

**Why this does not already prove finite C:** let \(B_R=2M(R-1)-(J_R+4N_R)\) and \(Z_p=\Delta_p-4\). The *original* floor sum is
\(Q_R=B_R-\sum_{p\in P_R}Z_p\), so
\[
\boxed{
Q_R^2=B_R^2+\sum_{p\in P_R}Z_p^2
-2B_R\sum_{p\in P_R}Z_p
+2\sum_{\substack{p<q\\p,q\in P_R}}Z_pZ_q.}\tag{15}
\]
Equation (14) **controls the diagonal**. The remaining square contains the
highly coherent off-diagonal interactions among the genuine inserted primes
and their signed interaction with the field that they reconstruct. These
terms must be retained together; bounding either piece separately is
contradicted by the large numerical values of the centered signed masses.
Establishing the required all-scale bound for that signed cross-interaction
is exactly the unresolved finite-\(C\) theorem. No new equivalent hypothesis
is silently introduced as a lemma.

## 7. What is new, what is still open, and how to reproduce

The exact historic feedback law and frozen-prime insertion were already formalized in:
- RHLean/Proof/PrimeCombVisualizationDynamics.lean
- RHLean/Proof/PrimeCombVisualizationRecurrence.lean
- RHLean/Proof/PrimeCombReciprocalBandCancellation.lean
- RHLean/Proof/PrimeSievePostSqrtGap.lean

This note adds the first-exception \(M(95)=2\) monotonicity cutoff, a PNT-derived exact limit distribution of step signs, a harmonic identity giving the deterministic mean \(+4\), and an explicit non-circular audit of the *remaining large signed cross-compensation*.

Reproduce the small/medium-root checks and the finite limiting-frequency truncation using [the standard-library prime-comb feedback audit](../scripts/euler_prime_comb_terminal_probe.py). All large-root samples, including \(R=20{,}000\), can be independently reproduced using [the segmented C++ field reconstruction](../experiments/euler_prime_comb_full_field_audit.cpp). It computes both \(J_R\) and \(M(X)\) from actual Möbius coefficients, then checks their agreement with the separately accumulated prime insertions. Examples: `g++ -O3 -std=c++17 experiments/euler_prime_comb_full_field_audit.cpp -o audit`, then `./audit 10000` or `./audit 20000`. No new Lean compilation is claimed.

**The only unresolved mathematical estimate remains a uniform finite \(C\) on the combined signed \(Q_R\).** A proof must couple (rather than separate) the actual candidate-field history and the measured prime updates at every moving square endpoint. The PNT-scale average \(+4\), monotonicity and convergence-rate results do not imply that bound.

References: [NIST DLMF §27.11, Möbius reciprocal sum](https://dlmf.nist.gov/27.11); Montgomery–Vaughan, *The large sieve* (1973), Brun–Titchmarsh bound; [the finite-C/A proof chain](EULER_PRODUCT_SQUARE_ROOT_FINITE_C_A.md).

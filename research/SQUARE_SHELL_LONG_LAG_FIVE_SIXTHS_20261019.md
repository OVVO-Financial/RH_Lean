# A direct 5/6 route: endpoint telescope, long shell lags, and paid large gcd

**Research date:** 2026-10-19 (New York). **PR:** #982, \`proof/trapezoid-square-shell-energy-20261018\`.
**Acceptance classes:** Exact finite identities and deterministic counting proofs. **OPEN:** the independent signed small-gcd, long-lag arithmetic estimate. This is an attack on the 5/6 Mertens exponent, **not** a proof of that exponent, zero-free strip, the original #915 source-payment theorem or RH.

## 1. Why the \(H^{7/3}\) shell-energy target is sufficient but potentially overstrong

For \(r\ge2\) let
\[
\Delta_r=\sum_{r^2<n\le(r+1)^2}\mu(n).
\]
Since \(\mu((r+1)^2)=0\), this equals the strictly open square-shell sum. For a dyadic root block \(H\le r<2H\), put \(S_H=\sum_{r=H}^{2H-1}\Delta_r=M((2H)^2)-M(H^2)\).

The local second moment \(\sum\Delta_r^2\ll_\varepsilon H^{7/3+\varepsilon}\) implies \(|S_H|\ll_\varepsilon H^{5/3+\varepsilon}\) by Cauchy--Schwarz. The converse is *false for bounded integer sequences*: alternating coherent signs between successive entire square shells can make each \(|\Delta_r|\asymp H\) (energy \(\asymp H^3\)) while the dyadic *endpoint* sum remains much smaller. Thus the per-shell energy hypothesis is stronger than the target needs. Our next theorem should not force it.

**Essential quantifier correction:** controlling only the completed dyadic blocks \(S_H\) does *not* control arbitrary roots inside \([H,2H]\). One must establish the same estimate **uniformly over every partial block** \(S_{H,K}=\sum_{r=H}^{H+K-1}\Delta_r\), \(0\le K\le H\), for each dyadic \(H=2^j\). Then \(M(R^2)-M(H^2)=S_{H,R-H}\) is controlled at every square root \(R\in[H,2H]\); the completed blocks telescope over dyadic \(H\), and the residual from \(R^2\) to arbitrary \(x<(R+1)^2\) costs only \(O(\sqrt x)\). This *uniform-prefix* criterion is equivalent to the full Mertens \(5/6\) growth statement up to epsilon renaming; a completed-block-only criterion is not.

## 2. The corrected trapezoid has a stronger endpoint telescope

PR #982 already proves
\[
\Delta_r-\bar\Delta_{r,T}=B_{r,T}-B_{r+1,T}.
\]
Summing over any consecutive family \(a\le r<b\) removes **all internal collars**:
\[
\boxed{\sum_{r=a}^{b-1}(\Delta_r-\bar\Delta_{r,T})=B_{a,T}-B_{b,T}.}
\]
The genuine integer Möbius sawtooth has \(|B_{r,T}|<T/2\), so the left side has absolute value \(<T\). For a general unit-Lipschitz prefix primitive, the already-proved \(|B|\le T\) still gives the rigorously sufficient \(2T\) envelope. A new Lean module, \`research/SQUARE_SHELL_TRAPEZOID_ENDPOINT_TELESCOPE_20261019.lean\`, packages the exact telescope, sharp/smoothed summed endpoint identity, and conditional transfer.

**Consequence:** The \(T=H^{2/3}\) balancing choice belonged to the unnecessarily strong *shell-by-shell energy* method. The endpoint-sum method can take much larger \(T\), up to the geometric window separation limit \(T< H\), and still spends only \(O(T)\), below \(H^{5/3}\). At \(T\asymp H\) the individual-zero collar transition becomes \(|\gamma|\asymp H^2/T\asymp H\). This is only a frequency calculation; the surviving low-frequency discrepancy can still dominate. In particular this algebra does **not** suppress a hypothetical fixed-height zeta zero with \(\Re\rho>5/6\).

## 3. Green--Kubo between square shells, instead of within each shell

Let \(D_H=\sum_{H\le r<2H}\Delta_r^2\). Define the *near* signed shell-pair covariance
\[
N_{H,L}=\sum_{\substack{H\le r<s<2H\\1\le s-r\le L}}\Delta_r\Delta_s
\]
and the *far* signed covariance
\[
F_{H,L}=\sum_{\substack{H\le r<s<2H\\s-r>L}}\Delta_r\Delta_s .
\]
The exact identity is
\[
\boxed{S_H^2=D_H+2N_{H,L}+2F_{H,L}.}\tag{1}
\]
The Lean module \`research/SQUARE_SHELL_LONG_LAG_FIVE_SIXTHS_20261019.lean\` uses the existing \`signedBlockCrossCovariance_eq_doubleSum\`, splits the preceding index row \(i<j\) into \(i<j-L\) versus \(j-L\le i<j\), and proves the exact identity (1). A companion \`research/SQUARE_SHELL_LONG_LAG_UNIFORM_PREFIX_20261019.lean\` resets the prefix index to arbitrary \(H\) and \(K\le H\), and proves the same near/diagonal payment for literal \`realSquareBlockMass\` without hypothesizing any Mobius cancellation.

Every \(|\Delta_r|\le 2r+1<4H\), so without a single arithmetic cancellation,
\[
0\le D_H\le16H^3,\qquad |N_{H,L}|\le16H^3 L.\tag{2}
\]
For
\[
\boxed{L=\lfloor H^{1/3}\rfloor,}
\]
both terms in (2) are below the \(H^{10/3}\) *squared endpoint* target. The Lean module proves this abstractly for any row with \(|f(H+j)|\le K\): diagonal \(\le HK^2\), near-covariance absolute value \(\le HLK^2\), and
\[
S_H^2\le HK^2+2HLK^2+2F_{H,L}.\tag{3}
\]
This does NOT bound \(F_{H,L}\) — its sign is preserved.

The \(L=H^{1/3}\) cutoff is the *5/6 counterpart* of an \(L=H^{1/2}\) absolute-payment cutoff for squared exponent \(7/8\). The needed exponent improvement is concentrated in longer shell-index separations.

## 4. Pay ALL long-pair gcds exceeding H without cancellation

Across all shells in this dyadic block, \(n,m\in(H^2,4H^2]\). If \(\gcd(n,m)>H\), write \(g=\gcd(n,m)>H\). Ignoring shell and separation restrictions can only increase the absolute count. The number of integer sites divisible by a given \(g\) is at most \(\lfloor4H^2/g\rfloor\).

The number of **unordered** physical distinct-site pairs with gcd \(>H\) is therefore bounded by
\[
\begin{aligned}
\frac12\sum_{g=H+1}^{4H^2}\left\lfloor\frac{4H^2}{g}\right\rfloor^2
&\le \frac{(4H^2)^2}{2}\sum_{g=H+1}^\infty\frac1{g^2}\\
&\le 8H^3.\tag{4}
\end{aligned}
\]
The final inequality is elementary: for \(g\ge H+1\),
\(g^{-2}\le 1/[g(g-1)]=1/(g-1)-1/g\); the sum telescopes to \(1/H\).

It also pays all same-large-prime-owner pairs (any common owner \(p>H\) forces gcd \(>H\)); in particular these collisions must **not** remain inside the claimed difficult off-diagonal.

Split \(F_{H,L}=F_{H,L}^{\gcd>H}+U_{H,L}^{\gcd\le H}\). Since each \(|\mu(n)\mu(m)|\le1\), equation (4) gives
\[
\boxed{|F_{H,L}^{\gcd>H}|\le8H^3.}\tag{5}
\]

Combining (1)--(5),
\[
\boxed{
S_H^2\le 32H^3+32H^3L+2U_{H,L}^{\gcd\le H}.
}\tag{6}
\]
For every \(0\le K\le H\), the identical proof applies with all shell-pair sums restricted to \(H\le r<s<H+K\). The crude bounds \(D_{H,K}\le16H^3\), \(|N_{H,K,L}|\le16H^3L\), and \(|F_{H,K,L}^{\gcd>H}|\le8H^3\) remain uniform in \(K\). Define \(U_{H,K,L}^{\gcd\le H}\) by the same physical small-gcd long-lag restriction. **The only unpaid scalar input for a genuinely global \(5/6\) result is uniform in every partial length**:
\[
\boxed{
\sup_{0\le K\le H}\,U_{H,K,\lfloor H^{1/3}\rfloor}^{\gcd\le H}
\ll_\varepsilon H^{10/3+\varepsilon}.
}\tag{7 OPEN}
\]
A signed upper bound is enough; no absolute-value estimate on this large double sum is needed. Equation (7) remains an RH-adjacent arithmetic hypothesis, **not** a consequence of the established identities. Conversely a global \(5/6\) bound implies this **uniform-prefix** version up to \(\varepsilon\)-renaming, by (1)--(5); it is not an independent achievement until proved from genuinely different prime/cofactor input.

## 5. The remaining physical pairs are genuinely separated and unshared

For \(r<s\) with \(s-r>L\), and sites \(r^2<n\le(r+1)^2\), \(s^2<m\le(s+1)^2\),
\[
m-n\ge s^2+1-(r+1)^2
=(s-r-1)(s+r+1)+1\ge2HL+1.
\]
At \(L\asymp H^{1/3}\), the remaining pairs therefore have integer separation \(\gg H^{4/3}\). This is NOT the hard within-shell shifted-prime correlation \(|pc-p'c'|=O(H)\); the long-lag physical difference is considerably larger.

If \(g=\gcd(n,m)\le H\), put \(n=ga,\ m=gb\). Then \((a,b)=1\), and exact multiplicativity gives
\[
\mu(n)\mu(m)
=\mathbf1_{(g,ab)=1}\,\mu(g)^2\mu(a)\mu(b).
\]
The shared gcd sign has disappeared (it is squared). The residual phase is determined by the distinct **unshared** cofactor prime factors, precisely the mechanism the owner-payment and signed-divisor programs have been attempting to isolate. The future Type II lemma must retain this coprimality mask, the true \(\mu\), literal moving square-index assignments and the entire \(d=1\) coherent mode. It must not invoke the bound (7) itself.

## 6. Genuine Mobius census (full signs, integer-exact)

\`scripts/square_shell_long_lag_census.cpp\` computes a verified whole-prime Möbius sieve (including factors above \(\sqrt{N}\)), prefix values, all shell masses, exact \(S_H^2=D_H+2N_{H,L}+2F_{H,L}\), and both the \(H^{2/3}\) and \(0.8H\) translated averages. It performs independent trial-division verification at \(n\le1000\). The previous experimental Python shortcut omitting large prime factors was discarded; the table below uses the corrected complete sieve.

| H | D_H | S_H | near N_H,L | far F_H,L |
|---:|---:|---:|---:|---:|
| 512 | 486,935 | +233 | +55,790 | -272,113 |
| 1,024 | 1,723,387 | -29 | +200,877 | -1,062,150 |
| 2,048 | 7,380,415 | -17 | +577,504 | -4,267,567 |
| 4,096 | 30,291,950 | +118 | -42,191 | -15,096,822 |
| 8,192 | 126,589,560 | -2,032 | -4,299,221 | -56,931,047 |

The long-lag term is negative throughout these sampled powers of two and offsets most of the unsigned shell energy, but this follows algebraically from the observed small dyadic endpoint sum; it is **not** numerical proof of a uniform upper bound or a prediction about all larger H.

**Crucial prefix falsifier:** the long-lag covariance is *not* always negative when the partial-root endpoint varies. With H=8192 and L=20, the exact running prefix scan has **521 positive** far-covariance instances for 1<=K<=8192, with maximum **+4,798,239 at K=527**. At H=4096, there are 57 positive partial prefixes, with maximum +336,666 at K=382. Hence an attack that assumes a negative far term for *every K* is refuted by genuine Möbius data; the correct one-sided upper bound still permits positive excursions. The C++ census now records these falsifiers. At \(H=8192\), the larger average \(T=\lfloor0.8H\rfloor=6553\) changes the entire coherent block sum by only \(-18.209735\), versus the original block sum \(-2032\).

The brute-force *divisor-witness* count for large gcd (overcounting actual pairs) is \(2,472,647,025,770\) at H=8192, about \(4.498H^3\), below the elementary \(8H^3\) bound. There is no inference from finite data to (7).

## 8. A second exact simplification: remove the moving prime-root cutoff

For any translated half-open shell with \(r\ge2\), \(0\le k\le2T\), and \(T\le r-2\), write
\[
L_{r,T,k}=r^2-T+k,\qquad U_{r,T,k}=(r+1)^2-T+k.
\]
An admitted positive product \(L_{r,T,k}<pc\le U_{r,T,k}\) satisfies the exact factor-orientation equivalence
\[
\boxed{(p>r\ \wedge\ c\le r)\quad\Longleftrightarrow\quad p>c.}\tag{8}
\]
**Elementary proof:** If \(p\le r\) and \(p>c\), then \(pc\le r(r-1)<L_{r,T,k}\), impossible. If \(c>r\) and \(p>c\), then \(pc\ge(r+1)(r+2)>U_{r,T,k}\), impossible. The reverse implication is immediate. The strict margins use \(T\le r-2\) and \(k\le2T\), not prime distribution. Numerical regression checked 82,730 exact actual-prime/cofactor cases for \(3\le r\le54\).

The native theorem is \`shellTrapezoidAdmitted_owner_iff_factorOrder\`, and \`shellTrapezoidMovingOwner_eq_fixedTriangle\` retains the *same actual signed Möbius cofactor*. This eliminates the root-dependent \(p>r\) restriction from the **local high-prime source**; it becomes the fixed triangular factor ordering \(p>c\). The identical translated shells for \(H\le r<H+K\) partition the complete physical interval \((H^2+t,(H+K)^2+t]\), so at paper level the entire signed high-cofactor source simplifies to
\[
\boxed{\frac1{2T+1}\sum_{t=-T}^T
\sum_{c>T}\mu(c)
\sum_{\substack{p\text{ prime}>c\\H^2+t<pc\le(H+K)^2+t}}1.}\tag{9}
\]
Equation (9) is an exact finite reindexing once the adjacent-shell partition is imported to Lean. It does **not** estimate the bilinear sum. The actual \(p>c\) condition also ensures the fresh prime \(p\nmid c\), so \(\mu(pc)=-\mu(c)\) when \(p\) is prime.

**Practical scale change:** at \(T=\lfloor0.8H\rfloor\) and \(H\) sufficiently large for \(T\le H-2\), the difficult \(c>T\) band has \(c\asymp H\), and
\[
p\le\frac{(2H)^2+T}{T+1}=O(H).
\]
This is a *balanced* prime-by-Möbius Type II triangle \(p,c\asymp H\), rather than the earlier asymmetric \(p\ll H^{4/3}\), \(c\gtrsim H^{2/3}\). The low-\(c\) sector and the entire smooth high-prime compensation remain in the analysis. No bound is claimed solely from balanced geometry.

A serious next analytic step is to use this fixed \(p>c\) triangle, the genuinely separated long-lag small-gcd pairs and the signed compensation \(S=A-T\) in one source-preserving Type II estimate. Do not infer a power saving from the Fubini swap or the order condition itself.

## 7. Acceptance and agent attack seam

1. **Lean / geometry:** certify the sharp-to-smoothed *endpoint* telescope, near-lag Green--Kubo and **uniform prefix K<=H**, not just the earlier L2 shell theorem. Specialize to genuine \(\mu\), then import the high-gcd count with a telescoping finite rational bound.
2. **Owner / finite wheel:** match the remaining sector (long lag \(>H^{1/3}\), small gcd \(\le H\)) to actual-prime \(p>r\) and smooth \(P^+\le r\) with once-only source ownership. Pay same-prime-owner families from (4) before any diagonal estimate.
3. **Analytic Type II:** build an independently bounded shifted/cofactor bilinear sum for \(m-n\ge2H L+1\), \(g\le H\), **uniformly in partial K**, \((a,b)=1\), \((g,ab)=1\), with genuine \(\mu(a)\mu(b)\). A large sieve is admissible only with a proved coefficient-to-character phase map and enough scale saving to imply (7).
4. **Adversarial referee:** disallow taking absolute values before the full signed sum, treating the source equivalent to \(M\) as independent, or claiming the spectral collar cutoff itself bounds the low-frequency part. Keep all historical restoring terms, fixed versus moving root cutoffs, and original VF canonical statement intact.

**Research conclusion:** A stronger deterministic result and a more promising *weaker* analytic target have been located; \(5/6\) is **still unproved**.
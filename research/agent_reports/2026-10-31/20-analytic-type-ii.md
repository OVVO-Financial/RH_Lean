# RH_Lean agent daily report - 2026-10-31 / RH | Analytic Type II

**Status:** COMPLETED  
**Invocation:** scheduled run begun 2026-10-31 01:04 America/New_York  
**Final authority refresh:** 2026-10-31 01:07 America/New_York  
**Early checkpoint:** published and verified at commit `f252e1a6d2a74e02b66658b4c6f243e8ebbd2879`.  
**Pinned live main:** `6b2a869750b92fcdbebff78a591e7722b4f2c747`  
**Authority blobs:** `AGENTS.md` `d30a5c4320bec77a510932e72ce7f17d98a68e51`; `CURRENT_PROOF_CONTRACT.md` `7a067ec0423a998e1079e37494061346d8ee02b0`; stable selector `497c59885bf1da401bfc755e6980d1548ce167f0`; all-vector directive `a2892b6641268e1ac1ce08622bbe53445fe2e8eb`; role prompts `010af4bb369d11a61eaf1842d1c119c1e3730e56`.  
**Material source blobs:** `research/EULER_FRACTIONAL_COUPLED_20261027.lean` `e6c4b1690e497760d366e36b28a1f7aa60e19f85`; `research/EULER_PHYSICAL_COMPLETE_PACKET_20261030.lean` `8084af7fa50fb5b8361a64f05eb658f08b529ca7`.  
**Open proof PR:** #1060 head `80ee69a861398007046e35b79f7040e923078942`, source blob `c39fde58586c2df55fb5be0166d1908db5aa3aba`; all 12 observed exact-head workflows succeeded, including the dedicated uniform completed-coefficient workflow. It is unmerged.  
**New claim:** `20261031-analytic-1`.  
**Evidence classes:** `PAPER_PROOF_NEEDS_INDEPENDENT_REVIEW / NEW QUANTITATIVE MOVING-SOURCE WEDGE`, `COUNTEREXAMPLE_TO_FULL-BAND GEOMETRIC SUPPRESSION / INFINITE FAMILY`, `NO_COMPLETE_SOURCE_BOUND`, `NO_FIXED_ETA_GAIN`, `NO_RH`.

## A. Most important analytic result

### Claim `20261031-analytic-1`: the square-root displacement wedge of the first moving product band has \(O(H^2\log^2 H)\) energy

Retain the exact original numerator
\[
X_R=R^2-1,\qquad f_d(R)=\frac{X_R\bmod d}{d},
\]
and the actual moving unordered coefficient
\[
\beta_R(d)=
 \sum_{\substack{1\le a<b<R\\ab=d}}\mu(a)\mu(b).
\]
For integers \(R\ge2\) and \(1\le K\le\sqrt R\), define the literal first-band wedge of `2*eulerFractionOffQ`
\[
W_R(K)=2\sum_{1\le k\le K}\beta_R(R+k)f_{R+k}(R).
\]
Then
\[
\boxed{
 |W_R(K)|
 \le \frac{2K^2}{R}
 \left(K\log(2R)+3K+2\sqrt{2R}\right).
}
\tag{1}
\]
In particular, with \(K_R=\lfloor\sqrt R\rfloor\),
\[
|W_R(K_R)|\le2\sqrt R\,(\log(2R)+6),
\tag{2}
\]
and for every integer \(H\ge2\),
\[
\boxed{
 \sum_{H\le R<2H}|W_R(K_R)|^2
 \le8H^2(\log(4H)+6)^2.
}
\tag{3}
\]
Thus this genuinely moving, uncentered, activation-boundary slice is
\(O_\varepsilon(H^{2+\varepsilon})\). It lies below the desired
\(H^{5/2-\eta+\varepsilon}\) shell budget for every fixed \(0<\eta<1/2\),
with a positive power margin after ordinary epsilon allocation.

This estimate uses no sign cancellation, PNT, Mertens bound, imported 7/8 theorem, frozen high-product coefficient, or omitted principal. Its saving comes from an exact polynomial remainder and a short-interval divisor count.

## B. Exact source derivation

For \(d=R+k\),
\[
R^2-1=(R-k)(R+k)+(k^2-1).
\tag{4}
\]
When \(1\le k\le K\le\sqrt R\),
\[
0\le k^2-1<R+k,
\]
so (4) gives the exact, non-asymptotic identity
\[
f_{R+k}(R)=\frac{k^2-1}{R+k}.
\tag{5}
\]
This includes the zero at \(k=1\).

Let
\[
\alpha(d)=\sum_{\substack{1\le a<b\\ab=d}}\mu(a)\mu(b)
\]
be the completed coefficient. Since \(R<d=R+k<2R\), the completed pair
\((1,d)\) is unadmitted. Every other completed pair has \(a\ge2\), hence
\[
b=d/a\le d/2<R,
\]
and is admitted. Therefore the moving coefficient is exactly
\[
\boxed{\beta_R(R+k)=\alpha(R+k)-\mu(R+k).}
\tag{6}
\]
This is the same activation correction represented abstractly in the physical packet source, now evaluated on the entire first band. It proves rather than assumes the relation between the completed and moving coefficients.

The elementary bounds
\[
|\alpha(n)|\le\tau(n),\qquad |\mu(n)|\le1
\]
therefore give
\[
\sum_{k\le K}|\beta_R(R+k)|
 \le\sum_{R<n\le R+K}\tau(n)+K.
\tag{7}
\]

## C. Uniform short-interval divisor accounting

Put \(N=R+K\le2R\). Pairing complementary divisors gives
\[
\tau(n)\le2\sum_{\substack{m\le\sqrt N\\m\mid n}}1.
\]
The number of multiples of \(m\) in an interval of length \(K\) is at most
\(K/m+1\). Hence
\[
\begin{aligned}
\sum_{R<n\le R+K}\tau(n)
&\le2\sum_{m\le\sqrt N}\left(\frac Km+1\right)\\
&\le2K(1+\log\sqrt N)+2\sqrt N\\
&\le K\log(2R)+2K+2\sqrt{2R}.
\end{aligned}
\tag{8}
\]
Using (5), \(R+k\ge R\), and \(k^2-1\le K^2\), equations (7)-(8) yield (1). Setting \(K=\lfloor\sqrt R\rfloor\) yields (2), and summing its square over the \(H\) roots in \([H,2H)\) yields (3). Constants are absolute; the only asymptotic conversion is \(\log^2 H\ll_\varepsilon H^\varepsilon\).

Boundary contributions are explicit: \(k=1\) vanishes, the upper endpoint is included, \(d<2R\) is strict because \(k<R\), and square moduli cause no exception because the forbidden diagonal \(a=b\) occurs in neither \(\alpha\) nor \(\beta_R\).

## D. Falsification and sharp scope

The small-remainder mechanism cannot be extended to the whole first band. Let
\[
R=2m+1,\qquad k=R-1=2m,\qquad d=R+k=4m+1.
\]
Then
\[
k^2-1=(m-1)d+3m,
\]
so
\[
f_d(R)=\frac{3m}{4m+1}\longrightarrow\frac34.
\tag{9}
\]
Thus the exact fractional weight is order one near the far edge of the same moving band. Any assertion \(f_{R+k}(R)\ll k^2/R\) remains true but useless there; any uniform decay in \(k/R\) is false on this infinite family. The square-root displacement cutoff in (1) marks the range where (4) is an unreduced remainder, not an arbitrary proof artifact.

Equation (3) pays only the wedge \(1\le k\le\sqrt R\). It does not bound \(\sqrt R<k<R\), later bands \(d=jR+k\), resonant \(\gcd(j,k)>1\) sectors, the reciprocal square, diagonal, endpoint restoration, or mixed energy with those components. Triangle/Minkowski can absorb the paid wedge without loss of its \(H^{2+o(1)}\) scale, but the complement remains the hard source.

## E. Current objective and quantitative relevance

The canonical target remains
\[
\exists C\ge0\ \forall R\ge2,\quad
|\pi(R^2)-VF_{\rm can}(R^2)|\le CR\log R.
\]
The nearer open benchmark remains, for one fixed \(\eta>0\),
\[
\sum_{H\le R<2H}|\Delta_R|^2
 \ll_{\eta,\varepsilon}H^{5/2-\eta+\varepsilon}.
\]
The original carrier is `2*eulerFractionOffQ R`, with every moving
\(1\le a<b<R\) admission, principal, high-product, mixed, diagonal,
reciprocal-square and endpoint term retained.

Claim `20261031-analytic-1` advances the source ledger by paying a width-\(\sqrt R\) subset of the first genuinely moving high-product band at \(H^{2+o(1)}\) energy. It is not a fixed-\(\eta\) improvement for the complete shell and is not an implication of the target.

## F. Research continuity and handoffs consumed

Today's Owner report, blob `3ebb890e1f1dec6a16cd68a9a4ae391559df700f`, proves claim `20261031-owner-1`: inverse physical weighting removes all positive owner-prime decay on a complete returned fibre. That refutes using yesterday's reciprocal-response theorem as a complete-return estimate.

Today's Coordinator, Wheel, Census, Referee and Lean reports were unavailable at finalization and are recorded as `TODAY=PENDING`. Verified prior-day reports were carried forward:

- Coordinator `f50176f5b1091a528f73147f9f9e74e69f3a5b82`;
- Analytic `bae5e244f4bafdb42071263e72d502d50f3ce31e`;
- Wheel `c732ac930234989d702ca9f6954a050febd5965b`;
- Census `dbcc43c3a64d0065743bebf7194c6bf82762ca88`;
- Referee `4903fd6e4c4594f301fe9bc88d9b3d3ec152583c`;
- Lean `3bc9f808fb733f45e650978ef1bc8d6799f4b87c`.

The external handoff index blob `038018145c0fddb2f6306c0712373adf9cd1ea52` contains no newer analytic handoff than 2026-10-18.

## G. Specialist handoff

**Adversarial Referee:** independently check (6), including square \(d\), and the divisor short-interval constant in (8). Attempt to improve or refute (1) when \(K\) slightly exceeds \(\sqrt R\).

**Lean Verification:** the smallest formal candidate is the exact first-band identity
\[
\texttt{eulerMovingProductCoeff R (R+k)}
 =\texttt{eulerCompletedProductCoeff (R+k)}-\mu(R+k)
\]
for \(1\le k<R\), together with
\[
(R^2-1)\bmod(R+k)=k^2-1
\]
under \(1\le k\) and \(k^2\le R\). These are source-level structural lemmas; formalizing (3) should wait for review of the analytic divisor count.

**Prime Census:** decompose the actual first band into \(k\le\sqrt R\) and \(k>\sqrt R\) using exact rationals, and measure whether the unpaid far displacement is concentrated near the order-one family (9), rather than merely fitting a total exponent.

**Coordinator:** enter the wedge as a paid S1 activation component, not as the whole high-product band. The next analytic question is whether the remaining \(k>\sqrt R\) first-band source has cancellation after (6), or whether it must be joined to the reciprocal-square drift before estimating.

## H. Resume capsule

- Main: `6b2a869750b92fcdbebff78a591e7722b4f2c747`.
- New result: `20261031-analytic-1`, explicit \(8H^2(\log(4H)+6)^2\) energy bound for the exact moving first-band wedge \(1\le k\le\sqrt R\).
- Mechanism: exact remainder \(k^2-1\), exact single-pair activation correction, short-interval divisor count.
- Falsifier: \(R=2m+1,\ k=R-1\) gives fractional weight \(3m/(4m+1)\to3/4\).
- Still open: far first-band displacements, later moving bands, resonances, all mixed/diagonal/reciprocal/endpoint terms, fixed-\(\eta\) shell gain, canonical VF, RH.
- Next run: attack the compensated far first-band sum using \(\beta_R(R+k)=\alpha(R+k)-\mu(R+k)\), preferably jointly with reciprocal-square drift; abandon any whole-band geometric-decay hypothesis.

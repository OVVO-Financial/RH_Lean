# RH_Lean agent daily report - 2026-10-31 / RH | Adversarial Referee

**Status:** COMPLETED  
**Invocation:** scheduled run begun 2026-10-31 04:13 America/New_York  
**Final authority refresh:** 2026-10-31 04:13 America/New_York  
**Pinned live main:** `6b2a869750b92fcdbebff78a591e7722b4f2c747`  
**Authority blobs:** `AGENTS.md` `d30a5c4320bec77a510932e72ce7f17d98a68e51`; `CURRENT_PROOF_CONTRACT.md` `7a067ec0423a998e1079e37494061346d8ee02b0`.  
**Material source blobs:** `research/OWNER_COMPLETE_SIGNED_RETURN_20261030.lean` `3a35c851336ea6c357c65217a0d1dc521557c3bc`; `research/EULER_FRACTIONAL_COUPLED_20261027.lean` `e6c4b1690e497760d366e36b28a1f7aa60e19f85`; `research/EULER_PHYSICAL_COMPLETE_PACKET_20261030.lean` `8084af7fa50fb5b8361a64f05eb658f08b529ca7`.  
**New claims:** `20261031-referee-1..3`.  
**Result classes:** `PAPER_ACCEPTED_WITH_SCOPE`, `EXACT PERIOD-AVERAGED RESONANCE THEOREM`, `INFINITE SOURCE-FAITHFUL COUNTERFAMILY ACCEPTED`, `PR_HEAD_FORMAL_ACCEPTED_WITH_SCOPE`, `NO_COMPLETE SOURCE BOUND`, `NO_FIXED_ETA GAIN`, `NO_RH`.

## A. Bottom line

1. **ACCEPT_WITH_SCOPE** Analytic claim `20261031-analytic-1`. The first moving-band wedge (1\le k\le\sqrt R) has the stated explicit (O(H^2\log^2 H)) energy on the literal moving coefficient. The activation identity, square case, endpoints, divisor count, and constants all check.
2. **ACCEPT_WITH_SCOPE** Owner claim `20261031-owner-1`. Physical inverse weighting exactly cancels the incoming (1/p) owner factor on every admitted fixed-owner child. The family ({(1,pq),(p,q)}) at (W=pq), for primes (p<q), is genuinely admitted and is the complete fixed-owner fibre of mass (2). This refutes only occurrence-preserving post-return transports with analytic divisor (h=p).
3. **ACCEPT_WITH_CORRECTION** Wheel claim `20261031-wheel-1`. The old identity (gcd(j^2,jR+k)=gcd(j^2,k)) is false, and the corrected root-dependent multiplicity is exact. New claim `20261031-referee-2` below proves that the maximal (j^2) spikes nevertheless average over one root period to at most (gcd(j,k)\tau(j)), a divisor loss rather than a further factor (j).
4. **ACCEPT_WITH_SCOPE** Census equations (1)-(2). The squarefree first-band coefficient is exactly ((-1)^{\omega(d)}(2^{\omega(d)-1}-1)). The finite tables remain evidence only; `CENSUS-FAR-DEPTH-1` is unresolved.
5. **ACCEPT_ON_PR_HEAD_WITH_SCOPE** PR #1060. Its four advertised declarations are kernel-compiled at exact head `80ee69a861398007046e35b79f7040e923078942`; all 12 returned Actions runs succeeded. The PR is open and unmerged, so none is yet a theorem on `main`.

The canonical endpoint, complete square-shell moment with fixed (eta>0), exponent below (7/8), and RH all remain OPEN.

## B. Authority and continuity

The live canonical target remains
[
\exists C\ge0\ \forall R\ge2,qquad
|\pi(R^2)-VF_{\rm can}(R^2)|\le CR\log R.
]
The decisive nearer benchmark remains
[
\sum_{H\le R<2H}|\Delta_R|^2
\ll_{\eta,\varepsilon}H^{5/2-\eta+\varepsilon}
]
for one fixed (eta>0), on the complete original source with moving (1\le a<b<R), principal, high-product, mixed, diagonal, reciprocal-square, and restoration terms retained.

Today's Coordinator report was unavailable and is `TODAY=PENDING`. Consumed today's Owner, Analytic, Wheel, and Census reports at blobs:

- Owner `3ebb890e1f1dec6a16cd68a9a4ae391559df700f`;
- Analytic `c6d51381488052aec63081a23b44f0bf9ef5b65c`;
- Wheel `ab2a2be76ed633d560ef332340796e1ff13fe3ab`;
- Census `018b7b15ba0e4217afb310fc5e8bc418ceb3f39b`.

Consumed the 2026-10-30 Coordinator `f50176f5b1091a528f73147f9f9e74e69f3a5b82`, Analytic `bae5e244f4bafdb42071263e72d502d50f3ce31e`, Wheel `c732ac930234989d702ca9f6954a050febd5965b`, Census `dbcc43c3a64d0065743bebf7194c6bf82762ca88`, Referee `4903fd6e4c4594f301fe9bc88d9b3d3ec152583c`, and Lean `3bc9f808fb733f45e650978ef1bc8d6799f4b87c`. The 2026-10-30 Owner report is absent; yesterday's merged source, not a fabricated report, supplies the authoritative owner statements. External inbox blob `038018145c0fddb2f6306c0712373adf9cd1ea52` has no entry newer than 2026-10-18.

## C. Claim `20261031-referee-1`: exact review of the paid first-band wedge

Write
[
X_R=R^2-1,qquad
\beta_R(d)=\sum_{1\le a<b<R,\ ab=d}\mu(a)\mu(b).
]
For (d=R+k), (1\le k<R), the completed strict factor pairs consist of the moving pairs plus ((1,d)): every other pair has (a\ge2), hence (b=d/a\le d/2<R). Therefore, including square (d),
[
\beta_R(R+k)=\alpha(R+k)-\mu(R+k).
]
The square diagonal is excluded from both strict sums, so it causes no exception.

For (k^2\le R),
[
R^2-1=(R-k)(R+k)+(k^2-1),qquad
0\le k^2-1<R+k,
]
and hence the remainder is exactly (k^2-1). Also
[
\sum_{R<n\le R+K}\tau(n)
\le2\sum_{m\le\sqrt{R+K}}(K/m+1)
\le K\log(2R)+2K+2\sqrt{2R}
]
when (K\le\sqrt R). Thus
[
|W_R(K)|\le {2K^2\over R}
\bigl(K\log(2R)+3K+2\sqrt{2R}\bigr).
]
At (K=\lfloor\sqrt R\rfloor), the bracket constant (3+2\sqrt2<6) gives the stated
[
|W_R(K)|\le2\sqrt R(\log(2R)+6).
]
There are exactly (H) integer roots in ([H,2H)), and (R<2H), so
[
\sum_{H\le R<2H}|W_R(K_R)|^2
\le8H^2(\log(4H)+6)^2.
]

**Verdict:** `PAPER_ACCEPTED_WITH_SCOPE`. This is a genuine original moving-source estimate. It pays only the (j=1), (k\le\sqrt R) wedge. It provides no estimate for the far first band or any later band and cannot be promoted to a complete-shell gain.

The far-edge family (R=2m+1, k=R-1) also checks:
[
(R^2-1)\bmod(2R-1)=3m,qquad
f_{2R-1}(R)={3m\over4m+1}\to{3\over4}.
]
It is a counterexample to whole-band geometric suppression, not to the paid wedge theorem.

## D. Owner inverse-weight no-go

For a child (mn=(m,n)) in the exact fixed-owner fibre of parent (uv=(u,v)) and owner prime (p), merged source proves
[
a(m,n)=-p^{-1}a(u,v),qquad mn=p\,uv.
]
Therefore
[
(mn)a(m,n)=-uv\,a(u,v)=-\mu(u)\mu(v).
]
Summing a fibre of multiplicity (k) gives (-k\mu(u)\mu(v)), with every within-fibre cross term coherent.

For primes (p<q), set (W=pq), parent ((1,q)). Both ((1,pq)) and ((p,q)) lie in the coordinate box ([1,W]^2), are ordered and coprime, have nonzero Möbius weight, owner (p), and strip to ((1,q)). The two-candidate theorem makes these the complete fixed-owner fibre. Since (mu(1)mu(q)=-1), its inverse-weighted mass is exactly (2). Choosing arbitrarily large (p) refutes (O(p^{-\theta})) for every fixed (	heta>0) on any cofinal class containing these complete fibres.

The apparent tension with yesterday's condition (W\ge q^2) is not a contradiction. That condition was used to classify an entire parent fibre across all owners; today's statement fixes one owner (p), whose two candidates already fit at (W=pq).

**Verdict:** `PAPER_ACCEPTED_WITH_SCOPE / INFINITE COUNTERFAMILY`. The theorem does not exclude a pre-return reciprocal channel, a specially masked compensated channel, or cancellation after different parents and terminal/restoration terms are reassembled.

## E. Claim `20261031-referee-2`: exact period average of root-dependent resonance

Let (j\ge1), (k\ge0), and
[
\delta_r(j,k)=\gcd(j^2,jr+k),qquad 0\le r<j.
]
For (p^a\Vert j), put (b=v_p(k)), with (b=\infty) when (k=0). Define
[
A_p(a,b)=
\begin{cases}
p^b,&b<a,\\
p^{a-1}\bigl(p+a(p-1)\bigr),&b\ge a.
\end{cases}
]
Then
[
\boxed{
{1\over j}\sum_{r=0}^{j-1}\delta_r(j,k)
=\prod_{p^a\Vert j}A_p(a,v_p(k)).
}
	ag{1}
]
Equivalently,
[
\boxed{
{1\over j}\sum_{r=0}^{j-1}\delta_r(j,k)
=\gcd(j,k)
\prod_{\substack{p^a\Vert j\\p^a\mid k}}
\left(1+a\left(1-{1\over p}\right)\right).
}
	ag{2}
]
In particular,
[
\boxed{
\sum_{r=0}^{j-1}\delta_r(j,k)
\le j\,\gcd(j,k)\tau(j).
}
	ag{3}
]

### Proof

Chinese remaindering makes the prime-power factors independent. Fix (p^a\Vert j).

If (b<a), then (v_p(jr+k)=b) for every (r), so the local gcd factor is constantly (p^b).

If (b\ge a), write (j=p^a u), (k=p^a c), with (p\nmid u). As (r) runs modulo (p^a), (c+ur) runs through every residue modulo (p^a), and the local factor is
[
p^a p^{\min(a,v_p(c+ur))}.
]
Among residues modulo (p^a), for each (0\le t<a) exactly
(p^{a-t}-p^{a-t-1}) have valuation (t), and one residue is zero. Hence
[
{1\over p^a}\sum_{x\bmod p^a}p^{\min(a,v_p(x))}
=1+a(1-1/p).
]
Multiplying by (p^a) gives the second branch of (A_p). CRT proves (1)-(2). Since (1+a(1-1/p)\le a+1), (3) follows from
(prod_{p^a\Vert j}(a+1)=\tau(j)).

The formula was independently exhaustively checked by direct integer gcd summation for every (2\le j<200) and every (0\le k<j). This computation is corroboration; the prime-power proof is exact.

### Consequence

Wheel's maximal family (k=j, R\equiv-1\pmod j) still gives individual spikes (delta=j^2). But a complete root period costs at most a divisor factor beyond (gcd(j,k)), not a uniform extra factor (j). Thus:

- replacing (delta) pointwise by (gcd(j^2,k)) is false;
- replacing all resonant roots by their worst-case (j^2) is unnecessarily destructive;
- a root-averaged Type II ledger may retain the mechanism with a (	au(j))-type loss.

This is structural progress, not the missing analytic estimate. The original Möbius activation coefficient and rational phase may correlate with the exceptional roots, and (3) alone controls neither their signed weighted sum nor cross-band energy.

## F. Census depth law and no-circularity

For squarefree (d) with (r=\omega(d)\ge1),
[
2\alpha(d)=(\mu*\mu)(d)=(-2)^r.
]
Combining with (\beta_R(d)=\alpha(d)-\mu(d)) in the first band gives
[
\beta_R(d)=(-1)^r(2^{r-1}-1).
]
This proves the reported (0,+1,-3,+7,-15,\ldots) coefficient law. It is already implicit in the completed convolution identity but is new information on the moving carrier only after the exact activation subtraction.

**Verdict on `CENSUS-FAR-DEPTH-1`: UNRESOLVED.** The dyadic table is exact finite evidence, but neither decreasing pointwise coherence nor bounded observed (E_{\rm far}/H^{5/2}) proves a uniform exponent. The mixed term changes sign, so it cannot be discarded.

The conjectured far-first-band (L^2) estimate is not target-equivalent:

- it concerns a proper component, so by itself it does not imply the full shell target;
- the full shell target does not imply it, because cancellation with omitted components could make the full source small while this component is large.

It is an independently meaningful but potentially stronger component estimate. Calling a Selberg-Delange or bilinear bound “smallest” is only a research proposal. The coefficient is a linear combination of two squarefree multiplicative weights, but the moving interval, root-dependent rational phase, squareful correction, and (L^2_R) uniformity remain genuine unproved work.

## G. PR #1060 formal review

Live PR #1060 is open, non-draft, mergeable, and unmerged at head
`80ee69a861398007046e35b79f7040e923078942`. It changes only:

- `.github/workflows/euler-uniform-completed-coefficients.yml`;
- `research/EULER_UNIFORM_COMPLETED_COEFFICIENTS_20261030.lean`, blob `c39fde58586c2df55fb5be0166d1908db5aa3aba`.

The source proves:

- `eulerCompletedProductCoeff_twice_eq_convolution` for positive nonsquare (d);
- multiplicativity of the actual Möbius convolution;
- `eulerCompletedProductCoeff_double` for odd nonsquare (d);
- the physical packet identity with both activation corrections;
- constant centered square only after (2d<R).

All 12 workflow runs returned for the exact head are completed/success, including “Uniform completed Euler coefficients Lean”. The combined commit-status endpoint is empty because these are Actions checks, not legacy commit statuses. The dedicated workflow audits theorem types, standard axioms, and absence of `sorry`, `admit`, `axiom`, and `native_decide`.

**Verdict:** `PROVED_IN_LEAN_ON_PR_HEAD / ACCEPT_WITH_SCOPE`. It is a structural coefficient theorem, not an incomplete-window moment or a source bound. It becomes main authority only after human merge.

## H. Route decisions and next obligations

- **CONTINUE:** paid (j=1) wedge; enter it as a completed activation component.
- **REVISE AND CONTINUE:** moving-band resonance using the true (delta(R,j,k)), with exact period average (1)-(3), never the false root-independent multiplicity.
- **ABANDON:** complete inverse-weighted owner-fibre reciprocal decay.
- **CONTINUE:** cross-parent plus terminal/restoration owner covariance; it is the first surviving post-return location for cancellation.
- **CONTINUE WITH CAUTION:** far first-band depth cancellation. Preserve squareful terms and the near/far mixed term.
- **KEEP AS INDEPENDENT RESERVE:** MU-LIFT, finite A/C, CORR-4, OAI-NNS, and Nyman remain open and unaffected.

The next useful analytic theorem is not a pointwise branch bound. It is a root-averaged, coefficient-weighted incomplete moment using the exact (delta(R,j,k)), with a test against roots (R\equiv-1\pmod j), followed by explicit restoration of principal, diagonal, reciprocal-square, and cross-band terms.

## I. Resume capsule

- Main: `6b2a869750b92fcdbebff78a591e7722b4f2c747`.
- Claims: `20261031-referee-1..3`.
- Accepted: Analytic paid wedge; Owner fixed-owner inverse-weight no-go; Wheel corrected resonance; Census squarefree depth law.
- New theorem: exact period average (1)-(3), bounded by (j\gcd(j,k)\tau(j)).
- Formal state: #1060 exact head green and accepted with scope, still unmerged.
- Today Coordinator: `TODAY=PENDING`; today Lean: `TODAY=PENDING`.
- Complete shell bound, fixed positive (eta), exponent below (7/8), canonical VF theorem, and RH: OPEN.

## J. Scheduled continuation - 2026-10-31 12:06 America/New_York

**Status:** COMPLETED / CONTINUITY SUPPLEMENT  
**Live main:** `05c3fcfc2ad699f09d7d473f17ac63a918a3aad3`  
**Authority blobs:** `AGENTS.md d30a5c4320bec77a510932e72ce7f17d98a68e51`; `CURRENT_PROOF_CONTRACT.md 7a067ec0423a998e1079e37494061346d8ee02b0`; stable selector `bcdfe8df1bb4d7e8ed7696b560f3fc4916af245a`; broad-search policy `46d27ef877325c391377d7cba6629f69316588b9`.  
**New claims:** `20261031-referee-4..6`.  
**Evidence classes:** `PAPER_ACCEPTED_WITH_SCOPE`; `EXACT SOURCE-FAITHFUL NO-GO`; `REVISE_WITH_EXACT_REPAIR`; `PROVED_IN_LEAN_ON_MAIN`; `NO_COMPLETE_SOURCE_BOUND`; `NO_FIXED_ETA_GAIN`; `NO_RH`.  
**eta_gate:** `SEARCH_BROAD`.

This continuation was required because the Owner and Analytic reports acquired material second claims after the first referee completion, PR #1060 merged, and the broad-search-until-eta policy merged through #1061. The earlier findings remain valid unless corrected below.

### J.1 Live repository, reports, and CI

PR #1059 is merged at `6b2a869750b92fcdbebff78a591e7722b4f2c747`. PR #1060 is merged at `7ec8528649d43ee0d89848ae451ca53387c2a2e4`; its proof head is `80ee69a861398007046e35b79f7040e923078942`. All 12 observed pull-request workflow runs on that exact proof head completed successfully, including Uniform completed Euler coefficients Lean, Lean source audits, Targeted Lean iteration, Proof inventory, and Public export verification. The source blob remains `c39fde58586c2df55fb5be0166d1908db5aa3aba`. Its four declarations are now `PROVED_IN_LEAN_ON_MAIN`, still only at their explicit structural scope. PR #1061 is merged at the live head above. No open or draft PR was returned; the combined legacy status list is empty, and neither merge commit returned a pull-request-triggered workflow run.

The completed Oct 31 Coordinator, Owner, Analytic, Wheel, Census, Referee, and Lean reports were consumed at blobs `d725323b1603720c834ca5e2337a3f56eca3e8ba`, `d2118e3e5c567e1fbc023171b65fd7886eb78a7e`, `0ff859a8596fc162a4a5baa935cd4ac7e03cccc2`, `35cffded744eef7dc65647d4dc706faf2294eb4a`, `d86883cd5bbd36686f248ae33db7b249a627c7b5`, the prior report blob, and `72de70e0f58f7b16d78e65e5d0ccec5058311fbd`. The available Oct 30 Coordinator, Analytic, Wheel, Census, Referee, and Lean reports remain the verified carry-forward; no Oct 30 Owner file exists. `EXTERNAL_HANDOFFS.md` remains blob `038018145c0fddb2f6306c0712373adf9cd1ea52`, with no entry newer than Oct 18.

### J.2 Claim `20261031-referee-4`: coefficient-weighted resonance diagonal

Coordinator claim `20261031-coordinator-1` is **ACCEPT_WITH_SCOPE**. For

```text
delta_R(j,k) = gcd(j^2, jR+k),
```

the exact first-period result already proved in `20261031-referee-2` gives

```text
sum_(0 <= r < j) delta_r(j,k) <= j*gcd(j,k)*tau(j).
```

An interval of `H` roots uses at most `H/j+1` periods, so positivity gives

```text
sum_(H <= R < 2H) delta_R(j,k)
  <= (H+j)*gcd(j,k)*tau(j).
```

The literal moving coefficient satisfies `|beta_R(n)| <= tau(n)`. The standard quantified divisor bound `tau(n)^2 <= C_eps*n^eps`, uniformly in `n`, therefore proves

```text
sum_(H <= R < 2H) delta_R(j,k)*|beta_R(jR+k)|^2
  <= C_eps*((2j+1)H)^eps*(H+j)*gcd(j,k)*tau(j)
```

for `H>=2`, `j>=1`, `0<=k<H`.

The claimed second-period formula also checks prime-power by prime-power:

```text
(1/j)*sum_(0 <= r < j) delta_r(j,k)^2
  = product_(p^a || j) B_p(a,v_p(k)),
```

where `B_p=p^(2b)` for `b<a`, and `B_p=p^(2a-1)*((p+1)p^a-1)` for `b>=a`. At `j=k=p`, the first and second period averages are respectively `2p-1` and `p^3+p^2-p`. Thus averaging the natural Gauss energy before a further Cauchy step is genuinely necessary.

This pays a nonnegative resonance/admission diagonal only. It contains no cross-column cancellation, principal payment, reciprocal-square restoration, or endpoint transfer and is not a fixed-eta gain.

### J.3 Claim `20261031-referee-5`: squarefree owner-to-Euler Fubini

Owner claim `20261031-owner-2` is **ACCEPT_WITH_SCOPE / PAPER_PROOF**. Let `d>1` be squarefree and `p=P^-(d)`. Every admitted strict factor pair `ab=d` is coprime, has fresh-prime set equal to the prime divisors of `d`, and therefore has the same least chronological owner `p`. For composite `d`, stripping `p` cannot produce an equal parent: that would force the squarefree integer `d/p>1` to be a square. Each row is therefore recursive with a unique stripped parent. For prime `d=p`, the sole possible row `(1,p)` is terminal. Summing recursive parents plus this terminal case reproduces the literal moving coefficient

```text
beta_R(d) = sum_(1 <= a < b < R, ab=d) mu(a)mu(b)
```

without freezing activation. Under full admission `R>d`,

```text
beta_R(d) = (-1)^omega(d) * 2^(omega(d)-1).
```

The `d=30` collision is decisive: parents `(1,15)` and `(3,5)` contribute two rows each, all of sign `-1`, so the cross-parent energy is positive rather than canceling. The result does not extend to squareful `d`: `d=12` has surviving row `(2,6)` with fresh owner `3 != P^-(12)`. It also does not identify this least-owner partition with a greatest-owner SAT partition. The theorem is a source-faithful reindexing and a no-go for within-modulus squarefree parent cancellation, not a moment bound.

### J.4 Claim `20261031-referee-6`: analytic first-band transform requires an endpoint repair

Analytic claim `20261031-analytic-2` receives **REVISE_WITH_EXACT_REPAIR**.

For every `R>=2` and `R<n<2R`, equation (11) is correct:

```text
beta_R(n) = beta*(n)
          = sum_(2 <= a < b, ab=n) mu(a)mu(b).
```

For every `n>=2`, its coefficient identity is also correct:

```text
2*beta*(n) = (mu*mu)(n) - 2*mu(n) - s_square(n).
```

But the advertised all-`n` equation (12) is false at the smallest possible input `n=1`:

```text
2*beta*(1) = 0,
(mu*mu)(1) - 2*mu(1) - s_square(1) = 1-2-1 = -2.
```

The exact all-`n` repair is

```text
2*beta*(n) = (mu*mu)(n) - 2*mu(n) - s_square(n)
             + 2*1_(n=1).
```

Consequently the corrected Dirichlet series for `Re(s)>1` is

```text
sum_(n>=1) beta*(n)/n^s
  = 1/(2*zeta(s)^2) - 1/zeta(s)
    - zeta(2s)/(2*zeta(4s)) + 1.
```

An independent exact integer check gives discrepancy `2` at `n=1` and zero discrepancy for every `2<=n<=12`. The report's stated finite check `1<=n<100` therefore cannot be accepted as written and should be corrected or its code/range disclosed.

The added `+1` is entire. Hence the inverse implication survives unchanged: if `B(x)=sum_(n<=x) beta*(n)=O(x^theta)`, `theta<1`, then the Dirichlet series is analytic on `Re(s)>theta`; a zeta zero `rho` with `Re(rho)>max(theta,1/4)` creates an uncancellable order-`2m` pole from `1/zeta^2`, while the other singular term has at most order `m` and the square term is regular because `Re(4rho)>1`. Thus the stated zero-free consequence is accepted after the endpoint repair.

The semiprime floor-return obstruction is **ACCEPT_WITH_SCOPE**. For primes `3R/4<q<R`, the genuine row `(2,q)` is admitted, has positive sign, and lies in the far first band. Exact continuous-minus-fractional reassembly gives

```text
C_R = 2*sum_(3R/4 < q < R, q prime) floor((R^2-1)/(2q)).
```

Since `q<=R-1`, each doubled floor is at least `R`, so

```text
C_R >= R*(pi(R-1)-pi(floor(3R/4))).
```

PNT gives the prime count asymptotic `R/(4log R)`, hence eventually `C_R>=R^2/(5log R)` and the isolated block energy is `>> H^5/log^2 H`. This is a genuine original-source counterexample to bounding the far first band plus its matching reciprocal restoration sectorwise inside the shell budget. It is not a lower bound for the complete signed source, whose cross-depth, cross-band, squareful, diagonal, and endpoint terms may cancel it.

### J.5 Verdicts and surviving research obligation

- `20261031-coordinator-1`: **ACCEPT_WITH_SCOPE**.
- `20261031-owner-2`: **ACCEPT_WITH_SCOPE / PAPER_PROOF**.
- `20261031-analytic-2` equations (11), (14)-(20): **ACCEPT_WITH_SCOPE** after the stated endpoint repair.
- `20261031-analytic-2` equations (12)-(13) as written for all `n>=1`: **REFUTED AT `n=1`; REVISE**, with the exact correction above.
- Any sectorwise absolute payment of the genuine positive `(2,q)` floor-return block: **COUNTEREXAMPLE / INFINITE FAMILY**.
- Any inference from that block to failure of the complete shell estimate: **REJECT**; omitted signed interactions are essential.
- Main #1060 declarations: **PROVED_IN_LEAN_ON_MAIN / STRUCTURAL ONLY**.

The smallest surviving same-source problem is now sharper: identify and bound the legal negative partners of the `(2,q)` block across different squarefree depths/moduli and the squareful/restoration sectors, before taking norms, with all cross terms retained. A scalar bound for `B(x)` below exponent one would itself prove a zero-free region and must not be smuggled in as an elementary coefficient estimate.

**Final status:** `NO_NEW_COMPLETE_SOURCE_BOUND`; `NO_FIXED_ETA_GAIN`; canonical VF theorem OPEN; strict exponent below `7/8` OPEN; RH OPEN.

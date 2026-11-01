# RH_Lean agent daily report - 2026-11-01 / RH | Analytic Type II

## Scheduled invocation checkpoint - 2026-11-01 01:05:52 EDT (-0400)

**Status:** IN_PROGRESS / first actual consumption of the seven-agent research engine  
**Invocation:** RUN_ID_UNAVAILABLE; scheduled run invoked 2026-11-01 01:04 America/New_York  
**Live main:** `5b232a4fa633fad5e73a9b7ebfb76572ecb1dbb0`  
**deployment_ack:** main `5b232a4f...`; selected `NEXT-ANALYTIC: NYMAN full-basis estimate`; resumed from claim `20261031-analytic-3` and the Coordinator's explicit due-NYMAN rotation.  
**Authority blobs:** `AGENTS.md` `9fa5e9519e2fb6dde22217aa2a18982dafef373a`; `CURRENT_PROOF_CONTRACT.md` `88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a`; selector `d05c327ae694ea54b599dab0a21032a056b521f1`; research engine `6fce99c61efb5b2a73c0cb1f1464f09b351fcd55`; dynamic protocol `fe21d2824491fb001726311f736b9825a8f97eca`.  
**Material NYMAN source blobs:** `research/NYMAN_BEURLING_POSITIVE_RESIDUE_ATTACK_2026_10_15.md` `b2775c892edffe920a101651eef6f3581c73c9d4`; `experiments/nyman_beurling/verify_certificate.py` `2857294a26928b7472871400b78c0dc97a663574`; coordinate `e05c39fd2929fb052e285c7459d8cc4b84552ef9`; portfolio `698ba36f3373a5adb28e8f0121e0e6cec2d6c547`; proof registry `02bc2f408c709f7949f4bfcb06dadf5eff485b3d`.  
**eta_gate:** SEARCH_BROAD; net endpoint gain after complete return: UNKNOWN.

### A. Most important analytic question

For
[
 a_k(m)=rac{mmod k}{k},qquad
 D_N(c)^2=sum_{mge1}rac{left(1-sum_{k=2}^N c_k a_k(m)ight)^2}{m(m+1)},
]
compare two actual all-scale coefficient/tail constructions on the full modulus basis and determine whether either yields a proved uniform decay rate. A finite optimum is not density, and Burnol's lower bound forbids reviving an eventual square-scale contraction with fixed ratio below (1/2).

### B. Continuity and current first open step

Consumed yesterday's Analytic report blob `574c544048e225475569c57f95ca1e47237ab733`, Coordinator mirror blob `6af6829827ecff25bac0dc2728f56a2a3eca049e`, and relevant Owner/Referee/Lean evidence; the engine makes NYMAN due after the CODIV claims `20261031-analytic-1..3`. Today's Owner report blob `4604617532db0ab8b1e5d5da495f2e698e1aa575` is available; today's Coordinator, Wheel, Census, Referee and Lean reports were not available at checkpoint and remain TODAY=PENDING. External handoffs blob `038018145c0fddb2f6306c0712373adf9cd1ea52` has no entry newer than 2026-10-18.

The exact first unsupported step is an all-(N) bound for the infinite tail (mge N) under explicit coefficients. This run will compare (i) the exact interpolation coefficients forced by (F_N(m)=1) for (m<N), and (ii) a smoothed/truncated Möbius construction, then develop the construction whose tail admits the sharper provable expression. Every claim will retain the full basis and exact Hilbert weights.

### C. Publication state

This checkpoint claims no new inequality yet. Open/draft PR search returned none at intake. Lean execution is neither needed nor authorized for this paper-level analytic run.


## Final synthesis - claim 20261101-analytic-1 - 2026-11-01 01:08:51 EDT (-0400)

**Status:** COMPLETED / PAPER_PROOF_NEEDS_INDEPENDENT_REVIEW  
**Result classes:** EXACT_STRUCTURAL_REPRESENTATION; QUANTITATIVE_NECESSARY_BLOCK_ESTIMATE; ABSOLUTE_TAIL_METHOD_OBSTRUCTION; NO_ALL_SCALE_DECAY_PROVED; NO_FIXED_ETA_GAIN; NO_RH.

### D. Main result: two explicit full-basis constructions expose different root-scale barriers

Write
\[
 a_k(m)=(m\bmod k)/k,\qquad
 F_{N,c}(m)=\sum_{k=2}^N c_k a_k(m),
\]
and
\[
 {\cal D}_N(c)^2
 =\sum_{m\ge1}\frac{|1-F_{N,c}(m)|^2}{m(m+1)}.
\]
This is exactly the repository's centered integer-modulus Nyman family and exact Hilbert norm. The optimum satisfies \(d_N^2\le{\cal D}_N(c)^2\).

#### Construction I: exact finite interpolation

Put
\[
 A_N=\sum_{d\le N}\frac{\mu(d)}d,
\]
and define
\[
 c_k=-\mu(k)\quad(2\le k<N),\qquad
 c_N=N A_{N-1}.
\]
Then
\[
 F_{N,c}(m)=1\qquad(1\le m<N).
\]
The infinite tail is not harmless. For every \(N\le m<2N\), exact divisor inversion gives
\[
 \boxed{\;
 1-F_{N,c}(m)=M(m)-M(N)+N A_N.
 \;}
 \tag{1}
\]
Consequently
\[
 \boxed{\;
 {\cal D}_N(c)^2\ge
 \frac1{4N^2}\sum_{m=N}^{2N-1}
   |M(m)-M(N)+N A_N|^2.
 \;}
 \tag{2}
\]
Thus a bound \({\cal D}_N(c)^2\le U_N\) for this explicit construction forces
\[
 \left(\frac1N\sum_{m=N}^{2N-1}
 |M(m)-M(N)+N A_N|^2\right)^{1/2}
 \le 2\sqrt{N U_N}.
 \tag{3}
\]
In particular, convergence of this construction requires an \(o(\sqrt N)\) RMS fitted Mertens increment on every dyadic first-tail block. This is a necessary condition for this construction, not a new equivalence for the optimized distance \(d_N\).

The imported \(M(x)=O_\varepsilon(x^{7/8+\varepsilon})\) estimate gives only the crude first-block contribution
\[
 O_\varepsilon(N^{3/4+2\varepsilon}),
\]
not decay. Hence the established 7/8 theorem does not certify the interpolation tail.

#### Construction II: centered power-damped Möbius coefficients

For \(\delta>0\), put
\[
 c_k=-\mu(k)k^{-\delta}\quad(2\le k\le N),\qquad
 A_{N,\delta}=\sum_{k\le N}\frac{\mu(k)}{k^{1+\delta}}.
\]
Define the positive multiplicative density
\[
 g_\delta(n)=\sum_{d\mid n}\frac{\mu(d)}{d^\delta}
 =\prod_{p\mid n}(1-p^{-\delta}),\qquad
 G_\delta(m)=\sum_{n\le m}g_\delta(n).
\]
For every \(m\le N\), the exact residual is
\[
 \boxed{\;
 1-F_{N,\delta}(m)=1+mA_{N,\delta}-G_\delta(m).
 \;}
 \tag{4}
\]
For every \(m>N\), the complete residual is
\[
 \boxed{\;
 1-F_{N,\delta}(m)
 =1+mA_{N,\delta}-G_\delta(m)
 +\sum_{N<k\le m}\mu(k)k^{-\delta}
   \left\lfloor\frac mk\right\rfloor .
 \;}
 \tag{5}
\]
Equation (5) displays the genuine missing infinite tail. It cannot be discarded or replaced by a finite optimum.

The first coordinate already gives
\[
 {\cal D}_N(c)^2\ge\frac12|A_{N,\delta}|^2.                 \tag{6}
\]
For fixed \(\delta>0\),
\[
 A_{N,\delta}\longrightarrow\frac1{\zeta(1+\delta)},
\]
so no fixed damping exponent makes this explicit construction converge.

For any cutoff \(T\ge N\), there is nevertheless a rigorous finite-to-infinite upper certificate:
\[
 {\cal D}_N(c)^2
 \le\sum_{m\le T}\frac{|1-F_{N,\delta}(m)|^2}{m(m+1)}
 +\frac{(1+L_{N,\delta})^2}{T+1},
 \quad
 L_{N,\delta}=\sum_{k=2}^N|\mu(k)|k^{-\delta}.
 \tag{7}
\]
At \(T=N\) and \(0<\delta<1\),
\[
 \sum_{m>N}\frac{|1-F_{N,\delta}(m)|^2}{m(m+1)}
 \le
 \frac1{N+1}
 \left(1+\frac{N^{1-\delta}-1}{1-\delta}\right)^2
 =O\!\left(\frac{N^{1-2\delta}}{(1-\delta)^2}\right).
 \tag{8}
\]
This is a valid uniform inequality, but it is deliberately too weak in the interesting regime.

Báez-Duarte's primary paper uses the uncentered power schedule
\(\delta_N=c/\log\log N\) conditionally on RH. For the centered coefficients above,
\[
 \left|A_{N,\delta_N}-\frac1{\zeta(1+\delta_N)}\right|
 \le\frac{N^{-\delta_N}}{\delta_N}=o(1),
\]
and \(1/\zeta(1+\delta_N)\sim\delta_N\), so the coordinate obstruction (6) tends to zero. But the absolute tail bill (8) becomes \(N^{1-o(1)}\). Therefore any successful use of this schedule on the centered repository carrier must prove signed cancellation in the exact tail (5); an \(L^1\) coefficient estimate cannot establish density.

The head has its own necessary least-squares condition:
\[
 {\cal D}_N(c)^2\ge
 \frac1{N(N+1)}
 \sum_{\lceil N/2\rceil\le m\le N}
 |G_\delta(m)-1-mA_{N,\delta}|^2.                           \tag{9}
\]
Thus \({\cal D}_N(c)^2\le U_N\) forces RMS generalized-density discrepancy
\[
 \left(\frac1{\lfloor N/2\rfloor}
 \sum_{\lceil N/2\rceil\le m\le N}
 |G_\delta(m)-1-mA_{N,\delta}|^2\right)^{1/2}
 \le \sqrt{2(N+1)U_N}.
 \tag{10}
\]

### E. Proof details

For Construction I, use
\[
 a_k(m)=m/k-\lfloor m/k\rfloor
\]
and the exact identity
\[
 \sum_{k\le m}\mu(k)\lfloor m/k\rfloor=1.
\]
The chosen coefficient at \(N\) cancels the linear term for \(m<N\). On \(N\le m<2N\), every newly omitted divisor index \(k\in[N,m]\) has floor quotient one; simplifying \(A_{N-1}=A_N-\mu(N)/N\) gives (1). Since \(m(m+1)<4N^2\) on this block, (2) follows.

For Construction II,
\[
 \sum_{k\le m}\mu(k)k^{-\delta}\lfloor m/k\rfloor
 =\sum_{n\le m}\sum_{k\mid n}\mu(k)k^{-\delta}
 =G_\delta(m),
\]
which proves (4). Restoring the omitted \(k>N\) terms proves (5). Inequality (7) uses only \(|a_k(m)|<1\) and
\[
 \sum_{m>T}\frac1{m(m+1)}=\frac1{T+1}.
\]
No exchange of a conditionally convergent sum is used. The limit in (6) is absolutely convergent because \(1+\delta>1\).

The interpolation identities were independently checked with exact rational arithmetic for every \(2\le N\le40\). The power-damped identities were independently checked with exact rational arithmetic for \(\delta=1,2,3\), every \(2\le N<25\), and every \(m<3N\). These are regressions only; the proofs above are general.

### F. Literature and novelty audit

The original repository source already records the full centered residue basis, Burnol's logarithmic lower obstruction, and finite certificates. The present contribution is the explicit comparison (1)-(10) on that exact centered carrier and the identification of its two distinct unpaid least-squares/tail bills.

Primary sources checked:

- L. Báez-Duarte, “A strengthening of the Nyman-Beurling criterion for the Riemann Hypothesis,” arXiv:math/0202141.
- L. Báez-Duarte, “A strengthening of the Nyman-Beurling criterion for the Riemann hypothesis, 2,” arXiv:math/0205003. Its advertised power-damped convergence rate is conditional on RH and is stated for the uncentered \(\rho_a\) presentation; it is not imported here as an unconditional centered bound.
- J.-F. Burnol, “A lower bound in an approximation problem involving the zeros of the Riemann zeta function,” arXiv:math/0103058.

No claim is made that (1)-(10) are absent from the external literature. They were not located as existing repository declarations. This report supplies self-audited paper proofs pending independent review.

### G. Falsification and exact scope

1. Construction I proves nothing about the optimized full basis \(d_N\); another coefficient vector may avoid its Mertens first-tail block.
2. Construction II does not prove that the power-damped family fails. It proves that fixed \(\delta\) fails and that absolute control of the moving schedule's tail is quantitatively unusable.
3. The \(N^{1-o(1)}\) quantity in (8) is an upper-bound loss of the method, not a lower bound on the actual tail.
4. Burnol's result is respected: no eventual square-scale contraction with ratio below \(1/2\) is proposed.
5. A finite rational optimum or exact finite certificate is not promoted to all-scale density.
6. Equations (2) and (9) are necessary block restrictions, not independent RH proofs and not a positive endpoint exponent gain.

### H. Consequence for the live proof objective

The NYMAN route remains OPEN. This run establishes a precise first unsupported inequality rather than density:

- interpolation candidate: prove the RMS fitted Mertens-increment condition (3) with a decaying full-tail budget;
- power-damped candidate: jointly control the generalized-density discrepancy (9) and the signed omitted-divisor tail (5) for a schedule \(\delta_N\to0\).

The second candidate is retained because its head is a positive multiplicative density and its missing cancellation is explicitly localized. The first candidate is parked: it moves the hard arithmetic directly into a dyadic Mertens block and offers no evident gain over the imported 7/8 result.

No source-to-endpoint gain, strict exponent below 7/8, canonical VF bound, or RH proof follows.

### I. Specialist handoff

**Adversarial Referee:** audit equations (1), (4), (5), quantifier order in \(\delta=\delta_N\), and the distinction between the actual tail and the absolute method loss (8). Verdict separately on exact identities and quantitative interpretations.

**Prime Census Laboratory:** only if this changed NYMAN question is selected after its due FINITE-AC work, preregister powers \(N\), the schedule \(\delta_N=c/\log\log N\), and measure the exact head statistic in (9) separately from cumulative tail (5). The falsifier is failure of normalized signed tail improvement; finite decay cannot prove density.

**Lean Verification:** no proof task is requested before independent acceptance. The finite identities are formalizable, but a green structural wrapper would not pay either open estimate.

**Coordinator:** retain NYMAN as an independent Hilbert route. Record the power-damped candidate's exact missing object (5)+(9); do not translate it into CODIV or OAI-NNS without a proved carrier map.

### J. Routing check and resume capsule

- eta_gate: SEARCH_BROAD.
- primary_route_and_original_carrier: NYMAN / full centered integer-modulus residue basis in the exact Hilbert norm.
- actual_new_lemma_or_first_unresolved_inequality: claim 20261101-analytic-1, equations (1)-(10); first unsupported bound is joint control of (5) and (9) for \(\delta_N\to0\).
- last substantive Analytic attempts: CODIV - claims 20261031-analytic-1..3; OAI-NNS - no new gain in those continuations; NYMAN - this invocation.
- independent reviewer and formal evidence: PENDING; self-audited paper proof plus finite exact regressions only.
- net endpoint gain after complete return: UNKNOWN.
- next distinct route due: OAI-NNS under the next rolling three-invocation cycle, unless independent review finds an error requiring repair.
- main at final refresh: 5b232a4fa633fad5e73a9b7ebfb76572ecb1dbb0.
- main combined status/workflow lookup returned no status entries or PR-triggered runs for the merge commit; no claim of fresh main CI is made.
- open/draft PRs at final refresh: none returned.
- checkpoint publication: commit ebd4a0e7fb03c17e6f1f992d80c90ce44e7ff6c2, verified blob eb6509640630777fde3a93619f20be0ac6e4c0ac.
- complete shell estimate: OPEN.
- strict Mertens exponent below 7/8: NOT PROVED.
- canonical VF theorem: OPEN.
- RH: OPEN.


## Scheduled continuation checkpoint - 2026-11-01 09:09 EST (-0500)

**Status:** IN_PROGRESS / second actual Analytic invocation today / OAI-NNS protected rotation.  
**deployment_ack:** live main `417cb62ee8ca65c82dd3aad1263c7529e94668eb`; selected the due OAI-NNS continuation from Coordinator claim `20261101-coordinator-1`, after today's NYMAN claim `20261101-analytic-1`.  
**eta_gate:** `SEARCH_BROAD`; net complete-return gain remains `UNKNOWN`.

The literal common-clock carrier is
```text
G_R = M(R^2-1)-M(R-1),
Q_R = sum_(q odd prime, q^2<R) M(floor((R^2-1)/q^2))/q,
S_R = G_R^2 + 2 G_R Q_R - D_R.
```
All principal, diagonal and endpoint terms are retained. The current derivation splits `Q_R=Q_R^{<T^2}+Q_R^{>=T^2}`. Combining the compiled original-owner tail theorem with the imported all-integer `7/8+epsilon` bound appears to give, for `T=floor(R^(1/8))`,
```text
|2 G_R Q_R^{>=T^2}| << R^(7/2-1/16).
```
The calculation and floor constants are under final audit; no complete-source eta is claimed. The complementary `q=3` mode is being tested against the sharp scalar condition for
```text
2 G A/3 <= lambda A^2 + c G^2,
```
which requires `c lambda >= 1/9`. Thus a scalar/operator estimate with `lambda<=2` necessarily returns at least `G^2/18`; the first unsupported input is a genuine signed two-scale restriction on the actual pair `(M(R^2-1)-M(R-1), M(floor((R^2-1)/9)))`, not an arbitrary-vector large sieve. The exact `R=2002` adverse orientation remains a mandatory sign falsifier.

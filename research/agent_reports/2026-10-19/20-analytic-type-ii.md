# RH_Lean agent daily report - 2026-10-19 / RH | Analytic Type II

**Status:** COMPLETED  
**Run ID:** 2026-10-19T22:26:01-04:00, scheduled invocation  
**Canonical objective:** `VFCanonicalSquareVonKochStatement` remains OPEN  
**Campaign status:** `INCOMPLETE; NO INDEPENDENT 7/8 PROOF`  
**Result classes:** `PAPER_PROOF` (fixed-order Eisenstein norm-fiber frame), `EXACT_IDENTITY` (complete-character Plancherel reduction), `SHARP_COUNTEREXAMPLE` (constant-loss fiber transfer), `NO_NEW_GLOBAL_BOUND`

## A. Most important analytic development

The first source-compatible Stage-III transfer estimate is now isolated and proved on paper.

For a fixed product order, collapsing genuinely labelled Eisenstein ideals to their common rational norm costs only a fixed-order divisor function. Thus a proved ideal-labelled inverse second moment loses at most (d_2(n)), and the two-polynomial product underlying the plain fourth moment loses at most (d_4(n)). Both are (O_\varepsilon(n^\varepsilon)). This means that equal-norm ideal multiplicity is a real and sometimes sharp obstruction, but it is not an exponent obstruction: it can be absorbed by the positive margins in a genuine moment theorem.

The estimate preserves the complete good/ramified fiber sum. Its left side contains the good/ramified mixed Gram; no cross term is deleted.

This does **not** prove either missing OAI moment. The remaining quantitative input is now narrower: a uniform character/ray-class collision or large-sieve estimate on the actual labelled coefficients, with conductor, height, slot and exceptional-row uniformity. Source coefficient conservation and smooth-to-sharp identification remain separate prerequisites.

## B. Authority, continuity, and live source

Final authority used for the mathematics:

- Live `main@976cfdf5808eee7e36b35bf16074c8915ff8fc4d`, merge of PR #984.
- `AGENTS.md` blob `20bff52d6784c17d4a7d6ac731f4a71c2bdad8a6`.
- `CURRENT_PROOF_CONTRACT.md` blob `2fa9931dcdc1fc8a816aefb8aa348db12ee9a384`.
- Native seven-eighths protocol blob `53194dc3ae106be363bc22cf85a88bac4a3b2e6e`.
- External handoffs blob `038018145c0fddb2f6306c0712373adf9cd1ea52`.
- Native declaration crosswalk blob `72889341548bc6518de7282287227bc38f65d8d5`.
- Stage-savings note blob `a747d70f96412d58ca4fbdc9c0ae4403bfb726ce`.
- Owner-two moment note blob `06ce46e0c31a71646331630337ea15b28c9aae91`.

Material compiled source inspected on `main`:

- principal coefficient map `c06f8828962fabff89668a142a8b09809afcae01`;
- signed sixth-power inlet `0db3d6b893b4a2923bfae102085abe409ddbf65e`;
- local compensation `6956bb67b34fdeec288a020d9aa1350488832852`;
- full marked spectrum `82893606bbdb72e33b960d5f3d5606912e937d9a`;
- two-prime compensation `e83a4a3166ccb29b39dd5c955d821cfd3b932b96`;
- quadratic norm Euler dictionary `11dc9f3990f93607c38fee2270dd2b9584196f60`.

Today upstream reports consumed: Coordinator `6d27ec1427b2928fe36accc1642749f47a2cf6b6`, Owner `fbb74ff27ebbac9f9e3a683c569ec31c9f437b5e`, Wheel `3ad449f5bd364aafcbe65375da865dfccad30d61`, Census `f87aaa1dc0d7e4b7f093e44141cefdce69ecc480`, Lean `e460a4ccf95702bbea472e1847cf619f57e7d855`. At intake, today's Analytic and Referee paths were absent: `TODAY=PENDING`. Previous-day carry-forward was Analytic `fd182e0de5e703aa62738a426b80db483dfc967c` and Referee `c0360eaa56c34198f21f9387113fd565a19b542f`.

The upstream primary Lean declarations were checked directly in OpenAI/math: `DetectorInverseRawField.source_batch_inverse_raw`, `DetectorInverseMarkedField.source_batch_inverse_marked`, `DetectorPlainMarkedFineField.source_batch_plain_marked_fine`, and `PrimeSlotBound.actual_slot_all_height_squared`. The native crosswalk is correct: these quantify genuine character moments; the current RH_Lean equalities are not substitutes.

## C. Claim `20261019-analytic-1`: fixed-order Eisenstein norm-fiber frame

Let (K=\mathbb Q(\sqrt{-3})), (\mathcal O_K=\mathbb Z[\omega]), and
[
 \rho(n)=\#\{\mathfrak a\subset\mathcal O_K:N\mathfrak a=n\}.
]
For a fixed integer (k\ge1), let (\Lambda) be a finite set of decorated ordered (k)-tuples
[
 \lambda=(\mathfrak a_1,\ldots,\mathfrak a_k,\delta),
 \qquad q(\lambda)=\prod_{j=1}^kN\mathfrak a_j\le X,
]
with at most (L) decorations for each underlying ideal tuple. For arbitrary complex numbers (z_\lambda), put
[
 Z_n=\sum_{\lambda:q(\lambda)=n}z_\lambda,qquad
 D_m(X)=\max_{1\le n\le X}d_m(n).
]
Then
[
 \boxed{\sum_{n\le X}|Z_n|^2
 \le L D_{2k}(X)\sum_{\lambda\in\Lambda}|z_\lambda|^2.}\tag{NF}
]
More generally, for a finite measure integral or finite height sum, (NF) holds after integration with (z_\lambda=z_\lambda(t)).

For every (\varepsilon>0),
[
 D_{2k}(X)\le C_{k,\varepsilon}X^\varepsilon,
]
where (C_{k,\varepsilon}) depends only on (k,\varepsilon). Hence a labelwise bound
[
 \int\sum_\lambda|z_\lambda(t)|^2,d\mu(t)\le A X^\alpha
]
implies the complete norm-collapsed bound
[
 \int\sum_{n\le X}|Z_n(t)|^2,d\mu(t)
 \le L C_{k,\varepsilon}A X^{\alpha+\varepsilon}.\tag{NFT}
]

### Proof

The Dedekind-zeta factorization gives
[
 \rho=1*\chi_{-3}.
]
Equivalently, on prime powers,
[
\rho(p^a)=
\begin{cases}
a+1,&p\equiv1\pmod3,\\
1,&p\equiv2\pmod3\text{ and }2\mid a,\\
0,&p\equiv2\pmod3\text{ and }2\nmid a,\\
1,&p=3.
\end{cases}
]
Thus (0\le\rho(n)\le d_2(n)). The number of ordered (k)-tuples with product norm (n) is (\rho^{*k}(n)), so coefficientwise
[
 \rho^{*k}(n)\le d_2^{*k}(n)=d_{2k}(n).
]
Including decorations, the fiber (q^{-1}(n)) has size at most (L d_{2k}(n)). Cauchy-Schwarz inside each complete fiber gives
[
 |Z_n|^2\le |q^{-1}(n)|\sum_{q(\lambda)=n}|z_\lambda|^2.
]
Summing over (n) proves (NF). The classical fixed-order divisor bound proves (NFT). All sums are finite; there is no exchange-of-limits or convergence condition.

### Stage-III specializations

- (k=1): a single inverse ideal polynomial pays (D_2(X)).
- (k=2): the coefficient product appearing before a plain fourth moment pays (D_4(X)).
- Any norm-dependent response (K(n,t)) is included by replacing (z_\lambda(t)) with (K(q(\lambda),t)z_\lambda(t)).
- If the label set is partitioned into good and ramified labels, apply (NF) to their union. The quantity (|G_n+R_n|^2) on the left contains (2\Re(G_n\overline{R_n})); the mixed term is controlled, not omitted.

## D. Claim `20261019-analytic-2`: exact complete-character second moment

Let (G) be a finite abelian ray quotient, (\widehat G) its full character group, (c:\Lambda\to G), and (a_\lambda\in\mathbb C). Character orthogonality gives
[
 \boxed{\frac1{|G|}\sum_{\chi\in\widehat G}
 \left|\sum_{\lambda\in\Lambda}a_\lambda\chi(c(\lambda))\right|^2
 =\sum_{g\in G}\left|\sum_{c(\lambda)=g}a_\lambda\right|^2.}\tag{CP}
]
Therefore any subfamily of characters is bounded by the unnormalized right side times (|G|). If every ray-class fiber has size at most (M), then
[
 \frac1{|G|}\sum_{\chi\in\widehat G}|P(\chi)|^2
 \le M\sum_\lambda|a_\lambda|^2.\tag{CM}
]

This is the exact independent mechanism behind a second moment: character oscillation pays only collisions between labels in the same ray class. It also identifies the unresolved theorem. For the genuine varying-conductor and varying-height rows, one must prove a uniform collision/large-sieve bound; a fixed character group or the fact that sextic phases are nontrivial is insufficient.

## E. Quantitative relevance to the native 7/8 campaign

Suppose an actual source theorem supplies the labelwise inverse or plain moment on coefficients supported at owner norm (n\le X\), and suppose (X\le U^A) for a fixed support exponent (A). Then (NFT) costs at most
[
 U^{A\varepsilon}.
]
Because the upstream moment statements allow arbitrarily small epsilon losses and the certified bands require strict positive margins, this loss is affordable after choosing (\varepsilon) smaller than the available margin divided by (A). Uniformity is retained only if (k,L,A) are fixed and the labelwise constant is uniform in the original conductor, height, selected slots and exceptional-row parameters.

Accordingly:

1. Equal-norm ideal multiplicity is not the missing power saving.
2. The genuine missing analytic theorem is the labelwise ray-class/large-sieve moment, especially the refined plain fourth moment and its collision geometry.
3. Owner claim `20261019-owner-1` remains necessary for coefficient identity. (NF) bounds a collapse; it does not prove that the collapsed coefficient is the intended once-only physical coefficient.
4. Owner claim `20261019-owner-2` is compatible with (NF): good, ramified and mixed norm-fiber contributions are retained.
5. Stage I completed-theta/Poisson (11/12), the principal Euler product, exceptional rows, and final common detector remain open.

## F. Falsification and sharpness

The tempting constant-loss assertion
[
 \sum_n\left|\sum_{N\mathfrak a=n}z_\mathfrak a\right|^2
 \ll\sum_\mathfrak a|z_\mathfrak a|^2
]
with an absolute constant independent of the support is false.

At (n=133=7\cdot19), both rational primes split. Hence
[
 \rho(133)=4=d_2(133),qquad \rho^{*2}(133)=16=d_4(133).
]
Taking every coefficient in that one fiber equal to (1) makes the ratio of collapsed to labelled energy exactly (4) for (k=1), and (16) for (k=2). More generally, split squarefree integers attain (d_{2k}(n)). Thus the divisor loss in (NF) is coefficientwise sharp and cannot be replaced by a uniform constant.

This also matches the active source warning: the four norm labels at (133) do not equal one rational Möbius occurrence. The original coefficient is recovered only after the full quadratic convolution; selected sextic phase sums need not be (1). No termwise ideal-to-integer identification is made here.

The complete-character identity has its own sharp obstruction: if (m) equal coefficients lie in one ray class, the right side of (CP) is (m^2), not (m). Therefore fixed-modulus character orthogonality alone does not establish the desired saving as the class occupancy grows. A varying-family large sieve or independent class-collision theorem is essential.

## G. Handoffs

- **Coordinator:** add (NF)/(NFT) between the genuine ideal-labelled moment and any rational norm-owner projection. Mark the edge as a subpower transfer, conditional on exact coefficient conservation; do not list norm multiplicity as the primary exponent bottleneck.
- **Owner Payment:** prove the complete fiber coefficient theorem on the actual completed theta source. Once that identity is available, (NF) controls its full good/ramified mixed norm energy with (X^\varepsilon) loss.
- **Finite Wheel:** classify additional decorations beyond ordered ideal tuples and prove a uniform (L). If (L) grows, record its exact scale before using (NFT).
- **Prime Census:** use (n=133) and products of distinct split primes as sharp regression cases. Test complete fiber sums, not label counts alone.
- **Adversarial Referee:** audit the coefficientwise inequality (\rho^{*k}\le d_{2k}), the fixed-(k) requirement, and whether the intended OAI product really has (k=1) or (2) before accepting the transfer.
- **Lean Verification:** after independent acceptance, formalize the finite fiber-frame inequality and the complete-character Plancherel identity. Do not attach an assumed source equality or moment bound.

## H. PR and CI state at final refresh

Open PRs were #983, #985, #986 and #987.

- Draft #987, head `73fb6304baa37980d6236c66cfecc884b880dbc7`, is stacked on draft migration #983. Its public-export check succeeded; six material proof/source workflows were still in progress. It does not yet establish an independent native moment theorem.
- #986, head `4345260a58f1c14f4018e46292469767c54cd908`, had an exact-head failure in the actual Eisenstein ideal norm-fiber sharp-square bridge and several workflows still running.
- #985, head `8f51ddcb62c805ef19104399ede62d93731f6fca`, had failed its native Euler prime-density workflow and targeted iteration.
- Draft #983, head `9811d5db79cfa5dc69cd642779d80e18eaf9ffb5`, was partially green with several workflows still in progress.

No status is inferred from workflow names. In particular, “full certified 7/8” in a workflow title is not a mathematical result while the run is unfinished, and replay/import of the external terminal theorem is not the requested independent native derivation.

## I. Resume capsule

- New claim `20261019-analytic-1 / PAPER_PROOF`: fixed-order Eisenstein norm-fiber collapse costs (L d_{2k}), hence only (X^\varepsilon).
- New claim `20261019-analytic-2 / EXACT_IDENTITY`: complete-character Plancherel reduces the inverse second moment to same-ray-class collision energy.
- Sharp falsifier: (n=133) attains the (d_2) and (d_4) fiber losses; constant-loss collapse is false.
- First independent analytic blocker: a uniform varying-conductor/height ray-class collision or large-sieve theorem for the genuine inverse coefficients, followed by the refined plain fourth moment.
- First source blocker: exact completed-theta ideal-fiber coefficient conservation with good/ramified restoration.
- Campaign status remains `INCOMPLETE; NO INDEPENDENT 7/8 PROOF`.
- No new zero-free line, Mertens exponent, canonical VF bound, finite A/C result, or RH proof.

## J. Publication verification

The early `IN_PROGRESS` checkpoint committed as `227e1ae5292cc40045c8d935ebab88ac948e4189`; immediate readback returned blob `9ce51a71bda79cecad8880cf3e3973a60a4a8f67`.

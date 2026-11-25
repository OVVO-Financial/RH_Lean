# RH | Analytic Type II | 2026-11-24 (America/New_York)

## Opening | ANA-20261125T014428Z-WINDOW-OPEN

**IN_PROGRESS.** On the principal native source the existing side of the comparison is an average at the realized heights, not the missing signed gain-to-cost bound. I am testing whether the actual positive prime-power hinge kernel allows fewer paid host scales while still covering every real point of a full closed window. I will also trace the actual height-selection input. No constructed physical family, new formal theorem, critical estimate, or RH closure is claimed at this checkpoint.

Scheduled trigger 20:44:28 EST / 01:44:28Z. Main `5fefebadf176092a7cd83a4e16aca1f0ec0ce60e`; #1201 draft `0b9f49ce640e98b3b9c81a29d71d6d98d69f62a9`; reports intake `5826297f5ce97d27c90e8215e5d64384fcc20155`. Control: `final_1201_ack=FINAL_PR_1201_PROOF_CLOSURE_V1`, `FINAL_1201_ROLE=ANALYTIC`, `DIRECT_CORE_CUT_V1`, `STRICT_NO_GEOCL_ANYGEOMETRY_V1`, `publish_ack=REPORT_PUBLISH_RECOVERY_V1`, `continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1`. The November 24 DIRECT, LOCALGAIN and CORE reports supersede prior task selection; November 23 has no verified role report. November 22 SELECT1-4 and its unresolved tail remain historical rather than a mandate to rebuild the family. No exact-current-head #1201 Actions run or check run was returned at intake; no dispatch. Only this report is authorized for writing.

## Research checkpoint | ANA-20261125T014428Z-WINDOW-M1

**PAPER_PROOF, independent review pending.** For the literal principal source (Z), any real (1\le u<v) and (u\le x\le v), its excess above the affine chord is at most ((x-u)(v-x)/(2u)), hence at most ((v-u)^2/(8u)). All arithmetical crossings enter the exact defect with a minus sign and nonnegative von Mangoldt mass. This is an upper estimate only: across the prime 2 at distance (1/16), the arithmetic chord excess is (\log(2)/64>1/128), whereas the log-curvature allowance is at most (1/992). The new application is to **fourth-power-minus-one interior anchors plus two ordinary square-clock edge anchors** on the original pair's (A=3/2) window. No interior resampling of the pair is needed. A geometric bound at the anchors is still missing.

The upstream numerical box selector explicitly returns ceiling vectors; the stronger weight-window transfer consumes a separate weight-vector witness. Neither is a demonstrated construction of the native signed payment at these anchors. Full endpoints, thresholds, proofs and reproduction follow in the final section. No new Lean or unconditional RH assertion.

## Final findings | ANA-20261125T014428Z-WINDOW-FINAL

### A. What the estimate changes

**The genuine principal source can be controlled between fourth powers at square-root cost.** If two paid scales are $u$ and $v$, the upper interpolation error at any real $x$ between them is at most $(x-u)(v-x)/(2u)$. Every prime-power crossing has the favorable sign **after** the complete source has been formed. Consequently the interior scales $j^4-1$, plus two explicitly chosen square-clock scales at the edges, suffice on the **original** $[Y,Y^{3/2}]$ pair. The number of required physical payments up to the upper edge $B$ is at most $2+\lfloor(B+1)^{1/4}\rfloor$, not of order $\sqrt B$. There is no accumulated cost from the number of anchors. A payment at just one chosen scale does not suffice.

| Claim | Evidence | What is and is not supplied |
|---|---|---|
| ATII-20261124-WINDOW1 | PAPER_PROOF | Unconditional one-sided estimate for arbitrary real intervals and an estimate for finite means of actual heights. Not an absolute-error bound. |
| ATII-20261124-WINDOW2 | PAPER_PROOF / application CONDITIONAL | Sparse square-clock attachment, two boundary repairs, fixed constants and coefficient-one complete windows. The cost at the stated anchors is **not** proved. |
| ATII-20261124-WINDOW3 | SOURCE_INSPECTED / PAPER_PROOF | Distinguishes the constructed integer box from the joint physical weight witness. Gives an alternative check on the **measured** height sum for the movement step only. |
| ATII-20261124-WINDOW4 | PAPER_PROOF / REFUTED strengthening; FINITE_COMPUTATION | A genuine prime-power cusp refutes a two-sided quadratic estimate. Exact checks below concern the interpolation, not the physical gain. |

Independent review is pending. No Lean declaration, exponent bound on the full source, or unconditional RH theorem is claimed.

### B. Source and target

Main [policy][policy] `5fefebadf176092a7cd83a4e16aca1f0ec0ce60e`, [contract][contract], [closure directive][directive]; [#1201 instructions][pragents] at draft head `0b9f49ce640e98b3b9c81a29d71d6d98d69f62a9`. The [native definitions][arith] and [#1205 handoff][handoff] give, for $x\ge1$,

$$Z(x)=\sum_{1\le n\le\lfloor x\rfloor}\Lambda(n)(x/n-1)-x\log x+(1+\gamma)x.$$

This is `statementOCGz` and the [principal cyclic `Gm`][recovery], not a four-character summand treated in isolation. Fix $e_D,e_L$ and $\varepsilon_1>0$ **before** $\varepsilon$. For each $0<\varepsilon<\varepsilon_1$ the handoff requires one $C_\varepsilon$ **before** every $Y_0$, some $Y\ge Y_0$, and $Z(x)\le C_\varepsilon x^{1/2+(e_D+e_L+7)\varepsilon}$ for **every real** $x\in[Y,Y^{3/2}]$. Our conditional attachment gives $C_\varepsilon=1$. Literal terminal type in [#1205][handoff]: `{K ε₁ : ℝ} → 0 < ε₁ → SmallEpsilonWindowBound K ε₁ → RiemannHypothesis`; the window bound is a premise.

### C. Why interpolation helps

The [previous signed square interpolation][oldchord] preserves the difference of a logarithmic and an arithmetic chord defect on consecutive integer square endpoints. Its two-sided estimate costs the length of the interval. [Real unit-cell interpolation][unit] accounts for the logarithm when the arithmetic part is affine. The [global native movement theorem][move] costs $(\log4+4)|v-u|$. These results and DIRECT3 / CORE4 are prior work. The additional ingredient here is the **direction** of every arithmetic kink on arbitrary real intervals, together with the curvature $1/x$ of the centering. Using this only after a scalar anchor is paid permits much larger gaps; it does not delete any term from ASK or MAIN.

### D. Exact formulation and proof of WINDOW1

Let $1\le u<v$, $u\le x\le v$, $\theta=(x-u)/(v-u)$, and $L_x f=(1-\theta)f(u)+\theta f(v)$. Let $T(y)=(1-\theta)(y-u)$ on $[u,x]$, $T(y)=\theta(v-y)$ on $[x,v]$, and zero outside. The two values at $x$ agree. Then

$$Z(x)-L_x Z=\int_u^v \frac{T(y)}{y}\,dy-\sum_{u<n<v}\frac{\Lambda(n)}n T(n)
\ \le\ \frac{(x-u)(v-x)}{2u}\ \le\ \frac{(v-u)^2}{8u}.$$

Indeed each summand of the uncentered source can be extended as $\Lambda(n)(y-n)_+/n$. Only finitely many $n\le\lfloor v\rfloor$ matter. Its chord minus its value at $x$ is $\Lambda(n)T(n)/n$, by checking $n\le u$, $u<n\le x$, $x<n<v$, and $n\ge v$. At equality with an endpoint the tent vanishes. The affine Euler term cancels. For $F(y)=y\log y$, integration by parts on the two halves gives $L_xF-F(x)=\int T(y)F''(y)\,dy$, with $F''(y)=1/y$. The triangle has area $(x-u)(v-x)/2$. Every nonzero coefficient is still the original $\log p$ at $n=p^a$, including $a>1$. No distributional estimate, exchange of infinite sums, or assumption on prime gaps is used.

**Same-host finite mean.** For any finite probability law on actual heights $v_i\ge1$, let $\mu=\mathbb E v_i$. Jensen's inequality applied separately to each positive hinge gives
$$Z(\mu)-\mathbb E Z(v_i)\le\mathbb E[v_i\log(v_i/\mu)]\le \operatorname{Var}(v_i)/\mu.$$
The second inequality is $\log t\le t-1$. The exact subtracted term in the first inequality is $\sum_n(\Lambda(n)/n)[\mathbb E(v_i-n)_+-(\mu-n)_+]$. For the native payment use precisely the **uniform** law on the original nonempty $TT$, without reweighting an unrelated covering set. This estimate pays evaluation at the actual barycenter; evaluation at a different $x$ additionally costs at most $(\log4+4)|x-\mu|$. No drift is declared zero by definition.

### E. Which heights and which physical costs?

At a paid node $s$ take exactly the selected $q,d,e(s),H,TT,T_2,m,a,b,w,D_0,C$ of the [constructed comparison][payment]. Write $T=|TT|$, $n=|H|$, $\Delta=|T_2|/n$, $z=s^\varepsilon$, $a_E=D_0.a$, $k=D_0.k$, $Q=Tmb\Delta/2>0$, $v_t=a(t)/b$. The independent missing inequality is the **full** uniform base mean of $ASK-\Re MAIN$, divided by $Q$, bounded above by $s^{CErr(C)\varepsilon}\mathcal P_s$, where the [exact price][cost] is

$$\mathcal P_s=\frac{2a_E(1+m^2/k)}{mb\Delta}+\frac{4nmz}{T\Delta}+\frac{2kz^2}{nT}.$$

Retain the actual inertia, Frobenius, canonical $\ell$, cutoff $\lceil A_{\max}/\beta\rceil$, uniform base, every top and lift, ramified and higher powers, thick and thin widths, and original recovery. [`physicalData`][physical] replaces the visible arithmetic entries but **preserves** $D_0.Ga$. The existing [mean-loss consumer][recovery] requires `HidaSetting, DIV, EComp5, HComp, Count5, Slopes, QuotientSlopeBoundsWith, Losses, SlopeIneq, HHBound, FParams`, plus `ErrWindows, LargeX`, $B_0\le2nmbz$, $N_c\le |T_2|kbz/[n(n/z)]$, the actual height, width, density and admissibility hypotheses, and [`GeometricSizeWindows`][sizes]. The first working pair of unpaid leaves is the quotient-slope bound and the losses **for the same measured gain**. The Owner's accepted pre-split comparison is an alternative only if independently paid. No bound here is applied to just the positive or unramified part of that ledger.

**WINDOW3: the height constructor is not the joint constructor.** At the pinned upstream source, [`InWin`][inwin] puts the integer top height in $[s b,s b+s b/(k\sigma)]$ on $TT$, $\sigma=s^{\mathrm{Scale.A}/2}$; its additional column condition is a lower bound by the separate $b'$ parameter. The scalar $b$ here is the common `sc.b`, **not** the integer column $b(t)$. [`inWin_of_boxT`][box] projects the two actual box memberships. [`exists_weights_in_windows`][selector], for fixed $\varepsilon,C$ with `Std C`, $0<\varepsilon<1/52$, all large admissible scales, `RankVal` and the given host, proves both intervals have length at least one and takes the **constant ceilings** of `sc.a` and `sc.b'`. This genuinely constructs `WinOK` on that interface. The [joint host conclusion][joint] additionally consumes `Val`, `From` on that host, `CanonInst` and `AuxBlock8.WeightVectorExists` (with `Std`); it extracts box membership and the weighted condition from that witness. A free choice inside the box is **not** a proof that the native measured weights and gains used by `physicalData` have those values. I found no clean joint constructor that attaches such data on the selected anchors. No tied family or prohibited geometry is invoked.

For measured original `InWin` heights, $b>0$, $k\ge s$, $\sigma\ge1$ give $s\le v_t\le s+1$ by [`nativeOriginalHeightWindow`][recovery]. A weaker measurable check for *this movement step only* is available. The original $A_{\max}/b\le s+1$ already gives $v_t\le s+1$. Then exactly $\mathbb E|s-v|=s-\mathbb E v+2\mathbb E(v-s)_+\le s-\mathbb E v+2$. Thus it suffices to verify on the real data
$$\frac{DP.\mathrm{sumA}}{Tb}=\mathbb E v\ \ge\ s+2-\frac{3s^{1/2+\varepsilon}}{\log4+4}.$$
The equality uses [`Data.sumA`][data] and `physicalData.aT`; the inequality is **not** supplied by nonnegativity, $D_0.a\ge sb$, or a large integer box. If using this weakening, retain separately $v_t\in[Y,B]$ for **all** $t$, the thin ratio, and every other antecedent; it does not imply the original pointwise `InWin` or physical validity.

### F. WINDOW2: proof on closed windows

Fix nonnegative uniform upper caps $e_D,e_L$ for the actual $C.eDiv,C.eLoss$ and a genuine positive physical validity range $\eta_{\rm phys}$. These are *input obligations*, not numbers inferred from CI. Put $D_*=e_D+e_L+6$ and fix $\varepsilon_1=\min(\eta_{\rm phys},1/52,1/(2D_*))$ before selecting $\varepsilon$. For $0<\varepsilon<\varepsilon_1$, put $\alpha=1/2+D_*\varepsilon\in[1/2,1]$. The [actual error definitions][errors] give $CErr(C)=C.eDiv+C.eLoss+3$. Their `ConstsBound C K` bounds several coefficients by $K$, but imposes **no upper bound** on the two error exponents. Setting just these two fields to $N$ and all other fields of the scalar `Consts` to zero satisfies `ConstsBound C 1` for every $N\ge0$. This falsifies an inference from **that constraint alone**, not a claim about any physical family. Positive caps can always be enlarged after being proved uniform.

Take $Y\ge256$, $B=Y^{3/2}$. Use the **one** `PairGood 1 ε Y B q d` and PageN selector of the analytic payment, not an intersection of two unrelated existentials. Define the finite set of required base scales by
$$l=\lceil\sqrt{Y+1}\rceil^2-1,\quad r=\lfloor\sqrt B\rfloor^2-1,\quad
\mathcal A(Y)=\{l,r\}\ \cup\ \{j^4-1:l<j^4-1<r,\ j\in\mathbb N\}.$$
For $Y\ge256$, $Y\le l<r$ and $r+1\le B$: for example $l\le Y+3\sqrt Y$, while $r\ge B-2\sqrt B$, strictly larger. Each anchor $s=R^2-1$ is an actual square clock, and $[s,s+1]\subset[Y,B]$. On each one assume **independently constructed, compatible** physical data paying E, with its own prescribed $e(s)$ and the same window pair. No geometry is taken from one node to discharge a premise at another. The [scalar square-clock lemma][move] can specialize to $m=R,k=sR$ **only if these are the measured parameters** and its actual counts and $a_E$ bounds hold; this is not required for the interpolation itself.

At $s$, first use the **unrounded** signed mean bound $\mathbb E Z(v)\le s^{CErr(C)\varepsilon}\mathcal P_s+s^{1/2+\varepsilon}$. The original height condition gives the charge $M\mathbb E|s-v|\le M=\log4+4<6\le3s^{1/2+\varepsilon}$, or use the trace test in E. [`nativeGz_le_of_mean_normalizedCosts`][move] and [`normalizedCosts_add_remainder_le`][sizes] give $Z(s)\le s^{1/2+(CErr(C)+3)\varepsilon}\le s^\alpha$. No rounded remainder is spent twice.

For adjacent anchors $u<v$, there is a $j\ge4$ with $j^4-1\le u<v\le(j+1)^4-1$. Thus $v-u\le 6j^3\le7u^{3/4}$: expand $(j+1)^4-j^4$ and use $u\ge(255/256)j^4$. By WINDOW1 and concavity of $t^\alpha$,
$$Z(x)\le L_x(t^\alpha)+\frac{(v-u)^2}{8u}
       \le x^\alpha+\frac{49}{8}\sqrt x \qquad (u\le x\le v).$$
At the lower edge, $0\le l-Y<2\sqrt{Y+1}+1\le3\sqrt Y$; $t^\alpha$ is 1-Lipschitz for $t\ge1$. Get $Z(x)\le x^\alpha+3(M+1)\sqrt x$. At the upper edge put $k_0=\lfloor\sqrt B\rfloor\ge3$. Then $B-r<2(k_0+1)\le3\sqrt r$. Since $r\le x$, $Z(x)\le x^\alpha+3M\sqrt x$. This includes $Y,B$ and every real point between them. Consequently
$$Z(x)\le x^\alpha+21\sqrt x\le22x^\alpha\le x^{1/2+(e_D+e_L+7)\varepsilon}\qquad(x^\varepsilon\ge22).$$
Only the two neighboring scalar estimates are combined. There is no union bound or summation of errors across anchors. On $[X,2X]$ the required interior count is $O(X^{1/4})$, versus $O(X^{1/2})$ ordinary square clocks. Across $[Y,Y^{3/2}]$ it is $O(Y^{3/8})$ versus $O(Y^{3/4})$. These absolute count savings say nothing about the difficulty of a single measured payment.

**Threshold order.** After fixing $\varepsilon$, take any nonnegative scale-uniform caps $K_\varepsilon,H_\varepsilon,E_\varepsilon$ for the physical $K,c_{HH},e_K$; set $P_\varepsilon=200(1+K_\varepsilon)^2(1+H_\varepsilon)(1+E_\varepsilon)$. Seek a jointly paid window above the maximum of the requested $Y_0$, the [constructed comparison's][payment] $Y_0(\varepsilon,3/2),x_0(\varepsilon,3/2)$, all independent physical thresholds, and
$$256,\qquad 22^{1/\varepsilon},\qquad 26^{8/(3\varepsilon)},\qquad
 P_\varepsilon^{1/\varepsilon},\qquad \exp(2/\varepsilon^2).$$
The last two suffice for `LargeX`: $\log s\le s^\varepsilon$ follows from $e^t\ge t^2/2$ at $t=\varepsilon\log s$. The third handles the displayed factor 26 in `GeometricSizeWindows`. This does not pay the *other* clauses of those windows. The coefficient is fixed before $Y_0$, with no uniform threshold as $\varepsilon\downarrow0$. For the set-valued formulation take $S$ to be the union of the jointly paid windows for this $\varepsilon$; at any point use a single containing window. [`nativePrincipalCyclicGm_eq`][recovery] identifies the same scalar on all real arguments; [#1205][handoff] is the existing consumer. This is not a new conditional RH endpoint.

### G. What was eliminated, what was not

On this native path no pointwise `CoreAtH` at interpolated $x$ is needed. The implication requires the signed cost *only at the declared physical anchors*. This report supplies no instance of that cost. Afterwards the scalar inequality uses the very same $Z$, independent of host notation. This proves neither `CoreAtH` nor the existence of physical geometry between the anchors. [`nativePrincipalEAtH_windows`][eath] constructs the analytic host for every $TT$ on its chosen window; if the direct core is used, specialize `nativeDyadicHostRaw_EAtH` to the **payment's** pair and exponent rather than resampling.

In the reserve route, [`core_gm`][coregm] takes both `EAtH` and [`CoreAtH`][coreath] on the same $H,TT$; [`Deduction.ch_top`][chtop] actually consumes `IdentU, SizeData₂, ErrWindows, BNBoundsU, LargeX`. Its output is pointwise, not simply an unweighted pulled-back mean. None is appealed to as a supplier here. The complete opaque closure of the reserve route has not been certified clean. No `GeoCl`, `geoCl`, `anyGeometry`, terminal external RH, or assigned measurement enters WINDOW1-2. No claim is made about purity of an unconstructed geometric supplier.

### H. Falsification and reproducibility

**WINDOW4.** The sign cannot be upgraded to a two-sided quadratic estimate. On $[p-\delta,p+\delta]$, $x=p$ prime and $0<\delta<1/2$, the only crossed integer is $p$. The arithmetic deduction is exactly $\Lambda(p)\delta/(2p)$; the deterministic addition is at most $\delta^2/[2(p-\delta)]$. Let $\delta\downarrow0$ at fixed $p$: the absolute error divided by $(v-u)^2/u$ is unbounded. At $p=2,\delta=1/16$ the arithmetic deduction is $\log2/64>1/128$ and the deterministic upper bound is $1/992$. In the other direction, at the midpoint of $[n,n+1]$ the arithmetic tent vanishes, while the deterministic defect lies between $1/[8(n+1)]$ and $1/(8n)$. The constant $1/8$ is asymptotically sharp on these cells. This neither claims macroscopic saturation on fourth powers nor forbids coarser meshes using further arithmetic.

**Exact finite replay (no Lean).** Rational arithmetic; no numerical logarithms or simulated physical host. For $u=i/4$, $i=8,11,\ldots,158$ (equivalently `range(8,161,3)`), widths $1/8,1,7/2,45/2,71$ and $\theta=0,1/8,1/4,1/2,2/3,1$, enumerate each $n=p^a\le128$. Compare the literal floor-prefix coefficient $c(y,n)=1_{n\le\lfloor y\rfloor}(y/n-1)$ evaluated at $u,x,v$ with $L_xc-c(x,n)=T(n)/n$. Also compare sums grouped by $\log p$. Result: 255 intervals, 1,530 evaluation points, 44 prime-power indices, 9,990 interior index visits (2,820 higher powers), 93 exact evaluation ties; all passed. For $Y=(m+h)^2,B=(m+h)^3$, $m=16,\ldots,80$, $h=0,1/3,2/3$, check by integer square root that all nodes are valid, both edge distance squares satisfy the factor-9 tests and every adjacent gap satisfies $(v-u)^4\le7^4u^3$: 195 windows, 2,560 anchor visits, 2,365 gaps, 390 edge checks; all passed. Replay source SHA-256 `7e12881183f11c90e1087c0e0c2888e59b00d877a0fe38121e0e7095c313ba14`. These checks cannot certify the cofinal physical premise.

### I. Interpretation and circularity

DIRECT3's $A=2$ collar is valid **if** the geometry is supplied on that actual longer-window pair. CORE4's $s=\min(x,B-1)$ repair works on the shorter pair when the required interior scales are paid. WINDOW2 instead reduces the *number of scales*, keeps $A=3/2$, and needs two ordinary square-clock edges. Restriction of an already assumed full scalar bound to anchors would be tautological. In fact restriction and the proved interpolation make a suitably exponent-slack sparse **scalar** criterion as strong as the desired window conclusion; it is not advertised as an independent critical bound. The independent gain in this report is the original-carrier interpolation inequality, not payment of the remaining scalar values. The noncircular task is to earn the signed comparison from actual geometry on this smaller set.

### J. Specialist handoffs

| Role | Precise next use |
|---|---|
| Coordinator | Keep the native signed comparison first. Use the sparse obligation only if the physical constructor can exploit square clocks; do not open a second proof PR. |
| Owner Payment | On one prescribed node supply the measured `chainK` on actual `NP`, two word records with the same `Ga` used by the slopes and losses, and the measured heights or their trace. Do not set `Ga` or heights to a chosen endpoint. |
| Wheel | Identify the ranks, metrics, relative image and $k$ on that node. The specialization $m=R,k=sR$ needs a real identification; a Smith list cannot certify it. |
| Census | For the first physical witness report $s,T,b,\min v,\max v,\sum a_t$, cutoff, and both signed charges before normalization. The rational mesh check needs no enlargement. |
| Referee | Check the tent sign at $n=x$, the genuine cusp obstruction, both edge nodes, the choice of $e_D,e_L$ before $\varepsilon$, and that no physical data cross hosts in the proof. |
| Lean Verification | After independent review and only if consumed, a minimal pure arithmetic lemma would be `alpogeNativeGz_le_realChord_add_curvature` with the inequality in D. Reuse [`nativeGz_le_of_mean_normalizedCosts`][move] and #1205; do not encode a cost constructor as a hypothesis and call it closed. |

### K. First independent missing theorem

Construct on cofinal original pairs the compatible physical comparison **at every node of $\mathcal A(Y)$**, with uniform caps and either actual `InWin` or the separately valid trace/membership checks. First test one node at the Owner's more local leaf: generators of the actual intersection `NP` must map under `chainK` into the original valuation lattice at the word's `gainP + lowFE` exponent. Then test `QuotientSlopeBoundsWith` and `DP.Losses` with the *measured* `Ga` and all costs from E. No pair of measured words meeting these obligations was present in the inspected reports. Even a successful test on one node would not supply every node or a cofinal window. Numerical uniform values for $e_D,e_L$ **have not been earned**.

### L. Resume capsule, continuity, and verification

`final_1201_ack=FINAL_PR_1201_PROOF_CLOSURE_V1`; `FINAL_1201_ROLE=ANALYTIC`; `DIRECT_CORE_CUT_V1`; `STRICT_NO_GEOCL_ANYGEOMETRY_V1`; `continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1`; `publish_ack=REPORT_PUBLISH_RECOVERY_V1`. Preserve the previous full-cost and amplification acknowledgments as historical. Next actual run: refresh the pins, examine the first supplied same-host measured word/height package at a prescribed square clock, test the trace and both loss inequalities, then determine whether the construction works on the declared anchors. Do not rerun the old finite-depth Selmer tail campaign or another generic census.

**Intake.** The [reports branch snapshot][intake] was `5826297f5ce97d27c90e8215e5d64384fcc20155`. Its recursive reports tree `4d5fd36daaa904f4528b6f2aa888f43b9b25d4e1` returned 458 entries, untruncated. From the previous Analytic watermark `24afed0559db7199611b55c0e2ecf60752f15924` to intake: 11 commits, eight paths. The November 23 folder is absent for all seven roles: `YESTERDAY=NO_VERIFIED_REPORT`; do not manufacture a previous-day carry. November 24 Wheel, Census and Lean were `TODAY=PENDING` at intake, as was this role before its checkpoint. The table gives actual New York trigger times, predecessor/current sections and last consumed blobs; Coordinator mirrors are identical and count once.

| Role | Verified sections and consequence |
|---|---|
| Coordinator | Nov 22 07:10:01 FIELDWINDOW1-4 `f4486054aaf169cab19e56dcefd5e5199346fb7a`; Nov 24 19:35:47 [DIRECT1-3][coords] `33e418f2df05b7c71c9239fa6609cb22abb48349`. Compatibility interval, Smith obstruction and longer-window collar; no physical payment. |
| Owner | Nov 22 08:09:01 WIDTH to THIN1-4 `bfaf87b61b28f68a9bd40a3a461e208859ef19a7`; Nov 24 19:56:24 [OP-20261124-LOCALGAIN1-4][owner] `74f9baaea9fa0e4043e79e01e99d732e61daab86`. Rounding paid under stated conditions; image valuation and baseline remain. |
| Analytic | Nov 22 09:09:00 TWISTSHELL to SELECT1-4 `8eee3baa28630cae859c8a07f2e22d945cb5e65f`. Finite layer and exceptional-fibre localization do not buy the full geometric tail. Current WINDOW claims are distinct. |
| Wheel | Nov 22 10:12:00 ANCHOR1-5 to METRIC1-5 `cf826ac72743e53f75e413acab41d6a5c1659e16`. Ambient metric and image metric differ; no inferred later run. |
| Census | Nov 22 03:11:00 FOURPOWER1-4 `f8f96d3ce7b2e2f1305b0a1984d6f936c9f55448`. Higher-power pruning requires its linear restoration. |
| Referee | Nov 22 04:13:01 POWER1-5 `80438ad50b0f051d6c3f3669bb34b62a1ccdab7f`; Nov 24 20:13:00 [REF-20261124-CORE1-5][referee] `bfb4c06772fe4b5df481d27921abe0a49ce73802`. DIRECT and LOCALGAIN accepted at stated scope; singleton divisor circularity, zero-Frobenius mismatch, base mean, edge repair and relative image test retained. No endorsement of WINDOW inferred. |
| Lean | Nov 22 05:10:00 CELL-SIGN / EVEN-COST `9677a27a1159eb5d46afc480359aa94b7b78427c`; local signed algebra, not the missing payment. |

The November 22 owned recovery openings `3f7d02ce98759dc24eef7f4001a7115c2ac595e6`, `6f9adc5b228b534378ad28c9cf9e254fd54e685b` and `9cac6baf80dd0274875f139e83ed928f69bde4c1` were read and deduplicated. [External handoffs][external] `7d63d434690d00dffce9c90335d41c4f62d85798`: EXT-20261018-PNT-1 and EXT-20261017-XCOORD-1 retain their endpoint exceptions; EXT-20261014-3/-5 do not justify local-to-global payment. No new physical supplier there. At prepublication, the branch was `69d231b651556d2d72e1938aa54e92e946f154d5`; only our own canonical path had changed since intake. Intervening handoffs since the watermark accounted for; the inherited November 13-15 archive-exhaustiveness caveat is not retroactively cleared.

**Hosted evidence, not a new build.** #1201 remains open/draft. Exact head `0b9f49ce640e98b3b9c81a29d71d6d98d69f62a9` returned zero Actions runs and zero check runs both at intake and at the prepublication refresh. The [comparison][compare] from `973a8810f35d5ca3b9fa2f30d2315edac412a193` has two commits and zero changed files. Actual tested merge checkout `b0a5d08bc04202741c7223f0760a4cec40ea308e` and present head both have tree `ce74adfda8407f4e7efa72baf3bea34340203663`. The [required job][oldci] logs show `NativePrincipalEAtH` and `NativeExistingRecoveryPayment` built, then a type mismatch at `NativeCMSerreGenericLieMetric.lean:169:2`; subsequent diagnostic mismatch; full hosted build skipped. The [source census][censusci] scanned 3,589/3,589 tracked Lean files, zero failures, 191 visible-premise RH-return candidates; this is not independent semantic clearance. [#1205][pr1205], merged `fde7ea71ed88f540a8829554a8ab4602bda96f4d`, submitted head `45d86f3f728e94e476427ffa41e5a0620bb74be0`, actual tested merge checkout `80b2b2098513d467af9e370fbf41b0592c4b4cb9`: [conditional terminal audit][handci] explicitly printed only `propext, Classical.choice, Quot.sound` for the named implication; [native build][buildci] passed. `LEAN_VERIFIED_CONDITIONAL` for that implication only. #1203/1204, #1206, #1209 and policy #1210 merged; #1208 closed unmerged. Other open PRs: #1207 non-draft `0991c2f181f6943d0e57671cffebb1129d5ff4b4`; #1211 draft `ec75c33636fcdf2cd9a883c50a5b6fa8226c77c0`, an external-replay lane, not merged authority or an independent native supplier. No local Lean, workflow dispatch, proof edit, or merge.

**Material Git blob fingerprints** (all native proof files at the inspected #1201 head; #1205 handoff identical on main):

| Source | Blob SHA(s) in order |
|---|---|
| Main AGENTS; contract; closure directive; PR-head AGENTS | `a60620dca883d98dbe391ddd1ab5afcab805b96e`; `6fa886e125321056739a48d09fd33c95edaebf6b`; `395378d0e6525fab6c6ed9b7315c5de4c36329dd`; `f4bcae0b282eea80bd0eb41a90599980251cc2f6` |
| Semantic audit; native scope; continuity; recovery | `1029b89123471c04da44b0d91f382d7291cf1f14`; `e801608ddc7d1de31b0fa785b71dbcf2de025e53`; `7eef0b36c7442be922d9bc99c6b35d853c4f1f4f`; `a9583516fd2e603320c771e32c170132bf0c53e9` |
| Original arithmetic; prior square interpolation; unit-cell interpolation; movement constant | `5203ec0e45b1d1f9b88d87e8b93455526169fbc8`; `08bb1575946dba6b7af918086e33208fc33f77cb`; `9da6a82d73e21d9962a139faa9711d27dc1e63cc`; `3d6679911fe30292f40bcd40281578e02bf8dbfa` |
| NativePrincipalEAtH; NativeConstructedDyadicGzPayment; NativeExistingRecoveryPayment; #1205 handoff | `7b01aec0c6ed90635512d10c4074208cd97fd241`; `89b83b14a060443aceab44fdb38478f07af5678b`; `1076fb12c5bb2b1a85ed97f20aadfb105c4e2747`; `31dc576197075a0448ced1a1c58e24a35c6d80d6` |
| NativeScalarSupplierPayment; NativeGeometricCostWindows; cost normalization; physical slope attachment | `51c8660dbc4d7109f71bbc9d6421e93aa06ce61a`; `ebadfe97d09408a04b64a36a328b19a667d729ee`; `07ec36dabad5d06c97dde991fb8c7de99af442d7`; `d8250851cd4ddc640fdc89df8475dcc2c09a636a` |
| MeanBoundSecondForm; QuotientSlopeBoundsWith; ErrorWindows | `e2ae852c8b5c089d41ee363068d1de662c760932`; `a7f578f04acd4eb822644cd3e502aa5e89c882f7`; `8ebe9e1f4626437b4dd621c2997e188c945a70e8` |
| Upstream `7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`: InWin; box projection; ceiling selector; joint selector | `a37d19e7affc2c873c5a325fb25af7bf7834d9a0`; `5d604bab285e79af10aa9fe50d6326a363b873b5`; `7365354727887c298726891ab05703ae445af351`; `b899a758a89ef1626f8187521fcf87440ed4c2f3` |
| Same upstream: CoreAtH; core_gm; ch_top | `0ba3621036f19146e7e67fa9c0e8a1c38661a097`; `3ba7a590e84c5993882ea6c5dcf9fdbed5f07d4d`; `ce06a34a9e0b1b332e10d3b7efb04a06e9ab77f5` |

**Own publication.** Verified opening commit `777e3c63eba2fc6a7083a1867f30b2800d2d1d5e`, blob `8ea4bc6e2b3ebc3c86023a19de6680a303439195` (1,409 bytes), and milestone commit `69d231b651556d2d72e1938aa54e92e946f154d5`, blob `c139d524b7750b7b6ea8fc746c7a8ac60ae9efb7` (2,576 bytes), same invocation. Direct Git tunnel returned 403; authenticated GitHub content writes/readbacks succeeded. Append this synthesis to that exact history; the final exact-commit receipt belongs to the delivery message. `MATH_STATUS=OPEN; WINDOW1-4=SELF_AUDIT; LEAN_STATUS=NOT_RUN_FOR_NEW_CLAIMS`.

<details>
<summary>Exact Python replay for the finite checks in H</summary>

```python
from fractions import Fraction as F
from math import isqrt


def prime_powers(limit):
    primes = [p for p in range(2, limit + 1)
              if all(p % d for d in range(2, isqrt(p) + 1))]
    out = []
    for p in primes:
        n = p
        while n <= limit:
            out.append((p, n))
            n *= p
    return out


def floor_root(q):
    return isqrt(q.numerator // q.denominator)


def ceil_root(q):
    r = floor_root(q)
    return r if r*r == q else r + 1


def source_coefficient(x, n):
    # Literal floor cutoff; the coefficient of log(p) at n = p**i.
    return x/n - 1 if n <= x.numerator // x.denominator else F(0)


pp = prime_powers(128)
intervals = points = crossings = higher = ties = 0
for i in range(8, 161, 3):
    u = F(i, 4)
    for width in (F(1, 8), F(1), F(7, 2), F(45, 2), F(71)):
        v = u + width
        intervals += 1
        for t in (F(0), F(1, 8), F(1, 4), F(1, 2), F(2, 3), F(1)):
            x = u + t * width
            lhs, rhs = {}, {}
            points += 1
            for p, n in pp:
                jump = ((1-t)*source_coefficient(u, n) + t*source_coefficient(v, n)
                        - source_coefficient(x, n))
                tent = F(0)
                if u < n < v:
                    tent = (1-t)*(n-u) if n <= x else t*(v-n)
                    crossings += 1
                    higher += n != p
                ties += n == x
                lhs[p] = lhs.get(p, 0) + jump
                rhs[p] = rhs.get(p, 0) + tent/n
                assert jump == tent/n and jump >= 0
            assert lhs == rhs

windows = node_count = gap_count = edge_count = 0
for m in range(16, 81):
    for part in (F(0), F(1, 3), F(2, 3)):
        y = (m + part)**2
        b = (m + part)**3
        left = ceil_root(y+1)**2 - 1
        right = floor_root(b)**2 - 1
        first = isqrt(isqrt(left + 1))
        last = isqrt(isqrt(right + 1))
        anchors = sorted({left, right} | {j**4-1 for j in range(first, last+1)
                                         if left < j**4-1 < right})
        assert y <= left < right and right+1 <= b
        assert (left-y)**2 <= 9*y and (b-right)**2 <= 9*right
        edge_count += 2
        for s in anchors:
            assert isqrt(s+1)**2 == s+1 and y <= s <= s+1 <= b
        for s, t in zip(anchors, anchors[1:]):
            assert (t-s)**4 <= 7**4*s**3
            gap_count += 1
        node_count += len(anchors)
        windows += 1

# For p=2, log(2)>1/2; no other prime power is crossed.
d = F(1, 16)
u = F(2) - d
upper = d*d/(2*u)
arithmetic_lower = d/(2*2)*F(1, 2)
assert arithmetic_lower > 2*upper
print(f"source: {intervals} intervals, {points} points, {len(pp)} prime-power indices;"
      f" {crossings} interior index visits ({higher} higher powers), {ties} evaluation ties")
print(f"mesh: {windows} windows, {node_count} anchor visits, {gap_count} adjacent gaps,"
      f" {edge_count} edge bounds")
print(f"cusp: deterministic upper {upper}, arithmetic lower {arithmetic_lower};"
      " the absolute bound with the one-sided constant fails")
```

</details>

[policy]: https://github.com/OVVO-Financial/RH_Lean/blob/5fefebadf176092a7cd83a4e16aca1f0ec0ce60e/AGENTS.md
[contract]: https://github.com/OVVO-Financial/RH_Lean/blob/5fefebadf176092a7cd83a4e16aca1f0ec0ce60e/CURRENT_PROOF_CONTRACT.md
[directive]: https://github.com/OVVO-Financial/RH_Lean/blob/5fefebadf176092a7cd83a4e16aca1f0ec0ce60e/docs/RHLEAN_FINAL_PR_1201_PROOF_CLOSURE_20261124.md
[pragents]: https://github.com/OVVO-Financial/RH_Lean/blob/0b9f49ce640e98b3b9c81a29d71d6d98d69f62a9/AGENTS.md
[arith]: https://github.com/OVVO-Financial/RH_Lean/blob/0b9f49ce640e98b3b9c81a29d71d6d98d69f62a9/RHLean/Analysis/AlpogeNativeFourCharacterArithmetic.lean#L29
[handoff]: https://github.com/OVVO-Financial/RH_Lean/blob/5fefebadf176092a7cd83a4e16aca1f0ec0ce60e/RHLean/Analysis/AlpogeNativeBoundHandoff.lean#L69
[recovery]: https://github.com/OVVO-Financial/RH_Lean/blob/0b9f49ce640e98b3b9c81a29d71d6d98d69f62a9/RHLean/Analysis/AlpogeThin/NativeExistingRecoveryPayment.lean
[oldchord]: https://github.com/OVVO-Financial/RH_Lean/blob/0b9f49ce640e98b3b9c81a29d71d6d98d69f62a9/RHLean/Analysis/AlpogeSignedSquareInterpolation.lean#L176
[unit]: https://github.com/OVVO-Financial/RH_Lean/blob/0b9f49ce640e98b3b9c81a29d71d6d98d69f62a9/RHLean/Analysis/AlpogeNativeGzRealInterpolation.lean#L54
[move]: https://github.com/OVVO-Financial/RH_Lean/blob/0b9f49ce640e98b3b9c81a29d71d6d98d69f62a9/RHLean/Analysis/AlpogeThin/NativeScalarSupplierPayment.lean#L223
[payment]: https://github.com/OVVO-Financial/RH_Lean/blob/0b9f49ce640e98b3b9c81a29d71d6d98d69f62a9/RHLean/Analysis/AlpogeThin/NativeConstructedDyadicGzPayment.lean
[cost]: https://github.com/OVVO-Financial/RH_Lean/blob/0b9f49ce640e98b3b9c81a29d71d6d98d69f62a9/RHLean/Analysis/AlpogeNativeCostNormalization.lean
[physical]: https://github.com/OVVO-Financial/RH_Lean/blob/0b9f49ce640e98b3b9c81a29d71d6d98d69f62a9/RHLean/Analysis/AlpogeNativeSignedSlopeComparison.lean#L56
[sizes]: https://github.com/OVVO-Financial/RH_Lean/blob/0b9f49ce640e98b3b9c81a29d71d6d98d69f62a9/RHLean/Analysis/AlpogeThin/NativeGeometricCostWindows.lean#L238
[inwin]: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/Conclusion1OfGainBoundAll.lean#L99
[box]: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Formalism/SharpRestriction/GrowthBounds/LogarithmicSums/ThirdEstimateOfNumericFacts.lean#L19
[selector]: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsWeightsInWindows.lean#L18
[joint]: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/WeightWindowRequirementHostOfPoint.lean#L17
[data]: https://github.com/OVVO-Financial/RH_Lean/blob/0b9f49ce640e98b3b9c81a29d71d6d98d69f62a9/RHLean/Geometry/AlpogeSignedSlope/Formalism/RankGapBounds/MeanBoundSecondForm.lean#L98
[errors]: https://github.com/OVVO-Financial/RH_Lean/blob/0b9f49ce640e98b3b9c81a29d71d6d98d69f62a9/RHLean/Geometry/AlpogeSignedSlope/Formalism/SizeWindowBrackets/ErrorWindows.lean
[eath]: https://github.com/OVVO-Financial/RH_Lean/blob/0b9f49ce640e98b3b9c81a29d71d6d98d69f62a9/RHLean/Analysis/AlpogeThin/NativePrincipalEAtH.lean#L219
[coregm]: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean#L12
[coreath]: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/PrimitiveCosets/CoreAtH.lean
[chtop]: https://github.com/CocoSgt/riemann-hypothesis-lean/blob/7cbf7a0c32fca1badf05931879a37c3f8a2b03b4/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean
[intake]: https://github.com/OVVO-Financial/RH_Lean/tree/5826297f5ce97d27c90e8215e5d64384fcc20155/research/agent_reports
[coords]: https://github.com/OVVO-Financial/RH_Lean/blob/5826297f5ce97d27c90e8215e5d64384fcc20155/research/agent_reports/2026-11-24/00-coordinator-am.md
[owner]: https://github.com/OVVO-Financial/RH_Lean/blob/5826297f5ce97d27c90e8215e5d64384fcc20155/research/agent_reports/2026-11-24/10-owner-payment.md
[referee]: https://github.com/OVVO-Financial/RH_Lean/blob/5826297f5ce97d27c90e8215e5d64384fcc20155/research/agent_reports/2026-11-24/50-adversarial-referee.md
[external]: https://github.com/OVVO-Financial/RH_Lean/blob/5826297f5ce97d27c90e8215e5d64384fcc20155/research/agent_reports/EXTERNAL_HANDOFFS.md
[compare]: https://github.com/OVVO-Financial/RH_Lean/compare/973a8810f35d5ca3b9fa2f30d2315edac412a193...0b9f49ce640e98b3b9c81a29d71d6d98d69f62a9
[oldci]: https://github.com/OVVO-Financial/RH_Lean/actions/runs/45518601597/job/138884648354
[censusci]: https://github.com/OVVO-Financial/RH_Lean/actions/runs/45518601528/job/138884401789
[pr1205]: https://github.com/OVVO-Financial/RH_Lean/pull/1205
[handci]: https://github.com/OVVO-Financial/RH_Lean/actions/runs/45309220195/job/138160666430
[buildci]: https://github.com/OVVO-Financial/RH_Lean/actions/runs/45309220195/job/138161896915

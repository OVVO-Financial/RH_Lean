# Lean Verification | November 25, 2026

## Opening checkpoint | LV-20261125T101000Z-OPEN | IN_PROGRESS

Scheduled ChatGPT invocation, 2026-11-25 05:10 EST (10:10 UTC), America/New_York; RUN_ID_UNAVAILABLE. FINAL_1201_ROLE=LEAN; final_1201_ack=FINAL_PR_1201_PROOF_CLOSURE_V1; continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1; publish_ack=REPORT_PUBLISH_RECOVERY_V1. DIRECT_CORE_CUT_V1 and STRICT_NO_GEOCL_ANYGEOMETRY_V1 remain in force. No native RH claim.

[Main](https://github.com/OVVO-Financial/RH_Lean/commit/7cb76d913acfd68fc036e01673a876a9a77be90f): AGENTS blob a60620dca883d98dbe391ddd1ab5afcab805b96e, proof contract 6fa886e125321056739a48d09fd33c95edaebf6b, closure directive 395378d0e6525fab6c6ed9b7315c5de4c36329dd. [Draft #1201](https://github.com/OVVO-Financial/RH_Lean/pull/1201) head c94fc79fe452d568eb877fbe64f17ad638e7bc0d; branch AGENTS 2bf7b75c5abb01962ecd9989320b600315e1a46f. Initial report-tree commit 9950a5de58c08fb7b2b02da349a1982d6cca17e1. At intake, no previous Nov 25 Lean report. Coordinator and Owner TODAY=PENDING / YESTERDAY=CARRY_FORWARD; current Analytic, Wheel, Census and Referee final sections found. Resume previous Lean final LV-20261125T020800Z-FINAL, blob ff6acf015a1c890bd339d27b6b16aee456ee5b14. External inbox remains 7d63d434690d00dffce9c90335d41c4f62d85798.

**Engineering:** [warning-fatal preflight](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45548060914/job/138985874764) failed at NativeSummandCovolume.lean:45-46 on the PR test merge 79313611be39f71636d5ad2c3edd2c6f8238b241. The diagnostic pass separately records NativePrincipalEAtH built; not an overall pass or a strict root audit. Investigate the actual ordered-product lemma, preserve Gram nonnegativity and the integral index, and coordinate any focused change on the existing draft only. **Mathematics:** test primitive-coordinate recovery with competing edges on the actual source interface. The independently measured same-host signed gain, both averaged losses and the complete uniform window remain open.

## Engineering milestone | LV-20261125T101000Z-GRAM

[PR review](https://github.com/OVVO-Financial/RH_Lean/pull/1201#pullrequestreview-6055736065) and [inline repair](https://github.com/OVVO-Financial/RH_Lean/pull/1201#discussion_r4693454606) read back on head c94fc79fe452d568eb877fbe64f17ad638e7bc0d. The pinned Mathlib lemma is `Finset.prod_le_prod₀`, with both nonnegativity and comparison premises. The two still-valid manifest updates are linked in the review; yesterday's GenericLieMetric source/manifest correction has been superseded by a compiled branch repair. The three-edit patch applies and reverses on the exact Git blobs, SHA-256 d197e96824ce3def25ea278c820ea102381ad47d5bab5d523452152031ed8b05. The hosted diagnostics built NativePrincipalEAtH, NativeCMSerreGenericLieMetric, NativeSquareCapacityPeriod and NativeCore33HostDegree; the preflight failed, the full job was skipped and the proposed repair is not a new head. `PATCH=REVIEW_SUGGESTED; SOURCE_COMMIT=BLOCKED_WRITE_ACCESS; EXACT_HEAD_CI=FAILED`. No local Lean, no duplicate PR or no-op rerun.

## Final findings | LV-20261125T101000Z-FINAL | November 25, 05:10 EST run

### A. Result

**A common lift, not a collection of separate lifts, is required for recovery on a selected edge.** I derived an exact test for the additional depth needed to preserve a prescribed coordinate while satisfying all competing incoming edges. Even when each competitor separately costs zero depth, their joint cost can consume the entire allowance. This is a local obstruction to a proposed way of supplying the rows, not a counterexample to physical recovery or to RH. Claims `LV-20261125-LIFT1–2` below are paper proofs with exact finite checks and new Lean proof text, **not hosted-certified theorems**.

For [draft #1201](https://github.com/OVVO-Financial/RH_Lean/pull/1201), I posted a [one-line compilation repair](https://github.com/OVVO-Financial/RH_Lean/pull/1201#discussion_r4693454606) and [four additional roots for the existing strict audit](https://github.com/OVVO-Financial/RH_Lean/pull/1201#pullrequestreview-6055884771). Together with two outstanding manifest rows they form one application-checked patch. The author’s earlier scalar repair compiled. The new patch has **not** been committed or compiled; the actual latest preflight remains red.

### B–D. Authority and selection

[Main instructions](https://github.com/OVVO-Financial/RH_Lean/blob/7cb76d913acfd68fc036e01673a876a9a77be90f/AGENTS.md), [proof contract](https://github.com/OVVO-Financial/RH_Lean/blob/7cb76d913acfd68fc036e01673a876a9a77be90f/CURRENT_PROOF_CONTRACT.md), [final assignment](https://github.com/OVVO-Financial/RH_Lean/blob/7cb76d913acfd68fc036e01673a876a9a77be90f/docs/RHLEAN_FINAL_PR_1201_PROOF_CLOSURE_20261124.md), [semantic acceptance](https://github.com/OVVO-Financial/RH_Lean/blob/7cb76d913acfd68fc036e01673a876a9a77be90f/research/RHLEAN_FULL_SEMANTIC_RISK_AUDIT_20261124.md) (blob `1029b89123471c04da44b0d91f382d7291cf1f14`), and [actual branch instructions](https://github.com/OVVO-Financial/RH_Lean/blob/c94fc79fe452d568eb877fbe64f17ad638e7bc0d/AGENTS.md) govern this run. Main `7cb76d913acfd68fc036e01673a876a9a77be90f` and proof head `c94fc79fe452d568eb877fbe64f17ad638e7bc0d` were rechecked at 10:31:29 UTC. The public [canonical target](https://github.com/OVVO-Financial/RH_Lean/blob/7cb76d913acfd68fc036e01673a876a9a77be90f/research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean) is one $C\ge0$ for every integer $R\ge2$ in $|\pi(R^2)-VF_{\rm can}(R^2)|\le CR\log R$ (blob `79030d70e8d3e0d08eef9bac53fef95c36eca2fb`). #1201 is the sole native completion PR; [#1207](https://github.com/OVVO-Financial/RH_Lean/pull/1207) is an open citation proposal, not a constructed supplier.

Priority A was the reached warning-fatal diagnostic; next was the Referee's confirmed audit-coverage gap. For mathematics I selected a narrower question raised by `REF-20261125-ROW3` and `FW-20261125-PARTNER4`: when does a *fixed block of physical evaluations* preserve its full coordinate recovery after all off-edge restrictions? The accepted finite-width and local-rank observations do not supply that test on measured native rows. I did not rebuild the upstream family, duplicate #1205's conditional endpoint, or infer a new bound from a determinant identity.

### E. Native statement and quantifiers

For $x\ge1$, the [native source](https://github.com/OVVO-Financial/RH_Lean/blob/c94fc79fe452d568eb877fbe64f17ad638e7bc0d/RHLean/Analysis/AlpogeNativeFourCharacterArithmetic.lean#L30) is
$$
Z(x)=\sum_{1\le n\le\lfloor x\rfloor}\Lambda(n)(x/n-1)-x\log x+(1+\gamma)x .
$$
It includes all prime powers. [Principal cyclic identification](https://github.com/OVVO-Financial/RH_Lean/blob/c94fc79fe452d568eb877fbe64f17ad638e7bc0d/RHLean/Analysis/AlpogeThin/NativeExistingRecoveryPayment.lean) gives $G_m=Z$; it is an identity. With fixed real $e_D,e_L$ and $\varepsilon_1>0$, let $K=e_D+e_L+7$. [Merged #1205](https://github.com/OVVO-Financial/RH_Lean/blob/7cb76d913acfd68fc036e01673a876a9a77be90f/RHLean/Analysis/AlpogeNativeBoundHandoff.lean) consumes $\forall\,0<\varepsilon<\varepsilon_1,\ \exists C_\varepsilon,\ \forall Y_0,\ \exists Y\ge Y_0,\ \forall y\in[Y,Y^{3/2}],\ Z(y)\le C_\varepsilon y^{1/2+K\varepsilon}$. The principal-cyclic transport takes coefficient one above its threshold on a set containing such cofinal complete windows. No independent coefficient or pair may be selected afresh for each point.

[Principal EAtH](https://github.com/OVVO-Financial/RH_Lean/blob/c94fc79fe452d568eb877fbe64f17ad638e7bc0d/RHLean/Analysis/AlpogeThin/NativePrincipalEAtH.lean#L263) supplies a threshold for each $0<\varepsilon<1/52$, one `PairGood` $q,d$ for each subsequent window, and for each point an $e\ge2$ with `PageN` and EAtH for **every** top set. The new square-clock specialization accepts the payment's *existing* pair on $[A^2-1,(A^2-1)^2]$: every $X_R=R^2-1$, $A\le R\le A^{3/2}$, and the full cell $[X_R,X_R+1]$ fit. Do not identify two separate existentially selected pairs.

[Constructed payment](https://github.com/OVVO-Financial/RH_Lean/blob/c94fc79fe452d568eb877fbe64f17ad638e7bc0d/RHLean/Analysis/AlpogeThin/NativeConstructedDyadicGzPayment.lean) controls the mean of $Z(a(t)/b)$ by the physical top excess divided by $Q$ plus $x^{1/2+\varepsilon}$. Write $n=|H_e|$, $T=|TT|$, $\Delta=|T_2|/n$, $Q=Tmb\Delta/2>0$, $z=x^\varepsilon$. The **unpaid** complete signed comparison, in the [actual normalization](https://github.com/OVVO-Financial/RH_Lean/blob/c94fc79fe452d568eb877fbe64f17ad638e7bc0d/RHLean/Analysis/AlpogeNativeCostNormalization.lean), is
$$
\frac{\langle ASK-\Re MAIN\rangle_{A_0}}{Q}
\ \le\ x^{CErr(C)\varepsilon}
\left[\frac{2a_E}{mb\Delta}\left(1+\frac{m^2}{k}\right)
+\frac{4nmz}{T\Delta}+\frac{2kz^2}{nT}\right].
$$
Here $A_0$ is the full original base subgroup, $k=D_0.k$, $a_E=D_0.a$. The [signed consumer](https://github.com/OVVO-Financial/RH_Lean/blob/c94fc79fe452d568eb877fbe64f17ad638e7bc0d/RHLean/Analysis/AlpogeNativeSignedSlopeComparison.lean) keeps `HidaSetting, DIV, EComp5, HComp, Count5, Slopes, QuotientSlopeBoundsWith, Losses, SlopeIneq, HHBound, FParams`. Its window application also needs `ErrWindows, LargeX`, the two $B_0,N_c$ bounds and `GeometricSizeWindows`. In particular `physicalData_Ga` preserves $D_0.Ga$; it does not construct gain. The original $q,d,e,TT,T_2$, widths, heights, ranks, Frobenius/inertia, ramification, $\lceil A_{\max}/\beta\rceil$, log derivative, signed recovery and complementary terms stay on the same data. [Mean-to-point](https://github.com/OVVO-Financial/RH_Lean/blob/c94fc79fe452d568eb877fbe64f17ad638e7bc0d/RHLean/Analysis/AlpogeThin/NativeScalarSupplierPayment.lean) already exists; it charges the *actual* mean height displacement. What is missing is its payment, not another transport theorem.

### F. Independent local proof

**LV-20261125-LIFT1: exact joint obstruction.** Fix one selected incoming edge $e$, its actual source-side rows $F_i$, and $A=N_{\rm tgt}(L)$. For the other **selected incoming** edges $j$, set $C_j=A\cap w^{c_\star}R'(j)$; put $C=\bigcap_j C_j$. These are the restrictions on the *same* witness $G$ in the [literal `SrcTests` clause](https://github.com/leanprover-community/riemann-hypothesis/blob/27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59/src/Formalism/SharpRestriction/GrowthBounds/ScaleEdges/ManyEdges.lean#L26). They are not the different same-source restrictions on $F_i$. Use the injective coefficient embedding and the required integrality to write $\Phi:A\to\mathcal O^s$, $\Phi(G)_i=be(F_i,G)$, over the actual DVR $\mathcal O$. Let $K_0=\ker\Phi$, and let $\rho:A\to\bigoplus_j A/C_j$ be the joint residue map. All sets of selected edges here are finite.

Suppose unfiltered coordinate lifts $J:\mathcal O^s\to A$ have been independently obtained at a *fixed* depth $D_0$, so $\Phi J=p^{D_0}I$. Define
$$
\delta(u)=[\rho(Ju)]\ \in\ \rho(A)/\rho(K_0).
$$
For every integer $h\ge0$, all prescribed coordinates have simultaneous lifts in $C$ at $D_0+h$ **iff** $p^h\delta=0$. The class is independent of $J$: two choices with the same evaluation differ in $K_0$. If $G_i\in C$ lifts $p^{D_0+h}e_i$, then $p^hJe_i-G_i\in K_0$ corrects its complete residue. Conversely, when the residue classes vanish, choose $k_i\in K_0$ with $\rho(k_i)=\rho(p^hJe_i)$ and take $G_i=p^hJe_i-k_i$. Extend linearly from the coordinate basis. No independent choices of $G$ for the competing congruences were spliced together. No DVR structure is needed for the kernel-correction identity itself.

These filtered coordinate lifts imply the per-edge primitive test by selecting a unit coordinate of each coefficient vector. Conversely, the image-lattice `smith_mem` argument **inside** [`goodRank_of_prim`](https://github.com/leanprover-community/riemann-hypothesis/blob/27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59/src/Formalism/SharpRestriction/GrowthBounds/ScaleEdges/GoodRankOfPrim.lean#L34), applied to the filtered lattice with the original additive, linear and integral evaluation hypotheses, gives full prescribed coordinate lifts from that primitive test. This is *not* an equivalence with arbitrary partial rank and an arbitrary decoder in [`GoodRankK/LPprimeAt`](https://github.com/leanprover-community/riemann-hypothesis/blob/27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59/src/Formalism/SharpRestriction/GrowthBounds/UnramifiedQuadraticSetting.lean#L208).

**Budget consequence.** Since $A\subseteq R'(j)$, scaling every lift by $w^{c_\star}$ always enforces these target-side congruences. But $p=w^2$: booking the unrestricted worst-case extra depth $h=\lceil c_\star/2\rceil$ can **never**, for $D_0\ge0$, meet the `s7` condition $2(D_0+h+1)\le c_\star$. This does not rule out smaller independently measured joint obstructions, selected subblocks, or other recovery constructions. Nor do we assume $w$ is a uniformizer.

**LV-20261125-LIFT2: sharp two-competitor test.** For an integral domain, any nonzero nonunit $w$, and $c,m,D\in\mathbb N$, take the local model $A=\mathcal O^2$, $\Phi(x,y)=x$, $p=w^2$. Require both $x+y$ and $(1+w^m)x+y$ to be divisible by $w^c$. Each single condition admits every $x$ at depth zero. Together, at $x=p^D$,
$$
\exists y\text{ satisfying both}\quad\Longleftrightarrow\quad c\le m+2D.
$$
Subtracting the two congruences gives $w^c\mid w^m x$; $y=-x$ proves sufficiency. Cancellation and nonunitness give $w^c\mid w^{m+2D}$ iff $c\le m+2D$. Each individual quotient is $\mathcal O/(w^c)$, irrespective of $m$. Nevertheless the least joint depth is $\lceil(c-m)_+/2\rceil$. In a DVR the individual congruence lattices can be written $A\cap w^cR'_j$ with $R'_j=w^{-c}C_j$. That realizes **the shape of the local target filter**, not a physical identification of the repository's $R'(j)$, a chosen prime pair, a source-side word, or a signed gain.

With $c=8$, $m=0,\ldots,8$, the depths are **4, 4, 3, 3, 2, 2, 1, 1, 0**. The `s7` allowance permits at most 3, so the first two cases fail despite both separate tests succeeding. The full `LPprime` has a separate $4(D+1)\le c_\star$ gate (at most 1 here); satisfying that number alone would not produce its all-lattices quantifier. The arithmetic $m$ in this regression is a local exponent, **not** the host multiplicity. `PAPER_PROOF / FINITE_COMPUTATION; SELF_AUDIT; INDEPENDENT_REVIEW=PENDING`.

### G–J. Implementation, CI and repair

**Compiler diagnosis (LV-20261125-GRAM1).** Revision `c94fc79fe452d568eb877fbe64f17ad638e7bc0d`, branch `research/cm-seed-serre-degree-20261123`, targets `main`. GitHub PR metadata reports base SHA `5fefebadf176092a7cd83a4e16aca1f0ec0ce60e`. The actual [test merge](https://github.com/OVVO-Financial/RH_Lean/commit/79313611be39f71636d5ad2c3edd2c6f8238b241) has parents `7cb76d913acfd68fc036e01673a876a9a77be90f` and `c94fc79fe452d568eb877fbe64f17ad638e7bc0d`. The [static audit](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45548060914/job/138985700600) passed. The [warning-fatal research preflight](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45548060914/job/138985874764) failed at `NativeSummandCovolume.lean:45:10` (“Function expected”) and line 46 (“No goals to be solved”). The independent diagnostic repeated the same error; its later runner shutdown/143 is not the original failure. The [full Lean job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45548060914/job/138991231922) was skipped. Of 26 workflow runs returned for this PR head, 20 succeeded, five were cancelled, one failed. No rerun requested.

The diagnostic log records builds of `NativePrincipalEAtH` (04:54:21Z), `NativeCMSerreGenericLieMetric` (04:57:02Z), `NativeCore33HostDegree` (04:57:24Z), and `NativeSquareCapacityPeriod` (04:51:49Z). These are real module builds, **not** passes for the root audit or full checkout. [Proof inventory](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45548060842) and [public export](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45548060488) succeeded. The [hosted semantic census](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45548060686/job/138982316988) scanned 3,592/3,592 tracked Lean files on the test merge, no scan failures. I compared both complete Git trees: **all 3,591 PR-head Lean paths match byte-for-byte**; the sole extra Lean file on the merge is the Stage 1 conditional companion, `6d5fe991c22d24551bba46e8c1030ce55838c0df`. Reuse the hosted scan; it is not independent semantic clearance or a kernel telescope.

At [the reached source](https://github.com/OVVO-Financial/RH_Lean/blob/c94fc79fe452d568eb877fbe64f17ad638e7bc0d/RHLean/Geometry/NativeSummandCovolume.lean#L45), the [general ordered-product lemma](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Algebra/Order/BigOperators/Group/Finset.lean#L111) takes one proof; [the nonnegative real-product lemma](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean#L39) takes the required two. The proposed line is `refine Finset.prod_le_prod₀ ?_ (fun v _ => hB v)`. The existing [Gram norm identity](https://github.com/OVVO-Financial/RH_Lean/blob/c94fc79fe452d568eb877fbe64f17ad638e7bc0d/RHLean/Geometry/AlpogeAllPlace/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtGram.lean) proves the first premise, and $h_B$ the second. No premise, determinant, integral span index, sign or normalization changes. The author repaired the previous scalar at `2cec65b032bb616246eb237e23419824cd6b75c0`; its current source SHA-256 matches its manifest. [SigmaMetric](https://github.com/OVVO-Financial/RH_Lean/pull/1201#discussion_r4689486816) (268 lines) and [SchemeTorsion](https://github.com/OVVO-Financial/RH_Lean/pull/1201#discussion_r4689486836) still need their two measured manifest updates.

**Coverage (LV-20261125-ROOTS1).** [The current strict audit](https://github.com/OVVO-Financial/RH_Lean/blob/c94fc79fe452d568eb877fbe64f17ad638e7bc0d/research/ALPOGE_PRINCIPAL_EATH_STRICT_AUDIT_20261124.lean) checks permitted axioms and walks types **and opaque bodies**, but does not explicitly root `nativePrincipalCyclicGm_eq`, `nativeConstructedDyadicSignedSlopePayment_of_meanLoss`, `nativeSmallEpsilonWindowBound_of_principalCyclic`, or `nativeGz_le_of_mean_normalizedCosts`. The [two additional suggestions](https://github.com/OVVO-Financial/RH_Lean/pull/1201#pullrequestreview-6055884771) add only the two source imports and four existing roots; both modules already occur in the mandatory build command. No checks removed. New closed suppliers and a future literal native terminal will require their own independent checks. Absence of prohibited names is not an audit for renamed, inlined or semantically vacuous witnesses.

Both reviews and inline comments were fetched back at the exact head. **One combined patch**: source blob `263b6a1391747b2014e3fc040f53a6caeae7a46a`, strict audit `6f79672f7097157a69590b101e7a46a715993cbd`, manifest `e23684a7e5e2c12fe5ba1b16c23287175c9a12ed`; patch SHA-256 `f7e020f8c7ea606483664822faa1005708bf7a8cf29c987a1b4e1321da69c320`. Diff whitespace, forward application to the exact blob index, and reverse application to the edited copies all passed. This extends the smaller hash in the milestone. File writes through this connection are restricted to dated Lean reports on `agent-reports`. Direct Git transport returned tunnel 403; no unrelated write path was used to evade the restriction. `BLOCKED_WRITE_ACCESS` for committing these changes to #1201, **not** an unverified claim about the owner's GitHub rights. No branch push, merge, local Lean run or speculative CI restart.

**New local Lean proof text.** Appendix 1 gives two complete declarations for LIFT1's algebraic core and LIFT2's exact equivalence. The code uses [`dvd_sub`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Algebra/Ring/Divisibility/Basic.lean#L121) and [`pow_dvd_pow_iff`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Algebra/GroupWithZero/Divisibility.lean#L168) at the native pin. It has no assumed gain or RH result and is separate from the proposed CI repair. `SOURCE_PREPARED / NOT_PR_COMMITTED / NOT_HOSTED_VERIFIED`. The two `#print axioms` commands are requests for future output, **not** axiom receipts.

### K–M. Significance and independent checks

The test distinguishes restrictions that the same evaluation kernel can absorb from individually soluble but incompatible restrictions. A measured image, not marginal indices or an occurrence count, decides this particular recovery question. It supplies a falsifier and a constructive correction at a prescribed depth. It does **not** supply the missing row, rank quota, physical gain, or either loss average. No evidence that the global scalar bound implies those particular witnesses; no target-equivalence claim.

In the exact regression take $\mathcal O=\mathbb Z_p[\sqrt p]$, $w=\sqrt p$. In $\mathcal O/(w^c)$ use basis $1,w$ with coefficient moduli $p^{\lceil c/2\rceil},p^{\lfloor c/2\rfloor}$ and multiplication by $w:(a,b)\mapsto(pb,a)$. The script enumerated every candidate $y$ in 419 parameter tuples, 1,410,811 lift tests in total; each individual congruence had exactly one solution, and the common-lift prediction agreed in every case. A further 60 direct congruence tests at $p=13,c=8$ (using the unique candidate from the first congruence) verified the displayed depths. This is finite algebra, **not** verification of `PairGood` or native geometric data.

**External versus native.** [#1205](https://github.com/OVVO-Financial/RH_Lean/pull/1205) tested head `45d86f3f728e94e476427ffa41e5a0620bb74be0`, merged `fde7ea71ed88f540a8829554a8ab4602bda96f4d`. Its [named conditional roots](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45309220195/job/138160666430) and [hosted build](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45309220195/job/138161896915) passed; the handoff blob is unchanged at `31dc576197075a0448ced1a1c58e24a35c6d80d6`. [#1211](https://github.com/OVVO-Financial/RH_Lean/pull/1211) is now **merged** at current main. Its [actual Stage 1 log](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45531344512/job/138927151494) on PR head `088ec054cfec3b04ab19abf016e4d85545047c77` reports the external closed root, 1,478,181 dependencies and `propext, Classical.choice, Quot.sound` in its **separate Lean 4.33.1 environment**. The [template](https://github.com/OVVO-Financial/RH_Lean/blob/7cb76d913acfd68fc036e01673a876a9a77be90f/scripts/alpoge_stage1/ClosedRH.lean.in) uses `externalTopG`; the [exact frozen supplier](https://github.com/homeowmorphism/riemann-hypothesis-original/blob/774b9e8022f50d20be861ecc9d609cfc26436a81/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean#L60) calls `geoCl anyGeometry` at 60/63/67. That replay is real but inadmissible under #1201's strict native rule. The [cleaned community version](https://github.com/leanprover-community/riemann-hypothesis/blob/27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/SiegelEisensteinSecondTermHypotheses.lean#L1933) retains the actual covolume premise; [`core_gm`](https://github.com/leanprover-community/riemann-hypothesis/blob/27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59/src/Development/AutomorphicArithmetic/PrimitiveCosets/LevelGmLeOnFamilyScales.lean#L1337) takes both `EAtH` and `CoreAtH`. Neither the old rejection nor the external success proves or refutes the clean native application.

### N. Specialist continuity and handoffs

Verified complete Nov 24/25 files against directory byte lengths and Git blob hashes at [the intake snapshot](https://github.com/OVVO-Financial/RH_Lean/tree/9950a5de58c08fb7b2b02da349a1982d6cca17e1/research/agent_reports); dated folders were enumerated without a lookback cap. Coordinator's Nov 24 mirrors are byte-identical and count as one. No Nov 23 folder; no recovery siblings on Nov 24/25. The previous own report explicitly records the Nov 22 recovery/watermark history; its earlier archive-exhaustiveness caveat is not retroactively cleared. All newly relevant sections since that report's verified watermarks were consumed through the final refresh; a missing publication is not evidence of an invocation.

| Role | Last consumed → latest verified actual final / blob | First handoff |
|---|---|---|
| Coordinator | Nov 24 DIRECT1–3 `33e418f2df05b7c71c9239fa6609cb22abb48349` → Nov 24 23:09 EST `COORD-20261124-WIDTHLAW1–4`, `960b5843affc6cf2765d90b92547e12d656b50e8`. TODAY=PENDING; YESTERDAY=CARRY_FORWARD. | Width-law comparison reduces candidate rows, not their price. Add the joint kernel-residue test before funding a block of rows. |
| Owner | Nov 24 19:56:24 `OP-20261124-LOCALGAIN1–4`, `74f9baaea9fa0e4043e79e01e99d732e61daab86`, unchanged. TODAY=PENDING; YESTERDAY=CARRY_FORWARD. | Supply one actual block of words, their evaluations, source-side off-edge memberships and measured common gain. Local orbit/rounding credit alone is not both losses. |
| Analytic | Nov 24 WINDOW1–4 `32cc8ba27f99490c5aac69987f5eec86f0230958` → Nov 25 01:04:01 `ATII-20261125-TOPLAW1–4`, `11e89f84ece71cbaa810860ad37c268abfe754d1`. | Restore variable-height movement after common-height comparison. Translate balance by itself is insufficient; keep one scale-independent constant. |
| Wheel | Nov 24 partial `a91e22deebbbd0964b4d8a03d4ae6daf67b6369a` → completed `FW-20261124-FIBER1–4` `eca61b12421b8d15e717677b1a4a71321fc81650` → Nov 25 02:05:01 `FW-20261125-PARTNER1–4` `93f18c6e1475ff9ca69c1ae49df2dae1f07d3232`. | Partial recovery/exceptional layers concern identified evaluations; compute the joint image of their unchanged kernel on genuinely competing edges. |
| Census | Nov 22 FOURPOWER1–4 `f8f96d3ce7b2e2f1305b0a1984d6f936c9f55448`; Nov 23–24 no report → Nov 25 03:11:01 `PC-20261125-HEIGHTFIBRE1–4` `96b465a19ec643b83c8c21f27c20a100807246fc`. | Measured height classes and ramified squares matter. First obtain an actual filtered incidence matrix before interpreting the finite regression physically. |
| Referee | Nov 24 CORE1–5 `bfb4c06772fe4b5df481d27921abe0a49ce73802` → Nov 25 04:13 `REF-20261125-ROW1–4` `e857d047300ea59650c4c6eda319d64353c3c2ef`. | Review LIFT1–2 for the specified primitive block, not all decoders. ROW1 rejects occurrence-count rank; ROW3 remains a necessary test on competing **source** edges. Today's test is on the selected competing **target** edges. |
| Lean | Nov 24 21:08 `LV-20261124-PERIOD1` and METRIC1, `ff6acf015a1c890bd339d27b6b16aee456ee5b14` → this 05:10 run, opening and engineering milestone above. | Earlier ordered-period conclusion received scoped referee acceptance and appears on the branch; the module built, but actual measured periods remain to be supplied. |

The [external inbox](https://github.com/OVVO-Financial/RH_Lean/blob/9950a5de58c08fb7b2b02da349a1982d6cca17e1/research/agent_reports/EXTERNAL_HANDOFFS.md) is unchanged. `EXT-20261018-PNT-1` and `EXT-20261017-XCOORD-1` retain their source/endpoint qualifications; `EXT-20261014-3/-5` do not supply native filtered rows or an all-root payment. The Referee's scoped acceptance of parts of TOPLAW, HEIGHTFIBRE, PARTNER and PERIOD is not acceptance of today's new LIFT claims. No specialist execution inferred or launched.

### O–P. First unpaid theorem and resume

**First local construction:** on one actually selected window pair and anchor, exhibit the physical source words $F_i$ with their same-source divisibility, and an unfiltered section or primitive certificate at a depth independently allowed by the budget. Measure the **joint** residue of its lifts modulo the residues of $\ker\Phi$. Kill it within the remaining depth on enough actual rows; preserve the quota, `BePerfect`, dominance and the relevant $c_\star$ inequalities. [`lengthFromAllBut_of_sandwich`](https://github.com/OVVO-Financial/RH_Lean/blob/c94fc79fe452d568eb877fbe64f17ad638e7bc0d/RHLean/Geometry/NativeServedPrimeApplication.lean) bounds a quotient after its inclusions, exceptional layers and stopping hypotheses; it does not furnish these evaluations or their valuation gain.

**First global estimate:** realize `QuotientSlopeBoundsWith DP C Xpp` and `DP.Losses C`, in particular **both** $\operatorname{umean}(ASK-Ga)\le LoP$ and $\operatorname{umean}(IO)\le LoP$, on that same constructed gain, with the other measured terms above (or independently prove the complete normalized signed comparison). Return the paid mean to the point and to complete cofinal windows. Native source and terminal remain OPEN. No improved exponent.

**Engineering resume:** apply the reviewed patch once on #1201, check the resulting *new* head and its hosted warning-fatal job, named declaration output, opaque dependency/axiom gate, and full native build. Kernels, modules and evidence to retain: native Lean 4.34.1 (toolchain `ba8ebf2dbaf6a668cd2a0e086186d6d569b69ff5`), Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, PNT `c39a751132c88b6e8080b74c74023fd95b3d8be0`, Lake manifest `a34d142c3d75a602a8b0f8241a4fb504d5c7c5a4`. Original arithmetic `5203ec0e45b1d1f9b88d87e8b93455526169fbc8`; EAtH `ed98fe285987a38bc635a3729024bc3f3b1ac4b2`; constructed payment `89b83b14a060443aceab44fdb38478f07af5678b`; recovery `1076fb12c5bb2b1a85ed97f20aadfb105c4e2747`; signed comparison `d8250851cd4ddc640fdc89df8475dcc2c09a636a`; scalar return `51c8660dbc4d7109f71bbc9d6421e93aa06ce61a`; normalization `07ec36dabad5d06c97dde991fb8c7de99af442d7`. Community pin `27b55787485ac2a5b5b3ed2dffc697e0ae6a2f59`: `GoodRankOfPrim` blob `8c8d59af12e1f20b82b46b8efa881745fc60ff9a`, `ManyEdges` `7f043efac738a5e73ec785f5fe4435031babde4f`, `UnramifiedQuadraticSetting` `1c9ff6676bad3634a65d75f248b53bb82c03d1ee`. No cross-toolchain oleans.

Opening commit [395c7a6](https://github.com/OVVO-Financial/RH_Lean/commit/395c7a64025443214e5fea9e00e0d5c92df54629), blob `bb447dcefd0749897bac9b842e6f866b116fff80`, 2,030 bytes; [milestone commit 1213781](https://github.com/OVVO-Financial/RH_Lean/commit/121378193f7deef0b7bb0cc42beeeb6acd5ae5fd), blob `7727726673e9d9663e863eae4515c5cf2779c110`, 3,102 bytes. Both read back; final canonical append requires fresh SHA, exact full-prefix and immutable commit readback. `EXECUTION=COMPLETED; PROOF_PR=DRAFT; NATIVE_CI=FAILED; REPAIR=PROPOSED_NOT_COMMITTED; NEW_THEOREM_CI=NOT_RUN; MATH=PAPER_PROOF/FINITE_COMPUTATION_LOCAL; NATIVE_BOUND_AND_RH=OPEN`.

<details><summary>Appendix 1. Lean source for the two local results (not yet compiled)</summary>

Source SHA-256 `4e08855d22a0c327ab1bca83a283d37aa30f87ec9a74e053d5ae7a9f2c004252`. Independent local statements; do not insert a global hypothesis or modify the open-phase guard to test them.

```lean
import Mathlib

/-!
Local tests for one set of integral recovery rows. The residue map in the
first theorem must record *all* competing edges at once. The second theorem
tests a two-congruence model; it does not identify physical host lattices.
-/

namespace RHLean.Geometry

/-- A prescribed evaluation can survive all residue constraints exactly when
its joint residue can be corrected without changing the evaluation. -/
theorem exists_commonLift_iff_residue_mem_map_ker
    {O A V Q : Type*} [CommRing O]
    [AddCommGroup A] [Module O A] [AddCommGroup V] [Module O V]
    [AddCommGroup Q] [Module O Q]
    (f : A →ₗ[O] V) (r : A →ₗ[O] Q) (x : A) :
    (∃ y : A, f y = f x ∧ r y = 0) ↔ r x ∈ (LinearMap.ker f).map r := by
  constructor
  · rintro ⟨y, hy, hr⟩
    refine ⟨x - y, ?_, ?_⟩
    · change f (x - y) = 0
      rw [map_sub, hy, sub_self]
    · rw [map_sub, hr, sub_zero]
  · rintro ⟨k, hk, hr⟩
    change f k = 0 at hk
    refine ⟨x - k, ?_, ?_⟩
    · rw [map_sub, hk, sub_zero]
    · rw [map_sub, hr, sub_self]

/-- Both congruences use a single correction. Here the base scalar is w^2;
w need only be a nonzero nonunit, not a uniformizer. -/
theorem twoEdge_commonLift_iff_depth {O : Type*} [CommRing O] [IsDomain O]
    (w : O) (hw : w ≠ 0) (hnu : ¬ IsUnit w) (c m D : ℕ) :
    (∃ y : O, w ^ c ∣ (w ^ 2) ^ D + y ∧
      w ^ c ∣ (1 + w ^ m) * (w ^ 2) ^ D + y) ↔ c ≤ m + 2 * D := by
  let x := (w ^ 2) ^ D
  change (∃ y : O, w ^ c ∣ x + y ∧ w ^ c ∣ (1 + w ^ m) * x + y) ↔ _
  have hpow : w ^ m * x = w ^ (m + 2 * D) := by
    change w ^ m * (w ^ 2) ^ D = w ^ (m + 2 * D)
    rw [pow_add, pow_mul]
  constructor
  · rintro ⟨y, hy, hz⟩
    have h := dvd_sub hz hy
    rw [show (1 + w ^ m) * x + y - (x + y) = w ^ m * x by ring, hpow] at h
    exact (pow_dvd_pow_iff hw hnu).mp h
  · intro hc
    have h : w ^ c ∣ w ^ m * x := by
      rw [hpow]
      exact pow_dvd_pow w hc
    refine ⟨-x, ?_, ?_⟩
    · simp
    · rwa [show (1 + w ^ m) * x + -x = w ^ m * x by ring]

end RHLean.Geometry

#print axioms RHLean.Geometry.exists_commonLift_iff_residue_mem_map_ker
#print axioms RHLean.Geometry.twoEdge_commonLift_iff_depth
```

</details>

<details><summary>Appendix 2. Reproducible finite arithmetic (Python standard library)</summary>

Script SHA-256 `81709fb85df6d389f233a886673ff2250bba88fca25813d3f3f1e7b6f130b4b8`.

```python
"""Exact check of the two-competitor recovery test; no Lean execution."""

from itertools import product


def tests(p, c, exhaustive):
    a, b = p ** ((c + 1) // 2), p ** (c // 2)
    cases = witnesses = 0
    depths = []
    for m in range(c + 2):
        outcomes = []
        for d in range((c + 1) // 2 + 2):
            x = pow(p, d, a), 0
            z, t = x
            for _ in range(m):
                z, t = (p * t) % a, z % b
            if exhaustive:
                single1 = single2 = joint = 0
                for u, v in product(range(a), range(b)):
                    ok1 = (x[0] + u) % a == 0 and v % b == 0
                    ok2 = (x[0] + z + u) % a == 0 and (t + v) % b == 0
                    single1 += ok1
                    single2 += ok2
                    joint += ok1 and ok2
                assert single1 == single2 == 1
                witnesses += a * b
            else:
                u, v = -x[0] % a, 0
                joint = (x[0] + z + u) % a == 0 and (t + v) % b == 0
            assert bool(joint) == (2 * d + m >= c)
            cases += 1
            if joint:
                outcomes.append(d)
        depths.append(min(outcomes))
    return cases, witnesses, depths


total = points = 0
for p, cmax in [(3, 8), (5, 5), (13, 4)]:
    for c in range(1, cmax + 1):
        n, w, _ = tests(p, c, True)
        total += n
        points += w
print(f"Exhaustive parameter tuples: {total}; candidate lifts examined: {points}")
n, _, depths = tests(13, 8, False)
assert depths[:9] == [4, 4, 3, 3, 2, 2, 1, 1, 0]
print(f"p=13, c=8; {n} direct congruence tests; least depths m=0..8: {depths[:9]}")
```

</details>


## Scheduled continuation | LV-20261125T181400Z-OPEN

**IN_PROGRESS, 2026-11-25 13:14 EST (18:14 UTC); RUN_ID_UNAVAILABLE.** The mandatory warning-fatal check on the current #1201 head `5eb0d87573d087aed794ef065ceea034021fa280` failed. The [hosted log](https://github.com/OVVO-Financial/RH_Lean/actions/runs/45625259670/job/139243948070) reaches the negative equality branch of `weight_self_zero`, warns about three unused instance binders in `NativePrimeExponentJet`, and separately times out when specializing the original consecutive Frobenius-coset minor. Full native build skipped. A source-level repair and its limits are being checked against this exact revision; neither this diagnosis nor an unweighted incidence minor is a physical recovery certificate.

Policy/main `cad8dba7bbab6c709264061a3269790230c0d9a5`; AGENTS blob `c7715e559ab64a8b2ebbf4623ecc246cb43179af`; contract `6fa886e125321056739a48d09fd33c95edaebf6b`; recovery directive `8c16f05a43e8794fa78f77ba2645b3913669b93f`. Initial `agent-reports` head `45025978c1d551f79b592e3dd4b7f1edf9b3e3c4`; verified previous own blob `665f7b85a0b93964f408c4342f6c8b09916fdf3a` (35,107 bytes). Latest seven actual reports located; Nov 25 and available Nov 24 originals retrieved by immutable blob, Coordinator mirrors identical, external inbox inspected. Carry `LV-20261125-LIFT1/2` as local paper results, not physical data. Review the new JETCUT, FRAME, PRICE and HALFSTEP handoffs, after the prior intake, against the actual selected source and dual. Record an exact constructor or a precise blocker; keep the same original signed data and #1205 quantifiers.

`native_economical_recovery_ack=NATIVE_ECONOMICAL_RECOVERY_V1; ECONOMICAL_RECOVERY_ROLE=LEAN; final_1201_ack=FINAL_PR_1201_PROOF_CLOSURE_V1; FINAL_1201_ROLE=LEAN; publish_ack=REPORT_PUBLISH_RECOVERY_V1; DIRECT_CORE_CUT_V1; STRICT_NO_GEOCL_ANYGEOMETRY_V1`. No local Lean, direct main write, parallel proof PR or automated merge. Native RH OPEN.

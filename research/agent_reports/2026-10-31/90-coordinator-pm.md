# RH_Lean Coordinator research report - 2026-10-31

**Status:** COMPLETED continuation at 15:13 America/New_York  
**Live main:** `05c3fcfc2ad699f09d7d473f17ac63a918a3aad3`  
**Authority blobs:** `AGENTS.md d30a5c4320bec77a510932e72ce7f17d98a68e51`; `CURRENT_PROOF_CONTRACT.md 7a067ec0423a998e1079e37494061346d8ee02b0`  
**Policy gate:** `SEARCH_BROAD` until a verified fixed positive eta survives the complete return.  
**New claim:** `20261031-coordinator-2`.  
**Evidence:** `PAPER_PROOF_NEEDS_INDEPENDENT_REVIEW / EXACT PRIME-RAY MOBIUS TELESCOPE`; `PAPER_PROOF_NEEDS_INDEPENDENT_REVIEW / FIXED-ETA COMPLETED SUBSECTOR`; `NO_COMPLETE_SOURCE BOUND`; `NO_GLOBAL FIXED-ETA GAIN`; `NO_RH`.

## A. What changed mathematically?

The coherent positive semiprime floor-return block isolated by `20261031-analytic-2` is not intrinsically unpayable. It is the first term of an exact, source-faithful factor-depth telescope.

For each prime (q) just below the root, the legal original rows
[
 (2m,q),qquad m {m odd},quad 1le mlelfloor(R-1)/2floor,
]
complete the positive (m=1) row. Odd Mobius inversion reduces the completed ray to a logarithmic power-of-two main term plus a short boundary Mertens tail. In the window (R-R^{1/3}<q<R), trivial control of that short tail already gives a pointwise (O(R^{2/3})) bound and dyadic energy
[
 O(H^{7/3})=O(H^{5/2-1/6}).
]

This is the first fixed positive-eta estimate found today on a completed legal subsector that contains the previously coherent ((2,q)) obstruction and its actual cross-depth partners. It does not estimate the complete Euler floor source, complete sharp shell, canonical VF defect, or Mertens function. The net endpoint gain remains unknown.

The earlier claim `20261031-coordinator-1`, accepted with scope by `20261031-referee-4`, remains valid: coefficient-weighted root-resonance diagonals have a divisor-loss period bound. The new result changes the portfolio by supplying an independent cancellation law rather than another resonance identity.

## B. Current proof objective

At current `main`, the public theorem remains
[
 exists Cge0 orall Rge2,quad
 |pi(R^2)-VF_{m can}(R^2)|le C Rlog R.
]
The nearer open benchmark is: for some fixed (eta>0),
[
 sum_{Hle R<2H}|Delta_R|^2
 ll_arepsilon H^{5/2-eta+arepsilon},
]
for the genuine complete signed sharp square-shell source. This would improve the independent Mertens exponent below (7/8). Neither statement is proved.

The exact source used below is `research/EULER_FRACTIONAL_COUPLED_20261027.lean`, blob `e6c4b1690e497760d366e36b28a1f7aa60e19f85`. On main it kernel-checks
[
 {m floor bilinear}
 =X_Rleft(sum_{n<R}{mu(n)over n}ight)^2
 -{m fractional diagonal}-2,{m fractional off},
 qquad X_R=R^2-1.
]
Therefore continuous-minus-fractional reassembly on one strict off-diagonal row is exactly its signed floor term; no model coefficient is substituted.

## C. Competing mechanism portfolio

### 1. Prime-ray Mobius telescope - PROMOTE, highest next value

**Concept.** Complete a coherent seed row ((2,q)) along the genuine multiplicative ray ((2m,q)), before taking norms. Mobius inversion across factor depth produces exact cancellation; only the moving boundary tail remains.

**Independent input.** The elementary odd-divisor identity
[
 sum_{substack{mle A\m {m odd}}}mu(m)lfloor A/mfloor
 =1+lfloorlog_2 Afloor.
]

**Target implication.** Claim `20261031-coordinator-2` gives a fixed (eta=1/6) energy gain for the near-root prime-ray subsector. A uniform partition into such rays, with overlap and residual sectors controlled, could pay part of the complete first band.

**First unproved step.** Prove a non-target-equivalent bound for the triangular boundary sum when (q) ranges farther from (R), and then restore every other seed, squareful row, diagonal, principal, band and endpoint term.

**Support.** Exact source identity on main; Analytic's accepted ((2,q)) carrier; Owner's exact squarefree coefficient/Fubini law; the proof below.

**Obstruction.** For broad (q), the boundary length (A_q-L) is order (R), and its signed triangular sum could rehouse the Mertens problem. Rays for different seeds may overlap.

**Decisive experiment.** Reconstruct the exact triangular tail by (u=R-q), test whether its full signed sum has cancellation beyond the trivial (U^2) bound, and search explicitly for duplicate occurrences between seed rays.

### 2. Root-period quadratic operator - CONTINUE, second priority

**Concept.** Average the exact root-dependent resonance
(gcd(j^2,jR+k)) before Cauchy, with the literal moving coefficient and centered principal.

**Independent input.** Referee claims `20261031-referee-2,4` and Coordinator claim `20261031-coordinator-1`; Census claim `20261031-census-2` gives exact cubefree support and finite rational Gram certificates.

**Target implication.** A (J(H))-growing incomplete operator bound, plus all omitted bills, would control multiple moving bands simultaneously.

**First unproved step.** Uniform cross-column centered Gram control with explicit (J)-growth, partial periods, (k>j), principal reconstruction, reciprocal-square, diagonal and endpoint restoration.

**Obstruction.** Squarefree (j) retains maximal resonance; the finite (Jle7) certificates do not imply a uniform large sieve.

**Disposition.** Continue, but do not spend the next Census allocation on a larger fixed-(J) table.

### 3. Genuine MU-LIFT cross-layer recurrence - RETAIN AS INDEPENDENT RESERVE

**Concept.** Estimate the complete signed floor kernel after the exact GCD-layer decomposition, retaining cancellation between quotient and factor-depth layers.

**Independent input.** Wheel claim `20261031-wheel-2` gives the occurrence-preserving GCD decomposition and a coherent coprime quotient-one prime rectangle.

**Target implication.** A full recurrence with power (r<2) and subpower loss would improve the Mertens exponent.

**First unproved step.** Cancel the order (N^2/log^2 N) prime rectangle against its legal complement uniformly for every (Ble X<B^2).

**Obstruction.** Componentwise absolute payment is impossible; the obstruction already lies in (g=1). Wheel's claim still awaits independent review.

**Disposition.** Continue as reserve, distinct from the Euler root-period carrier.

Complete inverse-weighted owner contraction and within-modulus squarefree parent cancellation are rejected mechanisms. Owner claims `20261031-owner-1,2` prove that the reciprocal owner factor is physically canceled and that squarefree parent contributions reinforce.

## D. Conceptual research performed

### Claim `20261031-coordinator-2`: exact near-root prime-ray telescope

Let (Rge8), (X=R^2-1),
[
 L=lfloor(R-1)/2floor,qquad
 A_q=leftlfloor{Xover2q}ightfloor,
]
and let (q) be prime with (R/2<q<R). Define the exact reassembled contribution
[
 T_R(q)=
 2sum_{substack{1le mle L\m {m odd}}}
 mu(m)leftlfloor{A_qover m}ightfloor. 	ag{21}
]

Every term is a genuine original strict pair. Indeed (2m<R), (q<R), and (2m
e q). Also (m<q), so ((m,q)=1), while
[
 mu(2m)mu(q)=(-mu(m))(-1)=mu(m).
]
Thus (21) is precisely continuous-minus-fractional reassembly for the rows ((2m,q)), counted once after ordering. Its (m=1) term is
(2lfloor X/(2q)floor), the positive semiprime row from `20261031-analytic-2`.

For every integer (Age1),
[
 sum_{substack{mle A\m {m odd}}}
 mu(m)lfloor A/mfloor
 =sum_{nle A}sum_{substack{mmid n\m {m odd}}}mu(m)
 =1+lfloorlog_2 Afloor, 	ag{22}
]
because the inner divisor sum is one exactly when the odd part of (n) is one, and zero otherwise.

Since (q<R), (A_qge L). Subtracting the missing tail from (22) gives the exact identity
[
 oxed{
 T_R(q)=2left(
 1+lfloorlog_2 A_qfloor
 -sum_{substack{L<mle A_q\m {m odd}}}mu(m)
 ight).} 	ag{23}
]

Now take an integer (1le Ule R/2) and (R-U<q<R). Since
(Lge(R-2)/2) and (q>R-U),
[
 A_q-L
 le {R^2-1over2q}-{R-2over2}
 ={R(R-q)+2q-1over2q}
 le U+1. 	ag{24}
]
Consequently
[
 |T_R(q)|le2(2+log_2 R+U). 	ag{25}
]
For
[
 {cal P}_R(U)={q {m prime}:R-U<q<R},qquad
 T_R(U)=sum_{qin{cal P}_R(U)}T_R(q),
]
the trivial count (|{cal P}_R(U)|le U) gives
[
 |T_R(U)|le2U(2+log_2 R+U). 	ag{26}
]

Set (U=lfloor R^{1/3}floor). Uniformly for (Rge8),
[
 |T_R(U)|=O(R^{2/3}),
]
and therefore
[
 sum_{Hle R<2H}|T_R(lfloor R^{1/3}floor)|^2
 =O(H^{7/3})
 =O(H^{5/2-1/6}). 	ag{27}
]

Equations (21)-(27) are `PAPER_PROOF_NEEDS_INDEPENDENT_REVIEW`.

### Why this is mathematically different

This is not a coordinate rewrite of the target. It introduces an independently proved cancellation principle: factor-depth completion along a physical prime ray converts the coherent floor mass into a boundary term. The proof uses only finite Mobius inversion and a trivial boundary count. It neither assumes nor concludes a bound for (M(x)).

The result also explains why the isolated ((2,q)) lower bound is not evidence against the complete source: its legal negative partners are explicit and quantitatively effective near the root.

### No-circularity and carrier audit

- The estimate is on a named strict subset of actual source occurrences, not on an invented coefficient sequence.
- The continuous and fractional parts are combined exactly into floors before estimation.
- The (m=1) obstruction is retained, not removed.
- All odd (mle L) are retained, including zero Mobius rows harmlessly.
- Different (q) give distinct pairs because (m<q).
- No PNT, zero-free region, random-sign premise, or canonical target is used.
- The claimed eta applies only to this completed ray sector. It cannot be transferred to the full quadratic expression without all cross terms and complements.
- Broadening the (q)-window leaves a potentially hard triangular Mertens boundary; no global gain is claimed.

## E. Specialist findings

- `20261031-owner-2`: `PAPER_ACCEPTED_WITH_SCOPE`. Squarefree least-owner fibres reassemble the literal moving Euler coefficient. Under full admission the coefficient is
  ((-1)^{omega(d)}2^{omega(d)-1}); cross-parent terms reinforce. Squareful extension fails at (d=12).
- `20261031-analytic-2`: accepted after Referee's endpoint repair. The all-(n) coefficient identity needs (+2,1_{n=1}), and the Dirichlet series needs (+1). Its inverse zero-free implication survives. The positive ((2,q)) floor-return block is a valid sectorwise no-go.
- `20261031-wheel-2`: `PAPER_PROOF_NEEDS_INDEPENDENT_REVIEW`. Exact GCD layers for the genuine MU-LIFT kernel and an order (N^2/log^2N) coprime quotient-one obstruction; no complete recurrence bound.
- `20261031-census-2`: `PAPER_PROOF` for cubefree support and nonsquarefree maximal-resonance exclusion; `FINITE_COMPUTATION` for exact rational finite Gram certificates. No uniform operator theorem.
- `20261031-referee-4..6`: accepted Coordinator's weighted resonance diagonal and Owner's squarefree Fubini; repaired Analytic's (n=1) endpoint; rejected any inference from the positive block to failure of the complete shell.
- `20261031-lean-2`: PR #1062 formalizes only the coprime criterion and the counterexample to root independence. It does not formalize the period mean or a moment estimate.

October 30 carry-forward remains active: `20261030-analytic-1` pays a reciprocal-response tail under a final (1/h) coefficient, but Owner's complete-return theorem prevents applying it wholesale; `20261030-coordinator-1` supplies the moving-band frontier; the moving-band sign conjectures remain unproved.

The external inbox remains blob `038018145c0fddb2f6306c0712373adf9cd1ea52`, with no handoff newer than October 18.

## F. Mathematical bottlenecks

1. **Prime-ray mechanism:** control the broad triangular boundary
   [
   sum_qsum_{L<mle A_q}mu(m)
   ]
   by an independent incidence or bilinear theorem, with overlaps and all non-ray rows restored.
2. **Root-period operator:** prove a (J(H))-uniform incomplete centered Gram estimate, then pay principal, diagonal, reciprocal-square, activation and endpoint terms.
3. **MU-LIFT:** prove complete cross-layer compensation for the coprime prime rectangle; no componentwise norm argument can work.
4. **Canonical endpoint:** bridge any complete Mertens/source saving through the registered consumer without importing the merged (7/8) benchmark as its own proof.

## G. Strategy decisions

- Promote the prime-ray telescope to the highest-value next same-source investigation.
- Continue the root-period operator, but demand a growing-(J) theorem rather than more fixed-(J) numerics.
- Retain MU-LIFT as the independent reserve.
- Reject within-modulus squarefree parent cancellation and complete inverse-weight owner decay.
- Do not formalize `20261031-coordinator-2` until Referee independently accepts its exact carrier and quantifiers.
- Preserve the broad-search gate: (27) is a local eta gain, not a verified complete-return eta.

## H. Next specialist assignments

**RH | Owner Payment.** Audit (21) occurrence by occurrence against the least-owner and physical return carriers. Decide whether the ray is complete under one owner decomposition or crosses owners; list terminal, shared-prime, and cross-parent terms. Falsifier: one legal ((2m,q)) occurrence missing, duplicated, masked, or carrying a different sign.

**RH | Analytic Type II.** Reverse the triangular tail in (23) by (u=R-q) and seek a uniform bound for windows (U=R^alpha), (alpha>1/3), without assuming a Mertens exponent. State the first theorem that improves the trivial (U^2) aggregate. Falsifier: show that the proposed tail estimate implies the canonical target or a forbidden zero-free region.

**RH | Finite Wheel & Incidence.** Generalize the exact telescope from seed (2) to squarefree seeds (s), classify overlaps between ((sm,q)) rays, and give the exact boundary length. Falsifier: the smallest duplicated physical pair or seed for which the restricted divisor sum has a non-sparse principal.

**RH | Prime Census Laboratory.** On held-out roots, reconstruct (21)-(23) exactly, stratify cancellation by (m)-depth, and search for the first overlap or boundary spike when several seeds are combined. Do not infer an exponent from finite data. Rotate the following allocation to FINITE-AC/CORR4 or NYMAN as already required.

**RH | Adversarial Referee.** Independently ACCEPT/REVISE/REJECT `20261031-coordinator-2`: check (A_qge L), (24), source signs, strict ordering, uniqueness, and the (H^{7/3}) energy exponent. Determine whether “completed subsector” is the strongest honest scope.

**RH | Lean Verification.** No immediate implementation. After independent acceptance, the smallest target is the finite identity (22) and exact equality (23), with the original row map explicit. Do not formalize (27) as a complete-source theorem.

## I. Lean and PR status

Current main includes merged #1060 and #1061. PR #1062 is the only open PR found. It is open, non-draft, mergeable, and human-review ready at exact head
`4309335c62ddcf41d7d3a17df2589de007291eff`, based on current main.

All 12 observed PR-triggered workflows on that head are green, including:
- root-dependent moving-band resonance run `41224963246`;
- targeted Lean iteration `41224963209`;
- Lean source audits `41224963426`;
- proof inventory `41224963210`;
- public export verification `41224963158`.

Classification remains `PROVED_IN_LEAN_ON_PR_HEAD / CI_GREEN / REVIEW_READY / STRUCTURAL_ONLY`. Human merge authority is unchanged. No Coordinator Lean branch or proof PR was created.

## J. Next-run resume capsule

- Main: `05c3fcfc2ad699f09d7d473f17ac63a918a3aad3`.
- Authority blobs: `AGENTS d30a5c...`; contract `7a067ec...`.
- Prior claim `20261031-coordinator-1`: accepted with scope.
- New claim `20261031-coordinator-2`: equations (21)-(27), pending independent review.
- Surviving new idea: exact odd-Mobius prime-ray completion; (U=R^{1/3}) gives sector energy (H^{7/3}).
- Decisive blocker: broad triangular boundary plus restoration of all other rows and quadratic cross terms.
- Portfolio: prime-ray telescope; root-period operator; genuine MU-LIFT.
- PR #1062: head `4309335c...`, 12/12 observed workflows green, review ready, unmerged.
- Complete shell bound, global fixed eta, exponent below (7/8), canonical VF theorem, and RH: OPEN.
- Highest-value next reasoning task: derive or refute a non-target-equivalent incidence bound for the triangular boundary after reversing the ((q,m)) order.

## Publication history

The earlier completed synthesis with claim `20261031-coordinator-1` was preserved through this continuation. An `IN_PROGRESS` checkpoint for claim `20261031-coordinator-2` was published first at commits `cec4efa4a662490b3a3d6bbb363458d397f485ea` (PM) and `58d7ec9006bac1756774876849ff168193c1c03d` (AM), both blob `272d0d9cc17ce5a56942294e500d257d3f9aae01`.


## Scheduled continuation checkpoint — 2026-10-31 23:09 America/New_York

**Status:** IN_PROGRESS / scheduled continuation; earlier completed claims preserved.  
**Live authority:** `main@2072393fa0c0389cbe6f77fab773a2c741bade09`; eta gate `SEARCH_BROAD`.  
**Formal change since the prior synthesis:** human merges #1062 and #1063 place the root-dependent resonance criterion and the near-root prime-ray occurrence/sign theorem on main. These are structural/source-admission theorems only; the odd Möbius telescope, local energy theorem, complete return, strict exponent gain, canonical VF estimate and RH remain open.

This continuation consumes all available October 30–31 reports and the external inbox, then investigates a distinct generalization of the accepted `v_2(a)=1` telescope. The precise question is whether completing a ray with a squarefree seed `s` converts the interior Möbius sum to a genuinely sparse principal, and whether the resulting family can be made disjoint without hiding the complete shell target. No result is promoted before the source, overlap and endpoint audits are complete.

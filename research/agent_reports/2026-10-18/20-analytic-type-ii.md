# RH_Lean agent daily report - 2026-10-18 / RH | Analytic Type II

**Status:** COMPLETED
**Invocation:** scheduled run at 2026-10-18T12:31-04:00
**Canonical objective:** `VFCanonicalSquareVonKochStatement` remains OPEN.
**Result classes:** `PAPER_PROOF` (new shellwise rank-one/no-dispersion theorem), `PAPER_PROOF` (exact cross-shell Abel gate with quantitative variation threshold), `REFUTED` (within-shell outer-prime Type-II dispersion as an independent saving mechanism), `NO_NEW_BOUND` on shell energy, Mertens, the canonical VF target, or RH.

## A. Most important analytic development

### Claim `20261018-analytic-1` - the proposed outer-prime tile is shellwise rank one

Use the exact strict shell
[
I_r={n:r^2<n<(r+1)^2},qquad
mathcal O_r={qin I_r:q {m prime}},qquad Q_r=|mathcal O_r|.
]
For a dyadic cofactor band, let
[
mathcal C_{r,C}={c:Cle c<2C, 2le cle r},qquad
G_{r,C}=sum_{cinmathcal C_{r,C}}e_r(c),
]
where the genuine compensated coefficient is exactly the plan's
[
e_r(c)=mu(c)P_r(c)-a_r^{m inc}(c).
]
Then the proposed tile has the exact factorization
[
oxed{mathcal J(H;C)=
sum_{Hle r<2H}Q_rG_{r,C}.}	ag{R1}
]

This is stronger than observing that the outer-prime reindex is an identity. On each shell define the incidence operator
[
T_{r,C}:ell^2(mathcal C_{r,C})longrightarrowell^2(mathcal O_r),
qquad
(T_{r,C}x)(q)=sum_{cinmathcal C_{r,C}}x(c).
]
If both index sets are nonempty, its matrix is the all-ones matrix, so
[
operatorname{rank}T_{r,C}=1,qquad
|T_{r,C}|=sqrt{Q_r|mathcal C_{r,C}|}.
]
Writing (P_r^0) for orthogonal projection onto the mean-zero subspace of
(ell^2(mathcal O_r)),
[
oxed{P_r^0T_{r,C}=0.}	ag{R2}
]
The same statement holds after expanding a cofactor into every actual inner prime (p): once ((c,p)) is known to lie in (I_r), every (qinmathcal O_r) is joined to it. The detailed (q)-by-((c,p)) matrix is again all ones, with the (mu(c)) or compensator weight carried only by the column.

**Proof.** The bracket defining (mathcal J) depends on (q) only through (r(q)=lfloorsqrt qfloor). There are exactly (Q_r) outer primes with (r(q)=r), giving (R1). Every row of (T_{r,C}) is the same vector ((1,ldots,1)), proving rank one, the singular value, and (R2). No PNT, model density, or Mertens estimate is used.

**Classification:** `PAPER_PROOF / NEW EXACT OPERATOR RESTRICTION / LOCAL TYPE-II NO-GO`.

### Consequence

A within-shell dispersion, large-sieve, or Fourier argument in the outer variable (q) controls only mean-zero (q)-modes. Those modes vanish identically for the actual tile. The surviving constant mode is
(Q_rG_{r,C}), precisely the unpaid arithmetic correlation. Thus ordinary (q/p) dispersion cannot produce the desired saving unless the source is changed to include a genuinely (q)-dependent weight; any such change must restore its deleted shell mean, which is the original term.

The shifted inequality involving (p-q/c) does not repair this. It is a consequence of the two independent memberships (qin I_r) and (pcin I_r), not a selective coupling inside the complete Cartesian product. Restricting to a thinner (q/p) diagonal creates a complement that can contain the entire constant mode.

This does not refute all Type-I/II approaches. It refutes the specific idea that the existing outer-(q) reindex itself supplies a nondegenerate two-prime dispersion variable. The available oscillation remains in (mu(c)), the smooth compensator, the divisor phase, or variation across different shells.

## B. Quantitative scale and complete carrier

For the full compensated cofactor range the paper identity from the shell-incidence note gives
[
sum_{1le cle r}e_r(c)=-delta_r.
]
Consequently the complete outer-prime tile is
[
oxed{mathcal J_{m full}(H)
=-sum_{Hle r<2H}Q_rdelta_r.}	ag{R3}
]
Since (delta_r=C_r-Q_r), this is (B_H-X_H) in yesterday's projection notation:
[
B_H=sum Q_r^2,qquad X_H=sum Q_rC_r.
]
Thus the full tile is the scalar-calibration residual, not a separately small prime-pair count.

If Target A held with a fixed (eta>0),
[
mathcal E(H)=sumdelta_r^2
ll_arepsilon H^{5/2-eta+arepsilon},
]
then the elementary bound (Q_rle2r) gives (B_Hle16H^3), hence
[
|mathcal J_{m full}(H)|
lesqrt{B_Hmathcal E(H)}
ll_arepsilon H^{11/4-eta/2+arepsilon}.
	ag{R4}
]
This is a necessary scale, not an achieved estimate. Claim `20261018-analytic-1` shows that centering the outer primes inside their shells erases (R3) rather than proving (R4).

## C. Claim `20261018-analytic-2` - exact cross-shell Abel gate

The only variation visible to the outer prime in the present carrier is the shell index. Put
[
Pi_r=pi(r^2).
]
Because ((r+1)^2) is composite for (rge1),
[
Q_r=Pi_{r+1}-Pi_r.
]
For every complex shell response (g_r) and integers (ale b),
[
oxed{
sum_{r=a}^bQ_rg_r
=Pi_{b+1}g_b-Pi_ag_a
+sum_{r=a+1}^bPi_r(g_{r-1}-g_r).
}	ag{A1}
]
Let (L_r=operatorname{Li}_2(r^2)) and (D_r=Pi_r-L_r). Splitting (A1) gives an exact Li part plus an exact discrepancy part. If
[
E_pi(a,b)=max_{ale rle b+1}|D_r|
]
and
[
V_{a,b}(g)=|g_a|+|g_b|+sum_{r=a+1}^b|g_r-g_{r-1}|,
]
then
[
oxed{
left|sum_{r=a}^b
igl[(D_{r+1}-D_r)g_rigr]ight|
le E_pi(a,b)V_{a,b}(g).
}	ag{A2}
]

**Proof.** Formula (A1) is finite summation by parts. Apply it separately to (Pi=L+D); the triangle inequality on the (D)-part gives (A2). All boundaries are explicit.

**Classification:** `PAPER_PROOF / EXACT TRANSFORMATION WITH QUANTIFIED LOSS / NO_NEW_ARITHMETIC_BOUND`.

### Required strength

For the complete response (g_r=-delta_r), the discrepancy portion can meet the necessary scale (R4) only if
[
E_pi(H,2H),V_{H,2H}(delta)
ll_arepsilon H^{11/4-eta/2+arepsilon}.
	ag{A3}
]
If one separately had a prime-discrepancy estimate
[
|pi(x)-operatorname{Li}_2(x)|ll_arepsilon x^{	heta+arepsilon},
]
then (E_pi(H,2H)ll H^{2	heta+arepsilon}), and (A3) requires
[
oxed{
V_{H,2H}(delta)
ll_arepsilon
H^{11/4-eta/2-2	heta+arepsilon}.}	ag{A4}
]
At the (7/8) benchmark this is (V(delta)ll H^{1-eta/2+arepsilon}). The unconditional trivial estimate is only (V(delta)=O(H^2)). Ordinary PNT supplies no fixed power exponent (	heta<1), and it supplies no signed variation theorem for (delta). Moreover the Li part in (A1) still needs its own signed cross-shell control.

Therefore (A1) identifies a genuine alternative mechanism, but also a severe quantitative gate: the currently available carrier would need a new response-variation or cross-shell spectral theorem. Declaring the Abel transform itself a saving would be circular.

## D. Falsification and no-circularity audit

1. **Genuine prime-square falsifier.** On the prime-only channel the response is (g_r=Q_r), so the mixed term is (sum Q_r^2), which is PNT-forced of order at least (H^3/log^2H). Every within-shell mean-zero (q)-mode is nevertheless exactly zero by (R2). Thus a mean-zero outer-prime estimate can be perfect while missing the dominant constant mode.
2. **Complete compensator.** Summing all (e_r(c)) gives (-delta_r), so a claimed small bound for the recombined constant mode is already a mixed form of the shell target. It cannot be assumed as the independent tile estimate.
3. **Thin (q/p) diagonal.** The exact source contains all pairs (qinmathcal O_r), (pcin I_r). A restriction by (|pc-q|), additive phase, or subinterval location is a new decomposition; its complement must be restored before any exponent claim.
4. **Cross-shell variation.** Formula (A2) uses absolute variation. With only (|delta_r|le2r), it loses (O(H^2)); no gain follows from PNT alone.
5. **Fixed cofactor density.** Coordinator claim `20261018-coordinator-1` and Owner claim `20261018-owner-2` show that fixed-cofactor modes carry PNT-sized coherent main terms. They reinforce, rather than evade, the constant-mode obstruction.
6. **Original VF.** Nothing here identifies unit Möbius shell weights with native #915 weights, masks, clips, historical anchor, positive residual, or NNS denominator. Owner's transfer cone must be preserved in any future direct-VF use.
7. **Novelty.** Repository search found the outer-prime reindex and finite checker, but no shellwise operator-rank statement, mean-zero annihilation theorem, or cross-shell variation threshold. The result is structural, not an exponent improvement.

## E. Relation to current source and established claims

- The compiled strict (S=A-T) and renewal boundary laws are preserved.
- The plan's exact strict endpoint (P_r(c)=pi(lfloor((r+1)^2-1)/cfloor)-pi(lfloor r^2/cfloor)) is preserved.
- The paper compensator (e_r(c)), (c=1) channel, smooth component, and all cofactor bands are preserved.
- Wheel's two-prime sign-coherence theorem and Census/Referee's (t=3) counterexample remain active no-gos.
- Merged #978 supplies exact Lambda/historical/anchor interfaces only; its total Lambda error rehousing of (M(X)log X-int M(t)dt/t) is not used as a bound.
- The external (7/8) result appears only in (A4) as a clearly conditional benchmark. It is not imported as a native Lean theorem and does not prove short-interval or response-variation saving.

## F. Mechanism decision

**Decision:** `REJECT / REFORMULATE` the within-shell outer-(q) dispersion proposed for (mathcal J(H;C)). The exact tile has no nonconstant (q)-mode.

**Continue** the two-scale shell program through one of two genuinely different inlets:

1. Prove a signed estimate in the cofactor/divisor variables for (G_{r,C}), including (c=1), then sum against the positive shell multiplicity (Q_r).
2. Introduce a cross-shell response transform and prove a new variation, spectral, or bilinear estimate strong enough for (A3), with the Li main term and every boundary restored.

The first route attacks the existing squarefree divisor phase directly. The second route is not a within-shell prime-pair theorem; it is a theorem about how the complete compensated Möbius response evolves across square shells.

No independently proved (eta>0), no (eta=0) shell theorem, no Mertens exponent improvement, no canonical VF estimate, and no RH proof were obtained.

## G. Specialist handoffs

- **Coordinator:** replace “outer (q/p) dispersion” in the dependency DAG by the exact rank-one gate. Any candidate tile must state where genuine (q)-dependence enters and how its constant shell mean is restored.
- **Owner:** the result is confined to the unweighted Möbius shell. Do not transfer it to #915 without the masked transfer cone, anchor, residual, and native weights.
- **Wheel:** search for an independently signed cofactor/divisor kernel inside (G_{r,C}); outer-prime location supplies none.
- **Census:** on fresh held-out dyadic (H), compute for each prescribed cofactor band
  [
  V_{H,2H}(G_C),quad
  sum (Q_r-[L_{r+1}-L_r])G_{r,C},quad
  sum [L_{r+1}-L_r]G_{r,C}.
  ]
  This directly falsifies or supports the cross-shell gate. Pre-register (C=1,2,3) and bands near (H^{1/4},H^{1/2},H^{3/4}); retain exact (e_r(c)) and all endpoints.
- **Referee:** audit the all-ones incidence claim and challenge any proposed (q)-dependent refinement at its complement/restoration step.
- **Lean:** the generic finite rank-one lemma and Abel identity are formalizable but low priority; neither should receive a quantitative consumer until an independent arithmetic bound exists.

## H. Authority, reports, PRs, and CI

- Live `main` HEAD: `5ae5a524ca447d1936e351bbbe4b134c068a1a13`.
- Authority blobs: `AGENTS.md` `4c66a1d462df98c84deebf0069ad11f904039858`; `CURRENT_PROOF_CONTRACT.md` `2fa9931dcdc1fc8a816aefb8aa348db12ee9a384`; dynamic protocol `bd1189617c069565a881c2a5c5dbd9a138bc48c1`; PNT-first contract `e8acbeff24942d1f8ee0079f715afff2ddda2c33`; two-scale plan `0606d764ffebb4639cc0abb52ccbef30546b7764`.
- Source blobs: `TwoABScaleTransfer.lean` `fae76878063583322a48a329810cc1cc7b037ee7`; `SquareRootMatchedTransport.lean` `e9ab3bff6b8819182c39721f92859679d250002e`; `SquareBlockSmoothTransportGram.lean` `09f5e0108eb254a2f20fa2fd694d69cb455b2857`; `SquareRootSmoothRenewalInstantiation.lean` `9a63c8c2f9e42a64c0010721a78101c1f56858b1`; shell compensation note `d7826257273473e80948117ea5c0fcd04713af6f`; merged Lambda/anchor source `c67797ae7cda0ad9a7c393c69715016685a14d0a`; two-scale falsifier `20cd0af940e2b334d4b9a440e4aaa9cba7e4825f`.
- External inbox `038018145c0fddb2f6306c0712373adf9cd1ea52` consumed, including `EXT-20261018-PNT-1..3`.
- Today reports consumed: Coordinator `c9337407b72329a8fc68bd8694f7660a72aafc52`; Owner `4655c4379f9a5d4b13a9f43c1c1c0addfe90d836`; Wheel `62da494755501409879e894779d026aed70835f8`; Census `08d80d6fe5f8114e210d6e50f5939603a511994e`; Referee `096513f9a32d79bc6699719fcac3c997572b31f0`; Lean `0ed62011c7a02051b634928b10ef670380033e34`.
- Own previous report: `2026-10-17/20-analytic-type-ii.md` blob `08e96ac308fc08f59f2e4f5c82a70ba7d901c97e`, used as `YESTERDAY=CARRY_FORWARD`.
- Open PR search at intake and final research pass returned none.
- PR #978 is merged at `742b0584fdd580ca37f2d3b9a2a6aedf1c12daaf`; exact proof head `ba89ca4e5fc6a341ca0422698ec40b4646480000`; all ten returned workflows succeeded, including the dedicated warning-fatal Lambda/anchor job.
- PR #979 is merged at live main; proof/document head `9c3535d9cadc7016f39071c00ed2e1cc344c4911`; all four returned workflows succeeded. Its finite script and plan establish no all-scale estimate.
- PR #969 remains absent from main despite its stacked-branch merge status; its OAI files are not on-main authority.

## I. Resume capsule

New claim `20261018-analytic-1` proves that the proposed outer-prime tile is shellwise rank one and that all mean-zero outer-(q) modes vanish. New claim `20261018-analytic-2` gives the only exact outer-prime escape available without changing the carrier: cross-shell Abel summation, with the explicit loss (E_pi V(g)) and the required threshold (A4).

The highest-value next analytic question is now precise: can one prove, from the squarefree divisor phase and moving shell endpoints, either a genuine low-divisor estimate for (G_{r,C}) or a cross-shell response theorem meeting (A3), while restoring the Li main term and all bands? A same-shell prime-pair theorem is not the missing input for the current tile.

No RH proof claim.


## J. Publication verification

Early `IN_PROGRESS` checkpoint commit: `16afdce40725d13a10cefba5e2eb18fc988ae741`. Substantive final commit: `f0f410bfca0ba775d23db43a9267421f324a7b0e`. Immediate readback returned blob `ce59751e02ffde8f6711dd17f2e0da8f68c71c36`, 14,120 characters, with `COMPLETED` status and both claim IDs present. Final live-main refresh remained `5ae5a524ca447d1936e351bbbe4b134c068a1a13`; open PR search remained empty.


## K. Authorized continuation checkpoint - 2026-10-18T22:26-04:00

**Status:** IN_PROGRESS. This scheduled continuation refreshed live authority to `main@c2b075fca8a02079ebab7464a16e1fb58c2b5c7a` and re-read the current proof contract, PNT-first contract, two-scale plan, today/yesterday specialist reports, and external handoffs. The on-main raw transfer cone is now `PROVED_IN_LEAN_ON_MAIN`; it remains a scalar obstruction and supplies neither the original #915 occurrence bridge nor a quantitative saving.

The active analytic question is the first genuinely missing cross-shell theorem left by claims `20261018-analytic-1/-2`: determine whether the exact complete compensated response admits an independently provable cancellation/variation mechanism after the shellwise rank-one mode, Li main term, endpoints, and all cofactor bands are restored. Same-shell outer-prime dispersion remains rejected at its proved scope. No new estimate is claimed at this checkpoint.

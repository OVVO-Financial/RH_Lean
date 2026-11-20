# November 20, 2026 | Research Coordinator

## 07:10 EST | IN_PROGRESS | COORD-20261120T121001Z-PORT

A sharp distinction to test today: detecting a nonzero discrepancy is not an upper bound for the whole signed source. No global exponent or RH conclusion is claimed.

Actual scheduled invocation: 2026-11-20 07:10:01 EST (12:10:01 UTC), America/New_York; platform run ID: RUN_ID_UNAVAILABLE. Main `6338941bb9d10387e9361ca3ca55468d4c710e4c`; intake reports `0956b4709f4693416c387a5aa2bd903324171a8b`. Main AGENTS/contract blobs `500b6daed5e867d19d97c30e43a7a1e7d2055a51` / `95566e37c8eaeb99ee680660df4f9d2e06ea5038`; half and reporting-policy blobs `96ad4439ec458af6168f7d9cb3eef5dde291d37c` / `a9583516fd2e603320c771e32c170132bf0c53e9`.

The intake directory contains six specialist reports and neither Coordinator mirror. The two canonical mirrors are one execution. PR #1153 is open, not merged. Exact-head audit, latest-actual backfill, independent mathematics and assignments are pending. Direct Git returned tunnel HTTP 403; use the separately authorized GitHub API and a live-head guard. Scope: own reports only; no agent launches or proof-branch writes.

half_bootstrap_ack=BOOTSTRAP_TO_HALF_V1; cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1; continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1; publish_ack=REPORT_PUBLISH_RECOVERY_V1. Checkpoint only; no completed-publication claim.

## 07:30 EST | Same invocation | COORD-20261120T121001Z-OCTAVE-FINAL

### A. What changed mathematically?

An off-line zeta zero would be visible before either Nyman repair band enters. On the single prescribed grid `H=6*2^j`, the squared error on just `H<m<=2H` has logarithmic growth exponent `2*Theta-1`, where `Theta` is the supremum of the real parts of the actual nontrivial zeta zeros. The new information is an inverse statement: such a zero forces a **positive signed excess of long-shift Mobius pairs** on infinitely many of these heads. The diagonal, a bounded list of shifts, and separate favorable contributions cannot account for it. There is also an unconditional obstruction: this strip's energy is not `o(1/log^2 H)` on the entire grid.

OCTAVE1 is a specialization of an existing identity. OCTAVE2-4 are a new paper derivation for this carrier (`SELF_AUDIT`, independent review pending, not Lean-certified); OCTAVE5 is finite evidence. The subpower upper bound for the strip is **equivalent to RH, not proved here**. One proper shift band admits an independent logarithmic saving; no exponent improvement, full-norm estimate or RH proof follows.

### B. Current proof objective

Intake main `6338941bb9d10387e9361ca3ca55468d4c710e4c`; closing main `5ca92d731adafb2e2faeb13277af825dcdbb177b` after human merge of #1153. Both authority files were reread there; their blobs and the campaign policies in the checkpoint are unchanged. `VFCanonicalSquareVonKochStatement` (blob `79030d70e8d3e0d08eef9bac53fef95c36eca2fb`) asks for one real `C>=0` before **every** integer `R>=2` such that `|pi(R^2)-vfMidFinishedMass(R)-sqrt(2)| <= C R log R`. Its named Lean consumer `riemannHypothesis_of_vfCanonicalSquare` explicitly takes `ClassicalVonKochRHCriterion`. The independent Mertens route uses the genuine mu, #949 and the half/RH bridge, not floor-Li.

The strongest fixed-family baseline checked is #1119: for each epsilon>0, `|M(x)| <<_epsilon x^(b*+epsilon)`, `b*=7/8-7/(64 Npack)`. Geometry/constants may depend on the positive error. `Npack=ceil(max(1,1/(6 ell)))+2 <= Nstar` (3 ell in #1108), and `7/64>1/48`. This is a closed error family on the native LOW, signed HIGH, principal and error return; it is not a zero-loss bound. #949 identifies the genuine growth exponent with Theta, so for **fixed** `Theta<b<1`, `|M(x)| <<_b x^b`. Taking `b=7/8` is legitimate; substituting `b=Theta` is not needed.

### C. Competing mechanism portfolio

| Priority and carrier | Independent mechanism; route to the endpoint | Decision and decisive test |
|---|---|---|
| 1. NYMAN / genuine Mobius first octave | A periodic test across consecutive physical blocks detects a pole even at a grid boundary. Independently estimate the signs of the original shifted pairs; exclusion of all the inverse configurations in D would exclude every zero right of 1/2. | `ACTIVE_CANDIDATE`. Test a fixed polynomial lag band, then account for every band jointly. No free selection of good heads. |
| 2. Actual-prime VF / SAT / JOH | With a covered base, exclude **every** first failure using the signed common-endpoint prime intervals, all four products, the history and the centered phase. The all-square estimate has the canonical consumer in B. | `ACTIVE_SUPPORT`. Owner's sharp high sector is paid almost everywhere; test the smaller common-height signed return on the exceptional squares, not another density-one count. |
| 3. MU-LIFT | Use coprime, degree-weighted factorizations of original integers in the Newton return; restore complementary sites, old history and all prefixes before #1135. | `ACTIVE_SUPPORT`. Test the inverse for the low-prime multiple-split mass. Reject a fixed number of unweighted pair moments as a substitute. |

For MU-LIFT, `E_M(B)=max_{1<=n<B}|M(n)|/sqrt(n)`. For fixed real `0<=r<2` and a fixed integer sequence `B_j -> infinity`, existence of eventual `G_j>=1`, `log G_j/log B_j -> 0`, with `E_M(B_j^2)<=G_j E_M(B_j)^r` is equivalent in both directions to every-positive-loss half growth (#1135). The full premise is `TARGET_EQUIVALENT`. The three mechanisms use different independent arithmetic inputs. No amendment of the governing priority is needed.

### D. Conceptual research performed

**OCTAVE1 | IDENTITY_ONLY.** All logs are natural. Let `j>=0`, `H=6*2^j`, `N=H^2=6K`, `L=log H`. For `1<=k<=N` let `p_k=log(N/max(H,k))`, `U=sum mu(k)p_k/k`, `V=2L+sum mu(k)p_k`. Write `s,t` for the reciprocal masses of `I1=(3K,4K]`, `I2=(5K,6K]`, respectively, and `a=(U-tV/K)/(s-t)`, `z=(sV/K-U)/(s-t)`. The original physical coefficients for `2<=k<=N` are `c_k=(a 1_I1+z 1_I2-mu(k)p_k)/L`. Keep the unit in the solver sums, squareful repair sites, and the two exact moments `sum c_k/k=1`, `sum c_k=3`. Put `r_H(m)=1-sum c_k (m mod k)/k` and

```
E_j = sum_{H<m<=2H} r_H(m)^2/[m(m+1)].
A_H(m) = sum_{H<n<=m} mu(n) log(n/H) = L r_H(m)    (H<=m<=2H).
```

Indeed `nyman_flat_return_of_moment` gives `L r=tail_N-tail_H+repairFloor`; the solver supplies its reciprocal-moment hypothesis. Here `2H<3K`, the N-tail and repairs vanish, and `floor(m/n)=1` for `H<n<=m`. The minus on the H-tail reverses `log(H/n)`. This is not clipping, nor zeroing a tail of the full Nyman norm. Sources: flat `2d23721027ecc44e85b7add02fc632b482f03352`, moments `1ce4bde64139395e79b9ceb2fd2a396457d7098a`, residual `2da630c1d5fb9302e2097ec1e170cf41c2b40609`.

**OCTAVE2 | PAPER_PROOF: detection on a single grid.** Put `tau=2*pi/log 2`, `q=6^(i*tau)`, `w(v)=1-cos(tau*v)`, and `B_j(s)=sum_{H<n<=2H} mu(n) n^(-s) w(log(n/H))`. On `[1,2]` the function `g_s(x)=x^(-s)w(log x)/log x` extends by zero at 1, vanishes at 2, and has bounded first derivative uniformly on compact sets of s. Discrete summation by parts gives exactly

```
B_j(s) = L H^(-s) sum_{H<n<2H} r_H(n)[g_s(n/H)-g_s((n+1)/H)].
|B_j(s)| <= C_compact L H^(1/2-Re s) sqrt(E_j).
```

The last inequality uses `|Delta g|<=C/H` and `sum_{H<n<2H} n(n+1)=O(H^3)`. There is no endpoint evaluation charge. For `D(s)=1/zeta(s)` let

```
F(s) = D(s) - (q D(s+i*tau) + q^(-1) D(s-i*tau))/2.
```

For `Re s>1`, `F(s)=sum_j B_j(s)+P(s)` where the finite Dirichlet polynomial `P` is the contribution of `n<=6` with weight `w(log(n/6))`. All larger integers occur exactly once, and `w` is periodic with period `log 2`. The meromorphic continuation on the left is fixed. The horizontal coordinate has not been smoothed away.

Fix an actual zero `rho=sigma+i*gamma`, `1/2<=sigma<1`, of order `d>=1`. On the progression `rho+i*k*tau` let `c(k)` be the Laurent coefficient of degree `-d` of D, using zero at regular points. If that coefficient of F vanished at every translate, `u(k)=q^k c(k)` would satisfy `2u(k)=u(k+1)+u(k-1)` for all integers k. Hence u would be affine; `u(0)!=0`, so it could have at most one zero. There are at least **two distinct regular sites**: for fixed `sigma>1/2`, Ingham's `N(sigma,T)<=T^(3(1-sigma)/(2-sigma)+o(1))=o(T)` suffices against a progression with positive density per unit height. At `sigma=1/2`, Li and Radziwill, Theorem 4, give a positive proportion of nonzeros on every fixed vertical progression `alpha*k+beta`, `alpha>0`, `beta` real; take `alpha=tau, beta=gamma`. No adjacency, uniformity in rho, simplicity, positive residues or independence of ordinates is assumed. Thus F has a pole of order **at least d** at some translate `s0`.

If `sqrt(E_j)=o(H^(sigma-1/2) L^(d-2))`, the block bound gives locally normal convergence for `Re s>sigma`. The identity theorem identifies that sum plus P with F there. At `s0+u`, `0<u<1`, it is bounded by finitely many initial terms plus `sum_j o((j+1)^(d-1)) exp(-u*j*log 2) = o(u^(-d))`: split at any fixed large index, then bound the tail by an arbitrary constant times the geometric moment. The block constant is uniform on this compact segment. This contradicts the pole. Consequently, for **each** such zero,

```
limsup_{j->infinity} E_j L^(4-2d) / H^(2sigma-1) > 0.
```

Conversely for every fixed `Theta<b<1`, ordinary partial summation of A against `log(n/H)` gives `max_{H<=m<=2H}|A_H(m)| <<_b H^b`; hence `E_j <<_b H^(2b-1)/L^2`. The two inequalities give `limsup log(E_j)/log H=2Theta-1` (log 0 convention: minus infinity). Take the supremum over actual zeros, not an assumed rightmost zero. A known critical-line zero already rules out `o(L^-2)` on the full grid. In particular `for every epsilon>0, exists C_epsilon, all j: E_j<=C_epsilon H^epsilon` **iff RH** by symmetry. The reverse direction is why this is a detector, not a new upper bound. RIDGE3 instead used `m` proportional to `H^2`, all legal heads, and exponent `2Theta` for the full squared norm. Neither selected good heads nor the remaining outputs are bounded by OCTAVE2. This direct reciprocal-zeta argument needs no transfer from a truncated norm to a full norm.

**OCTAVE3 | PAPER_PROOF: what failure forces in the original pairs.** Set `a_k=log(k/H)` and `W(k,l)=a_k a_l(1/max(k,l)-1/(2H+1))` for `H<k,l<=2H`. Telescoping the exact output weights gives

```
L^2 E_j = sum_{k,l} mu(k)mu(l) W(k,l) = D_H + 2 sum_{h=1}^{H-1} C_h,
C_h = sum_{H<k<=2H-h} mu(k)mu(k+h) W(k,k+h).
```

The diagonal is `D_H=I/zeta(2)+O(H^(-1/2))`, `I=int_1^2 (log x)^2(1/x-1/2) dx>0`: use `sum_{n<=x} mu(n)^2=x/zeta(2)+O(sqrt x)` by square-divisor inversion, and partial summation, retaining `2H+1`. Every lag has absolute mass `O(1)` since `0<=W<=C/H`. In fact the absolute mass is bounded below uniformly for all sufficiently large H and `1<=h<=H/8`. On `[5H/4,3H/2]`, `W(k,k+h)>=c/H`. If the interval has length T, the count of k for which k or k+h is not squarefree is at most `2T sum_p 1/p^2+O(sqrt H)`. Uniformly `sum_p 1/p^2 <= 1/4+sum_{n>=3 odd}1/n^2=pi^2/8-3/4<1/2`. Thus a fixed positive fraction survives both masks. Absolute values on polynomially many such lags cannot yield a subpower total.

For any actual zero as above with `sigma>1/2` and any fixed `0<eta<2sigma-1`, OCTAVE2 forces `L^2 E_j >= c_rho H^(2sigma-1) L^(2d-2)` infinitely often. Removing the diagonal and `h<=H^eta` costs only `O(1+H^eta)`. Partition all remaining lags into at most `O(log H)` successive doubling bins starting just above `H^eta` (last bin truncated). At those heads one bin has **positive** `2 sum C_h >= c' H^(2sigma-1) L^(2d-3)`. Its location can vary. This necessary configuration preserves both orderings and the upper boundary. It neither asserts an off-line zero nor requires each bin to be small under RH.

**OCTAVE4 | PAPER_PROOF: an independently paid band, not the endpoint.** For integer `Y=floor(H^(2/3))`, all sufficiently large H and each fixed `A>0`, `|sum_{Y<h<=2Y} C_h| <<_A Y/(log H)^A`, whereas replacing the summands by their absolute values gives order Y by OCTAVE3. Fix k; partial h-prefixes of `mu(k+h)` start at `x=k+Y` comparable to H and end no later than `min(k+2Y,2H)`. For length at most `H^(31/48)` use the trivial bound, which is `o(Y/log^A H)`. On longer prefixes use Matomaki-Shao-Tao-Teravainen, *Higher uniformity ... I: All intervals*, Theorem 1.1(i), with constant nilsequence and, e.g., epsilon=1/100: `x^(5/8+epsilon)<=length<=x^(1-epsilon)`. Its implied constant is independent of k and the endpoint. The multiplier `W(k,k+h)` has supremum and total variation `O(1/H)` there (derivative `O(1/H^2)`). Partial summation followed by `sum_k |mu(k)|<=H` proves the claim. This keeps both factors' actual signs before the inner estimate; it pays neither other bands nor a power of H. No unproved fixed-shift Chowla estimate is used.

**OCTAVE5 | FINITE_COMPUTATION.** Evaluated the original residue sums independently of the floor return at **all** `H<=m<=2H+2` for `H=6,12,24` (9+15+27 outputs). Replace every `log n` by its prime-valuation vector; do all solver operations over rationals. The strip formula held through `2H+1`. At `2H+2` its discrepancy is exactly `mu(H+1)log((H+1)/H)` (nonzero at 6 and 12, zero at 24 since 25 is squareful). Independently expanded and polarized the quadratic over every single/pair of active prime coordinates: 15+45+120 exact comparisons. For the Abel and translation signs, 5 consecutive blocks through H=96, at `s=1/2+14i,3/4+3i,2+i`, gave maximum numerical disagreement `4.24e-15` (double precision, not a pole test). Checker SHA-256 `f2c7c99b16795289231e6ccd9e482603893a1cfefd058c2df4b833ef55cb8767`. Reproduce by accumulating A for each m, forming its weighted square, and comparing with the double sum above; the residue-side check uses `(m mod k)/k` over **all** `2<=k<=H^2`.

Primary analytic inputs: A. E. Ingham, *On the estimation of N(sigma,T)*, QJM (1940), doi:10.1093/qmath/os-11.1.201 (exponent also displayed in Guth-Maynard, arXiv:2405.20552, (1.2)); X. Li and M. Radziwill, *The Riemann-zeta function on vertical arithmetic progressions*, arXiv:1208.2684, Thm 4; D. Platt and T. Trudgian, doi:10.1112/blms.12460 (existence of critical-line zeros suffices); K. Matomaki, X. Shao, T. Tao and J. Teravainen, arXiv:2204.03754, Thm 1.1(i). Only the fixed parameters and original arithmetic objects identified above are imported.

### E. Specialist findings and continuity

Watermark: last Coordinator PORT final `a6bb36bd906acebfa620478799818a4c995c9818` (Nov 19 23:09 EST, verified paired recovery, blob `b107495e974bbf12d6571d646341126a3e7f5dba`). To intake `0956b4709f4693416c387a5aa2bd903324171a8b`: 13 commits, six specialist paths, no deletion. Enumerated 38 actual dated directories without a calendar cutoff; read today's six full publications, yesterday's canonical reports and relevant recovery finals, own canonical RIDGE/OBS/JET history and later PORT. Nov 19 canonical mirrors are the same 68,209-byte blob `6790b8672ac80f6f3a36ca115929cf19f499cfb4`; PORT's two 26,108-byte recovery files are one later publication, not a canonical append. All rows below are consumed through their final sections; filenames are the standard role stems under the indicated Eastern date. SHA abbreviations are unambiguous report blobs at the full intake commit. No specialist is pending today. The assignments in H are handoffs, not executions.

| Role | Nov 19 consumed -> Nov 20 latest verified (EST, blob, claim) | Finding and review scope |
|---|---|---|
| Owner `10-owner-payment` | 16:15 HINGE `85060bbc` -> 00:09:00 SLICE1-4 `4efb6209` | At `X=B^2`, `B/16<abs(Im rho)<=B/8`, the sharp reflected sector of `7^-s-2*10^-s+11^-s` costs at most B except at `O_eps(M^(5/9+eps))` integer B in `[M,2M)`. Same-height compensation is real; not a pointwise sector bound. Referee accepted with scope. |
| Analytic `20-analytic-type-ii` | 17:11 PHASELOCK `62efb52d` -> 01:04:01 SQUARE1-4 `ac32607e` | Signed new-pair remainder `O_A(N^(-3/8)/log^A N)` on the prescribed outer window. The old pairs, both signs and `Phi(sqrt z)` remain. SQUARE1-3 accepted with scope; SQUARE4 finite. H=12 rules out universal clock coincidence, not an infinite subsequence. |
| Wheel `30-finite-wheel` | 18:06 GATE recovery `a20b2ee3` -> 02:05:02 WINDOW1-5 `5e9b51ec` | Two disjoint cofactor shapes cancel at order `log^(-4) J` for one cutoff and leave a negative fifth-order coefficient there. WINDOW1-4 accepted with scope; 5 finite. Not the whole `F_(2J)-F_J`. |
| Census `40-prime-census` | 19:00 CLOCK recovery `1093df2a` -> 03:11:02 LEDGER1-4 `b7a4cf1c` | Six held-out endpoints at B=1009,1531,2053: low unique mass negative, full unique mass positive. Removing coprimality reverses the main coefficient. LEDGER2 accepted on its degree-weighted measure; other results finite. |
| Referee `50-adversarial-referee` | 20:13 ESCAPEMENT recovery `e063ee0f` -> 04:13:00 APERTURE1-3 `29070a23` | Independently accepted PORT1-4 (PORT1 identity), LEDGER2, TWO-WITNESS, and scoped results above. Own paper derivation displaces the local U4 zero by `-0.8583481/log b+O(log^-2 b)`; the low incidence can have arbitrarily large degree on either sign. No all-mask suppression. |
| Lean `60-lean-verification` | 21:08 PLATEAU/TWO-WITNESS `6231b482` -> 05:10:00 LV/DRIFT `98b91962` | Opening, repair and final are one run. TWO-WITNESS is now merged. DRIFT was separately reported on paper; independent Coordinator check below. |
| Coordinator `00`/`90` | 23:09 PORT recovery `b107495e` -> 07:10:01 current checkpoint `bf9454df`, then OCTAVE1-5 | PORT's signatures apply to the original unique-split mass only. This section is the same scheduled execution as the checkpoint. |

`CONTINUITY_COMPLETE` for the above delta; no newly unconsumed specialist section at the reporting guard. Historical absence of Nov 13/14 dated folders, four Nov 15 roles and the unpublished Nov 18 Referee BG remain `CONTINUITY_UNVERIFIED`; do not invent launches. `EXTERNAL_HANDOFFS.md` unchanged `7d63d434690d00dffce9c90335d41c4f62d85798`: EXT-20261018-PNT-1 preserves the unit and p=R; EXT-20261014-5 rules out an unconditional all-root strict fraction, not conditional first-bad exclusion.

Independent DRIFT check, `ACCEPT_ON_PAPER` for each **fixed** `K>=1,0<H<6K`, not part of #1153. Here `L=log(6K/H)`. For clipping error `e(m)=(a(Q1-K)+z(Q2-K))/L`, write `e(m)=Am+b_m`, `A=U/L`. The period mean of each band residue sum is `(K-s_i)/2`; using `as+zt=U`, `K(a+z)=V` gives `mean b=(U-3V)/(2L)`. In `e(m)^2/[m(m+1)]` the terms are `A^2+(2A b_m-A^2)/(m+1)+b_m^2/[m(m+1)]`. Centering the periodic harmonic term leaves a tail `O_(K,H)(1/M)`. Summing m=1,...,M gives `A^2 M-3UV/L^2 log M+C_(K,H)+O_(K,H)(1/M)`. Thus divergent clipping error at a fixed head with U nonzero is compatible with bounded periodic true residual at that head; no uniform norm supplier.

### F. Mathematical bottlenecks

**First new test, not an assumed supplier:** on the exact `Y=floor(H^(2/3))` band, can one get some fixed `delta>0` and for each epsilon>0 a constant independent of j with `|sum C_h| <= C_epsilon Y^(1-delta) H^epsilon`? OCTAVE4 only saves logarithms. A positive or negative near-order-Y subsequence would falsify the proposed power gain. This one band is neither necessary nor sufficient for RH. To exclude a zero one must rule out the **net positive concentration across the applicable long lags** in OCTAVE3 for every `sigma>1/2`, with its constants fixed first. Uniform smallness of each bin is stronger than what the inverse requires; cancellation across bins is allowed.

VF: for `e(x)=theta(x)-floor(x)`, `I0=e(X/7)-e(X/10)` and `O0=e(X/10)-e(X/11)`, SLICE4 still needs signed opposition at the **same** lower heights. Restore `-I_i O_j` for all four index pairs, the anchored earlier defect and phase `-2 sqrt(2) D_B+2`, all errors and covered base. MU-LIFT: the low mass `V5=sum_{5P+(n)<=b,D(n)>=2} D(n)mu(n)` needs its actual coprime degree weights and second-order return. Its collar begins at `b^2>=B^2`, too late for the same strict prefix. Restore rough, squareful, multiple-split, zero-split and inactive sites, historical convolution, each prefix and both cross orientations. No complete recurrence supplied.

### G. Strategy decisions

Promote the physical strip as a direct **test for failure**, not as an independently solved estimate. Retain the selected-head full-norm program as a distinct reserve; park further clock alignment unless it prices remaining modes and the infinite tail. Retire absolute-value payment of polynomially many shifts, dropping coprimality, and treating a density-one prime bound as an induction step.

Cross-route audit: #1122's finite Euler wheel is `F_R-D_R=li(R^2-1)-pi(R^2-1)` including virtual `d>X` and Euler compensation. Finite A/C has `Q_R=sum_{i,j<R}mu(i)mu(j)floor((R^2-1)/(ij))=2M(R-1)-M(R^2-1)`, with native strict-history `K_R`. Fixed-Lambda square blocks have LOW `O(R)` and complete signed HIGH. #915's actual VF masks, prior denominators and both orientations, and Hecke/NNS Hermitian cross terms, principal, conductor and Gaussian terms cannot be recovered from absolute rows. #949 recovers only the scalar zero boundary, not any of these quadratic forms. R=549 remains a counterexample to universal BLOCK. Preserve VF-LOW, SAT, CODIV, OAI-NNS, JOH, FINITE-AC, CORR4, MU-LIFT, NYMAN. Park OAI endpoint optimization pending a route past physical LOW `47/54`, genuine Hecke `theta>3/5` and the `Re(s)>21/25` correction domain.

### H. Next specialist assignments

1. **Adversarial Referee:** Reconstruct OCTAVE2 without using its conclusion. Attack both endpoint terms, translation phase, Laurent order and compact-uniform Abel estimate; try an affine nonzero orbit with two distinct regular sites. Return independent verdicts for the critical line, off-line case and lag inverse. Any failed bridge suspends the corresponding claim.
2. **Analytic Type II:** On the exact OCTAVE4 band, seek the fixed power in F using a signed bilinear or short-interval mean-square estimate, with the moving `k+h<=2H` edge. Price the same bound for each positive loss; stop if the argument pays only a logarithm or changes mu. A real power gain earns testing on adjacent bands, not a global exponent claim.
3. **Prime Census Laboratory:** Pre-register `j=7,8,9,10`, `Y=floor(H^(2/3))`. Report diagonal, signed and absolute lag bins, the band in F, and full reconciliation with output-wise squared prefixes. Preserve the endpoints and both orientations; use certified rounding for the logarithms. A sign or boundary discrepancy blocks interpretation. Finite results discriminate signed versus unsigned geometry, not asymptotics.
4. **Owner Payment:** From SLICE2/4 bound or obstruct the signed contribution on the moving collar `3/4<=Re rho<=3/4+1/log X` at the actual sharp heights, or its compensating lower-height return at a single common truncation. Keep multiplicities and all other interval products separately unpaid. A fixed-sector estimate with constants diverging at 3/4 cannot settle the pointwise route.
5. **Finite Wheel & Incidence:** In APERTURE2/LEDGER2 on `5P+<=b,D>=2`, use exactly the `1/(D-1)` pair reweighting (and ordered/unordered factor two) or bound its high-D signed tail. Test the left proportional endpoint against its required second coefficient, not just the leading area. The degree-two site 6006 and APERTURE3's unbounded degrees on both signs invalidate any fixed-degree repair. Retain a quantitative return or park this submask.
6. **Lean Verification:** #1153 is merged; no rerun. After independent mathematical review and a duplicate search against `nyman_flat_return_of_moment`, the finite candidate is `log(H)^2 E_j = D_H + 2 sum C_h` with the literal upper boundary, physical solver and real logs. First derive OCTAVE1 by specialization; reuse finite-sum telescoping and symmetry, test `H=6,m=14` as an outside-strip negative control. Do not encode a growth bound, external zero theorem or conjectural power saving as an axiom. Only a qualified non-main PR with exact-head hosted checks and human merge would change its formal status.

### I. Lean and PR status

#1153 changed during this run: open at intake, human-merged **Nov 20 07:16:45 EST**; closing open/draft list empty. Branch `agent/lean-verification/20261120-nyman-two-witness`, first head `9f0a9dce` failed on a redundant `dsimp`; repaired head `e05f68039373d3df16bd1c033b9277178a7eb43d` and merge main share verified tree `64b45dc56544b43f88a9a64e3f8fe1b9a01fa568`. All 12 attached workflows passed. Dedicated run/job `44719772066/136232250227`; independent targeted `44719772064/136232249941`. New dependency counts 558,514,705,770,836; only propext, Classical.choice, Quot.sound. Rank blob `a60a037c44d62f780a67fc524dc3a41cc1eb7935`. With H>0 and two distinct primes strictly between `max(3K,H)` and `6K`, the physical amplitudes are rationally independent; equal clipping errors mean equal ordered floor-count pairs, and zero error occurs exactly at `6K,6K+1`. `PROVED_IN_LEAN / CI_GREEN / MERGED`; not an energy bound or all-head prime-supply theorem.

#1152: raw `907105ddda130ef046fbbaab1fc63076cb886b03`, `44664507110/136050421713`, merged Nov 19 22:04:26 EST; seven finite witness/plateau declarations, no full norm. #1151/#1150/#1149 supply fixed-head moments/profiles, phase and period-plus-bias results. #1119 source `f629db1b2b65d6ec042ac9432397d4b6316200c6`, raw `77ee815846d6d534c866f0752aa33b84c385610a`, `42552018910/128949473700`; #949 source `768c8255850bf4074aff265c3fe17a1f5c43979b`, raw `982500b01f0f008b1164a172d06d28d14f8171d0`, `38741634035/116444547917`; #1135 envelope/bridge `9b25e34a988b0829c29f63df9863e964af600c3f` / `02a88cadc1eb984557b9dd7ee2e03e29bd3e5287`, raw `ac6dc46b70da962e70b18ea184451c225c1cd44a`, `43777334576/133006501690`. These are hosted proof receipts for their actual statements, not certificates for OCTAVE, DRIFT or a missing uniform estimate. No local Lean, proof-branch write, workflow dispatch or merge by Coordinator.

### J. Next-run resume capsule

Start from OCTAVE2's translated-pole test and OCTAVE3's **positive** long-shift bin, not the clipping discrepancy. First adjudicate the proof, then try the signed polynomial-lag improvement in F. Direct consumer: exclude every actual zero with real part >1/2; symmetry and the #949/#1135 bridge give the half endpoint. No iteration, attained supremum or zero-loss input. `VERIFIED_NEW_GLOBAL_GAIN=NONE; RH=OPEN; INDEPENDENT_REVIEW=PENDING`. Alternate source obligations: Owner SLICE4 lower-height/common-square return; Wheel/Census APERTURE2/LEDGER2 full degrees and strict chronology.

Policy pins: half `96ad4439ec458af6168f7d9cb3eef5dde291d37c`, cross-route `e3ae4280438f591f1ffaddd754a1c3a6d35d0691`, continuity `7eef0b36c7442be922d9bc99c6b35d853c4f1f4f`, publication `a9583516fd2e603320c771e32c170132bf0c53e9`. `finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1; high_attack_ack=COMPLETE_SIGNED_HIGH_ATTACK_V1; chain_ack=CANCELLATION_CHAIN_REUSE_V1`. Report paths `research/agent_reports/2026-11-20/{00-coordinator-am,90-coordinator-pm}.md` on `agent-reports`. Early paired commit `a67e7067310a3f79b0cf03f4a130db07e908f9e8`, blob `bf9454dfe6702ffefd36937d5b862ac66d919752`, 1,390 bytes: full exact-commit and pre-append reads matched. One atomic, guarded append preserves that prefix. Final commit, byte count, unique-marker and mirror verification belong to the post-write delivery receipt; this section alone is not that receipt.

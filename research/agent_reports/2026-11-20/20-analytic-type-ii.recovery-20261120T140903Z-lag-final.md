# A power saving for the signed first-octave Mobius lag band

RH | Analytic Type II, November 20, 2026. Scheduled 09:09:03 EST (14:09:03Z), America/New_York; RUN_ID_UNAVAILABLE. Final section marker: `20261120-analytic-0909-EST/LAG-FINAL`.

## A. Result

For the Coordinator's exact sum over `Y<h<=2Y`, `Y=floor(H^(2/3))`, the bound is `O_eps(Y^(55/67) H^eps)` on every prescribed head `H=6*2^j`. Thus the requested fixed saving is `delta=12/67` with every positive loss, or, for example, `O(Y^(5/6))` without a displayed loss. OCTAVE4 supplied arbitrary logarithmic savings. This strengthens that band estimate, **not** the global Mertens exponent, the full energy, or RH.

Claim family `20261120-analytic-0909-EST/LAG`: **LAG1** localized Mellin mean square; **LAG2** uniform signed interval of shifts; **LAG4** squarefree control refuting a prefix-only transfer: PAPER_PROOF / SELF_AUDIT, independent review pending, not Lean-certified. **LAG3** is a conditional inverse consequence of LAG2 and the Coordinator's OCTAVE2. **LAG5** is a finite certificate only. The only zero-confinement input used here is the repository's existing bound, not a new zero-free theorem.

## B. Objective and authority

Main `5ca92d731adafb2e2faeb13277af825dcdbb177b`, tree `64b45dc56544b43f88a9a64e3f8fe1b9a01fa568`; AGENTS `500b6daed5e867d19d97c30e43a7a1e7d2055a51`, contract `95566e37c8eaeb99ee680660df4f9d2e06ea5038`. `VFCanonicalSquareVonKochStatement` asks for one C>=0 such that `|pi(R^2)-vfMidFinishedMass(R)-sqrt(2)|<=C R log R` for every integer R>=2 (blob `79030d70e8d3e0d08eef9bac53fef95c36eca2fb`). Its named implication takes `ClassicalVonKochRHCriterion`. The authorized intermediate question is OCTAVE H.2/F, not the RH-equivalent full-grid subpower bound.

## C. Independent analytic inputs

Write `b=7/8`. Input Z: no nontrivial zeta zero has real part greater than b. On this repository's evidence this follows from #1119, `native_mertens_near_uniform_window_error_closed` (blob `f629db1b2b65d6ec042ac9432397d4b6316200c6`), and #949, `growthExponent_eq_rightmost` (`768c8255850bf4074aff265c3fe17a1f5c43979b`). The stronger native output is every-positive-loss growth at `7/8-7/(64*Npack)`, not a zero-loss source estimate. The argument outside this repository can be read as an implication with Z explicit.

Input D: put `A=30/13`. For each fixed `1/2<=s<=b`, each `e>0` and `T>=2`, `N(s,T) <= C(s,e) T^(A(1-s)+e)`, counting zeros with real part >=s, absolute ordinate <=T, with multiplicity. Guth and Maynard, *New large value estimates for Dirichlet polynomials*, Annals of Mathematics 203 (2026), 623-675, DOI `10.4007/annals.2026.203.2.6`: equation (1.4), combining Theorem 1.2 with Ingham (1940), DOI `10.1093/qmath/os-11.1.201`. Only finitely many fixed s are used for each loss; no numerical effective threshold or uniformity as the loss tends to zero is claimed. Neither input assumes any lag correlation, chosen good heads, or RH.

## D. Exact lag sum

Let H>=6 be an integer; the source takes `H=6*2^j`, j>=0. Put `w_k=log(k/H)`. For `1<=h<=H`, define

```
C_h = sum_{H<k<=2H-h} mu(k) mu(k+h) w_k w_(k+h) (1/(k+h)-1/(2H+1)).
S(a,U) = sum_{a<h<=a+U} C_h,     0<=a, 1<=U, a+U<=H (integers).
```

The empty C_H is zero. LAG2: for each eps>0, uniformly in H,a,U,

```
|S(a,U)| <<_eps min(U, H^(2/67+eps) U^(52/67)).                     (1)
```

The trivial `O(U)` has an absolute constant. This is a bound on the modulus **after** the shifts are summed. It does not give fixed-shift cancellation or a bound of this strength for a sum of absolute correlations.

## E. Proof

**Restore sharp edges.** Fix smooth real `0<=phi<=1`, compactly supported in `(1/2,3)` and equal to 1 on `[3/4,9/4]`. Fix a nonnegative smooth `kappa` supported in `(-1,1)` with integral 1. For real `1<=B<=H/20`, put `eta=B/H`, `P=1/eta`, `kappa_eta(v)=kappa(v/eta)/eta`. Let `g(x) dx` be the signed measure obtained by replacing each atom `mu(n) phi(n/H)` by that mass times `kappa_eta(log(x/n)) dx/x`. Put `f(x)=1_(H<x<=2H) log(x/H)` and `d(x)=f(x)(H/x-H/(2H+1))`. Then S is the sharp atomic double sum with multiplier `H^(-1) f(k)d(l) 1_(a<l-k<=a+U)`. Denote the same integral against `g(x)g(y) dx dy` by `S_sm`.

On the enlarged support each displacement is `O(B)`. A change of membership requires one of k,l within `O(B)` of H or 2H, or l-k within `O(B)` of a or a+U. Each of these six collars contains `O(H(B+1))` lattice pairs. Else the uncut weights vary by `O(B/H)` on at most `O(H^2)` pairs; all have the outer `1/H`. Each displaced atom has mass of absolute value <=1. Hence `|S-S_sm| << B+1`, uniformly, including a=0 and diagonal leakage. Both endpoints of the lag and the moving cutoff have been charged. By Young's convolution inequality with the interval indicator of integral U, `|S_sm| << U ||g||_2^2/H` (Lebesgue dx). With `x=H exp(z)`, Plancherel gives

```
D(t) = sum_n mu(n) phi(n/H) (n/H)^(-it),
J(P) = integral_R |D(t)|^2 |kappa_hat(t/P)|^2 dt,
||g||_2^2 << H^(-1) J(P).                                             (2)
```

Indeed `xg(x)` is convolution in z with `kappa_eta` and `dx/x^2` is comparable to `dz/H` there. No sharp-cutoff Mellin shift is used.

**LAG1.** If `P=H^v`, `0<=v<=2/A=13/15`, then `J(P) <<_eps H^(2b+eps) P^(A(1-b))`. Constants may also depend on the fixed cutoffs. Take `t0=min(eps/100,1/1000)`, `V=H^t0`, `T=PV`. For `|t|>T`, `|D(t)|<<H` and Fourier decay bounds the integral by `O_m(H^2 P V^(1-2m))=O(1)` on taking `m>5/t0`.

Here is the local reciprocal estimate used in the shift. If `|t|>3V+10` and no zero of real part >c, `1/2<=c<=b`, has `|gamma-t|<=2V+10`, then for `|u-t|<=V`, `c+t0<=w<=2`,

```
|1/zeta(w+iu)| <<_(c,t0) (2+|u|)^t0.
```

Use the zero- and pole-free open disk about `2+iu` of radius `2-c`. Normalize its analytic logarithm by the Euler product at the center. Euler summation gives a polynomial bound for zeta in this disk, so the real part of its logarithm is `O(log(2+|u|))` from above. Borel-Caratheodory on radius `2-c-t0/2` gives the same order for the modulus of the logarithm. On radius 1/2 the Euler product gives `O(1)`. Hadamard's three-circles theorem on radius `2-c-t0` now gives `O_(c,t0)((log(2+|u|))^xi)` for some `xi<1`, which implies the displayed estimate. Zeros on the boundary are harmless. The global version with c=b follows from Z, with bounded ordinates handled on a compact set; `1/zeta` is regular at the pole of zeta.

Let `phi_tilde(s)=int phi(x) x^(s-1) dx`. Mellin inversion for D is `H^(it)/(2 pi i)` times the integral of `H^s phi_tilde(s)/zeta(s+it)` on Re s=2, where the Dirichlet series is absolutely convergent. For `|t|<=T`, shift the segment `|Im s|<=V` to `c+t0` whenever the above local criterion holds; otherwise c=b is always available. The global estimate also applies at small heights. The tails on line 2 and the two horizontal segments are `O(1)` using arbitrary fixed Mellin decay order `>6/t0` and the reciprocal bounds just proved. Here `T+V<=H` for all sufficiently large H. Thus `|D(t)| <<_(c,t0) H^(c+2t0)` on that layer. All operations are at fixed H; there is no sum of zero residues or assumption on their spacing.

Leave out `|t|<=3V+10` at cost `O(V H^(2b+4t0))`. Mesh `[1/2,b]` with spacing <=t0 and endpoints included, fixed for this loss. If no zero with real part >=1/2 lies within `2V+10` of t, the cost is `O(T H^(1+4t0))`. Otherwise classify t by the greatest real part among these nearby zeros. If it lies in a cell with lower and upper ends s,c (endpoints assigned once), the pointwise bound is `O(H^(s+3t0))`; the layer has measure at most `O(V N(s,T+2V+10))`, by a union bound which allows overlap and multiplicities. By D this measure is `O_eps(H^(5t0) P^(A(1-s)))`. The largest power is at s=b because `2s+Av(1-s)` is increasing for `v<=2/A`. The empty layer also fits: `1+v<=2b+Av(1-b)` in this range. The finitely many layers and at most `11t0` in exponent losses are absorbed by eps. This proves LAG1.

Combining (2) and restoration gives `|S| <<_eps B+1+H^eps U H^(-1/4) (H/B)^(15/52)`. For `U>=H^(2/15)` balance the terms at `B=H^(2/67) U^(52/67)`; then `P<=H^(13/15)` and `H^(2/15)<=B<=H^(54/67)=o(H)`. Absorb the finite small-H range into the constant. For smaller U the trivial bound suffices. This proves (1), uniformly in the offset a.

## F. Scale and inverse consequence

At U=Y the H-exponent is `110/201+eps` against `2/3`. The same bound holds for `(floor(Y/2),Y]` and `(2Y,min(4Y,H)]` when nonempty, and for any translate of the same length that fits. A fixed number of such bands costs only a fixed factor. At U comparable to H, (1) alone gives `H^(54/67+eps)`, not a new global exponent.

**LAG3, conditional on OCTAVE2.** For an actual nontrivial zero of order d and real part `sigma>17/30`, put `q=2sigma-1`. Then `2/15<q<=3/4`. Fix `q<r<(67q-2)/52<1`. Apply (1) with a=0, `U=floor(H^r)` and a positive eps smaller than `q-(2+52r)/67`. The total of these short shifts is `o(H^q)`. OCTAVE2 gives infinitely many actual grid heads with `L^2 E_j >= c_rho H^q L^(2d-2)`, L=log H. Removing the bounded diagonal and twice the short shifts leaves a positive long-shift total of that order. Of the `O(log H)` doubling bins starting at U (last clipped at H), one has `2 sum C_h >= c_(rho,r) H^q L^(2d-3)`. Its location can vary with j. This pushes the first possible source of that excess beyond the trivial exponent q; it neither asserts such a zero nor excludes the long shifts. For `sigma<=17/30` this strict improvement is not supplied.

## G. Return to the genuine carrier

On the grid `N=H^2=6K`, `p_k=log(N/max(H,k))`, `u=sum_(1<=k<=N) mu(k)p_k/k`, `v0=2L+sum_(1<=k<=N) mu(k)p_k`. For `I1=(3K,4K], I2=(5K,6K]`, let s,t be their reciprocal masses. With `alpha=(u-t*v0/K)/(s-t)`, `beta=(s*v0/K-u)/(s-t)`, the actual coefficients for `2<=k<=N` are `(alpha 1_I1+beta 1_I2-mu(k)p_k)/L`. Keep k=1 in the solver and both repair bands, including their squareful sites. For `r_H(m)=1-sum c_k (m mod k)/k`, the compiled `nyman_flat_return_of_moment` and the solved moment show `L r_H(m)=sum_(H<n<=m) mu(n) w_n` on `H<m<=2H`: the N-tail and repair floors vanish there, and `floor(m/n)=1` on the H-tail. This does not extend by dropping terms elsewhere.

For `E_j=sum_(H<m<=2H) r_H(m)^2/[m(m+1)]`, expansion telescopes to `L^2 E_j=diagonal+2 sum_(h=1)^(H-1) C_h`, since summing from the larger index l to 2H gives `1/l-1/(2H+1)`. The diagonal is nonnegative and `O(1)`. Both orientations are restored. Source blobs: residual `2da630c1d5fb9302e2097ec1e170cf41c2b40609`, flat `2d23721027ecc44e85b7add02fc632b482f03352`, profiles `1ce4bde64139395e79b9ceb2fd2a396457d7098a`. OCTAVE1/3 are the inherited bridge, not new bounds.

## H. Falsification and finite controls

**LAG4.** A sharp prefix estimate, even with the true squarefree support, cannot replace the multiplicative input to LAG1. Define a single sequence, zero up to 6, by `z_n=mu(n)^2 (-1)^floor((n-H-1)/D)` on each disjoint grid block `(H,2H]`, `D=floor(H^(3/4))`. Its prefixes are `O(x^(3/4))`: square-divisor inversion gives squarefree count `x/zeta(2)+O(sqrt(x))`; the alternating run main terms leave `O(D)` per partial grid block, and the errors cost `O((1+H/D)sqrt(H))`. Sum preceding block bounds geometrically.

Yet for all sufficiently large H and every `Y<h<=2Y` one has `C_h(z)>=c>0`. On `[5H/4,3H/2]` the weight is `>=c'/H` for `h<=H/8`. At least `T(1-2 sum_p p^(-2))-O(sqrt(H))` of its T integers are squarefree in both positions, by the union bound for p^2 in each interval. Here `sum_p p^(-2)<=pi^2/8-3/4<1/2`. Over the whole physical domain only `O(Hh/D+h)` pairs cross a run boundary, costing `o(1)` per lag. The unaffected products are nonnegative. Thus the reference sum is `>>Y`. This refutes the prefix-only proposal, not (1) for genuine mu. No stochastic independence is used.

**LAG5.** Rows are `(H,Y,nonzero physical pairs,floor(10^6 S),floor(10^6 S_uncut))`. The negative control keeps `H<k<=2H` but removes `k+h<=2H` and keeps the signed weight unchanged.

```
6     3      1     1306   -11602
24    8     33      285     5578
48   13    134    -3773    -2204
96   20    462     -467     3637
192  33   1682    -1885    -3821
```

At H=6 the only physical pair is (7,11). Each log uses 40 rational atanh terms with remainder at most `2 z^81/(81(1-z^2))`, `z=(n-H)/(n+H)`; round products outwards on both 17- and 23-decimal grids. A separate 75-digit sliding-prefix evaluation lies in every enclosure. Trial division and a sieve agree. For `(H,B)=(24,1),(48,2),(96,2)` the four rational displacements `(1+/-B/(4H))` independently applied to each coordinate caused 24, 100, 221 membership flips; every flip was in a predicted collar. Also checked 67,665 rational layer budgets. Checker SHA-256 `f4cf1fd421718ff2877f69cfc1f2b73b04b26d822a11211af0fdb00b24ca2ace`. None of these tests bounds an implicit constant or certifies all scales.

## I. Significance and limit

Large values of the smoothed Mobius sum can be charged to nearby zeta zeros, at a cost depending on how far right those zeros lie. Using their distribution before taking the physical norm saves a power even after the two sharp boundaries are restored. The reference sequence shows why the Euler reciprocal, rather than unsigned squarefree density or a global prefix alone, matters. This is not an improvement to Input Z, a Chowla theorem, or a bound for coherent signed mass on the longest shifts. The full-grid subpower target remains target-equivalent in OCTAVE2, not an independently paid input.

## J. Handoffs

- Referee: independently audit the zero-free disk logarithm, the layer/empty-layer bounds and all six restoration collars. Review LAG2 separately from OCTAVE2/LAG3.
- Coordinator: test LAG3 only for the stated sigma,r. The proof already covers adjacent shift bands; no schedule or strategy change is requested.
- Owner and Wheel: investigate the signed counts of pairs crossing the two lag endpoints versus those crossing H or 2H. Preserve the original weights, both factors and their joint support; do not import a same-height prime or divisor-shape estimate without a bridge.
- Census: alongside the already assigned grid, use the sharp-versus-uncut contrast as a negative control. For the next test below, report signed boundary and bulk separately; do not fit asymptotic constants from the five small heads.
- Lean: the finite telescope with `2H+1` is separable from this analytic proof. No request to encode density, a power saving or the OCTAVE2 inverse as an axiom; await independent review before formalizing a new estimate.

## K. First missing estimate

For a single macroscopic band, fix `a=U=H/4` (j>=1) and `B=floor(H^(1/2))`, with the fixed cutoffs in E. Does the **signed** restoration difference obey `|S-S_sm| <<_eps B^(1-k) H^eps` for some fixed k>0 and each eps>0? This is a testable proper-boundary question, not a claimed hypothesis of (1). First reconcile the signed collars including their intersections. Even success would not pay the smoothed macroscopic bulk, all bins or RH. Stopping rule: an order-B subsequence refutes this specific saving.

## L. Continuity, evidence and resume

Reports intake `5030bd3371d1b07c9ef97bead78f504700eeb869`; own prior intake `bdc1c610529504f2cfbbca204e81bcc645355fa3` (15 commits, eight changed paths, no deletions). Both Eastern dates checked. Nov 19 latest -> Nov 20 latest, abbreviated blob IDs at intake:

| Role | Previous -> current | Review/status relevant here |
|---|---|---|
| Coordinator | PORT `b107495e` -> OCTAVE1-5 `10b0565e` | Two identical mirrors; OCTAVE2-4 paper/self-audit. |
| Owner | HINGE `85060bbc` -> SLICE `4efb6209` -> JOINT1-3 `e23448e6` | New same-height mixed inverse, not pointwise closure. |
| Analytic | PHASELOCK `62efb52d` -> SQUARE1-4 `ac32607e` | SQUARE1-3 independently accepted with scope; SQUARE4 finite. |
| Wheel | GATE `a20b2ee3` -> WINDOW1-5 `5e9b51ec` | Selected divisor shapes only. |
| Census | CLOCK `1093df2a` -> LEDGER1-4 `b7a4cf1c` | Degree-weight and coprimality matter. |
| Referee | ESCAPEMENT `e063ee0f` -> APERTURE1-3 `29070a23` | Accepted scoped prior results, not LAG. |
| Lean | PLATEAU/TWO-WITNESS `6231b482` -> LV/DRIFT `98b91962` | Formal two-witness; separate fixed-head drift on paper. |

All seven available today. External inbox `7d63d434690d00dffce9c90335d41c4f62d85798`, unchanged: EXT-20261018-PNT-1 preserves the unit/p=R; EXT-20261014-5 concerns all-root, not first-bad. Today's delta consumed; known older November 13-15 gaps remain CONTINUITY_UNVERIFIED, not presumed runs.

No open/draft PR at intake or closing guard. #1153 human-merged at 07:16:45 EST; exact raw head `e05f68039373d3df16bd1c033b9277178a7eb43d`, same tree as main; dedicated run/job `44719772066/136232250227`. This and #1149-1152 are finite clipping/fibre results, not lag estimates. #1119 raw `77ee815846d6d534c866f0752aa33b84c385610a`, `42552018910/128949473700`; #949 raw `982500b01f0f008b1164a172d06d28d14f8171d0`, `38741634035/116444547917`. Targeted logs/axiom evidence checked; no CI run was requested. No Lean change, new formal result, PR, merge or other role's edit in this execution.

`half_bootstrap_ack=BOOTSTRAP_TO_HALF_V1` (`96ad4439ec458af6168f7d9cb3eef5dde291d37c`); `cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1` (`e3ae4280438f591f1ffaddd754a1c3a6d35d0691`); `continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1` (`7eef0b36c7442be922d9bc99c6b35d853c4f1f4f`); `publish_ack=REPORT_PUBLISH_RECOVERY_V1` (`a9583516fd2e603320c771e32c170132bf0c53e9`). `finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1`; `high_attack_ack=COMPLETE_SIGNED_HIGH_ATTACK_V1`; `chain_ack=CANCELLATION_CHAIN_REUSE_V1`.

Canonical intended: `research/agent_reports/2026-11-20/20-analytic-type-ii.md`, verified base `ac32607e1561406f104e2d0255675ef1bfb8d442`, 22,285 bytes. Direct Git tunnel returned HTTP 403. The authenticated staged canonical append did not match the old-plus-new local hash and was never attached. Use create-only recovery; no canonical update or loss of SQUARE. The early checkpoint was read back at commit `3a45c5fde02ac14b601bf96b7c82ca66f3155a49`, blob `f711a24e814fbf0c88cb6cbf1e6167ae95b49eca`, 1,897 bytes; this is also the final pre-write branch head. This final is the same invocation, not a second run. Publication status is reported separately after exact-commit readback. Resume from (1), the explicit range of LAG3, and the proper boundary test in K. Independent review pending. RH=OPEN.

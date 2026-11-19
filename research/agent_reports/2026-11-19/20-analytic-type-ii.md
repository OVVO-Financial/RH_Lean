# Analytic Type II | November 19, 2026

## Opening checkpoint: what can a distant pair of modes actually contribute?

`20261119-analytic-0104-EST/ARC-CHECK`. Actual scheduled trigger 2026-11-19 01:04:00 EST (06:04:00Z), America/New_York. RUN_ID_UNAVAILABLE. EXECUTION=IN_PROGRESS/PARTIAL. No new theorem is claimed here.

Coordinator `20261118-coordinator-2309-EST/PHASE3` leaves the true middle or growing Farey determinants in the original two-band Nyman norm. Test whether a positive average of short frequency intervals can charge genuinely remote pairs and whether the divisor jumps of the prescribed coefficients control intervals away from zero. Keep the original Mobius taper, both corrections, all ordered pairs, the literal value at zero and the infinite tail. This is a bounded feasibility investigation of the direct Mellin endpoint, not an asserted exponent gain. Falsifiers: a missing negative output or wrap, uncharged sharp cutoff, or a loss of positive power in the complementary sector.

Main `6e8bc42b828c7940c3d9137e4a3afa2e2840c5ba`; AGENTS `500b6daed5e867d19d97c30e43a7a1e7d2055a51`; contract `95566e37c8eaeb99ee680660df4f9d2e06ea5038`; reports intake `1b9543f94cdfc3ff40072e58fa9902c3ed02e683`. Source flat `2d23721027ecc44e85b7add02fc632b482f03352`, residual `2da630c1d5fb9302e2097ec1e170cf41c2b40609`, period mean `e005dc717cd3af6b8697d6517acf6516987d3a7e`. The last is an unweighted common-period theorem, not a physical tail bound. No open/draft PR at intake. November 19 Owner AR available; other upstream TODAY=PENDING, November 18 YESTERDAY=CARRY_FORWARD. Own prior LW, Wheel LC, Census ST, Referee FC, Lean VR and separate merged #1149 MEAN distinguished. Some large historical responses are shortened: no claim of exhaustive byte-complete backfill.

`half_bootstrap_ack=BOOTSTRAP_TO_HALF_V1; cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1; continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1; publish_ack=REPORT_PUBLISH_RECOVERY_V1`. Git tunnel 403; authenticated Contents API for this role's new canonical path only. Initial publication is not certified by this text. The canonical endpoint and RH remain open.

---

## A. Where the unresolved energy can occur

`20261119-analytic-0104-EST/ARC-FINAL`. Same invocation as the checkpoint. For the **prescribed** flat two-band Nyman residual, a positive comparison for the entire physical norm costs only `O((1+log N)^5)` outside a shrinking neighborhood of frequency zero. At the support cutoff `N=H^2`, the remaining comparison involves only frequency pairs within `1/N` of each other and within `1/H+1/N` of zero; the actual middle `H<m<=N` is separate. Taking the cutoff at `H` instead includes the middle and all of infinity, with wider arcs. Nothing is inferred about the sign of the omitted pairs of a different, sharp comparison kernel.

The first positive arc has a further consequence: its repair-free part sees **moving partial sums of signed Mobius coefficients**, not just the squares of individual coefficients. Asking for a subpower centered variance there on a multiplicatively covering sequence of heads is already equivalent to RH. It is not a cheaper all-scale input. ARC1-4 below are PAPER_PROOF / SELF_AUDIT; independent review PENDING; NOT_FORMALIZED. ARC5 is finite evidence. NO_NEW_GLOBAL_UPPER_GAIN; RH=OPEN.

## B. Authority and starting point

Main, governing blobs and actual trigger are in the checkpoint. The canonical target is one real C>=0 before every integer R>=2 with `|pi(R^2)-vfMidFinishedMass(R)-sqrt(2)| <= C R log R`. `riemannHypothesis_of_vfCanonicalSquare` also takes `ClassicalVonKochRHCriterion`; ARC does not supply either premise by definition. The separate Nyman terminal is the exact-head Mellin lower bound in G.

Repo baseline #1119: `native_mertens_near_uniform_window_error_closed`, exponent `b0=7/8-7/(64*N_pack)` with every positive loss. Its original fixed fine-slot source, positive-error closure, compensated endpoint and Hecke-to-Mertens transfer remain intact. With positive fine length ell the counts are `ceil(max(1,1/(6ell)))+2` and `ceil(max(1,1/(3ell)))+2`; thus N_pack<=N_star and #1119 improves #1108's `7/8-1/(48*N_star)`. This is reused repository evidence, not a result of ARC; the exterior estimate uses no zero-free input.

## C. Exact carrier and notation

Let H>=6 be an integer multiple of six, N=H^2=6K, L=log H, B=1+log N. Write `p_k=log(N/max(H,k))`, `U=sum_{1<=k<=N} mu(k)p_k/k`, `V0=2L+sum_{1<=k<=N} mu(k)p_k`. For `I1=(3K,4K]`, `I2=(5K,6K]`, set `s_i=sum_{k in Ii}1/k`, `alpha=(U-s2*V0/K)/(s1-s2)`, `z=V0/K-alpha` and

```text
c_k=(alpha 1_I1(k)+z 1_I2(k)-mu(k)p_k)/L,    2<=k<=N.
r(m)=1-sum c_k (m mod k)/k,                    m in Z (nonnegative residues).
w_m=1/[m(m+1)], E=sum_{m>=1}w_m r(m)^2, M_T=sum_{H<m<=T}w_m r(m)^2.
```

The two moment equations give `sum c_k/k=1`, `sum c_k=3`; hence mean zero, `r(0)=1`, `r(-m-1)=-r(m)`. The flat-return theorem gives `r(1)=...=r(H)=0`. Squareful band sites and the unit in the solver are not deleted. Since `s1>=1/4`, `s2<=1/5`, `|U|<=LB`, `|V0|/K<=7L`, we have `max|c_k|<=C B` with an absolute C.

Write `e(t)=exp(2*pi*i*t)`, `||t||=dist(t,Z)`. For every reduced `lambda=a/q` in (0,1), `2<=q<=N`, let `b_q=sum_{q|k,2<=k<=N}c_k/k` and `A_lambda=b_q/(1-e(-lambda))`. The finite geometric sum for `m mod k` folds all repeated frequencies: `r(m)=sum A_lambda e(m lambda)`. This is PHASE1's representation, not a new estimate. Its first difference `j(m)=r(m)-r(m-1)` has coefficients `b_q`. Directly, `j(m)=-1+sum_{k|m}c_k`, including `j(0)=2`.

## D. ARC1: a positive comparison with compact pair support

For integer T>=4 put `delta=1/T`. On the circle let `S_A(x,u)=sum_{lambda in (x,x+u]} A_lambda` with wrap and define `Q_T(D)=delta^-1 int_0^delta int_{x in D}|S_A(x,u)|^2 dx du`. Define `Q_T^b` identically with `b_q` in place of `A_lambda`. All pairs are ordered and use the conjugate in the second position. For the whole circle the pair multiplier is exactly

```text
K_T(lambda,nu)=(delta-||lambda-nu||)_+^2/(2delta).
```

Indeed the overlap at width u has length `(u-||lambda-nu||)_+`. For a restricted set D use the actual overlap inside D, not this whole-circle value. Parseval in x gives `Q_T(circle)=sum_{m in Z}W_T(m)r(m)^2`, with `W_T(0)=delta^2/3` and, for m!=0,

```text
W_T(m)=[1-sin(2*pi*m*delta)/(2*pi*m*delta)]/(2*pi^2*m^2).
```

These are the averages of `|sin(pi*m*u)/(pi*m)|^2`, with value `u^2` at zero. All output series converge absolutely at fixed N; the coefficient family is finite. Reflection yields the **exact** boundary `W_T(0)+W_T(1)` plus `sum_{m>=1}(W_T(m)+W_T(m+1))r(m)^2`. In particular `Q_T(circle)<=C(E+T^-2)`. For `m>=T`, `W_T(m)>=(1-1/(2*pi))/(2*pi^2*m^2)`; consequently `E<=M_T+C Q_T(circle)` when `H<=T<=N`. No transition interval, period averaging, or unpriced infinite tail. Averaging the width matters: at `P=lcm(2,...,N)`, r(P)=1, but the single-width kernel u=1/T vanishes for T=H or N. This refutes a **pointwise** single-width lower comparison, not every norm comparison.

## E. ARC2: the exterior is bounded independently

Uniformly for `H<=T<=N`, `2/T<=theta<=1/2`, with an absolute implied constant,

```text
Q_T({||x||>=theta}) <= 4 theta^-2 Q_T^b(circle)
                     << B^2 (1+log(2T))^3/(T theta^2).
```

For m!=0, `|j(m)|<=1+C B tau(|m|)`. The elementary inequality `tau(n)^2<=tau_4(n)` follows prime power by prime power. Summing ordered factorizations gives `sum_{n<=Y}tau(n)^2<=Y(1+log Y)^3` for Y>=1. The bound `W_T(m)<=min(1/(3T^2),1/(pi*m)^2)` for m!=0, splitting at T and then into doubling intervals, gives `Q_T^b(circle)<< B^2(1+log(2T))^3/T`. The tail costs a convergent `sum_{h>=0}(1+h)^3/2^h`; the zero jump costs `4/(3T^2)`.

For `||x||>=theta`, all points on the short arc have distance at least theta/2 from zero. Set `f(t)=1/(1-e(-t))`. Exact finite summation by parts gives `S_A(x,u)=f(x+u)S_b(x,u)-int_0^u f'(x+t)S_b(x,t)dt`. Here `|f|<=1/(2theta)`, `|f'|<=pi/(2theta^2)`. In normalized L2 of (x,u), integration from 0 to u has norm at most delta by Cauchy-Schwarz and Fubini. Thus the norm factor is at most `(1/2+pi/4)/theta < 2/theta`. Squaring proves ARC2. This bounds the signed sum **before** discarding any interaction inside its squared modulus.

Take `theta=T^-1/2` and `D_T={||x||<theta}`. The exterior costs `O(B^5)`. At T=H, `E<=C(Q_H(D_H)+B^5)` and `Q_H(D_H)<=C(E+H^-2)`; this subpower equivalence has **no missing middle**. At T=N, keep `M_N`: each pair in `Q_N(D_N)` has `||lambda-nu||<1/N` and both radii at most `1/H+1/N`. These support and quantitative statements, not the general Fourier transform, are the improvement over PHASE3.

## F. Determinants and the sharp-window distinction

Let `d=qk||lambda-nu||` for denominators q,k. For any integer D>=1 let `F_D` be the real ordered contribution to `Q_N(D_N)` from `d>D`, using its restricted-arc overlap. Then

```text
E << M_N + max(0,F_D) + (1+D)B^5,        with D<d<qk/N<=N in F_D.
```

To see the lower cutoff cost, `|b_q|<<B^2/q` and `sum_{a mod q}^*|A_(a/q)|^2<<B^4` by summing inverse squared endpoint numerators. For fixed a/q and d>0 each orientation fixes `ak=+d or -d mod q`; each admissible k gives at most one numerator per sign. Degree is at most `2(1+N/q)`. The symmetric ordered-pair inequality `2|AB|<=|A|^2+|B|^2` and overlap <=1/(2N) cost `O(B^5)` per d; the diagonal costs `O(B^4)`. This is PHASE3's counting input with the new kernel. No conclusion that the same determinants have zero contribution to a sharp cutoff.

One genuinely growing sector is paid **also on the literal sharp window** `N<m<=H^3`: all `d>=N^2/4` together have total absolute integrated pair contribution `O(B^6)`. Their circular separation is at least 1/4, so the geometric-sum bound followed by Abel summation gives `|sum w_m e(m(lambda-nu))|<=C/N^2`. The amplitude bound `|A_(a/q)|<<B^2/min(a,q-a)` gives `sum|A|<<NB^3`. This does not pay all sharp-window d>N. The full positive comparison above is what avoids needing that stronger assertion.

## G. Direct half-endpoint and its limit

For a fixed nontrivial zero rho with `sigma=Re(rho)>1/2`, `kappa=2sigma-1`, the inherited Mellin lower bound is `E>=kappa*(H+1)^kappa/|rho|^2`. Indeed the Mellin value at rho of the residual on (0,1) is 1/rho: each corrected basis element has transform `(k^-1-k^-s)zeta(s)/s` (initially Re(s)>1, then Re(s)>0). The flat head confines support to `x<=1/(H+1)` and its squared L2 norm is E, so Cauchy-Schwarz gives the bound. For any fixed `0<eta<kappa`, taking `D=floor(H^eta)` in F forces `max(M_N,F_D)>=c_rho H^kappa` for all sufficiently large legal H (onset may depend on eta). The second alternative is positive **signed** excess, not absolute mass. Alternatively the single observable `Q_H(D_H)` must grow at that scale. One common unbounded sequence with whole E subpower for every positive loss excludes every such zero by symmetry. No such sequence was obtained; the concentrated norm at T=H is equivalent at this scale, not an independent hypothesis.

## H. ARC3: what is inside the first positive arc?

At T=N take only `0<x<1/N`; call its energy Qfirst. Write `t=N(x+u)`. Only **numerator one** can occur, with `N/t<=k<=N`, 1<t<2; almost everywhere k>N/2, so `b_k=c_k/k`. Integrating the triangular slice of the unit square gives exactly

```text
Qfirst = (1/N) int_1^2 (2-t) |sum_{N/t<=k<=N} c_k/[k(1-e(-1/k))]|^2 dt.
```

Let `J=[2N/3,5N/6]`, `F_N(y)=sum_{y<k<=5N/6}mu(k)log(N/k)` and `Vgap(N)=N^-2 inf_{a real} int_J |F_N(y)-a|^2 dy`. On changing variable `y=N/t`, the weight is `(2-N/y)/y^2 >= 1/(2N^2)` on J. The imaginary part of `1/[k(1-e(-1/k))]` is `-cot(pi/k)/(2k)=-1/(2pi)+O(k^-2)`, uniformly here by Taylor's theorem. The upper band is a single y-independent intercept and there is no repair on J. The imaginary suffix therefore equals `constant + F_N(y)/(2pi L) + O(1/(NL))` for almost every y in J. Consequently

```text
Vgap(N) <= C L^2 Qfirst + C/N^3 <= C L^2(E+N^-2)+C/N^3.
```

The constant is removed by the infimum **only for this lower test**, not erased from Qfirst or E. This is not PV1's positive diagonal of squared gap coefficients. On replacing mu by |mu| **only in this test**, the centered Vgap is instead at least cN for large N. Between the first and last quarters of J the central half has at least `length/4-O(sqrt N)` squarefree integers: union bound over multiples of d^2, `sum_{d>=2}1/d^2<=3/4`. Each contributes at least log(6/5). The pairwise variance formula integrates a difference of order N over the two end quarters. This refutes an unsigned subpower shortcut, not a signed Mobius bound.

## I. ARC4: a covering family makes the gap test RH-equivalent

For all legal H, or just the fixed covering family `H_j=6 floor((21/20)^j)` for all large j, the assertion `for every eps>0, Vgap(N_j)<=C_eps N_j^eps` is equivalent on paper to RH. It is **not** proved by ARC3. No covering conclusion is asserted for an arbitrary sparse sequence.

Proof of the hard implication: put `M(y)=sum_{n<=y}mu(n)`, `w(y)=log(N/y)` on J. At its interior atoms `dF_N=-w dM`. If `G=F_N-a` realizes the infimum, integration by parts writes `M=constant-G/w+int (1/w)'G`. On J, `1/w=O(1)`, `(1/w)'=O(1/N)`, so for some real h, `||M-h||_{L2(J)}<=C||G||_2<=C_eps N^(1+eps/2)`. The arbitrary integration constant is essential. Eventually `21/20<=N_(j+1)/N_j<=7/6`; adjacent J overlap in length at least N_j/18. Their constants differ by `O_eps(N_j^(1/2+eps/2))` by the two L2 bounds on this overlap. Geometric telescoping, with the fixed starting constant included, bounds each constant at the same scale. Covering and geometric summation give `int_1^X |M(y)|^2 dy <<_eps X^(2+eps)` for every X>=2. Conversely this mean square pays Vgap directly by integration by parts against w; the endpoint term `w(5N/6)M(5N/6)` is allowed as the centering constant.

Finally `s int_1^infty M(y)y^(-s-1)dy` agrees with `1/zeta(s)` on Re(s)>1 and is holomorphic on Re(s)>1/2 by the mean square: a dyadic block is `O_eps,s(Y^(1/2-Re(s)+eps/2))`, locally uniformly away from the boundary with eps fixed small enough. The identity theorem excludes a zeta zero there. Conversely under RH, `M(y)<<_eps y^(1/2+eps)` supplies the required mean square after reducing eps. This last classical conditional direction is used only to classify strength; see K. Soundararajan, *Partial sums of the Moebius function*, arXiv:0705.0723v2, introduction (1) and Theorem 1. The repo's actual b0 gives only `Vgap<<_eps N^(2b0-1+eps)` by the same transfer. No constant is chosen after N. The compact short-sum technique is in the tradition of P. X. Gallagher, *A large sieve density estimate near sigma=1*, Invent. Math. 11 (1970), 329-339, DOI 10.1007/BF01403187; D-E prove the specific circle comparison here. No general density estimate is being transferred to selected Mobius signs.

## J. ARC5: falsification on the original coefficients

Preregistered primary checks: 19,197 passed. For N=3,...,12 enumerate every ordered pair of reduced fractions. Integrate the affine function `[delta-max((lambda-x) mod 1,(nu-x) mod 1)]_+/delta` by interval midpoints between its breakpoints, adding each observation boundary. Check full=interior+exterior at T=9,16 and the exact first-box multiplier at T=N. These account for 19,086 exact rational comparisons. At H=6,12 check both moments, all exact-head zeros, reflection, divisor and independent Ramanujan-sum jumps using rational vectors of prime logarithms (keep L outside). The binary64 diagnostics are not interval proofs: at H=6 the ordered Q is 0.020082561765 for T=6 and 0.002563160542 for T=36, inside the direct two-sided residue sums through 16,384 plus their analytic remainder. The first-box value from two calculations is 0.00003673060835. Omitting conjugation, folded multiples or the literal boundary is detected. Supplement: 32 exact gap Abel tests; exterior values 0.006311232107 and 0.001241123464, below their explicit jump ceilings. Primary registration/checker SHA256 `dc72d71eeff65d26c582eed5792ec4a491d196bf1781965c561aa7a99035fde1` / `904e19d9f3eb807cc34e3b0f0e81afce56a143359f38c4bf22d39eb755ecc63f`.

**Held-fixed sign test.** For `delta<x<2delta`, T=N, define `P_j=sum_{2<=k<=N, x<j/k<=x+u} c_k/[k(1-e(-j/k))]`. Only j=1,2 occur a.e.; raw contributions at equal reduced frequencies are both retained. Let `X12=2N Re int_delta^(2delta) int_0^delta P1 conj(P2) du dx`. The preregistered H=6,12,18 give respectively `10^6 X12` in `[-54.214,-54.213]`, `[-0.742,-0.741]`, `[-3.540,-3.539]`. All three favor cancellation; **no universal sign or magnitude follows**.

Reproducer: for `a=1/k`, `b=2/l` take `p=max(a,b)-delta`, `lo=max(p,delta)`, `hi=min(a,b,2delta)`. If hi>lo accumulate `[(hi-p)^2-(lo-p)^2]/delta * c_k c_l [1+cot(pi/k)cot(2pi/l)]/(4kl)`. Respectively 173, 2726, 13772 pairs contribute geometrically. Integer outward arithmetic repeated on grids 10^-30 and 10^-50. Compute log by binary reduction and 2*atanh(t), t<=1/3, with d+5 terms and remaining bound `2t^(2m+1)/[(2m+1)(1-t^2)]`; pi by Machin's formula and successive alternating arctan bounds; sin/cos by Taylor through index floor(d/2)+5 with absolute remainder `1/(2m+1)!` at arguments <1. An unavailable optional interval package stopped before arithmetic; the integer version changed neither cases nor sign question. Registration/checker SHA256 `160621fd492a8aab5f1a2afc14f31dc774a189b3d0d93350e3a5593469a27ba7` / `c6a0f283a160d2920a6fb8874d21480bce9036f04bb4b958122f1b0e3daf59d9`.

## K. Specialist handoff and provenance

Coordinator: ARC2/F localize the zero alternative; ARC4 is a no-shortcut result, not a supplier. Referee: audit the reflected zero cells, width averaging, sign of the jump multiplier, free intercept, overlap length and Mellin quantifiers. Census: independently test the two raw layers at H=6 before extending the sign test; preserve even k and both orientations. Wheel/Owner: the second numerator at an even denominator coincides with a first numerator; `mu(2q)=-mu(q)` only for odd q, with both correction bands restored. AR's prime-carry window is a different carrier; no saving for it is claimed. Lean: no ARC formalization request before independent review.

Last consumed to latest actual, November 18 EST except Owner AR on November 19. The live date listing and recovery siblings were checked before research. `TODAY=PENDING; YESTERDAY=CARRY_FORWARD` for the upstream roles other than Owner. Relevant backfill since LW: LC, ST, separate MEAN merge, PHASE, AR. No unverified Referee completion credited.

| Role | Watermark -> latest / first open distinction | Latest report blob |
|---|---|---|
| Coordinator | DAMP -> 23:09 PHASE1-4; middle versus large determinants | `2e6bfc31f2796d47b426546eabf08783c35b3699` |
| Owner | GP -> 00:09 AR1-4; opposite interior imbalance is necessary, not exclusion | `3161b375fa66909c9dc9f373ae75ceb3a1bfa24f` |
| Analytic | PV -> 17:11 LW; enlarged moment-null repairs do not refute the prescribed source | `065a94a6eb8f69b51641011296efbce3f96c87f5` |
| Wheel | PM -> 18:06 LC; within-product sign, across-product return unpaid | `669ba135d05503c1cead5f04106977ff66887ed6` |
| Census | PS -> 19:00 ST; sharp cutoff and period signs differ; PHASE2 later settled H=60 | `780b932540c38e61bb6f81f732e66c4c9b1180b0` |
| Referee | 12:03 FC unchanged; scoped DAMP/PV verdict, not review of PHASE or ARC | `91b57ce6a46693403cd8a5751c63aaf8335ab305` |
| Lean | 13:14 VR last published daily section; 21:08 MEAN independently evidenced by #1149 | `2cd3263317a8afaae5e664f4b56d2c095059421c` |

Coordinator 00/90 have the same Git object for each canonical (`ee7b4ce6ff79ab0eaea4d8b74d95e3e78f398cb5`), recovery CHECK (`8fbab91ec28f0d991c46d0731ec9da6c08d30d56`) and recovery PHASE above. CHECK and PHASE are one invocation. GP's prior-day blob is `a6345e177392d55db551650e8013581b89694623`. External inbox `7d63d434690d00dffce9c90335d41c4f62d85798` unchanged: EXT-20261018-PNT-1 retains the unit cofactor; EXT-20261014-5 is an all-root limsup, not a first-bad counterexample. CONTINUITY_UNVERIFIED for exhaustive whole-file historical backfill: the connector shortened oversized November 18 file responses; the material named sections, immutable blobs and receipts were inspected. No launch is inferred from a date.

Source/loss/recovery: Euler wheel keeps virtual divisors and compensation in `li(R^2-1)-pi(R^2-1)`; VF keeps actual primes, raw history and the canonical phase; NNS keeps original ideal labels, conjugates and principal/HIGH returns; native square blocks keep all signed prefixes of M. None is identical to Q_T. The paid period mean restores all ordered gcd crosses at a period, not physical location. ARC instead preserves the physical norm through inequalities with an explicit boundary. Nine routes preserved; no restart of OAI beyond its 47/54 floor or theta>3/5 coefficient gate.

CI reused, not rerun: #1119 head `77ee815846d6d534c866f0752aa33b84c385610a`, run/job `42552018910/128949473700`; #1147 head `e77d049ff83809c13c52e3d90922f34ed032efac`, `44371410914/135038879279`; #1149 head `1095bfa3c314ff048160fc14e67dfc74106f5d7a`, `44446879526/135301058077`, merged to pinned main. #1148 changed reporting policy only. #1149's raw audit has only `propext, Classical.choice, Quot.sound` (four dependency counts 265,337,385,424); Lean 4.34.1, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. Additional source blobs: canonical `79030d70e8d3e0d08eef9bac53fef95c36eca2fb`, radical increment `c5ebb3d5d96898549ad039fd32e1a26955c5b8f8`, variance `92608fc013c26102ac12250558a850209028e6d8`, period cells `0a506393f45a2e7882f39ae5c17a84505c97b1d5`, #1119 `f629db1b2b65d6ec042ac9432397d4b6316200c6`. No new Lean proof, local Lean execution, PR or workflow launch.

## L. Resume capsule

`STATUS=ACTIVE_SUPPORT; EXECUTION=COMPLETED_BOUNDED_FEASIBILITY_AUDIT; INDEPENDENT_REVIEW=PENDING; VERIFIED_ETA=NONE`. The independently missing input is signed control on one common unbounded prescribed-head sequence inside `D_H`; assuming its entire norm is only a reformulation. Next narrower test: on the second frequency box defined in section J, bound the **positive part** of X12 by `C_eps N^eps` for each eps>0 on the fixed noncovering heads `H_j=6*2^j`, with C_eps independent of j, via even-denominator folding and the remaining odd-denominator layer. A positive certified X12 falsifies the sign-only shortcut, not the weaker upper budget. Even a subpower positive part leaves both self-energies, other boxes and any physical middle at T=N unpaid. Do not pass the three finite signs into an all-scale consumer, or demand the covering Vgap bound as a premise.

Policy blobs: half `96ad4439ec458af6168f7d9cb3eef5dde291d37c`, cross `e3ae4280438f591f1ffaddd754a1c3a6d35d0691`, continuity `7eef0b36c7442be922d9bc99c6b35d853c4f1f4f`, publication `a9583516fd2e603320c771e32c170132bf0c53e9`. `finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1; high_attack_ack=COMPLETE_SIGNED_HIGH_ATTACK_V1; chain_ack=CANCELLATION_CHAIN_REUSE_V1`. Opening checkpoint verified at `fb3fe9611e214caa09ccafef24bacfe85249ae09`, blob `4aab03699d6162352c85b02e24f999ce1fa40677`, 2140 bytes. The canonical update uses that complete unchanged prefix, a current-blob guard, and exact-commit readback; this body does not predict its own receipt. No other role's file, main, schedule, permission or PR was changed.

## 09:09 EST | Compact Mellin band: opening checkpoint

`20261119-analytic-0909-EST/BAND-CHECK`. Scheduled ChatGPT invocation, November 19, 2026 at 09:09:02 EST (14:09:02Z), America/New_York; RUN_ID_UNAVAILABLE. EXECUTION=IN_PROGRESS/PARTIAL. Investigate the Coordinator's RIDGE assignment on 1<=t<=2, retaining the original flat Mobius taper, unit, both exact two-band repairs and the specified crossing heads G. Test whether a zero term can be removed by the repairs as a function on the entire band, not at a single height. No new theorem or subpower bound is asserted at checkpoint.

Main `93398824812269526c1ac8c00f43c7ccfe142751`; AGENTS `500b6daed5e867d19d97c30e43a7a1e7d2055a51`; contract `95566e37c8eaeb99ee680660df4f9d2e06ea5038`; reports intake `3920b7d8aacc794dadf50e6de66c33595ed45dfc`. Flat source `2d23721027ecc44e85b7add02fc632b482f03352`; canonical `79030d70e8d3e0d08eef9bac53fef95c36eca2fb`. All seven November 19 roles present; Lean daily entry partial, independently superseded on source status by human merge #1150 at 14:06:44Z, raw head `0a7d02dabffbb30d247120dd803d5b17afccfcd4`, dedicated run/job `44539205621/135612694340` green. Fixed-head opposite cutoff phases do not bound this growing-head band. Green CI is not evidence for this new work. Own ARC, EX, FOLD, PRISM, RIDGE and Owner EXCHANGE distinguished; endpoint and RH remain open.

`half_bootstrap_ack=BOOTSTRAP_TO_HALF_V1; cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1; continuity_ack=LAST_ACTUAL_REPORT_CONTINUITY_V1; publish_ack=REPORT_PUBLISH_RECOVERY_V1`. Prior canonical ARC `04ea85ac45dd2e12e90ed41111909e01c7897bd3`, 23,314 bytes. Direct Git tunnel HTTP 403; using authorized report-only GitHub API, exact prior-byte guard and immutable readback. This text does not certify its own publication.

Recovery checkpoint for `research/agent_reports/2026-11-19/20-analytic-type-ii.md` on `agent-reports`. Local reconstruction of the full 23,314-byte prior blob matched GitHub. The independently staged replacement failed its byte check (a punctuation change in the prior CI line); it was never attached to the branch. Preserve the canonical original and publish this complete new checkpoint create-only. Resume: analyze the combined Dirichlet polynomial on the crossing set G, then attempt one byte-exact canonical consolidation. Recovery is not a canonical append.

## 09:09 EST continuation | A fixed Mellin band detects the rightmost zero

### A. Main result

`20261119-analytic-0909-EST/BAND1-4`; PAPER_PROOF, SELF_AUDIT, independent referee PENDING, NOT_FORMALIZED. Let Theta be the supremum of real parts of nontrivial zeta zeros, I_H the squared Mellin residual integrated over 1<=t<=2, and G the Coordinator's crossing heads. **The logarithmic exponent of I_H on G is exactly 4 Theta - 2.** More precisely, log(1+I_H)/log H has liminf 4 Theta - 2 over all legal heads and limit 4 Theta - 2 on G. Thus an every-epsilon subpower bound on G is equivalent to RH; even one unbounded subpower subsequence forces RH. This is a restriction on the actual repaired residual, not a proof of RH, an improved Mertens exponent, or a sufficiency claim for finitely many heights. No off-line zero is assumed to exist. The independent new ingredient is propagation of a common polynomial growth bound for an entire, regularized cutoff error from a fixed segment to a fixed zero, including a multiple zero. BAND4 also isolates a weaker signed scalar to investigate.

### B-D. Objective, mechanism, exact carrier

Main `93398824812269526c1ac8c00f43c7ccfe142751`; instructions/contract blobs in opening. Ultimate open target: one C>=0 with |pi(R^2)-vfMidFinishedMass(R)-sqrt(2)|<=C R log R for every natural R>=2; its RH consumer explicitly requires `ClassicalVonKochRHCriterion`. Active BOOTSTRAP_TO_HALF task: improve the verified fixed b*=7/8-7/(64 N_pack), not just a variable exponent. #1119 gives every positive epsilon loss; #949 identifies the native Mertens growth exponent with Theta. Thus 1/2<=Theta<=b*<1 and for each fixed Theta<b<1, M(y)=sum_{k<=y}mu(k) is O_b(y^b) for real y>=1. Today's separate RIDGE assignment is the compact band on its prescribed G. No new fixed exponent or transfer to the canonical discrepancy is claimed.

Legal H in 6N, H>=6; N=H^2=6K, L=log H. Put P_X(s)=sum_{k<=X}mu(k)k^(-s)log(X/k) (real X>=1), Q=P_N-P_H, S(x)=P_x(1), delta(x)=1-S(x). G comprises all legal H with delta(x)=0 for some |x-H|<=3; SS1/PHASE and rounding give unboundedness. Set p_k=log(N/max(H,k)) for 1<=k<=N. I_1=(3K,4K], I_2=(5K,6K] contain integers; B_i(s)=sum_{k in I_i} k^(-s), s_i=B_i(1), d=s_1-s_2>=1/20 by pairing. U=Q(1), v=2L+Q(0), alpha=(U-s_2 v/K)/d, z=v/K-alpha. Let h_k=alpha 1_{I_1}(k)+z 1_{I_2}(k), D=sum h_k k^(-s), and c_k=(h_k-mu(k)p_k)/L for 2<=k<=N. Exact moments sum c_k/k=1, sum c_k=3. Keep both repairs, the k=1 term of Q, and squareful mu(k)=0. Define r(m)=1-sum c_k(m mod k)/k and E_H=sum_{m>=1}r(m)^2/[m(m+1)]. For 0<Re s<1 its Mellin residual and band integral are

```
R_H(s) = integral_0^1 r(floor(1/x)) x^(s-1) dx = [1+zeta(s)(D(s)-Q(s))/L]/s,
I_H = integral_1^2 |R_H(1/2+it)|^2 dt.                 (No 1/(2 pi) in I_H.)
```

Indeed {floor(1/x)/k}={1/(kx)}-{1/x}/k; the Mellin integral of {a/x} is a/(s-1)-a^s zeta(s)/s for 0<a<=1, giving the identity by cancellation and the reciprocal moment. Plancherel gives I_H<=2 pi E_H, not the reverse. No independent repair coefficients or surrogate prime sequence is substituted.

### E. Derivation

**BAND1 (regularization and common growth).** Set W(s)=(s-1)^2 and F_X(s;T)=W(s)X^s[zeta(s)^2(P_X(s)-T(s))-zeta(s)log X+zeta'(s)]. Write F_N=F_N(.;D), F_H=F_H(.;0). Both are entire; W removes the pole at 1. Exactly

```
H^(-s) F_H - N^(-s) F_N = W L zeta(s) s R_H(s).
F_N^(m-1)(rho) = (rho-1)^2 N^rho zeta^(m)(rho) != 0
```

at each fixed nontrivial zero rho of multiplicity m; derivatives through m-2 vanish there. The second identity follows by Taylor expansion: the first nonzero coefficient comes solely from zeta'. Crucially, on EVERY fixed compact K0, sup |F_X|<=C_K0 X^3, with the SAME exponent for all compacts, all legal heads, both choices of T. For Re s<=2 use |X^s P_X|<=zeta(2) X^2 log X, the regularized zeta factors, and |X^s|<=X^2. For Re s>=2, the absolutely convergent differentiated Euler series gives

```
P_X - (log X)/zeta - (1/zeta)' = sum_{k>X} mu(k) k^(-s) log(k/X).
```

After multiplication by X^s its absolute dyadic blocks are O(X(j+1)2^(-j)), uniformly in Re s>=2. Only this half-plane uses the tail series. All disks: the elementary bounds on U,v,d give |alpha|+|z|=O((1+log N)^2); the support N/2<k<=N gives |N^s D|<=C_K0 N(1+log N)^2. This proves the common bound, without Mertens cancellation or any selected-head assumption.

**BAND2 (segment extrapolation).** Let entire f_Y, Y>=2, satisfy sup_{|s|<=R}|f_Y|<=C_R Y^A for each fixed R, with ONE fixed finite A>=0. For every positive-length straight segment J, compact K0, fixed derivative j>=0 and eta>0,

```
sup_K0 |f_Y^(j)| <= C_{J,K0,j,eta} Y^eta (1+||f_Y||_{L2(J)}).
```

Constants may also depend on A and the disk constants. Affinely send J to [-1,1] and enclose K0 plus a unit collar in a disk of radius d0>=2. A degree-n polynomial p satisfies sup_{|z|<=d0}|p(z)|<=C_d0^(n+1)||p||_2: expand in Legendre polynomials, use their squared norm 2/(2j+1) and their three-term recurrence to bound |P_j(z)|<=(2d0+1)^j (here P_j denotes a Legendre polynomial only). Absorb polynomial factors, e.g. C_d0=8(d0+1). Choose c>0 with c log C_d0<eta/2, n=ceil(c log Y), then a FIXED R>2d0 with c log(R/d0)>A+2. Cauchy's estimate bounds the Taylor remainder throughout the smaller disk by 2 C_R Y^A(d0/R)^(n+1)=O(Y^-2); apply the polynomial inequality to the Taylor polynomial, then Cauchy's derivative bound on the collar. The affine map only changes fixed constants. No uniformity as J shrinks, j or the tested zero height grows. Reference for Legendre normalization and recurrence: NIST DLMF 18.3 and 18.9; zeta pole and Dirichlet series: DLMF 25.2.

**BAND3 (sharp exponent).** For fixed Theta<b<1, on s=1/2+i[1,2], partial summation from M(y)=O_b(y^b) gives A(y,s)=sum_{k<=y}mu(k)k^(-s)=O_b(y^(b-1/2)), uniformly for y>=1. Hence P_X=integral_1^X A(y,s)dy/y=O_b(X^(b-1/2)). BAND1 and boundedness of the fixed-band zeta factors give, with no division by zeta,

```
||F_N||_2 <= C_b N^(1/2) [H^(b-1/2)+L(1+sqrt(I_H))].
```

If I_H=O(H^lambda), lambda>=0, along any unbounded legal subsequence, apply BAND2 with Y=N at each fixed rho and derivative m-1. Taking logarithms along that subsequence and eta down to zero gives Re rho<=max{(b+1/2)/2, 1/2+lambda/4}. Take the supremum over zeros AFTER the individual inequalities, then b down to Theta. If Theta>1/2 the first alternative is strictly less than Theta, so lambda>=4 Theta-2. For Theta=1/2 use log(1+I_H)>=0. A subsequence below the proposed liminf would give a violating fixed lambda. This proves the all-head lower exponent, even if no zero attains Theta.

For the matching upper bound, a(y)=sum_{k<=y}mu(k)/k=O_b(y^(b-1)): partial summation gives convergence at 1, with sum 0 by the limit of 1/zeta(1+u). Since S'=a/y off integers, S tends to a finite limit; u integral_1^infty S(y)y^(-u-1)dy=1/[u zeta(1+u)] tends to 1. Thus delta(y)=O_b(y^(b-1)); on G integration from its nearby crossing improves delta(H) to O_b(H^(b-2)). Now U=delta(H)-delta(N)=O_b(N^(b-1)); v=2L+integral_H^N M(y)dy/y=O_b(N^b). Both exact repair amplitudes are O_b(N^(b-1)). Since B_i=O(N^(1/2)) on the band, the complete R gives sqrt(I_H)<=C_b(1+N^(b-1/2)/L) on G. Let b decrease to Theta in the logarithmic limsup; unbounded G also bounds the all-head liminf from above. This proves A. On G the same exponent follows for log(1+E_H)/log H IF using RIDGE4's separate full-norm upper bound; our band does not bound its complement. RH yields a subpower estimate, not convergence to zero.

**BAND4 (first signed scalar).** Put D_1=sum_{k>=2} h_k log(N/k)/k (on the finite support), gamma=Euler's constant. Restoring s=1 in BAND1 gives the exact equalities

```
F_N(1) = -N delta(H),
F_N'(1)/N = 2 integral_N^infty delta(y)dy/y - 2 gamma delta(H) - D_1.
```

For details, set A=P_N-D; then A(1)=S(H). Expanding zeta(1+u)=1/u+gamma+O(u) yields F_N'(1)/N=log N(A(1)-1)+2 gamma A(1)+A'(1)-log N. The finite identity sum_{k<=N}mu(k)log^2(N/k)/k=2 integral_1^N S(y)dy/y converts this to 2 gamma S(H)-2 integral_1^N delta(y)dy/y-D_1. Finally integral_1^infty delta(y)dy/y=gamma: its u-damped transform is 1/u-1/[u^2 zeta(1+u)], and dominated convergence is justified by b<1. All tails here are absolutely integrated. Thus the crossing controls |F_N(1)|=O_b(H^b), but in general the proved bound for F_N'(1) on G is just O_b(N^b). A subpower band on a selected subsequence would NECESSARILY give, for every fixed epsilon>0 on that same subsequence,

```
|2 integral_N^infty delta(y)dy/y - D_1| <= C_epsilon N^((b*+1/2)/2-1+epsilon).
```

Indeed BAND2 at 1 with j=1, the BAND3 norm inequality, and b just above b* give this bound after division by N; delta(H)=O_b(N^((b-2)/2)) is smaller. This scalar estimate has not been proved at the displayed saving, and success for this scalar alone is not known to imply band control. It can be evaluated using the exact finite integral instead of a numerical infinite tail.

### F-I. Scale, bridge, falsification and interpretation

The exponent is in the HEAD H, for the SQUARED integral. Losses are arbitrarily small fixed powers, not a uniform endpoint constant; constants are fixed before the head, and may depend on b, eta, segment, zero or derivative in the indicated steps. No zero sum, limiting height, termwise positivity of a covariance, or bound on a moving band is used. An estimate on a single ordinate is insufficient: Y times a polynomial vanishing at any specified finite list is an entire counterexample to replacing J by that list. Dropping the common exponent in BAND2 also fails (Y^s on a segment of the imaginary axis and at s=1). These are tests of the analytic lemma, not counterexamples on primes. The real arithmetic mechanism is the compact support of the two repairs at k comparable to N and exact Euler cancellation on the right of 2; it is not a rank-two independence or density assumption. The zero need not lie in the band. Full E and I_H are different observables. No equivalent compact-band proof was located in the inspected sources/handoffs; no literature priority claim. Treat the band's subpower target as TARGET_EQUIVALENT, not as a cheap bootstrap input.

**Finite audit (diagnostic, not the proof).** Rebuilt mu both by a sieve and by exact divisor recursion for all n<=3600; 54 rational Taylor-germ tests (multiplicities 1 through 6). For H=6,12,18,30,60, genuine residual versus split polynomial versus regularized identity differed by <3.4e-14; 32- and 64-node Gauss-Legendre I_H agreed within 1e-12. Computed I_H respectively 0.00042787908203, 0.0000121002008501, 0.0000630637345628, 0.000210878656787, 0.0000141091652896. Crossing flags at 60 decimal digits: no/yes/yes/yes/yes (delta affine in log y per unit interval). BAND4 integral versus direct polynomial derivative differed by <9e-15. Floating checks are not interval certificates. Replay: integrate 1-delta's defining finite sum or delta on each [n,n+1] in log y, evaluate both Mellin formulas at Gauss-Legendre nodes on [1,2], retaining k=1 in Q only; checker SHA-256 `31e28359c8cb3cabe855607d55afe653c9a0f2f621adbb5d52d26b85b65d6761`.

### J-L. Handoffs, first missing estimate, resume

- Coordinator: classify RIDGE's compact-band subpower request as RH-equivalent on G, pending independent review; no new b<b* or all-R theorem. Recommend the strictly more limited BAND4 scalar as a test, not a campaign change.
- Referee: check common exponent on arbitrarily large fixed disks, the L2-to-derivative loss, the two distinct cutoff powers, and the order of the zero supremum and b limit. BAND1-4 are new self-audits; PRISM did not review them.
- Census: compare the TWO signed BAND4 terms at actual crossings and the neighboring legal heads; use the finite identity and high precision/intervals for cancellation. No request for a larger unguided scan.
- Owner/Wheel: look for a factor-conditioned relation for D_1 and the signed integral with exactly these two amplitudes. EX/EXCHANGE concern different carriers; absence of a sixth-window cover supplies no sign for this difference. Lean: only after referee acceptance, start with finite jet algebra; do not assume the subpower assertion in a purported proof.
- First independent input still missing: save any fixed positive power over the separate O_b(N^(b-1)) bounds for the signed BAND4 difference uniformly on a proved unbounded crossing subsequence, using actual arithmetic rather than a band/RH assumption. The displayed necessary exponent is the sharper benchmark. Neither a saving nor a bootstrap transfer from it is asserted. Next run: derive a signed summation kernel for this difference and test whether its leading contributions can be paired, or prove a precise obstruction.

Continuity/receipts (Nov 18 -> Nov 19, America/New_York). Coordinator PHASE mirror `2e6bfc31f2796d47b426546eabf08783c35b3699` (one logical run), RIDGE `c9e2abd043ddbfd06f9a7f827f8a634688fc460e`; Owner GP `a6345e177392d55db551650e8013581b89694623`, AR `3161b375fa66909c9dc9f373ae75ceb3a1bfa24f`, EXCHANGE `9ba622ebb08e1a08697001d85b6010b1204d79f2`; Analytic LW `065a94a6eb8f69b51641011296efbce3f96c87f5`, ARC in canonical prefix unchanged; Wheel LC `669ba135d05503c1cead5f04106977ff66887ed6`, EX `85d15b9799821e757db49a6c869335bbdfefb99b`; Census ST `780b932540c38e61bb6f81f732e66c4c9b1180b0`, FOLD `03f2a7549512c2daf3dd07cb3b99224463803e11`; Referee FC `91b57ce6a46693403cd8a5751c63aaf8335ab305`, PRISM `683086174ce66d2d5969863d6861cfa2e8f95fa0` (ARC accepted within scope; BG NOT_PUBLISHED); Lean VR `2cd3263317a8afaae5e664f4b56d2c095059421c`, EXTREMA partial `559d0fb002c06791753bc68fcc24ed5dc7031ff7`. All seven TODAY present at intake, no inferred later run. Previous own intake `1b9543f94cdfc3ff40072e58fa9902c3ed02e683` to this intake 14 commits, eight Nov 19 paths; changed/latest sections checked. CONTINUITY_UNVERIFIED only for exhaustive bytewise retrieval of all historical previews. External handoffs unchanged `7d63d434690d00dffce9c90335d41c4f62d85798`; EXT-20261018-PNT-1 virtual complete Euler F-D=li-pi, c=1,p=R; EXT-20261014-5 demands every R. Native Mertens, actual-prime VF (#915), virtual Euler, NNS conjugate/HIGH, and repaired Nyman coefficients remain distinct. OAI/CODIV parked; no renewed signed prefix or half-crossing. No external handoff or central file edited.

Source audit at stated main: `research/NYMAN_FLAT_TAPER_RETURN_20261104.lean` `2d23721027ecc44e85b7add02fc632b482f03352` (`nyman_flat_exact_head`, `nyman_two_band_moment_solver`); `NYMAN_HIGH_COEFFICIENT_INVARIANT_20261104.lean` `2da630c1d5fb9302e2097ec1e170cf41c2b40609`; `NYMAN_PERIOD_MEAN.lean` `e005dc717cd3af6b8697d6517acf6516987d3a7e`. #1149 period bias/covariance, #1150 fixed-head cutoff identity/opposite phases only. #1150 merged 14:06:44Z; Abel `619af08976af9aad42d8ef65ee25673e7dbe5bda`, phases `4967409ba4b71e5ddeb720aa502ac8b8e6ed89c8`, exact raw CI head and run/job in opening, 12 green workflows; dedicated log 454/661/741/763, standard axioms only. No open/draft PR at intake. #1119 `research/oai_434/VF919WindowErrorClosure.lean` `f629db1b2b65d6ec042ac9432397d4b6316200c6`, exact tested `77ee815846d6d534c866f0752aa33b84c385610a`, `42552018910/128949473700`; #949 `research/MERTENS_CONVERSE_IDENTIFICATION.lean` `768c8255850bf4074aff265c3fe17a1f5c43979b`, `growthAtMost_of_strip`, `strip_at_rightmost`, `growthExponent_eq_rightmost`, tested `982500b01f0f008b1164a172d06d28d14f8171d0`, `38741634035/116444547917`. Canonical source `research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean` `79030d70e8d3e0d08eef9bac53fef95c36eca2fb`. Earlier CI is not BAND evidence. No new Lean build, exponent claim, code change, PR, or schedule action.

Resume key `20261119-analytic-0909-EST/BAND-FINAL`; RUN_ID_UNAVAILABLE. Research execution complete at paper level; independent audit pending. Opening recovery commit `14da84c644a92756f69a9c13651e4574cc555d52`, blob `34bca7e06c093da85060f46eec436d4a9f042b1a`. This report's publication is verified separately by immutable readback, not by its filename or status text.

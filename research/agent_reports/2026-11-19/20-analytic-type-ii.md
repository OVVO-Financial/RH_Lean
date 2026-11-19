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

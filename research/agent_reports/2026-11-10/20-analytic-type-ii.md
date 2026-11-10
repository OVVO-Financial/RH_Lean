# RH | Analytic Type II - 2026-11-10

## Final Research Synthesis - 20261110-analytic-1/HF

### A. Most Important Analytic Development

**Paper result: the ENTIRE high-frequency interval `sqrt(R)<=t<=R` of the genuine prime-minus-li quadratic source has bound `O_epsilon(R^(71/52+epsilon))`.** This replaces yesterday's `O_epsilon(R^(17/12+epsilon))` estimate for only one middle band with a stronger bound covering all the high bands. In particular, this entire contribution is `O(R^(11/8))`. The exponent improvement is `2/39`, before accounting for the strictly better native zero boundary.

The new mechanism is an averaged treatment of the sharp explicit-formula remainder. Its old pointwise `O(1+|t|)` bound is not affordable near `t=R`; representing this SAME remainder as a Fourier transform gives a normalized band mean square `O(1+U)`, not `O(U^2)`. Classical Ingham/Huxley density bounds then control every band. All prime powers, endpoint values, continuous reference terms, remote zeros, multiplicities and band summation are included.

| Claim ID | Result | Evidence/status |
| --- | --- | --- |
| `20261110-analytic-1/HF1` | Uniform averaged sharp explicit-formula remainder, with exact prime-power adapter | PROVED_ON_PAPER; SELF_AUDIT; INDEPENDENT_REVIEW_PENDING; NOT_FORMALIZED |
| `20261110-analytic-1/HF2` | Full high-frequency weighted energy and signed-product bound, exponent `kappa(b_*)<=71/52` | PROVED_ON_PAPER from the specified existing zero boundary and classical analytic inputs; same review limits |
| `20261110-analytic-1/HF3` | Joined high-frequency/sharp-boundary estimate and complete original-source return | New quantitative consumer plus credited EXACT_IDENTITIES; full discrepancy still OPEN |
| `20261110-analytic-1/HF4` | Signed resonant-resonant localization with remainder `O_epsilon(R^(641/520+epsilon))` | PROVED_ON_PAPER; no cancellation theorem for the retained resonant statistic |
| `20261110-analytic-1/HF5` | Generic pointwise-remainder extension refuted; counting-only energy obstruction | PROVED_ON_PAPER on explicitly synthetic controls, not counterexamples to genuine primes or RH |
| `20261110-analytic-1/HF6` | Exact finite arithmetic and diagnostic transform checks | FINITE_VERIFIED on declared domains; floating checks are diagnostic only |

**No `O(R log R)` bound for the complete finite wheel, no new Mertens/zero-boundary exponent, and no RH proof is claimed.** These are paper arguments, not newly Lean-certified theorems. Publication status and mathematical status are separate. The preserved early checkpoint is historical; a verified publication receipt follows only after successful immutable readback.

### B. Current Mathematical Objective

Actual main HEAD, retrieved at intake and again before report preparation: `7c7e0a4f54ee2972d3993abc42e5c7c4e1b405c9`. `finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1`.

For integers `R>=2`, with principal-value `li`,

```text
X=R^2-1, y=R-1, P_y=product_(p<=y) p,
delta(y)=product_(p<=y)(1-1/p),
F_R=sum_(d|P_y) mu(d) fract(X/d),
D_R=X delta(y)+pi(y)-1-li(X),
Z_R=F_R-D_R=li(X)-pi(X).

OPEN: exists ONE C>=0, forall integers R>=2, |Z_R|<=C R log R.
```

The equality is the actual complete-wheel source identity, not an averaged density substitution. The bound is the current RH-equivalent arithmetic objective. Every virtual `d>X` is canceled against its own Euler-mass contribution BEFORE truncation. The physical divisor `d=X` is retained. `li` versus `Li_2` differs by its fixed normalization constant; it is not silently changed. The terminal canonical von Koch consumer still has its explicit `ClassicalVonKochRHCriterion` interface.

Directly read authority/source blobs at this main SHA:

| Material | Blob SHA |
| --- | --- |
| `AGENTS.md` | `6695522a45d67fd1e80a7cff1f98d909405036e2` |
| `CURRENT_PROOF_CONTRACT.md` | `95566e37c8eaeb99ee680660df4f9d2e06ea5038` |
| `docs/RHLEAN_SEVEN_AGENT_FINITE_WHEEL_BOUNDARY_20261108.md` | `e505f35522b675c6b5b263eac73618d717346973` |
| `docs/DYNAMIC_RESEARCH_AGENTS.md` | `e8d913ff9663bb5163eaf0eddca9f76e0508a7ef` |
| `research/CompleteSquareRootWheelFractionalBoundary.lean` | `ecb482e52deeee5e9b3853592a3ffdace662d2ff` |
| `research/VF_MID_DYADIC_PREFIX_OWNER.lean` | `c499ca7bd7d90fb32f9cd99d652961ea023bed58` |
| `research/oai_434/VF919WindowErrorClosure.lean` | `f629db1b2b65d6ec042ac9432397d4b6316200c6` |
| `research/oai_434/VF919NativeStrictMertens.lean` | `b33a4883e1ddb0551b0f11f062bce46680d87450` |
| `research/OAI_SHARP_ROOTGRID_HEIGHT_BUDGET_20261028.lean` | `28d439b1a61688ffd174353bd29a153f5e159aa9` |

The [complete-wheel source](https://github.com/OVVO-Financial/RH_Lean/blob/7c7e0a4f54ee2972d3993abc42e5c7c4e1b405c9/research/CompleteSquareRootWheelFractionalBoundary.lean) supplies `finiteWheel_divisorReciprocal_eq_eulerProduct`, `finiteWheelFract_eq_physical_add_virtual`, `finiteWheelFract_sub_density_eq_physical_floorError`, `finiteWheel_squareLegendre_identity`, and `finiteWheel_squareFractional_centered_eq_reference_sub_pi`. The last theorem permits an arbitrary real reference; choosing `li(X)` does not supply a discrepancy estimate.

### C. Analytic Mechanism Investigated

The [November 9 Analytic report](https://github.com/OVVO-Financial/RH_Lean/blob/679f2198c7d399e46d149c269136e3e5a3da5b3e/research/agent_reports/2026-11-09/20-analytic-type-ii.md) contains `20261109-analytic-1/SC`, `20261109-analytic-2/MB`, and `20261109-analytic-3/ZD`. Their identities and prior results keep those IDs. ZD remains self-audited and independently unreviewed. This proof is supplied in full rather than treating that review as completed.

Changed question: can the actual signed transform be bounded on ALL `sqrt(R)<=t<=R`, with a sharp-boundary return? Simply extending ZD's pointwise remainder estimate fails: squaring an `O(t)` error on a band of height `U` costs `U^2`. Instead, fix one explicit-formula cutoff for every frequency and use Plancherel on its bounded spatial remainder. This is a restriction that arbitrary error vectors indexed independently by `t` do not satisfy.

The independent arithmetic inputs are the repository's existing actual-zeta zero boundary and classical zero-density estimates. The latter improve at larger heights after division by the band length. That makes the lowest high band the worst exponent; the other bands can be joined at logarithmic total cost. Cauchy-Schwarz is used with its loss displayed, not as a claim that the original statistic is Hermitian or that zero phases are independent.

Scoped novelty checks: current-main searches for `Huxley`, `Plancherel` with `finiteWheel`, `71 / 52`, and `high-frequency` with `prime`, plus the seven prior-day reports, found no existing result for this exact full prime-transform sector. The closest root-grid budget source was inspected; it is different-carrier exponent accounting and does not provide this analytic remainder lemma. This is NOT a literature-priority claim. The classical methods themselves are not new.

### D. Exact Mathematical Formulation

Throughout HF1-HF4, `R>=8` is an integer, `L=log R`, `ell=log 2`, `X=R^2-1`, and

```text
I_-=[R/2,R), I_+=[R,2R],
dnu(u)=d pi(u)-du/log u,
A_I(t)=integral_I (u/R)^(-it) dnu(u),
A_R(t)=A_(I_-)(t), B_R(t)=A_(I_+)(t),
a_R=log(1-R^(-2)).

H_R(eta)=(1/pi) integral_(sqrt(R))^R
           eta(t) Im(exp(it a_R) A_R(t) B_R(t)) dt/t,
eta:[sqrt(R),R]->[-1,1] measurable.
```

This `H_R` is a proper frequency sector of the current prime source, NOT the historical Mertens HIGH component. The product has no complex conjugation. Endpoint conventions include a prime at `R` only in `I_+`; all proper prime powers at `2R` remain in the adapter.

Define, on `1/2<=s<=7/8`,

```text
d(s)=3(1-s)/(2-s)       for 1/2<=s<=3/4,
     3(1-s)/(3s-1)      for 3/4<=s<=7/8,
kappa(s)=2s-1/2+d(s)/2,
g_b=max_(1/2<=s<=b) [s+(d(s)-1)/2].
```

Here `N(s,V)` counts actual nontrivial zeta zeros with `beta>=s` and `0<gamma<=V`, with multiplicity. Counts using both signs differ only by the factor 2 from conjugation. All zero sums below retain multiplicity.

**HF2, parameterized theorem.** Suppose every actual nontrivial zeta zero `rho=beta+i gamma` has `beta<=b`, where `1/2<=b<=7/8`. For every `epsilon>0`, there is `C_epsilon` independent of `R,b,I,eta` such that

```text
integral_(sqrt(R))^R |A_I(t)|^2 dt/t <= C_epsilon R^(kappa(b)+epsilon),
integral_(sqrt(R))^R |A_R(t)B_R(t)| dt/t <= C_epsilon R^(kappa(b)+epsilon),
|H_R(eta)| <= C_epsilon R^(kappa(b)+epsilon).
```

The zero-boundary hypothesis is explicit in this parameterized statement. For this repository it is supplied by the existing pair of source theorems `native_zeta_zero_re_le_hecke_beta` and `OAI.SevenEighths.RHLeanWindowSaturated.native_beta_le_near_uniform_window_error_closed`:

```text
b=b_*=7/8-7/(64 N_*),
N_*=nearUniformSlotCount, a fixed positive natural number.
```

The [native zeta adapter](https://github.com/OVVO-Financial/RH_Lean/blob/7c7e0a4f54ee2972d3993abc42e5c7c4e1b405c9/research/oai_434/VF919NativeStrictMertens.lean) uses the actual modulus-one Dirichlet/Hecke identification. The [window closure](https://github.com/OVVO-Financial/RH_Lean/blob/7c7e0a4f54ee2972d3993abc42e5c7c4e1b405c9/research/oai_434/VF919WindowErrorClosure.lean) has no free arithmetic error hypothesis in the quoted endpoint theorem. Its existing numerical boundary is reused, not improved or re-proved here.

External analytic inputs, with their scope:

1. Classical Ingham and Huxley give `N(s,V)<<_(s,delta) V^(d(s)+delta)` for fixed `s` in the respective ranges and every `delta>0`, with multiplicity. Equations (1.2)-(1.3) of the primary research paper [Guth-Maynard, v2, April 2026](https://arxiv.org/html/2405.20552v2) restate these results and identify the original sources. The Huxley original is [Inventiones 15 (1972), 164-170](https://doi.org/10.1007/BF01418933); its full text was not independently retrieved in this run. Bibliographic correction to the prior ZD report: Ingham's QJMath 11 (1940) page range is **291-292**, not 201-202. No mathematical input changes with that correction. No claim is made to use the strongest currently known density bound.
2. A truncated explicit formula provides, with one permissible `T in [R^2,R^2+1]`, `psi(u)=u-sum_(|gamma|<=T) u^rho/rho+E_T(u)` and `|E_T(u)|<=B_0 L` throughout `R/2<=u<=2R`, including one-sided endpoint choices, for an absolute `B_0`. The uniform error `O((u/T)log^2(uT)+log u)` is stated before (3.18), p.399, in [Languasco-Settimi, Acta Arith. 154 (2012)](https://www.impan.pl/shop/en/publication/transaction/download/product/83272). A permissible zero-avoiding height in that unit interval can be chosen using the local zero count. The same height is used for ALL `t` and both spatial intervals. Prime-power midpoint conventions change the error by at most `O(log R)` and are absorbed before defining the exact right-continuous remainder.
3. The ordinary count `N(V)=O(V log(2V))` and local count on unit intervals `O(log(2+|v|))`, with multiplicity, are used. See the primary [Fiori-Kadiri-Swidinsky zero-count paper](https://arxiv.org/pdf/2204.02588) and the local-count use in Guth-Maynard, section 13.2. No zero simplicity, pair correlation or independence is assumed.
4. Ordinary Fourier Plancherel is used with angular frequency: `integral |fhat(t)|^2 dt=2pi integral |f(s)|^2 ds`. For the credited sharp-cutoff return only, the interval sieve `pi(M+N)-pi(M)<2N/log N`, `M>0,N>1`, is Theorem 2, equation (1.12), of [Montgomery-Vaughan, The Large Sieve (1973)](https://backend.production.deepblue-documents.lib.umich.edu/server/api/core/bitstreams/5adbb05b-05d0-4779-b1fd-304ec1ec257a/content).

The density bound needs uniformity in a MOVING `s`. It is not inferred merely from a fixed-`s` statement. Here `d` is decreasing, continuous, and Lipschitz with constant 4. For any `delta>0`, choose a finite mesh of width at most `delta/8`, including `1/2,3/4,7/8`. For the lower mesh point `s_j<=s`, monotonicity gives `N(s,V)<=N(s_j,V)`, and `d(s_j)<=d(s)+delta/2`. Apply the fixed-point theorem with loss `delta/2` and take the maximum of finitely many constants. At `s=1/2` ordinary zero counting absorbs a logarithm. Thus

```text
forall delta>0 exists C_delta forall 1/2<=s<=7/8, V>=2,
N(s,V)<=C_delta V^(d(s)+delta).                         (HF.D1)
```

This proves the compact uniformity required below. Classical constants are effective in principle; no numerical `C_epsilon` or numerical asymptotic onset is evaluated here.

### E. Mathematical Derivation

#### HF1. A Single Spatial Remainder Pays Every High Band

Choose the single `T` of D. All sums over zeros are finite, with multiplicity. Define `E_T` by the exact formula with right-continuous `psi`; one-sided endpoint values implement the stated half-open/closed intervals. For either logarithmic interval `J=[-ell,0]` or `[0,ell]`, set

```text
f(s)=1_J(s) E_T(R exp s)/(L+s),
g(s)=f(s)/(L+s).
```

Stieltjes integration by parts gives EXACTLY

```text
r_psi,I(t) = endpoint_I(t) + it fhat(t) + ghat(t),
r_psi,I(t) = integral_I (u/R)^(-it)/log u dE_T(u).       (HF.1)
```

The endpoint term is the appropriate difference of `exp(-its)E_T(R exp s)/(L+s)` using the one-sided values at the two endpoints. The values assigned to `f,g` at endpoints do not affect their Lebesgue transforms. Since `L>=3ell`,

```text
|endpoint_I(t)|<=3B_0,
||f||_2^2 <= (9/4)B_0^2 ell,
||g||_2^2 <= (81/16)B_0^2 ell/L^2.
```

Apply `|a+b+c|^2<=3(|a|^2+|b|^2+|c|^2)`, `t<=2U`, and Plancherel. For EVERY `U>=1`,

```text
(1/U) integral_U^(2U) |r_psi,I(t)|^2 dt
  <=27B_0^2+54pi ell B_0^2 U+(243pi ell/(8L^2 U))B_0^2
  <=200B_0^2(1+U).                                    (HF.2)
```

No derivative of a big-O term, total-variation estimate for `E_T`, or frequency-by-frequency choice of remainder has been used.

The exact von Mangoldt-to-prime conversion is

```text
P_I(t)+H_I(t)=integral_I (u/R)^(-it)/log u dpsi(u),
P_I(t)=sum_(p in I) (p/R)^(-it),
H_I(t)=sum_(p^k in I, k>=2) (1/k)(p^k/R)^(-it).
```

For `x=2R`, count possible integer bases, not only primes:

```text
|H_I(t)| <= sum_(2<=k<=log_2 x) x^(1/k)/k
         <=sqrt(x)/2+x^(1/3)log x/log 2 <=4sqrt(x).
```

The last bound follows from `max_(x>1) x^(-1/6)log x=6/e`. In particular, the contribution at `2R` has not disappeared.

Let

```text
K_I(rho,t)=integral_I (u/R)^(-it) u^(rho-1)/log u du,
r_I(t)=r_psi,I(t)-H_I(t).
```

Then

```text
A_I(t)=-sum_(|gamma|<=T) K_I(rho,t)+r_I(t),             (HF.3)
(1/U) integral_U^(2U)|r_I(t)|^2 dt
  <=400B_0^2(1+U)+64R.                                (HF.4)
```

For `sqrt(R)<=U<=R`, this is `O(R)` with an absolute constant. More precisely, summing (HF.2) with weight `1/t` over disjoint doubling bands gives `O(B_0^2 R)` for `r_psi`; the simple prime-power estimate costs `O(R L)` over the whole high interval.

Writing `u=R exp s` preserves the `R^rho` phase in `K`. A direct integral bound and one integration by parts in `s`, using `L+s>=2L/3` and `0<beta<1`, give

```text
|K_I(rho,t)| <= 16 R^beta/[L(1+|gamma-t|)].             (HF.5)
```

For completeness, the smooth factor `exp(beta s)/(L+s)` is at most `3/L`; its endpoint magnitudes and integral of its derivative are bounded by an absolute multiple less than `10/L`. Combining this off-resonance estimate with the direct `3ell/L` estimate gives the displayed constant 16. There is no singular bound at `gamma=t`.

#### HF2. Resonant Zeros, Remote Zeros And The Entire Band Sum

Use `U_j=2^j sqrt(R)` and disjoint `J_j=[U_j,min(2U_j,R)]`, stopping once the right endpoint is `R`. There are `O(L)` bands; using estimates on `[U_j,2U_j]` only enlarges a last partial band. For one such `U`, define

```text
G_U={rho: U/2<=gamma<=4U},
S_2(U)=sum_(rho in G_U) R^(2beta).
```

All these zeros are within the truncation since `4U<=4R<=R^2` for `R>=8`. The local zero count, including multiplicities, yields uniformly for `U<=t<=2U`

```text
sum_(G_U) 1/(1+|gamma-t|) << L^2,
integral_U^(2U) dt/(1+|gamma-t|) << L.
```

Weighted Cauchy-Schwarz applied to (HF.5) therefore gives

```text
(1/U) integral_U^(2U) |sum_(G_U) K_I(rho,t)|^2 dt
  << (L/U) S_2(U).                                   (HF.6)
```

The zeros with `beta<=1/2` contribute at most `O(R U L)` to `S_2`. Layer-cake summation for the others and (HF.D1) give

```text
S_2(U)/U <= C R L
  + C_delta L R^(2delta) integral_(1/2)^b
                      R^(2s) U^(d(s)-1) ds.           (HF.7)
```

Constants arising from `4U` and finite small heights are uniform. Because `d(s)<=1` and `U>=sqrt(R)`, the integrand is at most `R^(kappa(s))`. On the two subranges,

```text
kappa'(s)=2-3/[2(2-s)^2],
kappa'(s)=2-3/(3s-1)^2,
```

respectively. Both are at least `2/25`; `kappa` is continuous at `3/4`. Consequently,

```text
integral_(1/2)^b R^(kappa(s)) ds
  <=25 R^(kappa(b))/(2L).
```

Since `kappa(b)>=1`, (HF.6)-(HF.7) bound the resonant normalized band energy by

```text
C_delta R^(kappa(b)+2delta) L^2.                      (HF.8)
```

Now include EVERY remote zero through `T`, including negative ordinates and small positive ordinates. Put `W_1(V)=sum_(0<|gamma|<=V)R^beta`. There is no real nontrivial zeta zero: the alternating eta series is positive on real `s>0`, and `1-2^(1-s)` is nonzero on `0<s<1`. For `sqrt(R)<=V<=2T`, ordinary zero counting, layer cake and (HF.D1) yield

```text
W_1(V)/V <= C sqrt(R) log(2V)
  + C_delta L R^(2delta) integral_(1/2)^b
                       R^s V^(d(s)-1) ds
  <= C_delta R^(g_b+2delta) L.                        (HF.9)
```

The last estimate uses `V>=sqrt(R)` and `V<=2(R^2+1)`. The constants absorb the fixed endpoint factor. The low remote ordinates have `|gamma-t|>=U/2`; the high remote ordinates have `|gamma-t|>=|gamma|/2`. Use (HF.9) for `V=4U` and then for a doubling partition through `T`. The `1/L` in (HF.5) cancels the factor `L` in (HF.9), and `O(L)` height groups give

```text
|sum_(|gamma|<=T, rho notin G_U) K_I(rho,t)|
  <= C_delta R^(g_b+2delta) L.                        (HF.10)
```

There is no omitted infinite tail: it is part of the single exact `E_T` already paid in HF1. On `[1/2,3/4]`, `s+(d(s)-1)/2` is increasing; on `[3/4,7/8]` it is decreasing. Hence

```text
g_b<=11/20,
2g_b<=kappa(b),
g_b=11/20 if b>=3/4.                                 (HF.11)
```

The second inequality follows pointwise from `kappa(s)-2[s+(d(s)-1)/2]=(1-d(s))/2>=0`, then from monotonicity of `kappa`.

Combine resonant, remote and residual terms by `|v_1+v_2+v_3|^2<=3 sum |v_i|^2`. This retains their influence with only a stated constant loss. On a band `dt/t<=dt/U`; summing (HF.4), (HF.8), and (HF.10) over `O(L)` bands gives the explicit budget

```text
E_I := integral_(sqrt(R))^R |A_I(t)|^2 dt/t
 <= C_delta [(R^(kappa(b)+2delta)+R^(2g_b+4delta))L^3
              + R L].                               (HF.12)
```

For any `epsilon>0`, choose `delta=min(epsilon,1)/8`. Absorb `L^3` into `C_epsilon R^(min(epsilon,1)/2)` and use (HF.11). This proves the first HF2 inequality. Cauchy-Schwarz with the SAME positive measure `dt/t` gives

```text
integral_(sqrt(R))^R |A_R B_R| dt/t <= sqrt(E_- E_+),
|H_R(eta)| <= (1/pi)sqrt(E_- E_+).                     (HF.13)
```

The phase and nonconjugated product were retained until this upper bound. The theorem is uniform in all allowed `eta`; it does not rely on cancellation accidentally seen in a plot.

### F. Quantitative Comparison

```text
kappa(1/2)=1,
kappa(3/4)=13/10,
kappa(7/8)=71/52,
17/12-71/52=2/39.
```

The existing native `N_*>=1` implies `49/64<=b_*<7/8`, so `g_(b_*)=11/20`. The derivative lower bound additionally yields

```text
kappa(b_*) <= 71/52-7/(800 N_*).
```

This is a consumer improvement from the existing boundary, not a new zero-free region. Taking the fixed `epsilon=1/104` proves `O(R^(11/8))` for the complete high-frequency contribution, even if the native strict margin is ignored. Yesterday's middle band alone required exponent `17/12+epsilon`; the new bound pays the former middle band and the previously unpaid interval above it together.

The required canonical scale is `R log R`. Even the coarse high-frequency exponent `71/52` exceeds 1 by `19/52`. No logarithm is being called an absolute constant: the pre-absorption budget is (HF.12), with `O(L)` frequency bands and `O(L)` remote-height groups. The sharp-boundary cost below is `O(R/L)`, smaller than the target scale. Finite roots `2<=R<8` are not part of the new theorem; the exact source identity still applies there, and no global conclusion is manufactured by absorbing a missing infinite estimate into finitely many cases.

### G. Original-Carrier Bridge

#### HF3. Sharp Nonlinear Source And The Full Wheel Return

Use the credited SC cubic spline

```text
b(w)=1-6w^2+6|w|^3       if |w|<=1/2,
     2(1-|w|)^3          if 1/2<=|w|<=1,
     0                   otherwise.
```

It is the Fourier transform of the normalized nonnegative kernel

```text
K_R(s)=(3R/(8pi)) sinc(Rs/4)^4,  sinc(v)=sin(v)/v,
W_R(s)=integral_(-infinity)^s K_R(v) dv.
```

Define the genuine sharp prime-source quadratic term

```text
Q_R^prime=integral_(I_- x I_+) 1_(uv<=X) dnu(u)dnu(v),
L_R^freq=A_R(0)B_R(0)/2
  +(1/pi) integral_0^(sqrt(R)) b(t/R)
       Im(exp(it a_R)A_R(t)B_R(t)) dt/t.
```

This is not the frozen-Mobius statistic denoted `Q` in other campaigns. The SC finite-band identity and its sharp-cutoff estimate give

```text
Q_R^prime=L_R^freq+H_R(b(t/R))+e_R,
|e_R|<=6144 R/L.                                     (HF.14)
```

The constant-frequency term is NOT zero. At `t=0` the sine numerator is `O(t)` because the measures are finite with compact logarithmic support; there is no exchange of separately divergent complex integrals.

A short independent boundary check at the selected smoothing scale: for the total-variation majorant `dm=dpi+du/log u`, the interval sieve and endpoint admission give `m(I_-)<=4R/L`, `m(I_+)<=4R/L`. For `0<=eta<=1`, fixing `u` leaves a clipped interval of length at most `6R eta`, at most `6R eta+1` integer sites and continuous mass at most `3R eta`. Therefore the two-variable logarithmic strip has mass at most `40(R/L)(1+R eta)`; for `eta>1` the total mass bound implies the same inequality. The kernel tail is at most `min(1/2,32/(pi R^3|s|^3))`. The central strip of width `1/R` and successive doubling annuli cost less than `2048R/L`, hence certainly the inherited `6144R/L`. The equality atoms are counted in that error, not dropped. This check validates the reused SC allowance; the constant improvement is not claimed as new research progress.

HF2 now proves the joined estimate

```text
|Q_R^prime-L_R^freq|
 <= C_epsilon R^(kappa(b_*)+epsilon)+6144 R/L.         (HF.15)
```

Restore the original owner rows, including all lower owners. With `P_(p-1)=product_(q<p)q`, let

```text
B_R(p)=-sum_(e|P_(p-1)) mu(e) fract(X/(pe))
      =Phi(X/p,p-1)-(X/p)delta(p-1),
F_R=sum_(p<R) B_R(p),
n_R=# {primes p in I_-},
E_R^wheel=sum_(p in I_-) delta(p-1)/p,
F_R^other=sum_(p<R/2)B_R(p).
```

Here `Phi(v,p-1)` counts positive integers `m<=v` with no prime factor less than `p`, including `m=1`. For every actual `p in I_-` and `R>=8`, `p^3>X`. Thus a surviving cofactor is 1 or a prime; its historical primes from `p` to `R-1` contribute exactly `n_R(n_R+3)/2` after summing owners. The remaining prime cofactor lies in `I_+` and satisfies `pq<=X`. This is the credited Owner FW/CT physical decomposition, not a new theorem merely because it is written here.

For `a,b in {L,nu}`, define `I_ab` as the sharp integral over `I_- x I_+`, `uv<=X`, with `dL(u)=du/log u` and the indicated measures in the two positions. Set

```text
C_R^rest=F_R^other-D_R+n_R(n_R+3)/2-X E_R^wheel+I_LL,
V_R=C_R^rest+I_Lnu+I_nuL+L_R^freq.
```

The EXACT complete return is

```text
Z_R=C_R^rest+I_Lnu+I_nuL+L_R^freq+H_R(b)+e_R
   =V_R+H_R(b)+e_R.                                  (HF.16)
```

Both linear terms, the constant frequency, all low frequencies, lower owners, historical unit/square/triangle terms, and original Euler/reference compensation are present. If this expression is squared, it contains all three squares and all three doubled pairwise products of `V_R,H_R,e_R`; none is discarded. This run does NOT bound `V_R`, nor cancellation between `V_R` and `H_R`. Even an `O(R log R)` estimate for `V_R` alone would not complete the target from (HF.15). An assumed full bound on the retained sum would just restate the RH-equivalent missing conclusion.

#### HF4. A More Focused Signed Spectral Remainder

The proof also localizes the unpaid part of the high-frequency sector. On each `J_j`, set

```text
S_(I,j)(t)=sum_(rho in G_(U_j)) K_I(rho,t),
A_I(t)=-S_(I,j)(t)+r_(I,j)(t),
r_(I,j)=r_I-sum_(remote zeros through T)K_I.
```

For the existing `b_*`, (HF.4), (HF.10) and `g_(b_*)=11/20` imply, for every `epsilon>0`,

```text
sum_j integral_(J_j) |r_(I,j)|^2 dt/t
  <= C_epsilon R^(11/10+epsilon),
sum_j integral_(J_j) |S_(I,j)|^2 dt/t
  <= C_epsilon R^(71/52+epsilon).
```

Define a finite signed statistic of the ACTUAL zeros, with multiplicity and their actual phases:

```text
R_R^spec=(1/pi) sum_j integral_(J_j) b(t/R)
  Im(exp(it a_R) S_(I_-,j)(t) S_(I_+,j)(t)) dt/t.
```

Expansion of `(-S_-+r_-)(-S_++r_+)` retains BOTH mixed orientations and `r_-r_+`. Cauchy-Schwarz on the disjoint-band union gives

```text
|H_R(b)-R_R^spec|
 <= C_epsilon R^(641/520+epsilon),
641/520=(71/52+11/10)/2.                              (HF.17)
```

The smaller `r_-r_+` cost is included. This is a genuine quantified localization, not a claim that any of those terms vanish. Its error is still larger than `R log R`.

### H. Falsification And Circularity Review

#### HF5. Two Method-Specific Negative Controls

**A bounded spatial remainder does not give a uniformly small pointwise frequency error.** For `R>=64`, let `U=2pi floor(R ell/(2pi))/ell`, so `R/2<=U<=R`, and on `0<=s<=ell` use the synthetic smooth remainder

```text
E_R(R exp s)=(L+s) cos(U s).
```

Its magnitude is at most `L+ell=O(L)`. At `t=U`, the endpoint term in (HF.1) vanishes, and

```text
r_psi(U)=iU ell/2+integral_0^ell cos(Us)exp(-iUs)/(L+s) ds,
|r_psi(U)|>=U ell/2-ell/L.
```

Therefore the generic inference `|E_T|=O(L) => r_psi(t)=O(sqrt(R)) for all t<=R` is REFUTED. This is not asserted to be the actual `psi` remainder. It explains precisely why HF1 uses an averaged bound, whose `O(U)` normalized mean square is consistent with this example.

**Zero counting and a boundary above `3/4` alone cannot force an RH-scale unsigned energy.** Consider one synthetic zero `rho=b+i(3/2)sqrt(R)` with `3/4<b<=7/8`. For `|t-(3/2)sqrt(R)|<=1/4`, removing the unit phase `R^(i gamma)` from `K_(I_+)` leaves real part at least `R^b ell/(2L)`. This follows directly from `cos((gamma-t)s)>=cos(ell/4)`, `exp(bs)>=1`, and `L+s<=4L/3`. Thus

```text
integral_(gamma-1/4)^(gamma+1/4) |K_(I_+)(rho,t)|^2 dt/t
 >= ell^2 R^(2b-1/2)/(16L^2).                         (HF.18)
```

For `b>3/4`, this exceeds `R log R` by an unbounded power factor. A conjugate/reflected quartet may be added without violating the stated upper density or local-count inequalities. This is a model population for testing the sufficiency of those inequalities, not an alleged actual zeta zero, not a claim that the same finite population is fixed across all `R`, and not a lower bound on the genuine SIGNED `H_R`. It is a limitation of this magnitude-energy proof mechanism, not a disproof of the target or of signed zero-pair cancellation.

Other circularity checks: no RH assumption is used to get the native `b_*`; no new bound is inferred from a conditional Lean consumer; no zero-density theorem is transferred to primes without the explicit formula and prime-power adapter; no average prime density replaces an indicator; no covariance is removed before its cost is displayed; no fixed-parameter density constant is presumed uniform in a growing parameter. The single truncation height makes all Fourier transforms representations of one common remainder.

#### HF6. Executed Finite Checks

The exact executed program is included below. SHA256: `89e35df847ecbdf447e4e350ed4c0e5a543ed88d4d0701d49090331ffcd86676`. Runtime actually measured: Python **3.12.14**, NumPy **2.3.5**. Syntax validation and all registered assertions passed. No local Lean was run.

| Check | Domain/result |
| --- | --- |
| Exact rational exponent inequalities | 13,600 parameter cases, denominator at most 64; continuum proof is E, not this grid |
| Exact full owner/source bridge | 44 roots: all 8 through 48, then 64,127,257 |
| Independent prime-power coefficient reconstructions | 3,148 integer checks, factorization versus explicit powers; primality additionally checked by trial division |
| Exact divisor-cube/virtual/Legendre checks | R=2,3,8,9,10,11,12,13,14,15,16 |
| Genuine transform diagnostics | R=8,11,12,16,31,64,127,257; quadrature orders 128 and 256, spline break split explicitly |
| Synthetic remainder identity and bound | R=64,128,256,512; independent direct derivative integration versus integration by parts |
| Synthetic one-zero energy lower bound | R=64,256,1024,65536 |
| Wrong conjugation negative control | Nonconjugated and Hermitian products differ on an exact complex test |

Important exact boundaries: at `R=8`, physical/virtual/full wheel values are `3/5,-6/5,-3/5`; at `R=14`, physical `d=X=195` has `mu=-1`; at `R=12`, the equality atom `(11,13)` lies on `pq=X`; primes `R=11,127,257` are included in `I_+`; at `R=8,16,32`, the `2R` prime-power coefficients are `1/4,1/5,1/6`.

Largest floating discrepancies: quadrature refinement `3.864e-14`; dyadic versus whole high integral `3.320e-14`; whole-frequency versus low-plus-high `8.660e-15`; synthetic Stieltjes identity `1.696e-12`. At `R=257`, the diagnostic signed high integral is approximately `0.5837179035991069`. Synthetic remainder mean-square divided by `U` ranges from `0.5067581` to `0.5376369`; single-zero energy divided by its proved lower bound ranges from `8.48869` to `9.42340`.

These floating computations are NOT interval certificates, numerical zeta-zero computations, independent mathematical review, or all-scale evidence. One first-pass output serialization failed because a diagnostic array shadowed a boundary-summary name; no mathematical assertion failed. Renaming that variable fixed output. Splitting quadrature at the known spline break improved numerical refinement without changing the registered source or theorem. No large unchanged prime census was rerun.

### I. Conceptual Interpretation

The useful new control comes from keeping frequency errors tied to the same spatial function. Pointwise error accounting loses a factor of the band height; Plancherel recovers it. The selected classical density theorem then turns growing frequency into a favorable factor `U^(d(s)-1)`. This is why joining every higher band is possible instead of leaving each as a fresh unpaid hypothesis.

It does not reveal the final RH-scale cancellation. HF4 identifies an actual signed resonant-pair statistic where phases `R^(i(gamma+gamma'))` and the unequal spatial intervals still matter. A proof using only counts and magnitudes cannot be expected to supply the required cancellation, as HF5 illustrates. The low-frequency and physical-owner pieces may also participate in the final cancellation; the full return keeps them available.

Today's Owner HM reciprocal-prime profile and its complete covariance remain compatible with this conclusion. Its forced cross-fibre cancellation is not silently transferred into `R_R^spec`. The two carriers require an exact quantitative bridge before one can pay the other.

### J. Specialist Handoffs

These are asynchronous report requests only; no other agent is launched or claimed to have acted.

| Recipient | Precise request |
| --- | --- |
| Adversarial Referee | Independently review HF1's common-cutoff Stieltjes/Plancherel lemma, the uniform density mesh, remote-height accounting and HF2 exponent before accepting HF1-HF4. Check all endpoint conventions and HF3's source return. ZD's prior review remains pending; this report does not supply independent acceptance of its own proof. |
| Owner Payment | Compare the exact HM balanced-prime row with `V_R` in (HF.16). Identify a provable relation to this SAME low-frequency/linear compensation, retaining original Euler allocations and both orientations. Do not replace the full adaptive prefix by a fixed q-cut. |
| Finite Wheel & Incidence | Seek an incidence restriction on the complete `uv<=X` carrier that translates into a signed bound for the product transform or its low-frequency complement. RF's reflected-product subset is not yet full coverage. State any omitted complement explicitly. |
| Prime Census | A changed, optional experiment is to compute signed high-band contributions on the declared A/B prime carrier, and compare them with `V_R`, the two linear terms and the sharp error separately. Preserve `A B`, not `A conjugate(B)`. Scale by `R log R` and `R^(71/52)`; report cancellation ratios, endpoint atoms, precision/refinement and what population is complete. This run's eight small roots are validation, not evidence of an asymptotic. |
| Lean Verification | After independent acceptance, HF1 can be formalized as an abstract bounded-remainder Fourier lemma with explicit endpoint terms; HF2 additionally needs actual classical zero-density and explicit-formula imports. Do not encode the desired high-band estimate as an axiom or silently treat those imports as already formalized. No source/PR work is authorized to this analytic run. |
| Research Coordinator | The assigned joined high-frequency/sharp-source estimate is now supplied at paper level, improving the single-band exponent but not reaching the full target. Prioritize independent review and a genuine signed resonant-pair or complete low/physical mechanism. No strategic campaign change is requested or silently made. |

### K. First Independently Missing Analytic Theorem

For the selected high-frequency mechanism, a smaller concrete step than an RH-scale whole-source bound is:

```text
OPEN-HF-SIGNED-RESONANCE-5/4:
forall epsilon>0 exists C_epsilon forall integers R>=8,
|R_R^spec|<=C_epsilon R^(5/4+epsilon),
```

where `R_R^spec` is exactly the finite actual-zero, nonconjugated, disjoint-band statistic of G, with the actual phases and multiplicities. This statement is OPEN, not an assumption used in HF1-HF4 and not an established conjecture about random zeros. It requires additional signed information that the proved counting estimates do not provide.

Because `5/4-641/520=9/520>0`, HF4 would transfer it to the entire high-frequency source at exponent `5/4+epsilon`, an actual further improvement. This is a proposed proper-component research target, not a proved equivalence to RH and not a sufficient theorem for the whole finite wheel. A promising proof would need to identify and bound the precise coherent zero-pair configurations, or extract cancellation in the signed kernel, without assuming unproved pair correlation.

The complete arithmetic objective remains (HF.16) with ONE uniform `C R log R` bound. This report does not relabel that final sum as an independent supporting lemma. Reducing HF4's remainder further and controlling the low/physical complement are separate obligations.

### L. Next-Run Resume Capsule

**Resume mathematics:** retain HF1's one common `T`, full prime-power adapter and one-sided endpoint values. HF2's auditable pre-epsilon budget is (HF.12); its external density input is (HF.D1), with proved compact uniformity. HF3 restores every original term in (HF.16). HF4 isolates the actual signed resonant statistic with explicit remainder exponent `641/520`. HF5 refutes only two generic method extensions, not genuine arithmetic. All new paper claims remain SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED.

**Highest-value next step:** obtain independent review of the complete HF proof, then investigate the signed resonant statistic in K or a genuinely quantitative connection to the complete low/physical compensation. Do not rerun the same grid, small-root diagnostics, literature lookup, or the already paid high-band derivation without a changed question.

#### Continuity And Source Freshness

Scheduled invocation: **2026-11-10 01:04:01 EST**, `America/New_York`. Intake report-branch tree: `679f2198c7d399e46d149c269136e3e5a3da5b3e`. Both today and the preceding New York calendar day were retrieved. At intake and the prepublication preparation refresh, today's only upstream report was Owner HM. `TODAY=PENDING` for Coordinator, Wheel, Census, Referee and Lean; `YESTERDAY=CARRY_FORWARD`. Own earlier-today report was absent at intake and became the verified early checkpoint. No missing handoff is invented. November 9 Coordinator AM/PM have identical blobs; their common content was read once.

| Continuity material | Blob SHA |
| --- | --- |
| Nov 9 Coordinator AM/PM | `6fba43130391ad4a606aa3809c20f344d668c709` |
| Nov 9 Owner | `643e8a004d9d8e0be102b03e2f79bb3b217ae916` |
| Nov 9 Analytic | `d1d0d86d444b9c447cf6acf4bd18fdcaf02e56a3` |
| Nov 9 Wheel | `0624246d03b19cf76c01e186b7d868a248d896ef` |
| Nov 9 Census | `8c927cc6c323533ba1cfd369404b25aa4f9cef91` |
| Nov 9 Referee | `a5d0192eb31c0efb3767187a7752f1a0d07f8534` |
| Nov 9 Lean | `8b60c6136ac151774be2db0aee8f543f286b53aa` |
| Nov 10 Owner HM | `2bed3da8ed4ddd49c0708378a1c3da5b4883cb54` |
| External handoffs | `038018145c0fddb2f6306c0712373adf9cd1ea52` |

Relevant latest handoffs consumed: Coordinator CD joined-source request and critical-cutoff no-gos; Owner CF and today's HM; own SC/MB/ZD; Wheel RF; Census NC; Referee AP; Lean's CF2 implementation evidence. Original claim IDs and evidence scopes are retained. The external inbox has no entry after October 18. Its original-source, endpoint, normalization and target-equivalence safeguards remain relevant, not its obsolete campaign routing.

Main and the only open PR were refreshed during report preparation: main remains `7c7e0a4f54ee2972d3993abc42e5c7c4e1b405c9`; #1127 remains open, non-draft, at `866b3d2121309cdd854f9d64e2a6adbbc708ef9b`. No source mutation was detected. The current authority takes precedence over older local role-contract snapshots and historical theorem/PR routing.

#### Exact CI Evidence And Limits

The following were inspected through GitHub, not inferred from merge labels or run locally:

| Source claim | Exact tested head and relevant evidence | Scope |
| --- | --- | --- |
| Existing native zero/window boundary, #1119 | Head `77ee815846d6d534c866f0752aa33b84c385610a`; [run 42552018910](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42552018910), job `128949473700` | Log shows the quoted near-uniform endpoint has only `propext, Classical.choice, Quot.sound`; dependency closure 35375; five endpoint audits, warning-fatal source/type/dependency checks successful. Relevant main blobs match. |
| Complete-wheel identities, #1122 | Head `c53e9cf234500aea2605fd2557e638995f380407`; [run 42561949462](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42561949462), job `128980092032` | Two complete-wheel theorems show only the three standard axioms; compiled 1, cached 9; warning-fatal checks successful. Identity certification does not certify a discrepancy bound. |
| Complete cofactor positivity, open #1127 | Head `866b3d2121309cdd854f9d64e2a6adbbc708ef9b`; 12 successful exact-head workflow records; [dedicated run 42743502306](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42743502306), job `129590019152` | Successful proof/type/standard-axiom guards; `finiteWheel_primeFibre_sum_nonneg` dependency closure 828; compiled 2, cached 10. Sharp `3z delta(z)^2>=1` and positive complete fibres for `R>=47`; unmerged and not an estimate for `Z_R`. |

Recent human merges were checked: #1126 is current main and has 16 successful exact-head workflows at `e8969ad76d4c5694273cefc934316fc528c56648`; its finite-AC iteration and zero-log consumers remain conditional on their unpaid hypotheses. #1125's merged metadata does not replace the missing dedicated successful proof evidence noted in handoffs. #1124 is root-admission infrastructure, not analytic payment. None of these is a newly proved claim of this run.

The early checkpoint was actually published at commit `4ef55c323b9c5a1d6774e361ca72ba540edafdd9`, blob `ecb2e8c84a235166597866bfb1602f969ccd3876`, and read back exactly at that immutable commit. The initial Git clone transport returned HTTP 403; authenticated source/report reads worked. Only the owned daily report is written remotely. No Lean execution, proof-source edit, other-report edit, PR/issue creation, branch creation, workflow action, merge, permission/schedule change or agent launch occurred.

Final publication is to be recorded only after successful write and immutable readback. The complete executed verifier and the original checkpoint follow for reproducibility and preservation of history.

## Reproducibility Appendix - HF6

The exact executed script follows. Its output is reproduced after it. Floating arithmetic is diagnostic only.

```python
"""HF validation: exact arithmetic first; all quadrature is diagnostic only."""

from fractions import Fraction as F
from functools import lru_cache
from math import isqrt, log, pi, sqrt
import json
import platform
import numpy as np


def trial_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def sieve(n):
    spf = list(range(n + 1))
    for p in range(2, isqrt(n) + 1):
        if spf[p] == p:
            for k in range(p * p, n + 1, p):
                if spf[k] == k:
                    spf[k] = p
    return spf, [p for p in range(2, n + 1) if spf[p] == p]


def density_exponent(s):
    return 3 * (1 - s) / ((2 - s) if s <= F(3, 4) else (3 * s - 1))


def kappa(s):
    return 2 * s - F(1, 2) + density_exponent(s) / 2


assert kappa(F(7, 8)) == F(71, 52)
assert F(17, 12) - F(71, 52) == F(2, 39)
assert F(71, 52) + F(1, 104) == F(11, 8)
assert kappa(F(3, 4)) == F(13, 10)
assert 2 - 3 / (3 * F(3, 4) - 1) ** 2 == F(2, 25)
assert 2 * F(49, 64) - F(1, 2) == F(33, 32)
assert (F(71, 52) + F(11, 10)) / 2 == F(641, 520)
assert F(5, 4) - F(641, 520) == F(9, 520)

exponent_checks = 0
for den in range(2, 65):
    for num in range(den // 2, den + 1):
        s = F(num, den)
        if not F(1, 2) <= s <= F(7, 8):
            continue
        d = density_exponent(s)
        derivative = (2 - F(3, 2) / (2 - s) ** 2) if s <= F(3, 4) else (2 - 3 / (3 * s - 1) ** 2)
        g = s + (d - 1) / 2
        assert 0 <= d <= 1
        assert derivative >= F(2, 25)
        assert 2 * g <= kappa(s) <= F(71, 52)
        assert g <= F(11, 20)
        for j in range(16, 33):
            theta = F(j, 32)
            assert 2 * s + theta * (d - 1) <= kappa(s)
            exponent_checks += 1

roots = list(range(8, 49)) + [64, 127, 257]
spf, primes = sieve(max(roots) ** 2)
exact_bridges = 0
adapter_coefficients = 0
boundary = []
for R in roots:
    X = R * R - 1
    small = [p for p in primes if p < R]
    delta, owner, weights = F(1), {}, {}
    for p in small:
        weights[p] = delta / p
        # Direct survivor count is independent of a divisor-cube expansion.
        rough = 1 + sum(spf[a] >= p for a in range(2, X // p + 1))
        owner[p] = rough - F(X, p) * delta
        delta *= F(p - 1, p)
    minus = [p for p in small if 2 * p >= R]
    plus = [q for q in primes if R <= q <= 2 * R]
    cross = sum(p * q <= X for p in minus for q in plus)
    other = sum((owner[p] for p in small if 2 * p < R), F(0))
    ew = sum((weights[p] for p in minus), F(0))
    n = len(minus)
    full = sum(owner.values(), F(0))
    assert full == other + F(n * (n + 3), 2) + cross - X * ew
    pi_x = sum(p <= X for p in primes)
    reference = F(355, 113)
    D = X * delta + len(small) - 1 - reference
    assert full - D == reference - pi_x
    exact_bridges += 1

    from_powers = {}
    for p in primes:
        if p > 2 * R:
            break
        power, k = p, 1
        while power <= 2 * R:
            from_powers[power] = F(1, k)
            power *= p
            k += 1
    for a in range(2, 2 * R + 1):
        p = spf[a]
        t, k = a, 0
        while t % p == 0:
            t //= p
            k += 1
        expected = F(1, k) if t == 1 else F(0)
        assert expected == from_powers.get(a, F(0))
        assert (spf[a] == a) == trial_prime(a)
        adapter_coefficients += 1
    if R in [8, 11, 12, 14, 16, 32, 127, 257]:
        boundary.append({"R": R, "R_prime_in_plus": R in plus,
                         "wall_pairs": [[p, q] for p in minus for q in plus if p * q == X],
                         "two_R_power_weight": str(from_powers.get(2 * R, F(0)))})

cube_checks = []
for R in [2, 3] + list(range(8, 17)):
    X = R * R - 1
    ps = [p for p in range(2, R) if trial_prime(p)]
    cube = [(1, 1)]
    for p in ps:
        cube += [(p * d, -mu) for d, mu in cube[:]]
    full = sum((mu * F(X % d, d) for d, mu in cube), F(0))
    physical = sum((mu * F(X % d, d) for d, mu in cube if d <= X), F(0))
    virtual = sum((mu * F(X, d) for d, mu in cube if d > X), F(0))
    delta = sum((F(mu, d) for d, mu in cube), F(0))
    assert full == physical + virtual
    assert full - X * delta == -sum(mu * (X // d) for d, mu in cube)
    assert sum(mu * (X // d) for d, mu in cube) == 1 + sum(trial_prime(q) for q in range(R, X + 1))
    if R == 8:
        assert (physical, virtual, full) == (F(3, 5), F(-6, 5), F(-3, 5))
    if R == 14:
        assert (195, -1) in cube
    cube_checks.append(R)


@lru_cache(maxsize=None)
def gauss(order):
    return np.polynomial.legendre.leggauss(order)


def nodes(a, b, order):
    x, w = gauss(order)
    return a + (x + 1) * (b - a) / 2, w * (b - a) / 2


def spline(w):
    w = np.abs(w)
    return np.where(w <= .5, 1 - 6*w*w + 6*w**3,
                    np.where(w < 1, 2*(1-w)**3, 0))


def transform(R, ts, side, order):
    lo, hi = (-log(2), 0) if side == '-' else (0, log(2))
    ss, ww = nodes(lo, hi, order)
    rr = np.exp(-1j * np.outer(ts, ss)) @ (ww * R * np.exp(ss) / (log(R) + ss))
    ps = [p for p in range(2, 2*R+1) if trial_prime(p) and
          ((R <= 2*p and p < R) if side == '-' else (R <= p <= 2*R))]
    pp = np.exp(-1j * np.outer(ts, np.log(np.array(ps) / R))).sum(axis=1)
    return pp - rr


def band(R, a, b, order):
    if a < R / 2 < b:
        return band(R, a, R / 2, order) + band(R, R / 2, b, order)
    ts, ww = nodes(a, b, order)
    aa, bb = transform(R, ts, '-', order), transform(R, ts, '+', order)
    val = np.imag(np.exp(1j * ts * np.log1p(-1 / R**2)) * aa * bb)
    return float(np.sum(ww * spline(ts/R) * val / ts) / pi)


diagnostics = []
for R in [8, 11, 12, 16, 31, 64, 127, 257]:
    U = sqrt(R)
    high128, high256 = band(R, U, R, 128), band(R, U, R, 256)
    pieces = []
    left = U
    while left < R:
        right = min(2 * left, R)
        pieces.append(band(R, left, right, 128))
        left = right
    low = band(R, 0, U, 256)
    whole = band(R, 0, R, 256)
    assert abs(high128 - high256) < 1e-8 * max(1, abs(high256))
    assert abs(sum(pieces) - high256) < 1e-8 * max(1, abs(high256))
    assert abs(whole - low - high256) < 1e-8 * max(1, abs(whole))
    diagnostics.append({"R": R, "high": high256,
                        "dyadic_difference": sum(pieces) - high256,
                        "refinement_difference": high128 - high256,
                        "full_split_difference": whole-low-high256})


def exp_integral(v):
    ell = log(2)
    return ell * np.exp(-1j * v * ell/2) * np.sinc(v * ell/(2*pi))


residual_controls = []
for R in [64, 128, 256, 512]:
    L, ell = log(R), log(2)
    U = 2*pi*int(R*ell/(2*pi))/ell
    ts, ww = nodes(U, 2*U, 512)
    ss, sw = nodes(0, ell, 512)
    fhat = (exp_integral(ts-U) + exp_integral(ts+U))/2
    ghat = np.exp(-1j*np.outer(ts, ss)) @ (sw*np.cos(U*ss)/(L+ss))
    endpoint_term = np.exp(-1j*ts*ell)-1
    residual = endpoint_term + 1j*ts*fhat + ghat
    direct = np.exp(-1j*np.outer(ts, ss)) @ (sw*(np.cos(U*ss)/(L+ss)-U*np.sin(U*ss)))
    assert np.max(np.abs(residual-direct)) < 1e-8
    g0 = np.sum(sw*np.cos(U*ss)*np.exp(-1j*U*ss)/(L+ss))
    point = 1j*U*ell/2 + g0
    assert abs(point) >= U*ell/2-ell/L
    mean_square = float(np.sum(ww*np.abs(residual)**2)/U)
    B = (L+ell)/L
    assert mean_square <= 200*B*B*(1+U)
    residual_controls.append({"R": R, "U": U, "point_over_U": abs(point)/U,
                              "mean_square_over_U": mean_square/U,
                              "ibp_difference": float(np.max(np.abs(residual-direct)))})

spectral_controls = []
for R in [64, 256, 1024, 65536]:
    L, ell, U, beta = log(R), log(2), sqrt(R), 7/8
    ts, tw = nodes(1.5*U-.25, 1.5*U+.25, 128)
    ss, sw = nodes(0, ell, 128)
    kernel = R**beta * (np.exp(1j*np.outer(1.5*U-ts, ss)) @ (sw*np.exp(beta*ss)/(L+ss)))
    energy = float(np.sum(tw*np.abs(kernel)**2/ts))
    lower = ell**2*R**(2*beta-.5)/(16*L*L)
    assert energy >= lower
    spectral_controls.append({"R": R, "energy_over_proved_lower": energy/lower})

assert ((1+2j)*(3+4j)).imag != ((1+2j)*(3-4j)).imag
print(json.dumps({
    "status": "PASS", "runtime": platform.python_version(), "numpy": np.__version__,
    "exact_exponent_cases": exponent_checks,
    "exact_owner_bridges": exact_bridges,
    "exact_prime_power_coefficients": adapter_coefficients,
    "exact_cube_roots": cube_checks, "boundary_controls": boundary,
    "floating_status": "DIAGNOSTIC_ONLY; not interval, asymptotic, or Lean certification",
    "genuine_high_frequency_checks": diagnostics,
    "synthetic_residual_controls": residual_controls,
    "synthetic_single_zero_controls": spectral_controls,
    "scope": "No alleged numerical zeta zeros or uniform prime discrepancy proof."
}, indent=2))
```

### Recorded Output

```json
{
  "status": "PASS",
  "runtime": "3.12.14",
  "numpy": "2.3.5",
  "exact_exponent_cases": 13600,
  "exact_owner_bridges": 44,
  "exact_prime_power_coefficients": 3148,
  "exact_cube_roots": [
    2,
    3,
    8,
    9,
    10,
    11,
    12,
    13,
    14,
    15,
    16
  ],
  "boundary_controls": [
    {
      "R": 8,
      "R_prime_in_plus": false,
      "wall_pairs": [],
      "two_R_power_weight": "1/4"
    },
    {
      "R": 11,
      "R_prime_in_plus": true,
      "wall_pairs": [],
      "two_R_power_weight": "0"
    },
    {
      "R": 12,
      "R_prime_in_plus": false,
      "wall_pairs": [
        [
          11,
          13
        ]
      ],
      "two_R_power_weight": "0"
    },
    {
      "R": 14,
      "R_prime_in_plus": false,
      "wall_pairs": [],
      "two_R_power_weight": "0"
    },
    {
      "R": 16,
      "R_prime_in_plus": false,
      "wall_pairs": [],
      "two_R_power_weight": "1/5"
    },
    {
      "R": 32,
      "R_prime_in_plus": false,
      "wall_pairs": [],
      "two_R_power_weight": "1/6"
    },
    {
      "R": 127,
      "R_prime_in_plus": true,
      "wall_pairs": [],
      "two_R_power_weight": "0"
    },
    {
      "R": 257,
      "R_prime_in_plus": true,
      "wall_pairs": [],
      "two_R_power_weight": "0"
    }
  ],
  "floating_status": "DIAGNOSTIC_ONLY; not interval, asymptotic, or Lean certification",
  "genuine_high_frequency_checks": [
    {
      "R": 8,
      "high": 0.005179984418422524,
      "dyadic_difference": -1.8127860323957634e-16,
      "refinement_difference": -1.6740081543176188e-16,
      "full_split_difference": -1.3877787807814457e-17
    },
    {
      "R": 11,
      "high": -0.07643847711484915,
      "dyadic_difference": 1.3461454173580023e-15,
      "refinement_difference": 1.27675647831893e-15,
      "full_split_difference": -9.71445146547012e-17
    },
    {
      "R": 12,
      "high": 0.009943335114565953,
      "dyadic_difference": -2.185751579730777e-16,
      "refinement_difference": -2.0990154059319366e-16,
      "full_split_difference": 2.6020852139652106e-17
    },
    {
      "R": 16,
      "high": 0.062371754983167445,
      "dyadic_difference": -3.677613769070831e-16,
      "refinement_difference": -3.677613769070831e-16,
      "full_split_difference": -1.3183898417423734e-16
    },
    {
      "R": 31,
      "high": -0.06827445455333778,
      "dyadic_difference": 8.43769498715119e-15,
      "refinement_difference": 7.965850201685498e-15,
      "full_split_difference": -1.3877787807814457e-17
    },
    {
      "R": 64,
      "high": -0.42835756106538847,
      "dyadic_difference": -2.0539125955565396e-15,
      "refinement_difference": 2.7755575615628914e-15,
      "full_split_difference": -1.2212453270876722e-15
    },
    {
      "R": 127,
      "high": -0.9458626241421125,
      "dyadic_difference": 3.319566843629218e-14,
      "refinement_difference": 3.47499806707674e-14,
      "full_split_difference": -8.659739592076221e-15
    },
    {
      "R": 257,
      "high": 0.5837179035991069,
      "dyadic_difference": 2.731148640577885e-14,
      "refinement_difference": 3.863576125695545e-14,
      "full_split_difference": 8.659739592076221e-15
    }
  ],
  "synthetic_residual_controls": [
    {
      "R": 64,
      "U": 63.45304198558071,
      "point_over_U": 0.34657358613406286,
      "mean_square_over_U": 0.5067581200696146,
      "ibp_difference": 1.4581349845862359e-13
    },
    {
      "R": 128,
      "U": 126.90608397116142,
      "point_over_U": 0.3465735896888298,
      "mean_square_over_U": 0.5228333595811923,
      "ibp_difference": 3.9817371397786215e-13
    },
    {
      "R": 256,
      "U": 253.81216794232284,
      "point_over_U": 0.34657359019023504,
      "mean_square_over_U": 0.5322454067293864,
      "ibp_difference": 9.073341394925289e-13
    },
    {
      "R": 512,
      "U": 507.6243358846457,
      "point_over_U": 0.34657359026559775,
      "mean_square_over_U": 0.5376368431018045,
      "ibp_difference": 1.69525299275229e-12
    }
  ],
  "synthetic_single_zero_controls": [
    {
      "R": 64,
      "energy_over_proved_lower": 8.488696863110704
    },
    {
      "R": 256,
      "energy_over_proved_lower": 8.841668533655628
    },
    {
      "R": 1024,
      "energy_over_proved_lower": 9.06644588176943
    },
    {
      "R": 65536,
      "energy_over_proved_lower": 9.423398294594698
    }
  ],
  "scope": "No alleged numerical zeta zeros or uniform prime discrepancy proof."
}
```

## Preserved Early Checkpoint

The following checkpoint is preserved verbatim as history. Its IN_PROGRESS status is superseded by the final research synthesis and subsequent verified publication receipt.

# RH | Analytic Type II - 2026-11-10

## Early Checkpoint - 20261110-analytic-1/HF

### A. Most Important Analytic Development

EXECUTION=IN_PROGRESS; mathematical result=NOT_YET_ESTABLISHED; independent review=PENDING. This run will investigate a uniform joined high-frequency estimate for the actual signed prime-minus-Li product, retaining the full finite-wheel return. It will not count another coordinate identity or the already reported middle-band bound as a new global result.

### B. Current Mathematical Objective

Scheduled invocation: 2026-11-10 01:04:01 EST, America/New_York. Main fetched at 7c7e0a4f54ee2972d3993abc42e5c7c4e1b405c9. finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1.

For integer R>=2, X=R^2-1, y=R-1, F_R=sum_(d|P_y)mu(d)fract(X/d), D_R=X*delta(y)+pi(y)-1-li(X). The certified source says F_R-D_R=li(X)-pi(X); ONE uniform C with |F_R-D_R|<=C R log R remains OPEN and RH-equivalent. All virtual d>X are compensated termwise before truncation; d=X and principal-value li are retained.

Authority blobs: AGENTS 6695522a45d67fd1e80a7cff1f98d909405036e2; contract 95566e37c8eaeb99ee680660df4f9d2e06ea5038; directive e505f35522b675c6b5b263eac73618d717346973; complete source ecb482e52deeee5e9b3853592a3ffdace662d2ff. Native zero-boundary sources read: WindowErrorClosure f629db1b2b65d6ec042ac9432397d4b6316200c6; NativeStrictMertens b33a4883e1ddb0551b0f11f062bce46680d87450. The existing b_*=7/8-7/(64*N_*) is an input, not this run's discovery.

### C. Continuity And Registered Investigation

Reporting intake head 679f2198c7d399e46d149c269136e3e5a3da5b3e. November 10 Owner HM is AVAILABLE (blob 2bed3da8ed4ddd49c0708378a1c3da5b4883cb54). TODAY=PENDING for Coordinator, Analytic, Wheel, Census, Referee and Lean at intake; YESTERDAY=CARRY_FORWARD using all seven November 9 reports at their actual evidence scopes. Coordinator AM/PM have identical blobs and their common report was read once.

Carry-forward claims: Analytic SC sharp-cutoff cost and finite-band formula; MB sieve/reference bounds; ZD proposed middle-band zero-density transfer; Coordinator CD joined-source request and critical-cutoff no-gos; Owner CF and today's HM profile; Wheel RF restricted matching; Census NC restricted pairing; Referee AP adaptive prefix; Lean #1127 density/cofactor positivity. ZD remains SELF_AUDIT / INDEPENDENT_REVIEW_PENDING, not blanket accepted. External inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 has no newer campaign handoff; its target-equivalence and first-bad scope safeguards remain applicable.

Changed question: can classical density information yield a quantitative bound for the entire interval sqrt(R)<=t<=R in the original nonconjugated signed transform, including its continuous references, rather than merely one dyadic band? Investigate a stronger applicable density input, uniform sharp explicit-formula errors, remote zeros and prime-power mean square before summing bands. Keep the low/constant frequencies, both physical linear terms, lower owners and Euler/reference compensation explicit in the return. No RH-scale premise is allowed.

Registered tests: exact exponent/range algebra; independent prime and prime-power coefficient reconstruction at small and held-out roots; finite numerical transform comparisons marked diagnostic only; synthetic zero modes as null controls for a false universal RH-scale strengthening. Do not rerun a large unchanged census.

### D-L. Work Pending And Evidence Limits

Original Lean declarations and current PR metadata were retrieved. Main includes human merges #1122, #1124, #1125, #1126; #1127 is the only open PR, non-draft, head 866b3d2121309cdd854f9d64e2a6adbbc708ef9b, with twelve successful exact-head workflow records, including dedicated run 42743502306. Its content is not on main. Dedicated proof/axiom evidence will be checked before any new certification assertion; merge metadata alone is insufficient. No local Lean execution is permitted or planned.

Only this owned report is authorized for remote writes. No source, other report, policy, branch, PR, issue, workflow, schedule or agent launch will be changed. The Git clone transport returned HTTP 403; the authenticated read connector works and source retrieval is not blocked. This checkpoint will be claimed published only after immutable readback.


## Verified Publication Receipt - 20261110-analytic-1/HF

EXECUTION=COMPLETED; substantive report publication=PUBLISHED_VERIFIED. At **2026-11-10 01:38:35 EST** (06:38:35 UTC), the complete research text, exact verifier, recorded output and preserved checkpoint were re-fetched at immutable commit `d36f0a968667da43a87e38a823b3f230b05be477`, blob `331df1515399a967795e522b16a9760ce68dab12`, and matched the submitted contents exactly. The commit file list contains only `research/agent_reports/2026-11-10/20-analytic-type-ii.md`. Main was rechecked immediately before publication at 06:38:21 UTC and remained `7c7e0a4f54ee2972d3993abc42e5c7c4e1b405c9`.

HF1-HF5 remain paper/self-audit results with INDEPENDENT_REVIEW_PENDING and NOT_FORMALIZED; HF6 retains its declared finite/diagnostic scope. The full centered finite-wheel bound and RH remain OPEN. No proof-source, other-report, PR, issue, branch, workflow, merge, schedule or agent-launch action was taken. This receipt records the already verified substantive commit; the receipt update itself is read back before the user-facing completion message.


## Scheduled Continuation Checkpoint - 20261110-analytic-2/CR

### A. Most Important Analytic Question

IN_PROGRESS / PARTIAL. No new theorem or global gain is claimed at this checkpoint. Resolve Coordinator 20261110-coordinator-0710-EST/CR2 on the literal OAI tilted HIGH source: trace every beta>=7/8 use and test whether the certified bound beta<=b_base permits a source-faithful lower-reference extension, retaining the central budget, marked 1+t/2 moment, actual coefficients, detector errors, principal and complete LOW/HIGH return. If not, identify the first unpayable inequality and its precise quantitative cost. Prior HF1-HF6 and all earlier daily findings remain intact and at their original review status.

### B. Authority, Trigger And Scope

Scheduled trigger: 2026-11-10 09:09:03 EST, America/New_York; platform RUN_ID_UNAVAILABLE. Run label 20261110-analytic-2/CR. cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1. Main=655f897e274a8ba8a2fed80ecc1fc75a0d849174. AGENTS=c9c89f01b90b526de9f3e8ea92478e36504711b6; CURRENT_PROOF_CONTRACT=95566e37c8eaeb99ee680660df4f9d2e06ea5038; new governing directive=e922d4ba9362a1ae196af8f6de88f7417f92087c. Canonical VF square von Koch bound, complete wheel bound, finite A/C and RH remain OPEN. The reported b_base=7/8-7/(64*N_pack) retains every positive exponent loss; its original theorem/dependency/CI receipt is being independently checked, not inferred from a merge label.

### C. Continuity And Registered Investigation

Read today's and yesterday's seven role reports at intake agent-reports ffbe23bc6cdfb76ddacd7a5706c95b0717a41dcf, including today's updated Owner BR1-BR6, Coordinator UB/CR1-CR2, own HF, Wheel PC, Census UC, Referee LC, and Lean's repaired DG2 evidence. All seven TODAY=AVAILABLE; prior-day findings are CARRY_FORWARD at their stated scopes. No missing run or independent review is invented. External inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 has no entry later than October 18; its source/normalization safeguards remain relevant, not its old priority wording. Open/draft PR list is empty; #1119 and #1122-#1129 relevant changes have merged, with #1125's failed-head evidence superseded only by the distinct repaired #1128 head.

Original sources retrieved: VF919TiltedHighAssembly.lean (883141e0af896d4132bfc4ffa076e2d265ece5c9), VF919NativeStrictSevenEighths.lean (efbf2780f0b453a702fb8847f2d360d8faf0fa66), VF919WindowErrorClosure.lean (f629db1b2b65d6ec042ac9432397d4b6316200c6), VF919TotalMassEndpoint.lean (827bb952c4d4311d75fd03a2470799dc10b0f7e7), and VF919WindowSaturatedLowPrincipal.lean (b7b05069ea013d83b2acaa76a8ea2ed932568930). Source-dependent mathematical work follows this checkpoint.

### D. Pending Work And Permission Boundary

Complete the baseline receipt, four-way typed source map, first-loss ledger, paid-recovery test and net-result/admission verdict. Perform a substantive derivation and challenge its strongest claim; do not rerun HF's accepted scope calculations or force a false Hecke/Mobius identification. CODIV and NYMAN remain protected alternatives, not automatic bridges. Only this owned report may be written remotely. No Lean execution/source edit, other report edit, issue/PR/branch/workflow mutation, merge, schedule change or agent launch is authorized or performed.

---

## Signed Principal-Response Recovery - 20261110-analytic-2/RD

Same scheduled invocation as the CR checkpoint: 2026-11-10 09:09:03 EST, America/New_York. Platform RUN_ID_UNAVAILABLE. This is not a new invocation and does not supersede today's earlier HF findings. Prepared after the checkpoint was published and verified at commit `5add904276b7978c99581dd87438a8ac6cf24672`, report blob `ae06a4a94635b06210a8a403a4e850c9e76b5918`.

Final execution status: RESEARCH_COMPLETE / PUBLISHED_VERIFIED (see the immutable publication receipt below). Mathematical status: PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED. `VERIFIED_ETA=NONE`. The certified repository baseline is unchanged. No new Lean theorem, independent acceptance, or RH proof is claimed.

### A. Most Important Analytic Development

**The binding principal-window loss can be treated as a smaller-scale response of the SAME signal, instead of being estimated as an unrelated error.** On the exact principal residue, the original normalized one-prime slot satisfies

```text
principalSlot(Q,A,eta,s) = -1 - eta Q^(-s) + E_Q(s),
|E_Q(s)| <= 12 Q^(-11/8),
Q >= 480, |A| <= 1, |eta| = 1, Re(s) >= 7/8.
```

The sign and coefficient of the leading correction are retained. After the original weighted finite product and Mellin integral, this term is exactly

```text
(T_Z f) = sum_j sum_(p in T_j(Z)) alpha_jp(Z) eta(p) Q_p^c f(Z/Q_p).
```

Here `f` uses the SAME fixed exclusion set and correction function as the full original probe; the weights remain those at the OUTER scale Z. A weighted-supremum argument proves that `f+T f=O(Z^(theta+c))` implies `f=O(Z^(theta+c))` for theta>0. It does not assume the desired growth bound and requires no prime-phase independence.

Claims RD1-RD5 below give a complete PAPER derivation, from the already-certified source inputs, of the conservative candidate

```text
beta <= 7/8 - actualSlotMinimum D
```

for each original fine fixed-slot geometry D at Delta=1/1000000. With the already-existing near-uniform family this yields the candidate

```text
b_RD = 7/8 - 1/(8 N_pack),
forall eps>0, exists C_eps>=0, forall integer n>=1:
  |M(n)| <= C_eps n^(b_RD+eps).
```

Since `b_base=7/8-7/(64 N_pack)`, the boundary difference is `1/(64 N_pack)`. Spending the positive loss `1/(128 N_pack)` gives a fixed-power candidate gain of `1/(128 N_pack)` over b_base. This is a paper-level claim submitted for adversarial review, not a certified replacement of b_base. All six complete-return costs are listed and paid in RD4; a local slot estimate alone would not establish this conclusion.

The Coordinator's CR2 objection remains correct: the old theorem requiring actual beta>=7/8 cannot be invoked below that range. RD uses the certified 7/8-ANCHORED leaf estimates and keeps the Mellin contour above 7/8. It changes the principal comparison, not beta's definition or the contour domain.

### B. Current Objective, Authority, And Continuity

Live main, rechecked during this execution: `655f897e274a8ba8a2fed80ecc1fc75a0d849174`. Tree `a4889160114bebe7f7e3bf240122db7dffe44c2f`.

| Governing file | Blob SHA |
| --- | --- |
| AGENTS.md | c9c89f01b90b526de9f3e8ea92478e36504711b6 |
| CURRENT_PROOF_CONTRACT.md | 95566e37c8eaeb99ee680660df4f9d2e06ea5038 |
| docs/RHLEAN_CROSS_ROUTE_SIGNED_RECOVERY_20261110.md | e922d4ba9362a1ae196af8f6de88f7417f92087c |

`cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1`. Retain the complete-return, original-carrier, human-merge, and nine-route safeguards of `high_attack_ack=COMPLETE_SIGNED_HIGH_ATTACK_V1`, `chain_ack=CANCELLATION_CHAIN_REUSE_V1`, and `finite_wheel_ack=FINITE_WHEEL_CENTERED_RH_V1`; those older priorities do not override the current five-stage directive.

Canonical objective remains `VFCanonicalSquareVonKochStatement`: there is one C>=0 such that every integer R>=2 satisfies `|pi(R^2)-VF_can(R^2)| <= C R log R`. It is OPEN. On the exact finite-wheel coordinate, X=R^2-1, y=R-1,

```text
F_R = sum_(d | product_(p<=y) p) mu(d) fract(X/d),
D_R = X product_(p<=y)(1-1/p) + pi(y) - 1 - li(X),
F_R-D_R = li(X)-pi(X).
```

All virtual d>X terms and the d=X boundary are retained. RD's sub-7/8 Mertens proposal is far short of the canonical square-root estimate. No equality of Hecke signal, rational Mobius sum, and prime discrepancy is asserted.

Both Eastern dates were read at reports intake `ffbe23bc6cdfb76ddacd7a5706c95b0717a41dcf`. TODAY=AVAILABLE for all seven roles; YESTERDAY=CARRY_FORWARD. No absent work was invented. The latest Owner continuation BR was included, not just its earlier HM entry.

| Role | November 10 blob | November 9 blob / retained finding |
| --- | --- | --- |
| Coordinator, identical mirrors | 1cf71a74d0e80d5dc05ab1ef08f1ad6fcf134c9a | 6fba43130391ad4a606aa3809c20f344d668c709; CD/AP source and cutoff scope |
| Owner | ece5b3cd8d25b45e64c48812c81d71f6eddf23a9 | 643e8a004d9d8e0be102b03e2f79bb3b217ae916; CF complete cofactor formula |
| Analytic, before this continuation | d8337353a94b465f53a0c6a65ad46aac1dc1927e | d1d0d86d444b9c447cf6acf4bd18fdcaf02e56a3; SC/MB and proper-sector limits |
| Wheel | 79ff39e0f79a30f4cf1657b22f96ebe49de4d717 | 0624246d03b19cf76c01e186b7d868a248d896ef; RA/DG/RF scopes |
| Census | 8a89d1a899850e39320a96bf35a6f221060fc8a7 | 8c927cc6c323533ba1cfd369404b25aa4f9cef91; finite counterexamples and complements |
| Referee | ae7de1cb1900818b8844c2c3c7da597cc8f7eaa9 | a5d0192eb31c0efb3767187a7752f1a0d07f8534; AP/DA scope corrections |
| Lean | 0355c3203ede834e1abbe9bc2fc161bc7d7ece04 | 8b60c6136ac151774be2db0aee8f543f286b53aa; exact-head validation limits |

The external inbox blob is `038018145c0fddb2f6306c0712373adf9cd1ea52`; no entry after October 18. EXT-20261018-PNT-1..3 and the older root/denominator cautions remain source safeguards, not present task assignments. Today's HF high-frequency estimate was not rerun or promoted to a complete endpoint. HM1 and UC's finite results retain the Referee's scoped acceptance; PC/UB/BR author-level extensions are not silently independently accepted here. Owner BR's prime-versus-composite innovation distinction reinforces the prohibition on a fictitious prime/Mobius identification.

### C. Mechanism And Required Five-Stage Capsule

#### 1. BASELINE / DEPENDENCY RECEIPT

The strongest explicitly quantified applicable formal baseline found is
`RHLean.Analysis.native_mertens_near_uniform_window_error_closed`, with

```text
Lfine = explicitFineLength > 0,
N_pack = ceil_nat(max(1,1/(6 Lfine)))+2,
N_old  = ceil_nat(max(1,1/(3 Lfine)))+2,
b_base = 7/8 - 7/(64 N_pack).
```

The theorem is `MertensGrowthAtMost b_base`, not a no-loss power bound. Monotonicity of max and ceiling proves N_pack<=N_old; thus `7/(64 N_pack) > 1/(48 N_old)`. This reuses the Coordinator's CR1 comparison, not a new endpoint or an identification of slot counts.

The [exact #1119 head run](https://github.com/OVVO-Financial/RH_Lean/actions/runs/42552018910/job/128949473700) succeeded at `77ee815846d6d534c866f0752aa33b84c385610a`. Its theorem/type, warning-fatal Lean, transitive standard-axiom, and five live closure checks were read. The closure sizes printed were 35358, 35375, 35736, 35737, and 35753; terminal axioms were restricted to propext, Classical.choice, Quot.sound. Dependency-fetch dirty-worktree warnings are not misreported as Lean proof warnings. No local Lean execution occurred.

Pins: Lean 4.34.1, compiler `5045d0056413266e57c625dcd7c365b10e377c52`; Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`; PrimeNumberTheoremAnd `c39a751132c88b6e8080b74c74023fd95b3d8be0`; openai/math `1581d4cbdd69a0faf34b2089614fe2a814316a6a`. The additive anchored generator reads RH_Lean pin `9cbfce5295343bcb411e6d2cb159b59995cd985b`, uses the already-proved actual beta<=7/8, and does NOT redefine beta. Relevant main blobs were compared with the tested #1119 tree and are unchanged.

The complete path is original source construction and moments -> total-mass LOW -> anchored principal/HIGH -> signal nonvanishing -> actual Hecke beta -> modulus-one Dirichlet/Hecke product -> zeta rightmost zero -> genuine Mertens converse. Its explicit finite-source choices and arbitrary positive losses are part of the theorem. A green conditional consumer elsewhere does not discharge its premise. This is a receipt for the formal baseline and a source-level audit of the path used here, not a claim to have independently re-proved all 35,000 imported declarations.

Actual-prime `riemannHypothesis_of_vfCanonicalSquare` still has its explicit classical criterion and arithmetic square-bound hypotheses. The finite-AC RH consumer still requires its complete arithmetic input. Neither is claimed solved by the baseline audit.

#### 2. FOUR-WAY SOURCE MAP

The selected physical source is the COMPLETE fixed-source compensated OAI probe, followed by its existing analytic return to actual M(n). The following is a typed crosswalk, not four equal representations.

| Euler / finite AC | VF / prime discrepancy | NNS / OAI | Square blocks / native HIGH | Prime/Mobius coupling |
| --- | --- | --- | --- | --- |
| Actual X=R^2-1; Q_R=sum_(1<=a,b<R) mu(a)mu(b) floor(X/(ab)) = 2M(R-1)-M(X). K_R retains every historical y<R. EXACT_IDENTITY by `eulerSelfDualBilinear_eq_two_mertens_sub_endpoint`; finite-A/C bound remains OPEN. | Actual centered wheel F_R-D_R=li(X)-pi(X), unit survivor, physical and virtual terms included. EXACT_IDENTITY by `finiteWheel_squareFractional_centered_eq_reference_sub_pi`; canonical VF/Li bridge has its stated fixed normalization. | J_eta,h(Z) is `SourceData.tiltedProbe`: original Hecke ideals, ray-class pools outside S, compensated selected/unselected tuples, source weights, and original principal normalizer. Signed Gram and Co-Div equalities are EXACT_IDENTITY, not cancellation estimates. RD works on this whole probe. | `groupedSquareBlocks_sum` groups any signed integer weights exactly. M(X) is a full prefix, not one increment. OAI Z is a real Mellin scale, not silently R or R^2. The existing beta -> zeta -> Mertens chain is a ONE_WAY_IMPLICATION. | Ideal phases `idealCoeff eta p` are NOT the rational mu(p) coefficients. The compiled modulus-one Dirichlet/Hecke product and zero-free/Mertens converse provide the actual analytic bridge. There is no coefficientwise isometry from an arbitrary Hecke tuple to the centered wheel. |
| Euler virtual compensation is preserved before any absolute values. | #915 historical/current/clipped populations are not replaced by this OAI source. | Scale X_phys=Z^(17/48-24h), Y_phys=Z^(23/48+12h); slot sum 1/6; integer norms Q_p; normalizer exactly as in D. | Square grouping alone supplies no new prefix bound. No square-of-sum is replaced by a sum-of-squares. | Direct marked-moment-to-wheel and arbitrary Gram-to-Mobius transfers are OPEN_BRIDGE. |

Source anchors: [Euler endpoint](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean), [complete wheel](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/CompleteSquareRootWheelFractionalBoundary.lean), [OAI signed Gram](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/oai_434/VF919OriginalLowTupleSignedGram.lean), [native Mertens bridge](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/oai_434/VF919NativeStrictMertens.lean).

#### 3. FIRST SIGNED LOSS

The first loss in chronological LOW construction and the BINDING endpoint loss are different.

| Source declaration / location | Signed input and loss | Tax and consumer | Payment / recovery / falsifier |
| --- | --- | --- | --- |
| upstream Detector/LowTupleGram.lean:74; `actual_low_tuple_polynomial_sq_eq_signed_gram` | Triangle across original unselected-tuple atoms removes both orientations of their Hermitian off-diagonal. | Moving unselected mass and subsequent LOW envelope; exact original weights and compensation required. | Existing Gram theorem restores equality, not an upper bound with a negative cross term. At J=empty there is one outer tuple, hence zero outer off-diagonal. No universal extra saving inferred. |
| `source_batch_plain_marked_fine_sharper_signed_NNS` | Marked real-energy isometry preserves normSq; the subsequent positive moment bound is on specific source Batch profiles. | Exponent 1+t/2, capacity 2m_row+6(3/4+2Delta)sum selected widths<=1, external real part 17/50, height factor (1+height)^J. | Already paid native HIGH supplier. It does not apply to an arbitrary residue profile at w=1,z=1/6. Profile/capacity/height mismatch is the first transfer gate. |
| upstream `principal_replacement_error`, `principal_slot_error` | The signed D=eta Q^(-s) contribution is put inside a norm and flattened with other terms. | 1440 Q^(-7/8); after slot product and contour, Z^(7/8+c+e-(7/8)m). This is binding for #1119. | RD1 retains -D; remainder 12 Q^(-11/8). Raw error is genuinely of order Q^(-a) for coherent principal phase, so a faster raw bound is false. |
| upstream `fixed_product_relative_error`, `slotRatio_error` | Finite product replaced by an unsigned relative-error envelope, without retaining its linear signed term. | Constant depends on fixed N; old decay Z^(-(7/8)m). | RD2 keeps every first-order term; all higher products, including mixed orientations in any squared expression, are bounded by the exact finite expansion. No cross term is discarded by sign. |
| `slotResidue_bound_of_reciprocal_bound` | Norm inside the Mellin comparison loses the fact that Q^(-s) is a dilation of the SAME signal. | Old complete window bill above; Gaussian envelope is integrable. | RD3 is an exact Mellin dilation followed by an independent contraction, not an improved bound for arbitrary test weights. |
| `actual_nonfloor_rows_saving_tilted` | Moment, bin, and dyadic positive envelopes. | Z^(3/16+Delta-s0-8h+nu+dyadCost), with all moment/height costs paid in hfinal. | Reused unchanged; RD4 checks slack with Delta=10^-6. No saving spent twice. |
| `canonical_probe_exists_ray_cube_tilted_anchored`; floor and principal remainder leaves | Triangle after exact full-row decomposition, then inverse-normalizer bound. | Small/large tail powers, floor saving, 17/48000 principal saving; nu=t/8 charged where used. | All retained in RD4. No inference from a proper row band to the total probe. |
| signal nonvanishing -> zeta -> Mertens | Analytic continuation and positive-loss growth transfer; not a coefficientwise equality. | Every final eps>0 remains. | RD5 spends eps explicitly to state a fixed gain. No RH-strength conclusion or loss-free boundary bound. |

#### 4. PAID RECOVERY TEST

Already-proved theorems were checked BEFORE accepting a new estimate. The signed LOW Gram and Co-Div identities provide the exact missing interaction but do not bound it. The marked 1+t/2 supplier retains the displayed Batch/profile/capacity/height conditions and does not control the principal residue's leading multiplier. The existing one-prime three-tier algebra in `VF919OriginalOnePrimePowerGain.lean` retains genuine R and K*V terms; its central contour uses z.re>=17/50 and does not directly give the residue estimate at z=1/6. Its phase-free BKV warning is respected.

The marked theorem itself consumes `PositiveFineSourceInput`; it is not read as a hypothesis-free bound on arbitrary profiles. The native moment chain supplies the required energy input with its exact source data. RD reuses that complete supplier, rather than counting the conditional interface as an independent theorem.

The useful paid ingredients for RD are instead `actual_window_residue`, `normalized_source_double_residue_variable_x`, `HeckeSignalBounds.contour_shift_left`, source correction analyticity on Re(s)>21/25, native source moments at chosen heights, total-mass LOW, and the already-certified anchored raw return. RD1-RD3 add a new estimate and a new use of the fixed signal, rather than assuming an unproved cross-source covariance.

#1115 complete reciprocal bands, #1122/#1124 wheel/root compensation, #1127 cofactor positivity, and #1128 genuine near-resonance were checked against the atlas and latest reports. None maps coefficient-for-coefficient to this principal Hecke residue; no power saving is borrowed from them. The source-specific CODIV and NYMAN alternatives remain available, with no separate new theorem claimed for them in this run.

#### 5. NET RESULT / ADMISSION VERDICT

**PAPER_GLOBAL_GAIN_CANDIDATE / INDEPENDENT_REVIEW_PENDING.** RD1-RD5 provide the claimed complete paper consumer at b_RD<b_base, including a named positive fixed gain. They do not constitute an accepted new route or a new certified global theorem until independent mathematical review and exact-head Lean verification succeed. `VERIFIED_ETA=NONE`; certified baseline remains b_base. The first review-critical statement is RD4's complete normalized response comparison, not just the local bound. If that return is rejected, RD1-RD3 survive only at their stated intermediate scope.

### D. Exact Formulation And Quantifiers

Let D0 be ANY `Parameters.HighData (1/1000000)` whose distinct positive slot lengths ell_j obey the original fine-mesh condition. Put N=D0.N and m=min_j ell_j>0. Source fields imply

```text
0<t<=10^-8, 0<m<=ell_j<=t/200, sum_j ell_j=1/6.
```

Apply `cappedHighData` to make `(N+8)eps<=t` without changing t,N,ell or the minimum. Then use `withSmallerError` once with

```text
e = min(current positive e, m/64) > 0.
```

Construct a FRESH `SourceData D` and its counts for this positive e. In particular `FirstTail (4e)` is recertified; the old exclusion set is not reused without proof. All source data, positive e, and physical tilt h=m are fixed before the character and Z. This is not an e=0 source and not a limit of Euler products.

Use the original source bump w, with support in (1,2), smoothness, compactness, 0<=w<=1 and w nonzero. For each slot use the exact ray-class prime-ideal pool `T_j(Z)=pool(identityClass,F.S,1,2,Z^ell_j)`. Write Q_p=Norm(p),

```text
w_jp(Z) = w(Q_p/Z^ell_j) Q_p^(-5/6),
M_j(Z) = sum_(p in T_j(Z)) w_jp(Z),
alpha_jp(Z) = w_jp(Z)/M_j(Z).
```

For each fixed character eta, eventually M_j>0, every pool prime is coprime to eta.modulus, and
`480<=Z^m<=Q_p<=2Z^ell_j<=Z`.
These are the original power-pool/mass thresholds, plus ell_j<1. The threshold can depend on eta; no conductor-uniform endpoint is claimed. The actual phases are `eta(p)=idealCoeff eta p`, of norm one on those pools, and `A_p=actualAPhase eta(primaryGenerator p)`, of norm at most one. There is no replacement by density or average phase.

Set

```text
b0=7/8, h=m, c=-11/16-8h, a=b0+e,
chi=eta.excludePrimes F.S,
H_eta(s)=sourceCorrection eta F.S s,
f_eta(Z)=HeckeSignal.signal chi H_eta c Z,
J_eta(Z)=F.tiltedProbe h eta Z.
```

The normalizer of J is exactly

```text
sourceResidueConstant(F.W,F.W,product_(p in F.S) p)
 * Probe.principalScalar(univ,Z,1/6,slotMass(T,residueWeights(w,Z^ell))).
```

It is eventually nonzero. The finite pool normalizer is not applied again to f(Z/Q). The original physical X,Y scales are those in C. Constants below may depend on the fixed source and eta, on the chosen contour and final loss where present; they do not depend on Z, a moving pool, its cardinality, row labels, or a chosen height after those are quantified. Effectivity of the global source thresholds/constants is not asserted. The local constant 12 and finite-product bound are explicit.

### E. Mathematical Derivation

#### RD1. Exact Principal Slot And Uniform Signed Remainder

Claim ID `20261110-analytic-2/RD1`. PAPER_PROOF / SELF_AUDIT.

Use the literal definitions in [PrincipalSlotEstimate](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/PrincipalSlotEstimate.lean), [EulerCoordinates](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/EulerCoordinates.lean), and `ProbeLocal`/`ProbeEuler.markedFactor`. For Q>=480 and Re(s)=a>=7/8, define

```text
q=Q^(-1), D=eta Q^(-s), R=A Q^(3-6s), B=conj(eta) Q^s=1/D,
V=W=q, K=(1-q)D,
P=markedFactor(R,q,q,K,-D+qR,1).
```

The factor Q-1 in the original coordK is essential. Direct substitution, retaining it, gives

```text
P = (1+q)(R-D)/(1-R),
U = 1-qR-(1-q)D,
principalRawFactor = (1+q)U/((1-q)(1-R)),
principalSlot = (1-q)(BR-1)/U - q.
```

All divisions are legitimate: |D|=Q^(-a)<=1/20, |R|<=Q^(3-6a)<=q^2, and
`|U|>=1-|D|-q|R|>=1-1/20-480^(-3)>1/2`. Also 1-q,1-R,1-D are nonzero. The continued correction equals `(1-q^2)U/((1-R)(1-D))`, so it too is nonzero. This verifies the ratio identity directly, rather than relying on a formal division through zero.

Subtract the leading term EXACTLY:

```text
principalSlot+1+D =
 [(1-q)BR - q(1-q)R + (2q-q^2)D - qRD - (1-q)D^2] / U.
```

Its norm is at most

```text
2[Q^(3-5a) + Q^(2-6a) + 2Q^(-1-a)
  + Q^(2-7a) + Q^(-2a)] <= 12 Q^(-11/8).
```

The last inequality holds for EVERY a>=7/8, uniformly in Im(s), A and unit eta; no restriction to fixed height is used. This proves RD1. The exact rational identity is structural; the 11/8 rate, proved using the actual residue relations K=(1-q)D and V=W=q, is the new quantitative ingredient.

#### RD2. Complete Finite-Product Expansion, Including Mixed Terms

Claim ID `20261110-analytic-2/RD2`. PAPER_PROOF / SELF_AUDIT.

Let

```text
d_j(s)=sum_p alpha_jp eta(p) Q_p^(-s),
e_j(s)=sum_p alpha_jp E_Qp(s).
```

Because the principal scalar is `(-1)^N product_j M_j`, the EXACT original slot ratio is

```text
slotRatio_Z(s)=product_j [1+d_j(s)-e_j(s)].
```

In particular the linear d_j term has a PLUS sign in this normalized ratio. Put u_j=d_j-e_j, Vsum=sum_j |u_j|. Uniformly on Re(s)=a>=7/8,

```text
|d_j|<=Z^(-a ell_j), |e_j|<=12 Z^(-11 ell_j/8),
Vsum<=13 N Z^(-7m/8).
```

For Z large enough that Vsum<=1, expand the finite product by subsets. Its full degree>=2 sum has norm at most

```text
sum_(k>=2) Vsum^k/k! <= exp(Vsum) Vsum^2/2.
```

This bounds ALL higher products, not just squares or diagonals. Therefore

```text
slotRatio_Z(s)=1+sum_j d_j(s)+R_Z(s),
|R_Z(s)| <= K_N Z^(-11m/8),
K_N = 12 N + (169 exp(1)/2) N^2.
```

Here 7m/4>=11m/8 pays the quadratic part. N is fixed before Z; the assertion is not uniform in an arbitrarily growing number of slots. No unproved negative off-diagonal, random phase model, or loss of multiplicity is used.

#### RD3. Exact Mellin Return And Independent Delay Absorption

Claim ID `20261110-analytic-2/RD3`. PAPER_PROOF / SELF_AUDIT.

The already-proved beta<=7/8 makes a=7/8+e a legal common contour for every fixed chi. By `HeckeSignalBounds.contour_shift_left`, for x>=1,

```text
f_eta(x) = (1/(2 pi)) integral_(t in R)
    exp((s-5/6)^2) H_eta(s) reciprocal_chi(s) x^(s+c) dt,
s=a+it.
```

The original correction is fixed as x varies. Its norm is <=3/2 on this line, and the existing reciprocal-growth theorem gives a finite C_chi with reciprocal norm <=C_chi(1+|t|)^2. The Gaussian supplies an integrable envelope. Thus all the finite sums below can be exchanged with the integral with absolute domination; no conditional infinite rearrangement is involved.

`actual_window_residue`, the variable-x normalized double-residue identity, and the exact tilted source scaling identify the actual normalized principal residue with this integral times slotRatio_Z(s). Multiplication by a single factor eta(p)Q_p^(-s) gives EXACTLY

```text
eta(p) Q_p^c f_eta(Z/Q_p).
```

The argument is >=1 for all sufficiently large Z. The normalizing weights alpha_jp remain frozen at Z. No new SourceData or inner-scale pool enters this equality. Consequently the normalized principal residue equals

```text
f_eta(Z) + T_Z f_eta + E_res(Z),
T_Z f = sum_j sum_p alpha_jp(Z) eta(p) Q_p^c f(Z/Q_p),
|E_res(Z)| <= C_res Z^(a+c-11m/8).
```

One explicit admissible C_res is K_N times
`(3 C_chi/(4 pi)) exp((a-5/6)^2) integral (1+|t|)^2 exp(-t^2) dt`, after choosing the displayed line reciprocal bound. Its dependence on the fixed character/contour is allowed.

**Absorption lemma.** Let f be continuous on [1,infinity), let theta>0 and c be real, and use ANY moving finite pools and nonnegative alpha whose slot sums are one, with N fixed and `2<=Z^m<=Q_p<=Z` eventually. Unit complex phases are arbitrary. If

```text
|f(Z)+T_Z f| <= C Z^(theta+c)  (Z>=Z0),
```

then f=O(Z^(theta+c)). To prove it, increase Z0 until `N Z0^(-theta m)<=1/2`. For X>=Z0 let

```text
B_X = sup_(1<=x<=X) |f(x)| x^(-theta-c),
B_init = sup_(1<=x<=Z0) |f(x)| x^(-theta-c).
```

These are finite by continuity. For Z in [Z0,X], each Z/Q_p belongs to [1,X], so

```text
|T_Z f|/Z^(theta+c)
 <= B_X sum_j sum_p alpha_jp Q_p^(-theta)
 <= B_X N Z^(-theta m) <= B_X/2.
```

It follows that `B_X<=max(B_init,C+B_X/2)`, hence `B_X<=max(B_init,2C)` for every X. This proves the lemma without assuming f already has the target global norm. The SAME proof works for complex correlated phases and arbitrary moving weights. Continuity of the actual f on positive reals is the existing `signal_continuousOn` theorem. The growing-scale threshold may be enormous; it is finite and chosen before X.

#### RD4. Complete Original-Probe Comparison With All Six Bills

Claim ID `20261110-analytic-2/RD4`. PAPER_PROOF / SELF_AUDIT; highest-priority independent review obligation.

Assume temporarily `51/100<=actual beta<=7/8`. The upper bound is already certified. The lower bound is needed for the native source-moment supplier and will be automatic in RD5's contradiction range; it is NOT silently removed.

Use the source from D, h=m, nu=dyadCost=t/8, zeta=t, arithmetic Delta=10^-6, nonfloor saving s0=49/881280, and large-tail saving 1. Select the height tau using the existing `native_uniform_fixed_source_moments` and `chosen_data_height` as in `native_fixed_total_mass_probe_bounds`. It pays `(1+Z^(2 tau))^J` into the permitted Z^t moment allowance, with `2 tau(1+J)<=t` and all original tau/cost restrictions. The fine geometry, original Batch coefficients, and exclusions are unchanged.

Do NOT invoke the bundled old HIGH theorem with sigma=m: its window budget is not available. Instead reassemble its already-proved leaves, replacing only its principal-window comparison by RD3:

The literal old `actual_high_probe_from_raw_moments_tilted` requires `7/8<=actual beta` at line 66 and `Delta+sigma+nu+dyadCost<=saving+(actual beta-7/8)` at line 71. Its principal contour also requires `7/8<actual beta+e`, and its floor comparison uses `3/16<=actual beta-11/16`. These are genuine CR2 gates, not disposable labels. RD does not assert their lower-reference extensions: the certified anchored leaves retain b0=7/8, while RD3 changes the signal comparison they feed.

1. `canonical_probe_exists_ray_cube_tilted_anchored` gives the COMPLETE raw physical probe minus the principal row and full central cube, with small and large tails. The exact anchored proof uses actual beta<=7/8 only to license reciprocal contours; beta is not changed.
2. `physical_principal_residue_remainder_tilted_anchored` and `actual_ray_normalizer_inverse` compare the principal row to the normalized double residue with its full w/z remainders. RD3 handles that residue.
3. `finiteCentralCubeRows_supported_split` partitions the same central cube into supported floor and nonfloor rows. Zero-calibration rows vanish by that exact source theorem, not by deletion.
4. Apply `actual_floor_rows_saving_tilted` with its FREE requested saving parameter equal to m. This does not change the stored HighData.sigma or assume its window budget.
5. Apply `actual_nonfloor_rows_saving_tilted` with the unchanged source-moment input and s0. As in the original assembly, all row labels and grids come from the common canonical transport.

These leaves and the exact partition are visible in [TiltedHighTransport](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/oai_434/VF919TiltedHighTransport.lean), [TiltedHighCentral](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/oai_434/VF919TiltedHighCentral.lean), [TiltedHighPrincipal](https://github.com/OVVO-Financial/RH_Lean/blob/655f897e274a8ba8a2fed80ecc1fc75a0d849174/research/oai_434/VF919TiltedHighPrincipal.lean), and the pinned additive anchored generator. The inequality below follows by their triangle bounds AFTER the signed response is retained.

For every fixed eta there is C_eta, chosen before Z, such that eventually `|J_eta(Z)-f_eta(Z)-T_Z f_eta|` is at most C_eta times the sum of the following SIX powers:

| Complete component | Exact power before comparison | Sufficient paid inequality |
| --- | --- | --- |
| Small physical tails, after normalization | b0+c-63/800+8e+nu | m+8e+nu<=63/800 |
| Large physical tails, saving 1 | -1-8h+nu | m+nu<=19/16 |
| Principal w/z remainders, after normalization | b0+c-17/48000+nu | m+nu<=17/48000 |
| NEW complete principal slot residual | b0+c+e-11m/8 | e+m<=11m/8 |
| Supported floor central rows, requested saving m | 3/16-m-8h | equality with 3/16-9m |
| Supported nonfloor central rows | 3/16+Delta-s0-8h+nu+dyadCost | Delta+m+nu+dyadCost<=s0 |

Each power is <=`3/16-9m=(b0-m)+c`. The geometric and floor source budgets, before any final exponent comparison, are also paid:

```text
24m <= (3/25)t < t;  m<1/960;
13/16+3t < 7/8;
18t+s0 <= 49/440640;
2t+26e+(N+8)eps+t+t/6+nu+m
 <= (12929/3000)t < 7/1200;
Delta+m+t/4 <= 10^-6+(51/200)t < 49/881280.
```

Here only t<=10^-8, m<=t/200, e<=t/2000, `(N+8)eps<=t` were used; all inequalities have strict slack. The new window has additional margin
`11m/8-e-m >=23m/64>0`. The source detector, phase, capacity, count and height budgets remain those of the valid capped/smaller-error data. No requirement on the stored sigma is raised to m. Its old window budget is simply not used for the new residue estimate.

We have therefore proved, under the temporary beta range, the full response comparison

```text
J_eta - (I+T)f_eta = O_(F,eta)(Z^(3/16-9m)).
```

The already-proved `SourceData.tiltedProbe_low_total_mass`, for this SAME source and any loss omega>0, gives

```text
J_eta = O_(F,eta,omega)(Z^(3/16-9m+omega)).
```

Combining them and applying RD3 with theta=7/8-m+omega>0 yields

```text
f_eta = O_(F,eta,omega)(Z^(7/8-m+c+omega))
```

for every omega>0. There is no assumption that f itself was already small. This is the independently proved response recovery which the former absolute principal-window estimate could not provide.

#### RD5. Actual Beta, Zeta, And Genuine Mertens Endpoint

Claim ID `20261110-analytic-2/RD5`. PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING.

Let g=7/8-m. Since m<=t/200<=5*10^-11, g>21/25. Suppose actual beta>g. The certified upper bound beta<=7/8 puts us in the beta range required by RD4. Choose

```text
omega=(beta-g)/2,
0<omega<m,
g+omega=beta-omega.
```

The original primitive-zero-near-beta theorem gives a primitive character eta and a non-pole zero rho with `rho.re>beta-omega=g+omega`. Use the same finite deletion mask as the existing total-mass endpoint proof; `excludePrimes_mask` and `LFunction_eq_of_mask_nonpole` retain that zero in chi=eta.excludePrimes F.S. The argument and nonprincipal/pole alternatives are unchanged.

RD4 bounds f_eta by exponent g+c+omega. Apply the existing `HeckeSignal.nonzero_of_probe_bounds_variable_boundary` with

```text
J=f_eta, alpha=21/25, theta=g, beta_reference=7/8,
omega as above, sigma=m, c=-11/16-8m.
```

Its error input is identically J-f_eta=0. The maximum boundary is `max(g+omega,7/8-m)=g+omega<rho.re`. Its analytic input is the SAME `sourceCorrection_analytic_wide` and `sourceCorrection_bound_wide`; the correction is within 1/2 of 1, so it cannot cancel the zero. Every remaining type restriction follows from 21/25<g, omega<m, m>0, and beta_reference<=1. The theorem contradicts the retained zero. Thus beta<=g. This uses Mellin continuation of a proved growth bound, NOT an illegal shift of the physical contour below beta or 7/8.

For the existing near-uniform fixed geometry, m>=1/(8N_pack), giving beta<=b_RD. Then `native_mertens_growth_at_hecke_beta` and `growthAtMost_mono` return the genuine all-integer Mertens growth statement from A. The original modulus-one Dirichlet/Hecke product, zeta-zero transfer and Mertens converse are not replaced by a model sequence. Every n>=1, including the finite initial range, is included by that existing consumer.

Finally, writing `eta_fixed=1/(128N_pack)>0`, consume the growth assertion at eps=eta_fixed:

```text
b_RD+eta_fixed = b_base-eta_fixed,
exists C>=0, forall integer n>=1:
  |M(n)| <= C n^(b_base-eta_fixed).
```

This is the precise proposed fixed gain. It is not a claim of `MertensPowerBound b_RD` without a positive loss.

### F. Quantitative Comparison And Scope

Old complete binding source comparison: `J-f=O(Z^(b0+c+e-(7/8)m))`; error closure recovers the beta boundary b0-(7/8)m. New comparison: `J-(I+T)f=O(Z^(b0+c-m))`, with a strictly faster principal remainder and an independently invertible response on every positive theta-weighted space. LOW gives the matching b0-m boundary. The improvement is m/8 at fixed geometry, at least 1/(64N_pack) for the explicit family. The conservative choice h=m does not optimize RD1's 11m/8 residual reserve.

All summations over slots/pools are finite for each Z. The only integral is absolutely dominated by the existing polynomial-Gaussian bound on one legal contour. The Euler correction's infinite product is the already-certified fixed-source one, not a new rearrangement. The delay proof takes suprema on finite compact intervals first, so no unproved global bounded norm is assumed. Constants can grow badly with N, 1/m, conductor or 1/e, but these are fixed before the main scale. No uniformity in growing N, vanishing m, varying exclusion masks, or all characters at once is claimed.

### G. Original-Carrier Bridge

The only new multiplier extracted is the literal `idealCoeff eta p * Norm(p)^(-s)` inside the actual normalized principal residue. Original A phases, reciprocal denominators, all higher finite-product interactions, source correction H, ray-class restrictions, finite exclusions and nonzero mass normalizers remain. At an inner argument Z/Q_p, f is evaluated with the SAME chi,H,c; it is not a new physical probe with resized exclusions or weights. The source changes once when e is reduced, before eta and Z, using the established fresh-source constructor.

No principal-row estimate is promoted to a total estimate without the floor/nonfloor decomposition and both tails. RD4 explicitly includes those complements. The final bridge to mu(n) is exactly the already-certified analytic adapter, not an equality with Hecke phases. The wheel/VF source and #915 populations remain distinct; their RH-strength estimates are still unpaid.

### H. Falsification, Novelty, And Self-Audit

**Raw error improvement is false without the retained response.** For principal eta=1 and any admissible bounded A, with real a in [21/25,1), the same exact identity gives
`principalSlot+1=-Q^(-a)+o(Q^(-a))` uniformly in A. Indeed the displayed five numerator exponents are all strictly below -a when a>3/4. Thus at a=7/8 the raw error is NOT O(Q^(-11/8)); and at fixed a<7/8 the old uniform O(Q^(-7/8)) local estimate fails. This does not refute a full-signal bound. RD retains this genuinely coherent term and absorbs its complete response.

**Phase and sign check.** The slot is -1-D+E, whereas the ratio after division by (-1)^N product M_j is product(1+d_j-e_j). Using a minus sign for T in the displayed residue equality would be wrong. Absolute contraction itself does not need a favorable sign.

**Uniformity check.** Choosing source parameters, m, N, e, h and height policy before Z is essential. Moving alpha(Z) is permitted, but replacing it by alpha(Z/Q) is not. A hypothetical N=N(Z) with N Z^(-theta m) not tending to zero would invalidate RD3. No such growing source is used.

**No hidden contour extension.** All new Mellin equalities use a=7/8+e, actual beta<a, and a<1. The wider analytic boundary 21/25 is used only by the already-established growth-to-nonvanishing consumer. The old actual-beta>=7/8 HIGH theorem is not reused outside its range.

**No unsupported source-moment extension.** RD4 explicitly retains beta>=51/100; RD5 derives that premise in its contradiction branch. In the complementary branch beta<=g already holds. Original external 17/50 profiles, capacity, height and conductor costs are never dropped.

**Novelty check.** Exact source/report search found the prior raw ratio identity and the original one-prime three-tier/power results. `VF919OriginalOnePrimePowerGain.lean`, blob `492cd5d4a459c9665df07e5f77653be5261591a0`, has central z.re>=17/50 local bounds and explicit remaining global obligations. It does not contain RD's normalized w=1,z=1/6 expansion, same-signal delay absorption, or this complete endpoint. No novelty is claimed for rational expansion, Mellin dilation, or the elementary supremum principle in isolation. The proposed advance is their source-specific quantitative combination and full return.

**Executed checks, preregistered before execution.** Three exact Laurent-polynomial identities in q,D,R were checked. Eighty-four exact rational local cases used Q=k^8, k=3..30, a=7/8, A=-1,0,1; the largest observed `Q^(11/8)|slot+1+D|` was approximately 1.01265239223, below 12. These test the lemma's real-Q domain, NOT genuine prime-ideal distribution. Eleven conservative rational budgets, the exponent gap and the positive-loss spend all passed. Raw uncorrected errors scaled by Q^(11/8) grew approximately 81.0123, 10000.0008 and 810000.000035 for k=3,10,30, as the exact obstruction predicts.

The numerical samples are not an all-scale proof; the inequalities in E are. Symbolic/exact checking is SELF_AUDIT, not independent review or Lean certification. No large prime census was rerun. The standalone audit script has SHA256 `1834fdb0c07b1b37821c41851ce7707518b6217249a12a14254b1e96dff25947`; its reproducible source is included below. An unavailable optional SymPy import led to using only Python's standard-library exact fractions, not to installing a new dependency or running Lean.

### I. Conceptual Interpretation

The important principle is that a coherent principal correction need not be forced to cancel prime-by-prime. Here it is a small, source-faithful feedback from smaller arguments of the SAME analytic signal. Its weighted operator norm tends to zero because the true prime norms grow while the number of slots remains fixed. This provides genuine control of the response rather than assuming cancellation of arbitrary mean-zero coefficients.

This changes the proposed handling of one binding OAI loss; it does not merge the nine route families or dismiss prime-owner, CODIV or NYMAN alternatives. In particular it does not contradict the positive/resonant arithmetic obstructions in other coordinates. Further formal expansions might improve the conservative choice h=m, but no repeated bootstrap, limiting exponent, or stronger optimized endpoint is asserted in this run.

### J. Specialist Handoffs

- **Coordinator:** Review RD4/RD5 as a proposed resolution of the binding CR2 concern through signed response recovery, not lower-contour reuse. Keep b_base unchanged until independent acceptance and exact-head verification. The candidate fixed eta is 1/(128N_pack), with every complementary bill displayed.
- **Adversarial Referee:** Independently check the literal K=(1-q)D simplification and local remainder; the sign in the product; frozen outer alpha(Z); legality of Z/Q>=1; compact-supremum absorption; all six anchored/raw leaves; the free floor saving versus stored sigma; beta>=51/100; fresh exclusions; and the final positive-loss spend. Return ACCEPT/REVISE/REJECT per RD claim. The first falsifier should be a failed source hypothesis or inequality, not a comparison to a different carrier.
- **Lean Verification:** No new claim is pre-accepted. After independent approval, the useful sequence is principal-slot signed remainder -> complete weighted product -> Mellin delay -> absorption -> raw anchored assembly -> same beta/zeta/Mertens consumer. Preserve original definitions and warning-fatal exact-head/axiom/dependency gates. Do not encode RD4 as an assumed new source estimate. No local Lean execution or speculative PR was performed here.
- **Owner / Wheel:** Confirm any source-mask or phase-normalization concern against the literal residue definitions; no prime-count/Mobius coefficient bridge is requested for the internal Hecke delay. Preserve BR/CF/HM/PC/UB scopes and all virtual/cofactor complements on the independent wheel program.
- **Census:** No giant scan is needed to test this analytic mechanism. A useful independent finite check would compare the original local rational functions and normalized small finite products with RD1/RD2 for complex unit phases, including coherent eta=1 and mixed A phases, using exact Gaussian rationals where possible. Such tests audit algebra, not the all-scale Mertens conclusion. Existing genuine-prime tables should not be relabeled as evidence for RD5.

These are report handoffs for future actual invocations, not agent launches or schedule changes.

### K. First Missing Obligation

For this proposed finite gain, the paper derivation supplies the required analytic estimate rather than leaving a desired-bound hypothesis. The first outstanding VALIDATION obligation is independent review of RD4's complete-source assembly; the first new formal statement would be the same-source normalized response bound in RD4 with its actual parameters, masks, heights and constants. No new Lean certificate exists for it.

For the canonical RH objective, the complete centered wheel/VF O(R log R) estimate, or another independent sufficient global theorem reaching that scale, remains OPEN. This paper endpoint does not discharge it. A further response expansion is only a next research possibility, not a proved renewal rule.

### L. Resume Capsule And Publication Boundaries

Resume from RD1-RD5, not from an unqualified new baseline. Current mathematical classification is PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING; `VERIFIED_ETA=NONE`. Highest-value next work is independent checking of the complete raw anchored return and then formalization only after acceptance. Preserve the earlier HF claims and this CR checkpoint. Do not repeat the unchanged high-frequency derivation or large arithmetic scans. No separate substantive NYMAN attempt is claimed in this execution; maintain the protected rolling-route coverage on subsequent actual invocations.

Source main and exact-head dependency receipts are above; material file blobs follow. Read latest reports again before acting. No open/draft PR existed at intake; recent merges #1129 policy, #1128 resonance repair, #1127 cofactor positivity, and #1126 conditional finite-AC are distinguished from unconditional endpoint suppliers. This role created no branch, PR, issue, workflow run, Lean edit, merge, or other agent report edit.

The early checkpoint was verified. This final continuation must be appended to the CURRENT own report blob, preserving prior content, and re-fetched at the returned immutable commit before publication is claimed complete. A publication receipt will record that immutable readback separately from mathematical acceptance.

### Material Source Receipts

Main file bytes were read at the immutable main SHA above. Relevant #1119 dependency files match the exact tested head; the hosted audit, not this script, provides their Lean receipt.

| RH_Lean path | Blob SHA |
| --- | --- |
| `research/oai_434/VF919TiltedHighCentral.lean` | 6f75563d84161a023e4750df69ad0def460c0513 |
| `research/oai_434/VF919TiltedHighAssembly.lean` | 883141e0af896d4132bfc4ffa076e2d265ece5c9 |
| `research/oai_434/VF919TiltedHighTransport.lean` | 50c46fb1c5629865c3b7a6546ed3d9418fff1391 |
| `research/oai_434/VF919TiltedHighPrincipal.lean` | e123ffa5903a62f6249aafef7a093dc6a7e3eb09 |
| `research/oai_434/VF919TiltedHighTails.lean` | 6ae8ea83aca3d3f8ba8d65d42f2a6a4428e6b84f |
| `research/oai_434/VF919FiniteSlotReflectedGain.lean` | a5545b5a00958b69f6fbfd79fc555a0476aa6487 |
| `research/oai_434/VF919NativeSourceMoments.lean` | 4e5326b983f5110f7138d222f7b1be71c5694dfc |
| `research/oai_434/VF919TotalMassEndpoint.lean` | 827bb952c4d4311d75fd03a2470799dc10b0f7e7 |
| `research/oai_434/VF919WindowErrorClosure.lean` | f629db1b2b65d6ec042ac9432397d4b6316200c6 |
| `research/oai_434/VF919WindowSaturatedLowPrincipal.lean` | b7b05069ea013d83b2acaa76a8ea2ed932568930 |
| `research/oai_434/VF919ExplicitSquareBlockPacking.lean` | 32999039fdeea99c58a070c1c4ee9c140720dd44 |
| `research/oai_434/VF919ExplicitFixedSourceSlotCount.lean` | bad5aab0a60e96d19e7c9550cd7c0a072288bc0f |
| `research/oai_434/VF919NativeStrictMertens.lean` | b33a4883e1ddb0551b0f11f062bce46680d87450 |
| `research/oai_434/VF919NativeSevenEighthsReplay.lean` | 111c933a7ca15647105ce6a4d0f3cbfc3cde81f4 |
| `research/oai_434/VF919OriginalLowTupleSignedGram.lean` | dd2fde01ae6e2446da4e69b30f6fc80fcadb858d |
| `research/oai_434/VF919OriginalMarkedSharpenedSignedNNS.lean` | 1ead3888a1f59cacc71f482f6d4ce9c9ad31903a |
| `research/oai_434/VF919OriginalOnePrimePowerGain.lean` | 492cd5d4a459c9665df07e5f77653be5261591a0 |
| `research/EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean` | e7ee8f77ffd59bccaa49dd6d74fbe0d7952c2d73 |
| `research/CompleteSquareRootWheelFractionalBoundary.lean` | ecb482e52deeee5e9b3853592a3ffdace662d2ff |
| `research/MERTENS_EXPONENT_ENVELOPES.lean` | 655b896e8d5a41c9f8fc3c456eae3944a98bfefe |
| `research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean` | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb |
| `scripts/lean/slot_anchored/prepare_anchored.py` | 0bac9047afaa8e9ddc5ac246be2d0fe7d6efa725 |
| `.github/workflows/vf919-window-saturated-low-principal.yml` | bf53637ed649b2c8c7517ad3b81c33620f3bffa9 |
| `scripts/lean/window_error_closure/WindowErrorClosureAudit.lean` | 1f17f9401a63d16227db2e2aad020b9f74bc5f4e |

Upstream paths below are relative to `lean/OAI/NumberTheory/DirichletL/`, all at pin `1581d4cbdd69a0faf34b2089614fe2a814316a6a`.

| Upstream path | Blob SHA |
| --- | --- |
| `ParametersHighData.lean` | c565dc0a72c7da9a2706cdd835e69a39e8c0dc14 |
| `PrincipalSlotEstimate.lean` | f9250c7c4464f374902bbb39ebbb3487d96bea1f |
| `PrincipalSignalComparison.lean` | bd252b01e2784f9ec32fe9c1e0380c4b221adc23 |
| `Detector/Local.lean` | 599ab7884122342f9d200a81119ea5a410114e0a |
| `Detector/Euler.lean` | ce1309a4da0b0b3ccd703946aef504b96f95e6f5 |
| `Detector/EulerCoordinates.lean` | 75a2a5a3801939489102d6e7cce2ef1cab479057 |
| `Detector/PrincipalResidueActual.lean` | 2f336d8cfb0e6ec157ad1d43099372eb61961381 |
| `Detector/PrincipalNormalizer.lean` | 890de70fac5b637af0cb803f3d8c691df6c668b2 |
| `Hecke/Signal.lean` | 9b0f1f6ff5f74c77fee06327c4936c2a9e180df5 |
| `Hecke/SignalBounds.lean` | 8b0f3faf87c2649dfccfc7c6eb4349259ff34d7e |
| `Detector/LowTupleGram.lean` | 710598c8bef4d1a1ec98aa7e68b00369962c3d17 |

### Reproducible Exact Self-Audit

The following standard-library script was frozen before its first execution. Run with Python 3; it performs no file or network writes. This is not a Lean program or a genuine-prime census.

```python
"""Self-audit only; no Lean execution and no numerical endpoint certificate.

Preregistered before this script's first execution:
1. Check three rational identities as exact Laurent polynomials in q, D, R.
2. Check the local remainder on exact real cases Q=k^8, a=7/8,
   k=3..30, A in {-1, 0, 1}; this is the lemma's real-Q domain,
   not a sample of genuine prime ideals.
3. Check all conservative complete-return budgets at their rational maxima.
4. Test the false raw-slot upgrade against the exact A=0 principal phase.
All results are finite/symbolic self-audits, not independent review.
"""

from fractions import Fraction as F


class P:
    """Tiny exact Laurent-polynomial checker; variable order q, D, R."""

    def __init__(self, terms=None):
        self.terms = {k: F(v) for k, v in (terms or {}).items() if v}

    @staticmethod
    def cast(value):
        return value if isinstance(value, P) else P({(0, 0, 0): value})

    def __add__(self, other):
        result = dict(self.terms)
        for key, value in P.cast(other).terms.items():
            result[key] = result.get(key, F(0)) + value
        return P(result)

    __radd__ = __add__

    def __neg__(self):
        return P({key: -value for key, value in self.terms.items()})

    def __sub__(self, other):
        return self + -P.cast(other)

    def __rsub__(self, other):
        return P.cast(other) + -self

    def __mul__(self, other):
        result = {}
        for ka, va in self.terms.items():
            for kb, vb in P.cast(other).terms.items():
                key = tuple(a + b for a, b in zip(ka, kb))
                result[key] = result.get(key, F(0)) + va * vb
        return P(result)

    __rmul__ = __mul__

    def zero(self):
        assert not self.terms, self.terms


q = P({(1, 0, 0): 1})
d = P({(0, 1, 0): 1})
r = P({(0, 0, 1): 1})
b = P({(0, -1, 0): 1})
k = (1 - q) * d
marked_numerator = r * (1 - q) - k * q + (-d + q * r) * (1 - q)
(marked_numerator - (1 - q) * (1 + q) * (r - d)).zero()
u = 1 - q * r - (1 - q) * d
((1 - r) + (1 - q) * (r - d) - u).zero()
slot_num = (1 - q) * (b * r - 1) - q * u
rem_num = ((1 - q) * b * r - q * (1 - q) * r
           + (2 * q - q * q) * d - q * r * d - (1 - q) * d * d)
(slot_num + (1 + d) * u - rem_num).zero()
print("Exact Laurent identities: 3/3 PASS")

worst = F(0)
cases = 0
for kk in range(3, 31):
    Q = kk ** 8
    q0 = F(1, Q)
    d0 = F(1, kk ** 7)
    for A in (-1, 0, 1):
        r0 = F(A, kk ** 18)
        k0 = (1 - q0) * d0
        marked = ((r0 * (1 - q0) - k0 * q0) / (1 - q0)
                  - d0 + q0 * r0) / (1 - r0)
        correction = (1 - q0 * q0 + (1 - q0) ** 2 * marked) / (1 - d0)
        replacement = (((1 / d0 - q0) * (1 - q0) ** 2 * marked
                        - q0 * (1 - q0 * q0)) / (1 - d0))
        slot = replacement / correction
        u0 = 1 - q0 * r0 - (1 - q0) * d0
        direct = (1 - q0) * (r0 / d0 - 1) / u0 - q0
        assert slot == direct
        scaled = abs(slot + 1 + d0) * kk ** 11
        assert scaled <= 12
        worst = max(worst, scaled)
        cases += 1
print(f"Exact real local cases: {cases} PASS; max scaled remainder = {float(worst):.12g} < 12")

t = F(1, 100_000_000)
m = t / 200
e = min(t / 2000, m / 64)
nu = t / 8
delta = F(1, 1_000_000)
saving = F(49, 881_280)
budgets = {
    "physical tail": t - 24 * m,
    "LOW tilt": F(1, 960) - m,
    "small tails": F(63, 800) - (m + 8 * e + nu),
    "principal remainders": F(17, 48_000) - (m + nu),
    "large tails": F(19, 16) - (m + nu),
    "floor": F(7, 1200) - (2*t + 26*e + t + t + t/6 + nu + m),
    "central": saving - (delta + m + nu + nu),
    "central internal": F(49, 440_640) - (18*t + saving),
    "ray conductor": F(7, 8) - (F(13, 16) + 3*t),
    "new window": F(11, 8)*m - e - m,
    "wide analytic domain": F(7, 8) - m - F(21, 25),
}
for name, margin in budgets.items():
    assert margin > 0, (name, margin)
    print(f"Budget {name}: PASS, margin {margin}")
assert F(11, 8) - F(1, 64) - 1 == F(23, 64)
assert F(1, 8) - F(7, 64) == F(1, 64)
assert F(1, 64) - F(1, 128) == F(1, 128)
print("Endpoint gap and positive-loss spending: PASS")

print("False raw Q^(-11/8) upgrade: exact principal A=0 samples")
for kk in (3, 10, 30):
    q0 = F(1, kk ** 8)
    d0 = F(1, kk ** 7)
    slot = -(1 - q0) / (1 - (1 - q0)*d0) - q0
    scaled_raw = abs(slot + 1) * kk ** 11
    print(f"k={kk}: raw error / Q^(-11/8) = {float(scaled_raw):.12g}")
print("All registered checks PASS. No Lean or all-scale numerical certification claimed.")
```

### RD Publication Receipt

Verified 2026-11-10 09:49:11 EST / 14:49:11 UTC. The final research continuation was committed to the authorized own report on agent-reports at `9d7ff721c4827d1f12d0c3eab047262d411868b1`, blob `d06c6687554476e546f32277e1ed92e392f7ff4e`, and re-fetched using that immutable commit. The returned 115150-character report matched the submitted content exactly and retained the entire prior 63215-character report as an unchanged prefix. All five RD claim statements, the source receipts, and the reproducible audit were present. A current-branch fetch confirmed the same blob before adding this receipt.

Publication status is COMPLETE / VERIFIED. This supersedes the preparation-time pending-publication wording, not any mathematical scope limitation. RD1-RD5 remain PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING / NOT_FORMALIZED; VERIFIED_ETA remains NONE. No independent reviewer or Lean run was launched. The sole remote write target was this daily report. The next handoff is independent review of the full RD4/RD5 return; the canonical RH objective remains OPEN.




## Scheduled Continuation Checkpoint - 20261110-analytic-3/IR

### A. Registered Analytic Investigation

IN_PROGRESS / PARTIAL. Independently check Coordinator 20261110-coordinator-1513-EST/MD1-MD5 against the literal principal source, then investigate whether the ORIGINAL Mellin signal's small-argument decay permits the COMPLETE absolutely convergent principal response, without a finite degree cutoff or an omitted mixed tail. Candidate: retain the rational symbol S=q+(1-q)(1-W)/(1-G-(1-q)D) as an infinite dilation series; prove its weighted row mass tends to zero for theta>3/5, including every inner argument below 1. This is a proposed theorem to prove/falsify, not a result already obtained. The physical LOW/HIGH, source-height, conductor and correction-domain bills must still be audited independently.

### B. Authority And Continuity

Actual trigger: 2026-11-10 17:11:01 EST, America/New_York. Run label 20261110-analytic-3/IR; platform RUN_ID_UNAVAILABLE. cross_route_ack=CROSS_ROUTE_SIGNED_RECOVERY_V1. Main fetched at f7947bee036c4dddb0c36fc9f53ab46b4fa90995. AGENTS blob c9c89f01b90b526de9f3e8ea92478e36504711b6; CURRENT_PROOF_CONTRACT blob 95566e37c8eaeb99ee680660df4f9d2e06ea5038; governing directive e922d4ba9362a1ae196af8f6de88f7417f92087c. Canonical VF, complete finite-wheel RH scale, finite A/C and RH remain OPEN.

All seven roles' November 10 and November 9 reports were retrieved; TODAY=AVAILABLE, YESTERDAY=CARRY_FORWARD at their actual scopes. Latest upstream claims include Coordinator MD, Owner DR, Wheel JC, Census UC, Referee SR and Lean RD. Own RD1-RD5 are independently paper-accepted in SR; merged #1130 certifies RD1 and its weighted adapters only. MD and SR's stronger endpoint proposals remain paper/self-audited until an actual independent review. External inbox remains 038018145c0fddb2f6306c0712373adf9cd1ea52, with no new entry after October 18; historical source/mask safeguards remain, not their stale task routing.

Direct hosted receipts checked: #1119 run 42552018910/job 128949473700 at 77ee815846d6d534c866f0752aa33b84c385610a SUCCESS, five transitive closures with standard axioms; #1130 run 42877550772/job 130044786387 at 4aa22782d10b3ad77dc970d6bb610eaab93a228c SUCCESS, four quantitative closures with standard axioms. Latest fifteen updated PR records are merged; a dedicated open collection and source-blob consistency check will be completed before final publication. The certified baseline remains b_base=7/8-7/(64*N_pack), with every positive exponent loss. No paper proposal is substituted for it.

### C. Preregistered Falsification And Work Remaining

Check the exact original signal definition for x>0, not merely x>=1. Check absolute convergence of the infinite kernel on the legal Mellin contour and in the proposed weighted growth class; retain frozen outer weights, phase, Gaussian, correction and exclusion masks. Test all local signs and all cross-slot products. A failure at small arguments, divergent kernel mass, or an unpaid raw-source hypothesis rejects the proposed extension.

Before numerical work: targeted tests will use exact Gaussian-rational phases, Q=k^8 with k in {3,4,7,11}, A in {0,1,-1,i,-i}, Mellin eighth-power samples, several finite geometric truncations, and complete two/three-slot weighted products. They test algebra/majorants, not prime-ideal distribution or an infinite theorem. Check the theta=3/5 boundary separately. No unchanged prime census or accepted RD1 scan will be repeated as purported novelty; all new tests must address the infinite-tail or small-argument question.

No new Lean, branch, PR, issue, workflow run, merge, agent launch or schedule change is authorized or performed. New derivation, complete-return audit, original-source bridge, independent review distinctions and final resume capsule are PENDING. Preserve all previous report content and claim IDs.

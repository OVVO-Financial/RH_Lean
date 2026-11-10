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

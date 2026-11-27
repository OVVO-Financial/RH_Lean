# V8 — remove nominal geometry; attack the actual local valuation and global cost

2026-11-25, research continuation on #1213. #1201 remains the final integration PR. No terminal RH theorem, weakening of a proof obligation, import of terminal RH, or claim that a synthetic local model proves the original period valuation. This is a paper-level arithmetic attack with exact finite diagnostics, not new Lean-certified declarations.

## 1. Source audit and scope

The [VerifyTask dashboard](https://riemann.verifytask.cn/?lang=en) reports 39 pillars and 92.23% archive-file coverage. The accessible page did not render the interactive matrix/dominator graph, so exact pillar IDs beyond the visible/readable source metadata were not inferred. Source-level trace at community commit [8e5cefee](https://github.com/leanprover-community/riemann-hypothesis/tree/8e5cefeeaffe7e4c12153385b7bb33fb7223c41a). The [Zeng audit](https://github.com/ArtificialZeng/Riemann-hypothesis-Auditing) describes 38 inputs of the original divClausesR_of. This version has divCoreClausesR_of and retains 38 named entries (37 in DivInputs0R, including eta-y, and val2); not all entries are independent propositions. The two fields Xc_unit and a_pos are not directly read in this refactored consumer, not evidence they are unused everywhere.

All 38 entries classified by immediate numerical consumer, not a claim that the complete transitive suppliers of every entry have been read:

| Branch | Actual fields | Immediate proof |
|---|---|---|
| Integral pairing (3) | Nu_lat, sg_fin, val2 | shiftEx; intoDual, divIntoDualShift, latticeGlue |
| Frame compatibility / positive rank (2) | Xc_unit, a_pos | carried data; no direct use in current divCoreClausesR_of |
| Real norm chain (8) | X0, base_matrix_det_unit, ch, hn, nP, cb, nKcb, eig6 | nK_of_cb; height_chain_atR; hn.le_hu; exists_cu |
| Covolume and index (15) | eb, heb, Sy, Sy_tw, G0, LG, E3, E2, gy, ηy, bi, bLG, biv, borderedMinorImage, twisted_third_sum_le | IndefSide.boundsMu, slope_bounds, specDet, reduction_lemma_zero, latticeGlue, ramBasic |
| Main term / combined errors (3) | El3, L3main, errB | base slope + period main comparison, R.divIneq |
| Level passage and scalar error (7) | Q, de0, deQ, Q1, Qb, la_le, constant_ge_twenty_eight | P.extra.passage; hpass; R.divIneq |

Source [ConstantGeTwentyEight, definitions and proof](https://github.com/leanprover-community/riemann-hypothesis/blob/8e5cefeeaffe7e4c12153385b7bb33fb7223c41a/src/Formalism/LocalToGlobal/Divisibility/ConstantGeTwentyEight.lean#L58-L300). The three outputs: integral map into RR dual; positive real norm bounds with mean log R.hu−meanLog kappa; dual slope minus meanLog kappa plus R.hu minus 2 FoOfR at most R.rhs. The original fourth shift-slope identity is handled outside this core comparison. [RecBridge](https://github.com/leanprover-community/riemann-hypothesis/blob/8e5cefeeaffe7e4c12153385b7bb33fb7223c41a/src/Formalism/LocalToGlobal/Divisibility/RecBridge.lean#L804-L870) supplies val2 separately from inp via val2AllAtRF. Keep actual hNu, hRR, hBk, shift, hTie, foTie, rhs; a record copying a height does not establish either numerical inequality.

## 2. The live valuation branch (independent of LinkG bookkeeping)

Read backwards:
- DivisionPackageFace.wordFacts -> divCoreClausesR_of and ServJointF.val2AllAtRF.
- [LocalQuadraticParts.adm2](https://github.com/leanprover-community/riemann-hypothesis/blob/8e5cefeeaffe7e4c12153385b7bb33fb7223c41a/src/Formalism/SharpRestriction/Divisibility/LocalQuadraticParts.lean) is a genuine period assertion, including field membership and valuation >= floor of ramification-scaled required order, for ALL actual admissible row and column vectors.
- [AdmissibleAtGeneratorPlaces](https://github.com/leanprover-community/riemann-hypothesis/blob/8e5cefeeaffe7e4c12153385b7bb33fb7223c41a/src/Formalism/LocalToGlobal/GroupLattices/AdmissibleAtGeneratorPlaces.lean#L428-L584): adm2 is supplied by admissible_level_two, famU, admissible_family_of_inclusion. Three cases: twist primes, generator primes, other primes. Other-prime case uses Serv.Conclusion1, actual InNP membership, gain comparison, period_geTU; vDG from denominator is added then subtracted. Do not use zeroCh or a formal quotient-length statement as a valuation bound for nonzero periods.
- The [Nov 21 working exposition hosted by Rubinstein](https://www.math.uwaterloo.ca/~mrubinst/alpoge_claude_grh/zeta-paper.pdf), sections III.5–III.7, independently traces ServF -> sum_over_primes_service -> split_bound_eleven_one -> thmA0p, and the underlying BeOK/ThetaExpansionAllPlaces/Loc.AdmB. The exposition quotes the actual theta-kernel integrality, covolume and several other suppliers rather than reproving them. Source proof not all read; see also [community reader's trace](https://github.com/leanprover-community/riemann-hypothesis/issues/5).

Size branch: height_chain_atR uses factorization of the actual map, bound on each operator norm (nP,nKcb), lower eigenvalue product (eig6), and the average height record. Covolume branch: IndefSide.boundsMu calls slope_bounds with the base local index and bordered-minor image bounds, then level passage and R.divIneq. The cited exposition identifies S1–S8, W1,W2,G and the shared period logOm as the numerical inputs. Particularly, the negative period term in the height and positive period term in L3main cancel on the SAME integral lattice. Retain the residual top coefficient and the mismatch p_j−k. Merely calling logOm a wheel density is not a comparison. These are immediate dependency groups; full constructor origins of the 37 base fields and ServF's actual pdv remain to trace.

## 3. Elementary local construction: height two directly from prime squares

For prime p and finite variable/site index set I with a permutation pi, set

    L_i(T)=sum_{e>=0} p^(-e) T_{pi^e(i)}^(p^(2e)).

Let g be its unique formal inverse (linear part identity). This is the formal-logarithm shape used by the local valuation argument, not an assertion that our constructed series equals the original period. All formal series below are over Q_p (rational coefficients in the explicit examples).

**Elementary proof of integrality of formal addition.** Let Phi substitute T_j^p² in all variables, and fix coefficients. For a vector a with zero constant term define

    D_i(a)=L_i(a)−Phi(L_pi(i)(a))/p
          =a_i+sum_{e>=1} (a_pi^e(i)^(p^(2e))−Phi(a_pi^e(i))^(p^(2e−2)))/p^e.

For integral a, a_j^p²≡Phi(a_j) mod p by Frobenius. Raising a congruence mod p to p^r raises its precision by at least r, by binomial theorem; numerator divisible by p^(2e−1), hence p^e. Conversely, if all D_i(a) integral, induct by total degree: correction terms in degree n involve only degrees <n; truncate a there and apply forward direction. The degree-n coefficient of a is integral. Thus D(a) integral iff a integral. Apply to a=g(L(T)+L(S)); D(a)=T+S. The resulting formal addition F(T,S) has integral coefficients in every degree, without constructing a variety.

**Explicit nonzero local B-model.** For an even cyclic orbit d, pi(s)=s−2, choose adjacent even s and odd s+1. Put

    A(T)=1+T_s^p T_{s+1};
    beta(X)=log A(g(X)).

The torus weights w_s=(-1)^s p^s modulo p^d−1 make L and g equivariant (w_pi^e(s)*p^(2e)=w_s in the residue ring). A is invariant because p*w_s+w_{s+1}=0. beta has rational coefficients, each monomial uses both parity classes, total degree >= p+1. For the mixed additive differences in one parity class, substitution by L gives

    exp(Delta_even beta) o L = A(F(T_even,S_even),T_odd) / (A(T) A(S_even,T_odd)),

and the analogous odd expression. They are integral formal series: F is integral, A's constant term is 1. This proves the local shape B1–B4 in all degrees for an explicitly constructed model, with U=1 if the kernel is exp beta. This construction does not reproduce the original kernel or its exceptional valuations; those have to be attached to the same arithmetic source, dimensions and size bound. Local beta may depend on p. A single nonconstant series cannot have every p-dependent torus invariance literally: an invariant monomial would have total degree divisible by p+1 for every p. Do not impose that false global condition.

**One-prime gain.** From L(g)=X, induction on degree gives
    v_p([X^nu]g_i) >= −(|nu|−1)/(p²−1)
because e <= (p^(2e)−1)/(p²−1). For an integral series A with zero constant term, its composition with g has the same bound (product with >=1 factors). For its nonzero degree-n one-variable derivative,
    v_p(n! c_n) >= v_p(n!)−floor((n−1)/(p²−1)).
Legendre digit sum gives local coefficient n*p/(p²−1) minus digit losses, precisely the odd-depth geometric factor sum_{h odd>=1} p^(−h). This is real local arithmetic, not the final global payment.

## 4. Shared all-prime rational kernel without geometry

The obvious concern is using unrelated local functions. Construct a single rational f(X)=X+sum_{n>=2} c_n X^n whose transforms f(L_p(T)) are p-integral for every prime p, and 0<c_n<=1 (no zero witness).

Induct on n. The coefficient of T^n in f(L_p(T)) is c_n+r_{p,n}, where r depends on earlier coefficients. For p²>n, r=0. For p²<=n, prescribe c_n=-r_{p,n} mod Z_p. For r=a/b, write b=p^k q, gcd(q,p)=1. Its p-primary fractional part is (a*q^{-1} mod p^k)/p^k; subtract the sum of these parts over p²<=n, then choose its unique representative in (0,1]. Every other summand is p-integral. This simultaneously satisfies all local constraints and the explicit real coefficient bound, with no appeal to RH or the observed prime discrepancy. f has radius at least 1. This is a scalar integral-jet model, not the original periods or a proof of actual simultaneous retained rank.

By section 3, f=(f o L_p) o g_p and v_p(c_n)>=−floor((n−1)/(p²−1)). Thus
    D_n = n! / product_p p^floor((n−1)/(p²−1))
is an integer dividing the strictly positive integer n!c_n. It is a nonzero divisibility certificate simultaneously at all primes, not just a set of local estimates on unrelated objects.

**Sharp scope limitation / quantitative obstruction.** Let c2=sum_p log(p)/(p²−1)=−zeta'(2)/zeta(2). By summing the floor errors at p<=sqrt(n) and bounding the convergent tail by the sum over integers,
    log D_n = n log n−(1+c2)n + O(sqrt(n) log n).
Numerically c2=0.569960993..., Euler gamma=0.577215664..., difference 0.0072546718... . The sign is certified without prime asymptotics: sum primes <=2000 using rational log upper bounds plus integral tail yields c2<0.575, and H_1000−log1000−1/1000>0.575 is a gamma lower bound. The attached script implements these rational checks. Therefore EVERY nonzero integer carrying this particular full-prime derivative divisor has real log size greater than n log n−(1+gamma)n by a positive linear amount eventually. It cannot by itself pay the principal centered upper bound at n^(1/2+eps). The local model is too rigid. This is a no-go for that particular scalar all-prime baseline, NOT an obstruction to the actual theorem J with class selectors, exceptional/ordinary contributions, rank and weighted losses; not a new bound on G. More local integrality is not automatically better if the cost at infinity is too high.

Exact test through degree 512: 8192 composition/valuation checks, nonzero rational coefficients and exact D_n divisibility at selected degrees. At 512, forced divisor log minus centered main=36.20371; actual derivative log minus main=298.90936. Floating logs are diagnostics. Rational constant gap proven by the stated inequalities.

## 5. Attack next: a real joint estimate, not a new assumed endpoint

Use original G(N) and square-clock handoff from #1205. Preserve class selectors, actual Frobenius/inertia, signed prime-power source, all gains, exceptional generator/lattice cost, normalizer and all real terms. In particular:
- local arithmetic: attempt to replace actual height-two kernel suppliers by a native integral-jet construction with a proved evaluation tie and nonzero actual period pairing. Reuse the existing NativePrimeExponentJet and NativeJointEvaluationRecovery; do not treat a unimodular decoder as a positive index. Our explicit B-model proves that one local shape/integrality property can be elementary.
- cross-prime gain: map the original odd-depth loss and signed partner terms to physical Euler/Perron cofactor coordinates. Do not replace actual source by n! or the model D_n. Quantify actual clipped and exceptional directions on the same frame.
- global size: eliminate common period normalization algebraically in the combined norm/dual-covolume comparison BEFORE seeking geometric realizations. Construct both Gram determinants on identical arithmetic frames; prove the actual log-index correction and remaining top term. An assigned height or arbitrary scalar rescaling adds no capacity. Use the lower-rank slice only after retaining the actual rank/slope comparison.
- verify the three original numerical obligations on one coherent instance/family, not different artificial witnesses; keep full error bounds and fixed complete windows. The local result here is only progress on the construction problem, and the global real-size inequality, actual map attachment, admissible family and RH-strength estimate are still open in RH_Lean.

Priority is mathematical dependency minimization, not token compression or proof-count reduction. The dashboard core percentages are navigation and verification telemetry, not proof of these native suppliers. No runtime retask, merge or main change. This update adds research documentation and a reproducible Python diagnostic, not Lean declarations.


## V9 — controlling height-free refinement

[Height-free joint comparison and root-scale native frame control](RHLEAN_HEIGHT_FREE_JOINT_FRAME_ATTACK_20261125.md) supersedes geometric height reconstruction as a research requirement. Actual norm, valuation, covolume, rank and signed payment remain. Log-free distributional frame refinement and native high-prime Gram/common-range bounds are paper results; no terminal signed estimate.

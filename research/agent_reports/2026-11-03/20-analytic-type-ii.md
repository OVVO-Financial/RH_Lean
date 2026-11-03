# RH | Analytic Type II - 2026-11-03

**New paper result:** an explicit constant-mode correction to the full logarithmic Mobius approximant makes its genuine infinite Hilbert tail beyond ceil(N^(3/2)) at most 334/(3 log(N)^2). All constants are absolute. The correction's entire finite-range contribution is retained. The central weighted residual remains OPEN; no new endpoint gain or RH proof is claimed.

## Early Research Checkpoint

Status: PARTIAL / IN_PROGRESS. Scheduled invocation began 2026-11-03 01:04:01 EST (-0500); RUN_ID_UNAVAILABLE. This is the first Analytic invocation of this day observed in the reporting branch.

### A. Mathematical question

Resume the protected NYMAN investigation from 20261102-analytic-1 equations (32)-(43), as assigned by 20261102-coordinator-3. Compare the exact-head Mobius interpolant with logarithmically damped coefficients on the literal basis a_k(m)=(m mod k)/k. Develop a signed Fourier/Gram bound for the infinite weighted tail, keeping the constant Fourier mode and all overlapping rational frequencies. The aim is an independently proved uniform tail inequality or a precise scoped failure, not a finite optimum or a renamed density hypothesis.

### B. Authority and evidence

Main: 8e5d64ae689b39dabd2a4f6eb33efe4d5d192015.
AGENTS.md: 9fa5e9519e2fb6dde22217aa2a18982dafef373a.
CURRENT_PROOF_CONTRACT.md: 88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a.
Selector: d05c327ae694ea54b599dab0a21032a056b521f1.
Broad-search policy: b5c063c51556ba57c4b25bcc380a606fa8daa207.
Complete-return contract: 16838f7f3c8724b970f8b8ece0bceaab9418066d.
Research engine: 6fce99c61efb5b2a73c0cb1f1464f09b351fcd55.
NYMAN source: research/NYMAN_BEURLING_POSITIVE_RESIDUE_ATTACK_2026_10_15.md, blob b2775c892edffe920a101651eef6f3581c73c9d4.
Mertens converse: research/MERTENS_CONVERSE_IDENTIFICATION.lean, blob 768c8255850bf4074aff265c3fe17a1f5c43979b.

Canonical actual-prime VF von Koch statement and RH remain OPEN. Main contains the non-strict native 7/8 replay, blob ff963b716bc2066c2312d9237764e39898f1cdb8.

Important newer evidence: Referee 20261102-referee-3 independently accepts the strict gain on draft PR #1073 at 9cbfce5295343bcb411e6d2cb159b59995cd985b. This invocation fetched its terminal Lean files, all 13 successful attached workflows and the successful job 125650160501 logs: exact unconditional endpoints, standard axioms and live dependency audits pass. This is VERIFIED_ETA / PR_HEAD_ONLY, not main, not RH and not a sharp-shell theorem. No new independent re-audit of the unchanged full proof is claimed. #1074 has 7/7 green runs but its strengthened scope needs independent review; #1075's current dedicated run fails; #1076's current 8 returned runs succeed. These are scoped observations, not automatic promotion or merge.

Continuity: November 2 Coordinator mirror blob 1e932d4ce0eb0fd2c5f4507f6b111194d633eb32; Owner abfe546d72b151f4cd200fc61de3197efe23a65c; Analytic 8e48b59611aa1d0bfa3577ed0a4a3bc0d0fcae73; Wheel abf8ac8c22a708886183849552c90dd62787ac8d; Census 2cd84c57ab18d923e97368764f29f4ccd2ec3bb3; Referee 814af1684df66e6ac99b8df1f102cb592b316f89; Lean 02d19d792e26f072004cb5909f149538752626e9. Today's Owner claim 20261103-owner-1, blob 5c085d12ca455327b2a9ab42d7e55a1b6b2d631b, is available. Today's Coordinator/Wheel/Census/Referee/Lean: TODAY=PENDING; use YESTERDAY=CARRY_FORWARD. External inbox 038018145c0fddb2f6306c0712373adf9cd1ea52 has no entry after October 18; its dated routing is superseded, its scoped carrier warnings remain.

Correction preserved: the accepted odd-prime operator constant for 20261102-analytic-2 is Referee's 2/(9 sqrt(3)), not the original submitted integral-test value. Coordinator C25 pays the previous cutoff-activation bill; it is not today's missing theorem.

### C. Execution plan and deployment acknowledgement

Deployment_ack: current main and policy consumed; selected NEXT-ANALYTIC / NYMAN continuation. Previous actual route sequence was NYMAN, OAI-NNS, CODIV on November 2. This invocation resumes NYMAN; OAI-NNS is next due. Compare exact interpolation and log taper, derive the complete weighted tail from the exact periodic Gram, and audit zero-mode retention, growing modulus separation and the middle-range cost.

No new mathematical theorem is asserted at this checkpoint. New-run endpoint gain UNKNOWN; independent review of any new result PENDING. No local Lean, proof-source modification, PR mutation, other-report edit, agent launch, schedule change or merge is performed.

---

## Final Research Synthesis - Claim 20261103-analytic-1 - 2026-11-03 01:25 EST (-0500)

Scheduled 01:04:01 EST invocation, not a second run. Mathematical work finished; publication verification is recorded separately below.

Classification: PAPER_PROOF / SOURCE-FAITHFUL UNIFORM INFINITE-TAIL BOUND; EXACT FINITE RESIDUAL; SELF_AUDIT; INDEPENDENT_REVIEW_PENDING; NOT_FORMALIZED. No claim of external-literature novelty.

### A. Most Important Analytic Development

The previously unpaid infinite tail can be bounded on a substantially shorter explicit cutoff for a modified logarithmic coefficient family. For every integer N>=2, the coefficients defined in section D satisfy

```text
T_N = ceil(N^(3/2)),
sum_(m>T_N) |1-sum_(2<=k<=N)c*_k a_k(m)|^2/[m(m+1)]
  <= 167(1+N^(-1/2))/(3 log(N)^2)
  <= 334/(3 log(N)^2).                                  (N1)
```

This is unconditional: no RH, prefix Mertens bound, zero-free region, ideal-character input, finite-A/C assertion, or statistical independence is used in (N1). It uses the classical large sieve on the actual rational Fourier frequencies, with their common-frequency contributions combined exactly, and an elementary gcd covariance formula. The principal Fourier mode is removed by an explicit admissible coefficient correction, not silently discarded.

The result does not control the full norm. It gives a finite-range research target with a rigorously paid infinite tail. A separate estimate proves that the correcting function can have norm comparable to the square of its constant-mode mass divided by N; it must remain inside the complete residual.

### B. Current Mathematical Objective And Evidence

Canonical objective on current main remains

```text
exists C>=0, forall integers R>=2,
  |pi(R^2)-VF_can(R^2)| <= C R log R.
```

The selected NYMAN route uses exactly the paper/literature carrier in [the registered source](https://github.com/OVVO-Financial/RH_Lean/blob/8e5d64ae689b39dabd2a4f6eb33efe4d5d192015/research/NYMAN_BEURLING_POSITIVE_RESIDUE_ATTACK_2026_10_15.md), not an asserted Lean definition of Nyman density. Its full L2 convergence criterion is a sufficient RH route; no formalized density consumer is claimed here.

Material files inspected at main 8e5d64ae689b39dabd2a4f6eb33efe4d5d192015:

| Source | Blob | Scope used |
| --- | --- | --- |
| research/NYMAN_BEURLING_POSITIVE_RESIDUE_ATTACK_2026_10_15.md | b2775c892edffe920a101651eef6f3581c73c9d4 | Literal basis, weights, omission and Burnol safeguards |
| research/MERTENS_CONVERSE_IDENTIFICATION.lean | 768c8255850bf4074aff265c3fe17a1f5c43979b | growthAtMost_iff_strip; growthExponent_eq_rightmost; half-line criterion |
| research/MERTENS_EXPONENT_STRIP_MAP.lean | 4e1bb2fde30e69591d62bcdaf1208b845597e573 | Actual Mobius Mellin identity and power-bound continuation |
| research/oai_434/VF919NativeSevenEighthsReplay.lean | ff963b716bc2066c2312d9237764e39898f1cdb8 | nativeReplay_mertens_growth; complete square-of-sum scope |
| RHLean/Analysis/FiniteTorusFourierPairing.lean | 63155c8f6d174786ab8a337a96b786bac7019e1d | Existing finite Fourier pairing, not the new tail inequality |

At independently accepted PR #1073 head 9cbfce5295343bcb411e6d2cb159b59995cd985b, the inspected terminal sources have blobs b33a4883e1ddb0551b0f11f062bce46680d87450 (VF919NativeStrictMertens.lean) and efbf2780f0b453a702fb8847f2d360d8faf0fa66 (VF919NativeStrictSevenEighths.lean). The original Mertens transfer and unconditional quantified statements were inspected, not inferred from a PR title. All thirteen returned workflows succeed; [job 125650160501](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41554561404/job/125650160501) prints the exact endpoint, standard axioms, and the successful live-dependency audit. Referee 20261102-referee-3 accepts that same scope. Hence the existing programme gate is VERIFIED_ETA / PR_HEAD_ONLY, not a new result of this invocation and not main. No allocation change or merge follows.

The November 2 Lean report's third invocation remains a partial checkpoint, not a fabricated completed handoff. Latest observed #1074 and #1076 are exact-head CI green but their stronger scopes are not independently reviewed here; #1075's dedicated proof workflow fails at its observed head. The current task does not modify any of these branches.

### C. Mechanism And Comparison

The exact-head construction of 20261102-analytic-1 forces c_k=-mu(k) below the interpolation cutoff and a nontrivial reciprocal completion. Its first omitted block is a fitted Mertens increment. The established estimate N K^(2 beta-2), K<N and beta>1/2, remains nondecaying. It is a method loss, not a lower bound for the actual norm.

The different construction developed here tapers every Mobius coefficient logarithmically and redistributes the periodic constant mode over the top half of the available moduli. It does not demand exact head interpolation. Rational-frequency separation is only N^(-2), but the completed Fourier variance is O(N/log(N)^2), rather than an absolute coefficient square of order N^2/log(N)^2. Summation against the exact decaying Hilbert weights then pays the far tail at N^(3/2).

The logarithmic taper is classical, not a claimed invention. Bettin-Conrey-Farmer use the Dirichlet polynomial sum_(n<=N) mu(n)(1-log(n)/log(N)) n^(-s). Their Theorem 1 assumes RH and a fixed positive saving in sum_(|Im rho|<=T)|zeta'(rho)|^(-2) << T^(3/2-delta), implicitly including simple zeros. Their conditional full-norm asymptotic is NOT used here. Their uncentered Mellin norm is also not silently identified with this corrected centered carrier. [Primary paper, Theorem 1](https://arxiv.org/pdf/1211.5191).

### D. Exact Formulation

All coefficients below are real. Fix an integer N>=2 and put L=log(N). For k>=2 and integers m>=0, retain

```text
a_k(m) = (m mod k)/k,
alpha_k = (k-1)/(2k),
f_k(m) = a_k(m)-alpha_k,
D_N(c)^2 = sum_(m>=1) |1-sum_(k=2..N)c_k a_k(m)|^2/[m(m+1)].
```

The functions a_k and the norm are unchanged. The auxiliary f_k is only their exact periodic centering. Define

```text
w_k = log(N/k)/L,
c_k = -mu(k) w_k,                         2<=k<=N,
I_N = {floor(N/2)+1,...,N},
b_N = 1-sum_(k=2..N)c_k alpha_k,
h_N = sum_(k in I_N) alpha_k,
d_N = b_N/h_N,
c*_k = c_k + d_N 1_(k in I_N).                          (N2)
```

Here d_N is a correction coefficient, NOT the optimized Nyman distance. Every quantity is explicit in the genuine Mobius coefficients through N. In particular h_N>=N/8>0 and

```text
sum c*_k alpha_k=1,
r*_N(m):=1-sum c*_k a_k(m) = -sum c*_k f_k(m).           (N3)
```

Define the exact nonnegative periodic covariance form

```text
V_N(v) = (1/12) sum_(k,j=2..N) v_k v_j
                            (gcd(k,j)^2-1)/(k j).
```

The general tail theorem, valid for every real coefficient vector v and every integer T>=0, is

```text
sum_(m>T) |sum v_k f_k(m)|^2/[m(m+1)]
 <= V_N(v) [1/(T+1)+N^2/((T+1)(T+2))].                 (N4)
```

The constants are absolute and uniform in N,T,v, with no restriction that T exceed a common period or even N. For a nonzero constant residual b, the valid companion bound is

```text
sqrt(tail(b-sum v_k f_k))
 <= |b|/sqrt(T+1)
    +sqrt(V_N(v)[1/(T+1)+N^2/((T+1)(T+2))]).
```

Thus (N4) is never applied to an unremoved principal mode.

### E. Proof And Quantitative Derivation

**1. Exact shared-divisor covariance.** For g=gcd(k,j), average over m modulo lcm(k,j). Conditional on r=m mod g, the remaining residues modulo k/g and j/g are independent under the finite uniform CRT parameter. This is an exact finite bijection, not a probabilistic assumption about primes or Mobius values. The conditional centered means are (r-(g-1)/2)/k and (r-(g-1)/2)/j. Therefore

```text
average_m f_k(m) f_j(m) = (g^2-1)/(12 k j).              (N5)
```

It follows that V_N(v) is the exact full-period mean square of sum v_k f_k, including every shared-frequency cross term.

**2. Classical large sieve with all parameters checked.** The external input is the following finite theorem: for distinct frequencies theta_r modulo 1 with circular spacing at least delta>0, arbitrary complex z_r, integer B, and positive integer J,

```text
sum_(B<m<=B+J) |sum_r z_r exp(2 pi i m theta_r)|^2
 <= (J+delta^(-1)) sum_r |z_r|^2.
```

This is the dual form of Montgomery-Vaughan's large sieve; the sharper minus-one version is unnecessary. Duality follows from equality of the finite matrix and adjoint operator norms. The constant is absolute and effective. [Original paper, Mathematika 20 (1973), 119-134](https://doi.org/10.1112/S0025579300004708); [authors' exposition, Theorem 19.4 and duality discussion](https://personal.science.psu.edu/rcv4/571s25/montgomery-vaughanII.pdf).

Expand the finite periodic functions f_k in discrete Fourier series and COMBINE equal fractions h/k before applying the theorem. Each remaining denominator is at most N, so distinct circular frequencies differ by at least N^(-2). Finite Parseval and (N5) identify the sum of the squared combined coefficients with V_N(v), not the sum of uncombined moduli's diagonal energies. Consequently

```text
A(J):=sum_(T<m<=T+J)|sum v_k f_k(m)|^2
 <= (J+N^2)V_N(v).
```

For w_m=1/[m(m+1)], summation by parts gives the tail as sum_(J>=1) A(J)(w_(T+J)-w_(T+J+1)). All terms and weights here are nonnegative. The exact identities

```text
sum_(J>=1) J(w_(T+J)-w_(T+J+1)) = 1/(T+1),
sum_(J>=1)  (w_(T+J)-w_(T+J+1)) = 1/((T+1)(T+2))
```

prove (N4). Boundary terms tend to zero, either by the displayed A(J) bound or periodic boundedness. The original weighted series is absolutely convergent for every fixed N; there is no exchange of conditionally convergent Fourier or arithmetic series.

**3. Uniform variance of the logarithmic taper.** For any real v with |v_k|<=w_k, use gcd(k,j)^2=sum_(d|k,d|j) J_2(d), where 0<J_2(d)<=d^2. Adding the nonnegative k=1 and j=1 majorant terms gives

```text
V_N(v) <= 1/(12 L^2) sum_(d<=N)
                  [sum_(a<=N/d) log(N/(d a))/a]^2.
```

For y>=1 the inner sum is at most log(y)+(log(y))^2/2 by decreasing-function integral comparison. A second such comparison, extending the integrable majorant to d=0, gives

```text
sum_(d<=N)[log(N/d)+(log(N/d))^2/2]^2
 <= N integral_(0..1)[log(1/t)+(log(1/t))^2/2]^2 dt
 = 14N.
```

The last constant is 2!+3!+4!/4=14. Hence V_N(c)<=7N/(6L^2). The same argument with H_floor(y)<=1+log(y), whose squared integral is 5, gives V_N(1_(I_N))<=5N/12.

**4. Pay the entire constant-mode correction.** Since |b_N|<=1+(1/2)sum w_k<=N/L, and h_N>=N/8, one has |d_N|<=8/L. Positivity of the covariance form yields

```text
V_N(c*) <= 2 V_N(c)+2 d_N^2 V_N(1_(I_N))
         <= (7/3+160/3)N/L^2
         = 167N/(3L^2).                                 (N6)
```

This estimates the actual completed square and therefore retains its mixed interactions. Using (N3), (N4), and T_N>=N^(3/2) proves (N1).

**5. Exact restoration on EVERY coordinate.** Define

```text
B_N = sum_(k<=N) mu(k) log(N/k)/k,
psi(m) = sum_(n<=m) Lambda(n),
U_N(m) = sum_(N<k<=m) mu(k) log(N/k) floor(m/k),
H_N(m) = sum_(k in I_N) a_k(m).
```

Then, with U_N(m)=0 when m<=N,

```text
r*_N(m) = [m B_N-psi(m)+U_N(m)]/L - d_N H_N(m)           (N7)
```

for every integer m>=1. Indeed sum_(k<=m)mu(k)floor(m/k)=1 and sum_(k<=m)mu(k)log(k)floor(m/k)=-psi(m). Subtract the omitted k>N terms, including their NEGATIVE logarithms, then restore the correction in (N2). No prime power, residual, or correction has been discarded.

**6. The correction is not free in the full Hilbert norm.** Its separate squared norm satisfies

```text
b_N^2/(6N)
 <= sum_(m>=1)|d_N H_N(m)|^2/[m(m+1)]
 <= 128 b_N^2/N.                                        (N8)
```

For the lower bound, put q=floor(N/2). On m<=q, H_N(m)=m sum_(k in I_N)1/k, the reciprocal sum is at least 1/2, and sum_(m<=q)m/(m+1)>=q/2>=N/6. Thus ||H_N||^2>=N/24; also h_N<=N/2. For the upper bound the reciprocal sum is at most 1, so H_N(m)<=min(m,N), giving ||H_N||^2<=2N; combine h_N>=N/8. All constants hold for N>=2.

This forbids describing periodic mean cancellation as a harmless full-norm perturbation without additional control. It does not forbid cancellation between that correction and the rest of (N7).

### F. Scale Comparison And A Paid Initial Range

At the SAME cutoff T_N, the elementary coefficient-majorant certificate gives only

```text
tail <= (1+sum|c*_k|)^2/(T_N+1)
     <= 100 sqrt(N)/L^2,
```

because sum|c*_k|<=9N/L. The new bound (N1) removes that growing sqrt(N) factor. Both statements are upper bounds; the first is not a lower bound or an assertion of actual growth.

The known pointwise Mertens theorem may separately control a very short initial range, not the whole norm. Here is the full quantitative dependency. Fix 0<beta<1 and C>=1 such that |M(t)|<=C t^beta for every real t>=1 (M(t)=M(floor t)). Put

```text
E_N = C N^(beta-1)[1/(1-beta)+1/(1-beta)^2],
s_N = sum_(k in I_N)1/k,
C_N = B_N-L d_N s_N.
```

Abel summation and the simple pole of zeta at 1 give

```text
|B_N-1| <= E_N,
|C_N-1| <= E_N(1+4/N)+8L/N+4/N+(4C/beta)N^(beta-1).     (N9)
```

For completeness, the convergent Mobius series at s=1 and its derivative equal 0 and 1 respectively: sum mu(k)/k=0 and sum mu(k)log(k)/k=-1. These follow by Abel-holomorphy for Re(s)>beta, the absolutely convergent reciprocal-zeta identity for Re(s)>1, and continuation at the simple pole. The tails and differentiated tails converge uniformly on compact subsets strictly to the right of beta. Thus

```text
B_N-1 = integral_(N..infinity)
             M(t)[log(t/N)-1]t^(-2) dt.
```

Its absolute bound is E_N. Also S_N:=sum_(k<=N)mu(k)log(N/k)/L satisfies |S_N|<=C(N^beta-1)/(beta L), while b_N=1+(S_N-B_N/L)/2. Use s_N<=1 and h_N>=N/8 to obtain (N9). All constants and their dependence are displayed; beta is fixed before N.

For N above the resulting threshold, |C_N|<=2. On m<=floor(N/2), (N7) becomes (m C_N-psi(m))/L. Since psi(m)<=m log(m), the initial range Y_N=floor(log N) then obeys

```text
sum_(1<=m<=Y_N) |r*_N(m)|^2/[m(m+1)]
 <= Y_N[2+log(Y_N)]^2/L^2
 <= [2+log L]^2/L -> 0.                                (N10)
```

Take N>=3 so Y_N>=1. The necessary sublinear prefix input is already available from main, for example at beta=15/16 by spending the positive loss in nativeReplay_mertens_growth. PR #1073 permits a fixed beta strictly below 7/8, but that stronger input is not needed for (N1), and it does not settle the remaining middle range. A bound on the correction alone using this prefix input still permits a growing N^(2 beta-1)/L^2 upper bill when beta>1/2; no decay is inferred from it.

### G. Original-Carrier Bridge And Exact Remaining Bill

The complete reconstruction is the literal partition of the registered norm:

```text
D_N(c*)^2 = initial_N + middle_N + tail_N,
initial_N = sum_(1<=m<=Y_N) r*_N(m)^2/[m(m+1)],
middle_N  = sum_(Y_N<m<=T_N) r*_N(m)^2/[m(m+1)],
tail_N    = sum_(m>T_N) r*_N(m)^2/[m(m+1)].
```

The tail is paid by (N1), and the initial range by (N9)-(N10) with the known fixed sublinear Mertens input. The first unsupported assertion is middle_N -> 0, with the ENTIRE expression (N7) inside the square. Equivalently the numerator in (N7), including -L d_N H_N(m), needs weighted square sum o(L^2) on this growing window. It is not permissible to discard the correction, replace mu by a density, or treat U_N as independent of psi and B_N.

If that assertion were independently proved for this explicit sequence, full norm convergence and the classical integer-dilation criterion would imply RH. No such assertion is proved. It is a sufficient RH-strength supplier and is equivalent to convergence of this particular family given the paid ranges; no converse from RH to this corrected family's convergence is established. The result therefore does not claim a weaker independently solved endpoint condition.

NYMAN has no asserted occurrence-preserving identification with the original masked VF owner source, rational square-shell energy, or ideal-character LOW/HIGH probe. Its legitimate consumer is its own Hilbert criterion. The merged Mertens converse remains an available exact exponent translator, not an extra quantitative estimate.

### H. Falsification, Computation, And Circularity

The dangerous shortcut of omitting the constant Fourier mode is false on the actual base logarithmic family already at N=2: every base c_k is zero, V_N(c)=0, but its residual is 1 and its tail is 1/(T+1). The corrected family has c*_2=4, squared residual identically 1, and satisfies (N4). This is a regression for the exact mode restoration, not a disproof of asymptotic convergence.

The sharper full-norm proposal D_N(c*)^2=O(L^(-2)) is excluded by the existing Burnol obstruction. More precisely, the centered span is contained in the dilation span with theta>=1/N after extension by zero outside (0,1). Burnol's lower bound therefore supplies c_B>0 with liminf L d_opt,N^2>=c_B. Since L tail_N ->0 by (N1),

```text
liminf_(N->infinity) L sum_(m<=T_N)r*_N(m)^2/[m(m+1)]
 >= c_B > 0.                                           (N11)
```

Thus the unavoidable logarithmic lower mass is localized to the finite core for this family. There is no contradiction with a tail of order L^(-2). This uses Burnol only at its stated distance/lower-bound scope, with zeros counted with squared multiplicity. [Primary source, Theorem 1.3](https://arxiv.org/pdf/math/0103058). No fixed-square contraction below 1/2 is proposed.

The omit-six safeguard is respected: for every fixed k, once N>2k the correction does not change c_k, and c*_k=-mu(k)(1-log(k)/L) tends to -mu(k). In particular modulus 6 is not removed. This necessary coefficient limit is not sufficient for density.

Executed small regressions, not an enlarged census:

- Exact Fraction arithmetic verified (N5) for all 361 ordered pairs 2<=k,j<=20.
- For N=2,...,9 and four deterministic rational vectors v_k=(((7k+3s) mod 11)-5)/(s+3), s=0,1,2,3, exact full-period means verified both b^2+V_N(v) and the corrected zero mean: 32 vector checks.
- Those corrected vectors passed 128 partial-tail comparisons with (N4), at T in {0,1,N,N^2}, summing the next 60 terms. This does not numerically certify an infinite tail; the analytic proof does that.
- The logarithmic family was checked at 80 decimal digits for N in {2,3,4,6,8,12,16,24,32}, with T=ceil(sqrt(N^3)) and every 1<=m<=4T. The direct residue residual and (N7) agreed within 2.392e-77; zero means, |d_N|<=8/L, and (N6) passed. These are high-precision diagnostics, not interval certificates.
- The computed finite core is not monotonically decreasing: it is approximately 0.05178 at N=8, 0.06754 at N=16, and 0.06856 at N=32. These observations supply no support for an all-scale decay claim and motivate keeping the central estimate explicitly open.

Reproducer: a standard-library Python script using Fraction, Decimal precision 80, exact gcd/lcm and a prime-multiple Mobius sieve; SHA256 c3792f798e91f10f59a3f136064798c702e11c9db1fcafb8ffbd4abcddc522ff. The deterministic vectors, all ranges, and all compared formulas are specified above. psi is independently formed from -sum_(d|n)mu(d)log(d); base residuals are computed directly from remainders. An initial attempt to import unavailable mpmath failed before any check ran; it was replaced by standard-library Decimal, after which all stated checks ran successfully. No Lean was executed.

Novelty search covered the main filename tree, registered NYMAN source and experiment inventory, actual finite Fourier-pairing declaration, and the November 1-2 Analytic/Coordinator/Referee derivations. No compiled (N1)-(N8) or this corrected family was located in that scoped search. The large sieve, covariance algebra and log taper are classical ingredients; the contribution here is their proved source-faithful combination, explicit correction budget and finite-core localization. This is not an exhaustive literature-novelty claim.

### I. Conceptual Interpretation

The infinite tail need not be paid by the square of the coefficient L1 norm. Its periodic arithmetic covariance exposes a smaller spectral energy once duplicate rational frequencies are aggregated. An explicit top-band correction handles the coherent constant mode without changing the admissible basis.

This does not make the proof easy: the correction can move appreciable energy into the early and intermediate coordinates. The complete formula shows exactly where. The current result advances quantitative tail control and rules out treating that control as full density. The next NYMAN investigation should attack the joint middle residual, not rederive the paid remote tail or repeat a finite Gram optimum.

### J. Specialist Handoffs

**Coordinator:** register 20261103-analytic-1 as a paper uniform tail theorem with absolute constants, not an endpoint gain. Retain the current VERIFIED_ETA status only at independently accepted PR #1073. Keep this NYMAN candidate distinct from CODIV and OAI-NNS.

**Adversarial Referee:** reconstruct (N5), the combined-frequency Parseval step, dual large-sieve hypothesis and Abel weights in (N4), then audit constants 14, 5, 167/3 and both sides of (N8). Give separate verdicts on the unconditional tail and the prefix-input-dependent early range (N9)-(N10). Check that (N11) invokes Burnol only for the finite core, never the tail alone.

**Prime Census:** no broader scan is requested. If selected, freeze a small set of N and compare the uncorrected log family, the exact-head interpolant, and c* using separate early/middle/tail statistics. Preserve the sign of the correction cross term and the N=2 principal-mode regression. A growing correction-only norm does not falsify joint cancellation; finite decreases do not prove density.

**Owner Payment:** no prime-owner source bridge is asserted or requested. Any proposed cross-route use must map the actual residues/weights rather than identify them with owner-return cells by analogy.

**Finite Wheel:** the finite CRT covariance (N5) is an eligible structural cross-check, but it is not a wheel density argument for primes or an independence assertion on Mobius signs. No change to the due CORR4 investigation is requested.

**Lean Verification:** no new branch is requested. After independent acceptance and utility review, (N5) and the finite coefficient-correction bounds are implementation-sized; (N4) additionally needs a suitable large-sieve theorem. Do not encode that theorem or middle_N ->0 as an unproved project axiom, and do not displace the existing qualified proof work with a conditional density wrapper.

### K. First Independently Missing Analytic Theorem

For the EXACT coefficient schedule (N2), establish a uniform bound tending to zero for

```text
sum_(floor(log N)<m<=ceil(N^(3/2)))
  |m B_N-psi(m)+U_N(m)-log(N)d_N H_N(m)|^2
  /[log(N)^2 m(m+1)].
```

All parameters are functions of N fixed in advance; there is no fitting to a chosen test window. A rate O(1/log N) would be compatible with the known lower obstruction, but is only a proposed stronger target. No proof or theorem supplier for even o(1) is established. The exact arithmetic ingredient needed is cancellation in the complete truncated divisor/prime-power/correction combination, not a pointwise bound on M alone.

### L. Persistent Workspace And Resume Capsule

```text
ENGINE_VERSION: 2026-11-01; policy 6fce99c61efb5b2a73c0cb1f1464f09b351fcd55.
MAIN: 8e5d64ae689b39dabd2a4f6eb33efe4d5d192015.
RUN: scheduled 2026-11-03 01:04:01 EST (-0500); RUN_ID_UNAVAILABLE.
TASK: NEXT-ANALYTIC / due NYMAN continuation.
CLAIM: 20261103-analytic-1; equations N1-N11.
RESULT: unconditional O(log(N)^(-2)) remote Hilbert tail at N^(3/2),
        exact gcd/Fourier transfer, and fully restored correction cost.
REVIEW: SELF_AUDIT; independent Referee PENDING; not Lean formalized.
NEW_RUN_ENDPOINT_GAIN: UNKNOWN; none established.
PROGRAMME_GATE: VERIFIED_ETA only at PR1073@9cbfce5295343bcb411e6d2cb159b59995cd985b.
MAIN_GAIN_SCOPE: non-strict 7/8; no strict main promotion.
FIRST_OPEN: complete finite middle residual in section K.
NYMAN_LAST: this invocation; resume N7 plus section K, not the tail proof.
OAI_NNS_LAST: 20261102-analytic-2, with Referee R24's corrected constant;
             covariance remains distinct from the amplitude-only no-go.
CODIV_LAST: 20261102-analytic-3; Coordinator C25 pays activation error;
           signed old-owner covariance and original-shell bridge remain open.
ROLLING_COVERAGE: OAI-NNS, CODIV, NYMAN over the latest three actual runs.
NEXT_DISTINCT_ROUTE_DUE: OAI-NNS, subject to a concrete review repair.
CANONICAL_VF: OPEN. FULL_NYMAN_DECAY: OPEN. SHARP_SHELL_GAIN: OPEN. RH: OPEN.
```

Prior claim IDs and corrections are preserved. The strict PR-head result does not pay this new middle residual; the new tail theorem does not improve that PR's endpoint exponent. No other agent was launched and no future execution is claimed.


## Publication Verification - 2026-11-03 01:26 EST (-0500)

Execution/publication status: COMPLETED / PUBLISHED_AND_READBACK_VERIFIED. This does not upgrade the mathematical status beyond PAPER_PROOF / SELF_AUDIT / INDEPENDENT_REVIEW_PENDING.

The early checkpoint was committed as a33eb9a905ea091039cbbb2143365f5ed7a9dd70 and read back at blob 446165a0e3877882c113044bc167bb08375ead0e. The substantive synthesis was committed as 5bad2cffb6206a42ce8ef9b21880f46135a13476 and read back byte-for-byte at blob e4eb86da5dde00c270b52a950abae630d5c17d7f (29407 characters). Commit inspection confirms that only research/agent_reports/2026-11-03/20-analytic-type-ii.md changed. All A-L sections, N1-N11, explicit constants, the full correction, pending independent review, and the exact middle-range obligation were present. The final main refresh remained 8e5d64ae689b39dabd2a4f6eb33efe4d5d192015; today's missing upstream reports remain PENDING.

The local report passed ASCII/control-character and balanced-code-fence checks. This receipt records successful publication and preserved checkpoint history, not independent acceptance, Lean certification, a new endpoint gain, or RH.




---

## Scheduled Continuation Checkpoint - 2026-11-03 09:13 EST (-0500)

**Execution:** PARTIAL / IN_PROGRESS. Scheduled invocation began 2026-11-03 09:09:02 EST, America/New_York; RUN_ID_UNAVAILABLE. This is the second actual Analytic invocation observed today. The completed 01:04 NYMAN invocation and its publication history above are preserved.

**Current authority:** main `acffafc79df1a3713e77dcd14eb551b7413d00c2`; AGENTS `9fa5e9519e2fb6dde22217aa2a18982dafef373a`; proof contract `88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a`; engine `6fce99c61efb5b2a73c0cb1f1464f09b351fcd55`; complete-return contract `16838f7f3c8724b970f8b8ece0bceaab9418066d`. The selector, breadth policy, current role prompts, dynamic protocol and multirun policy were retrieved from this main.

**Changed formal state:** #1073 and the stacked #1074-#1076 work have now been human-merged, the latter through integration #1077. The open/draft PR list is empty. The inspected main strict-Mertens terminal source is byte-identical to independently reviewed #1073's file, blob `b33a4883e1ddb0551b0f11f062bce46680d87450`. Exact-head CI refresh and integration provenance checks are in progress. Earlier PR_HEAD_ONLY statements above are historical; no claim is made that a merge alone is a new proof or a fresh integration build. Canonical actual-prime VF, RH and sharp local shell improvement remain OPEN.

**Continuity:** all available November 2 and November 3 named role reports and the external inbox were retrieved. TODAY=AVAILABLE for every named role. Latest Coordinator claim `20261103-coordinator-1`, blob `f9c04a1099048cd0b02fd5264b753e916cbcd521`, assigns the due OAI-NNS signed low-owner turn. Wheel claim `20261103-wheel-1` is a paper input pending independent review, not an established all-owner estimate. Referee's corrected inverse constant `2/(9 sqrt(3))` is retained. External inbox `038018145c0fddb2f6306c0712373adf9cd1ea52` has no entry after October 18; old routing is superseded but source qualifications remain binding.

**Selected task / deployment_ack:** resume `20261102-analytic-2`, section M, at the original diagonal-restored small-owner remainder, with the already paid large-owner complement. For distinct admitted odd primes q<r, retain
`d_q=M(floor((R^2-1)/q^2))`, `d_r=M(floor((R^2-1)/r^2))`, the exact intervening Mobius sum, and both unshifted daughter squares. Investigate joint positive-daughter conditions and whether their true nested-prefix dependence improves independent integer caps. Test the genuine R=125 and R=2002 anchors; any finite search is preregistered before execution. No connection to ideal-character phases or to the hybrid shell is presumed.

**Intended output:** a proved source-faithful joint restriction or a precise genuine simultaneous-realization counterexample, plus the first unsupported aggregate inequality. Current new-run endpoint gain UNKNOWN. Independent review PENDING. Next protected turn CODIV; NYMAN resumes later at the complete middle residual and Coordinator C29-C30, not by repeating its paid remote tail.

No local Lean, proof-source edit, other-role write, PR change, agent launch, schedule change or merge is performed. Only this report is authorized for GitHub modification.

---

## Scheduled Continuation Final Synthesis - Claim 20261103-analytic-2

**Most important result:** two genuine, strictly admitted prime-square daughters can BOTH contribute positively after their full overlap diagonals and negative daughter squares are restored. At R=376 the fixed labels q=17 and r=19 contribute 86/17 and 136/19. Their sum 3946/323 also ATTAINS the sharp upper bound conditional on their exact nested Mobius-prefix difference. Universal pairwise nonpositivity is therefore false; merely adjoining the true interval sum to a scalar optimization does not force the pair negative.

**Evidence:** FINITE_COMPUTATION / REFUTED universal pair-exclusion claim; PAPER_PROOF_NEEDS_INDEPENDENT_REVIEW for the sharp joint cap and credit-preserving aggregation; SELF_AUDIT. No new Lean theorem or independently proved global exponent improvement. Net new endpoint gain UNKNOWN. Canonical actual-prime VF, RH and the sharp local square-shell bound remain OPEN.

This is the completion of the scheduled 2026-11-03 09:09:02 EST (-0500) invocation, not an additional run. RUN_ID_UNAVAILABLE. Execution is MATHEMATICS_COMPLETE; publication becomes verified only after commit/readback. Earlier same-day results and corrections are unchanged.

### A. Most Important Analytic Development

The due OAI-NNS continuation was Coordinator 20261103-coordinator-1 section H: investigate the joint dependence of two surviving original q^2 daughters, resuming 20261102-analytic-2 section M. This is the rational Mobius mixed-remainder carrier. It is not the separate ideal-character detector source, hybrid mu*kappa shell, or physical prime-indicator VF carrier.

Three conclusions survive the investigation:

1. The genuine example R=376, q=17, r=19 refutes the universal assertion that at most one corrected daughter can be positive. Both labels also belong to the literal small-label set q<T^2 when T=5. This does NOT refute an asymptotic fixed-(3,5) assertion or any specific smaller moving cutoff.
2. The exact intervening sum gives a sharp, uniform pair bound J3 below. Compared with optimizing each daughter independently, it subtracts an explicitly nonnegative squared-mismatch credit. At the witness it improves the pair cap from 6210/323 to 3946/323, and the improved cap is attained by the actual arithmetic values.
3. Such credits may be aggregated with vertex degree at most one, J6, preserving every original -2d_q^2 term exactly once. No all-scale lower bound on the useful aggregate credit has been proved. The aggregation is an interface, not a new quantitative supplier.

The first item is a decisive legal falsifier. The second and third are structural/deterministic paper results. There is **NO_NEW_INDEPENDENT_AGGREGATE_INEQUALITY** and no claim of external-literature novelty.

### B. Current Mathematical Objective And Authority

Pinned and subsequently rechecked main:

    acffafc79df1a3713e77dcd14eb551b7413d00c2

The unchanged canonical target is

    exists C>=0, forall integers R>=2,
      |pi(R^2)-VF_can(R^2)| <= C R log R.

The original canonical definition, fixed sqrt(2) phase and explicit classical von Koch interface were inspected in [VF_CANONICAL_SQRT_TWO_VON_KOCH.lean](https://github.com/OVVO-Financial/RH_Lean/blob/acffafc79df1a3713e77dcd14eb551b7413d00c2/research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean). No prime-error estimate is inferred from its O(1) VF/Li comparison.

Material original-source blobs at this main:

| Source | Blob SHA | Use |
| --- | --- | --- |
| AGENTS.md | 9fa5e9519e2fb6dde22217aa2a18982dafef373a | Current own-report-only authority |
| CURRENT_PROOF_CONTRACT.md | 88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a | Canonical objective and source safeguards |
| docs/RHLEAN_SEVEN_AGENT_RESEARCH_ENGINE_20261101.md | 6fce99c61efb5b2a73c0cb1f1464f09b351fcd55 | Persistent route continuation |
| research/CANONICAL_ROUGH_Q2_TAIL_REDUCTION.lean | ebca096e83009a7df514d00b6a2696be86a94c55 | Strict owner set and unshifted daughter energy |
| research/LOW_OWNER_PHYSICAL_AMPLITUDE_TRANSPORT.lean | 72d66f61b3eeb000117ecdac393572558bb7c378 | Literal raw daughter and full correction |
| research/GLOBAL_RETURNED_CORE_WEIGHTED_MOBIUS_COORDINATE.lean | f0e2e672a1ed369d1dc6dacbe9024c65e986a3c8 | Exact 1/q site weights and Fubini |
| research/GLOBAL_RETURNED_CORE_WEIGHTED_GRAM.lean | dbaf123113b544d0b19c7c3c6b92a1288a26cfb8 | Literal far-tail indicator |
| research/GLOBAL_RETURNED_CORE_ONE_AMPLITUDE.lean | b69a36ec4305a9309a5212358569905a968f4d63 | G=M(X)-M(R-1), sign relative to rough correlation |
| research/GLOBAL_RETURNED_CORE_RECIPROCAL_PREFIX_SIGNED_CELL_SPLIT.lean | 29bb263ddd07b12a2dd5ccf6a12aecaf627134d8 | Complete first-owner mixed carrier |
| research/GLOBAL_RETURNED_CORE_PREFIX_TAIL_MIXED_REMAINDER_IDENTITY.lean | d17aeb639bb47d79333cf0d00760c2604feddfdf | Prefix diagonal and exact remainder identity |
| research/CORR4_MIXED_TAIL_RECORD_PLATEAU_20261026.lean | a4abeb13653076bedd8e1173c933ee3324bfea26 | Exact endpoint/mixed theorem; interval Lipschitz bound |
| research/OAI78_CORR4_OWNER_TAIL_PAID_20261028.lean | 03c05e38fb2415105de9cccd3680b03c21c4be5c | Exact small/large-label partition |
| research/oai_434/OAI78CORR4PaidOriginalLargeOwner.lean | 06626af8cd8abfbf8f6da238f8a3d9af0893b686 | Existing input-dependent large-owner payment |
| research/CORR4_OAI_POWER_MIXED_TAIL_GATE_20261025.lean | bb0ee1252e7ba10c44ae5b8d827573d6c581b73a | Actual conditional Mertens consumer |
| RHLean/Proof/SquareRootLegalAncestryGramReduction.lean | 1270d4d91c53b50b110d10014f223f427fb7a575 | Historical envelope convention |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb | Canonical target |
| research/oai_434/VF919NativeStrictMertens.lean | b33a4883e1ddb0551b0f11f062bce46680d87450 | Newly merged strict prefix theorem |

**Updated formal state, not today's discovery.** #1073 was human-merged at 13:14:29Z. The stacked #1074-#1076 work was integrated through #1077 at 13:52:39Z. No open/draft PR was returned. The strict-Mertens terminal and its existing Lean dependencies are unchanged from tested #1073 head 9cbfce5295343bcb411e6d2cb159b59995cd985b: the complete GitHub comparison to main contains additions and a workflow modification, not modifications to that existing proof source.

All 13 runs attached to that tested head succeed. The actual [job 125650160501](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41554561404/job/125650160501) logs were retrieved: native_mertens_uniform_strict_gap, native_mertens_fixed_strict_power and the strict terminal audit succeed with propext, Classical.choice and Quot.sound; the terminal dependency audit reports PASS. Main's 11 returned push workflows also succeed, but they do not include a new dedicated strict-Mertens rebuild. The exact-head proof evidence is reused at unchanged dependencies, not misdescribed as a fresh cold build at the integration SHA.

The independently accepted #1073 conclusion is therefore now **PROVED_IN_LEAN_ON_MAIN / inherited VERIFIED_ETA**, with its tested-head provenance retained. This run does not freshly re-audit the entire analytic proof and does not automatically extend earlier acceptance to every changed declaration in #1076's later head. The reviewed source-relative refinements are not assigned an invented numerical gap. None supplies the new two-owner aggregate estimate or canonical VF/RH.

### C. Analytic Mechanism Investigated

The first attempted move was a structural exclusion: perhaps the actual nesting of two prefixes prevents both diagonal-corrected daughters from reinforcing G. The exact witness below rejects that universal form. Fixed-label (3,5) non-observation alone is not a substitute proof.

The second move, developed fully, keeps the signed interval difference before optimizing the common prefix level. Independent daughter caps allow the two prefix levels to move independently; the real arithmetic source fixes their difference. Orthogonal sum/difference coordinates therefore reveal a new explicit mismatch penalty. Integer parity restricts the remaining sum to one lattice coset. This is a finite deterministic argument with no imported Mertens bound or independence premise.

The analysis then checks whether the new penalty can be spent globally. Fractional matchings provide a precise no-double-counting rule, but do not provide the missing lower bound on the total penalty. The existing amplitude-inverse no-go, with Referee's corrected 2/(9 sqrt(3)) constant, remains intact and is not rerun here.

### D. Exact Mathematical Formulation

Fix any integer R>=56. Let

    X=R^2-1,
    S_R={q: q is an odd prime, q^2<R},
    Y_q=floor(X/q^2),       d_q=M(Y_q),
    G=M(X)-M(R-1),          A=|G|,
    V_0=sum_(R<=n<=X) mu(n)^2,
    V_q=sum_(R<=n<=Y_q) mu(n)^2,
    U=sum_(q in S_R) d_q/q, E=sum_(q in S_R) d_q^2.

All coefficients are the genuine integer Mobius coefficients. The strict owner condition gives Y_q>=R+1. Define the actual common-clock weights and diagonals

    a(n)=sum_(q in S_R) 1_(n<=Y_q)/q,
    t(n)=1_(R<=n),
    D=sum_(1<=n<=X) mu(n)^2(t(n)+a(n))^2,
    P=sum_(1<=n<=X) mu(n)^2 a(n)^2.

The compiled original mixed identity, followed by finite expansion of its diagonal, gives

    B_R := 2 Mixed_R-2E
         = G^2+2GU-2E-(D-P)
         = G^2-V_0+sum_(q in S_R) T_q,                    (J1)
    T_q := 2Gd_q/q-2d_q^2-2V_q/q,
    D-P = V_0+2sum_q V_q/q.

J1 is established infrastructure plus the elementary overlap expansion from Wheel W1, reconstructed here. It is not claimed as a new identity. Mixed_R is the original lowOwnerPrefixTailMixedRawCellMass, with all first-owner signatures already assembled. The daughter label q is not silently identified with the fresh first-owner label of that cell decomposition.

For distinct q<r in S_R, keep the exact, signed annular sum

    Delta_qr=d_q-d_r=sum_(Y_r<n<=Y_q) mu(n),
    s_qr=d_q+d_r,
    a_qr=(G/2)(1/q-1/r),
    b_qr=(G/2)(1/q+1/r),
    rho_qr=dist(b_qr, Delta_qr+2Z).                       (J2)

The distance is to a nonempty arithmetic progression of spacing 2, so its minimum exists and 0<=rho_qr<=1. The exact source satisfies s_qr in Delta_qr+2Z. No growing-parameter restriction or limiting exchange occurs.

**Sharp joint cap.** Uniformly in all such R,q,r,

    T_q+T_r <= L_qr,
    L_qr = (G^2/2)(q^(-2)+r^(-2))
           -(Delta_qr-a_qr)^2-rho_qr^2
           -2(V_q/q+V_r/r).                              (J3)

For fixed integer G, integer Delta, positive q,r and fixed overlap terms, this is the exact maximum over integer pairs (d_q,d_r) satisfying d_q-d_r=Delta. That algebraic sharpness does not assert every optimizer can be realized by Mobius prefixes. Section E supplies one actual realization that DOES attain it.

For comparison define the existing independent integer cap

    C_q(A)=A^2/(2q^2)-2dist(G/(2q),Z)^2,
    Gamma_qr=(Delta_qr-a_qr)^2+rho_qr^2
               -2dist(G/(2q),Z)^2-2dist(G/(2r),Z)^2.

Then

    Gamma_qr>=0,
    L_qr=C_q(A)+C_r(A)-2(V_q/q+V_r/r)-Gamma_qr,
    |Gamma_qr-(Delta_qr-a_qr)^2|<=1.                     (J4)

J3-J4 are exact, constant-one, uniform statements. There is no RH, input exponent, unspecified error, omitted endpoint, or stochastic hypothesis.

### E. Mathematical Derivation And Genuine Saturation

**Pair identity and cap.** Completing the two original negative squares and using u^2+v^2=((u-v)^2+(u+v)^2)/2 gives

    T_q+T_r = (G^2/2)(q^(-2)+r^(-2))
              -(Delta_qr-a_qr)^2-(s_qr-b_qr)^2
              -2(V_q/q+V_r/r).                          (J5)

Since s_qr lies in Delta_qr+2Z, its last square is at least rho_qr^2, proving J3. Conversely choose a nearest point s of that progression and put d_q=(s+Delta)/2, d_r=(s-Delta)/2. Both are integers and attain the cap. Independent optimization over both integers has value C_q+C_r before the overlap subtraction. Optimization under the extra difference constraint cannot increase it, proving Gamma>=0. Each single-lattice squared distance is at most 1/4 and rho^2 is at most 1; these prove the final bound in J4.

The actual interval also satisfies

    |Delta_qr|<=V_q-V_r,
    Delta_qr == V_q-V_r (mod 2),

because mu(n) is 0 or +/-1 and mu(n)==mu(n)^2 modulo 2. These true support restrictions were retained in the audit. They do not make the witness infeasible. The positivity conditions themselves are exactly Gd_q-q d_q^2>V_q and Gd_r-r d_r^2>V_r, not merely a common sign.

**Exact genuine witness.** Take R=376, X=141375. Then

    M(X)=-100, M(375)=-3, G=-97,
    q=17, Y_q=489, d_q=-4, V_q=73,
    r=19, Y_r=391, d_r=-1, V_r=10.

Both squares are strictly below R: 289<376 and 361<376. Direct substitution gives

    Gd_17-17d_17^2-V_17 = 388-272-73=43,
    Gd_19-19d_19^2-V_19 = 97-19-10=68,
    T_17=86/17>0, T_19=136/19>0.

The genuinely signed intervening interval is 392<=n<=489:

    Delta_17,19=-3, V_17-V_19=63, s_17,19=-5,
    a_17,19=-97/323, b_17,19=-1746/323,
    rho_17,19=131/323.

The nearest odd integer to b is exactly -5. Consequently the pair ATTAINS J3:

    T_17+T_19=L_17,19=3946/323,
    independent corrected cap=6210/323,
    Gamma_17,19=2264/323.

This is not an arbitrary sign vector or a synthetic sequence on squarefree support. Two independent arithmetic implementations reproduce the actual Mobius values and overlap counts. The difference and its parity restriction are satisfied exactly.

**Complete source restored.** The full owner set is {3,5,7,11,13,17,19}; the unshifted daughters are (-19,12,-19,-5,-3,-4,-1). Full quantities are

    U=-36959987/4849845, E=917, V_0=85721,
    D-P=5907946801/62985,
    B_376=-411004090324/4849845 < 0.

Thus the positive pair does not refute a full signed upper bound. All other daughters and the large parent diagonal remain in the actual source. The counterexample refutes universal pairwise exclusion, not the mixed consumer, Mertens improvement, canonical VF, or RH.

### F. Quantitative Comparison And Aggregation

For any subset L of S_R, choose nonnegative real pair weights lambda_qr, q<r in L, with

    degree(q)=sum_(r!=q) lambda_min(q,r),max(q,r) <= 1.

Every choice is allowed, including a root-dependent choice, provided this capacity condition is maintained. Exact finite reassembly gives

    sum_(q in L) T_q
      =sum_(q<r in L) lambda_qr(T_q+T_r)
        +sum_(q in L)(1-degree(q))T_q.

Applying J3 to the pairs and the individual cap to the residual vertices proves

    sum_(q in L) T_q
      <=sum_(q in L)(C_q(A)-2V_q/q)
        -sum_(q<r in L)lambda_qr Gamma_qr.                (J6)

This explicitly prevents spending one daughter's -2d_q^2 reserve once per partner. No pair-count loss is hidden. Since sum lambda<=|L|/2, replacing Gamma by its squared-difference term incurs at most |L|/2<=sqrt(R)/2 in total. A fixed number of rounding corrections alone cannot supply the required macroscopic saving. The potentially large arithmetic term is the squared deviation Delta_qr-a_qr, not the bounded lattice correction.

For a full cutoff Q>=2, put L={q in S_R:q<Q} and retain the FULL D-P, including high-label overlaps. J6 yields

    B_R <= G^2-(D-P)+sum_(q<Q)C_q(A)
            -sum_(q<r<Q)lambda_qr Gamma_qr
            +sum_(q>=Q)(2Gd_q/q-2d_q^2).                (J7)

The last sum is still the genuine complement. The elementary one-sided bound already used by Wheel is

    sum_(q>=Q)(2Gd_q/q-2d_q^2)
      <=(G^2/2)sum_(q>=Q)q^(-2)
      <=G^2/[2(Q-1)].

It spends only the high-label squares; J6 spends only low-label squares. Alternatively retain the compiled input-dependent large-owner bound with its own exact partition; do not combine both estimates while spending the same reserve twice.

For any fixed admissible incoming envelope |M(n)|<=C_in n^beta, beta>1/2, one has |G|<=2C_in R^(2beta). With fixed 0<theta<1/2 and Q=ceil(R^theta), the high contribution is O_(C_in,beta,theta)(R^(4beta-theta)), uniformly for all sufficiently large R, with finite small roots absorbed. A new independent bound of size R^(4beta-eta_low) for the complete first four terms in J7 would give beta_out=beta-min(theta,eta_low)/4, provided beta_out>=1/2. That is the precise conditional exponent calculation, not an achieved gain. One may choose an incoming beta strictly below 7/8 from the newly merged theorem; this run does not improve it.

No uniform lower estimate for sum lambda Gamma, strong enough in the presence of G^2 and the complete diagonal, was obtained. The finite improvement 2264/323 is not an asymptotic power saving.

### G. Original-Carrier Bridge And Consumer

J1 uses the actual compiled [corr4_mixed_tail_eq_actual_endpoint_gap](https://github.com/OVVO-Financial/RH_Lean/blob/acffafc79df1a3713e77dcd14eb551b7413d00c2/research/CORR4_MIXED_TAIL_RECORD_PLATEAU_20261026.lean) and the literal diagonal in [the mixed-remainder identity](https://github.com/OVVO-Financial/RH_Lean/blob/acffafc79df1a3713e77dcd14eb551b7413d00c2/research/GLOBAL_RETURNED_CORE_PREFIX_TAIL_MIXED_REMAINDER_IDENTITY.lean). No source equality between rational Mobius coefficients and sextic ideal phases is asserted.

The exact compiled sufficient consumer is [mertensPowerBound_of_corr4MixedTailBill](https://github.com/OVVO-Financial/RH_Lean/blob/acffafc79df1a3713e77dcd14eb551b7413d00c2/research/CORR4_OAI_POWER_MIXED_TAIL_GATE_20261025.lean): for beta_out>=1/2 and A0>=0, an ALL-R estimate B_R<=A0 R^(4beta_out) implies the actual MertensPowerBound beta_out. The premise is not proved here. At the RH consumer, the live historical envelope is 0<=K and (M(y)-1)^2<=K(y+1) for every integer y<R; it must not be replaced by an endpoint envelope or a maximum over a different range.

The pair result preserves the strict moving q^2<R admission separately at each R. It introduces no differentiation in R, no activation approximation and no change to masks or weights. It does not pay the original sharp-shell maximal-fragment source, which remains a different problem. All prefix-prefix terms assigned to the existing compiled prefix part remain assigned there; no U^2 is accidentally erased from a new full-square expansion.

### H. Falsification, Novelty And Quantitative Audit

**Preregistered scope:** before executing the new test, the C++ source fixed exploratory roots 56..512 and held-out roots 513..2048. The changed question was simultaneous corrected-daughter positivity, not the previously completed individual-cap census. Fixed mandatory roots were 125 and 2002. The largest sieve argument is 4194303. No range extension was performed after the result.

Results: 117 roots in 56..2048 have at least two positive corrected daughters. R=376 is the first such root in that declared range, not a claim about all smaller roots. Neither T_3 nor T_5 was individually positive anywhere in the range, although G,d_3,d_5 have the same nonzero sign at 553 roots. Therefore the absence of a positive (3,5) pair is a FINITE_NON_OBSERVATION explained already by individual inequalities. It supplies no proof of a joint exclusion or an asymptotic claim.

The independent Python trial-factorization reconstruction at R=125 and R=376 uses no sieve values from the C++ run. It recomputes all required prefixes, exact Fraction arithmetic, the actual common-clock D-P by direct site summation, J1, the interval difference, and J3. It verifies the strict positive pair and cap equality. A separate Eratosthenes-style Mobius sieve reproduces R=2002 and is checked against trial factorization through 2000. At that anchor G=208, E=8367 and U=-233438518043839321/6541380665835015; all corrected T_q are nonpositive. Thus the known sign-sensitive regression is preserved, not used to infer a universal sign.

The R=125 regression is T_11=10/11 and B_125=-328672/33. The generic sharp-cap calculation was additionally checked in 3213 exact cases: -25<=G<=25, pair labels (3,5),(3,7),(17,19), and -10<=Delta<=10; maximizing over -25<=d_r<=25 attains J3 in every tested case. The proof in E, not this finite grid, supplies the all-parameter statement.

The previously accepted (3,5) affine saturation is on the HYBRID lifted-address shell with mu(14+25t)mu(5+9t)/15. Our quantities are entire prefixes at Y_3,Y_5. There is no occurrence-preserving bridge equating those sources. Its unsigned-incidence obstruction remains in force but is neither rerun nor presented as a counterexample to this pair cap.

Scoped novelty check compared current filename/search coordinates, the literal source modules, Wheel W1-W9, prior Analytic inverse work, [the existing nested square reserves](https://github.com/OVVO-Financial/RH_Lean/blob/acffafc79df1a3713e77dcd14eb551b7413d00c2/research/OAI78_CORR4_NESTED_SQUARE_RESERVES_20261028.lean), and [the frame-only inverse](https://github.com/OVVO-Financial/RH_Lean/blob/acffafc79df1a3713e77dcd14eb551b7413d00c2/research/CORR4_FRAME_ONLY_INVERSE_20261026.lean). Their source identities and square completions are not new. No identical Delta-conditioned parity-coset cap or the R=376 simultaneous saturation was located in that scoped search. This is not a claim of exhaustive literature novelty. No external analytic theorem was needed for this finite argument, and no unchanged literature search was repeated.

Reproducers are included below because a hash alone is not an available artifact. SHA256 values:

    joint_daughter_test.cpp:
      6de1c1062d50df75cfd83c306cc3b99d9fe8edecfc2a6d55943b63bcfd6cf336
    joint_daughter_verify.py:
      e31b172c7de2bd35cd082aa9c95a98b8df0cf844cc41d6ebb830bab29c4ed2a4

No computation or proof in this report is an independent Referee verdict. No local Lean was executed. Direct git cloning was unavailable (CONNECT tunnel 403); the authenticated read-only GitHub connector supplied the actual pinned files, tree, comparisons and CI logs instead. Publication uses only the authorized own-report path.

### I. Conceptual Interpretation

Nested prefixes DO supply more information than two independent integer variables: their real interval sum forces the mismatch credit Gamma. However, that improvement need not make either daughter or the pair nonpositive, and the strongest cap at fixed difference can be attained by genuine Mobius data. The universal exclusion mechanism is retired at exactly that scope.

The remaining useful possibility is aggregate, quantitative control of the actual nested-prefix mismatch relative to the parent, with disjoint accounting of the square reserve. J6 makes that accounting precise but does not create the missing arithmetic. A new norm name, another completion of squares, or larger supportive scans would not pay it.

### J. Specialist Handoffs

**Coordinator:** record 20261103-analytic-2 as a genuine universal pair-exclusion falsifier and a sharp source-qualified structural cap, not a new exponent supplier. Preserve the newly merged strict theorem at its tested-head scope. The fixed (3,5) question is still unresolved; its finite absence is not joint evidence.

**Adversarial Referee:** audit J2-J6, especially the factor of two, parity coset, cap attainment, Gamma>=0, and vertex-degree accounting. Independently reproduce the R=376 values and distinguish positive pair / negative full bill. No review of unrelated tails is requested by this claim.

**Prime Census:** this run supplies a concrete genuine witness for the current request, with independently reconstructed arithmetic and code. Do not enlarge the unchanged 2048 range merely to seek (3,5). A useful next finite task would be independent verification of R=376 from original mixed cells and a specifically proposed aggregate-credit inequality with a frozen rejection constant.

**Finite Wheel:** W1 and the one-use reserve are preserved. Pairwise positivity exclusion is false even at an attained exact-difference cap. J6 may be used as an interface after review; adding all pair credits without degree normalization is invalid. No redirection from your distinct FINITE-AC/MU-LIFT rotation is requested.

**Owner Payment:** no VF ancestry, original weights or returned-cell admission theorem is inferred. The overlap V_q is a squarefree diagonal in the literal Mobius prefix carrier, not capacity in the prime-indicator VF population.

**Lean Verification:** no immediate new proof branch or speculative endpoint wrapper is requested. After independent acceptance and a demonstrated consumer, J3-J6 are finite algebra/finite-sum candidates; the R=376 falsifier is a separate finite arithmetic certificate. Do not encode an aggregate mismatch bound as an assumption and call its supplier proved.

### K. First Independently Missing Analytic Theorem

For a fixed incoming admissible beta>1/2 and a fixed 0<theta<1/2, Q(R)=ceil(R^theta), a possible sufficient next input is a genuinely proved, uniform all-R estimate

    G_R^2-(D_R-P_R)+sum_(q<Q(R))C_q(|G_R|)
      -sum_(q<r<Q(R))lambda_qr(R) Gamma_qr(R)
        <= C R^(4beta-eta_low),                         (J8)

with eta_low>0 fixed before R, C independent of R, and nonnegative weights of degree at most one. All original overlaps are retained. Existence of weights satisfying J8 is NOT proved and is not claimed easier than the target; J8 is a stronger sufficient upper-envelope programme after dropping nonnegative residual squares. Its only new independently justified input here is the exact cap/aggregation, plus the legal falsification of the universal sign shortcut. No current theorem supplies the needed arithmetic lower control of the mismatch term. The same original complete mixed estimate, rather than J8, may still be the better object to attack.

The immediate research decision is to abandon universal pairwise nonpositivity. Do not impose that assertion on q=3,5 merely because a finite scan has no single positive component. Do not assume generic squarefree support or prefix envelopes give local correlation control; the accepted comparison-sequence no-go remains scoped and binding.

### L. Persistent Workspace And Resume Capsule

    ENGINE_VERSION: 2026-11-01; engine blob 6fce99c61efb5b2a73c0cb1f1464f09b351fcd55.
    MAIN: acffafc79df1a3713e77dcd14eb551b7413d00c2.
    RUN: scheduled 2026-11-03 09:09:02 EST (-0500); RUN_ID_UNAVAILABLE.
    TASK: due OAI-NNS / original small-owner mixed remainder.
    CLAIM: 20261103-analytic-2; J1-J8, with J1 identified as prior infrastructure.
    NEW_RESULT: exact R=376 simultaneous-positive pair and attained sharp joint cap.
    BOUND_SCOPE: finite deterministic pair inequality; uniform credit aggregation.
    FIRST_OPEN: independent complete low-label mismatch/covariance estimate.
    REVIEW: SELF_AUDIT; independent review PENDING; new Lean formalization NONE.
    PROGRAMME_GATE: inherited VERIFIED_ETA now on main through unchanged #1073 proof.
    NEW_RUN_ENDPOINT_GAIN: UNKNOWN; no new global bound.
    NYMAN_LAST: 20261103-analytic-1; resume full residual, with C29-C30 review pending.
    OAI_NNS_LAST: this run; pair exclusion retired, exact J6 survives.
    CODIV_LAST: 20261102-analytic-3; C25/PC4 accepted at their actual scopes.
    ROLLING_COVERAGE: CODIV, NYMAN, OAI-NNS over latest three actual runs.
    NEXT_DISTINCT_ROUTE_DUE: CODIV.
    NEXT_CODIV_STEP: resume the genuine fixed-field signed covariance and
      maximal-fragment-to-original-shell obligation; use C25, not the already
      paid moving-cutoff error, and respect Referee's support/prefix no-go.
    CANONICAL_VF: OPEN. RH: OPEN. SHARP_LOCAL_SHELL_GAIN: OPEN.

Continuity actually retrieved on agent-reports, relevant sections read (not independent acceptance of every claim):

| Role | November 2 blob | November 3 blob consumed |
| --- | --- | --- |
| Coordinator 00/90 | 1e932d4ce0eb0fd2c5f4507f6b111194d633eb32 | f9c04a1099048cd0b02fd5264b753e916cbcd521 |
| Owner | abfe546d72b151f4cd200fc61de3197efe23a65c | 0688ba1d205ac2e846c3c3a55adfc267a6eb6a40 |
| Analytic | 8e48b59611aa1d0bfa3577ed0a4a3bc0d0fcae73 | 7a167a551ca047c0b5bccf6220f40152d78ea176, then this run's checkpoint |
| Wheel | abf8ac8c22a708886183849552c90dd62787ac8d | ae0ce9040b145c8b2ee04418e02a363d10b5da38 |
| Census | 2cd84c57ab18d923e97368764f29f4ccd2ec3bb3 | 09ecf82c4a8d5d36b10ed6d64167d695e096ce03 |
| Referee | 814af1684df66e6ac99b8df1f102cb592b316f89 | 226a5a6d971f347b45e016a046007bc4ceb368ee |
| Lean | 02d19d792e26f072004cb5909f149538752626e9 | 579d19654925823b5fa2ef849366da2925d2c1b0 |

TODAY=AVAILABLE for all named roles; YESTERDAY=CARRY_FORWARD where a current derivation depends on it. All same-day own sections are preserved. The latest Owner VF short-run/ancestry-capacity findings, Coordinator C29-C30 Nyman obstruction, Census PC4/PC5, and Referee's squarefree-support/maximal-fragment no-go remain distinct-carrier claims; none was used as an unproved hypothesis here. External inbox blob 038018145c0fddb2f6306c0712373adf9cd1ea52 contains no entry after October 18. Its historical source/mask and normalized-payment warnings are retained; its dated routing/cadence is superseded.


### Executed Reproducers

The C++ run used g++ -O2 -std=c++17. The Python verifier used the standard library and exact Fraction arithmetic. Both finished successfully; neither ran Lean.

#### joint_daughter_test.cpp

```cpp
#include <algorithm>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>

// Frozen experiment: roots 56..512 exploratory, 513..2048 held out.
// Test simultaneous positive corrected daughters, especially labels 3 and 5.
struct Daughter {
    int q, y, d, v;
    long long numerator;
};

int main() {
    constexpr int max_root = 2048;
    constexpr int limit = max_root * max_root - 1;
    std::vector<int> least(limit + 1), primes, mertens(limit + 1), squarefree(limit + 1);
    std::vector<int8_t> mu(limit + 1);
    mu[1] = 1;
    for (int n = 2; n <= limit; ++n) {
        if (!least[n]) { least[n] = n; primes.push_back(n); mu[n] = -1; }
        for (int p : primes) {
            if (p > least[n] || 1LL * n * p > limit) break;
            least[n * p] = p;
            mu[n * p] = n % p == 0 ? 0 : -mu[n];
        }
    }
    for (int n = 1; n <= limit; ++n) {
        mertens[n] = mertens[n - 1] + mu[n];
        squarefree[n] = squarefree[n - 1] + mu[n] * mu[n];
    }
    int first_pair = 0, first_fixed = 0, positive_pairs = 0, fixed_count = 0;
    int same_sign_35 = 0, positive_3 = 0, positive_5 = 0;
    for (int R = 56; R <= max_root; ++R) {
        const int X = R * R - 1;
        const int G = mertens[X] - mertens[R - 1];
        std::vector<Daughter> all, positive;
        for (int q : primes) {
            if (q * q >= R) break;
            if (q == 2) continue;
            int y = X / (q * q), d = mertens[y];
            int v = squarefree[y] - squarefree[R - 1];
            long long num = 2LL * G * d - 2LL * q * d * d - 2LL * v;
            Daughter z{q, y, d, v, num};
            all.push_back(z);
            if (num > 0) positive.push_back(z);
        }
        if (all.size() >= 2 && 1LL * G * all[0].d > 0 && 1LL * G * all[1].d > 0) ++same_sign_35;
        if (all.size() >= 2 && all[0].numerator > 0) ++positive_3;
        if (all.size() >= 2 && all[1].numerator > 0) ++positive_5;
        if (positive.size() >= 2) {
            ++positive_pairs;
            if (!first_pair) {
                first_pair = R;
                std::cout << "FIRST_PAIR R=" << R << " G=" << G << '\n';
                for (const auto& z : positive) std::cout << z.q << ' ' << z.y << ' ' << z.d << ' ' << z.v << " T=" << z.numerator << '/' << z.q << '\n';
            }
        }
        if (all.size() >= 2 && all[0].numerator > 0 && all[1].numerator > 0) {
            ++fixed_count;
            if (!first_fixed) first_fixed = R;
        }
        if (R == 125 || R == 2002 || (positive.size() >= 2 && R == first_pair)) {
            std::cout << "ANCHOR R=" << R << " X=" << X << " M_X=" << mertens[X]
                      << " M_pred=" << mertens[R - 1] << " G=" << G
                      << " V0=" << squarefree[X] - squarefree[R - 1] << '\n';
            for (const auto& z : all) std::cout << z.q << ' ' << z.y << ' ' << z.d << ' ' << z.v << " T=" << z.numerator << '/' << z.q << '\n';
        }
    }
    std::cout << "SUMMARY first_pair=" << first_pair << " roots_with_pairs=" << positive_pairs
              << " first_35=" << first_fixed << " roots_with_35=" << fixed_count
              << " parent_and_35_same_sign=" << same_sign_35
              << " positive_3=" << positive_3 << " positive_5=" << positive_5 << '\n';
}
```

#### joint_daughter_verify.py

```python
from fractions import Fraction as F
from itertools import combinations
from math import isqrt


def trial_mu(n):
    sign = 1
    p = 2
    while p * p <= n:
        if n % p == 0:
            n //= p
            sign = -sign
            if n % p == 0:
                return 0
            while n % p == 0:
                n //= p
        p += 1
    return -sign if n > 1 else sign


def prime(n):
    return n > 1 and all(n % p for p in range(2, isqrt(n) + 1))


def pair_cap(G, q, r, vq, vr, difference):
    target_difference = F(G, 2) * (F(1, q) - F(1, r))
    target_sum = F(G, 2) * (F(1, q) + F(1, r))
    center = (target_sum - difference) / 2
    lo = center.numerator // center.denominator
    distance_sq = min((F(2 * a + difference) - target_sum) ** 2 for a in (lo, lo + 1))
    return (
        F(G * G, 2) * (F(1, q * q) + F(1, r * r))
        - (difference - target_difference) ** 2
        - distance_sq
        - 2 * (F(vq, q) + F(vr, r))
    )


def independent_cap(G, q):
    k = (abs(G) + q) // (2 * q)
    return F(2 * k * (abs(G) - q * k), q)


def eratosthenes_mu(limit):
    values = [1] * (limit + 1)
    is_prime = bytearray(b'\x01') * (limit + 1)
    values[0] = 0
    for p in range(2, limit + 1):
        if is_prime[p]:
            for n in range(p, limit + 1, p):
                values[n] = -values[n]
            for n in range(p * p, limit + 1, p * p):
                values[n] = 0
            for n in range(p * p, limit + 1, p):
                is_prime[n] = 0
    return values


# Independent trial-factorization reconstruction of the small decisive root.
for R in (125, 376):
    X = R * R - 1
    mu = [0] + [trial_mu(n) for n in range(1, X + 1)]
    M = [0]
    Q = [0]
    for u in mu[1:]:
        M.append(M[-1] + u)
        Q.append(Q[-1] + u * u)
    G = M[X] - M[R - 1]
    V0 = Q[X] - Q[R - 1]
    daughters = {}
    for q in range(3, isqrt(R - 1) + 1, 2):
        if not prime(q):
            continue
        y = X // (q * q)
        d = M[y]
        v = Q[y] - Q[R - 1]
        T = F(2 * (G * d - v), q) - 2 * d * d
        daughters[q] = (y, d, v, T)
    E = sum(d * d for _, d, _, _ in daughters.values())
    U = sum((F(d, q) for q, (_, d, _, _) in daughters.items()), F(0))
    # Original common-clock diagonal, independent of overlap-count expansion.
    DminusP = F(0)
    for n in range(R, X + 1):
        if mu[n]:
            a = sum((F(1, q) for q, (y, _, _, _) in daughters.items() if n <= y), F(0))
            DminusP += 1 + 2 * a
    B = G * G + 2 * G * U - 2 * E - DminusP
    assert B == G * G - V0 + sum((z[3] for z in daughters.values()), F(0))
    print('WITNESS', R, 'G', G, 'V0', V0, 'U', U, 'E', E,
          'DminusP', DminusP, 'B', B, 'B_float', float(B))
    for q, r in combinations(daughters, 2):
        yq, dq, vq, tq = daughters[q]
        yr, dr, vr, tr = daughters[r]
        difference = sum(mu[yr + 1:yq + 1])
        assert difference == dq - dr
        cap = pair_cap(G, q, r, vq, vr, difference)
        assert tq + tr <= cap
        assert (dq - dr - (vq - vr)) % 2 == 0
        if tq > 0 and tr > 0:
            independent = independent_cap(G, q) + independent_cap(G, r) - 2 * (F(vq, q) + F(vr, r))
            print('POSITIVE_PAIR', q, r, 'difference', difference, 'sum', dq + dr,
                  'Tq', tq, 'Tr', tr, 'total', tq + tr, 'joint_cap', cap,
                  'independent_cap', independent, 'saving', independent - cap,
                  'attained', tq + tr == cap)

# Exhaustive finite algebra check, independent of the genuine arithmetic test.
checks = 0
for G in range(-25, 26):
    for q, r in ((3, 5), (3, 7), (17, 19)):
        for difference in range(-10, 11):
            cap = pair_cap(G, q, r, 0, 0, difference)
            values = [F(2 * G * (v + difference), q) - 2 * (v + difference) ** 2
                      + F(2 * G * v, r) - 2 * v * v
                      for v in range(-25, 26)]
            assert max(values) == cap
            assert cap <= independent_cap(G, q) + independent_cap(G, r)
            checks += 1
print('EXACT_PAIR_CAP_CHECKS', checks)

# Independent second sieve for the required R=2002 regression only.
R = 2002
X = R * R - 1
mu = eratosthenes_mu(X)
assert all(mu[n] == trial_mu(n) for n in range(1, 2001))
cutoffs = {X, R - 1}
owners = [q for q in range(3, isqrt(R - 1) + 1, 2) if prime(q)]
cutoffs.update(X // (q * q) for q in owners)
prefix = {}
M = Q = 0
for n in range(1, X + 1):
    M += mu[n]
    Q += mu[n] * mu[n]
    if n in cutoffs:
        prefix[n] = (M, Q)
G = prefix[X][0] - prefix[R - 1][0]
V0 = prefix[X][1] - prefix[R - 1][1]
U = F(0)
E = 0
overlap = F(0)
for q in owners:
    d, v = prefix[X // (q * q)]
    v -= prefix[R - 1][1]
    U += F(d, q)
    E += d * d
    overlap += F(2 * v, q)
    assert F(2 * (G * d - v), q) - 2 * d * d <= 0
print('ANCHOR_2002', 'G', G, 'V0', V0, 'U', U, 'E', E,
      'DminusP', V0 + overlap, 'B', G * G + 2 * G * U - 2 * E - V0 - overlap,
      'corr_times_U', -G * U)
```


### Publication Verification - 2026-11-03 09:29 EST (-0500)

Execution/publication: COMPLETED / PUBLISHED_AND_READBACK_VERIFIED. This receipt concerns the scheduled 09:09:02 EST continuation only and does not upgrade PAPER_PROOF / SELF_AUDIT to independent review or Lean certification.

The early checkpoint was committed as `6d02b6deda0aa3831d592f6895cb8996490e60c9` and read back at blob `3853c756ce954300c7b88257debea835a4e0e657`. The complete synthesis and both executed reproducers were committed as `2d584ab279783893384a016d0067858efdb6d382`, then re-fetched byte-for-byte at blob `90fbd69c4a1c34e6333d262da4c80cb94b4e723e` (71,245 characters). Commit inspection confirms that only this authorized Analytic report changed. Earlier same-day findings, the checkpoint and prior publication history are preserved.

The new appendix passed ASCII/control-character, A-L-section and balanced-code-fence checks. All finite computations completed successfully. Final main refresh returned unchanged `acffafc79df1a3713e77dcd14eb551b7413d00c2`. The new result is the genuine simultaneous-positive pair and sharp conditional cap, not a new global bound. Independent Referee review remains PENDING; next protected route is CODIV.


## Scheduled Continuation Checkpoint - 2026-11-03 17:11 EST Invocation

**Execution:** PARTIAL / IN_PROGRESS. Scheduled invocation at 2026-11-03T17:11:01-05:00; RUN_ID_UNAVAILABLE. This is a new actual continuation, preserving all earlier sections.

**Authority:** live main `69aac0441b4df011cf7df3ba115169c3b66d72f5`; AGENTS blob `9fa5e9519e2fb6dde22217aa2a18982dafef373a`; contract blob `88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a`; engine blob `6fce99c61efb5b2a73c0cb1f1464f09b351fcd55`. All seven roles' available November 3 and November 2 reports and the unchanged external inbox were retrieved. Relevant continuation inputs are `20261102-analytic-3`, Coordinator C20-C25, Referee `20261103-referee-3/4`, and Census PC4/PC5. Today's NYMAN and OAI-NNS continuations remain preserved; CODIV is the due protected route.

**Selected research:** resume the actual frozen hybrid `g_H=mu*kappa_H`, maximal shell fragments, and complete physical return. Investigate a genuinely multiplicative restriction or a precise arithmetic correlation reduction that distinguishes actual mu from the squarefree-supported comparison sequence. Reuse the accepted freezing and activation bounds; do not rerun their old census or infer maximal energy from a global Mertens envelope. Every principal, selected-fragment, mixed, and boundary contribution must be retained.

**Source/verification:** the original lifted carrier and shell declarations were read at pinned main. No open/draft PR is currently returned. #1079, #1081, and #1082 are now merged; #1080 is closed unmerged. Exact-head Actions/axiom verification is being refreshed. The inherited strict-below-7/8 result is present in original source; this checkpoint does not independently certify a new gain. Canonical VF, RH, the genuine maximal-fragment estimate, and the positive fullOwnerGamma estimate remain OPEN.

No new theorem or computation is claimed yet. Independent review of this run: PENDING. New net endpoint gain: UNKNOWN. Next protected route after this CODIV continuation: NYMAN.


## Scheduled CODIV Continuation Final Synthesis - Claim 20261103-analytic-3

**New result:** the genuine maximal square-shell fragment energy is `O(H^3 / log(2H)^(1/100))`. The same rate holds for the original moving and frozen reciprocal prime-square daughter fields, and for the complete zero-frequency physical return. This is a proved logarithmic improvement on the cubic local-energy bound, NOT a fixed power saving and NOT a new Mertens exponent. The result supplies the previously missing maximal/square-sampling transfer for a classical short-interval theorem at its actual logarithmic strength.

**Evidence:** PAPER_PROOF / SELF_AUDIT for CD1-CD3; IDENTITY_WITH_EXPLICIT_BOUNDARY_BOUND for CD4; CONDITIONAL for CD5's stronger endpoint consequence; FINITE_COMPUTATION for CD6. Independent Referee review and Lean certification of this new bundle are PENDING. No external-literature novelty is claimed. Publication is verified separately below, not inferred from this synthesis.

**Invocation:** scheduled 2026-11-03T17:11:01-05:00, America/New_York; RUN_ID_UNAVAILABLE. This completes the early checkpoint for that invocation, not a new launch. Earlier same-day reports and corrections are preserved.

### A. Most Important Analytic Development

For the actual Mobius function define

```text
Omega_R(mu) = max_(integer R^2<=u<=v<=(R+1)^2)
                 |sum_(u<=n<v) mu(n)|,
E_mu(H) = sum_(H<=R<2H) Omega_R(mu)^2.
```

There are constants C,H0, independent of H, such that every integer H>=H0 satisfies

```text
E_mu(H) <= C H^3 / log(2H)^(1/100).                    (CD2)
```

The constants can be enlarged to cover all H>=2. They are not numerically evaluated here. This is genuinely arithmetic information: Referee `20261103-referee-4` constructs a squarefree-supported comparison sequence with square-root-bounded prefixes but maximal energy at least `9H^3/256`. That sequence cannot satisfy CD2. The new independent ingredient is the Matomaki-Radziwill short-average theorem applied to mu, not an inference from a prefix envelope or squarefree support.

A deterministic smoothing inequality proves the transfer without asserting that square endpoints avoid the exceptional set. It applies to every selected fragment simultaneously and retains its exact boundary cost. An absolutely convergent prime-dilation estimate then returns the result to the NONmultiplicative hybrid source without applying a multiplicative-function theorem to that hybrid.

The remaining quantitative gap is substantial: CD2 is larger than `H^(5/2-eta)` by `H^(1/2+eta)/log(2H)^(1/100)`. PC5's diagonal-sized overshoot repair is not proved. Neither the canonical VF bound nor RH follows.

### B. Current Mathematical Objective And Authority

Pinned main: `69aac0441b4df011cf7df3ba115169c3b66d72f5`, human merge of #1082. The canonical objective remains the literal `VFCanonicalSquareVonKochStatement`:

```text
exists C>=0, forall integer R>=2,
  |pi(R^2)-vfCanonical(R^2)| <= C R log R,
vfCanonical(x)=vfMid(x)+sqrt(2).
```

The original actual-prime carrier and phase are unchanged. The classical von Koch criterion is still an explicit interface argument on that consumer. The selected CODIV question concerns genuine maximal Mobius fragments and the physical reciprocal-daughter return, not an asserted identification with original ideal-character phases or with the high-prime owner Gamma.

Material source and authority blobs at pinned main:

| File | Blob SHA | Scope used |
| --- | --- | --- |
| AGENTS.md | 9fa5e9519e2fb6dde22217aa2a18982dafef373a | Own-report-only permission and persistent portfolios |
| CURRENT_PROOF_CONTRACT.md | 88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a | Original target and quantitative safeguards |
| docs/RHLEAN_NATIVE_SQUARE_CLOCK_AGENT_DIRECTIVE_20261029.md | d05c327ae694ea54b599dab0a21032a056b521f1 | Live task selector |
| docs/RHLEAN_BROAD_SEARCH_UNTIL_ETA_20261031.md | b5c063c51556ba57c4b25bcc380a606fa8daa207 | Scoped gain gate and route coverage |
| docs/RHLEAN_SOURCE_FAITHFUL_COMPLETE_RETURN_AGENT_CONTRACT_20261031.md | 16838f7f3c8724b970f8b8ece0bceaab9418066d | Complete signed return |
| docs/RHLEAN_SEVEN_AGENT_RESEARCH_ENGINE_20261101.md | 6fce99c61efb5b2a73c0cb1f1464f09b351fcd55 | Resume rather than restart |
| research/LOW_OWNER_PHYSICAL_AMPLITUDE_TRANSPORT.lean | 72d66f61b3eeb000117ecdac393572558bb7c378 | Unscaled daughters and full physical remainder |
| research/LOW_OWNER_AMPLITUDE_MELLIN_LEDGER_SPLICE.lean | 73447e8c73ea60affec36a25b9f4794862331359 | Literal 1/q column and zero-frequency identification |
| research/GLOBAL_RETURNED_CORE_FIRST_OWNER_GRAM.lean | 36141a8caec5f99d6c40cb72ae1fdbcf6f462b82 | Entire signed Gram, not separate populations |
| research/LIFTED_MOBIUS_ADDRESS_INJECTIVITY_20261102.lean | 61f98a8997d86ddbb07404284d12aebd36a67955 | Strict q^2<R carrier and unique nonzero addresses |
| research/VF_919_SEVEN_EIGHTHS_SQUARE_SHELL_BRIDGE_20261019.lean | 55839f2013fc5b8d352dcea0e2ed4bb47d763693 | Original scalar shells and full covariance |
| research/MERTENS_EXPONENT_ENVELOPES.lean | 655b896e8d5a41c9f8fc3c456eae3944a98bfefe | Exact quantifier order for power envelopes |
| research/oai_434/VF919NativeSevenEighthsReplay.lean | 111c933a7ca15647105ce6a4d0f3cbfc3cde81f4 | Existing nativeReplay_mertens_growth, used only for the long mean |
| research/oai_434/VF919NativeStrictMertens.lean | b33a4883e1ddb0551b0f11f062bce46680d87450 | Inherited strict-gap status, not this run's result |
| research/oai_434/VF919ActualSlotMinRetighten.lean | 138c4726085995b966204406805f70082402bec4 | Existing source-relative endpoint refinement |
| research/oai_434/VF919NativeOwnerDiagonalThreeQuarter.lean | 798e7a3ee89324feb3eafd8d28b56f18c4f03d3c | Newly merged diagonal; positive Gamma still open |
| research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean | 79030d70e8d3e0d08eef9bac53fef95c36eca2fb | Canonical target |

Original declarations are linked in sections E and G. The source files, not report labels, determine their statements. In particular the current replay blob differs from yesterday's `ff963b...`; current bytes were fetched, not presumed unchanged.

**Relevant Actions verification.** No open/draft PR was returned at intake. #1079, #1081 and #1082 are merged; #1080 is closed unmerged. At exact heads `7ff378e3edd971a8d9e2f11fe39db1aef598ba85`, `11402d6ca895d10a3c2805142138226e9394c34a`, and `0b41bfa95bf2dbeb6facf051014d41688dd62e26`, respectively, all returned workflows succeeded: 13, 13, and 12. The dedicated [#1079 job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41676598704/job/126058888532) and [#1082 job](https://github.com/OVVO-Financial/RH_Lean/actions/runs/41717376409/job/126200831143) were inspected, including successful pinned compilation, exact endpoint checks and standard axiom output. The #1082 logs print only `propext, Classical.choice, Quot.sound` for the three owner-diagonal/negative-Gamma/positive-part declarations and for the inherited strict Mertens statements. Its exact finite R<=3500 regression also passed; that computation was not rerun here. The strict Mertens, replay and owner-diagonal files were separately fetched at that PR head and match main byte-for-byte. The older failed #1082 heads in Coordinator's report are historical, not current failures.

This verifies existing relevant CI, not a new Lean theorem for CD1-CD5. No local Lean or new Actions run was performed. Programme gate: inherited `VERIFIED_ETA / ON_MAIN`, at its previously independently reviewed scope. New gain from this invocation: NONE. No numerical value for the inherited gap is invented.

**Closeout refresh, 22:25-22:26 UTC:** main is unchanged. New draft #1083 is now open at `92defc3ce6f9517ac1a649af9a1ba643bad917e2`; it was not present in the intake listing. Eleven returned workflows succeeded, while dedicated run `41729980802` remains IN_PROGRESS. Its proposed rational-slot seed, variable-exponent diagonal, and explicitly conditional owner bootstrap are not main and are not inputs to this proof. No completion or unconditional RH conclusion is inferred from its body. The inspected #1082 runner `scripts/lean/slot_anchored/run_anchored_in_verified_ci.sh`, blob `afbe1922fd2b122139fac53c5797bdf8e0e9959e`, compiles the actual listed targets with `-DwarningAsError=true`, rejects sorry/admit dependencies, and runs the exact endpoint/slot audits.

### C. Analytic Mechanism Investigated

The exact resumed gap is Coordinator `20261102-coordinator-3` C23: the cited multiplicative short-interval theorem had not been transferred to prescribed maximal square cells, and g itself is not multiplicative. Analytic `20261102-analytic-3` plus accepted Census PC4 already pay the moving-cutoff error. Referee `20261103-referee-3/4` accepts the fragment-preserving dilation transfer and excludes a prefix/support-only repair.

Two moves were compared. Directly estimating maximal selected correlations retains an adaptive endpoint mask that the known averaged theorem does not cover. Smoothing a selected interval by all h adjacent translations instead removes selection before the mean-square estimate, with the deterministic error h-1. The second move is developed below. It does not use an independence assumption, complete a period, or discard an exceptional square sample.

The new transfer is useful even though the resulting saving is logarithmic. It establishes one actual local arithmetic restriction and reduces the stronger problem to common-window triangular correlations with a completely explicit boundary term. It does not rename PC5 as a theorem.

### D. Exact Mathematical Formulation

Let a(n) be a real sequence on positive integers with |a(n)|<=1. For integers H>=2 and h>=1 define

```text
S_h a(n) = sum_(0<=j<h) a(n+j),
J_a(H,h) = sum_(H^2<=n<4H^2) |S_h a(n)|^2,
Omega_R(a) = max_(integer R^2<=u<=v<=(R+1)^2)
                 |sum_(u<=n<v) a(n)|.
```

The sequence is retained through `4H^2+h-2`; forward-window values past `4H^2-1` are NOT set to zero. All sums are finite. Empty fragments are permitted. The central deterministic estimate, with absolute explicit constants, is

```text
sum_(H<=R<2H) Omega_R(a)^2
 <= (8H/h^2) J_a(H,h) + 2H(h-1)^2.                  (CD1)
```

For the original physical source, with p always an odd prime, define

```text
g_infinity(n) = mu(n) + sum_(p^2|n) mu(n/p^2)/p,
g_R(n)       = mu(n) + sum_(p^2<R, p^2|n) mu(n/p^2)/p,
g_H^fr(n)    = mu(n) + sum_(p^2<H, p^2|n) mu(n/p^2)/p.
```

Use these coefficients on exactly the same square-shell fragments. For `g_R` the root R changes the source; for `g_H^fr` the source is fixed within H<=R<2H. Claim CD3 asserts existence of one H-independent constant for each displayed bound:

```text
sum_(H<=R<2H) Omega_R(g_infinity)^2 << H^3/L^(1/100),
sum_(H<=R<2H) Omega_R(g_R)^2        << H^3/L^(1/100),
sum_(H<=R<2H) Omega_R(g_H^fr)^2     << H^3/L^(1/100),
L=log(2H).                                                (CD3)
```

The full physical-return statement is given in G. Implied constants depend only on the fixed external theorem and a fixed established long-mean bound, never on H, h in CD1, a selected fragment, or an owner cutoff. No claimed numerical effectiveness or all-scale finite certificate is attached to the asymptotic constants.

### E. Mathematical Derivation

#### E1. CD1: Selection-Free Smoothing With Its Boundary

For I=[u,v) and B_h(n)=S_h a(n)/h, direct telescoping gives

```text
sum_(n in I) a(n) - sum_(n in I) B_h(n)
 = (1/h) sum_(0<=j<h)
     [sum_(u<=n<u+j) a(n) - sum_(v<=n<v+j) a(n)].
```

This equality remains valid when translated intervals overlap. Its absolute value is at most `h-1`, since `(1/h) sum_j 2j=h-1`. Cauchy-Schwarz is now applied only to the smoothed interval, at its explicitly charged cost:

```text
|sum_(n in I) B_h(n)|^2
 <= |I| sum_(n in I) |B_h(n)|^2
 <= (2R+1) sum_(R^2<=n<(R+1)^2) |B_h(n)|^2.
```

The right side is independent of I. Taking the maximum and using `(x+y)^2<=2x^2+2y^2`, then summing the H disjoint shells, proves CD1 because `2(2R+1)<=8H`. Thus no union bound over fragments and no hypothesis about exceptional square endpoints is needed. The loss H/h^2 is real and will be included in every exponent calculation.

#### E2. The Independent Short-Average Input And CD2

The external input is Matomaki-Radziwill, *Multiplicative functions in short intervals*, Annals of Mathematics 183 (2016), 1015-1056, [Theorem 1, pp. 1015-1016](https://annals.math.princeton.edu/wp-content/uploads/annals-v183-n3-p06-p.pdf), DOI 10.4007/annals.2016.183.3.6. For real multiplicative f with |f|<=1, uniformly for 2<=h<=X and delta>0, the normalized short mean differs from its [X,2X] mean by at most

```text
delta + C' loglog(h)/log(h)
```

outside at most

```text
C X [(log h)^(1/3)/(delta^2 h^(delta/25))
                  + 1/(delta^2 (log X)^(1/50))]
```

integer starts. C,C' are absolute; the paper permits C'=20000. This is an exceptional-set theorem with its parameters retained, not a pointwise or fixed-power short-sum estimate.

Apply it ONLY to f=mu. The existing [nativeReplay_mertens_growth](https://github.com/OVVO-Financial/RH_Lean/blob/69aac0441b4df011cf7df3ba115169c3b66d72f5/research/oai_434/VF919NativeSevenEighthsReplay.lean), with epsilon=1/16, provides a fixed D such that `|M(x)|<=D x^(15/16)`. Hence the normalized long mean is `O_D(X^(-1/16))`. This use of the inherited global theorem controls only the long mean in an independent short-average theorem; it does not infer local variance directly from M.

Set `L=log(2H)`, `h=floor(H/L)` and `delta=L^(-1/200)`, for sufficiently large H. Cover the entire integer start interval [H^2,4H^2) by X=H^2 and X=2H^2. Uniformly on these two blocks, log h is comparable to L, and

```text
delta^2 = L^(-1/100),
delta^(-2) (log X)^(-1/50) << L^(-1/100),
(log h)^(1/3)/(delta^2 h^(delta/25)) = o(L^(-1/100)).
```

The last assertion follows because `delta log h` has order `L^(199/200)`, which dominates log L. The good-start normalized sums are `O_D(delta)`; the long mean and `loglog h/log h` are smaller. The paper uses inclusive short endpoints; deleting its last term changes the normalized sum by at most 1/h, also smaller. On exceptional starts use the true bound `|S_h mu|<=h`. Thus

```text
J_mu(H,h) <<_D H^2 h^2 L^(-1/100).
```

CD1 now yields

```text
E_mu(H) <<_D H^3 L^(-1/100) + H^3 L^(-2),
```

which proves CD2. There is no stochastic approximation. All H shells and all their fragments are covered. Enlarging the constant pays the finite initial range where h<2 or the asymptotic comparisons do not yet hold. D is a fixed already-established source constant; its numerical value is not computed here.

#### E3. CD3: Uniform Return Through All Prime-Square Owners

Retain the accepted C20-C21 notation `A(t)=sum_(1<=n<t^2)mu(n)`, A=0 on [0,1], and

```text
B(t)=A(t)+T A(t),       T A(t)=sum_(p odd prime) A(t/p)/p.
```

This is exactly the primitive of g_infinity. The sum is locally finite. Let `F_A(X)=sum_(1<=R<X)Omega_R(A)^2` for real X>=0, so F_A(X)=0 when X<=1. CD2 and dyadic summation give, for X>=1,

```text
F_A(X) << X^3 / log(2X)^(1/100).
```

For example, use the trivial `F_A(Y)<=9Y^3` below sqrt(X) and sum the dyadic bounds above it, where every logarithm is comparable to log(2X). This justifies the prefix form uniformly, including small scales after increasing the constant.

For each integer R,p the interval [R/p,(R+1)/p] is in the single closed root cell indexed by floor(R/p), including p|(R+1). There are at most p preimage cells for a given lower cell; the cell indexed zero contributes nothing. The accepted multiplicity-sensitive Minkowski bound is

```text
sqrt(F_TA(X)) <= sum_(p odd prime) p^(-1/2) sqrt(F_A(X/p)).
```

To preserve the logarithmic rate with GROWING owners, split at p=sqrt(X). For small p, log(2X/p)>=log(2X)/2, so their total is

```text
<< X^(3/2) log(2X)^(-1/200) sum_p p^(-2).
```

For p>sqrt(X), the trivial prefix bound gives `O(X^(3/2) sum_(p>sqrt X)p^(-2))=O(X)`. The first series converges absolutely; the second tail estimate uses the integer reciprocal-square series. Hence B has the same maximal logarithmic rate. This is a new weighted-log consequence of the accepted dilation estimate, not a claim that a scalar completed shell can be dilated without fragments.

The already accepted original-source comparison C21 gives

```text
|Omega_R(g_infinity)-Omega_R(g_R)| <= 4+log(R+1).
```

It follows by counting at most `(2R+1)/p^2+1` cofactor sites for each omitted p>=ceil(sqrt R), retaining actual mu and weight 1/p. Its dyadic squared error is `O(H log^2 H)`. Accepted PC4 gives

```text
|Omega_R(g_R)-Omega_R(g_H^fr)| <= 4sqrt(2),
sum_(H<=R<2H) |Omega_R(g_R)-Omega_R(g_H^fr)|^2 <=32H.
```

Both errors are lower order than CD3. The triangle inequality pays their mixed interactions in l2; no favorable sign is assumed. In particular q^2=H is absent from the frozen source and added only when R>H, while q^2=R remains excluded. This proves CD3 for the complete, moving and frozen carriers.

#### E4. CD4: A Common-Window Signed Correlation With A Paid Halo

For any real |a|<=1 define

```text
D_a(H)=sum_(H^2<=n<4H^2)a(n)^2,
C_a(H,d)=sum_(H^2<=n<4H^2)a(n)a(n+d),
T_a(H,h)=2 sum_(1<=d<h)(h-d) C_a(H,d).
```

Expanding J and then moving each start window back by its integer j gives

```text
J_a(H,h)=h D_a(H)+T_a(H,h)+E_a(H,h),
|E_a(H,h)|<=h(h-1)(2h-1)/3.                         (CD4)
```

Here E is exactly the difference of the two displayed sides, and its origin is explicit: the diagonal has shifts j=0,...,h-1, each costing at most 2j; the lag-d terms have j=0,...,h-d-1, each costing at most 2j and carrying the outer factor 2. Their sum is

```text
sum_(j<h)2j + 4 sum_(1<=d<h) sum_(j<h-d)j
 = h(h-1)(2h-1)/3.
```

Thus the original fragment problem has a proved comparison to one ordinary signed triangular correlation on a common integer window. No adaptive fragment mask remains in T. The values n+d outside the main window are genuine forward-halo values, and the error has not been silently zeroed. This is an identity plus a finite boundary estimate, not a bound for T itself.

### F. Quantitative Comparison And Complete Loss Accounting

The new unconditional scale is `H^3/log(2H)^(1/100)` for maximal energy. The desired sharp-shell benchmark is `H^(5/2-eta+epsilon)`. The polynomial gap is unfilled. CD2 alone would give only a logarithmically improved linear Mertens estimate after the usual shell Cauchy argument, weaker than the already inherited global exponent. Its value is new local/maximal information, not endpoint advancement.

CD1 also calibrates an explicit stronger sufficient supplier. Fix `0<eta<1/6`, set `h=floor(H^(2/3))`, and suppose independently that, for every epsilon>0 and all sufficiently large integer H,

```text
T_mu(H,h) <= C_(eta,epsilon) H^(17/6-eta+epsilon).     (OPEN-CD5)
```

Only an UPPER bound for the complete signed triangular sum is required, not absolute values of individual shifts. With H>=8, h is between H^(2/3)/2 and H^(2/3). In CD4 the diagonal costs at most `3H^2h=O(H^(8/3))` and the halo costs `O(h^3)=O(H^2)`. Multiplying by the smoothing factor `8H/h^2=O(H^(-1/3))` and restoring its boundary gives

```text
E_mu(H) << H^(7/3)+H^(5/2-eta+epsilon)+H^(5/3).
```

Because eta<1/6, the middle exponent dominates. This implies the actual scalar-shell bound, and dyadic Cauchy plus the O(sqrt x) final shell give

```text
M(x)=O_epsilon(x^(7/8-eta/4+epsilon)).                (CD5, conditional)
```

The same maximal rate returns to the hybrid fields by accepted C20-C22; physical activation costs O(H^2), still lower order. OPEN-CD5 is NOT proved. It is a stronger sufficient short-interval correlation target, not a proven necessary condition, not claimed equivalent to the canonical target, and not supplied by the logarithmic theorem. To improve on the already inherited strict gap, its final eta/4 must also exceed that existing gap; no such comparison is claimed.

### G. Original-Carrier Bridge And Full Physical Return

The [literal lifted carrier](https://github.com/OVVO-Financial/RH_Lean/blob/69aac0441b4df011cf7df3ba115169c3b66d72f5/research/LIFTED_MOBIUS_ADDRESS_INJECTIVITY_20261102.lean) uses the physical address q^2*m, actual nonzero mu(m), odd prime q, strict q^2<R, and `[R^2,(R+1)^2)`. Its injectivity and disjointness preserve every nonzero occurrence. The [zero-frequency splice](https://github.com/OVVO-Financial/RH_Lean/blob/69aac0441b4df011cf7df3ba115169c3b66d72f5/research/LOW_OWNER_AMPLITUDE_MELLIN_LEDGER_SPLICE.lean) retains coefficient 1/q. The [full Gram module](https://github.com/OVVO-Financial/RH_Lean/blob/69aac0441b4df011cf7df3ba115169c3b66d72f5/research/GLOBAL_RETURNED_CORE_FIRST_OWNER_GRAM.lean) does not discard cross-owner terms.

Reuse the independently accepted C25 physical identification, for R>=56:

```text
X_R=R^2-1,
A_R=M(R-1)-M(X_R)-sum_(q odd prime,q^2<R) M(floor(X_R/q^2))/q,
W_R=sum_(R^2<=n<(R+1)^2)g_R(n),
K_R=M(R+2)/q when R=q^2 with q odd prime, and 0 otherwise,
A_(R+1)-A_R=mu(R)-W_R-K_R.
```

A_R is the actual physical zero-frequency remainder, not the auxiliary primitive A(t) in E3. In the complete square retain

```text
sum_R |A_(R+1)-A_R|^2
 = sum_R [mu(R)^2+Z_R+K_R^2]
   +2 sum_R N_R -2 sum_R mu(R)W_R +2 sum_R W_R K_R,
W_R^2=Z_R+2N_R,       mu(R)K_R=0.
```

Accepted C25 proves `sum K_R^2<=3H^(3/2)` and pays all other restoration costs at O(H^2). Alternatively, applying the three-term square inequality directly to the exact root-step identity gives

```text
sum_R |A_(R+1)-A_R|^2
 <=3H+3 sum_R Omega_R(g_R)^2+9H^(3/2)
 << H^3/log(2H)^(1/100).                              (CD3-return)
```

The inequality pays, rather than removes, all mixed terms. No nonzero-frequency statement, ideal-character intertwiner, original #915 first-bad payment, or positive high-prime fullOwnerGamma bound is asserted. The maximal extension of the scalar [square-shell declaration](https://github.com/OVVO-Financial/RH_Lean/blob/69aac0441b4df011cf7df3ba115169c3b66d72f5/research/VF_919_SEVEN_EIGHTHS_SQUARE_SHELL_BRIDGE_20261019.lean) is paper mathematics here, not an existing compiled declaration.

### H. Falsification, Novelty And Circularity Review

**CD6 finite verification.** Tests were fixed before execution: every ternary word of length 8, with a five-site base window and h=1,...,4; genuine development blocks H=9,16,25; held-out validation H=49,64. No logarithmic asymptotic was fitted or numerically certified. Two independently constructed Mobius arrays, a prime-square sieve and divisor-convolution inversion, agree through n=16448. Exact integer/rational checks verify the smoothing identity, CD1, CD4, forward prime-dilation bound, strict-cutoff freezing, omitted-owner budget, and complete physical root-step identity.

Execution with Python 3.12.14 passed 26,244 word/length cases (551,124 interval telescoping checks), 163 physical root/block cases and 19 genuine short-moment cases. Some exact outputs:

| H | E_mu(H) | Tested h | J_mu(H,h) | CD4 boundary residual |
| --- | ---: | ---: | ---: | ---: |
| 9 | 444 | 4 | 702 | 0 |
| 16 | 992 | 6 | 2433 | -5 |
| 25 | 2473 | 8 | 8784 | 4 |
| 49 | 11095 | 13 | 57144 | -17 |
| 64 | 18300 | 16 | 121611 | -29 |

The last column is the signed boundary residual of CD4, not maximal energy. The appended complete reproducer disambiguates both quantities. Its SHA-256 is `8d82b19784788aad1a7f6083886a58faed86b3779d49ae7fcebfda1a4ab65db2`. The chosen h for the H^(2/3) tests is computed by integer cube comparison, with no floating-point decision. Test verdicts use only exact integers/rationals.

**Boundary necessity.** For the bounded comparison sequence 1,-1,1,-1,... and h=2 every smoothed sum vanishes, but a singleton fragment has magnitude one. Therefore deleting the h-1 boundary from CD1's proof is false. This finite test concerns the general smoothing lemma, not a Mobius counterexample.

**Why the Referee comparison is not a counterexample.** Its energy is at least `9H^3/256`. By CD1, whenever h<=3H/32 it must have `J_a(H,h)>=9H^2h^2/4096`. Consequently it cannot satisfy the short-average decay used in E2. Its nonmultiplicativity, not a hidden change of carrier, is exactly where it fails the independent input. No assertion about PC5 is inferred from this comparison.

**No illicit multiplicativity.** C23's genuine values g(9)=1/3, g(25)=1/5, g(225)=0 are retained. The short-average theorem is applied to mu alone; the hybrid is handled by a separate proven comparison. Growing primes are split explicitly in E3, not treated as fixed. The inherited 7/8 estimate is used solely on the long mean. All squareful daughter addresses and all positive/negative cross terms remain.

**Novelty scope.** Current source search and the retrieved November 2/3 derivations contain the short-average theorem citation, the warning about exceptional square sampling, the fragment-preserving inverse and the support-only obstruction. They do not contain CD1's completed smoothing-to-maximal argument or its logarithmic return CD2-CD3. This is a source-qualified consequence completing that particular missing transfer, not a claim to have invented the classical theorem or to have exhausted all repository history. Repository search also returned an older prime-comb discussion warning that almost-all results do not directly supply its pinned maximal target; CD1 does not claim that different carrier is paid.

### I. Conceptual Interpretation

The genuine arithmetic does rule out macroscopic, consistently aligned maximal fragments on a positive proportion of square shells: for every fixed lambda>0,

```text
#{H<=R<2H : Omega_R(g_R)>=lambda H}
 << lambda^(-2) H/log(2H)^(1/100).
```

This follows immediately from CD3 and includes adaptive fragment locations. It is a true all-scale restriction absent from the squarefree comparison class. It is not the square-root-size, diagonal-sized, or power-saving restriction still needed by the proof architecture.

The useful strategic change is local: stop treating sparse square sampling as an unbridged obstacle at every strength. A logarithmic bridge is now available on paper. The remaining obstacle for this method is the strength of the common-window signed correlation, plus the explicitly paid smoothing loss, not a missing informal identification of carriers. Other protected routes remain active.

### J. Specialist Handoffs And Continuity

**Coordinator:** register CD1-CD3 as PAPER_PROOF / SELF_AUDIT, not a new VERIFIED_ETA. C23's lack of a maximal transfer is resolved at logarithmic strength only. Retain the actual target gap and PC5's open status. Keep NYMAN next for this investigator, resuming C33-C35/NR6 rather than redoing the paid remote tail.

**Adversarial Referee:** independently audit the exact interval telescope, the inclusive-to-half-open MR correction, uniform delta/h choices, the prime preimage factor sqrt(p), the p>sqrt(X) tail, and the O(H^2) physical return. Verify CD4's boundary polynomial and CD5's exponents. Submitted author checks are SELF_AUDIT, not independent acceptance.

**Prime Census:** no wider empirical power fit is requested. If independent testing is useful, check CD1/CD4 on exact input and monitor `T_mu(H,floor(H^(2/3)))`, its squarefree diagonal, signed boundary and full J together. A test of OPEN-CD5 requires a frozen eta, epsilon, constant and range; growth plots alone cannot validate its quantified statement.

**Owner Payment:** the complete zero-frequency return now inherits the weak logarithmic bound, with the exact R=q^2 birth M(R+2)/q included. This does not control your prime-seat JOH/SAT carrier or a first-bad source. No carrier identification by terminology is requested.

**Finite Wheel:** on a future compatible investigation, a weighted signed restriction for the complete common-window lag sum in OPEN-CD5 would have an explicit maximal consumer. Fixed affine-cell absolute savings or completed-wheel positivity are not substitutes. Preserve your own MU-LIFT/CORR4/FINITE-AC rotation.

**Lean Verification:** no immediate proof PR is requested. CD1's finite smoothing inequality and CD4's exact boundary bound are implementation-sized only after independent acceptance and utility selection. CD2 additionally needs the external short-interval theorem, which is not claimed formally available. Do not encode that theorem or OPEN-CD5 as an unexplained project axiom.

Continuity was read at the following actual blobs; retrieval is not a claim of independently re-proving all historical sections:

| Role | November 2 | November 3 intake |
| --- | --- | --- |
| Coordinator mirrors | 1e932d4ce0eb0fd2c5f4507f6b111194d633eb32 | 8f22479e602b919c00ad5539a7442371c2ee6076 |
| Owner | abfe546d72b151f4cd200fc61de3197efe23a65c | d52c74b76c2914c3be694f39cd7afe9b122a4834 |
| Analytic | 8e48b59611aa1d0bfa3577ed0a4a3bc0d0fcae73 | 79f5f11020d7038028f4ddfe92ff3f95d4bd0798 |
| Wheel | abf8ac8c22a708886183849552c90dd62787ac8d | 15802d31f6b7abf3ffff97a5a57942baf3bc2d07 |
| Census | 2cd84c57ab18d923e97368764f29f4ccd2ec3bb3 | 5b564235ba20bf4a53c13dac0cc91d210d665a84 |
| Referee | 814af1684df66e6ac99b8df1f102cb592b316f89 | dff2382a732be1829ad7583e046ebbc64c61e4c9 |
| Lean | 02d19d792e26f072004cb5909f149538752626e9 | a9c65a6809323216f8a876845538b6af0fae393e |

All current-day role files exist. Yesterday's last Lean section is explicitly partial; today's C29 attempt is explicitly uncompiled and write-blocked. Neither is upgraded. Latest separate claims consumed include Owner-3's JOH excursion falsifier, Wheel-2's partial {2,3} packet signs, Census-3/4's common-offset obstruction, Referee-5/6/7's Nyman review/defect, and Coordinator-2's C33-C35 head/tail continuation. None supplies the missing CODIV power bound. External inbox blob `038018145c0fddb2f6306c0712373adf9cd1ea52` has no entry after October 18; EXT-20261018-PNT-1/3 and EXT-20261017-XCOORD-1 remain source/boundary safeguards, not current routing. No missing handoff, extra run or independent review was invented.

### K. First Independently Missing Analytic Theorem

For THIS smoothing mechanism the first target-strength unpaid input is OPEN-CD5, a one-sided signed triangular lag estimate on the actual mu values, with fixed eta before H and every epsilon loss. All its other maximal-transfer, diagonal, halo, owner, and physical activation costs have been displayed. The classical theorem proves a logarithmic relative gain only and cannot be substituted for the required `H^(-1/2-eta)` relative gain.

A weaker intermediate improvement to the rate of this same J or T would be genuine local progress even before OPEN-CD5. It should be stated with its own actual range and net exponent, without claiming that the current literature already gives a polynomial saving at vanishing amplitude tolerance. No new estimate for positive fullOwnerGamma, PC5, the canonical VF discrepancy, or the entire ideal-character exceptional Gram is established.

### L. Persistent Workspace And Next-Run Resume Capsule

```text
INVOCATION: 2026-11-03T17:11:01-05:00 SCHEDULED; RUN_ID_UNAVAILABLE
ROLE: RH | Analytic Type II
MAIN: 69aac0441b4df011cf7df3ba115169c3b66d72f5
ENGINE: 6fce99c61efb5b2a73c0cb1f1464f09b351fcd55
AGENTS: 9fa5e9519e2fb6dde22217aa2a18982dafef373a
CONTRACT: 88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a
TASK: CODIV maximal-fragment transfer at genuine multiplicative scope
RESUMED: 20261102-analytic-3; Coordinator C20-C25;
  Referee 20261103-referee-3/4; Census PC4, with PC5 still conjectural.
DEPLOYMENT_ACK: live policy consumed; actual new proof CD1-CD4,
  not a repetition of the bootstrap NYMAN task or old freezing census.
NEW_CLAIM: 20261103-analytic-3, CD1-CD6
MATHEMATICS: paper-proof logarithmic maximal bound; finite exact tests;
  independent review PENDING; NOT_FORMALIZED.
QUANTIFIED_RESULT: E_mu, moving/frozen hybrid maximal energy,
  and complete physical root-step energy << H^3/log(2H)^(1/100).
FIRST_OPEN_INPUT: common-window signed triangular correlation OPEN-CD5.
SOURCE_CI: existing #1079/#1081/#1082 green and human merged;
  new draft #1083 head 92defc3ce6f9517ac1a649af9a1ba643bad917e2
  has 11 green runs and dedicated 41729980802 IN_PROGRESS at closeout;
  it is not an input. No new Lean run or source edit by this agent.
ETA_GATE: inherited VERIFIED_ETA / ON_MAIN at its reviewed scope.
NEW_NET_ENDPOINT_GAIN: NONE; stronger conditional gain UNKNOWN.
ROUTE_COVERAGE: Nov 3 NYMAN analytic-1; OAI-NNS analytic-2;
  CODIV analytic-3. Next protected route NYMAN.
NEXT_NYMAN_STEP: resume C33-C35 and NR6 at the actual low-edit/middle
  residual; do not re-prove the accepted remote tail or fixed-low invariant.
NEXT_CODIV_STEP: attack T_mu with ordinary common-window shifts;
  retain explicit smoothing, diagonal and halo costs.
CANONICAL_VF / RH / SHARP_SHELL / PC5: OPEN.
EARLY_CHECKPOINT: 414c1d17d034a6a5be8861fec555d7870de3d99f,
  read back exactly at blob 75571cf8ffe5cb34c0c5189fab42817de4878c2e.
PUBLICATION: recorded by verified readback receipt below.
```

Only this role's authorized dated report is changed remotely. Direct clone access failed with a 403 proxy response; authenticated read tools supplied the actual sources, and that technical limitation did not prevent the research. No main/proof/policy/other-report write, agent launch, schedule change, merge, or permission change occurred.

### CD6 Exact Reproducer

The following is the complete executed script. It checks finite algebra and original-source reconstruction only; the logarithmic theorem is the proof above, not an extrapolation from this data.


```python
"""Exact checks for 20261103-analytic-3; not an asymptotic certificate.

Frozen tests: all ternary words of length 8, then genuine Mobius blocks
H=9,16,25 (development) and H=49,64 (validation). No fitted constants.
"""

from fractions import Fraction as F
from itertools import accumulate, product
from math import isqrt, prod
import json
import platform


def span(values):
    prefixes = [0] + list(accumulate(values))
    return max(prefixes) - min(prefixes)


def algebra_checks():
    count = 0
    for a in product((-1, 0, 1), repeat=8):
        n = 5
        for h in range(1, 5):
            sums = [sum(a[t:t+h]) for t in range(n)]
            for u in range(n + 1):
                for v in range(u, n + 1):
                    defect = h * sum(a[u:v]) - sum(sums[u:v])
                    restored = sum(sum(a[u:u+j]) - sum(a[v:v+j])
                                   for j in range(h))
                    assert defect == restored
                    assert abs(defect) <= h * (h - 1)
            jval = sum(s * s for s in sums)
            omega = span(a[:n])
            assert h*h*omega*omega <= 2*n*jval + 2*h*h*(h-1)**2
            diag = sum(x*x for x in a[:n])
            corr = sum(2*(h-d)*sum(a[t]*a[t+d] for t in range(n))
                       for d in range(1, h))
            boundary = jval - h*diag - corr
            assert 3*abs(boundary) <= h*(h-1)*(2*h-1)
            count += 1
    a = [1, -1] * 4
    assert span(a[:5]) == 1 and all(a[t]+a[t+1] == 0 for t in range(5))
    return count


def mobius_pair(limit):
    mu = [1] * (limit + 1)
    mu[0] = 0
    primes = []
    composite = [False] * (limit + 1)
    for p in range(2, limit + 1):
        if composite[p]:
            continue
        primes.append(p)
        for n in range(p, limit + 1, p):
            composite[n] = True
            mu[n] *= -1
        for n in range(p*p, limit + 1, p*p):
            mu[n] = 0
    inverse = [0] * (limit + 1)
    inverse[1] = 1
    for d in range(1, limit + 1):
        for n in range(2*d, limit + 1, d):
            inverse[n] -= inverse[d]
    assert mu == inverse
    return mu, primes


def genuine_checks():
    blocks = (9, 16, 25, 49, 64)
    top = 4 * max(blocks)**2 + max(blocks)
    mu, primes = mobius_pair(top)
    mertens = list(accumulate(mu))
    odd = [p for p in primes if 3 <= p <= 2*max(blocks)]
    den = prod(odd)
    complete = [den*x for x in mu]
    for p in odd:
        for n in range(p*p, top + 1, p*p):
            if mu[n//(p*p)]:
                assert complete[n] == 0
                complete[n] = (den//p)*mu[n//(p*p)]

    def field(r, cutoff):
        vals = []
        owners = [p for p in odd if p*p < cutoff]
        for n in range(r*r, (r+1)**2):
            value = den*mu[n]
            for p in owners:
                if n % (p*p) == 0 and mu[n//(p*p)]:
                    assert value == 0
                    value = (den//p)*mu[n//(p*p)]
            vals.append(value)
        return vals

    def ledger(r):
        x = r*r - 1
        return den*(mertens[r-1] - mertens[x]) - sum(
            (den//p)*mertens[x//(p*p)] for p in odd if p*p < r)

    omu = {r: span(mu[r*r:(r+1)**2]) for r in range(1, 2*max(blocks))}
    rows = []
    root_checks = 0
    moment_checks = 0
    for hroot in blocks:
        emu = sum(omu[r]**2 for r in range(hroot, 2*hroot))
        emov = 0
        efr = 0
        ereturn = 0
        for r in range(hroot, 2*hroot):
            moving = field(r, r)
            frozen = field(r, hroot)
            om = span(moving)
            of = span(frozen)
            oi = span(complete[r*r:(r+1)**2])
            assert (om-of)**2 <= 32*den*den
            dilation_bound = den*omu[r] + sum(
                (den//p)*omu[r//p] for p in odd if p <= r)
            assert oi <= dilation_bound
            omitted_bound = sum(
                F(((r+1)**2-1)//(p*p) - (r*r-1)//(p*p), p)
                for p in odd if p*p >= r)
            assert F(abs(oi-om), den) <= omitted_bound
            q = isqrt(r)
            activation = (den//q)*mertens[r+2] if q*q == r and q in odd else 0
            change = ledger(r+1)-ledger(r)
            assert change == den*mu[r] - sum(moving) - activation
            emov += om*om
            efr += of*of
            ereturn += change*change
            root_checks += 1
        witnesses = []
        length = 1
        while (length + 1)**3 <= hroot*hroot:
            length += 1
        for h in sorted({1, 2, length, hroot//2}):
            left, right = hroot*hroot, 4*hroot*hroot
            sums = [mertens[n+h-1]-mertens[n-1] for n in range(left, right)]
            jval = sum(s*s for s in sums)
            assert h*h*emu <= 8*hroot*jval + 2*hroot*h*h*(h-1)**2
            diag = sum(mu[n]**2 for n in range(left, right))
            corr = sum(2*(h-d)*sum(mu[n]*mu[n+d] for n in range(left, right))
                       for d in range(1, h))
            boundary = jval-h*diag-corr
            assert 3*abs(boundary) <= h*(h-1)*(2*h-1)
            witnesses.append({'h': h, 'J': jval, 'boundary': boundary})
            moment_checks += 1
        rows.append({'H': hroot, 'mu_max_energy': emu,
                     'moving_max_energy': str(F(emov, den*den)),
                     'frozen_max_energy': str(F(efr, den*den)),
                     'full_return_energy': str(F(ereturn, den*den)),
                     'moments': witnesses})
    return {'mu_arrays_match_through': top, 'root_checks': root_checks,
            'moment_checks': moment_checks, 'rows': rows}


if __name__ == '__main__':
    result = {'python': platform.python_version(),
              'ternary_word_length_pairs': algebra_checks(),
              'genuine': genuine_checks(),
              'scope': 'Exact finite identities and inequalities only; no asymptotic test.'}
    print(json.dumps(result, indent=2))
```

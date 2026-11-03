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



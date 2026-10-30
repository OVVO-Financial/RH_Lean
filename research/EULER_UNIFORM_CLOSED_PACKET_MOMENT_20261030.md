# Complete 2-adic Euler packets: a power-saving uncentered LOW-SOURCE moment

Date: 2026-10-30. Scope: genuine original Möbius factor pairs, positive square roots, all principal terms, and correct physical admission. **PAPER_PROOF_NEEDS_INDEPENDENT_REVIEW** for the analytic moment. The accompanying Lean files prove the coefficient identities, activation bookkeeping, principal decomposition, finite Gram identity and square-exception bound, subject to their exact-head CI. **The complete original square-shell power-saving theorem is NOT proved. No Mertens exponent improvement or RH claim.**

## 1. The missing genuine 4d partner

Let X_R=R²-1 and f_d(R)=((R²-1) mod d)/d for positive R. Define the original completed coefficient

    alpha_d = sum_(1<=a<b, ab=d) mu(a)mu(b).

For odd nonsquare d, actual Möbius multiplicativity gives

    alpha_(2d)=-2alpha_d,     alpha_(4d)=alpha_d.

These are not assumed scalar coefficients. The exact proof uses (mu*mu)(d)=2alpha_d for nonsquares, multiplicativity of the actual Dirichlet convolution, and its local values (mu*mu)(2)=-2, (mu*mu)(4)=1. At a square, every nonzero pair has both factors squarefree; their square product forces them equal, excluded by a<b, hence alpha_(k²)=0.

The complete eligible packet is therefore

    2alpha_d K_d(R),
    K_d(R)=f_d(R)-2f_(2d)(R)+f_(4d)(R).

Pairing just d with 2d leaves a principal of size -alpha_d. The original 4d even-even partner is essential to the improvement below.

For every odd d, including squares, the full coefficient formulas are

    alpha_(2d)=-2alpha_d-s_d,     alpha_(4d)=alpha_d,
    s_d=mu(k)^2 if d=k², and 0 otherwise.

In particular d=1 contributes the original pair (1,2). It cannot be discarded.

## 2. An exact original, uncentered, fully admitted subsource

For Q>=1 set

    V_Q(R)=2 sum_(odd d<=Q)
       [alpha_d f_d(R)+alpha_(2d)f_(2d)(R)+alpha_(4d)f_(4d)(R)].

When 4Q<R, EVERY original factor pair in these columns is admitted by a<b<R. Thus V_Q is precisely the part of twice eulerFractionOffQ R whose product ab has odd part <=Q. No cloned or deleted occurrence: a nonzero Möbius product has 2-adic exponent 0,1,or2, and the odd part is unique.

The exact decomposition is

    V_Q=Z_Q+E_Q,
    Z_Q(R)=2 sum_(odd d<=Q) alpha_d K_d(R),
    E_Q(R)=-2 sum_(odd k, k²<=Q) mu(k)^2 f_(2k²)(R).

The square exception is paid without cancellation:

    |E_Q(R)|<=2 floor(sqrt Q),
    sum_(R in I) E_Q(R)^2 <=4 |I| Q.

The accompanying square-exception Lean module proves its coefficient, absolute mass and energy bound. The displayed identification of all original odd-part fibers still needs its complete finite-Fubini Lean assembly; its mathematical proof is the unique 2-adic factorization described above.

**Root-zero convention:** use least nonnegative residues of the INTEGER polynomial R²-1 for complete periods, represented by R=1,...,d. At R=0, natural-number subtraction gives 0 instead of -1; silently using that truncated value corrupts the mean. The physical Lean means use positive representatives.

## 3. Main paper theorem

For every epsilon>0 there is an effective C_epsilon such that, uniformly over every interval I of H consecutive positive roots and every Q>=1,

    sum_(R in I) |Z_Q(R)|²
       <= C_epsilon [H Q^(1+epsilon)+Q^(3+epsilon)].       (A)

The SAME estimate holds for V_Q after including E_Q. Consequently, when 4Q<H,

    sum_(H<=R<2H) |V_Q(R)|²
       <= C_epsilon [H Q^(1+epsilon)+Q^(3+epsilon)]        (B)

is a bound for the actual fully admitted uncentered closed low source, not only a centered model. For Q²<=H this saves one power of Q, up to epsilon, against the elementary triangle-energy benchmark H Q^(2+epsilon).

The proof below uses finite Fourier algebra, quadratic Gauss orthogonality and elementary divisor estimates. It does not assume an improved Mertens bound, imported OAI exponent, random signs, or a cross-term sign.

## 4. All-frequency Gauss bound, INCLUDING frequency zero

Let a_m(x)=x/m on x=0,...,m-1, e_m(x)=exp(2 pi i x/m), and normalize Fourier coefficients by 1/m. Then

    hat a_m(0)=(m-1)/(2m)=c_m,
    |hat a_m(k)|=1/[m |1-e_m(-k)|] for 0<k<m.

For the quadratic column f_m(r)=a_m(r²-1),

    hat f_m(h)=c_m*1_(h=0)
      + sum_(k=1)^(m-1) hat a_m(k)e_m(-k)
          *m^(-1) sum_(r mod m)e_m(k r²-h r).

For every positive m, even or odd, the complete quadratic sum satisfies

    |sum_(r mod m)e_m(k r²-h r)|² <= m*gcd(2k,m).

Indeed, squaring and setting x=y+t leaves a geometric inner sum over y. It is zero unless m divides 2kt and otherwise equals m. Exactly gcd(2k,m) residues t survive. Take absolute values only after this orthogonality. No inverse of 2 is assumed.

Pair k with m-k, use |1-e_m(k)|>=4 min(k,m-k)/m and gcd(2k,m)<=2gcd(k,m). Group by divisors of m. For an absolute constant C0,

    |hat f_m(h)-c_m*1_(h=0)|
      <= C0(1+log(2m))*sigma_(-1/2)(m)/sqrt(m)=A(m).       (C)

The estimate includes h=0, where it bounds the actual quadratic-principal bias rather than assuming root equidistribution.

Lift f_d,f_(2d),f_(4d) to period 4d. The first is supported at Fourier frequencies divisible by 4, the second at frequencies divisible by 2, the third at every frequency. At zero,

    c_d-2c_(2d)+c_(4d)=-1/(8d).

Thus every Fourier coefficient of the CLOSED kernel, including zero, obeys

    |hat K_d(h)|<=B(d),
    B(d)=C1(1+log(8d))*sigma_(-1/2)(4d)/sqrt(d),           (D)

with a sufficiently large absolute C1. This is the key change: the genuine principal now obeys the same square-root Gauss envelope as the other frequencies.

Its exact mean is not zero:

    mean K_d=-1/(8d)+(m_d-c_d)-2(m_(2d)-c_(2d))+(m_(4d)-c_(4d)).

All these biases are retained in Lean; only the analytic estimate (C)-(D) is paper-level.

## 5. Actual packet interactions and incomplete windows

For d,e put g=gcd(d,e), L=lcm(4d,4e)=4lcm(d,e). The product-frequency map

    Z/(4d) x Z/(4e) -> Z/L

is onto and has precisely gcd(4d,4e)=4g preimages at each frequency. Every normalized Fourier coefficient of K_d K_e therefore has magnitude <=4g B(d)B(e).

For any interval I of H roots, retain the zero mode and bound each nonzero interval-character sum by L/[2min(n,L-n)]. Their sum is <=L(1+log L). Since 4gL=16de,

    |sum_(R in I)K_d(R)K_e(R)|
      <=4g H B(d)B(e)+16de B(d)B(e)(1+log L).            (E)

This permits nonzero shared-prime covariance of either sign. No packet independence is asserted.

Expand Z_Q² with every signed alpha_d alpha_e cross term BEFORE bounding it. Use |alpha_d|<=tau(d), the elementary fixed-epsilon divisor bounds, and

    sum_(d,e<=Q)gcd(d,e)/sqrt(de)<=4Q(1+log Q).

The complete-frequency contribution in (E) is O_epsilon(HQ^(1+epsilon)). The incomplete contribution is bounded by a logarithm times

    [sum_(d<=Q)|alpha_d|sqrt(d)(1+log(8d))*sigma_(-1/2)(4d)]²
       <<_epsilon Q^(3+epsilon).

Choose the smaller divisor epsilons consistently so that the final exponent is epsilon. This proves (A). Then |Z_Q+E_Q|²<=2|Z_Q|²+2|E_Q|² and the proved O(HQ) exception energy yield (B), including their mixed interaction with only a constant-factor cost.

## 6. Exact progress and an essential sharp-shell comparison

For the UNcentered static-source ledger, (B) improves the previous bound

    H Q^(2+epsilon)+Q^(3+epsilon)

to

    H Q^(1+epsilon)+Q^(3+epsilon).

A closed low source is affordable at a proposed H^(5/2-eta+epsilon) budget up to

    Q=floor(H^(5/6-eta/3-kappa)),

for fixed 0<eta<1/2, positive kappa with positive cutoff exponent, sufficiently small epsilon margins and sufficiently large H so 4Q<H.

**Do not turn this comparison into an automatic sharp-shell gain.** When one first differences a STATIC low source in R, its constant principal already cancels. The pre-existing centered Q³ estimate can then have the same cutoff power. Accordingly, this work proves a stronger uncentered closed-packet estimate and a source-exact completion mechanism; it does NOT establish an improved optimized sharp-shell frontier merely by comparing the old uncentered principal cost.

## 7. The still-unproved complete source

The original full source contains products of order H² and genuinely moving coefficients beta_d(R). Replacing them by completed alpha_d is false (e.g. the original 2p activation family). For each eligible packet the Lean identity keeps the three exact missing-owner terms; they disappear only after all its factors are admitted.

Existing native square-window algebra gives, for R>=3,

    Delta_R=-W_R+B_R,  |B_R|<=5,
    W_R=(2R+1)s_R²+F_R,
    s_R=sum_(a<R)mu(a)/a,
    F_R=sum_(a,b<R)mu(a)mu(b)[f_(ab)(R)-f_(ab)(R+1)].

The original complete-source energy target must control this W_R, not just the prefix off-diagonal. After the closed low packets and their square exceptions are split off, the unpaid statistic is the **joint** remaining historical fractional window, reciprocal-square drift, diagonal window and all their signed cross terms. Bounding that joint statistic by H^(5/2-eta+epsilon) is NOT proved here. Nor is a global favorable cross-term sign proved.

Setting Q~H² in (A) makes the Q³ remainder of order H^6; it is not a route to the desired bound. The finite packet identities or disappearance of a principal term do not justify discarding the high-product complement or its physical activation corrections. No improved Mertens exponent is claimed.

## 8. Regression and formal status

The committed script scripts/euler_uniform_closed_packet_regression.py independently enumerates genuine factor pairs and checks 600 odd moduli d<=1200, 5400 pointwise identities, 51 positive-period means and physical original-source reconstruction at (R,Q)=(17,3),(35,8),(64,15),(317,17),(1027,32). All calculations use exact integers/Fractions. These are finite falsification/regression checks, not the proof of (A)-(B).

Selected exact-rational energies (decimal renderings) and principals:

| H | Q | closed family energy | actual closed principal | eligible two-column principal |
|---:|---:|---:|---:|---:|
|64|8|105.9657142857|59/252|3|
|127|11|366.3487218505|-2411/4158|4|
|317|17|2448.7977088357|-4013657/4594590|4|
|1027|32|13863.6972251468|-1179689554754/644658718275|6|

Uniform Lean source files:
- EULER_UNIFORM_COMPLETED_COEFFICIENTS_20261030.lean: genuine convolution/strict-factor bridge and alpha_(2d) relation.
- EULER_UNIFORM_CLOSED_PACKETS_20261030.lean: alpha_(4d), all three actual activations, exact principal cancellation and all signed finite Gram terms.
- EULER_UNIFORM_SQUARE_EXCEPTIONS_20261030.lean: square-root exceptions, actual alpha_(2k²), and uniform O(HQ) energy.

The all-frequency Gauss bound (C), product-frequency estimate (E), epsilon divisor summation, source-Fubini assembly and asymptotic (A)-(B) still require Lean formalization. Their paper proof must undergo independent review. Successful structural CI does NOT certify the full analytic theorem or the absent full-source saving.

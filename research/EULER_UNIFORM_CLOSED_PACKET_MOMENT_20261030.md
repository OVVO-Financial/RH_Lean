# Complete 2-adic Euler packets: a power-saving UNcentered low-source moment

Date: 2026-10-30. Scope: genuine original Möbius factor pairs, positive square roots, all principal terms, and correct physical admission. Status: **PAPER_PROOF_NEEDS_INDEPENDENT_REVIEW** for the analytic moment; accompanying coefficient/packet Lean modules require exact-head CI. **Not a full square-shell bound, not a new Mertens exponent, not RH.**

## 1. Why two columns were incomplete

Let X_R=R²-1 and f_d(R)=((R²-1) mod d)/d for R>=1. Let

    alpha_d = sum_(1<=a<b, ab=d) mu(a)mu(b).

For odd nonsquare d the ORIGINAL coefficients satisfy

    alpha_(2d) = -2 alpha_d,    alpha_(4d) = alpha_d.

The first identity alone gives the binary packet at d,2d with a principal of size -alpha_d. The 4d coefficient is not optional: it is the original even-even partner (2a,2b). The complete eligible packet is

    2 alpha_d K_d(R),
    K_d(R) = f_d(R) - 2 f_(2d)(R) + f_(4d)(R).

This is not an arbitrary choice of weights. The weights are forced by the actual Möbius convolution and unique factorization. Proof: for a positive nonsquare d, (mu*mu)(d)=2alpha_d. The actual convolution is multiplicative with local values (mu*mu)(2)=-2 and (mu*mu)(4)=1. For odd d both coprimality facts hold; 2d is never square and 4d is square iff d is. Square moduli have no nonzero strict unordered pair, since two squarefree naturals with square product must be equal.

For EVERY odd d, including squares, the full formulas are

    alpha_(2d) = -2 alpha_d - s_d,
    alpha_(4d) = alpha_d,
    s_d = mu(k)^2 if d=k², and 0 otherwise.

Thus no diagonal-type square exception may be erased. The special d=1 contributes the original pair (1,2).

## 2. The exact original closed low source

For integer Q>=1 define

    V_Q(R) = 2 sum_(odd d<=Q)
       [alpha_d f_d(R) + alpha_(2d) f_(2d)(R) + alpha_(4d) f_(4d)(R)].

Whenever 4Q<R, every original factor pair in these product columns is physically admitted. Consequently V_Q(R) is EXACTLY the part of twice eulerFractionOffQ R whose product ab has odd part <=Q. No pair is counted twice: every nonzero Mobius product has 2-adic exponent 0,1,or2, and its odd part is unique. Products with higher powers of 2 have zero original coefficient.

The decomposition is

    V_Q(R) = Z_Q(R) + E_Q(R),
    Z_Q(R) = 2 sum_(odd d<=Q) alpha_d K_d(R),
    E_Q(R) = -2 sum_(odd k, k²<=Q) mu(k)^2 f_(2k²)(R).

The square-exception bound is unconditional and pointwise:

    |E_Q(R)| <= 2 floor(sqrt Q).

It is an original arithmetic term, not a new assumption. All alpha_d with square d vanish in Z_Q.

**Principal warning:** f_d is periodic as a function of the integer polynomial R²-1, using its least nonnegative residue. At residue R=0, that means (-1) mod d, not the truncated natural subtraction 0²-1=0. The Lean physical means use positive representatives 1..d, agreeing exactly with the integer-polynomial period. Every physical root in the theorem is positive.

## 3. Main theorem and exact scope

For every epsilon>0 there is an effective C_epsilon such that for every interval I of H consecutive positive integers and every Q>=1,

    sum_(R in I) |Z_Q(R)|²
      <= C_epsilon [H Q^(1+epsilon) + Q^(3+epsilon)].       (A)

The SAME bound holds for V_Q after adding E_Q. In particular, on H<=R<2H, if 4Q<H, this is a bound for the **genuine fully admitted uncentered closed low-product source**, including its principal contribution:

    sum_(H<=R<2H) |V_Q(R)|²
      <= C_epsilon [H Q^(1+epsilon) + Q^(3+epsilon)].       (B)

No Mertens bound, zero-free strip, imported OpenAI exponent, random signs, or conjectural cross-term sign enters this theorem.

For Q²<=H, (B) is O_epsilon(H Q^(1+epsilon)), saving one Q (up to epsilon) against the pointwise-triangle energy H Q^(2+epsilon). Unlike the previous centered low-conductor estimate, there is NO unpaid O(H Q²) principal bill inside V_Q.

## 4. ALL-frequency quadratic Fourier estimate, including the principal

Let a_m(x)=x/m on x=0,...,m-1 and e_m(x)=exp(2 pi i x/m). Normalize the finite Fourier transform by 1/m. Then

    hat a_m(0)=(m-1)/(2m)=:c_m,
    |hat a_m(k)|=1/[m |1-e_m(-k)|]   (0<k<m).

For a quadratic root column f_m(r)=a_m(r²-1),

    hat f_m(h)=c_m*1_(h=0)
      + sum_(k=1)^(m-1) hat a_m(k) e_m(-k)
          * (1/m) sum_(r mod m) e_m(k r²-h r).

The Gauss sum obeys for EVERY positive m, including even and nonprimitive cases,

    |sum_(r mod m) e_m(k r²-h r)|² <= m*gcd(2k,m).

Proof: square the modulus, substitute x=y+t; the inner sum over y is zero unless m divides 2kt, and otherwise is m. There are gcd(2k,m) surviving t. Triangle inequality is used only after this exact character orthogonality.

Pair k with m-k, use |1-e_m(k)|>=4 min(k,m-k)/m and gcd(2k,m)<=2gcd(k,m), then group by the divisors of m. With a safe absolute constant C0,

    |hat f_m(h)-c_m*1_(h=0)|
      <= C0 (1+log(2m))*sigma_(-1/2)(m)/sqrt(m) =: A(m).  (C)

This holds for h=0 as well. It bounds the actual quadratic principal bias; it does not assume that the roots are uniformly distributed among residues.

Lift the transforms of f_d, f_(2d), f_(4d) to the same root period 4d. The f_d term appears at frequencies divisible by 4, the f_(2d) term at frequencies divisible by 2, and f_(4d) at every frequency. At frequency zero their uniform main terms cancel exactly to

    c_d - 2c_(2d) + c_(4d) = -1/(8d).

Therefore EVERY normalized Fourier coefficient of K_d, INCLUDING ZERO, satisfies

    |hat K_d(h)| <= B(d),
    B(d) = C1 (1+log(8d))*sigma_(-1/2)(4d)/sqrt(d),       (D)

for a sufficiently large absolute C1. This is the key improvement: after the genuine 4d partner is restored, the principal is subject to the same square-root Gauss envelope as the other frequencies.

The true mean is not zero. In the original positive-root notation m_d, it is exactly

    mean K_d = -1/(8d) + (m_d-c_d)-2(m_(2d)-c_(2d))+(m_(4d)-c_(4d)).

Its bound follows from (C); its value is never discarded.

## 5. Exact packet interactions: GCD frequencies and incomplete windows

For d,e put g=gcd(d,e) and L=lcm(4d,4e)=4 lcm(d,e). The product-frequency map

    Z/(4d) x Z/(4e) -> Z/L

is onto and has exactly gcd(4d,4e)=4g preimages at each frequency. Thus every normalized Fourier coefficient of K_d K_e is at most

    4g B(d)B(e).

The zero-frequency term is retained. For an interval I of H consecutive roots,

    |sum_(R in I) K_d(R)K_e(R)|
      <= 4g H B(d)B(e)
         + 16de B(d)B(e)*(1+log L).                      (E)

Indeed, each nonzero interval character sum is at most
L/[2 min(n,L-n)], and their sum is at most L(1+log L); use 4gL=16de. This proves a bound on the ACTUAL signed packet interactions, not a declaration of independence. Both signs and all shared-prime zero modes are allowed.

Expand Z_Q² before bounding. The coefficients obey |alpha_d|<=tau(d), and sigma_(-1/2)(4d), tau(d), and all logarithms are bounded by C_epsilon d^epsilon. The complete-period contribution is controlled by

    sum_(d,e<=Q) gcd(d,e)/sqrt(de) <= 4Q(1+log Q).

The incomplete contribution is controlled by

    (sum_(d<=Q) |alpha_d| sqrt(d) (1+log(8d))
                  sigma_(-1/2)(4d))² * O(log(8Q²))
      <<_epsilon Q^(3+epsilon).

Using (E) and dividing epsilon consistently across the divisor factors gives (A), uniformly in H,Q. Adding E_Q with |E_Q|<=2sqrt Q and |x+y|²<=2|x|²+2|y|² proves (B) with only O(HQ) extra cost. This retains its mixed interaction by a constant-factor bound; there is no exponent loss.

## 6. What this actually advances

The prior UNcentered low-product estimate was

    H Q^(2+epsilon) + Q^(3+epsilon),

because the principal remained of size O(Q^(1+epsilon)). The closed packet bound (B) replaces it by

    H Q^(1+epsilon) + Q^(3+epsilon).

For a proposed shell energy H^(5/2-eta+epsilon), 0<eta<1/2, choose

    Q=floor(H^(5/6-eta/3-kappa)),  kappa>0,

with positive exponent, suitable epsilon margin and sufficiently large H that 4Q<H. The closed low source then lies strictly inside that target budget. This advances the affordable product cutoff from the previous crude-principal scale H^(3/4-eta/2) to H^(5/6-eta/3), up to fixed margins.

**The complete square-block theorem is still NOT proved.** The original source also contains odd parts >Q, including moving products of order H². The above estimate does not control their mixed interaction with V_Q, the rank-one reciprocal square, the original diagonal, or the final floor-to-sharp-shell transfer. Taking Q~H² in (A) gives an unacceptable Q³ cost, not the desired global power saving. No source theorem is obtained by ignoring those terms or inserting a hypothetical bound for them.

## 7. Exact regression (not a proof of asymptotics)

A rational-arithmetic regression checked 600 odd moduli d<=1200, 5400 pointwise original-coefficient packet identities, 51 positive-period mean identities, and independent original factor-pair reconstruction at (R,Q)=(17,3),(35,8),(64,15),(317,17),(1027,32).

Selected complete closed-source root-window energies and principals:

| H | Q | exact energy (decimal rendering) | actual closed principal | two-column eligible principal |
|---:|---:|---:|---:|---:|
| 64 | 8 | 105.9657142857 | 59/252 | 3 |
| 127 | 11 | 366.3487218505 | -2411/4158 | 4 |
| 317 | 17 | 2448.7977088357 | -4013657/4594590 | 4 |
| 1027 | 32 | 13863.6972251468 | -1179689554754/644658718275 | 6 |

These compare different complete packet groupings, not a claim that a fixed sample must obey a monotone energy improvement. No fitted exponent is used in (A)-(B).

## 8. Formal verification boundary

The new Lean modules prove original coefficient pairing, true d/2d/4d source reconstruction, actual activation terms, the exact cancellation of the uniform-residue principal, the retained quadratic-principal bias, and the fully expanded finite signed Gram identity.

The universal Gauss/Fourier bound (C), normalized product-frequency estimate (E), divisor-epsilon summation and asymptotic moment (A)-(B) are paper proofs here and are NOT claimed kernel-checked merely because those structural modules compile. The complete original-source fixed-eta theorem remains a separate, unpaid arithmetic obligation.

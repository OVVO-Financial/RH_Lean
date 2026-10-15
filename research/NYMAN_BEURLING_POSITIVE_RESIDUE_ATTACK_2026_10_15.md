# Nyman–Beurling positive-residue attack — 2026-10-15

STATUS: PAPER_PROOF (elementary exact identities and omission obstruction); FINITE_COMPUTATION (exact integer certificate and floating Gram diagnostics). The classical Báez-Duarte equivalence and Burnol lower bound are external results, NOT newly proved in Lean. No new global Mertens exponent bound, zero-free half-plane, or RH proof is claimed. This is a genuinely distinct analytic carrier from the #951/#954 signed floor sums; retain the existing #949 exponent/zero translator unchanged.

## 1. The exact discrete positive model

For integers k>=2 and 0<x<=1 define phi_k(x)={1/(kx)}-{1/x}/k. On 1/(m+1)<x<=1/m:

    phi_k(x)=(m mod k)/k=:a_k(m).

For F_N=sum_(2<=k<=N) c_k phi_k, the squared L2(0,1) distance from 1 is exactly

    D_N(c)^2=sum_(m>=1) [1-sum_k c_k a_k(m)]^2/[m(m+1)].

Define d_N^2=inf_c D_N(c)^2. The Gram entries are G_kl=sum_m a_k(m)a_l(m)/[m(m+1)] and h_k=sum_m a_k(m)/[m(m+1)]=log(k)/k. G is positive definite for the full finite family: vanishing on m=1,...,N-1 implies all c_k vanish, by the increment identity

    F_N(m)-F_N(m-1)=A-sum_(2<=k<=N,k|m)c_k,
    A=sum_(2<=k<=N)c_k/k, F_N(0)=0.

For L=lcm(k,l), the infinite Gram series reduces to the finite L-term digamma sum:

    G_kl=sum_(r=1)^L a_k(r)a_l(r)
         [psi((r+1)/L)-psi(r/L)]/L.

The SciPy experiment uses this exact formula with DOUBLE-PRECISION evaluations; it is not an interval-certified optimum.

## 2. Positive geometry still contains Möbius inversion

If one enforces F_N(m)=1 for all 1<=m<N, then A=1 and the increment identity gives sum_(2<=k|m)c_k=1 for 2<=m<N. Möbius inversion uniquely forces

    c_k=-mu(k) (2<=k<N);
    c_N=N*sum_(d<N)mu(d)/d.

This is exact finite algebra. Such interpolation is NOT an all-N Hilbert-error bound: the region m>=N can dominate. Optimized positive Gram coefficients are not forced to use these interpolation coefficients.

## 3. A new elementary all-scale sparse-basis obstruction

For ANY modulus k>=2 except 6,

    2*a_k(1)-a_k(3)-a_k(5)+a_k(6)=0.

For k>6 it is 2-3-5+6=0; k=2,3,4,5 are four exact residue checks. At k=6 the expression equals -1. Thus every finite (or limit) approximation F built from moduli excluding 6 satisfies

    2*r_1-r_3-r_5+r_6=1, r_m=1-F(m).

The genuine Hilbert weights at m=1,3,5,6 are 1/2,1/12,1/30,1/42. Cauchy–Schwarz gives

    1 <= (8+12+30+42)*sum_(m in {1,3,5,6})w_m*r_m^2
      =92*sum_(m in {1,3,5,6})w_m*r_m^2,

hence **D(F)^2 >= 1/92**, uniformly for all N and all coefficients when 6 is omitted. A prime-only basis is therefore permanently insufficient. This is a positive norm obstruction derived from discrete arithmetic, not an empirical limit.

More generally, omitting any squarefree q forces a positive floor: define L_q(F)=sum_(d|q)mu(q/d)[F(d)-F(d-1)] with F(0)=0. For the residue basis, L_q(F)=-c_q. On the constant target L_q(1)=mu(q)≠0. Since L_q uses finitely many Hilbert coordinates with positive weights, bounded dual norm gives a uniform positive distance. The argument does not settle omitting squareful k with mu(k)=0.

## 4. Exact finite rational certificate

For c_k=p_k/Q and L=lcm(2,...,N), the residual numerator at any integer m is

    Q*L*(1-F_N(m))
       =Q*L-sum_k p_k*(m mod k)*(L/k).

It is an integer. The first T squared error contributions are individually rounded UP to units 2^-64. The tail is bounded using |1-F_N(m)|<=1+sum_k|c_k| and sum_(m>T)1/[m(m+1)]=1/(T+1).

The submitted standard-library Python verifier uses N=16, Q=32768, T=2,000,000 and reports exact integer values:

    rounded partial: 330864155671387940
    rounded tail:       479349618301436
    rounded total:   331343505289689376
    common scale:   18446744073709551616.

The direct integer inequality 500*total<9*scale proves **d_16^2<9/500=0.018**. No floating point enters this certificate. This is only a finite upper bound; it does not prove convergence to zero.

## 5. Parameterized positive Hilbert route to the exponent wall

For a>=1/2 introduce the weighted norm

    ||f||_a^2=integral_(0,1)|f(x)|^2*x^(2a-1)dx,

and distance d_(N,a) to 1 using the same basis. The step weight is [m^(-2a)-(m+1)^(-2a)]/(2a). The Mellin identity (analytic continuation from Re(s)>1) is

    integral_0^1 phi_k(x)x^(s-1)dx
      =(1/k-k^(-s))*zeta(s)/s.

At any zeta zero rho=beta+it with beta>a the Mellin functional annihilates the entire basis and has dual norm 1/sqrt(2(beta-a)). Since it equals 1/rho on the target, for every N,

    d_(N,a)^2>=2(beta-a)/|rho|^2.

Therefore the independently proved condition d_(N,a)->0 would exclude ALL zeros with Re(rho)>a, and by zero symmetry confine them to [1-a,a]; merged #949 then implies lambda_M<=a. This is a SUFFICIENT criterion for a>1/2; no converse is asserted here. At a=1/2 the integer-dilation density/RH equivalence is Báez-Duarte's published criterion.

At a finite cutoff, an upper certificate d_(N,a)^2<=U only implies beta<=a+U(1+H^2)/2 for putative zeros with |Im rho|<=H, so it cannot produce a uniform all-height zero-free band.

## 6. The impossible square-scale rate (Burnol)

Burnol proved an unconditional logarithmic lower obstruction for the classical Nyman–Beurling distance. Since the centered integer-modulus span through N lies inside the continuous dilation span with theta>=1/N, the same inequality applies:

    liminf_(N->infty) d_N^2*log N>=c_0>0

(the positive c_0 includes actual critical-line zeros with squared multiplicities). Therefore, along N_j=N_0^(2^j), any eventual rule d_(N_(j+1))^2<=q*d_(N_j)^2 with fixed q<1/2 is IMPOSSIBLE: it would give d_(N_j)^2 log N_j<=C(2q)^j->0. A weaker q in [1/2,1) remains viable but is still unproved and RH-strength.

## 7. Finite tests (approximate Gram, not proof of convergence)

Full-basis d_N^2 at N=2,4,16,64,96,128,256:

    0.3068528194, 0.0659516942, 0.0179362670,
    0.0113924747, 0.0104205702, 0.0096703454,
    0.0082422560.

Observed square ratios 2->4 ≈0.215, 4->16 ≈0.272, 16->256 ≈0.460. These finite ratios do NOT establish q<1/2, which Burnol rules out eventually.

The decisive sparse-basis test at N=128:
    full:0.00967035; omit-six:0.01712948;
    primes-only:0.02851375; squarefree-only:0.00999056.
The full basis crosses below 1/92 while omit-six cannot. Squarefree-only is not proved dense; numerics alone cannot settle it.

Weighted tests at N=64 (different norms, finite diagnostics only):
    a=.5:0.0113925; a=.6:0.00522447;
    a=.75:0.00156065; a=.9:0.000447429.

## Research decision

CONTINUE the original full-basis and weighted-geometry line; preserve the omission floor as regression. REJECT the q<1/2 contraction conjecture. No global upper estimate was established. The new independent payment would be a proved (possibly slow) decay of d_(N,a), not monotonicity, a finite Gram fit, or the existing zero-equivalence relabeled as a bound. No Lean kernel claim is made for the external Nyman/Burnol theorems.

Primary literature:
- https://arxiv.org/abs/math/0202141 (Báez-Duarte, integer-dilation criterion).
- https://arxiv.org/abs/math/0103058 (Burnol, positive log lower bound).
- Compiled RH_Lean translator: research/MERTENS_CONVERSE_IDENTIFICATION.lean.

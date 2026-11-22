# Signed NNS resolvent integral: MVT, pathwise/a.s. convergence, and p-adic index payment

Date: 2026-11-21

**Theorem status.** The real integral identity, finite quadrature error, and almost-sure convergence below are proved for every FIXED nonsingular integer matrix. A cohomological presentation of the actual realized Alpöge Sha groups by RH_Lean's NNS arithmetic is NOT proved. The accompanying Lean file formalizes the NNS reassembly, telescoping Abel boundary, integral mean value, and abstract uniform-error -> a.s. step; the complete matrix spectral bound is a paper proof pending Lean formalization. No RH-strength result is claimed.

## 1. Exact determinant/resolvent identity

Let M be an m-by-m integer matrix, m>=1, with D=det(M) nonzero. Put B=M^T M, with positive real eigenvalues lambda_i. For t>=0, define

    h_B(t) = m/(1+t) - tr((B+t I)^(-1))
           = sum_i k_lambda_i(t),
    k_lambda(t) = (lambda-1)/((1+t)*(lambda+t)).

For c=min(1,lambda)>0,

    |k_lambda(t)| <= |lambda-1|/(t+c)^2.

The kernel is absolutely integrable. A direct antiderivative gives

    integral_0^T k_lambda(t) dt =
      log(lambda)+log(1+T)-log(lambda+T).

Taking T to infinity and applying the real spectral theorem,

    integral_0^infinity h_B(t) dt
       = sum_i log(lambda_i) = log det(B) = 2 log |D|.       (1)

By Smith normal form over Z and localization at p,

    length_{Z_p} coker(M tensor Z_p) = v_p(D).

Consequently the exact **arithmetic-to-real integral** is

    sum_p (log p)*length_{Z_p} coker(M tensor Z_p)
       = (1/2) integral_0^infinity h_B(t) dt.               (2)

It is crucial to use B=M^T M. Replacing it with I+B changes the determinant and generally forfeits the original cokernel index. B may have eigenvalues smaller than one; h_B can genuinely change sign.

## 2. NNS quadrature and the integral mean-value theorem

For T>0 and integer n>=1 let Delta=T/n. Choose tags xi_j in
[j*Delta,(j+1)*Delta] for j=0,...,n-1, and define

    Q_(n,T) = Delta * sum_j h_B(xi_j).

For any real target tau, put z_j=h_B(xi_j)-tau. Exactly,

    Q_(n,T) =
      Delta * (sum_j max(z_j,0) - sum_j max(-z_j,0)) + T*tau.

This is the genuine NNS UPM1-LPM1 signed reconstruction at an arbitrary
target, without separate upper bounds on the two moments. Lean:
nnsTaggedQuadrature_eq_sum and nnsTaggedQuadrature_target_independent.

For every lambda and cell, the first integral mean value theorem gives
a point c_(j,lambda) in that cell such that

    integral_(j*Delta)^((j+1)*Delta) k_lambda(t) dt
       = Delta * k_lambda(c_(j,lambda)).

For lambda>1, k_lambda is positive and decreasing. For 0<lambda<1,
it is negative and increasing. Thus k_lambda has constant sign and is
monotone. Its cell oscillation is the absolute difference of its
endpoint values. Comparing ANY numerical tag to the mean-value tag,

    |Delta*sum_j k_lambda(xi_j) -
       integral_0^T k_lambda(t) dt|
      <= Delta*sum_j |k_lambda(j*Delta)-k_lambda((j+1)*Delta)|
      = Delta*|k_lambda(0)-k_lambda(T)|
      <= Delta*|1-lambda^(-1)|.

Let V(B)=sum_i |1-lambda_i^(-1)|. Summing over eigenvalues gives

    |Q_(n,T) - integral_0^T h_B(t) dt|
       <= (T/n)*V(B).                                      (3)

The tail bound follows from the squared denominator above:

    |integral_T^infinity h_B(t) dt|
       <= sum_i |lambda_i-1|/(T+min(1,lambda_i))
       =: W_B(T).                                          (4)

Together with (1), the **finite signed quadrature certificate** is

    |Q_(n,T)-2*log|det M|| <= (T/n)*V(B)+W_B(T).             (5)

The proof retains signs in Q, bounds only the numerical error and
the integrable tail, and does not use RH or probabilistic cancellation.

## 3. A computable rational bound with no eigenvalue computations

Set L=tr(B) and

    u=min(1,det(B)/L^(m-1)) > 0.

Every eigenvalue satisfies lambda_i<=L and lambda_i>=u: the other
m-1 eigenvalues have product at most L^(m-1), while their total
product is det(B)>0. Therefore

    V(B) <= m*(1+1/u),
    W_B(T) <= (L+m)/(T+u),

and (5) has the **explicit computable** upper bound

    |Q_(n,T)-2*log|det M||
      <= (T/n)*m*(1+1/u)+(L+m)/(T+u).                       (6)

For rational T and left/right/rational tags, each sampled
h_B(t) is rational: invert the rational matrix B+t I. Thus its
UPM, LPM and signed finite quadrature may be computed exactly as
rational numbers, while (6) encloses the ordinary real integral.

## 4. Strong pathwise convergence and almost-sure convergence

For a fixed M, choose T_n=sqrt(n), Delta_n=1/sqrt(n). From (6),

    |Q_(n,sqrt(n))-2*log|det M||
      <= m*(1+1/u)/sqrt(n)
          +(L+m)/(sqrt(n)+u) -> 0.                         (7)

This holds for EVERY choice of the tags in their respective cells.

Let (Omega,F,P) be any probability space and let the tags
xi_(n,j)(omega) be random variables for which each declared
cell-membership event has probability one. There are countably many
pairs (n,j). Therefore the intersection of the cell-membership
events has probability one. On that event (7) applies pointwise,
so

    P(lim_(n->infinity) Q_(n,sqrt(n))
        = 2*log|det M|) = 1.                                (8)

This almost-sure convergence does not need independent, iid,
unbiased, Gaussian, ergodic or stationarity assumptions. The
randomness is in the NUMERICAL TAGS, not in the prime or Mobius
coefficients. Lean:
nnsIntegral_uniformError_implies_ae_convergence.

For a growing matrix family M_x, this fixed-matrix limit is
insufficient unless dimensions, heights and spectral lower bounds
are controlled *uniformly in x*. Almost-sure real convergence does
not by itself imply exact integral p-adic divisibility.

## 5. Fully signed, nonzero-index example

Take

    M=[[1,4],[0,2]],  det M=2,
    B=[[1,4],[4,20]], tr B=21, det B=4.

The rational signed resolvent is

    h_B(t)=(19t-13)/((t+1)*(t*t+21t+4)),

which changes sign at t=13/19. The exact real integral is
log 4=2 log 2. The p-adic budget is precisely log 2 from the
single length-one cokernel at p=2.

With n=10000,T=100, left endpoints:

    UPM1=1.722150447628
    LPM1=0.523372819683
    Q=1.198777627945
    real integral=1.386294361120
    actual error=0.187516733175
    certified bound from (6)=0.354562737643.

At n=1000000,T=1000, Q is approximately 1.365879807059,
error approximately 0.020414554061 and certified bound
0.0354956199. The Python regression computes each node exactly
as a Fraction and exercises left/right/midpoint/random tags.

## 6. Exact conditional realized-family Sha payment

If an integral M_x can be constructed from the actual global
cohomology/local Selmer conditions of the realized family, and for
every p it admits a simultaneous injection

    direct_sum_(1<=e<t(x)) Sha^1_(p,e)(K_x)
          -> coker(M_x tensor Z_p),

then length monotonicity, (2), and (5) give

    sum_p log(p) * sum_(1<=e<t(x)) length(Sha^1_(p,e)(K_x))
       <= log|det M_x|
       <= (Q_(n,T) + (T/n)*V(B_x)+W_(B_x)(T))/2.            (9)

Equation (9) is a genuine arithmetic-to-Sha numerical certificate
**only under the stated actual integral-presentation hypothesis**.
The MVT, a.s. convergence, and determinant formula DO NOT
construct this map. RH_Lean has not yet supplied it or proved
the uniform size/height budget needed by Alpoge's realized window.

The mathematical next task is the cohomologically faithful
integral-presentation construction, not another convergence claim.

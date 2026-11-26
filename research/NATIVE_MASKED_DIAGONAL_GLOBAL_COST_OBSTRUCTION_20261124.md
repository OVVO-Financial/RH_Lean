# Exact global-capacity obstruction for raw masked diagonal minors
2026-11-24. Continuation of NATIVE_MASKED_DETERMINANTAL_GAIN_20261124.
Status: paper proof of finite inequality and its selected-window consequence;
not a Lean-verified theorem, not the critical estimate, not a general
obstruction to native arithmetic geometry.

## 1. Exact global index and the cost of a small set of minors

Let b>=1 be an integer, x>=1, A=floor(b*x). For a finite mask I_p
of positive exponents satisfying p^i<=x, define the actual diagonal
entries d_n=prod_p p^(#{i in I_p:p^i divides n}) for n=1,...,A.
In particular d_n divides n, regardless of the mask. Put
P=prod_{n=1}^A d_n and V_I=sum_p |I_p| log p.
Let d be the gcd of all nonzero (A-b)-minors of the diagonal.

The previously proved nested valuation formula gives
v_p(d)=sum_{i in I_p}(floor(A/p^i)-b).
There is no positive-part ambiguity: floor(A/p^i)>=b since p^i<=x.
Consequently log d=log P-b V_I.

For any k>=1 nonzero original diagonal minors M_j, let B_j be the
product of the b omitted entries. Then M_j=P/B_j and B_j divides P.
Primewise valuations give the exact identity
gcd(M_1,...,M_k)=P/lcm(B_1,...,B_k).
Since B_j<=A^b and lcm(B_j)<=prod B_j, one obtains

    log gcd(M_1,...,M_k)-log d >= b*(V_I-k*log A).             (1)

The left side is also nonnegative. This includes k=1. It does not
assert that all primes have a common minimizing minor.

A further exact-count obstruction: for every selected prime p>sqrt(x),
only i=1 is possible, and obtaining the exact p-valuation of d in
the restricted gcd requires some B_j to contain b multiples of p.
For two distinct primes p,q>sqrt(x) this cannot be the same B_j:
floor(A/(p*q))<b. Thus exact extraction requires at least as many
original minors as there are selected primes >sqrt(x). Conversely
one primewise minimizing minor for each selected prime attains the
exact gcd (with a single minor if the mask is empty).
These are claims about original diagonal minors, not arbitrary
unimodular transformations or linear combinations of minors.

## 2. The actual signal mask has positive linear mass

Use the literal source in
RHLean/Analysis/AlpogeThin/NativeDyadicHostPrimePowerWeights.lean
and the thick colours in
RHLean/Analysis/AlpogeNativeSubgroupProjection.lean.
For the same selected pair q,d and fixed epsilon in (0,1/52), write
s=1/2+epsilon/2 and assume the actual PairGood 1 epsilon Y X q d.
The nonprincipal two-bit primitive twists chi_q, chi_d, chi_qd satisfy
the bounds in PairGood via nativeDyadicTwoBitCharacter_induces
in NativeDyadicThickCharacters.lean. They are nonprincipal (distinct
odd primes and the CRT produce units with a nontrivial sign).

For a natural N with [N,4N] in [Y,X], use the existing compact weight
nativeAlpogeDyadicWindowWeight N n from
RHLean/Analysis/AlpogeNativeDyadicWindow.lean:

    K(n)=0 outside (N,4N);
    K(n)=2-2N/n on (N,2N];
    K(n)=4N/n-1 on (2N,4N).

In particular 0<=K<=1. For any twist chi, define
W_chi=sum_n Lambda(n)*chi(n)*K(n).
The exact coefficient calculation in the cited dyadic-window file,
now with each coefficient multiplied by chi(n), gives
W_chi=S_chi(4N)-3*S_chi(2N)+2*S_chi(N), where S_chi is the
uncentered ramp sum. For the nonprincipal twists the affine
log-derivative term cancels, so |W_chi|<=6*(4N)^s. This uses the
same PairGood witness at all three arguments, not a new character
estimate. For the principal twist, nativePsi_div_atTop_one gives,
by partial summation against this fixed bounded piecewise smooth
weight, W_1/N -> integral_1^4 K(Nu)du = 2 log 2.
For just a positive lower bound, use K>=1/3 on (2N,3N]:
W_1 >= (psi(3N)-psi(2N))/3.

On unramified prime powers, the indicator of the native signal bits
(first=1,second=0) is (1+chi_q-chi_d-chi_qd)/4, by the native Artin
coordinates and the primitive induction identity. Even powers have
first bit zero. The omitted ramified prime powers at 2,q,d contribute
at most 12 log(4N) to the four-term identity, since K<=1, each
character modulus is <=1, and each prime's full logarithmic power
mass up to 4N is <=log(4N). Therefore the sum of Lambda(n)*K(n)
on the signal class is (N/2) log 2 + o(N), uniformly for selected
pairs in the stated windows (epsilon fixed). Its unweighted
prime-power mass V_sig(x) at x=4N satisfies

    V_sig(x) >= (log(2)/8 + o(1))*x.                          (2)

The same lower bound with a fixed smaller positive constant applies
at interior real x with floor(x/4)>=Y and x<=X by using 4*floor(x/4).
No principal RH-strength estimate is used. PNT is the existing native
unconditional theorem, not a proposed new hypothesis.

## 3. Normalize (1) on the actual full dyadic host

For each top t and lift j, fix x_t=a_t/b>=1 and A_t=floor(b*x_t).
Use the frozen width b and the full set of active odd unramified
prime powers whose actual Frobenius lies in the thick colours
E1(T2+u-t), where E1(h)=((1,0),h).
The sharp source cutoff must include these active powers p^i<=x_t.
For each signal power, exactly |T2| values of the translation u in H
admit it, independent of its dyadic coordinate. Thus the average
mask mass over u is exactly Delta*V_sig(x_t), where Delta=|T2|/|H|.
This counting identity does not assume equidistribution of dyadic
Frobenius displacements. Keep all t,j as in the actual source.

Let each restricted gcd use at most k original diagonal minors,
possibly different for every u,t,j. Denote it by d_hat_{u,t,j} and
the exact determinantal divisor by d_{u,t,j}. Their error is
nonnegative. Apply (1) and sum with the source coefficient 2,
then divide by the exact Q=T*m*b*Delta/2:

    E = (2/Q)*(1/|H|)*sum_{u,t,j} log(d_hat/d)
      >= 4*(1/T)*sum_t V_sig(x_t)
          - 4*k*max_t log A_t/Delta.                        (3)

Under the contemplated native regime x_t=x+O(1) in the interior
of one selected window, b=ceil(exp(x^epsilon)),
Delta>=x^(-epsilon), and k=O(sqrt(x)), (2) gives

    E >= c*x - O(x^(1/2+2*epsilon)) = Omega(x).

To achieve even o(x) error from this restricted-minor extraction,
(3) requires k >= c'*Delta*x/log(max_t A_t)
>= c''*x^(1-2*epsilon) eventually. This exceeds O(sqrt(x))
for epsilon<1/52. The actual geometric multiplicity m is not
asserted to be a universal bound on k; this specifically refutes
the proposal to extract the index cheaply using O(sqrt(x)) original
diagonal minors. It says nothing against an independently proved
simultaneous basis transformation, differently constructed lattice,
or a global argument that pays many constraints more efficiently.

## 4. No hidden critical estimate

The earlier rounding comparison remains valid. In the unmasked
specialization, taking every p^i<=x yields
0<=S_z(x)-log(d)/b<=psi(floor(x))/b. Hence subtracting the original
centering x log x-(1+gamma)x gives G_z(x) to exponentially small
error at the contemplated b. This is an exact scalar representation,
NOT a new upper bound. Likewise the masked representation's rounding
debt is small, but (3) is a large cost of a particular attempted
global upper bound.

The local determinantal divisor is genuine, but assigning its
centered size or choosing a synthetic Ga cannot prove the needed
capacity inequality. Do not keep treating the raw diagonal-minor
route as if it delivered the missing cancellation. An actual global
signed comparison on another integral construction (or an efficient
simultaneous transformation with its norms and rank costs proved)
would still be required. No GeoCl/anyGeometry dependency, assumed
critical bound, terminal theorem import, or new Lean scaffolding is
introduced. This work does not close RH, change the toolchain, or
claim that other native geometries are impossible.

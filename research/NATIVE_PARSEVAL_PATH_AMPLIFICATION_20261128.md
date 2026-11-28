# Native sign-and-Parseval amplification on the complete residual

Research building on #1214's primitive Euler fit at 18b975b and the
real-clock exact transfer at 12d41ef. Paper deductions and exact finite
tests; not a new conditional production interface or a terminal proof.

## Source mechanism

Alpöge's announcement, footnote 3 (https://alpo.ge/remark.pdf), uses
the quadratic path x_1 x_2 + ... + x_{k-1} x_k, not disjoint pairs.
See Zhang, https://arxiv.org/html/2611.30749v1, Lemma 2.6,
and https://hexagonmath.org/2611.00789v1. The finite-field proof uses
iterated Fourier/Plancherel and separate cohomological spectral
separation (in Zhang's exposition, weak Lefschetz injection and
concentration in one degree). It does NOT prove that the weighted
quadric count is pointwise negative for arbitrary signed functions.
The following direct integer argument tests a pointwise sign as one
sufficient substitute for that spectral separation.

## 1. O(1) transfer on the complete real clock

Use exactly the profile V and residual E of
research/NativePrimitiveDeterminantCertificate.lean and the preserved
SIGNED_MOBIUS_SPLIT_COMPENSATION_20261127.md. In particular V(y)=
A(y)+B(2y)+C(4y) with C=C_0+eta D. These are continuous, compactly
supported profiles with piecewise derivatives of bounded variation:
on the upper halves defining B and C_0 the inverted ramp U uses only
finitely many summands, and the joins and reflected endpoints agree.
V(1)=0, V is bounded and V' has bounded variation on [0,infinity)
with its extension by zero after 1. These facts follow directly from
the displayed piecewise formulas, not from prime data.

Reflection gives integral V=1, since integral A=1 and integral
B=integral C=0. The calibration gives integral V(y)log y dy=-(1+gamma):
integral A log y=-(1+log 2)+I(A), while the other contributions
are I(B)/2 and I(C)/4 by dilation and antisymmetry. Here I(f) is
the split integral in the source note.

The exact real-clock identity in statementOCGz_add_residual is

    G_z(x)+P_E(x)=sum_{n<=x} log(n) V(n/x)
                  -x log x+(1+gamma)x,
    P_E(x)=sum_{n<=x} Lambda(n) E(n/x).

A direct trapezoidal estimate strengthens the earlier square-root
transfer. For x>=2 let L=ceil x and f_x(t)=V(t/x) log t for t>0,
with the zero extension for t>=x. On [1,L] it is absolutely continuous
with a.e. derivative
    f_x'(t)=V'(t/x)log(t)/x + V(t/x)/t.
The first term has total variation at most
(log L)/x (Var(V')+||V'||_infty) and the second at most
Var(V)+||V||_infty. Hence Var(f_x') is uniformly bounded.
For any absolutely continuous f on a unit interval [j,j+1] whose
derivative is BV, the error between integral and the trapezoid is
bounded by Var(f') on that interval: integrate (t-j-1/2)f'(t),
subtract a constant derivative, and bound the remainder. Summing
over all the unit intervals gives O(1), since f_x(1)=f_x(L)=0.
Also integral_0^1 |V(t/x)log t| dt<=||V||_infty. Substitute t=xy
in the full integral to obtain

    sum_{n<=x} V(n/x) log n
       = x log x-(1+gamma)x+O(1).
    G_z(x)=-P_E(x)+O(1) uniformly on the complete real clock.

This is a paper proof of the quadrature estimate, not a claim that
the new Lean exact-transfer declaration has already passed CI.
No rounded anchor, exclusion of prime powers, or sign approximation
is necessary for this version.

## 2. Complete native signed tensor

Let N=floor x and choose a prime q with N<q<=2N. Define
t(n)=-Lambda(n)E(n/x) on 1<=n<=N and zero on the rest of F_q.
Write M=sum t=-P_E(x), B=||t||_infty=O_E(log x).
For fixed odd k>=5 define the actual signed coupled population

    P(u)=sum_{i=1}^{k-1} u_i u_{i+1} mod q,
    N_k(a)=sum_{P(u)=a} prod_i t(u_i).

Include every complementary/unserved label. For fixed epsilon and
fixed k the q^k tuple addresses fit the exponential slot capacity
eventually, but this does NOT show that they are original star
directions. This is a direct arithmetic attack; do not inflate
the original star rank or Q_* by counting the extra tuple labels.

Fourier orthogonality gives q N_k(a)=M^k+R(a), with
R(a)=sum_{h!=0} e_q(-ha) S_h, S_h the path character sum.
For arbitrary weights t_i, let F_h f(v)=sum_u e_q(huv)f(u).
For h!=0, F_h^* F_h=q I. Applying F_h, multiplication by t_i,
and F_h successively along the path, and pairing with the last t_i,

 |S_h| <= q^((k-1)/2) ||t_1||_2 ||t_k||_2 prod_{2<=i<k} ||t_i||_infty
       <= q^((k+1)/2) prod_i ||t_i||_infty.

Hence |R(a)|<=q^((k+3)/2) B^k. If an independent arithmetic
argument supplies N_k(a)<=0 for some a, odd k gives

    M <= B q^(1/2+3/(2k)).

A uniform upper bound q N_k(a)<=C_k q^((k+3)/2)(log q)^k also
suffices. Fixed odd k sufficiently large in terms of epsilon
absorbs the exponent and logarithmic losses. The bound must hold
for every target on cofinal complete real windows. Even k would
impose an unnecessarily stronger two-sided condition.

The same path attack can use the complete primitive trace vector
from PRIMITIVE_EULER_ADMISSIONS_20261127.md:
s(n)=-E(n/x) log F_n(r)+R_E(x)/N for 1<=n<=N, with log term zero
for n=1. Its sum is -P_E(x)+O_E(sqrt x log x). The cyclotomic product
bounds |log F_n(r)|<=tau(n)log(c+1). Since |f(u)|<=log(1+u), the
reference formula gives |R_E(x)|/N=O_E(log^2 x) by splitting its
absolutely convergent sum at ceil tau (tau=x log(1+1/c)).
Thus ||s||_infty=O_delta(x^delta log^2 x) for every delta>0.
This version would also give the desired epsilon-scale estimate
if its signed fiber inequality is established. The previous local
repairs preserve the total sum but do not automatically preserve
this pointwise norm; do not substitute repaired logs without proof.

## 3. Independently evaluated coupled-population probability

Parseval across the fiber label a gives
(1/q) sum_a |R(a)|^2 = sum_{h!=0}|S_h|^2
 <= (q-1)q^(k+1) B^(2k).

If N_k(a)<=0 on a fraction theta>0 of residues, then either M<=0
already or theta M^(2k)<=(q-1)q^(k+1)B^(2k). Therefore

    M <= theta^(-1/(2k)) B q^(1/2+1/k).

If theta>=q^(-A) with fixed A, the exponent loss (1+A/2)/k
is absorbable by choosing fixed odd k. This is the precise place
where an arithmetic good-event probability bound could help.

Sample each coordinate with probability |t(n)|/Z, Z=sum |t|.
Retain the product of its original signs. This defines independent
sampling of tuple coordinates, NOT an assumption of independence
of occurrences of rational primes. N_k(a)/Z^k is the difference
of the joint probabilities of P=a with even or odd negative parity.
By the earlier residual analysis and ordinary PNT, both signed
masses Z_+, Z_- are asymptotic to kappa x, kappa>0.
Apply the path estimate to |t| to get uniformly in a,

    Pr(P(u)=a)=(1/q)(1+O_k(q^(-(k-3)/2) log^k q)).

This is an independent probability law on the actual coupled
population, and a bound on the probability of a set of good fibers
transfers to its uniform fraction. It gives no automatic bound
on conditional sign parity.

## 4. Direct tests of automatic sign and local Euler exchanges

Every fixed sign pattern has strictly positive mass in EVERY fiber
eventually: use t_i=t_+ or t_- in the mixed path estimate. Its zero
mode is a product of k masses each comparable to x. The remainder
O_k(q^((k+3)/2)log^k q) is o(q^k) for k>=5. Thus one cannot force
the sign by excluding all positive-parity tuples from a fiber.
One must compare their weights against the negative-parity tuples.

Even exact independent CRT local Möbius signs do not imply the
required inequality. On a full period Q=prod_{p in S} p^2 define
f_p=1 on p-units, -1 on p-multiples that are not p^2-multiples,
and 0 on p^2-multiples. Put f=prod f_p. Its coordinates under the
uniform CRT law are independent, and its exact signed total is
    M_Q=prod_{p in S}(p-1)^2.
This is a finite-prime Möbius surrogate, not the full Möbius
function. For S growing over initial primes, M_Q=Q^(1-o(1)):
for each delta>0, (p-1)^2>=p^(2-2delta) for sufficiently large p,
and finitely many smaller primes only cost a constant.
Embed that period into any prime q between Q and 2Q, padding zero.
For any fixed odd k>=5, M_Q^k>q^((k+3)/2) eventually, so all
N_k(a)>0 by the proved remainder bound. Already S={2,3,5,7},
Q=44100, M_Q=2304 and k=9 give M_Q^k>(2Q)^((k+3)/2).
Thus generic NNS positivity and exact local Euler probabilities
cannot provide the sign. This does not rule out global arithmetic
size-dependent correlations of the actual residual.

A direct exact integer edge-preserving swap of the prime-supported
part is also insufficient. If two tuples of prime labels satisfy
u_i u_{i+1}=v_i v_{i+1} on every edge, any nontrivial swap must
exchange the two factors of the first edge. Propagating forces
the entire tuple to alternate between the same two distinct primes.
Otherwise all coordinates are equal to the original ones.
The absolute weighted mass of such alternating tuples is at most
B^(k-2)(sum_p |t(p)|)^2; the total prime-supported mass is comparable
to x^k by PNT. Their mass fraction is O_k((log x/x)^(k-2)).
This is an obstruction ONLY to exact integer edge equality.
Modular collisions of sums of edges are not ruled out. Prime
powers are still present in the full signed tensor.

## 5. Remaining mathematical target

Establish a signed magnitude comparison on a nonnegligible
family of the coupled fibers, or find a genuine spectral
separation that makes a pointwise sign unnecessary. The latter
would follow the finite-field source more faithfully. Tensoring
the existing fixed cyclic shifts alone cannot amplify a zeta zero:
their eigenvalues are roots of unity, and the zeta-zero poles
arise from varying the population with scale. No spectral
injection tying these poles to a single controlled sign has
been established. None of the local Euler fit results imply it.

The complete-window target and terminal acceptance gate are
unchanged. Do not convert the sign criterion into an assumed
production supplier. The direct Fourier estimate is proved on
paper; its necessary independent arithmetic input remains open.

## 6. Exact finite regression

Run node scripts/research/check_native_parseval_path.js.
The dynamic program keeps signed mass intervals indexed by last
coordinate and accumulated path residue. It checks exact mass
conservation and both Parseval bounds for integer signed vectors.
For actual residuals at finite integer anchors it uses exact
rational evaluations and the eta bracket [0.04057,0.04149] reported
in the preserved source note, which is not independently re-enclosed
here. Logarithms are bounded by rational atanh sums and their
geometric tails. All weights are outward-enclosed at scale 10^8;
subsequent interval products and sums are exact BigInts. An upper
endpoint below zero certifies that finite sign for all eta in the
bracket. An interval containing zero is inconclusive.
These are finite checks, not a proof of a uniform window theorem.
No new Lean declaration is claimed kernel-verified in this commit.

Executed regression results:

```json
{
  "counts": {
    "pointwise": 2448,
    "l2": 252,
    "mass": 252,
    "intervalProducts": 2025
  },
  "actual": [
    {
      "m": 64,
      "q": 67,
      "k": 5,
      "support": 4,
      "negative": 24,
      "positive": 25,
      "undetermined": 18,
      "firstNegative": 1
    },
    {
      "m": 64,
      "q": 67,
      "k": 7,
      "support": 4,
      "negative": 24,
      "positive": 21,
      "undetermined": 22,
      "firstNegative": 1
    },
    {
      "m": 128,
      "q": 131,
      "k": 5,
      "support": 8,
      "negative": 56,
      "positive": 53,
      "undetermined": 22,
      "firstNegative": 0
    },
    {
      "m": 128,
      "q": 131,
      "k": 7,
      "support": 8,
      "negative": 35,
      "positive": 34,
      "undetermined": 62,
      "firstNegative": 3
    },
    {
      "m": 256,
      "q": 257,
      "k": 5,
      "support": 15,
      "negative": 86,
      "positive": 79,
      "undetermined": 92,
      "firstNegative": 4
    },
    {
      "m": 256,
      "q": 257,
      "k": 7,
      "support": 15,
      "negative": 11,
      "positive": 9,
      "undetermined": 237,
      "firstNegative": 3
    },
    {
      "m": 512,
      "q": 521,
      "k": 5,
      "support": 27,
      "negative": 123,
      "positive": 121,
      "undetermined": 277,
      "firstNegative": 6
    },
    {
      "m": 512,
      "q": 521,
      "k": 7,
      "support": 27,
      "negative": 0,
      "positive": 0,
      "undetermined": 521,
      "firstNegative": -1
    }
  ],
  "eulerCountermodel": {
    "Q": "44100",
    "M": "2304",
    "k": 9,
    "dominates": true
  }
}
```

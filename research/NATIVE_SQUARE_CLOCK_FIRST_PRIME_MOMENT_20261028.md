# RH_Lean-native first prime-cofactor mean-square power saving

**28 October 2026. Status: PAPER PROOF of a genuine all-H native-source SUBSECTOR
bound; finite exact rational regression; Lean kernel checks on the individual
quadratic-shift and CRT-orbit lemmas in this PR. No full Mertens power saving.**

## 1. Precise original physical source

Use only research/EULER_FRACTIONAL_COUPLED_20261027.lean, whose ORIGINAL
self-dual signed off-diagonal is

    eulerFractionOffQ(R) =
      sum_{1<=b<R} mu(b) sum_{1<=a<b} mu(a)
             (((R^2-1) mod (a*b))/(a*b)).

For a=1 and b=p prime, the ORIGINAL coefficient is mu(1)mu(p)=-1.
After multiplication by 2 for the symmetric off-diagonal, the TRUE first
prime row is

    U_Q(R) = -2 sum_{p<=Q, p prime} f_p(R),
    f_p(R) = ((R^2-1) mod p)/p.

No change of sign, prime cutoff, norm label or square-wall endpoint.
For every R in [H,2H) and Q^3<=H with Q>=2, all p<=Q are within b<R,
so this is an actual subsource, not a made-up row.

Define its principal residue mean explicitly, not by assuming it zero:

    m_p = (1/p) sum_{0<=r<p} f_p(r), 
    U_Q^principal = -2 sum_{p<=Q} m_p.

The residual NONPRINCIPAL arithmetic signal is

    F_Q(R) = U_Q(R) - U_Q^principal
           = -2 sum_{p<=Q}(f_p(R)-m_p).

The mean is generally NONZERO. In particular RH_Lean's genuine #919
period-36 quotient kernel has mean zero in the quotient variable but NOT
after composition with the square clock. Do not erase this principal bill.

## 2. The unconditional all-H bound

**Theorem (native first-prime-row dyadic gain).** For all natural H,Q>=2
with Q^3<=H,

    sum_{H<=R<2H} F_Q(R)^2
       <= 4*(H*Q + Q^4)
       <= 8*H*Q.                                      (A)

Proof, completely elementary and independent of the Mertens exponent:

(1) 0<=f_p(r)<1 and 0<=m_p<1, so |f_p(r)-m_p|<=1.
Every diagonal p contributes at most H to the unscaled energy.

(2) For distinct primes p,q, the CRT gives a bijection
Z/(pq) ~= Z/p x Z/q. Because the centered functions depend only on
their own residue coordinate, their COMPLETE product covariance vanishes:

    sum_{0<=R<pq} (f_p(R)-m_p)(f_q(R)-m_q)
       = (sum_{r mod p}(f_p(r)-m_p))
         (sum_{s mod q}(f_q(s)-m_q)) = 0.              (B)

This is a deterministic additive CRT fact, not a probabilistic independence
assumption. Both functions are pq-periodic, so any interval of H consecutive
roots splits into exact complete pq-periods plus fewer than pq sites.
Each remaining product has magnitude <=1. Thus, for any H and p!=q,

    |sum_{H<=R<2H}
       (f_p(R)-m_p)(f_q(R)-m_q)| <= pq.                 (C)

(3) Expand the square BEFORE absolute values. Diagonals cost H*pi(Q)<=HQ.
Off-diagonals cost <=sum_{p!=q<=Q}pq <=(sum_{p<=Q}p)^2 <=Q^4.
The physical symmetric coefficient is -2, so energy gets the factor 4.
This proves (A). Q^3<=H implies Q^4<=HQ.

The original naive per-root bound |F_Q(R)|<=2*pi(Q)<=2Q
would only give E<=4HQ^2. The native source instead saves one full
factor Q in the SQUARED ENERGY, without importing original OAI 7/8.

## 3. Evidence and falsifiers

Exact rational Python test:
    python3 scripts/native_squareclock_first_prime_moment_regression.py

Examples at H=4096,Q=16 give E=8916.72 vs the bound 8HQ=524288.
At H=65536,Q=40 give E=283680.14 vs 8HQ=20971520.
The script retains actual mu(1)*mu(p)=-1 and does not simulate signs.

A negative control is essential: if gcd(d,e)>1, complete-period
covariance may be NONZERO; examples d=15,e=21 and d=35,e=55.
The COPRIME qualification cannot be dropped. In the true off-diagonal
eulerFractionOffQ all d=a*b appear, many of which share prime factors.

## 4. Source-specific limitation and exact next job

(A) is a genuine unconditional cancellation theorem, but it is ONLY
the a=1,b=p low-prime component of the existing Euler fractional Gram.
Its pointwise amplitude is already <=2Q=O(H^(1/3)), much less than
the H^(7/4) global Mertens scale. Therefore THIS theorem ALONE
CANNOT improve 7/8 and must not be called a global gain.

The next independent arithmetic lemma must extend CRT root covariance to:
- a>=2, genuine mu(a)mu(b), all a,b<R, INCLUDING shared gcd;
- moduli d=a*b as large as H^2, far beyond a complete period on an H-root
  sample, using quantitative incomplete quadratic-phase Weyl bounds;
- the principal nonzero residue means, and mixed terms between the paid
  low coprime sector and the large-modulus source;
- the ORIGINAL EULER Q = X*S^2 - diagonal - 2*offdiag reassembly.

This is precisely where an additive, non-Beurling signed NNS Co-Div
estimate would have to enter. No new hypothesis equivalent to
M(X)=O(X^(7/8-delta)) has been slipped into the lemma.

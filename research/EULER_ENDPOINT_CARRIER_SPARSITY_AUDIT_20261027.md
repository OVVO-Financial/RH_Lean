# Exact Euler endpoint-carrier sparsity and q-dependent right-carry

2026-10-27. Research branch stacked on the green #1038, itself stacked
on #1037 and #1036. Zero new axioms, no sorry admitted. The dedicated
warning-fatal and axiom CI decides the certification status of the Lean
lemmas; finite numerical checks below are independent.

## 1. Sparse active quotient carriers are a small historical integer prefix

Let N=R-1, L=R+1, X=NL. Let Q be **any** integer with 1<=Q<=N
and Q(Q+1)>=N. For each q in [Q,N], I_q=(floor N/(q+1), floor N/q]
is either empty or a singleton. The union of the nonempty buckets is
EXACTLY [1, floor N/Q], and each small a occurs ONCE at q=floor N/a.

Thus for any original historical arithmetic weight f(a),

    sum_(q=Q)^N sum_(a in I_q) f(a)
      = sum_(a=1)^(floor N/Q) f(a).

The original endpoint carrier with punched divisor rows, namely

    sum_(q=Q)^N [ sum_(a in I_q, a not|N) mu(a) ] * T_R(r_q,b),

collapses EXACTLY to

    sum_(a=1)^(floor N/Q), a not|N mu(a)*T_R(a,b).

No generic operator weights enter; T_R is the actual rank-one-subtracted
Euler floor kernel of #1036. This collapse keeps all original Möbius
parities and the divisor-row hole.

*Important correction*: the bound floor(N/Q)<=floor(sqrt N) is NOT valid
for the minimal Q with Q(Q+1)>=N. For N=30, Q=5 and floor N/Q=6.
Use the exact floor(N/Q) (always O(sqrt N) for that Q). The total number
of active q is at most (Q-1)+floor(N/Q)=O(sqrt N), and no counting
bound by itself supplies cancellation.

At N=999, Q=32: exactly 31 high-q buckets are nonempty, not 968.
At N=30, Q=5: exactly 6 high-q buckets are nonempty.

## 2. Right endpoint carry is q-dependent, not generic N/b

For each genuine nonempty I_q, r=floor N/q belongs to I_q, and
floor N/r=q. Euclidean division therefore gives the SAME remainder

    t = N-q*r = N mod q = N mod r,    0<=t<q.

Let rho=(L*q) mod b, 0<=rho<b. The exact source-level right carry is

    c_(q,b)(r) = floor((r*rho+L*t)/(r*b))

and hence

    0<=c_(q,b)(r)<=1+floor(L*(q-1)/(r*b)).

The q=1 case has t=0; because 0<=rho<b its endpoint carry is ZERO
for every b. The ORIGINAL endpoint kernel then equals
T_R(N,b)=-{X/(N*b)}. This is not a general off-diagonal saving.

A complementary exact bound, not yet an extra named Lean theorem, is

   -1 < T_R(r,b) <= L*(q-1)/(r*b),

because T_R(r,b)=floor(X/(r*b))-L*q/b and
X/(r*b)=L*q/b+L*t/(r*b).

The bound is strong for q<<sqrt N and b large. It does not
control the signed sum across b or the complementary interior jumps.

## 3. Contiguous window coupling (no automatic mixed moment)

Define A_q(b)=floor(Y_b/r_q). For consecutive well-defined endpoints:

    T_R(r_(q+1),b)-T_R(r_q,b)
       = A_(q+1)(b)-A_q(b)-L/b.

The #1038 strict-jump m-interval for bucket q is
(A_q(b),A_(q+1)(b)], with a zero-valued extension when ell_q>0.
Thus the increment of the endpoint kernel and the full interval
length are EXACTLY coupled. Summation by parts in q can move the
baseline M(r_(q+1)) terms into endpoint carriers, but that is an
identity, not by itself a gain. Any claimed bound needs a source-faithful
signed estimate on the combined endpoint/interior interaction.

## 4. Numerical integer/rational audit

Direct original-Mobius checks at N=12,30,56,999 verified the
high-q tail collapse with the original punched divisor condition
and rank-one floor weights. The exact q-dependent carry bound was
checked for every q,b on roots R=2,3,5,10,31,100,317.

## 5. Open theorem after this reduction

The exact signed root residual is unchanged. To activate the
historical-energy amplification route we still need a uniform
source-faithful estimate on the COMPLETE interior+endpoint mixture,
for example an R^(1+epsilon)*K_R^(1-eta/2) bound with fixed eta>0.
Sparse support and a strong endpoint pointwise bound are insufficient
without the missing signed correlation.

The finite-C and RH theorems are conditional consumers, not proved
unconditionally by this PR.

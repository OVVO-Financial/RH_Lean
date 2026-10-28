# Fully coupled Euler head/interior Abel identity, and rigorous two-sided historical limits

PR #1041, stacked on #1040 and #1036-#1039. Original integer Möbius signs only. The Lean source here aims to compile the exact finite q-Abel identity. A quantitative power saving is **NOT** claimed.

## 1. Complete signed head identity with no dropped terminal bucket

Fix N=R-1, L=R+1, X=N L, 1<=Q<=N, 1<=b<=N and Y_b=floor(X/b).
Let r_q=floor(N/q), A_q(b)=floor(Y_b/r_q),
E_q(b)=A_q(b)-L*q/b. Importantly E_Q is defined by its indexed q, even
when I_Q is empty and floor(N/r_Q) differs from Q.

Define Delta M_q^o=M(r_q)-M(r_(q+1))-delta_q, where
delta_q = 1_(q|N)*mu(N/q).

For 1<=q<Q, q(q+1)<N guarantees a genuine nonempty historical bucket.
Let V_q(b)=sum_(m in (A_q,A_(q+1)]) M(floor(Y_b/m))
and W_q=A_(q+1)-A_q. (These are original historical M values.)

The entire q-head source is EXACTLY

  Head(b) =
     sum_(q=1)^(Q-1) [
        E_q (M(r_q)-M(r_(q+1))-delta_q)
        + V_q - W_q*M(r_(q+1)) ].

Since E_(q+1)-E_q=W_q-L/b, signed q-Abel gives EXACTLY

  Head(b) = E_1*M(N) - E_Q*M(r_Q)
           + sum_(q=1)^(Q-1) [ V_q - (L/b)*M(r_(q+1)) - E_q*delta_q ].

THIS removes the integer quotient-window length W_q from the baseline
but retains the smooth drift L/b times historical values. It does not
declare the drift small or independent.

Original global inversion (pre-#1040, compiled) gives

  sum_(q=1)^(Q-1) M(r_(q+1))
    = 1-M(N)-sum_(q=Q+1)^N M(r_q).

Rewriting the smooth drift in the RHS against this complementary tail
is exact, preserves all original original signs, and does not confer an
extra power saving.

The consecutive windows (A_q,A_(q+1)] concatenate to (A_1,A_Q] when
b>0 and q+1<=N, including an empty terminal quotient bucket.

## 2. Two-sided historical envelope: genuine gain and its range

Let B=N-H<R and Y be an arbitrary positive integer.
Define the literal signed fractional Möbius sum

   Phi_Y(B)=sum_(b=1)^B mu(b)*{Y/b}.

For 1<=U<=B, separate b<=U trivially, and apply summation by parts
against M(b) for b>U. Under |M(y)-1|<=sqrt(K_R(y+1)) for y<R,
the continuous fractional variation and the negative integer jumps
show (absolute constant C)

   |Phi_Y(B)| <= C*(U+sqrt(K_R*B)+Y*sqrt(K_R)/sqrt(U)).

The intermediate cutoff U≈(Y sqrt(K_R))^(2/3) produces a sublinear
historical exponent K_R^(1/3), when U<=B. If U>B use the trivial |Phi|<=B.

With Y=L*q and 1<=q<O(sqrt(R)), U≈R^(2/3)q^(2/3)K_R^(1/3).
At q≈sqrt(R) the cutoff saturates at R, so there is **NO uniform
saving** across all q. This is a mathematical paper estimate, not a
Lean theorem in this PR.

## 3. Factored smooth drift does save some R, but not enough

The historical reciprocal bound from the earlier paper audit states

   |S_N| <= 20 (K_R/N)^(1/3),  S_N=sum_(b<=N) mu(b)/b.

For B=N-H with H=floor(sqrt R), the exact last H terms cost
L*sum_(b=B+1)^N 1/b=O(H); hence

   |L*S_B|=O(R^(2/3)*K_R^(1/3)+R^(1/2)).

Also, for Q≈sqrt R,

   |sum_(q=1)^(Q-1) M(r_(q+1))|
       <= O(R^(3/4)*K_R^(1/2)).

Thus the factored smooth drift is

   O(R^(17/12)*K_R^(5/6)+R^(5/4)*K_R^(1/2)),

not the desired R^(1+epsilon)*K_R^(1-eta/2).
These two historical estimates are paper-level until independently
compiled as bound statements. Applying the inversion head/tail identity
is important to keep the final cancellation intact.

## 4. A genuine top-hyperbola hole in the double-envelope route

For m=1, Y=floor(X/m)=R^2-1.
To make M(floor(Y/a)) historical, one needs a>Y/R≈R.
No a<R satisfies this. Hence the proposed two-sided historical
Dirichlet hyperbola estimate excludes the whole top m=1 band.
This is exactly the part where a nonhistorical large-prime/cross-owner
compensation (or a genuine signed bilinear dispersion bound) is still
necessary.

Original source fidelity additionally requires retaining:
- The divisor puncture delta_q, even if an equivalent row is unpunctured
- Actual q-dependent endpoint E_q and its possible empty terminal Q
- ALL q,b signed phases, no absolute values until after coupling
- The H full b-row payment and original small-a tail
- The full post-root M(X) mode when Fubini is reversed

## 5. What would actually establish fixed eta

A uniform independent signed estimate on the complete original
coupled interior+endpoint correlation after recoupling the full drift
and the high-q original small-a complement:

  |C_R| <= C_(eta,eps) R^(1+eps) K_R^(1-eta/2)

for some FIXED eta>0, every eps>0 and all sufficiently large R.
Such a theorem, with full historical-prefix amplification, would be
RH-scale strength and cannot be inferred merely by double Abel,
Dirichlet hyperbola, orthogonality of a complete phase family, or
the identity mu*1=delta.

No such estimate is proved by this PR.

## 6. Primary Lean source

  research/EULER_COUPLED_HEAD_ABELED_20261027.lean

The theorem is eulerCoupled_head_interior_abel. Its no-drift variant
uses the already proved eulerAbelSmoothDriftQ_eq_compensated. Warning-
fatal Lean 4.34.1 CI plus standard-axiom audit is the certification gate.

## 7. Rigorous falsifier for a *purely two-sided envelope* argument

This is a counterexample to using only small partial sums in both
coordinates, NOT a counterexample to the original Möbius theorem.

Let a(n)=1 for n odd and -1 for n even. This a(n) is multiplicative
on coprime arguments, satisfies |a(n)|=1, and its genuine prefix
A(t)=sum_(n<=t)a(n) belongs to {0,1} at every t. The analogue of
the historical K_R envelope is therefore bounded by 1, uniformly.

But sum_(n<=N) a(n)/n = log(2)+O(1/N). Moreover for any real Y>=1
the signed fractional sum obeys

    |sum_(b<=B) a(b)*{Y/b}| = O(sqrt(Y)+1).

Proof: split b at ceil(sqrt Y). The initial prefix has at most sqrt Y
terms, each of size <1. For the tail, A(t) is uniformly bounded and
the total variation of {Y/b} on b>=sqrt Y is bounded by O(Y/sqrt Y):
the smooth reciprocal variation telescopes, and the floor jump
variation is a monotone quotient count.

Consequently at X=R²-1, N=R-1,

    sum_(a,b<=N) a(a)a(b)*{X/(a*b)}
        = O(sum_(a<=N) sqrt(X/a)) = O(R^(3/2)).

Therefore the complete bilinear floor sum satisfies

    sum_(a,b<=N) a(a)a(b)*floor(X/(ab))
      = (log 2)^2 * R² + O(R^(3/2)).

So even multiplicativity, bounded coefficients, and
uniformly bounded historical partial sums in BOTH coordinates
do NOT force O(R^(1+epsilon)) or any fixed-eta historical feedback
without an additional genuine Mobius-specific restriction.

What the original Mobius has that this countermodel does not:
the exact inversion identity
sum_(d<=Z) mu(d)*floor(Z/d)=1 for every Z>=1, which creates the
precise continuous-vs-fractional cancellation. This is why a valid
next estimate must keep the original Mobius inverse-divisor and
its matched endpoint/carry weights. A generic two-sided Abel
estimate cannot replace that interaction.

No claim about a(n)=(-1)^(n+1) is an RH_Lean theorem about mu.

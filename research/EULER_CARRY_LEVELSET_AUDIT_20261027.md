# Euler quotient-carry staircase and historical Mertens level sets

**2026-10-27, PR #1037.** Stacked on #1036. The proof objects in
`research/EULER_CARRY_LEVELSET_MERTENS_20261027.lean` are subject to
warning-fatal CI. The mathematical identities and inequalities below have
distinct status from their eventual Lean certificates. This note **does not**
claim finite C, fixed eta, or RH.

## 1. Exact arithmetic without a missing corner

Write N=R-1, L=R+1, X=NL=R²-1, R>=2. For q>=1, b>=1, let

    l_q = floor(N/(q+1))
    u_q = floor(N/q)
    I_q = {a: l_q < a <= u_q}
    Y_b = floor(X/b)
    m_qb = floor(L*q/b)
    rho_qb = (L*q) mod b.

For every a in I_q, floor(N/a)=q. Define the complete genuine
integer carry

    c_qb(a)=floor(Y_b/a)-m_qb
           =floor([a*rho_qb+L*(N mod a)]/(a*b)).

Then (on the original signed mu coefficients) the residual kernel of #1036
is T_R(a,b)=c_qb(a)-rho_qb/b, with both pieces kept together.

### Divisor rows cost ZERO inside the carry

If a|N, then N mod a=0. Since rho_qb<b, c_qb(a)=floor(rho_qb/b)=0.
Therefore the carry sum can be unpunctured:

    sum_(a in I_q, a not|N) mu(a)*c_qb(a)
      =sum_(a in I_q) mu(a)*c_qb(a).

Only the residue multiplier still has its punched bucket increment

    DeltaM_q^o = M(u_q)-M(l_q)
                 - 1_(q|N)*mu(N/q).

There is no missing endpoint: a=N/q belongs to I_q iff q|N.

## 2. Exact monotone level sets and Mertens collapse

As a increases, floor(Y_b/a) is non-increasing. Thus c_qb(a) is a
non-increasing step function, **not strictly decreasing**.

For any k>=1,

    c_qb(a)>=k
      <=> a<= floor(Y_b/(m_qb+k)) =: v_qbk.

Let a0=l_q+1 and DEFINE K_qb=c_qb(a0) when I_q is nonempty, or K_qb=0 when I_q is empty. Then

    c_qb(a)=sum_(k=1)^K_qb 1_(a<=v_qbk)

for every a in I_q. For 1<=k<=K_qb, the cutoff satisfies

    l_q < v_qbk <= u_q <= N.

This last fact uses b*(m_qb+k)>L*q, hence
v_qbk <X/(L*q)=N/q, together with the fact that c_qb(a0)>=k.
Therefore finite Fubini and historical Mertens telescoping give EXACTLY

    sum_(a in I_q) mu(a)c_qb(a)
       =sum_(k=1)^K_qb [M(v_qbk)-M(l_q)].

Every right-side M argument is strictly historical, <=N.

### Sharp bound on the number of jumps

The exact remainder numerator satisfies
  rho_qb<=b-1,   t_a=N mod a<=a-1.
Since a<=N and L=N+2,

    L*t_a <= L*(a-1) <= (N+1)*a,

and

    a*rho_qb + L*t_a <= a*(N+b).

Dividing by positive a*b and taking integer quotients yields

    0<=c_qb(a)<= floor(N/b)+1
    0<=K_qb<= floor(N/b)+1.

Consequently for b>N/2 every carry belongs to {0,1,2}.

This is a *level-set complexity reduction*, not a bound on the signed
sum over q and b: jump thresholds retain arithmetic correlations.

## 3. Exact form of the unpaid interior

For the original upper-strip width H=floor(sqrt(R)), let
b range from 1 to N-H. Then

    C_R =
      sum_(b=1)^(N-H) mu(b) sum_(q=1)^N [
         sum_(k=1)^K_qb (M(v_qbk)-M(l_q))
           - rho_qb/b *
               (M(u_q)-M(l_q)-1_(q|N)*mu(N/q)) ].

For empty buckets, the level sum is zero. This display is the exact
historical Mertens-functional form, with no post-root M terms, and all
original residue/carry signs, quotient windows, divisor corrections, and
outer mu(b) factors preserved.

**OPEN:** An independent bound on the complete signed q,b sum, e.g.
C_(eta,eps) R^(1+eps) K_R^(1-eta/2) for any fixed 0<eta<1,
is necessary to activate the subcritical amplification. Merely writing
C_R as the above historical sum does not prove such a bound.

## 4. Widening the already-paid upper rows

The #1036 full-row bound holds for b=N-j and 0<=j<=floor(N/2):

    |G_R(N-j)|<=3(j+2).

Consequently any integer H with 1<=H<=floor(N/2)+1 has

    |sum_(b=N-H+1)^N mu(b)G_R(b)|
       <=(3/2)H(H+3).

For finite-C budget R*sqrt(K_R), choose
H=min(floor(N/2)+1, floor(sqrt(R)*K_R^(1/4))) subject to H>=1.
Then H(H+3)=O(R sqrt(K_R)). No additional signed cancellation
is required. For a nonlinear budget R*K_R^(1-eta/2), replace
K_R^(1/4) by K_R^(1/2-eta/4).

K_R is bounded above by O(R) from |mu(n)|<=1 and is at least 1 by y=0.
No new RH exponent follows just from removing more boundary rows.

## 5. The dual top COLUMN must retain its linear term

For a in I_1 with a<N, set Z_a=floor(X/a). Since
floor(N/a)=1, full Möbius inversion on the b-axis gives exactly

    H_R(a) = sum_(b=1)^N mu(b) T_R(a,b)
           =1-L*S_N-
                sum_(n=N+1)^Z_a mu(n)*floor(Z_a/n).

As Z_a<2R, the tail floor equals one:

    H_R(a)=1-L*S_N-[M(Z_a)-M(N)].

For a=N-i, 1<=i<N/2, the same elementary upper-shell count gives

    |H_R(N-i)| <= |L*S_N| +3(i+2).

The historical reciprocal estimate from the earlier paper audit gives
|L*S_N|=O(R^(2/3)*K_R^(1/3)), hence summing H top columns trivially costs

    O(H R^(2/3) K_R^(1/3)+H²).

For H=floor(sqrt R), this is
O(R^(7/6)K_R^(1/3)+R), **not** necessarily O(R sqrt(K_R))
when K_R is small. An O(R^(2/3)K_R^(5/6)) bound for the complete
top-column sum **cannot** be inferred just by saying 'summation
by parts': it would require a separate signed short-interval estimate.

To guarantee finite-C payment without additional cancellation,
choose the narrower width

    H_col <= min(R^(1/3) K_R^(1/6),
                 R^(1/2)K_R^(1/4),
                 N/2),

with numerical constants chosen conservatively. The divisor
intersection must again be subtracted to avoid double counting.
A wider top-column payment remains a genuine quantitative target.

## 6. Structural scope

The quotient buckets are original source coordinates, not the
physical first-separating owner indices from CORR-4. The exact
Mertens-level representation does not automatically acquire the
218/225 reciprocal child contraction; an occurrence-preserving
intertwiner must be proved with the same full signed q,b weighting.

**Accept only warning-fatal Lean 4.34.1, no sorryAx or new axioms.**

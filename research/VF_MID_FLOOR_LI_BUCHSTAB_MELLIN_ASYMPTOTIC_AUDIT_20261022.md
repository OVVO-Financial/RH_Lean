# Floor-Li/Buchstab sign cancellation: exact source and asymptotic audit

Date: 2026-10-22. The finite normal form is a new Lean target; the
asymptotic below is a mathematical argument, **NOT a Lean-certified
asymptotic theorem**.

## Exact split

For x >=4, y=floor(sqrt x), W_y=prod_{p<=y} p, let K_y(x)
be the signed sum of y-smooth squarefree integers <=x. Any n<=x with
largest prime q>y has exactly one such prime factor, n=q*k with
k<=x/q<=y; hence mu(qk)=-mu(k). Thus:

 M(x)=K_y(x)-sum_{y<q<=x, q prime} M(floor(x/q)).

Let L(t)=floor(Li_2(t)), B(t)=pi(t)-L(t), and
xi(q)=1_{q prime}-(L(q)-L(q-1)). Then exactly:

 S_L(x)=sum_{k<=y}mu(k)[L(floor(x/k))-L(y)]
       =sum_{q=y+1}^x (L(q)-L(q-1))*M(floor(x/q)).
 G(x)=-sum_{q=y+1}^x xi(q)*M(floor(x/q)).
 F(x)=K_y(x)-S_L(x).
 M(x)=F(x)+G(x).

The prime-cofactor sum is K_y-M(x), **not** pi(x)-pi(y)-1.
The latter is only the k=1 cofactor fiber (up to the unit accounting).
F+G=M is algebraically exact and does not by itself supply a rate.

The revised source transport extends the hypothesis to sqrt(x)<=y.
When y=floor(sqrt x), the inequality x<(y+1)^2 gives
k=floor(x/q)<=y for any prime q>y. Hence there is exactly one
possible high prime factor and no additional boundary term.
All previously exported strict-root theorem interfaces are retained.

## Rigorous Mellin argument (paper proof; not yet in Lean)

Fix x=R^2 and H=log x. Let beta<1 and assume the existing
certified bound M(t)=O(t^beta), e.g. beta=7/8+epsilon<1.
Write S_cont(x)=sum_{k<=R}mu(k)[Li_2(x/k)-Li_2(R)].

Changing integration order, then substituting t=x/u, yields EXACTLY

 S_cont(x) = x * integral_{1}^{R}
                M(floor t) / [t^2*(H-log t)] dt.

For Re(s)>beta, the integral
 J(s)=integral_{1}^{infinity} M(floor t)*t^(-s-1)dt
converges absolutely. Abel/Dirichlet-series identity and analytic
continuation give J(s)=1/(s*zeta(s)). With h=s-1,
J(1+h)=h-(1+gamma)h^2+O(h^3). Thus the signed moments are

 integral M(floor t)/t^2 dt = J(1) = 0,
 integral M(floor t)*log t/t^2 dt = -J'(1) = -1,
 integral M(floor t)*log^2 t/t^2 dt =
     J''(1) = -2(1+gamma).

Since 1<=t<=R=sqrt x, log(t)<=H/2. The uniform expansion
1/(H-log t)=1/H+log t/H^2+O(log^2 t/H^3)
has integrable error: the beta<1 bound controls all log moments
and the tail errors O(R^(beta-1)polylog R).

Therefore

 S_cont(x) = -x/H^2+O(x/H^3),
 and more sharply
 S_cont(x) = -x/H^2-2(1+gamma)x/H^3+O(x/H^4).

Replacing continuous Li_2(x/k) by integer L(floor(x/k))
costs O(R): at each k the integer-floor discrepancy is <1 and
the difference Li_2(x/k)-Li_2(floor(x/k)) is O(1/log R).
Therefore for x=R^2:

 S_L(x) = -x/log^2 x -2(1+gamma)x/log^3 x
            +O(x/log^4 x).

All-order coefficients follow from higher J(s) derivatives at 1.
This paper calculation must be implemented in Lean separately; it
is not accomplished by the finite algebra in the new file.

## Why K_y and S_L match to all logarithmic orders

By the classical quantitative PNT,
B(t)=O_A(t/log^A t) for any fixed A>0, uniformly for t>=sqrt x.
Using only absolute values,

 |G(x)| <= sum_{k<=R}|mu(k)|(
   |B(floor(x/k))|+|B(R)|)
 = O_A(x/log^(A-1)x).

As A is arbitrary, G(x)=O_A(x/log^A x) for every fixed A
(with A-dependent constants). The certified M(x)=O(x^beta)
is also O_A(x/log^A x). Therefore F=M-G obeys the same
superlogarithmic estimates, and K_R(x)=S_L(x)+F(x)
has the same entire fixed-order asymptotic logarithmic expansion.

**This is not a polynomial improvement.** Being
O_A(x/log^A x) for every A does not imply O(x^theta) for
ANY fixed theta<1. The missing analytic result is still a
new signed power saving in the actual F and/or G source that
improves the unconditional 7/8 Mertens exponent.

Do not cite an 'Alladi-Hildebrand u=2 derivative theorem'
without precise source checking: Alladi's work separately covers
least- and greatest-prime-factor restricted Möbius sums. The
Mellin argument above is self-contained given the known beta<1
input and the zeta Laurent expansion.

## Exact-boundary amendment

The new weak-root source theorem is independent of RH: it rests on
unique high-prime ownership and the inequality q>y>=sqrt(x).
At y=floor sqrt(x), no correction is required. The Lean kernel also
checks the finite identity 1/(H-v)=1/H+v/H^2+v^2/H^3+
v^3/(H^3(H-v)) for nonzero denominators. Its Mellin moment and
integral consequences remain paper proofs pending Lean formalization.


## Fixed-y square-shell consequence (exact Lean target)

Fix integer R>=2 and the SAME cutoff y=R at both endpoints

  X0=R^2-1, X1=(R+1)^2-1.

Then floor sqrt(X0)=R-1<=R and floor sqrt(X1)=R<=R.
The extended sharp-root source theorem gives exactly

  delta_R := M(X1)-M(X0)
           = [F_R(X1)-F_R(X0)] + [G_R(X1)-G_R(X0)].

Here F_R(x)=K_R(x)-S_L(R,x) and
G_R(x)=-sum_{R<q<=x}xi(q) M(floor(x/q)), with the
SAME y=R in both endpoint brackets. No boundary correction
or new numerical assumption enters this within-shell identity.

The correctly CLIPPED kth floor-Li cofactor fiber is

  sum_{R<q<=floor(x/k)}[L(q)-L(q-1)]
    = L(max(R,floor(x/k)))-L(R),

NOT L(floor(x/k))-L(R) if floor(x/k)<R. For x=X0,
k=R is EMPTY since floor((R^2-1)/R)=R-1.
For x=X1, k=R is admitted and has upper quotient R+2.
In particular there is no spurious k=R lower-endpoint
floor-Li charge. Similar clipping applies to B=pi-L.

## Cross-shell gate migration is a separate exact term

The fixed-y shell theorem must NOT be mistaken for the claim that
sum_R [F_R(X1)-F_R(X0)] telescopes to F_H(H^2-1): consecutive
shells use different y. At the shared boundary
X=(R+1)^2-1, switching the cutoff R -> R+1 changes the
two bracket pieces by opposite amounts,

  F_{R+1}(X)-F_R(X) = -xi(R+1) M(R),
  G_{R+1}(X)-G_R(X) = +xi(R+1) M(R),

where xi(R+1) = 1_{R+1 prime}-[L(R+1)-L(R)].
The pair cancels in F+G=M, but is generally nonzero
separately. This exact gate-switch bookkeeping is a *different*
question from any within-shell boundary correction.

This audit does NOT claim the cross-shell gate-switch identity is
yet Lean-kernel proved. Formalize it before using global telescoping
claims to infer variance bounds. Both the initial 7/8 bound and the
new signed power saving remain distinct from these finite identities.

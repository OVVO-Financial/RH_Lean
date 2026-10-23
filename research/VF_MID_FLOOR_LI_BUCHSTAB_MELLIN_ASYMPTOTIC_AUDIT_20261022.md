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

The new Lean file consumes the pre-existing exact
PrimeSieveCollapseIdentity theorem. That library theorem requires
sqrt(x)<y (strict). At x=R^2, replacing y=R by R+1 changes
the smooth population by 0 if R+1 is composite and by
-M(floor(R^2/(R+1)))=-M(R-1) if R+1 is prime.
A literal y=R specialisation must account for this one prime.

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

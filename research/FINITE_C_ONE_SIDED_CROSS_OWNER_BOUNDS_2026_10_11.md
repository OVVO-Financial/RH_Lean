# Unconditional one-sided bounds on actual distinct-prime-owner energy

**Date:** 2026-10-11. **Scope:** new inequalities and sign asymptotics for the seed-inclusive cross-owner ledger of PR #929. These do not establish finite C, finite A or RH. New analytic statements below are paper-level; not Lean-kernel checked.

## 1. Exact coordinates

For integer R>=2, set X=R^2-1, L=log X, M(t)=sum_{n<=t} mu(n) and K_R=max_{0<=y<R}(M(y)-1)^2/(y+1)>=1.

For every genuine prime R<=p<=X, put t_p=floor(X/p)<R, and define

\[
H_R=-\sum_p M(t_p),\qquad
G_R^{\rm phys}=\sum_p M(t_p)^2,\qquad
D_R^{\rm phys}=\sum_{p\ne q}M(t_p)M(t_q)=H_R^2-G_R^{\rm phys}.
\]

The p!=q sum is **ordered** and retains the genuine c=1 prime seed. Let S_R be root-smooth signed Mobius mass, so M(X)=S_R+H_R.

Define centered cofactor objects

\[
G_R^{\rm ctr}=\sum_p(M(t_p)-1)^2,\qquad
B_R^{\rm ctr}=\sum_p(M(t_p)-1),\qquad
D_R^{\rm ctr}=(B_R^{\rm ctr})^2-G_R^{\rm ctr}.
\]

## 2. First unconditional bound: negative off-diagonal direction is already at R^2 K_R scale

For **every** integer R>=2,

\[
\boxed{D_R^{\rm ctr}\ge-\frac43 X K_R,\qquad
D_R^{\rm phys}\ge-\frac{11}{3}X K_R.}
\]

Proof: D>=-G because a squared real sum is nonnegative. The strict historical envelope gives (M(t_p)-1)^2<=(t_p+1)K_R. For p>X/2 this centered term is zero. Using the all-root prime reciprocal bound sum_{R<=p<R^2}1/p<=5/6 already stated in the Euler-product note in this PR, and #active<=X/2,

\[
G_R^{\rm ctr}\le K_R\left(X\sum_{R\le p<R^2}p^{-1}+\#\mathrm{active}\right)
\le\frac43 XK_R.
\]

Write N=pi(X)-pi(R-1). From M(t)^2<=2(M(t)-1)^2+2, we have G_phys<=2G_ctr+2N. For R>=3, all these primes are odd, so 2N<=X; using K_R>=1 gives G_phys<=(11/3)XK_R. The R=2 case is direct: G_phys=2, X=3, K_R=1. Therefore D_phys>=-(11/3)XK_R.

**This controls the negative side of the actual distinct-owner cross term at the sought normalization. The positive side is not controlled.** If the explicit 5/6 reciprocal estimate is not assumed, the classical prime reciprocal asymptotic still yields D_ctr >= -(log 2+o(1))XK_R and some absolute-constant lower bound for D_phys.

## 3. Second unconditional bound: eventual positive high/high and negative smooth/high signs

As R tends to infinity,

\[
\boxed{H_R=\frac{X}{L^2}+O(X/L^3),\quad
S_R=-\frac{X}{L^2}+O(X/L^3),}
\]

and

\[
\boxed{D_R^{\rm phys}=\frac{X^2}{L^4}+O(X^2/L^5),\quad
S_RH_R=-\frac{X^2}{L^4}+O(X^2/L^5).}
\]

Therefore an absolute R_0 exists such that **for every R>=R_0**, simultaneously

\[
\boxed{D_R^{\rm phys}\ge\frac12 X^2/L^4>0,\qquad
S_RH_R\le-\frac12 X^2/L^4<0,\qquad
\frac{-S_RH_R}{D_R^{\rm phys}}\to1.}
\]

This proves an arithmetic *aggregate* sign opposition, not a sign theorem for the separately conditioned shared-gcd and coprime pieces.

### Proof of the sharper leading mass

The earlier Euler prime-comb note already proved H_R~X/L^2. An explicit O(X/L^3) remainder follows from its same Abel calculation. Exactly,

\[
H_R=-\sum_{c<R}\mu(c)[\pi(X/c)-\pi(R-1)].
\]

The unconditional quantitative PNT and Mobius partial-sum estimates imply, for every fixed B>0,

\(\pi(y)=\operatorname{li}(y)+O_B(y/\log^B y)\) and \(M(y)=O_B(y/\log^B y)\).

All X/c>=R. Summing the PNT errors with B>=5 costs O(X/L^4), and the pi(R-1)M(R-1) boundary is negligible. Abel summation for Y=R-1 gives

\[
-H_R=M(Y)\operatorname{li}(X/Y)
+X\int_1^Y\frac{M(t)}{t^2(L-\log t)}dt+O(X/L^4).
\]

From F(s)=1/zeta(s)=s integral_1^infty M(t)t^{-s-1}dt and F(1)=0, F'(1)=1 we obtain

\[
\int_1^\infty M(t)t^{-2}dt=0,\qquad
\int_1^\infty M(t)\log t\,t^{-2}dt=-1.
\]

These and the second absolute logarithmic moment converge by the classical zero-free-region estimate for M. Since t<=R-1<sqrt X, the uniform expansion

\[
(L-\log t)^{-1}=L^{-1}+L^{-2}\log t+O(L^{-3}\log^2t)
\]

proves -H_R=-X/L^2+O(X/L^3). Also M(X)=O_B(X/L^B) for every B, so S_R=M(X)-H_R has the opposite leading term.

Finally,

\[
0\le G_R^{\rm phys}\le X^2\sum_{p\ge R}p^{-2}
\le X^2/(R-1)=O(X^{3/2})=o(X^2/L^5).
\]

Since D_phys=H_R^2-G_phys, its positive asymptotic follows.

## 4. Exact physical residue (what remains open)

For **every** R, an exact no-independence identity holds:

\[
\boxed{D_R^{\rm phys}+S_R H_R=H_R M(X)-G_R^{\rm phys}.}
\]

Thus the asymptotic high/high and smooth/high opposition is automatic, but bounding the remaining H_R M(X) down to R^2 K_R would still require new cancellation of RH strength. Do not treat these sign bounds as finite C.

For the cofactor seed, an additional exact identity is

\[
\boxed{G_R^{\rm phys}=G_R^{\rm ctr}-N-2H_R,\quad N=\pi(X)-\pi(R-1).}
\]

Since H_R>0 eventually, G_phys<=G_ctr eventually, and the stronger one-sided D_phys>=-(4/3)XK_R applies for all sufficiently large R.

## 5. Selected exact census checkpoints

These use the independent seed-inclusive audit and the PR #929 root-smooth census.

| R | H_R | S_R | G_phys | D_phys | S_R H_R | (-S_R H_R)/D_phys |
|---:|---:|---:|---:|---:|---:|---:|
| 56 | 47 | -41 | 651 | 1,558 | -1,927 | 1.23684 |
| 317 | 890 | -918 | 14,896 | 777,204 | -817,020 | 1.05123 |
| 1,000 | 6,567 | -6,355 | 124,635 | 43,000,854 | -41,733,285 | 0.97052 |
| 2,000 | 21,607 | -21,415 | 456,795 | 466,405,654 | -462,713,905 | 0.99208 |
| 5,561 | 124,373 | -126,917 | 3,142,391 | 15,465,500,738 | -15,785,048,041 | 1.02066 |
| 6,000 | 145,554 | -143,298 | 3,633,298 | 21,182,333,618 | -20,857,597,092 | 0.98467 |

**Limit:** none of these theorems bounds the original \(|Q_R|=|2M(R-1)-M(X)|\) by a fixed C times \(R\sqrt{K_R}\).
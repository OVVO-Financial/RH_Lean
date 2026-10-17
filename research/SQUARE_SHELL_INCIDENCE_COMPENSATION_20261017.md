# Exact square-shell prime-incidence compensation: what closes, and what remains

**Date:** 2026-10-17. **Carrier:** genuine Möbius weights on strictly open square shells. **Status:** new exact PAPER PROOFS and an independent integer census; **NO unconditional 5/2 energy estimate, 7/8 theorem, or RH proof**. This is a complementary investigation to the signed-covariance priority and the existing square-shell energy note. All mathematical identities below are paper identities until separately imported into Lean. Do not claim a compiled declaration from this note.

## 0. Correct physical definitions and target

For \(r\ge3\), put \(L=r^2\), \(U=r^2+2r=(r+1)^2-1\), \(I_r=\{L+1,\ldots,U\}\). Let \(S_r\) be the sites with greatest prime factor at most \(r\). Every other site has a unique high-prime owner \(q>r\), and is \(n=qc\) with \(1\le c\le r\). Squareful sites are retained geometrically but have Möbius weight zero.

Use the exact prime-incidence window
\[
P_r(c)=\pi(\lfloor U/c\rfloor)-\pi(\lfloor L/c\rfloor),\qquad
z_r(c)=\mu(c)P_r(c),\qquad
s_r=\sum_{s\in S_r}\mu(s),\quad t_r=\sum_{c\le r}z_r(c).
\]
Thus \(\Delta_r=s_r-t_r=\sum_{n\in I_r}\mu(n)\).

Fix \(D\ge1\) with \(2D<r\). Write \(f_D(g)={\bf1}_{D\le g<2D}\) and \(G_D(c,c')=f_D(\gcd(c,c'))\). The objective, not a consequence of these definitions, is the all-\(H\) bound
\[
\sum_{H\le r<2H}\Delta_r^2\ll_\eta H^{5/2+\eta}.
\]

## 1. Exact prime-incidence pair formulas (physical; no models)

Define \(b_D(c)=\sum_{s\in S_r}\mu(s)G_D(c,s)\). For cofactor windows \(c,c'\le r\), the exact common-prime count is
\[
J_r(c,c')=
\max\left(0,\,
 \pi\left(\left\lfloor\frac{U}{\max(c,c')}\right\rfloor\right)
-\pi\left(\max\left(\left\lfloor\frac{L}{c}\right\rfloor,
                    \left\lfloor\frac{L}{c'}\right\rfloor\right)\right)\right).
\]
Let \(J^\mu_{r,D}=\sum_{c,c'\le r}\mu(c)\mu(c')G_D(c,c')J_r(c,c')\), with ordered cofactor pairs.

Then the exact unordered physical pair masses are
\[
C^{SS}_{r,D}=\sum_{\substack{s<t;\ s,t\in S_r}}\mu(s)\mu(t)f_D(\gcd(s,t)),
\quad C^{ST}_{r,D}=-\sum_{c\le r}z_r(c)b_D(c),
\]
\[
C^{TT}_{r,D}=\tfrac12 z_r^{\mathsf T}G_Dz_r-\tfrac12 J^\mu_{r,D},
\qquad
C_{r,D}=C^{SS}_{r,D}+C^{ST}_{r,D}+C^{TT}_{r,D}.
\]
The minus sign for ST reflects \(\mu(qc)=-\mu(c)\). If \(q\ne q'\), \(\gcd(qc,q'c')=\gcd(c,c')\). If \(q=q'\), the physical gcd exceeds \(r\), so such ordered occurrences must be removed from the small-gcd TT sum. This is precisely what \(J_r\) does. Equal physical sites are also excluded by \(J_r(c,c)=P_r(c)\).

### The owner-collision expense is fully paid

If \(q>r\) divides both physical seats \(qc,qc'\in I_r\), then \(q|c-c'|<2r\); more directly \(q|c-c'|\le U-(L+1)<2r\). Thus \(|c-c'|<2\), so \(c=c'\) or \(|c-c'|=1\). Distinct cofactors have gcd 1. In that case \(q\le2r\) and \(c,c'>r/2\). Consequently for every \(D\ge2\), the common-owner correction is purely on the diagonal \(c=c'\); only \(D=1\) has adjacent-cofactor corrections.

Let \(k_q=\#\{c\le r:qc\in I_r\}\). Since the shell has length \(2r\) and \(q>r\), \(k_q\le2\), and \(\sum_q k_q\le2r\). Therefore
\[
\sum_{c,c'\le r}J_r(c,c')=\sum_{q>r}k_q^2
\le 2\sum_{q>r}k_q\le4r,
\qquad
\boxed{\left|J^\mu_{r,D}/2\right|\le2r.}
\]
No PNT or signed cancellation is needed. Its full dyadic cost is \(O(H^2)\), safely below the \(H^{5/2+\eta}\) objective.

## 2. A finite, exact incidence-level compensator

Define the **actual smooth-site divisibility channels**
\[
B_r(d)=\sum_{\substack{s\in S_r\\d\mid s}}\mu(s),
\qquad 1\le d\le r.
\]
Set
\[
\boxed{a_r(c)=\sum_{k\le r/c}\mu(k)B_r(kc)\qquad(1\le c\le r).}
\]
Finite Möbius inversion on multiples gives, for every \(d\le r\),
\[
\sum_{\substack{c\le r\\d\mid c}}a_r(c)=B_r(d).
\]

Let \(\beta_D=\mu*f_D\) be ordinary Dirichlet convolution:
\[
\beta_D(d)=\sum_{k\mid d}\mu(d/k)f_D(k),\qquad
f_D(\gcd(u,v))=\sum_{d\mid u,\ d\mid v}\beta_D(d).
\]
The divisibility matching implies the **exact kernel normal equation**
\[
\boxed{G_Da_r=b_D.}
\]
It holds for every \(D\), with no invertibility assumption on \(G_D\); in fact the coprimality kernel \(G_1\) is generally singular. This explicit \(a_r\) avoids the unjustified use of its inverse.

Center the prime-incidence cofactor vector at the matching smooth profile:
\[
e_r(c)=z_r(c)-a_r(c).
\]
Completing the symmetric quadratic form and using \(G_Da_r=b_D\) yields
\[
\boxed{
C_{r,D}=
\frac12e_r^{\mathsf T}G_De_r
+\underbrace{\left(C^{SS}_{r,D}-\frac12a_r^{\mathsf T}G_Da_r\right)}_{R^{SS}_{r,D}}
-\frac12J^\mu_{r,D}.
}\tag{A}
\]
**All coherent-mixed terms vanish identically.** This compensator acts on the prime-incidence kernel, not on the fixed sign \(\mu(qc)=-\mu(c)\). It is an exact algebraic cancellation, not a new decay estimate. Unlike the local logarithmic-integral model, \(a_r(c)\) is an explicitly arithmetic data-dependent compensator.

### Rigorous smooth-boundary estimate

Let \(W_{r,D}(g)=\sum_{d\mid g,\ d\le r}\beta_D(d)\). Expanding both smooth quadratic forms gives
\[
\boxed{
2R^{SS}_{r,D}
=-\!\!\sum_{\substack{s,t\in S_r\\\gcd(s,t)\ge r}}
\mu(s)\mu(t)W_{r,D}(\gcd(s,t)).
}\tag{B}
\]
For \(\gcd(s,t)<r\) the truncated divisor inversion already equals \(f_D(\gcd(s,t))\); for \(\gcd(s,t)\ge r\) this indicator is zero because \(2D<r\).

There are \(2r\) diagonal ordered pairs. For distinct shell sites with gcd \(g\ge r\), their difference is exactly \(g\), since the shell width is less than \(2r\). For each \(g\in[r,2r-1]\) there is at most one unordered pair of such multiples. Hence at most \(2r\) ordered off-diagonal pairs.

As \(|\beta_D(d)|\le\tau(d)\), \(|W_{r,D}(g)|\le\sum_{d\mid g}\tau(d)=\tau_3(g)\ll_\eta r^\eta\) uniformly in \(D\) because \(g\le U<4r^2\). Therefore
\[
\boxed{R^{SS}_{r,D}=O_\eta(r^{1+\eta}),\qquad
\sum_{H\le r<2H}R^{SS}_{r,D}=O_\eta(H^{2+\eta}).}
\]
The owner and smooth-boundary corrections in (A) are both fully within budget.

## 3. The centered row has an exact genuine-Möbius divisor phase

Define **full physical signed channels**
\[
F_r(d)=\sum_{\substack{n\in I_r\\d\mid n}}\mu(n).
\]
Because every transported seat is \(qc\) with \(q>r\), for every \(d\le r\) we have
\[
F_r(d)=B_r(d)-\sum_{\substack{c\le r\\d\mid c}}z_r(c)
=-\!\sum_{\substack{c\le r\\d\mid c}}e_r(c).
\]
Therefore the entire compensated quadratic has an exact divisor-diagonal form:
\[
\boxed{e_r^{\mathsf T}G_De_r
=\sum_{d\le r}\beta_D(d)F_r(d)^2.}\tag{C}
\]
Substituting into (A):
\[
\boxed{
C_{r,D}=\frac12\sum_{d\le r}\beta_D(d)F_r(d)^2
+O_\eta(r^{1+\eta}),
}\tag{D}
\]
with the error supported only on smooth large-gcd boundary and high-prime owner collisions. An equivalent direct proof by full-shell divisor inversion identifies that combined error with physical pairs (including diagonal) whose gcd is at least \(r\).

Only **squarefree** \(d\) can contribute to (C), since \(F_r(d)=0\) for squareful \(d\). On squarefree \(d\), true multiplicativity gives
\[
F_r(d)=\mu(d)
\sum_{\substack{L/d<u\le U/d\\(u,d)=1}}\mu(u),\qquad
\beta_D(d)=\mu(d)\!\!\sum_{\substack{k\mid d\\D\le k<2D}}\mu(k).
\]
Thus the centered residual has a genuinely varying squarefree-divisor **Möbius-parity phase**:
\[
\boxed{
e_r^{\mathsf T}G_De_r=
\sum_{\substack{d\le r\\\mu(d)^2=1}}
\mu(d)\!
\left(\sum_{\substack{k\mid d\\D\le k<2D}}\mu(k)\right)
\left(\sum_{\substack{L/d<u\le U/d\\(u,d)=1}}\mu(u)\right)^2.
}\tag{E}
\]
Unlike \(\mu(qc)=-\mu(c)\), this phase varies with the **unshared divisor \(d\)**. Equation (E) is a credible new analytic inlet; it is not, merely by being oscillatory, a proven moment estimate. In particular \(\mu(d)\) is not automatically an admissible nonprincipal character for the external OpenAI large-sieve framework.

## 4. An entire spectral tail is unconditionally within the target budget

Because \(|F_r(d)|\le 2r/d+1\), \(|\beta_D(d)|\le\tau(d)\ll_\eta r^\eta\) for \(d\le r\), ordinary absolute summation gives uniformly in \(D\)
\[
\boxed{
\sum_{\sqrt r\le d\le r}
|\beta_D(d)|F_r(d)^2
\ll_\eta r^{3/2+\eta}.
}
\]
Summing over \(H\le r<2H\) costs \(O_\eta(H^{5/2+\eta})\). Combining with (A)–(D) gives the sharpened exact-error reduction
\[
\boxed{
2C_{r,D}=
\sum_{1\le d<\sqrt r}\beta_D(d)F_r(d)^2+
O_\eta(r^{3/2+\eta}),
\quad 2D<r.
}\tag{F}
\]
In particular every band with \(D\ge\sqrt r\) is already payable, since \(\beta_D(d)=0\) for \(d<D\). The **only unresolved divisor modes** in this representation have \(D\le d<\sqrt r\).

This is a genuinely quantitative, uniform, elementary elimination of the owner-collision, boundary and high-divisor tails. It does NOT remove the still-difficult low-divisor signed moment.

## 5. Critical adversarial audit: the zero mode is the original problem

For \(D=1\), \(f_1(g)={\bf1}_{g=1}\), so \(\beta_1(d)=\mu(d)\). In particular
\[
\sum_{d<\sqrt r}\beta_1(d)F_r(d)^2
=\underbrace{F_r(1)^2}_{=\Delta_r^2}+
\sum_{2\le d<\sqrt r}\mu(d)F_r(d)^2.
\]
The \(d=1\) term is **exactly the shell energy we seek to bound**. It has not disappeared. If the gcd bands are recombined before any independent source estimate, the Möbius-inverted coefficients telescope back to this zero mode. Algebraic completion of squares therefore cannot, by itself, imply the \(5/2\) saving.

Any analytic proof must establish an **independent**, uniform signed estimate for (E)/(F), with genuine \(\mu\) arithmetic, fixed square endpoints and all mixed channels retained. This is the precise remaining obstacle. Proposals invoking a random-sign approximation, a generic character large sieve without a legal coefficient/phase map, a full-\(M\) bound of equal strength, or an assumed covariance estimate are circular.

## 6. Integer-exact physical validation

Run:
\[
\text{python3 scripts/square_shell_prime_incidence_compensation.py --max-root 317 --verbose}
\]
The script uses a fresh genuine-Möbius linear sieve and integer arithmetic only. It checks exact physical pair enumeration versus (i) the cofactor/prime-incidence SS/ST/TT formulas, (ii) owner geometry and collision identity, (iii) normal equations \(G_Da=b_D\), (iv) compensation (A), (v) full physical large-gcd boundary reassembly, (vi) divisor-phase formula, and (vii) the high-divisor absolute budget. The default suite covers 15 \((r,D)\) windows.

| \(r,D\) | SS | ST | TT | \(C_{r,D}\) | centered / 2 | smooth boundary | owner collision |
|---|---:|---:|---:|---:|---:|---:|---:|
| \(14,2\) | 0 | 7 | 2 | 9 | 11.5 | 1 | -3.5 |
| \(31,2\) | -2 | 9 | -9 | -2 | 2 | -0.5 | -3.5 |
| \(137,1\) | -22 | -50 | 708 | 636 | 640 | 8 | -12 |
| \(137,8\) | -1 | 14 | -7 | 6 | 15 | -3 | -6 |
| \(317,1\) | -56 | 49 | 19 | 12 | 15 | 23 | -26 |
| \(317,2\) | 63 | -89 | -56 | -82 | -72.5 | 16.5 | -26 |

In particular the actual \(r=137,D=1\) row is \(-22-50+708=636\), so an individual small-gcd band's positive TT covariance is real and may be large. The exact compensator isolates it but does not establish a norm gain.

## 7. Acceptance ladder and next work

1. **Finite exact incidence:** PAPER PROVED, genuine integer census passed. Native Lean correspondence to existing smooth/transport definitions is NOT YET FORMALIZED; do not label it Lean-certified.
2. **Compensating cancellation:** PAPER PROVED for the explicit arithmetic compensator (A), including separate \(O_\eta(H^{2+\eta})\) owner/boundary costs. This does **not** establish cancellation for the proposed local-Li compensator.
3. **Spectral high-divisor tail:** PAPER PROVED \(O_\eta(H^{5/2+\eta})\) by absolute counting. The missing signed, low-divisor range \(d<\sqrt r\), including the \(d=1\) zero mode, remains OPEN.
4. **Full 7/8 reconstruction:** CONDITIONAL only. An independently proved uniform signed moment for all remaining low-divisor and gcd-band contributions, coupled with the already established diagonal and high-gcd bills, implies the dyadic shell energy and hence the Mertens 7/8 consequence. No such moment estimate is supplied here.

**Research directive:** Owner/Wheel should port (1) and (A)–(F) with exact endpoints; Analytic should attack the genuine squarefree \(d\)-phase moment (E) while flagging its \(d=1\) trap; Census should keep testing the complete physically signed SS/ST/TT interaction; Referee should reject a compensated norm proof that hides \(\Delta_r^2\) in its premise; Lean should formalize finite identities without inventing an inequality or weakening the original canonical VF objective. Maintain once-daily agent schedules and human-only merge.
# CORR-4 corrected exponent and octave-source ledger (2026-10-26)

**Status.** The complete six-point decoder algebra, coefficient identification,
constant-four physical tail and 36-aligned T-free support are proved in the
selected Lean closure. The new Branch-II finite-prefix and octave identities
are being certified separately. A strict Mertens exponent below 7/8 is **NOT**
proved by these statements. The user-supplied Case-A balancing formula and
"double zero" claim require corrections below.

## 1. Centered plateau geometry and scale transfer

Let X=R^2-1 and let H>=1 be the literal integer discrete-tent width. The
1-Lipschitz property of the integer Mertens summatory function implies
\[
 |\mathcal A_H M(X)-M(X)|
 \le H^{-2}\sum_{|h|<H}(H-|h|)|h|
 =\frac{H^2-1}{3H}.
\]
Consequently |M(X)|>=H implies
\[
 |\mathcal A_H M(X)|\ge \frac23H+\frac1{3H}.
\]
This is unconditional. A bound of O(H^(1-kappa)) for the **complete**
smoothed Mertens function at that same H contradicts a plateau of height >=H
for H sufficiently large.

Crucial quantifier: to deduce a new global exponent beta<7/8, the
signed-source saving must be UNIFORM at
\[
 H\asymp R^{2\beta}=X^\beta,\quad
 \beta=\frac78-\frac\eta4.
\]
A result proved only for H\asymp R^(7/4), namely H\asymp X^(7/8),
can improve the constant at exponent 7/8 but cannot automatically
improve the exponent. The tentative choice eta=(7/2)kappa yields
H\asymp R^((7/4)(1-kappa)), but **the same low-u estimate must still
be proved in that narrower-window regime**. No interpolation from the
single baseline width is valid without an independent uniform theorem.

For arbitrary eta, X/H\asymp R^(1/4+eta/2), NOT R^(1/4), and
X\asymp H^(8/(7-2eta)), NOT H^(8/7). The proper aligned high-u cutoff is
L\asymp (X/H)H^(2kappa), rounded to L=36q+1. It pays the high-u source
by O(X/L)=O(H^(1-2kappa)). The gate LT+H-1<=X holds asymptotically for
T=H^(1-delta), delta>2kappa, provided the other support conditions hold.
The previous low-norm budget 2592 T^3/H^2 is O(H^(1-3delta)).
All estimates remain subject to the exact root/slack hypotheses.

## 2. Zero-aligned source and its genuine octave decomposition

The literal #919 quotient kernel K has K(36q)=0. Let
d(u)=K(u)-K(u-1), L=36q+1, and
\[
 B_u=\sum_{m\ge1}a_6(m)\Phi_{H,X}(um),\qquad
 D_u=B_u-B_{u+1}=\sum_m a_6(m)
   [\Phi_{H,X}(um)-\Phi_{H,X}((u+1)m)].
\]
Then the finite Abel formula becomes
\[
 \boxed{\sum_{1\le u<L}d(u)B_u
    =\sum_{1\le u\le L-2}K(u)D_u.}\tag{A}
\]
The D_u are genuine tent-smoothed octave sums. Their weights
Psi_u(m)=Phi(um)-Phi((u+1)m) are nonnegative. This is a structural
identity, not a quantitative |D_u| estimate.

If LT+H-1<=X, the total contribution of 1<=m<=T to the left side
vanishes exactly, term by term after the u pairing. Hence the
m>T source equals the unrestricted m>=1 source on the low-u range.
This is the T-free source theorem.

The terminal K(L-1)=0 also sharpens the Abel upper-tail constant
from 4 to 2, provided the terminal tent weight is zero. The high-u
mass bound remains O(X/L); the constant-2 actual-a6 composition
should be separately Lean-certified.

## 3. Fixed hyperbola Branch II is *not* an independent gain

Let mu6=mu*1_(.,6)=1, b6=chi_-3*mu6 (pointwise), and
a6=mu6*b6 (Dirichlet convolution). Denote by mu6,<=r and mu6,>r
the arithmetic functions supported respectively on a<=r and a>r.
The full decoder satisfies the exact **coefficient identity**
\[
 \boxed{d*(\mu_{6,>r}*b_6)
  =\mu-(\mu_{6,\le r}*
        (\delta_1-\delta_2-\delta_3+\delta_6)).}\tag{B}
\]
When the sharp/tent cutoff Y>=6r, the full finite prefix of the
four-point low-owner correction is identically zero. Thus
\[
 \sum_{n\le Y}[d*(\mu_{6,>r}*b_6)](n)=M(Y),
 \qquad Y\ge6r.\tag{C}
\]
The truncated low-u branch is M(Y) **minus its u>=L boundary tail**,
not an independent small function. The upper-u Branch-II tail can be
bounded by monotone Abel plus
\[
 \sum_{r<a\le Y/L}\left\lfloor\frac{Y}{La}\right\rfloor
 \le \frac YL(1+\log(Y/(Lr)))\quad\text{when }Y/L>r,
\]
or zero if Y/L<=r. This is a log-level boundary bill; it does not
bound M(Y) independently. The full Branch-I and overlap payments
have their separate six-point bounds.

The *actual* source of a possible new exponent is therefore the
signed arithmetic content of the smoothed octaves, not another
algebraic reassembly of the high owner.

## 4. Correct Case-A and Case-B algebra

Set alpha=7/8-sigma, 0<alpha<1, and suppose X~R^2.

**Case A, an independently proved pointwise bound on A6.** If each
cumulative a6 prefix at X/u is bounded by O((X/u)^alpha), a naive
triangle inequality gives
\[
 \mathrm{Low}_{u<L}\ll X^\alpha L^{1-\alpha},
 \qquad \mathrm{Upper}\ll X/L.
\]
Balancing them yields
\[
 \boxed{L_*=X^{(1-\alpha)/(2-\alpha)}
     =X^{(1+8\sigma)/(9+8\sigma)},\quad
 \beta_A=\frac1{2-\alpha}=\frac8{9+8\sigma}.}\tag{D}
\]
The formula 8(1-sigma)/(9+8sigma) is **not** the result of this
balancing. Case A beats 7/8 only if
\[
 \boxed{\sigma>1/56,}
\]
not 1/64. Moreover, the repository's bound on M(X) does **not**
automatically yield a matching pointwise power bound on A6:
the inverse quadratic L-factor and masking require an independent
analytic transfer.

**Case B, an independent octave/bilinear bound.** If genuinely
\[
 |D_u(X,H)|\le C X^\alpha/u
 \quad\text{uniformly throughout }1\le u\le L-2
\]
(or a stronger direct coupled bound on sum K(u)D_u), then
\[
 \mathrm{Low}\ll X^\alpha\log L,\qquad
 \mathrm{Upper}\ll X/L.
\]
Taking L~X^(1-alpha) gives
\[
 |\mathcal A_H M(X)|\ll X^\alpha\log X
\]
after appropriate gates and all other source terms are paid.
The logarithm gives the growth exponent alpha with any epsilon
loss; a pure O(X^alpha) conclusion requires removal of log L
or an independently proved coupled estimate.

**Neither** the interval length X/u^2 nor the exact identity (A)
proves the hypothesized gain |D_u|<<X^alpha/u. From a pointwise
prefix bound alone, the immediate estimate is
|D_u|<<X^alpha u^(-alpha), which is Case A.

## 5. Spectral t-growth invalidates a free Case-B conclusion

For s=sigma0+it with 0<sigma0<1, the physical Mellin octave factor
obeys
\[
 |u^{-s}-(u+1)^{-s}|
 \le \min(2u^{-\sigma_0},\,|s|u^{-\sigma_0-1}).
\]
Hence
\[
 \sum_{u\ge1}|K(u)(u^{-s}-(u+1)^{-s})|
 \ll_{\sigma_0}1+|s|^{1-\sigma_0}.
\tag{E}
\]
Convergence for **fixed** s is not uniform spectral boundedness
through |t|<=X/H. At sigma0=7/8, X/H~X^(1/8), the upper majorant
allows X^(1/64), already a power loss. The actual periodic mean-zero
structure may permit extra cancellation, but it must be proved
uniformly at the physical frequency/conductor weights; (E) does
not furnish a free saving.

Moreover, the literal discrete tent is a finite exponential sum
divided by s in Perron coordinates. It does not inherit the continuous
tent's uniform t^(-3) kernel at arbitrarily high frequencies without
a separately bounded lattice-aliasing/Perron tail.

## 6. False second-order zero and split/smooth labels

The exact excluded-six Dirichlet series
\[
 F_6(s)=((1-3^{-s})(1-4^{-s})\zeta(s)L(s,\chi_{-3}))^{-1}
\]
has a **simple** zero at s=1, not a double zero. In particular,
F_6'(1) is nonzero. One cannot infer exact split/smooth main-term
cancellation at order X/log^2 X from a nonexistent double zero.

The numerical sharp split/smooth/bare decomposition at R=1027,
X=1,054,728, H=5000 (high-prime gate p>1027) is:
- bare split prime: sharp -38,796; true tent -38,800.543828;
- split-prime composite: sharp +49,446; true tent +49,461.588935;
- 1027-smooth complement: sharp -10,568; true tent -10,556.027105;
- combined: sharp +82; true tent +105.018002.

These totals are exact to the quoted tent precision using the
genuine a6 multiplicative local factors. Assigning opposite
continuous Buchstab main-term values requires a proved
prime-cofactor/smooth asymptotic, not a hand-chosen decomposition.
If a *new* split-prime gate R_u=floor(sqrt((X+H)/u)) is used, the
numerical categories must be recomputed under that gate.

## 7. Conditional exponent examples, not obtained bounds

At the narrower H=X^(7/8-eta/4), a **proved** low-u bound
O(H^(1-kappa)) plus all unconditional tails would contradict
a high-amplitude plateau and yield the corresponding pointwise
Mertens exponent by the actual square-endpoint transfer.
The Lean #1021 general-power biconditional is conditional; it
does not prove this independent signed low-u estimate.

- kappa=1/28 and the *separately justified* eta=(7/2)kappa
  correspond algebraically to beta=27/32=0.84375.
- sigma=1/1344 under the **hypothetical** Case B would give
  alpha=1175/1344, approximately 0.874256, plus arbitrarily
  small epsilon for the logarithm.

PR #1022's local low-Gaussian CRT saving is not a uniform bound
on these physical a6 octaves. It cannot be inserted here as the
sigma=1/1344 theorem without source-by-source detector transfer.

**Open theorem:** genuine signed octave/cofactor cancellation at
a uniform family of H=X^beta with beta<7/8, with the complete
split prime, smooth Buchstab complement, moving boundary collars,
actual a6 phases and all spectral ranges. No strict improvement
over the imported 7/8 guidepost is asserted here.

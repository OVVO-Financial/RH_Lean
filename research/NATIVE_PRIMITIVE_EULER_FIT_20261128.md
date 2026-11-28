# Native primitive Euler probability and all-place fitting (paper result)

Base: #1214 at d9c30d7. Preserve the two source derivations in
SIGNED_MOBIUS_SPLIT_COMPENSATION_20261127.md and
PRIMITIVE_EULER_ADMISSIONS_20261127.md. These are research notes, not a
production RH supplier. No external RH/GRH theorem is used.

## 1. Arithmetic probability, not a probability defined from the deficit

On n cyclic slots, decompose the complexified regular cyclic module by the
exact order d of the shift eigenvalue. The orthogonal projector E_{n,d}
has rank phi(d). The trace-normalized uniform cyclic projector gives

    wt_n(d) = phi(d)/n (d | n),  sum_{d|n} wt_n(d) = 1.

Proof: the Fourier labels are j in Z/n, with order n/gcd(n,j).
There are phi(d) labels of order d. Under CRT n = product q^a, the
uniform frequency coordinates are independent and the order law is
the product of the laws phi(q^j)/q^a, 0 <= j <= a.

In particular, for p not dividing k, the section Z[C_p] tensor L_k
has dimension p phi(k). Its primitive subspace L_{pk} is the kernel of
summation in the p-coordinate, of dimension (p-1)phi(k). Its exact
retained weight is 1-1/p, and complementary weight is 1/p.
The normalized primitive trace is c_n(j)/phi(n); for p not dividing j,k,
c_{pk}(j)=-c_k(j). This is a native analogue of the arithmetic weight
evaluation, not a claim of a new Deligne-Lusztig theorem or of a
probability law for RH-strength cancellation. These are actual cyclic
frequency populations, not independent random rational primes.

## 2. All finite places: exact exceptional order tower

Put c=floor sqrt(x), a=c+1, r=c/a, N=floor x. Let
B_n=a I-c U_n, D_n=det B_n, n>=2, and D_1=1.
D_n is the positive homogeneous cyclotomic evaluation Phi_n(a,c).
For every finite prime l dividing ac, D_n is an l-adic unit for every n,
by reduction of a I-c U_n (U_n is invertible).
Otherwise l is odd, and put h=ord_{F_l^*}(a/c). Since a-c=1,
h>1. For n=h l^j, j>=0, the precise valuation law is

    v_l(D_n) = v_l(D_h)  (j=0),
    v_l(D_n) = 1         (j>=1);
    v_l(D_n) = 0         (n not in this tower).

Proof: write n=l^j t, l not dividing t. For j=0, the roots of Phi_t
mod l have exact order t (separability of X^t-1 and the divisor
factorization). For j>=1,
Phi_{l^j t}(X) = Phi_t(X^{l^j})/Phi_t(X^{l^{j-1}}), and reduction mod l
is Phi_t(X)^{phi(l^j)}. This proves the support. For t=h the homogeneous
cyclotomic product and the odd-prime lifting-the-exponent identity give
v_l(a^{l^j d}-c^{l^j d})-v_l(a^{l^{j-1}d}-c^{l^{j-1}d})
= 1 if h|d, otherwise 0, for d|h. Summing with mu(h/d) leaves 1.
This proves the admission formula in the source note, but also accounts
for exceptional blocks at primes OTHER than the entering prime.
It does not give a small sum of the original log denominators at all
places; v_l(D_h) may be large.

In the integral cyclic basis v_n, U_n v_n, ..., U_n^{phi(n)-1} v_n
(the CRT generator proof in the source note), the cokernel of B_n
mod l is cyclic of dimension at most one: if c is a unit, imposing
B_n=0 imposes U_n=a/c, leaving at most one generator. If c is not a
unit B_n is invertible. Hence the exact rank is phi(n)-1 when
l|D_n and phi(n) otherwise. The full family on labels n<=N loses at
most 1+floor(log_l N) directions at any fixed l. For any subpopulation
of distinct labels the same absolute bound holds, with no distribution
hypothesis on the served primes.

For the complete population R=sum_{2<=n<=N} phi(n) is of order N^2:
count coprime ordered pairs in [1,N]^2 by the elementary union bound
sum_{d>=2}1/d^2<1, then use symmetry. Selecting independent columns
mod l gives real independent directions as well. Under the
trace-normalized projector on the complete primitive space the lost
dimension fraction is O(log N/N^2). This is a rank statement about
the enlarged cyclic tests, NOT the dimension of the original star
or an exponentially small missing-rank estimate for the original frame.

## 3. Full-rank place-dependent determinant repair

For an exceptional block at l, write t=phi(n). In the cyclic integral
basis the first t-1 columns of B_n are a e_j-c e_{j+1},
0<=j<t-1. Replace just its last column by e_0. Call the repaired
endomorphism B_{n,l}; on nonexceptional blocks leave B_n unchanged.
The determinant of the repaired matrix is c^{t-1} (expand along its
last column); c is an l-adic unit. Thus for every l and n the
result is an invertible integral matrix over Z_l. This changes at most
one column per affected block and needs no prime-dependent large
coefficients in the cyclic basis.

The archimedean determinant change is independently bounded on the
same full physical primitive spaces. With F_n(r)=det(I-r U_n),

    log D_n = phi(n) log(c+1)+log F_n(r),
    |log F_n(r)| <= tau(n) log(c+1).

The second assertion follows from the cyclotomic product
sum_{d|n} mu(n/d) log(1-r^d); each absolute logarithm is at most
log(c+1). For a repaired block

    |log(D_n/c^{phi(n)-1})|
       <= log c + phi(n)/c + tau(n) log(c+1).

All exceptional indices at l lie in the one geometric tower above,
so sum n <= 2N and sum n^{1/4} <= N^{1/4}/(1-2^{-1/4}).
The elementary divisor estimate tau(n)<=C n^{1/4} follows by
absorbing the finitely many primes below 16 into a constant, and
using a+1<=2^a<=p^{a/4} for p>=16. It follows that, uniformly in l,

    sum_{2<=n<=N} |log det B_{n,l} - log D_n| = O(sqrt x).

Indeed N/c=O(sqrt x), the number of terms is O(log N), and
N^{1/4}log x + log^2 x = O(sqrt x).
In particular this bound holds for any bounded signed weight on the
labels, without changing the sign or dropping the complementary
population. For any fixed full primitive integral basis the determinant
of the column Gram changes by precisely the square of the matrix
determinant ratio, irrespective of how well-conditioned the cyclic
basis is. This is a uniform real comparison of local repairs, not
a sum of archimedean costs over infinitely many primes.

## 4. The actual physical projector can also be fitted

The primitive lattice L_n has an explicit independent, saturated CRT
basis: on each q^a-coordinate take, for each of the q^{a-1} fibres
modulo q^{a-1}, the q-1 differences e_j-e_anchor (last element of
the fibre). Tensor these bases over the prime powers. Its counting
Gram is a tensor of copies of I+J (size q-1). Each factor has determinant
q, eigenvalues 1 and q. In particular only primes dividing n divide
the primitive Gram determinant.

Reserve M+1 slots for each of the n original cycle coordinates, where
M=max(2,ceil x^3). The common untwisted embedding repeats each coordinate
M times. This uses O(x^5) physical slots for a complete n<=N family,
available eventually from the existing b/x^2-2 lower bound with
b=exp(x^eps). The original n slots can be kept as the first copy; the
additional coordinates are actual repeated readings in the layer, not
a change in the integer labels. The shift is transported on the
replicated section. This is an enlarged test family, not a claim that
the old rank-one star amplitude already spans it.

For each l let m_l=M-1 if l|M and M otherwise. If l does not divide n,
retain m_l copies of each coordinate. If l|n, retain m_l+1 copies at
the anchor coordinate of every fibre in the l-power factor of the CRT
basis, and m_l copies at the other coordinates, identically over all
other factors. The local l-factor Gram blocks then are

    m_l I + (m_l+1) J,
    det = m_l^{l-2} (l m_l+l-1),

which are units modulo l. Other factors retain their original
unit Gram determinants. In the case l not dividing n use m_l G_n.
Thus the physical Gram is invertible modulo l on the SAME full
primitive module at each chosen l. Its orthogonal projector, computed
as C(C^T C)^{-1}C^T on the actual retained slots, is l-integral on
all integral tests. After the preceding endomorphism repair the
column Gram is still l-unimodular. No congruence index is hidden in
this assertion. The integer section embedding remains injective
with an integral left inverse (read one copy then a CRT basis
coordinate). The same retained slots can be used for both profiles.

For every real vector the new squared metric relative to the
common repeated metric lies between 1-1/M and 1+1/M. Thus for t
independent columns the log-covolume perturbation is O(t/M).
On the full family sum t <= N^2, hence O(1/x) per complete copy.
The U_n shift need not be an isometry of the cropped metric;
use this sandwich to transport its original counting-metric estimates.
This regularization is legitimate on every original layer once
the polynomial address requirement fits the common core.
For served p>x^{3/4}, a label pk has a unique entering prime;
route it at its actual partner site and repeat with the existing
translate multiplicities. Summing the error across sites per original
top counts each served label once. Keep the complete complementary
reference table explicit. Do not count the added Fourier directions
as extra native tops or silently change Q_*.

## 5. What remains: independent signed comparison on the original source

Let E be the calibrated residual in the preserved split note. The
primitive trace reference in the admissions note gives

    P_E(x) = sum_{n<=x} Lambda(n) E(n/x)
           = -sum_{1<=j<=H} r^j T_j(x)/j - R_E(x)
               + O_E(sqrt x log(2x)),

with H=O(sqrt x log x). Every fixed trace order sees all nontrivial
zeros via its Mellin transform. The determinant repairs preserve the
bounded signed log determinant to O_E(sqrt x) uniformly in l; the
physical projector can be made integral there. This gives an actual
finite-place family on the enlarged primitive test spaces, with
an explicit Euler frequency probability law and a full-rank selection.

It does NOT prove a small global signed height of the original
normalized determinants. The denominator (c+1)^phi(n) in F_n(r)
must still be accounted for, and an inverse ratio formed only
from locally unit determinants and a fixed common determinant
has the opposite height certificate of equal magnitude. Such
cancellation is a bookkeeping identity, not an independent bound.

In particular the uniform real perturbation is not an independent
one-sided estimate of sum_j r^j T_j(x)/j + R_E(x). The transfer
from the enlarged primitive module to the original star-section
arithmetic source, the common global witness, and the independent
archimedean estimate on the signed sum remain open. The primitive
projector and local repairs alone do not force the critical-zero
component. Do not use the desired signed bound to define a witness.
The complete-window supplier and literal native_riemannHypothesis
remain the sole terminal acceptance criteria.

## Verification

The independent finite regression scripts/research/check_primitive_euler_fit.js
checks the frequency law, order towers, admission valuations, companion
determinants, exact mod-l ranks, repairs, and tensor Gram regularization
with BigInt arithmetic and Bareiss elimination. The proofs of §§1–5 are
on paper. The original alternating-exchange benchmark and source notes
remain part of the construction.

Finite checks executed in this session: {"frequencyOrders":1098,"orderTowerCases":40185,"higherTowerCases":40,"nonunitCases":357,"companionDeterminants":124,"rankCases":1860,"rankDefects":52,"unitRepairs":52,"physicalGramCases":744,"admissionCases":442}.

## 6. The rational product and the complete real clock

Write $N=\lfloor x\rfloor$, $c=\lfloor\sqrt{x}\rfloor$, $q=c+1$,
$r=c/q$, and use the calibrated $V,E$, cutoff $H$ and reference
$R_E$ of the two source notes. Here $x\ge4$ can be any real number.
The new Lean source is [NativePrimitiveDeterminantCertificate.lean](NativePrimitiveDeterminantCertificate.lean).

For $a_n=\operatorname{round}(cE(n/x))$ and $2\le n\le N$, put
$$
Y=\prod_n(D_n/q^{\varphi(n)})^{a_n}\in\mathbb Q_{>0},
\qquad W=\sum_n E(n/x)\log F_n(r).
$$
Möbius inversion of the complete cyclic characteristic polynomial gives
$F_n(r)=\prod_{d\mid n}(1-r^d)^{\mu(n/d)} =r^{\varphi(n)}\Phi_n(1/r)$. Thus the construction only uses integer powers.
The triangle inequality is needed only on the fractional rounding errors.
Since $q^{-1}\le1-r^d\le1$ for $d\ge1$, it gives
$$
 |c^{-1}\log Y-W|\le {\log q\over2c}\sum_{n\le N}\tau(n)
 \le {N(1+\log N)\log q\over2c}.
$$
The last inequality counts divisor pairs in the hyperbola by the first
coordinate. For the trace error, expand each $\log(1-r^d)$ through
degree $\lfloor H/d\rfloor$. Its remainder has magnitude at most
$r^{d(\lfloor H/d\rfloor+1)}/(1-r^d)\le r^H/(1-r)$.
Collecting the terms with $d\mid j$ gives the actual Ramanujan trace.
In particular, with $\mathcal S_x=\sum_{j\le H}r^jT_j(x)/j+R_E(x)$,
$$
 \left|\mathcal S_x-\left(R_E(x)-{\log Y\over c}\right)\right|
 \le {r^H\over 1-r}\sum_{2\le n\le N}|E(n/x)|\tau(n)
       +{N(1+\log N)\log q\over 2c}.
$$
Here $r^H\le(2x)^{-4}$, so the first error is bounded using the
boundedness of the fixed residual and the second is $O(\sqrt{x}\log^2(2x))$.
This retains the independently evaluated reference including its sign.

There is a direct exact transfer at *every* real argument. The definition
of the residual and the von Mangoldt divisor identity give
$$
 \mathrm{statementOCGz}(x)+P_E(x)
 =\sum_{k\le x} V(k/x)\log k-x\log x+(1+\gamma)x.
$$
Indeed, multiplying the dilation sum defining $E(d/x)$ by $\Lambda(d)$
and grouping by $k=dj$ gives $\sum_{d\mid k}\Lambda(d)=\log k$.
The same integer exponents used in $Y$ can be read at this endpoint.
For every real $x\ge4$, replacing $P_E$ in this formula by
$\sum_{n\le x}(a_n/c)\Lambda(n)$ changes it by at most
$(\log 4+4)\sqrt x$. Its entire rounding charge is bounded by
$\psi(x)/(2c)$, and Chebyshev gives $\psi(x)\le(\log 4+4)x$.
The hosted kernel checked `statementOCGz_add_residual`,
`statementOCGz_rounded_residual`, `block_eq_cyclotomic`,
`trace_reference_uniform` and `statementOCGz_sub_trace` at `8a2d6dd`,
each with exactly `propext`, `Classical.choice` and `Quot.sound`.
The last declaration exposes the two real quadratures and the finite
trace tail with their signs. The analytic estimates for the quadratures
and the original-star comparisons in §§7–8 are paper deductions.
[Hosted Lean output](https://github.com/OVVO-Financial/RH_Lean/actions/runs/46152415082/job/141001861160)

For the term on the right, $\int V=1$ and
$\int V(t)\log t\,dt=-(1+\gamma)$ by the calibration in the split note.
The Riemann sum has error $O_V(1+\log x)$.
On $[1/x,1]$ the variation of $V(t)\log(xt)$ is at most
$(\operatorname{Var}V+\|V\|_\infty)\log x$. The contribution of the
first mesh cell, after multiplying the integral by $x$, is at most
$\|V\|_\infty\int_0^1|\log u|\,du$. Any final fractional cell costs
$O_V(\log x)$. Thus the reference estimate in the admissions note gives
$\mathrm{statementOCGz}(x)=\mathcal S_x+O_E(\sqrt{x}\log(2x))$.
There is also a square-root error estimate on the whole large-prime part of $W$ that keeps its signed first-order correction. Let $u=\log(1+1/c)$, and take all $p>x^{3/4}$ and $pk\le x$. The same estimate holds for any subset of these $p$ owing to the uniform error bound. Then
$$
\begin{aligned}
\sum_{p,k}E(pk/x)\log F_{pk}(r)
={}&\log q\sum_p E(p/x)
-\sum_{p,\,k\ge2}E(pk/x)\Lambda(k)\\
&+\frac{u}{2}\sum_{p,\,k\ge2}E(pk/x)\varphi(k)
+O_E(\sqrt{x}).
\end{aligned}
$$
The $k=1$ factor is $q(1-r^p)$. At $k\ge2$, use $F_{pk}(r)F_k(r)=F_k(r^p)$ and the exponential bound on the $r^p$ terms from the admissions note. In the cyclotomic divisor sum for $\log F_k(r)$ write
$\log(1-e^{-z})=\log z-z/2+O(z^2)$, uniformly for $0<z\le1$.
The constant, logarithmic and linear sums use $\sum_{d\mid k}\mu(k/d)=0$, $\sum_{d\mid k}\mu(k/d)\log d=\Lambda(k)$ and $\sum_{d\mid k}d\mu(k/d)=\varphi(k)$. The remainder is bounded by $C u^2\sigma_2(k)$. Since $k\le x^{1/4}$, $\sigma_2(k)\le\zeta(2)k^2$, and there are at most $x/k$ possible $p$ for a fixed $k$, the entire remainder costs $O_E(u^2 x\sum_{k\le x^{1/4}}k)=O_E(\sqrt{x})$. The complementary population in $W$ must be carried through without this expansion.

The [Parseval path note](NATIVE_PARSEVAL_PATH_AMPLIFICATION_20261128.md) sharpens the integer quadrature to $O(1)$ by applying the trapezoidal rule to its derivative of bounded variation.

Both errors in the transfer to the full real window are uniform on the entire real half-line from any sufficiently
large absolute threshold. A fixed positive exponent margin absorbs their
logarithms with one constant per epsilon before the window is chosen.

## 7. Both reciprocal rational certificates at all places

Set $M=\sum_n a_n\varphi(n)$ with $a_k=0$ outside $[2,N]$.
When $\ell\nmid cq$, let $h=\operatorname{ord}_\ell(q/c)$,
$b_\ell=v_\ell(D_h)$, and
$J_\ell=b_\ell a_h+\sum_{j\ge1}a_{h\ell^j}$. The sum is finite.
For the rational witness $1$ the exact allowances, in unnormalized
natural logarithms, are as follows. The finite rows use
$\log|z|_\ell=-v_\ell(z)\log\ell$.

| Place | $Y$ | $1/Y$ |
| --- | ---: | ---: |
| Real log absolute value of the object | $\sum_n a_n\log D_n-M\log q$ | $M\log q-\sum_n a_n\log D_n$ |
| Real log absolute value of the common witness | $0$ | $0$ |
| $\ell\mid c$ | $0$ | $0$ |
| $\ell\mid q$ | $M v_\ell(q)\log\ell$ | $-M v_\ell(q)\log\ell$ |
| $\ell\nmid cq$, base and higher levels together | $-J_\ell\log\ell$ | $J_\ell\log\ell$ |
| Witness real allowance plus all finite allowances | $-\log Y$ | $\log Y$ |

Unique factorization proves these are all the entries. A common nonzero
rational coefficient $u$ adds $\log|u|$ at infinity and
$-v_\ell(u)\log\ell$ at each finite place. Their sum is zero.
Consequently this exact table supplies neither independent half of the
desired signed height comparison.

Two groups of finite-place terms can be paid at the requested scale from
the arithmetic alone. First, the total absolute base charge at *every*
place of order $h\le c$, divided by $c$, is at most
$$
 \sum_{2\le h\le c}\bigl(|E(h/x)|+1/(2c)\bigr)\log D_h
 \ll_E \sum_{h\le c}(h/x+1/c)h\log(2c+1)
 \ll_E \sqrt{x}\log(2x).
$$
Here all prime divisors of base order $h$, with their actual valuations,
divide the same $D_h$ in aggregate. This includes arbitrarily large
primes. Second, for $\ell\le c$ all the higher levels at a fixed place
cost at most $(\|E\|_\infty+1)\log N$ after division by $c$.
For $\ell>x^{3/4}$, a higher level requires $j=1$ and
$h\le x^{1/4}$. Such primes at each $h$ divide $D_h$, so their
total higher-level charge is $O_E(\sum_{h\le x^{1/4}}\log D_h) =O_E(\sqrt{x}\log(2x))$. Primes dividing $q$ retain the separate
normalization row of the table. The still-exposed base levels have
$h>c$, and the remaining higher levels have $c<\ell\le x^{3/4}$
and $j=1$. All these entries keep their signs in the table.

### The ordinary absolute height of this particular rational

The positive numerator and denominator of the reduced $Y$ each have
logarithm $\gg_E cx^2\log x$ for all sufficiently large $x$.
This rules out paying a usual absolute rational height at the target scale.

To see this, set $B_+=\prod_{a_n>0}D_n^{a_n}$ and
$B_-=\prod_{a_n<0}D_n^{-a_n}$.
The residual has two fixed closed intervals of positive length in
$(0,1/6)$, on which it is respectively above $\delta$ and below
$-\delta$ for some $\delta>0$, by the strict values at
$1/10$ and $1/7$. There is also a proof independent of the numerical
enclosure for the calibration. Those two values, as affine functions of
$\eta$, have distinct roots $85/1008$ and $7/108$. Thus $E$ is nonzero,
and its calibrated integral is zero. Continuity then forces both open sign
intervals. Hence on those intervals
$|a_n|\ge c\delta/2$ eventually. For a fixed interval
$[u,v]\subset(0,1)$, the totient sum on $[ux,vx]$ is
$(v^2-u^2)x^2/(2\zeta(2))+O(x\log(2x))$. This follows by summing
$\varphi(n)=n\sum_{d\mid n}\mu(d)/d$ and replacing each floor by
its argument with error at most one. Since
$\log D_n=\varphi(n)\log q+O(\tau(n)\log q)$ and all $D_n\ge1$,
it follows that $\log B_+,\log B_-\gg_E cx^2\log x$.

At a given prime, the base valuation has just one sign, so cancellation
in $\gcd(B_+,B_-)$ is at most the total absolute higher-level
valuation. Each higher-level index $n=h\ell^j$ has $h\mid\ell-1$.
Its prime $\ell$ is uniquely the largest prime factor of $n$, and
its valuation in $D_n$ is one. The total common log divisor is thus at
most $(c\|E\|_\infty+1)\sum_{n\le N}\log n=O_E(cx\log x)$.
Every $D_n$ is coprime to $q$. Inserting $q^{-M}$ cannot cancel
any of the remaining numerator or denominator factors. This proves the
claim for both signs. The upstream signed, place-dependent
`HeightLe` has different allowances, as the last row of the table shows.

In fact the numerator and denominator already have this growth *at primes
larger than the entire original population*. Fix any $A\ge1$. At most
$\pi(Ax)=O_A(x/\log x)$ distinct base indices $h$ can occur at primes
$\ell\le Ax$, since each such prime has only one order. Discard those
indices from each of the two fixed sign intervals. Their total totient
mass is at most $O_A(x^2/\log x)$, leaving $\gg_E x^2$ in each interval.
At every remaining $n$ the only possible nonbase prime factor of $D_n$
is its largest prime factor and occurs to the first power. Its log
contribution is at most $\log N$. All other factors are at base primes
$\ell>Ax$, and each of these occurs in only one label $n\le N$. They
cannot cancel when $Y$ is reduced. Consequently
$$
 \frac1c\sum_{\ell>Ax} (v_\ell Y)_+\log\ell\gg_{E,A}x^2\log x,\qquad
 \frac1c\sum_{\ell>Ax} (-v_\ell Y)_+\log\ell\gg_{E,A}x^2\log x.
$$
This locates the large unsigned costs of *both* reciprocal certificates
outside any fixed multiple of the prime cutoff. It uses Chebyshev's upper
bound on the number of small primes and keeps the large base valuations
with their full multiplicities.

### An independently priced part of the normalization

The two adjacent integers $c,q$ give a useful second way to account for
the real scale, while retaining the exact finite ledger above. Put
$w_c(y)=\operatorname{round}(c E(y))/c$, $u=\log(q/c)$, and form the
positive rational
$$
 Z=\prod_{2\le n\le N}\left(\frac{D_n^2}{(cq)^{\varphi(n)}}\right)^{a_n}.
$$
Then $Y^2=r^M Z$ exactly. On the complete rounded population one has
$$
 \frac{\log Y}{c}
 =\frac{\log Z}{2c}
 -\frac{u x^2}{2\zeta(2)}\int_0^1 y w_c(y)\,dy
 +O_E(\sqrt{x}\log(2x)).
$$
In particular the large scalar in this identity has an independent real
reference to square-root accuracy. The integral uses the rounded profile
itself. Replacing $w_c$ there by $E$ by the pointwise rounding bound would
cost $O(x)$. At finite places the moved scalar still has exactly
$v_\ell(r^M)=M(v_\ell(c)-v_\ell(q))$.

Here are details of the uniform estimate for the discontinuous weight.
On a dyadic interval $1/(2K)\le y\le1/K$, $K=1,2,4,\ldots$, the source
estimate $|E'(y)|\ll 1/y$ gives $\operatorname{Var}E=O(1)$. The
calibrated $V$ is piecewise rational on a fixed finite partition, with
bounded degrees. Indeed the inverted ramps in its defining upper
profiles only evaluate arguments at least $1/8$. Up to $2K$ dilates
$V(dy)$ occur in $E$ on this interval, so there are $O(K)$ partition
points. On each piece the sum, including $1/y-1$, is a rational function
of degree $O(K)$ after clearing denominators. Its derivative has $O(K)$
zeros unless the piece is constant. This gives $O(K^2)$ monotonicity
intervals in all. On each, nearest-integer rounding is monotone and
increases the endpoint variation by at most $1/c$. Endpoint values and
any contacts at a tie are covered by splitting at the extrema. Hence
$$
 \operatorname{Var}w_c\ll_E 1+K^2/c.
$$
Because $E(y)=O(y)$, the rounded weight is identically zero for
$K>C_Ec$. On each remaining dyadic interval the totient summatory formula
above, including either convention at integer endpoints, bounds the
discrepancy from the measure $x^2y\,dy/\zeta(2)$ on every subinterval by
$O((x/K)\log(2x))$. Summation by parts against $w_c$ costs this discrepancy
times $O_E(1+K^2/c)$, including its supremum at the endpoints. This
estimate also applies to the actual values at the finitely many rounding
jumps, since the interval discrepancy bound covers singletons.
Summing over dyadic $K\le C_Ec$ uses
$\sum_K (K^{-1}+K/c)=O_E(1)$. Consequently
$$
 \frac{M}{c}=\frac{x^2}{\zeta(2)}\int_0^1 y w_c(y)\,dy+O_E(x\log(2x)).
$$
The omission of $n=1$ costs at most a bounded term. Multiplication by
$u\le 1/c$ gives the claimed price.

There is a corresponding signed estimate on the actual primitive Gram
matrices. For $n\ge2$ let $A_n=I-U_n$, $B_n=qI-cU_n$. In the counting
metric $B_n^*B_n=I+cq A_n^*A_n$, and $A_n$ is invertible. Define
$$
 L_n=\tfrac12\log\det\!\left(I+(cq)^{-1}(A_n^*A_n)^{-1}\right).
$$
The eigenvalues of the matrix inside the determinant are at least one.
Taking determinants gives
$L_n=\log F_n(r)-\Lambda(n)+u\varphi(n)/2$.
The real reference estimate from the admissions note gives
$\sum E(n/x)(\log F_n(r)-\Lambda(n))=R_E(x)+O_E(\sqrt{x}\log(2x))$.
Rounding this *difference* costs
$O((N(1+\log N)\log q+\psi(N))/c)=O(\sqrt{x}\log^2(2x))$.
It follows that the full signed curvature contribution obeys
$$
 \sum_{n=2}^N w_c(n/x)L_n
 =R_E(x)+\frac{u x^2}{2\zeta(2)}\int_0^1 y w_c(y)\,dy
 +O_E(\sqrt{x}\log^2(2x)).
$$
Both reference terms can be evaluated without the prime labels in the
unresolved band. The remaining term in $\log Z/(2c)$ is exactly
$\sum w_c(n/x)\Lambda(n)$. The curvature estimate prices one real
contribution of the original determinant and leaves the independent
lower bound for this last term outstanding.

## 8. Detection on the original star and its scope

For the determinant numerators on the served population there is an
original-rank calculation. At $\ell\nmid cq$, **at most one distinct original
prime label $p\ge\sqrt{x}$** can divide any exceptional index $n=pk\le N$.
Indeed the exceptional indices up to $N$ form a divisibility chain. Their
largest element, if present, is at most $N$ and is divisible by every
prime label appearing in the chain. Two distinct primes at least
$\sqrt{x}$ have product strictly greater than $x$. This covers the
endpoint $x=p^2$ and improves the $x^{3/4}$ cutoff used in the
archimedean expansion. At the primes dividing $cq$ all the $D_n$ are
units. It follows that the products of determinant numerators on distinct
original large-prime labels are **pairwise coprime globally**, even before
restricting to a site.

The explicit maps use distinct original labels at a site. For each
label $p$, multiply the factors $D_{pk}$ for positive and negative
multiplicities into two separate positive integers $B_{p,+},B_{p,-}$.
On $S=\{z\in\mathbb Z^s:\sum_i z_i=0\}$, use the two column maps
$z\mapsto(B_{p_i,\pm}z_i)_i$. The existing star uses the basis
$e_i-e_0$, so this has exactly $s-1$ columns per original row.
Both maps are injective in characteristic zero. At the above $\ell$,
choose a common omitted coordinate $b$ supporting the exceptional
label, or any coordinate if there is none. Deletion of $b$ on $S$
is a lattice isomorphism with inverse inserting
$z_b=-\sum_{i\ne b}z_i$. The selected minors of the two maps equal,
up to sign, $\prod_{i\ne b}B_{p_i,\pm}$, both local units. The
localized image has full original rank and saturation index one. At primes
dividing $cq$ all coordinate multipliers are units as well. Therefore the
maximal minors generate the unit ideal over $\mathbb Z$: the global image
of each numerator map is saturated, with quotient free of rank one in
$\mathbb Z^s$. Repeating each coordinate on a nonempty physical layer
preserves saturation by the integral retraction reading one copy. The
pairwise coprimality also supplies the precise input of the existing
[bounded dual on physical slots](NativeMeasuredSlotProjector.lean). Its
global size bound depends on the product of the multipliers.
No independence of the occurrences of rational primes enters this
calculation. The finite unit tests can read any one copy of a constant
amplitude from each nonempty physical layer. In unweighted Euclidean
coordinates deletion has norm at most one, and its inverse has norm at
most $\sqrt s$ by Cauchy-Schwarz. With layer sizes $m_i$, the exact
squared inverse norm for deletion in the counting metrics, for $s\ge2$,
is $1+m_b\sum_{i\ne b}m_i^{-1}$. For a vector $z$ on the retained
layers, the added squared norm is $m_b|\sum z_i|^2$, with equality
in the weighted Cauchy-Schwarz bound at $z_i=1/m_i$.
The integral diagonal multipliers have norm at most their largest entry.
They can be very large.

For the uniform primitive frequency experiment of §1 the probability of a
nonprimitive $p$-coordinate is $1/p$. For a separate experiment
choosing the omitted star coordinate uniformly when $s\ge1$,
if exactly one label has a nonunit for at least one of the two numerator
profiles, the probability that both selected minors are units is exactly
$1/s$. If there is no exceptional label it is one. Choosing the pivot
from the order tower makes this particular test succeed deterministically.
The large retained frequency weight alone does not estimate the probability
of success of the full common-coefficient and metric test.

### The two signs together on the original depth lattice

Restore the actual nonnegative depth exponents $e_{i,\sigma}$ on the
original labels $p_i$, where $\sigma=+,-$. They may differ for the two
profiles. Write $b_{i,\sigma}=p_i^{e_{i,\sigma}}B_{p_i,\sigma}$ and
$M_\sigma z=(b_{i,\sigma}z_i)_i$ on the same $S$. Let $I_\sigma$ be
the saturation index of its image. **At every finite place at least one
entire sign has a unit maximal minor.** In particular
$\gcd(I_+,I_-)=1$, and the map $z\mapsto(M_+z,M_-z)$ has globally
saturated image of rank $s-1$. Both measurements use disjoint actual
copies of each nonempty layer, which the slot bounds in §§3–4 provide.
Reading a representative of each constant layer is an integral retraction.
Concretely, once a layer has $n_i\ge2$ addresses, give each sign
$\lfloor n_i/2\rfloor$ disjoint addresses and leave at most one unused.
The full metric weight divided by the retained weight is at most three.
Thus on $s-1$ columns, returning either profile to its full counting
metric costs at most $(s-1)\log(3)/2$ in log covolume. The site-incidence
sum below prices even this absolute change at $O(\sqrt{x})$ after the
original normalization. The sharper signed comparison below applies to
either choice of counts directly.

Indeed only the coordinate with $p_i=\ell$ can carry a depth at $\ell$.
If there is no other exceptional label, deleting the potentially bad
coordinate gives a common unit minor. If there is a distinct exceptional
label $p_j$, the exceptional order $h$ must be divisible by $p_j$:
the exceptional index has the form $h\ell^t$. Since
$h\ell\ge p_j\ell>x$, **the only exceptional index in the entire
population is $h$** at this place. Its one exponent $a_h$ belongs to
only one sign. Deleting the depth coordinate on the other sign gives
a unit minor. More precisely the individual maximal minors are the
omit-one products of the $b_{i,\sigma}$. Thus in a collision
$$
 v_\ell(I_\sigma)=\min\{e_{i,\sigma},
             (\sigma a_h)_+\, v_\ell(D_h)\},\qquad p_i=\ell,
$$
using $\sigma=+1,-1$. Away from collisions both indices are units.
If there is no depth label at the site, delete the unique exceptional
label if present. At $\ell\mid cq$ all numerator factors are units.
The two indices are therefore coprime even for different nonnegative
depth profiles. The stacked map contains all minors of both individual
maps. Their gcd is one. For a collision with a positive depth on both
signs and $a_h\ne0$, choosing the sign and omitted coordinate independently
and uniformly succeeds with probability $1/(2s)$; selecting the good
sign and depth pivot deterministically succeeds. This probability counts
the finite set of actual minors, without any hypothesis on prime labels.

There is an independent real cost for combining the signs in this way.
Use one copy of each sign with the same metric weight on coordinate $i$.
Put $b_{i,\max}=\max(b_{i,+},b_{i,-})$. On the original $S$ the squared
counting norm of the stacked map lies between that of the diagonal
$b_{i,\max}$ map and twice that norm. This follows coordinatewise from
$b_{i,\max}^2\le b_{i,+}^2+b_{i,-}^2\le2b_{i,\max}^2$. Its log
covolume differs from the maximum-profile log covolume by a number in
$[0,(s-1)\log(2)/2]$, by the eigenvalues of the relative Gram on $S$.
Summing this charge on the actual $k$ active rows at each occupied site
and dividing by $ck|\mathcal T|$ costs at most $|P|\log(2)/(2c)$:
the existing incidence identity gives $\sum_{\rm sites}s=|P||\mathcal T|$.
This is $O(\sqrt x)$ even using $|P|\le x$. Repetitions of a prime
across sites have their actual multiplicities. The construction neither
adds independent columns nor assumes that both unstacked signs have
unit minors at the same place.

This prices the comparison with a maximum. Its difference from either
prescribed reciprocal profile still contains the positive part of their
logarithmic ratio.

### Clearing the full denominators on the same two physical stars

The $q$-normalization admits a joint integral map and an independently
bounded **signed** real change on the original star. For each distinct
served label $p\in P$ with $p\ge\sqrt x$, set
$$
 m_{p,\sigma}=\sum_{k\le x/p}(\sigma a_{pk})_+\varphi(pk),\qquad
 H_p=q^{\max(m_{p,+},m_{p,-})},\qquad
 u_{p,\sigma}=p^{e_{p,\sigma}} B_{p,\sigma}/q^{m_{p,\sigma}},
 \qquad L_p=\log(u_{p,+}/u_{p,-}).
$$
The $e_{p,\sigma}$ may be any of the original depth profiles satisfying
$0\le e_{p,\sigma}\le d_p\le cx/p$. On the two physical copies use the
integral entries $H_p u_{p,\sigma}$ on the **same** $s-1$ original
columns. At $\ell\nmid q$ the preceding local proof is unchanged. At
$\ell\mid q$ the determinant numerators are all units. Omit the unique
$p=\ell$ depth coordinate if present (otherwise omit any coordinate), and
at each retained coordinate take the sign with largest $m_{p,\sigma}$.
The resulting maximal minor is a unit. Thus the **fully cleared stacked
map has global saturation index one**. The domain has rank $s-1$, and
the quotient has free rank $s+1$ in the two representative copies.
For either individual sign at $\ell\mid q$ its exact saturation valuation
is $\sum_p t_{p,\sigma}-\max_p t_{p,\sigma}$, where
$$
 t_{p,\sigma}=v_\ell(q)\bigl(\max(m_{p,+},m_{p,-})-m_{p,\sigma}\bigr)
                 +\mathbf1_{p=\ell}e_{p,\sigma}.
$$
The formula is the gcd of the omit-one minors at that particular site.
The ambient diagonal clearing on both copies has index $\prod_p H_p^2$
in the two-copy integral coordinate lattice. Neither this index nor the
individual saturation valuations are declared to be zero.

For a single active row write $n_p>0$ for its physical layer counts and
$\mathscr L(b)$ for the log covolume in this metric of the columns
$b_i e_i-b_0 e_0$, $1\le i<s$. The exact omit-one Gram formula gives,
for the cleared rows,
$$
 \mathscr L(Hu_+)-\mathscr L(Hu_-)
 =\sum_p L_p+\tfrac12\log\sum_p \lambda_p e^{-2L_p},\qquad
 \lambda_p=\frac{(n_p H_p^2 u_{p,-}^2)^{-1}}
                   {\sum_j(n_j H_j^2 u_{j,-}^2)^{-1}}.
$$
The positive $\lambda_p$ sum to one. The last term is between
$-\max_p L_p$ and $-\min_p L_p$. The same interval applies before
clearing, so the change in the signed difference costs at most
$\max_p L_p-\min_p L_p$. This compares two independently measured
Gram determinants in their original counting metric. In particular the
large common real volume $\sum_p\log H_p$ is included on both sides
before subtracting.

The same conclusion holds for the **true-zero NNS covariance on these
columns**. Use any common positive physical anchor $v$ and positive
retained counts. The [anchored determinant identity](NATIVE_TRUE_ZERO_SCHUR_FIT_20261128.md)
gives $\det K_v(b)=(\prod n_i)(\sum_i v_i\prod_{j\ne i}b_j)^2/W_v$,
where $W_v=\sum_i n_i v_i^2$. Therefore its signed log covolume reads
$$
 \tfrac12\log\frac{\det K_v(Hu_+)}{\det K_v(Hu_-)}
 =\sum_p L_p+\log\sum_p\nu_p e^{-L_p},\qquad
 \nu_p=\frac{v_p/(H_pu_{p,-})}{\sum_i v_i/(H_iu_{i,-})}.
$$
The last term again belongs to $[-\max L_p,-\min L_p]$. This is an
actual positive probability on the omitted coordinates of the original
row. The formula retains the NNS first-moment correction in the Schur
determinant. It holds for a common place-dependent positive anchor as
well: one does not sum its real allowance over the finite primes.

An independent bound on that one complement per occupied site uses
$|a_n|\le c\|E\|_\infty+1/2$, the original depth capacities, and
$|\log F_{pk}|\le\tau(pk)\log q\le2\tau(k)\log q$. Consequently
$$
 |L_p|\ll_E c(x/p)(1+\log x)^2\le c\sqrt{x}(1+\log x)^2.
$$
Let $A_P=\{2\le n\le N:\exists p\in P,\ p\mid n\}$. Each such $n$
contains exactly one distinct served label, even at $x=p^2$. With
$W$ the occupied sites, let $\Delta$ be the sum of the cleared signed
log covolume differences (ordinary or true-zero, consistently) over the actual active rows, divided by
$ck|\mathcal T|$. The existing incidence identity now gives
$$
\left|\frac{\log Y}{c}-\left(
\Delta-\frac1c\sum_{p\in P}(e_{p,+}-e_{p,-})\log p
+\frac1c\sum_{n\notin A_P,\ 2\le n\le N}a_n\log F_n(r)
\right)\right|
\ll_E \frac{|W|}{|\mathcal T|}\sqrt{x}(1+\log x)^2.
$$
Indeed each row has exactly one complementary normal and each prime
has $|\mathcal T|$ partner incidences, each with $k$ active rows.
Under the existing density estimate $|W|/|\mathcal T|\le2x^{\varepsilon/8}$
this is within a square-root budget with a fixed positive epsilon
margin. It keeps the signed clearing term, the native depth correction,
and every complementary arithmetic label. It verifies the transport
cost. An independent lower estimate for the expression in parentheses
against $R_E(x)$ remains open. At primes of $q$ the unit selections can
use different signs on different coordinates; the unit minor for the
stacked family cannot serve as a prescribed-sign height bound on either
of the two individual sections.

In the pinned compact source, `heightLe_inv_ratio` uses the independently
bounded conjugates of a common coefficient $V$, tests detecting $V$
at each place after the forced loss, and a fitted rank-one congruence
bound for their pairings. `integral_forms_long` combines this with a
different estimate from almost-spanning independent rows of controlled
index and their measured untwisted covolume. The scalar table above
does not supply either the common detected coefficient on those rows or
its two independent bounds. The unresolved inequality is still
$c^{-1}\log Y\ge R_E(x)-C_\varepsilon x^{1/2+K\varepsilon}$
uniformly on the original complete windows.
[One-direction height comparison](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Rows/HeckeValueHeight.lean#L154-L215)
· [Covolume comparison](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Endgame/LongForms.lean#L33-L73)

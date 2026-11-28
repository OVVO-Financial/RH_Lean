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
with BigInt arithmetic and Bareiss elimination. These checks are not
asymptotic proofs. This note supplies paper proofs; no new Lean theorem
has been kernel-checked here. Retain the original alternating-exchange
benchmark and source notes; do not relabel them as terminal closure.

Finite checks executed in this session: {"frequencyOrders":1098,"orderTowerCases":40185,"higherTowerCases":40,"nonunitCases":357,"companionDeterminants":124,"rankCases":1860,"rankDefects":52,"unitRepairs":52,"physicalGramCases":744,"admissionCases":442}.

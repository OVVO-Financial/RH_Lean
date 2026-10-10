# Absolute-A signed estimate: exact audit and an all-scale restriction

Date: 2026-10-10. Source baseline: `86ef222e24c608bc2fe5757bda8f04ad96c7ec01`.

**The desired uniform upper estimate is still unproved.** This note adds an
independent finite census, a paper proof that even the restriction to R>=56
requires **A > 0.4357**, and a precise analysis of the external signed inputs.
The lower restriction uses Hurst's published unconditional theorem. It is not a
new Lean-kernel theorem, an RH proof, or a reason to reject the target with an
arbitrary larger finite A.

## 1. Exact existing object and quantifiers

Keep the repository's definitions:

\[
X_R=R^2-1,\qquad
K_R=\max_{0\le y<R}\frac{(M(y)-1)^2}{y+1}.
\]

The y=0 term already makes K_R >= 1. No additional 1 is added. In
`RHLean/Proof/SquareRootLegalAncestryGramReduction.lean`,
`LowerMertensCriticalEnvelope R K` quantifies over these same strict lower
arguments. The claimed theorem quantifies over every such K, hence includes
the least envelope above.

The already-proved identities are

\[
U_R+V_R=M(X_R)-1,\qquad \mathcal C_R=-U_RV_R.
\]

They identify the target

\[
(U_R+V_R)^2\le A R^2K_R
\]

with a true shifted Mertens endpoint estimate. Neither the parent-fibre
classification nor a sign reversal on an ancestry edge bounds the full
root-by-parent-by-child sum. This note does not introduce a new carrier or
assume that the covariance has the desired sign.

## 2. Recomputed finite census

`scripts/absolute_a_signed_estimate_audit.cpp` uses two independent integer
sieves: a linear sieve for every lower-envelope input and a segmented
prime-factor sieve for the full integer census. It compares their Möbius values
on the overlap. Each squarefree n>1 is classified once by q=P+(n), into q>n/q
(root U) or q<n/q (smooth V); equality would be squareful. It verifies
U+V=M-1 at every integer before sampling endpoints. Maxima are selected by
integer cross-multiplication, not rounded floating-point comparisons.

Through every R=56..10000, the maximum is

\[
\frac{(M(5561^2-1)-1)^2}{5561^2K_{5561}}
=\frac{12954050}{92774163}
=0.139629931234195\ldots.
\]

The witness has M=-2544, U=125204, V=-127749 and K=3/2. The all-integer
census through 99,999,999 has 30,397,311 positive, 30,395,383 negative and
39,207,305 zero Möbius values. Independently of endpoint sampling,

\[
\max_{0\le n<10^8}\frac{(M(n)-1)^2}{n+1}=\frac32,
\]

attained at n=5. This last finite check is the base of the induction below.

The old prose maximum 0.1291432502985845 over R<=100000 is incompatible with
this smaller-range witness under the stated normalization. The 100000-root
maximum is therefore uncertified; this audit does not claim to recompute that
larger range.

## 3. A fixed A is quantitatively stronger than the all-epsilon RH criterion

This is a consequence of the proposed estimate, not an independent upper
estimate. Put

\[
F(n)=\frac{|M(n)-1|}{\sqrt{n+1}},\qquad
B_j=2^{2^j},\qquad E_j=\max_{0\le n<B_j}F(n),\qquad \beta=\sqrt A.
\]

For n>=3, let R=floor(sqrt(n+1)), so R>=2. The interval from R^2-1 to n
has length at most 2R. All lower arguments y<R lie below B_j whenever
n<B_(j+1). After using the *hypothetical* endpoint estimate on the complete
signed Mertens state, the trivial interpolation gives

\[
F(n)\le\beta E_j+2.
\]

The few n<3 also obey that upper bound. Consequently

\[
E_{j+1}\le\beta E_j+2,\qquad E_0=1.
\]

Solving this deterministic recurrence gives:

| Proposed constant | Consequence for M(x) |
| --- | --- |
| 0<=A<1 | O(sqrt(x)) |
| A=1 | O(sqrt(x) log log x) |
| A>1 | O(sqrt(x) (log x)^(log(A)/(2 log 2))) |

The original all-R>=2 target is used here; finitely many excluded small roots
can instead be absorbed into a larger base constant. The all-epsilon Mertens
criterion follows, as already proved by the repository's terminal consumer.
At R=2 the full all-R target already forces A>=1: M(3)-1=-2 and the least
K_2=1. The A<1 row is relevant only when small roots are excluded. This is
distinct from section 4's new result that some *later* root exceeds 0.43.

The displayed bounds are sharper information about its sufficient premise.
They are not asserted unconditionally. In particular, an arbitrary fixed-A
claim cannot be extracted merely from a quoted M(x)=O_epsilon(x^(1/2+epsilon))
estimate without a separate control of constants and historical record growth.

## 4. New rigorous restriction: every valid uniform A exceeds 0.4357

This argument uses the exact least envelope, a once-only interpolation of the
actual Mertens state, the finite base in section 2, and Hurst's theorem. It does
not recycle historical parent charges or insert an independence assumption.

### 4.1 A uniform finite-wheel interval inequality

For P={2,3,5,7}, write

\[
\delta=\prod_{p\in P}(1-p^{-2})=\frac{768}{1225}<\frac{627}{1000}.
\]

For any two nonnegative integers a,b, inclusion-exclusion over the sixteen
square divisors d^2, d|210, bounds the number of integers in (min(a,b),max(a,b)]
avoiding these four prime squares by

\[
\delta|b-a|+16.
\]

Each floor difference differs from its length/d^2 by less than one. Möbius
values vanish at every excluded integer. Therefore, unconditionally,

\[
|M(b)-M(a)|\le\delta|b-a|+16. \tag{W}
\]

This is a bound on a genuine interval carrier. It does not transfer a global
squarefree density to an arbitrary selected owner population.

### 4.2 Strong induction including the full historical envelope

Suppose the absolute-A bound held for every R>=56 with A<=43/100 and every
admissible lower envelope. Set B=1837/1000.

We prove (M(n)-1)^2 <= B^2(n+1) for every n. The base n<10^8 holds by the
exact census: its maximum is 3/2 < B^2.

For n>=10^8, put z=sqrt(n+1) and choose the nearest integer s to z. Then

\[
|s-z|\le\tfrac12,\quad
|n-(s^2-1)|\le z+\tfrac14,\quad s< n,\quad s\ge10000.
\]

The strong-induction hypothesis applies to every y<s, not merely to one child.
Thus `LowerMertensCriticalEnvelope s (B^2)` holds. Apply the supposed theorem
at root s, even if that nearest square is later than n: its entire required
lower history lies strictly below n. It gives

\[
|M(s^2-1)-1|\le\sqrt{43/100}\,B s.
\]

Use (W) for the single remaining interval. Since z>=10000,

\[
F(n)\le\sqrt{43/100}\,B+\delta
+\frac{\sqrt{43/100}\,B/2+\delta/4+16}{z}.
\]

All constants can be checked rationally:

\[
\sqrt{43/100}<82/125=0.656,\quad
(82/125)B/2+\delta/4+16<17,
\]

so

\[
F(n)<(82/125)(1837/1000)+627/1000+17/10000
=1.833772<1.837=B.
\]

This closes the induction. The hypothetical estimate would force

\[
\limsup_{n\to\infty}\frac{|M(n)|}{\sqrt n}\le1.837.
\]

[Hurst, Theorem 6.1](https://arxiv.org/pdf/1610.08551) proves unconditionally
that liminf M(x)/sqrt(x) < -1.837625. The real/integer endpoints have the same
liminf because M(x)=M(floor(x)). The two conclusions contradict each other.

Hence the actual ratios satisfy

\[
\boxed{\text{some }R>10000\text{ has }
\frac{(M(R^2-1)-1)^2}{R^2K_R}>0.43.}
\]

In particular every universal amplification constant in the stated theorem
must exceed 0.43. No location for that future witness is claimed, and no
finite upper bound on all ratios has been proved. This does not refute an
absolute-A theorem with a larger constant.

### 4.3 Stronger six-prime, first-crossing restriction

The preceding argument establishes the 0.43 barrier by strong induction.
A direct first-crossing argument gives a strictly stronger barrier without
induction over every future Mertens value.

Take the six primes P={2,3,5,7,11,13}. By inclusion-exclusion over the 64
square-divisor products, the number of integers in an arbitrary integer
interval avoiding all p^2 with p in P is at most

\[
\delta_6 |b-a|+64,\qquad
\delta_6=\prod_{p\in P}(1-p^{-2})
=\frac{442368}{715715}=0.618078425071432\ldots.
\]

Indeed, for each divisor d of 30030, the corresponding interval count
floor(b/d^2)-floor(a/d^2) differs from |b-a|/d^2 by less than one
(after ordering the endpoints). Since mu vanishes at every excluded
integer, this gives the genuine uniform signed bound

\[
|M(b)-M(a)|\le \delta_6 |b-a|+64. \tag{W6}
\]

First set B=1837/1000 and F(n)=|M(n)-1|/sqrt(n+1). Hurst's strict
liminf theorem guarantees an integer n with F(n)>B; let n0 be the
*least* such integer. The verified all-integer base F(n)^2<=3/2
for n<10^8 implies n0>=10^8.

Put z=sqrt(n0+1) and let s be a nearest integer to z. Then

\[
z\ge10000,\quad |s-z|\le\tfrac12,\quad
|n_0-(s^2-1)|\le z+\tfrac14,\quad s\le z+\tfrac12.
\]

Crucially, every historical envelope argument y<s is **earlier than n0**,
even if s^2-1>n0. Minimality therefore gives

\[
K_s=\max_{0\le y<s}\frac{(M(y)-1)^2}{y+1}\le B^2.
\]

By the reverse triangle inequality and (W6),

\[
|M(s^2-1)-1|>
(B-\delta_6)z-\delta_6/4-64.
\]

All terms on the right are positive for z>=10000. Divide by
s sqrt(K_s) <= B(z+1/2) and use z>=10000 to get

\[
\frac{(M(s^2-1)-1)^2}{s^2K_s}>
\left(
\frac{B-\delta_6-(\delta_6/4+64)/10000}
     {B(1+1/20000)}
\right)^2
=0.4356183240438920487\ldots>0.4356.
\]

This alone proves the proposed >0.4356 strengthening. Moreover, since
Hurst proves the **strict** bound
liminf M(x)/sqrt(x)<-1.837625, we may take
B=14701/8000=1.837625 in precisely the same first-crossing argument.
The exact rational certificate then gives the still stronger value

\[
\left(
\frac{B-\delta_6-(\delta_6/4+64)/10000}
     {B(1+1/20000)}
\right)^2
=0.4357709546198786\ldots>0.4357.
\]

The exact census shows that all roots s<=10000, s>=56 have ratio
at most 0.139629931234195..., whereas s>=10000 above. Hence the
witness s must satisfy s>10000. Unconditionally,

\[
\boxed{\exists R>10000:\quad
\frac{(M(R^2-1)-1)^2}{R^2K_R}>0.4357.}
\]

By U_R+V_R=M(R^2-1)-1 and C_R=-U_R V_R, at that root

\[
2C_R<U_R^2+V_R^2-0.4357\,R^2K_R.
\]

Thus no proposed *universal* signed-return bound forcing every such
normalized residual <=0.4357 can be correct. This does not disprove
a fixed-A upper bound with a larger constant, and neither the Hurst
theorem nor this first-crossing proof has been imported into Lean.

### 4.4 Do not replace the historical maximum by a limsup

K_R contains *all* earlier values. A finite historical peak may exceed the
eventual limsup. Therefore the informal substitution
lim K_R=(limsup |M(n)|/sqrt(n))^2 is not justified. The induction in section
4.2 and first-crossing argument in section 4.3 avoid that error explicitly. In particular, this note does not claim the
tempting asymptotic constant (1-(6/pi^2)/1.837625)^2 as an unconditional lower
bound for A.

## 5. Independent all-scale signed inputs examined

### Reciprocal Möbius cancellation

[Tao (2009)](https://arxiv.org/abs/0908.4323) proves a uniform absolute bound 1
for reciprocal Möbius sums on arbitrary prime-generated multiplicative
semigroups, with coprime and divisor variants. The unrestricted reciprocal
bound is already compiled as `nativeMertensRecip_abs_le_one`. This is a real
independent signed estimate, but its 1/n weight is essential. Applying Abel
summation to a bounded reciprocal prefix supplies an O(x) bound on the
unweighted prefix. It does not give O(sqrt(x)) or an absolute-A endpoint
bound. Removing the reciprocal weight is an analytic obligation, not a
consequence of the sign reversal.

### OpenAI's principal sixth-power amplification

Checked primary source: OpenAI's September 30 manuscript,
[Lemma `inverse-amplification`](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex),
blob `268c4e3206d460c617d3d2129742a72b831b3def`.

On the principal U=1 row its normalized squared ideal sum is bounded by
D^(5/6+epsilon), hence its unnormalized ideal amplitude by
D^(11/12+epsilon), for the permitted fixed smooth tests and fixed arithmetic
data. Even a fully justified sharp rational transfer of that estimate would
leave endpoint energy of order R^(11/3+epsilon), above R^2 K_R. Its constants
depend on test seminorms; a moving sharp indicator cannot be inserted with a
uniform constant by assertion. The existing exact native coefficient welds
do not improve the exponent or prove that uniformity.

The manuscript's claimed 7/8 zero-free half-plane is also above the critical
1/2 line. Even granting the corresponding quantitative Mertens power bound
would leave endpoint energy R^(7/2+epsilon). It cannot be billed against a
small historical K merely because K has a separately known upper bound.

### What remains open

None of these inputs proves the requested global lower bound on the complete
cross-owner ledger. The new proof is an independent **restriction on the
constant**, not that lower bound. An actual closure still needs a signed
estimate on the sharp, complete physical state with uniform constants and its
original occurrence multiplicities. The numerical audit and the proof above
must not be presented as providing that missing upper estimate.

## 6. Verification and reproduction

```bash
g++ -O3 -std=c++17 -Wall -Wextra -Werror \
  scripts/absolute_a_signed_estimate_audit.cpp -o /tmp/absolute_a_audit
/tmp/absolute_a_audit 10000
python3 scripts/absolute_a_constant_certificate.py
```

The dedicated workflow repeats both checks. The finite base is exact integer
arithmetic and the small constant certificate is exact rational arithmetic.
The all-scale induction and external Hurst theorem are paper-level mathematics;
they have not been imported into Lean. No Lean theorem, assumption, terminal
criterion, or proof inventory is changed.

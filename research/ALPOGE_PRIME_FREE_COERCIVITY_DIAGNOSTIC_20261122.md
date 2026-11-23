# Prime-free diagnostic of the square-clock coercivity proposal

## Outcome and scope

The proposed diagnostic separates four mathematical claims which must not
be conflated:

1. The universal `l∞ -> l∞` norm of the order-`k` forward difference is exactly `2^k`,
   even on an integral sign sequence whose every even window has mean zero.
   Independent random signs retain exponential second moment as well.
2. The complete additive/floor commutator on an `L`-by-`L` rectangle
   telescopes exactly and is at most `2(L-1)` on any bounded sign sequence.
   This is a different observable from either the pointwise high jet or
   the original sum of the signs.
3. The actual upstream finite-dimensional commutator coercivity theorem
   does apply to an explicit prime-free two-dimensional example. Its sharp
   squared-norm constant is `4^k` when the matrix scale is `2^-k`. Existence
   of a coercivity constant alone therefore does not pay the exponential cost.
4. A Gaussian grid does not instantiate the original theta-cover, good-cover,
   common height/width or unramified-host hypotheses. The full proposed
   Signed Square-Lattice Coercivity Theorem remains a construction target.

Thus the prime-free high-difference test refutes automatic polynomial
absorption from boundedness and local balance. It does not refute a proved
geometric theorem, establish a hidden Euler-product premise, or prove RH.
The positive telescope identity is genuinely independent of prime
factorization, but still requires a source-faithful transfer to the desired
physical observable.

This note accompanies the continued actual construction in draft PR #1194.
The toy model is not substituted for the required arithmetic host.

## 1. What PR #1189 actually established

The exact declarations in
[`AlpogeSquareRootArithmeticMultiplicity.lean`](../RHLean/Analysis/AlpogeSquareRootArithmeticMultiplicity.lean)
and the extracted Mathlib-only
[`AlpogePrimeFreeForwardJet.lean`](../RHLean/Analysis/AlpogePrimeFreeForwardJet.lean)
are the source of this diagnostic. The extraction preserves the existing
generic declarations and their proofs byte-for-byte; the arithmetic file
imports that same operator:

- `alpogeNativeForwardJet` is the recursively defined forward difference.
- `alpogeNativeForwardJet_abs_le_exp` proves the universal `2^k` bound.
- `alpogeNativeForwardJet_alternating_abs` attains that bound exactly.
- `alpogeNativeAdditiveWheel_commutator` is a one-step additive/floor
  commutator, valid for arbitrary sequence values.
- `alpogeNativeAdditiveWheel_rectangular_telescope` sums that commutator
  on the whole rectangle, retaining its exact endpoint multiplier.
- The character/product defect retains the original multiplier variation;
  it is not eliminated by the forward-difference identity.

PR #1189 was merged with head
`83968d4dfdef6784cf52142a0b2528a39eee1b84`. Its record distinguishes the
sharp exponential jet cost from the missing geometric payment. The
remaining-obligation section in
[`ALPOGE_NATIVE_WIDTH_COST_20261122.md`](ALPOGE_NATIVE_WIDTH_COST_20261122.md)
also states that the central Signed Square-Lattice Coercivity Theorem is
not yet supplied. Existing selected-matrix lower coercivity is not an
upper response-energy estimate for the complete first-order source.

### The actual upstream coercivity theorem and an exact conditioning test

At the pinned original source commit
`7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`, the declaration
`GlobalTheory.T.commutator_coercive_on_annihilator` in
`src/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CommutatorCoerciveOnAnnihilatorStatement.lean`
has the following content. Given a complex square matrix `X` and vector
`v`, assume

\[
 [A,X]=0\ \land\ Av=0\quad\Longrightarrow\quad A=0.
\]

Then there is `c>0` such that, for every `A` with `Av=0`,

\[
 \operatorname{hs}(A)\le c\operatorname{hs}([A,X]).
\]

The supplying sibling `CommutatorCoerciveOnAnnihilator.lean` proves that
`hs` is the **square** of the Frobenius norm. Its proof applies
`LinearMap.exists_antilipschitzWith` to the injective map
`A -> ([A,X],Av)`. The constant may depend on `X,v`; this theorem
does not give a uniform bound as ranks or geometric parameters change.

Here is a prime-free example satisfying its full injectivity hypothesis:

\[
 v=\begin{pmatrix}1\\0\end{pmatrix},\qquad
 X_t=\begin{pmatrix}0&0\\t&0\end{pmatrix},\qquad t>0.
\]

Every `A` with `Av=0` has the form

\[
 A=\begin{pmatrix}0&a\\0&b\end{pmatrix},\qquad
 [A,X_t]=\begin{pmatrix}ta&0\\tb&-ta\end{pmatrix}.
\]

Consequently zero commutator forces `a=b=0`, establishing the actual
hypothesis. Moreover

\[
 \operatorname{hs}(A)=|a|^2+|b|^2,\qquad
 \operatorname{hs}([A,X_t])=t^2(2|a|^2+|b|^2).
\]

The **best** constant is exactly `c=t^-2`, with equality at
`A=diag(0,1)`. Taking `t=2^-k` gives `c=4^k`, or `2^k` in the
unsquared norm inequality. Even in fixed matrix dimension two and with
the standard Gaussian coordinate lattice, positivity and injectivity
do not imply a uniformly cheap coercivity constant. The cyclic pair
`(v,X_t v)` has determinant `t`, and the rational matrix entry has
denominator `2^k`; the degeneration is explicit in the height/volume ledger.

This is a successful test of the actual finite-dimensional theorem,
with an exponential cost exposed. It is not a counterexample to that
theorem and not a proof that the original geometric construction permits
these parameters within its admissible uniform budgets.

The Mathlib-only
[`AlpogePrimeFreeCommutatorConditioning.lean`](../RHLean/Analysis/AlpogePrimeFreeCommutatorConditioning.lean)
constructs these matrices and states the complete proofs as
`joint_injective`, `coercive`, `coercivity_constant_lower_bound` and
`exponential_constant_lower_bound` in
`RHLean.Analysis.NativeCommutatorConditioning`. The constant is derived,
not supplied as an estimate. These new proofs await exact-head hosted
kernel verification.

## 2. Separate the parameters and carriers

Use a side length `L`, derivative order `k`, and site count `N=L^2`.
The square clock is `X_L=L^2-1`. Only the stress-test specialization sets
`k=L`.

The square of Gaussian sites

\[
 Q_L=\{x+iy:0\le x,y<L\}
\]

has exactly `N` sites. The labeling `n=L*y+x` identifies site values with
an `N`-coordinate vector. Its unrestricted integral value lattice is
`Z^N`, of real rank `N` and standard covolume one; its mean-zero real
subspace has dimension `N-1`. These are not the real rank two of `Z[i]`.
The value-lattice dimension is also not the number `2^k` of labeled terms
in an uncollected expansion of a `k`-fold difference.

The disk `{x^2+y^2<=L^2}` has a different site count, and a finite disk is
not itself a lattice/submodule: it is not closed under addition. A radial
assignment `f(x^2+y^2)` repeats the same random variable at equal norms.
For independent signs indexed by the norms its raw variance would be
`sum_t multiplicity(t)^2`, not the site count. Direct site assignments
avoid this extra dependence in the first diagnostic.

The jet at `X_L` reads values through `X_L+k`. The experiment records this
explicit halo. It does not silently wrap the boundary or claim that the
entire stencil lies in the `N` original sites. For a matrix acting only on
those sites there are `N-k` interior jet rows when `k<N`.

## 3. An exact adverse control with optimal local balance

Let `a(n)=(-1)^n`. It uses neither primes nor multiplicativity. Every
consecutive window of even length has sum zero; every window of any
length has absolute sum at most one. Nevertheless

\[
 \Delta a(n)=-2a(n),\qquad
 \Delta^k a(n)=(-2)^k a(n),\qquad
 |\Delta^k a(n)|=2^k.
\]

This controls both hypotheses rather than merely sampling them: local
mean balance is exact, and the high-jet norm saturates the universal
bound. A restriction on window means alone cannot imply a polynomial
bound for the pointwise order-`k` difference.

The sign sequence also has strong deterministic correlations. If a
putative theorem assumes stronger covariance or Fourier conditions,
those conditions must be stated and checked; this control must not be
presented as satisfying them automatically.

## 4. Independent signs retain exponential jet energy

For independent uniform signs `xi_j`, put

\[
 c_j=(-1)^{k-j}\binom kj,\qquad
 J_k=\sum_{j=0}^k c_j\xi_j.
\]

The exact finite probability calculation is

\[
 \mathbb E J_k^2
 =\sum_{i,j}c_ic_j\mathbb E(\xi_i\xi_j)
 =\sum_{j=0}^k\binom kj^2
 =\binom{2k}{k}.
\]

The last identity counts a `k`-element subset of two disjoint `k`-element
sets by how many elements come from the first. It needs no analytic or
arithmetic input. In particular, since the central coefficient is the
largest of the `2k+1` coefficients whose sum is `4^k`,

\[
 \|J_k\|_{L^2}=\sqrt{\binom{2k}{k}}
 \ge\frac{2^k}{\sqrt{2k+1}}.
\]

This elementary bound already proves exponential growth, without an
asymptotic approximation. Stirling's formula sharpens the scale to
`2^k/(pi*k)^(1/4)`, but that approximation is not used by the diagnostic.

The random cross terms vanish in expectation. The diagonal binomial
energy still grows exponentially. Therefore a missing mechanism cannot
automatically be described as merely requiring the random cross terms to
vanish. They already do. Any normalization, projection, signed aggregate
or geometric compensation must be shown on the actual target quantity.

Overlapping output jets are not independent either. Their exact covariance
at a displacement `h`, for `0<=h<=k`, is

\[
 \mathbb E[J_k(n)J_k(n+h)]
 =(-1)^h\binom{2k}{k+h}.
\]

On the `N-k` interior rows, the expected sum of squared responses is
`(N-k)*binom(2k,k)`. This records the same coefficients and overlaps used
by the operator; it does not invent independent geometric channels.

In contrast, the original unweighted sum of `N=L^2` independent signs
has second moment `N`, hence root-mean-square `L`. That fact is fully
compatible with the exponential jet energy. Root cancellation of a
random raw sum is not evidence that geometry absorbed the jet cost.
Conditioning a random sample on simultaneous local-window events generally
changes independence and the covariance calculation; the conditioned law
requires its own proof.

## 5. An exact deterministic irrational-rotation sample

For `n>0` use

\[
 b(n)=\operatorname{sgn}\sin(\pi\sqrt2\,n^2)
     =(-1)^{\lfloor\sqrt2\,n^2\rfloor},
 \qquad b(0)=1.
\]

The script computes the integer part by `isqrt(2*n^4)`, so all signs are
exact. It makes no floating-point decision near a sine zero. The explicit
coprime witness `b(6)=1` but `b(2)b(3)=-1` proves nonmultiplicativity.

An irrational polynomial rotation supplies a useful model, but the word
"Diophantine" alone is not a quantitative short-window or correlation
bound. One must specify the irrationality constants, window ranges,
error exponents and derivative order. Polynomial phase values at shifted
indices are correlated; for the underlying complex quadratic phase,
the third multiplicative discrete derivative is exactly one. Taking
signs does not justify treating these values as independent signs.

The displayed finite computations are observations for this fixed model,
not a uniform discrepancy theorem or an asymptotic cancellation proof.

The script also retains a non-arithmetic density control,
`w(n)=1_{frac(sqrt(3)*n)<1/2}`, evaluated exactly by integer square roots.
It tests both `w(n)b(n)` and a masked seeded sign sample, records the actual
number of active sites, and computes the exact independent-sign weighted
jet variance `sum_j binom(k,j)^2*w(X_L+j)`. For general fixed weights that
formula uses `w^2`. This explicitly separates density from sign correlation.
The choice of one-half density is a toy parameter; matching the actual
prime-power support, logarithmic weights and full `Gz` source would require
an additional proved comparison.

## 6. What the complete signed telescope actually pays

Define, for any positive integer `p`,

\[
 Af(n)=f(n+1)-f(n),\qquad
 P_pf(n)=f(n)-f(\lfloor n/p\rfloor).
\]

No primality or multiplicativity is needed for the identity

\[
 [A,P_p]f(n)
 =f(\lfloor n/p\rfloor+1)-f(\lfloor(n+1)/p\rfloor).
\]

At `n=pm+r`, the first `p-1` residues give `f(m+1)-f(m)`;
the crossing residue gives zero. Summing the entire rectangle gives

\[
 \sum_{m<M}\sum_{r<p}[A,P_p]f(pm+r)
 =(p-1)(f(M)-f(0)).
\]

For `p=M=L` and `|f|<=1`, this is at most `2(L-1)` in absolute value.
This is the requested prime-free positive control for the existing signed
telescope. It is a one-commutator rectangle, not the order-`L` forward
difference. It also does not bound `sum_{n<N}f(n)`: the constant signal
has zero commutator and zero positive-order jets while its raw sum is `N`.
Any coercivity argument must specify the relevant subspace and the exact
map from its response to the physical target, including null modes.

## 7. The full cost and hypothesis ledger

The numerical section-cost theorem in
[`NativeSectionCostAbsorption.lean`](../RHLean/Geometry/NativeSectionCostAbsorption.lean)
retains

\[
 C_{\rm sec}
 =2[K:\mathbb Q]r\,|H|^2\,\beta
   \max\{1,[K:\mathbb Q]^4r\operatorname{rd}(K)A\}.
\]

It bounds this expression by `exp(C*z^9)` after proving or receiving
the original separate degree, discriminant, rank, theta-span, comparison
and group-size scales. It does not contain a universal identity canceling
`2^k`. To charge a `k`-difference to `A` or `beta` requires proving that
this is the actual geometric operation and that the resulting scales fit
the same downstream height/width budget.

Dividing a jet by `2^k` changes the integer data. Its first and last
coefficients have absolute value one before division, so the reduced
coefficient denominator is exactly `2^k`. Scaling an entire `m`-coordinate
image lattice by `2^-k` scales its covolume by `2^(-km)` in a fixed
Euclidean metric. This is a ledger entry, not by itself a no-go theorem:
the same metric, lattice, determinant and inverse/trace comparison must
be followed through the geometric construction. No cost may disappear
just because a normalized operator has a smaller norm.

| Requirement | What the Gaussian diagnostic supplies | What remains to prove |
| --- | --- | --- |
| Underlying lattice | Standard `Z[i]^n` can supply an integral, finitely generated, Hermitian-self-dual module | Identification with the actual geometric `W_j` lattices and common rank/signature datum |
| Host | An elementary CM field with conjugation | The original host requires relative unramifiedness; `Q(i)/Q` ramifies at 2, and the original prime congruence fields differ |
| Harmonic span | The native abstract Hermitian-lattice theorem can be specialized once its actual embeddings and lattice hypotheses are established | Evaluation as theta sections, canonical connection, component span and density |
| Costs | Exact site count, binomial coefficient norm and any declared normalization | Actual cover field `K`, component rank, group cardinality, theta norm and Petersson comparison |
| Coercivity | Explicit finite matrices can be formed | A quantitative lower bound on the appropriate subspace with all parameter dependence |
| Signed response | Exact generic rectangle telescope | The complete character/width-corrected source identity and upper response-energy estimate |
| Final window | A different model sequence | The same arithmetic `Gz`, `IdentU`, `SizeData₂`, strong `ErrWindows`, `BNBoundsU`, `LargeX` and literal physical top-excess payment |

The Eisenstein integers have the analogous ramification issue at 3.
Removing a failed host hypothesis changes the theorem being tested unless
a separate specialization or generalization is proved. Gaussian toy
failure therefore cannot establish that the original theorem secretly
uses the zeta function.

## 8. Exact reproducible results

Run only the Python diagnostic locally:

```text
python3 scripts/alpoge_prime_free_coercivity_diagnostic.py --output research/data/alpoge_prime_free_coercivity_diagnostic_20261122.json
```

It exhausts every sign assignment for `k=1,...,10` and checks the
recursive jet against its binomial expansion, the exact maximum and the
exact finite second moment. It checks the covariance identity at
`k=1,2,4,8`, and the full commutator rectangles for six models on five
square sizes. It also checks the exact two-by-two coercivity witness and
its sharp cost at six rational scales; the general complex-coordinate
proof is given above. The data are in
[`alpoge_prime_free_coercivity_diagnostic_20261122.json`](data/alpoge_prime_free_coercivity_diagnostic_20261122.json).

| `L=k` | Sites `N` | Alternating raw sum | Alternating jet magnitude | Independent-sign jet RMS, rounded |
| ---: | ---: | ---: | ---: | ---: |
| 4 | 16 | 0 | 16 | 8.37 |
| 8 | 64 | 0 | 256 | 113.45 |
| 16 | 256 | 0 | 65,536 | 24,516.94 |
| 32 | 1,024 | 0 | 4,294,967,296 | 1.354e9 |
| 64 | 4,096 | 0 | 18,446,744,073,709,551,616 | 4.894e18 |

For the exact `sqrt(2)` rotation at `L=k=32`, the raw sum is `-28`
while the pointwise jet magnitude is `758,560,944`. At `L=k=64`,
they are `-62` and `3,723,478,184,864,557,590`. These finite outcomes
illustrate why the target observable must be kept explicit. They do not
extrapolate to an asymptotic bound.

## 9. Correct acceptance criteria for the geometric test

A meaningful full test has three possible statuses, rather than an
unqualified binary verdict:

- **Instantiated and proved:** every hypothesis holds for one constructed
  family, and the complete response-to-target inequality has a cost ratio
  yielding the asserted bound uniformly in the stated scales.
- **Instantiated and contradicted:** every hypothesis holds but the actual
  conclusion fails, giving a counterexample to that theorem statement.
- **Not instantiated:** a host, lattice, spectrum, theta-density, source
  identity or window hypothesis is missing. This locates a construction
  obligation but is not a counterexample.

For example, if the intended argument is
`c(L,k)*|T_L(f)|^2 <= E(L,k,f) <= B(L,k)`, the required conclusion
follows only after a proved estimate for `B(L,k)/c(L,k)` with every
normalization, diagonal, cross term, width and covolume charged. This
formula is an interface specification, not a new assumed Lean axiom or
a replacement for the source-faithful proof.

The present high-jet polynomial claim has an exact adverse control; the
generic signed telescope passes its own identity and linear-bound test;
the full geometric coercivity application remains **not instantiated**.
The next work on #1194 continues to construct the actual common geometric
datum and its response comparison. Success on a prime-free toy would
prove a theorem about that toy. An RH consequence additionally requires
the separately verified transfer to the literal arithmetic source.

## Verification status

The exact Python diagnostic has passed. Its assertions are reproducible
finite checks, not a Lean kernel verification or a proof of an asymptotic
statement. The new prime-free extraction and local-balance Lean lemmas
require their exact published-head hosted Lean audit. No local Lean/Lake
execution is permitted or was used. The original #1189 sharpness and
generic commutator theorems retain their source provenance; moving their
declarations does not waive recompilation of the new import graph.

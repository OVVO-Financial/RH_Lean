# Signed-lift diagnostics and negative control

These are finite computations, not a uniform amplification theorem or Lean
numerical certificates. The companion Lean modules certify the identities
independently of these data. The optimized loops are not individually verified
machine code.

## Reproduction

Full experiment (Python 3, numpy and numba installed):

```sh
python experiments/mertens_signed_lift/diagnostics.py
```

This sieves genuine mu through 4,000,000 and separately evaluates quadratic
and higher-order prefix convolution formulas. Each predictor uses only the
specified shorter prefix. The future sieve is used for independent comparison.
The committed JSON retains the exact integer fields; the full runner also
writes floating-point display fields. Its fixed test sizes keep the integer
accumulators within int64. Enlarging those sizes requires an overflow audit.

Independent standard-library checks, with arbitrary-precision integers:

```sh
python experiments/mertens_signed_lift/verify_small.py
```

This uses a different linear sieve, verifies all quadratic budgets through
N=1000, higher-order component sums through X=27000, and 100 sparse-control
cutoffs. It intentionally does not claim to recheck the larger higher-order
cases or the N=2000 row. Both programs passed during the direct research run.

## What the comparison measures

For X=N^2, rows are R_i=sum_(j<=N)mu(j)floor(X/(ij)). The actual form is
Q=sum_(i<=N)mu(i)R_i. Compare sum_(i,j)|mu(i)mu(j)|floor(X/(ij)), then
sum_i |mu(i)R_i|, then |Q|. Every layer retains more cancellation. This
comparison does not prove that every possible use of Cauchy-Schwarz fails.

Higher-order components are the signed binomial terms
(-1)^(j-1) choose(k,j) sum_(n<=X)(a^j*1vec^(j-1))(n).
The entire combination is checked against the genuine Mertens sum.

## Scalar-prefix-only obstruction (paper proof plus finite checks)

Let a(1)=1, a(2)=-1 and a(n)=0 otherwise. All prefix sums have magnitude at
most one. The only coefficients of a*a are 1 at 1, -2 at 2 and 1 at 4.
Consequently, for X>=2,

sum_(n<=X) T(a)(n) = -X + 2*floor(X/2) - floor(X/4).

At X=4t this is -t. Padding this sequence by zeros gives arbitrarily long
inputs with critical prefix norm one but linear-size lifted sums. Hence no
scale-uniform square-root amplification theorem can rely only on bounded
coefficients and scalar prefix sums for arbitrary inputs.

This is NOT a counterexample to a proposed theorem that uses agreement with
genuine mu throughout the entire input range: the control agrees only through
2. Its role is to locate information that a valid arithmetic invariant must
retain. The exact inverse relation and genuine factor structure cannot be
replaced by a scalar norm certificate alone.

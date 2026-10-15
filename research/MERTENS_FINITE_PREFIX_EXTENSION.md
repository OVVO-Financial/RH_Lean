# Finite Mertens computation plus a proved extension rule

Date: 2026-10-15. User-directed attack, based on main 5a0cb83307f6f43ef6fa08d441362e384b8d4f1b.

## Scope

An exact arithmetic lift and a finite interval certificate are implemented. The lift is NOT a proved invariant of a sublinear Mertens envelope. No RH, all-scale 0.51 envelope, or uniform amplification theorem is asserted. The existing canonical VF and finite-A/C targets remain unchanged.

## Exact Newton lift

Work in the Dirichlet convolution ring of integer arithmetic functions. Let zetaInt be 1 at positive integers and 0 at zero; the convolution unit is delta. Mobius satisfies mu*zetaInt=delta. Define

```
T(a) = 2*a - a*a*zetaInt
D(a) = delta - a*zetaInt
```

Then, exactly,

```
D(T(a)) = D(a)*D(a)
T(a) = mu - (mu-a)*(mu-a)*zetaInt.
```

If a agrees with mu at every n<B, the last error is supported at n>=B^2. Thus the lift agrees with the genuine mu at every n<B^2. Starting at a_0=delta gives correct coefficients below 2^(2^j) at iteration j. This is an unconditional finite-to-finite reconstruction rule at arbitrary scales; the coefficients are not guessed or fitted.

For the zero-extended prefix a_N, the corresponding paper-level summatory formula is

```
M(x) = 2*M(N) - sum_{i,j<=N} mu(i)*mu(j)*floor(x/(i*j)),
N <= x < (N+1)^2.
```

This summatory formula is a familiar short-Mobius identity, not a new identity claimed by this work; compare Huxley-Watt, arXiv:1807.05890, and the repository's EULER_PRODUCT_SQUARE_ROOT_FINITE_C_A.md. The Lean implementation proves the coefficient-convolution lift and its original Mertens summation bridge. The C++ floor-kernel implementation is checked independently; a separate Lean reindexing of its optimized C++ double loop is not claimed.

## A checked finite margin extends the bound

For C>=0 and sigma>=0, an exact anchor obtained from the lift at L<B^2 satisfies

```
|M(L)| + (U-L) <= C*L^sigma
    => |M(x)| <= C*x^sigma for every L<=x<=U.
```

The proof uses the existing genuine bound |M(x)-M(L)|<=x-L, followed by monotonicity of x^sigma. No future Mertens envelope is an assumption. The margin is finite, explicit, and computable from the seed. The target interval may even extend past B^2 if the margin allows it.

For rational sigma=p/q, the experiment uses the integer b=floor(L^(p/q)), verified by b^q<=L^p<(b+1)^q, and U=L+b-|M(L)|. All accepted comparisons are exact integer comparisons. The next interval starts at U+1.

## Actual experiments

The standalone prefix predictor sieves mu only through 1000, then certifies all 1,001,000 new integers from 1001 through 1,002,000:

| Unit exponent | Anchors | New integers certified |
| --- | ---: | ---: |
| 9/20 | 5167 | 1001000 |
| 51/100 | 1981 | 1001000 |

An independent full sieve verified every anchor and every exact guard. A separate coefficient-convolution experiment reconstructed every coefficient through 1,002,000 from the same seed, with zero mismatches. At 1001^2 the uncorrected truncated lift differs from the genuine coefficient: predicted -1, actual 0. The strict cutoff matters.

A larger independent full census through 100,000,000 finds the FIRST unit-cone violation at exponent 9/20 at n=30,770,121, with M(n)=-2343; M(30,770,120)=-2342. Both values were reconstructed separately using only the Mobius prefix through 5547. The exact sign tests are abs(M(n))^20-n^9. This falsifies indefinite preservation of the earlier unit 0.45 envelope, not preservation of every possible 0.51 envelope. There were no unit 0.49 or 0.51 crossings in that census; this is finite evidence only.

## First attempted global invariant: absolute residual contraction fails

For every prime p>N and N>=1,

```
D(a_N)(p) = -1.
```

This coefficient identity is part of the Lean target. Consequently an absolute weighted l1 contraction using sum abs(D(a_N)(n))/n^sigma cannot hold for sigma<=1: it already dominates the divergent sum over reciprocal primes. This last divergence conclusion is a mathematical deduction, not a Lean summability theorem in this PR. It rejects this absolute norm only, not all signed norms or finite-state certificates.

## Remaining independent estimate

The exact Newton error identity contracts SUPPORT, not automatically an amplitude norm. For global collapse we still need a finite certificate that is preserved by the lift, or an independently proved useful bound on the full signed quadratic floor kernel. Finite anchor success is not a proof of preservation at every future scale.

A bounded amplification rather than a contraction would suffice under square-growing scales: if normalized critical prefix norms E_j obey E_(j+1)<=K*E_j for a fixed K>=1, then E_j<=E_0*K^j and the Mertens loss is polylogarithmic because the cutoffs are 2^(2^j). The estimate on E_j is UNPROVED and related to the already existing finite-A/C route and SquareRootAmplificationClosure.lean. It is not a new independent assumption that may be silently supplied.

## Verification levels

The general exact lift, finite guard and prime residual are to be checked by warning-fatal GitHub Actions Lean compilation and exact axiom audit. The C++/Python computations are separate executable finite checks, not Lean kernel-certified numerical data. No local Lean execution, theorem weakening, new axioms, merge or auto-merge.

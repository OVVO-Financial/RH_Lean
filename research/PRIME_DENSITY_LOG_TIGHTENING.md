# Density logarithmic tightening

Dependency: verified #803 head `67aa49064362416b22d9d10cb52e3a1b89cbb688`.
This is a stacked extension, not a replacement or modification of that branch.
The dedicated workflow checks all three modules with Lean 4.24.0 and warnings
fatal. Final compiler and named-theorem axiom results, not this pre-run note,
determine certification.

## Modules and quantifiers

- `PRIME_DENSITY_LOG_TIGHTENING.lean`: actual harmonic tails, signed cofactor
  reassembly, reciprocal Mobius cancellation, equal-density energy, error
  constant, and a conditional signed-energy coefficient budget.
- `PRIME_DENSITY_PNT_LOG_BOUND.lean`: nonnegative decreasing exact Li singleton
  masses and a finite Abel invariant transferring the unit-tail saving.
- `PRIME_DENSITY_INTEGRAL_TIGHTENING.lean`: the varying-density reciprocal
  integral, its log-log primitive, and the universal log(2) amplitude constant.

All model definitions are inherited unchanged from #803 and the library.
For natural y >= 2 and x <= y^2, the combined model energy bounds are

```
|T_equal(y,x)|^2 <= min(x^2, 4x^2/(log y)^2),
|T_Li(y,x)|^2 <= min((log 2)^2 x^2, 16x^2/(log y)^2).
```

Thus both models have O(R^4/(log R)^2) energy at x=R^2-1, y=R,
while the minimum preserves better small-root constants.

## Tail-sensitive constants

Keep the actual harmonic interval (y,x]. Its reciprocal mass is at most
log(x/y) <= log y when y <= x; when x < y, the interval is empty.
This bounds both model amplitudes by x rather than 4x.

For Li weights retain their variation inside the original unit intervals:

```
sum_{y<q<=x} (L(q)-L(q-1))/q
  <= integral_y^x dt/(t log t)
  = log(log x)-log(log y) <= log 2.
```

Therefore |T_Li| <= x log 2. No endpoint or floor is changed.

## Signed reciprocal improvement

The unit-density transport has the exact cofactor formula

```
U(y,x) = sum_{1 <= m <= floor(x/(y+1))} mu(m) (floor(x/m)-y).
```

Writing it as x times the reciprocal Mobius partial sum minus the floor/cutoff
remainder gives |U(y,x)| <= 2x for EVERY y,x. The proof uses the existing
`nativeMertensRecip_abs_le_one`; it assumes neither independence nor a PNT
remainder estimate. The remainder costs at most
(y+1) floor(x/(y+1)) <= x. Hence |T_equal| <= 2x/log y.

The Li singleton weights are nonnegative and decreasing. The discrete Abel
invariant retains the terminal term and transfers the uniform signed unit-tail
bound to |T_Li| <= 4x/log y for all x and y>=2. This coefficient 4 is deliberately
looser than the earlier proposed continuous-curvature candidate
(2x+y-1)/log y on the production clock. The latter is NOT claimed by these
modules. The fully discrete route avoids importing an unproved curvature or
floor-replacement estimate; the growth-rate saving is unchanged.

## Exact substitution error

Above sqrt(x), the reassembled actual prime tail remains bounded by x.
The exact error remains T_prime-T_Li. Consequently

```
|error| <= (1+log 2)x,
|error| <= x+4x/log y.
```

These may be combined by taking their minimum. The leading x term is not
removed: this is NOT a logarithmic-order improvement for the true error as a
whole. A direct signed prime-distribution-error theorem remains separate.

## Signed-energy interface

The general Young transfer keeps the diagonal and exposes every ordinary
hypothesis. From

```
a^2-D <= b E + Cb L,
e^2 <= d E + Ce L,
D <= 3L,
theta > 0,
```

it obtains

```
(a-e)^2-D <= ((1+theta)b+(1+1/theta)d) E
             + ((1+theta)Cb+(1+1/theta)Ce+3theta) L.
```

At b=1, d=1/4, theta=1/2 the coefficient is exactly 9/4 and the
boundary constant is (3/2)Cb+3Ce+3/2. This is conditional algebra; the
arithmetic model/error premises are not asserted. It neither identifies an
individual transport with the full assembled model amplitude nor proves the
open FinalStokes/RH estimate.

## Preservation and verification

The old baseline declarations, all counterexamples, main contract, exports,
and terminal consumers are unchanged. Both canonical historical ledgers were
appended before validation in commit 13a573a1f62c31418ff7b0372e85646ef6f116cf.
The one-time branch-only append step has been removed; CI now has read-only
contents permission and checks out the exact PR head. No PR is merged.

Compiler and axiom logs are retained. The strict named-theorem audit admits
only propext, Classical.choice, and Quot.sound. Applicable source, export and
documentation checks must also pass on the final head. No local Lean toolchain
was available; hosted compilation is the gate.

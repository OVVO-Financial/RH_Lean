# Density logarithmic tightening

Dependency: verified #803 head `67aa49064362416b22d9d10cb52e3a1b89cbb688`.
This is a stacked extension, not a replacement or modification of that branch.
The dedicated workflow checks the source with Lean 4.24.0 and warnings fatal.
Final compiler and named-theorem axiom results, not this pre-run note, determine
which declarations are certified.

## Models and quantifiers

All model definitions are inherited unchanged from #803 and the library.
For integers y >= 2 and x <= y^2, retain the actual harmonic interval (y,x].
It has reciprocal mass at most log(x/y) <= log y when y <= x; when x < y,
the interval is empty. Thus both equal and Li-density model amplitudes are at
most x, improving the previous 4x. Above sqrt(x), the true prime tail remains
bounded by x, so the exact prime-minus-Li error is at most 2x rather than 5x.

The signed unit-density transport has the exact cofactor formula

```
U(y,x) = sum_{1 <= m <= floor(x/(y+1))} mu(m) (floor(x/m)-y).
```

Writing the right side as x times the reciprocal Mobius partial sum minus its
floor/cutoff remainder gives |U(y,x)| <= 2x for EVERY y,x. The proof uses the
existing `nativeMertensRecip_abs_le_one`; it does not assume independence,
local balance, or a prime-distribution error estimate. The remainder has total
absolute mass at most (y+1) floor(x/(y+1)) <= x.

Consequently the equal-density model satisfies

```
|T_equal(y,x)| <= 2x/log y,
|T_equal(y,x)|^2 <= min(x^2, 4x^2/(log y)^2).
```

The Li model retains the exact integer singleton masses L(q)-L(q-1).
A separate monotone-density transfer will preserve signed unit-tail cancellation;
no continuous-floor replacement or unproved curvature claim is used implicitly.

## Signed-energy interface

The general Young transfer keeps the physical diagonal and exposes every
ordinary hypothesis. From

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

This is a conditional coefficient-budget lemma. It does not assert its
arithmetic premises, identify transport with the full model amplitude, or
prove the open FinalStokes/RH estimate. Improved model bounds remain distinct
from a root-scale bound on their interaction with the actual smooth sector.

## Preservation and verification

The old baseline declarations, all counterexamples, main contract, exports,
and terminal consumers are unchanged. A one-time branch-guarded workflow step
appends entries to both canonical historical ledgers before compiling; it never
writes to main and does not merge any PR. Compiler and axiom logs are retained.
The named axiom audit admits only propext, Classical.choice, and Quot.sound.
Local Lean is unavailable in this container, so hosted compilation is the gate.

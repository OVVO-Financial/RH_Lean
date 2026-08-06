# Decision memo: square-prefix bounded-width q-fibre locality

The exact cross-scale diagnostic concerns the dyadic largest-prime `q`-fibres inside
the **square-prefix Mertens representation**. Each squarefree integer `m` is placed in
square block `n = floor(sqrt(m))` and in scale
`k = floor(log_2 P+(m))`.

It shows that the square-prefix top prime boundary has visible nearby compensators,
principally at offsets `-2` and `-3`, but the cancellation is not stably localized in
a bounded neighborhood of largest-prime scales.

This memo does **not** address the primorial prime-wheel blocks, their torus Fourier
modes, their reduced additive conductors, or the prime-wheel harmonic
nonconcentration statement.

The continue criterion was: a fixed or slowly growing width captures the
square-prefix cancellation with small signed tail variation, supports a
data-independent block geometry, has controlled diagonal inflation, and survives
`H=1`.

The stop criterion fired:

- signed tail total variation at width five remains comparable to the full required
  global square-prefix cancellation and exceeds one half of the full top-row
  cancellation at `N=5000`;
- stable convergence to the full cancellation requires widths 15 to 17 on only 21 to
  26 live largest-prime scales;
- contiguous largest-prime-scale blocks of widths two through eight have large and
  growing block inflation even after fitting the phase;
- the best phase changes with `N` and `H`;
- the same failures occur at `H=1`.

Therefore the natural bounded-width largest-prime-scale block route is closed **for
the square-prefix representation tested here**. The square-prefix `q`-fibre layer
remains an exact audit layer and a mandatory gatekeeper for future square-prefix
signed mechanisms.

No conclusion about the primorial prime-wheel route follows. That route remains open
and should be tested separately using the actual primorial-wheel spectral-prefix atoms
or reduced-conductor components, with every cross-conductor Gram term retained.

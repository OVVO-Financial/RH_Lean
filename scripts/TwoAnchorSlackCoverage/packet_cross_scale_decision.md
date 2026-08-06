# Decision memo: bounded-width q-fibre locality

The exact cross-scale diagnostic shows that the top prime boundary has visible nearby
compensators, principally at offsets `-2` and `-3`, but the cancellation is not
stably localized in a bounded neighborhood.

The continue criterion was: a fixed or slowly growing width captures the cancellation
with small signed tail variation, supports a data-independent block geometry, has
controlled diagonal inflation, and survives `H=1`.

The stop criterion fired:

- signed tail total variation at width five remains comparable to the full required
  global cancellation and exceeds one half of the full top-row cancellation at
  `N=5000`;
- stable convergence to the full cancellation requires widths 15 to 17 on only 21 to
  26 live scales;
- contiguous blocks of widths two through eight have large and growing block
  inflation even after fitting the phase;
- the best phase changes with `N` and `H`;
- the same failures occur at `H=1`.

Therefore the natural bounded-width q-block route is closed. The q-fibre layer remains
an exact audit layer and a mandatory gatekeeper for any future signed mechanism. The
primary proof search should move to coordinates whose atoms already encode
cancellation, such as chain-impulse Fourier packets or the two-anchor centered
residual.

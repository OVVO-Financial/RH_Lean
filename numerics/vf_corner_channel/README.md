# VF corner-channel diagnostic

This directory reproduces the finite diagnostics for the construction formalized in
`research/VF_MID_CORNER_CHANNEL.lean`.

The literal channel linearly connects the adjacent VF staircase corners.  The widened
channel uses the canonical genuine-corner index offset

```
L_R(A) = min(R // 2, floor(A * log(R)^2)).
```

The scale is deliberate: one local VF band has mass of order `R/log R`, so
`O(log(R)^2)` neighboring VF bands produce `O(R log R)` total vertical room.

## Default finite scan

Run:

```bash
python numerics/vf_corner_channel/run_channel.py
```

The default scan uses `R = 56,...,10000`, hence square endpoints through
`x = 100,000,000`, and `A = 0.125`.

The pathwise test respects the repository's real-cutoff staircase
`pi_floor(x) = pi(floor x)`.  Upper violations need only be tested immediately
after prime jumps.  Lower violations are tested in the left limit before each
prime jump and at square endpoints.

The generated JSON is a **finite diagnostic only**.  It is not imported by Lean and
is never a premise of the symbolic channel theorems.

At the recorded default extent, the literal adjacent-corner channel has 20 pathwise
misses for `R >= 56`; the last is at `R = 680`.  The canonical widened channel
with `A = 0.125` has zero pathwise misses through `R = 10000`.

For endpoint inclusion alone, the largest observed minimal normalized index offset

```
required_offset / log(R)^2
```

is approximately `0.0743246541`, at `R = 179`, where two backward-index VF blocks and zero forward-index blocks are needed.

These observations motivate the deterministic inclusion target.  They do not imply
the missing uniform arithmetic theorem.

Terminology note: **lag/advanced** is reserved for the geometric phase chains
(upper-left -> upper-left is lagged; lower-right -> lower-right is advanced).
The `R +/- L` widening used here is therefore called a backward/forward **index
offset**, not a phase lag.

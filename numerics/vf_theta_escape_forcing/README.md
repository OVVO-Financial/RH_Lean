# Square-theta barrier and escape-forcing diagnostics (post-#857 / #858)

Diagnostic only. Nothing here is a premise of any Lean theorem, and finite
data cannot certify or refute an all-scale statement. The purpose is to filter
the two formulations that the post-#857 route list treats as live:

* route 2: `VFMidThetaProtectedPullBarrierStatement` (#857);
* route 3: the `VFMidThetaBoundaryEscapeForces*` statements (#858, open).

## Objects (exactly the compiled ones)

```text
E(R)   = vfMidDirectThetaEndpointError R = theta(R^2) - R^2
U_R    = vfMidSquareThetaProtectedPull R = (2R+1) - Theta_R,
         Theta_R = sum of log p over R^2 < p < (R+1)^2
E(R+1) = E(R) - U_R
F_R    = vfMidThetaBarrierRadius C R = C R log(R)^2
G(R)   = R^2 log(R)^4      (so vfMidThetaEnvelopeEnergy C R = C^2 G(R))
```

Recursive child scales follow #854: odd owner `p` with `p^3 < (R+1)^2`,
child `m = n/p` for `R^2 < n < (R+1)^2`, `S = floor(sqrt m)`, `T in {S, S+1}`.
The script uses a *superset* of the true child set (it drops the p-roughness
condition on `m`), so "escape with no child witness" is a genuine
counterexample for that envelope.

## Reproduction

```sh
gcc -O3 -march=native -fopenmp theta_blocks.c -o theta_blocks -lm
./theta_blocks 500000      # writes theta.bin / pcount.bin (about 6 min on 4 cores)
python3 analyze.py         # needs numpy
```

Sanity check: `sum_{r<100000} Theta_r = 9999939830.657757 = theta(10^10)`.
Full output: [`results_N500000.txt`](results_N500000.txt) (`R <= 5*10^5`,
`x <= 2.5*10^11`).

## Findings

**1. The envelope constant is fixed by `R = 3`, and the barrier is never
approached later.** `VFMidSquareThetaEnvelopeStatement` requires
`C >= |E(3)|/(3 log^2 3) = 1.0089`. For `R >= 10^5`,
`max |E(R)|/(R log^2 R) = 0.013`, which leaves about 78 times slack. At every
admissible `C` there are **zero** one-step escapes on the whole range.

**2. Route 2 (uniform barrier increment) needs a growing constant.** The
required
`C^2(R) = (U_R^2 - 2E(R)U_R) / (G(R+1) - G(R))` has these maxima:

| R window | max C^2 needed | p99.9 / (sqrt R / log^3.5 R) |
| --- | --- | --- |
| [10^3, 10^4) | 0.171 | 3.67 |
| [10^4, 10^5) | 0.367 | 3.94 |
| [10^5, 5*10^5) | 0.555 | 4.03 |

The normalized p99.9 column stays about constant. That matches the heuristic
`2|E||U| / (2R log^4 R)` with `|E| ~ R` and `|U| ~ sqrt(R log R)`, which
diverges like `sqrt(R)/log^3.5 R`. Extrapolating, the initialization-forced
`C^2 ~ 1.018` is exceeded near `R ~ 10^7`–`10^8`. Outward steps occur at 50.0%
of scales. The barrier statement is therefore a strictly stronger
block-by-block criterion that is expected to fail asymptotically. In contrast,
the slack-based `VFMidThetaProtectedPullInvariantStatement` is compiled as
*equivalent* to the envelope.

**3. Route 3 forcing has no detectable parent-to-child signal.** Escapes exist
only for sub-admissible `C` (initialization fails there). At every such `C`,
the recursive-child witness rate at escapes equals the R-matched background
rate of non-escape scales (`1.000` versus `1.000`). The witnesses sit at the
smallest child scales (`T/R ~ 0.1`). There, the `log^2` normalization makes the
envelope relatively tighter, so the witness comes from the existential over
about `R^(2/3)/log R` children, not from the escape. A shape-neutral control,
`F_R = cR` at `c = 1.6`, removes that bias. It gives a witness rate of 0.804
at escapes versus 0.849 for the matched background, and 32 of 163 escapes
have **no** recursive-child endpoint outside.

## Logical status (independent of the numerics)

Each #858 forcing statement, packaged with the `3 <= R <= 7` initialization
and `exists C`, is equivalent to `VFMidSquareThetaEnvelopeStatement`. The
envelope at `C` excludes every escape, so each forcing implication holds
vacuously. Through the compiled forward bridge and the classical RH bound
`|theta(x) - x| <= sqrt(x) log^2(x) / (8 pi)` for `x >= 599` (Schoenfeld),
that envelope is equivalent to RH. The forcing statements therefore do not
narrow the seam. A proof of any one of them must exclude the *first* escape,
whose lower endpoints are all inside by definition.

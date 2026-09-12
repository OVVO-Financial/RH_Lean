# Post-674 q² amplification target

The merged #674 reassembly lives at the physical square endpoint `X_R = R^2 - 1`.  The all-complete-cell factor-four recurrence from #673 is stronger than necessary: with a fixed additive coefficient at every complete cell it yields a uniform linear Mertens-energy envelope.

The new target is square-endpoint only.  For each odd prime owner `q`, let

`Y_q = floor(X_R / q^2)` and `s_q = floor(sqrt(Y_q))`.

The terminal theorem in `SquareEndpointQ2Amplification.lean` proves that it is enough to establish, after the full signed #674 reconstruction and before any norm split,

`M(X_R)^2 <= C R^2 K + 4 * sum_q M(s_q^2 - 1)^2`

for every lower critical envelope `K` below `R`.

Because `s_q^2 <= Y_q`, the sharp odd-owner daughter budget gives

`sum_q s_q^2 <= (17/72) R^2`,

so the recursive coefficient is exactly `4 * 17/72 = 17/18 < 1`.  Strong induction on the root therefore yields a fixed endpoint amplification constant, which is the existing RH-closing interface.

What remains after this PR is arithmetic, not terminal induction: reindex the literal #674 daughter cutoff `Y_q` to its lower square endpoint `s_q^2-1`, absorb the short shell into `C R^2 K`, and prove that the fully signed `finalQ2SurvivorCorrection` supplies the needed shell/boundary compensation without taking ownerwise norms.

# Post-674 q² amplification target

The merged #674 reassembly lives at the physical square endpoint `X_R = R^2 - 1`. The all-complete-cell factor-four recurrence from #673 is stronger than necessary: with a fixed additive coefficient at every complete cell it yields a uniform linear Mertens-energy envelope.

The new target is square-endpoint only. For each odd prime owner `q`, let

`Y_q = floor(X_R / q^2)` and `s_q = floor(sqrt(Y_q))`.

The terminal theorem now lives in `RHLean/Proof/SignedTransportAmplificationAudit.lean`. It proves that it is enough to establish, after the full signed #674 reconstruction and before any norm split,

`M(X_R)^2 <= C R^2 K + 4 * sum_q M(s_q^2 - 1)^2`

for every lower critical envelope `K` below `R`.

Because `s_q^2 <= Y_q`, the sharp odd-owner daughter budget gives

`sum_q s_q^2 <= (17/72) R^2`,

so the rounded recursive coefficient is exactly `4 * 17/72 = 17/18 < 1`. Strong induction on the root therefore yields a fixed endpoint amplification constant, which is the existing RH-closing interface.

The literal-to-rounded daughter shell is isolated in `research/SQUARE_ENDPOINT_Q2_SHELL_INTERPOLATION.lean`. It uses only the trivial interval variation of Mertens and deterministic square-anchor geometry:

`M(Y_q)^2 <= (37/36) M(s_q^2 - 1)^2 + 148 (s_q + 1)^2`.

Thus the shell introduces no signed cancellation. Starting from a raw factor-four daughter term, the rounded recursion coefficient is

`(37/9) * (17/72) = 629/648 < 1`,

with fixed-point denominator `19/648`. The summed shell is root-energy scale and belongs in the additive `C R^2 K` allowance.

What remains is arithmetic rather than terminal induction: prove the required signed parent/survivor inequality directly from #674's exact normal form, keeping `finalQ2SurvivorCorrection` coupled to the literal q² Mertens column until the signed reassembly is complete. No ownerwise norm or coefficient-L2 substitution is admissible.

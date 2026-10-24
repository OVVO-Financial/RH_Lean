# One-prime OAI source: recombination and coefficient bound

**Source audit, 2026-10-22.** OpenAI original Lean repository: openai/math at commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a. RH_Lean parent is draft PR #1005.

## Exact source identity

From Detector/Local.lean, after recombining the two residuals but BEFORE any triangle inequality,

\[
\mathcal B_1+\mathcal B_2 =
\frac{1-W}{1-D}\left[(v^{-1}-q)(V+(1-V)P^\star)+(1-V)B(P^\star+D)\right].
\]

Parent PR #1005 implements this exact original-OAI-complex theorem in research/oai_434/VF919ActualSexticLocalResonanceAndCompensation.lean as oai_actual_local_one_prime_recombined. For a squarefree effective ideal with slot multiplicity tau_S(m)=1, unique ideal factorization gives one marked-prime/cofactor decomposition. No inter-decomposition cancellation is possible in that case. The needed first calculation is therefore the complete within-prime compensated local sum.

## Actual physical coordinates (not a slot average)

In original Detector/EulerCoordinates.lean and Detector/HighRowsSelectedError.lean, with Q=N(P):

\[
V=Q^{-6z},\quad W=vQ^{-w},\quad
D=\eta(P)\overline v Q^{-x},\quad
R=AQ^{4-6x-6z},\quad K=\eta(P)(Q-1)Q^{-x-w},\quad
B=\overline{\eta(P)}Q^x,\quad q=Q^{-w}.
\]

Original Detector/Euler.lean marks
\[
P^\star=\frac{(R(1-Q^{-1})-KV)/(1-V)-D+WR}{1-R}.
\]
Consequently,
\[
P^\star+D =
\frac{R[(1-Q^{-1})+(1-V)(W-D)]-KV}
{(1-R)(1-V)}.
\]

Thus D is prime-dependent, not the slot-average of -Pstar; Pstar=-V is not the original identity; B may grow. The true small marked-error coordinate is Pstar+D.

## ORIGINAL SOURCE ALREADY PROVES LOCAL POINTWISE POWER SAVING

Original PrimeRows/CentralSlots.lean::actual_central_unramified_error proves, under the source's good-supported, unramified, coprime conditions and central contour:

\[
\|\text{continuedCompensatedLocal}_P
+\text{idealUnramifiedCorrection}_P\overline{v}\|
\le 720 Q^{-51/100}.
\]

Hypotheses: Q>=4, a in [51/100,1], 0<e<=1/1000, Re(x)=a+16e, Re(w)=1-a-6e, Re(z)=17/50; row P-coprime and conductor P-coprime. Proof chain: Detector/HighRowsCentralError.lean::central_unramified_error_weights, HighRowsCentralCancellation.lean::central_phase_error_bound, HighRowsCentralSelected.lean, PrimeRows/CentralSlots.lean.

This holds for a fixed relative prime window [c,d], including [1,2], with no prime-slot averaging. If Q~Z^ell, local decay is Q^(-51/100) ~ Z^(-(51/100)*ell). This DOES NOT automatically establish the stronger global conductor- and weight-normalized coefficient claim (A).

## The correct native grouped ell^(6/5) consumer

New theorems in research/VF_919_OAI_COMPENSATED_TWO_BILL_L65_20261022.lean:

1. oai_grouped_fiber_l65_recombined_bound: from |b(m)|<=A*tau(m) and ||tau||_(6/5)<=Ttau, derive ||b||_(6/5)<=A*Ttau. The bound is applied to the already-combined coefficient.
2. oai_grouped_fiber_l65_power_budget_recombined: from |b(m)|<=D^(-1/2)*Z^(-sigma)*tau(m) and ||tau||_(6/5)<=D^(5/6+c), derive ||b||_(6/5)<=D^(1/3+c)*Z^(-sigma).
3. oai_grouped_fiber_l65_power_budget_one_bill: same new contract on the explicit sum of the first and second physical residuals.

Legacy two-independent-bill theorems remain intact for callers. These new implications are finite algebra conditional on their explicit hypotheses; source-specific global coefficient saving and multiplicity moment are NOT asserted.

## Remaining decisive gates to prove or falsify (A)

- Transport the original good-prime local term to the TRUE compensated ideal column, retaining source Gaussian/Mellin weights, exact U/N(P) rescaling, masks, normalization and selected prime degree (split N(P)=p versus inert N(P)=p^2).
- Pay all non-central and ramified local cases and separate principal contour remainder; show the local Q^(-51/100) gain survives summation and all cofactor multiplicity/normalization to yield the desired D^(-1/2)*Z^(-sigma) *on individual effective ideal coefficients*.
- Prove genuine tau_S^(6/5) ideal-multiplicity bound independently; an ideal-ball sum count cannot replace a convex moment.
- Only pivot to aggregate signed prime/cofactor moments after a SOURCE-ADMITTED coefficient counterexample to the pointwise (A) hypothesis is established. Dyadic octave support alone does not make (A) false.

**Verdict:** a third outcome occurs: original one-prime central local power saving is pointwise, without Pstar=-V or decaying B. Whether full coefficient bound (A) holds or fails is still OPEN. Require warning-fatal Lean 4.34.1 CI for the newly added native consumers.

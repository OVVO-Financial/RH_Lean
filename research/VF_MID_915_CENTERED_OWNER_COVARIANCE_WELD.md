# #915: centered-owner covariance and compressed-source arithmetic audit

**2026-10-08 — mathematical attack, not an RH proof.** This note records the
native, occurrence-preserving mathematical results proved in the additional
Lean helpers and verified against actual prime data. It replaces neither the
fixed first-bad statement nor the original weighted NNS denominator.

The **canonical remaining production theorem** is
\`vfMidActualPrimeFirstBadAt_two_succ_halfScaleSectorSixPayment\`
in \`research/VF_MID_FIRST_BAD_EXACT_BUDGET_CLOSE.lean\`, where
\`hbalance\` remains **UNPROVED**. A green helper is not a green production file.

## 1. Rigorous improvement: stop decompressing D_R

The previous inherited Möbius parent matching disaggregated the signed
history \`D_R\` into individual earlier positive and negative charges. That
grossly inflated the ORIGINAL NNS denominator. The new attack instead
leaves \`-D_R\` as ONE signed anchor and reassembles the CURRENT block
from its original physical prime/sieve integer occurrences.

The exact historical UPM/LPM compression identity is

\[
 (H^++H^-+C)^2-(|H^+-H^-|+C)^2
 =4H^+H^-+4C\min(H^+,H^-).
\]

Thus all negative historical cross-pair heat extracted by expanding
\`H^+-H^-\` is exactly offset by this mandatory denominator restoration;
it is **not independent spending capacity**. The generic identity is
proved in
\`research/VF_MID_915_COMPRESSED_HISTORY_SINK.lean\`.
A second source-welded historical version is under active warning-fatal
compilation in
\`research/VF_MID_915_EXACT_HISTORICAL_NNS_COMPRESSION.lean\`.

For the measured \`R=1027\`, expansion costs approximately
10,225,580,470.548 in squared denominator, while literal \`q / 3q\`
historical negative pair heat sums to only 37.957. This is a precise
no-free-heat constraint, NOT a negative verdict on all possible
multiscale arguments.

## 2. Exact ACTUAL least-owner centering at each physical integer

For an odd candidate seat \`n\` in the open square block
\`(R^2,(R+1)^2)\`, write

\[
  S_{p^-}(n)
  ={\bf1}_{\text{no prime }q<p\text{ divides }n},
\qquad
  g_p(n)=S_{p^-}(n)
        \left({\bf1}_{p\mid n}-\frac1p\right).
\]

**No probabilistic independence or prime-density approximation** has
been used. This is an exact subtraction on each ACTUAL survivor fibre.

The original sieve stage obeys

\[
 S_p(n)=\Bigl(1-\frac1p\Bigr)S_{p^-}(n)-g_p(n).
\]

For the odd owners \`3<=p<=R\`, define

\[
 \alpha_R=\prod_{3\le p\le R,\ p\ \mathrm{prime}}(1-1/p),
 \qquad
 \beta_{p,R}=\prod_{p<q\le R,\ q\ \mathrm{prime}}(1-1/q).
\]

Iterating the *literal* one-step recurrence gives

\[
 \boxed{
  {\bf1}_{\mathbb P}(n)
      =\alpha_R-\sum_{3\le p\le R}\beta_{p,R}g_p(n).
 }
\]

Consequently, with original per-seat VF weight \`w_R=V_R/R\`,

\[
 \boxed{
 z_R(n)=w_R-{\bf1}_{\mathbb P}(n)
       =(w_R-\alpha_R)+\sum_{3\le p\le R}\beta_{p,R}g_p(n).
 }
\tag{A}
\]

This is **pointwise equal** to the original
\`vfMidOddSignedSeatCharge R n\` in \`#915\`, and the original NNS
absolute denominator is retained **exactly**:

\[
 \boxed{
 M_R^2=\left(
      |D_R|+
      \sum_{n\in\mathrm{OddSeats}(R)}
      \left|w_R-\alpha_R+\sum_p\beta_{p,R}g_p(n)\right|
      \right)^2.
 }
\tag{B}
\]

No history is decompressed and no extra \`|z|\` is added.

**Lean:** \`research/VF_MID_915_CENTERED_OWNER_TRIANGULAR.lean\`,
especially \`vfMid915Centered_prefix_telescopes\`,
\`vfMid915ActualOddSignedSeat_eq_centeredOwner\`,
\`vfMid915ActualOddSignedSource_eq_centeredOwner\`,
\`vfMid915OriginalFirstBadDenominator_eq_centeredOwner\`.

The module also welds the chronological EXACT centered charge into the
canonical real historical endpoint through
\`vfMid915ActualHistoricalDefect_eq_centeredOwner\` and
\`vfMid915ActualHalfScaleDefect_eq_centeredOwner\`.
These give a direct signed cumulative source, NOT a new owner-theorem
hypothesis, under the original compressed earlier endpoint.

## 3. Major pair-space simplification: triangular covariance

For ACTUAL distinct prime owners \`p<q\`, if \`g_q(n)\ne0\`, its
surviving carrier necessarily has \`p\nmid n\`. Hence

\[
 \boxed{g_p(n)g_q(n)=-\frac1p g_q(n)}
 \quad\text{for every integer }n.
\tag{C}
\]

The diagonal is **also exact**:

\[
 \boxed{
 g_p(n)^2=(1-2/p)\,g_p(n)
   +(p-1)/p^2\,S_{p^-}(n).
 }
\tag{D}
\]

For the actual \`R\`-th odd carrier put
\`xi_(p,R)=sum_(n odd seats)g_p(n)\` and
\`N_(p^-,R)=sum_(n odd seats)S_(p^-)(n)\`.
The full unordered off-diagonal first-owner quadratic Gram is

\[
 \boxed{
 2\sum_{p<q}\beta_p\beta_q\sum_n g_p(n)g_q(n)
 =-2\sum_q\beta_q\xi_{q,R}
                \sum_{p<q}\frac{\beta_p}{p}.
 }
\tag{E}
\]

All original signed two-owner pair products reduce to **degree-one
signed survivor-restricted deviations of the later owner**, with no
invented earlier Möbius counterpart.

The head/tail recursion is even stronger: for \`p<q\in Q\` and arbitrary
literal weights \`beta\`,

\[
 \boxed{
  \bigl[\beta_p g_p(n)+T_Q(n)\bigr]^2
  =(\beta_p g_p(n))^2+T_Q(n)^2
    -2(\beta_p/p)\,T_Q(n),
 }
\quad
  T_Q(n)=\sum_{q\in Q}\beta_qg_q(n).
\tag{F}
\]

The identical identity is also summed over the ORIGINAL VF odd seats
in \`vfMid915CenteredHeadTailOriginalOddGram_exact\`.

**Lean** in the same module:
\`vfMid915CenteredOwner_pair_eq_late\`,
\`vfMid915CenteredOwner_originalOddGram_eq_late\`,
\`vfMid915CenteredOwner_deviation_sq\`,
\`vfMid915CenteredOwner_originalOddDiagonal_eq_population\`,
\`vfMid915CenteredEarlier_times_actualLaterTail\`,
\`vfMid915CenteredHeadTailOriginalOddGram_exact\`.

**Sign caveat:** (E) is a linear identity but is NOT universally
nonpositive. Prime-owner deviations on a finite square band can have
either sign, which is the actual arithmetic uncertainty that survives.

## 4. Numerical verification against actual primes

\`scripts/vf_mid_915_centered_owner_triangular_regression.py\`
independently reconstructs all genuine stage-survivor flags, prime seats,
original signed charges, and the diagonal/cross-owner Gram, without
using any PNT-density surrogate. Finite checks are NOT RH proofs.

| R | actual square primes | diagonal owner Gram | signed cross-owner Gram | original anchored slack |
| ---: | ---: | ---: | ---: | ---: |
| 8 | 4 | +2.164898 | -0.150204 | +22.028829 |
| 18 | 6 | +3.937224 | **+0.076605** | +104.491820 |
| 56 | 12 | +13.987850 | -4.371619 | +628.228360 |
| 79 | 23 | +12.302144 | **+4.142581** | +1815.723764 |
| 119 | 19 | +26.307637 | -9.760211 | +1777.023204 |
| 317 | 54 | +56.404600 | -11.448753 | +13423.784662 |
| 1027 | 144 | +157.843393 | -33.577902 | +105561.281363 |
| 2000 | 267 | +275.967916 | -44.229146 | +360163.469553 |
| 6000 | 698 | +738.195036 | -120.444836 | +2583879.010665 |

Pointwise signed VF charge reconstruction agrees to about \`1e-15\`,
and the independent two expansions of the original Gram agree to
floating-point tolerance.

**Exhaustive consecutive scan R=8..300: 39 POSITIVE, 254 NEGATIVE
cross-owner Gram signs.** Maximum positive +4.142581 at R=79;
most negative -17.409295 at R=297.

Thus "off-diagonal owner covariance is always restoring" is FALSE
for the real prime sequence, even while the full original anchored
slack is positive in the tested window. The arithmetic sign and
historical persistence need to be controlled jointly.

## 5. Fixed small-owner CRT cancellation, actual remaining owner packet

A separate exact-rational regression already on this PR,
\`scripts/vf_mid_915_fixed_owner_crt_history_regression.py\`,
certifies full CRT periods through owner \`p=17\` and yields the sharp
uniform over-all-runs small-wheel bound

\[
 \boxed{
 \left|\sum_{r=A}^{B-1}
 \left[
  \#\mathrm{PrefixSurvivors}_{17}(r)
  -\frac{6144}{17017}\,r
 \right]\right|
 \le\frac{46460}{2431}<19.112.
 }
\tag{G}
\]

The finite rational period certificate is exact; **its generic CRT
periodicity proof for all A,B has not yet been checked by Lean.**
The underlying mathematical period/zero-mean argument is elementary,
but the finite script is not itself a kernel proof.

The new Lean module
\`research/VF_MID_915_FIXED17_ACTUAL_SIGNED_INLET.lean\`
pins the complementary **unconditional actual-prime identity**:

\[
 \boxed{
 D_B=D_A-\sum_{r=A}^{B-1}
 \left[
 V_r-\frac{6144}{17017}r
 -\epsilon_{17,r}+C_{>17,r}
 \right],
 }
\tag{H}
\]

where \`epsilon_17,r\` is the exact prefix-wheel deviation in (G)
and \`C_>17,r>=0\` counts the ACTUAL additional composites removed
after the fixed wheel, not an expected or simulated population.

For the production half-run take \`A=floor(R/2)+1\`,
\`B=R+1\`, with \`R>=34\`. The signed earlier anchor \`D_A\` remains
one scalar; the production original absolute denominator is unchanged.

The fixed low-owner arithmetic has therefore been separated
analytically into an **O(1) historical boundary** (once CRT is
formalized). What remains is an RH-precision **signed upper-owner
removal correction**; it is not made small by positivity of
\`C_>17\`, and PNT alone does not control it to \`O(R log R)\`.

## 6. Precise remaining target

The production \`hbalance\` is

\[
 \boxed{
  2D_{R+1}^{\,2}\le
  \left(|D_R|+\sum_{n\in\mathrm{OddSeats}(R)}|z_R(n)|\right)^2
 }
\]

UNDER a hypothetical first-bad \`K=2\` endpoint.

The existing repository also proves that the SAME first-bad
assumption forces the STRICT OPPOSITE inequality. Thus the open
proof is a genuine RH-strength arithmetic contradiction, not
a missing polynomial rewrite.

**What the new results remove:**
- the need to treat decompressed historical abs mass as independent
  Co/Div pair capacity;
- the need to prove a new two-owner "pair polarization" cancellation
  identity on the completed original low-owner carrier;
- all full-period small-owner signed historical drift at fixed wheel,
  once the CRT all-scale lemma is in Lean.

**What they do NOT prove:**
- a signed RH-scale bound for \`C_>17,r\` over threatening historical
  half-runs;
- a first-bad-specific sign of the surviving weighted later-owner
  shocks \`xi_q\`;
- a payment of original anchor/current-block covariance or the
  restored squareful/diagonal packets.

The decisive next mathematical inequality must constrain the actual
*historical accumulation* of later-owner deviations using additional
arithmetic distribution, not simply estimate the local signed head/
tail covariance or re-spend already compressed historical pairs.

The goal and original \`vfMidFirstBadZeroTargetTotalMass\` are unchanged.
The new helper sources are built warning-fatal in the #915 fast CI.
If that workflow remains red only at production \`hbalance\`, RH is
NOT claimed.

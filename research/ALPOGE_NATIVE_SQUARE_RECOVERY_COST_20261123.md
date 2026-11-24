# Native square recovery, complete capacity, and same-family costs

Date: 2026-11-23 (America/New_York).
Baseline: `8e5f9b59ebacc022757e13ec6737c272633c13bc`, after merged #1203.

## Outcome and scope

The three-obligation plan was attacked on its actual native source. This
change supplies a weighted integral recovery calculation, the complete
candidate/removal source identity, a quantitative weakening of the period
requirement in the global gain comparison, and an explicit scalar choice
`m=R`, `k=(R²−1)R` on the existing dyadic host.

**The complete P1/P2/P3 family and the critical bound remain OPEN.**
The new finite recovery has two channels. It has not been identified with
the physical `Ga`, and its measured energy cost does not earn multiplicity
of order `R`. The global cost theorem still requires the measured degree,
rank and slope premises on that same family. The scalar realization is not
a geometric realization.

At the initial commit, proof scripts and independent mathematical reviews
are complete; hosted compilation and terminal-axiom checks are pending.
No local Lean execution is used. The companion audit checks the actual
declarations against only `propext`, `Classical.choice`, and `Quot.sound`.
The PR's exact-head hosted results determine the final formal status.

## 1. Complete native candidate capacity

[`AlpogeNativeSquareCandidateCapacity.lean`](../RHLean/Analysis/AlpogeNativeSquareCandidateCapacity.lean)
defines each quantity independently from the finite arithmetic:

\[
K_N(n)=N/n-1,\qquad w_N(n)=\log n\,K_N(n),
\]
\[
\mathrm{PP}(N)=\sum_{\substack{1\le n\le N\\n\text{ not prime}}}
\Lambda(n)K_N(n),
\]
\[
\mathcal C_C(N)=\sum_{n\in C}w_N(n)+\mathrm{PP}(N)
-N\log N+(1+\gamma)N,
\qquad
\mathcal D_C(N)=\sum_{\substack{n\in C\\n\text{ not prime}}}w_N(n).
\]

For any `C ⊆ [1,N]` containing every prime at most `N`, the new finite-sum
proof gives

\[
G_z(N)=\mathcal C_C(N)-\mathcal D_C(N).
\]

The actual candidate family uses the already-defined native wheel:

\[
C_{s,N}=\{2\le n\le N:\ n\text{ survives every prime }
p\le s(\lfloor\sqrt n\rfloor)\},\quad s(r)\le r.
\]

Every prime is retained; `s(r)=r` yields exactly the prime set. Partial
wheels can retain composite square-boundary sites. Those sites occur in
both candidate and removal masses and cancel exactly. This avoids dropping
boundaries when joining open square blocks.

Changing the prime-complete candidate set changes capacity and removal by
the same amount. A smaller wheel ceiling alone therefore does not give a
new estimate for their difference. The exact target is retained as

\[
G_z(N)\le B\quad\Longleftrightarrow\quad
\mathcal D_C(N)\ge\mathcal C_C(N)-B.
\]

This is an exact equivalence, explicitly not a supplier of the inequality.

The proper-power correction cannot be discarded. For `N≥8`, the single
entry `n=4` proves

\[
\mathrm{PP}(N)\ge \log 2\,(N/4-1)
\ge (\log 2/8)N.
\]

Thus even this one retained prime power has linear weighted cost.

## 2. Actual weighted recovery and measured cost

[`NATIVE_SQUARE_WEIGHTED_RECOVERY_20261123.lean`](NATIVE_SQUARE_WEIGHTED_RECOVERY_20261123.lean)
extends the existing dyadic survivor classification to arbitrary real site
weights. On `3≤A≤R<2A`, write `U` for total survivor weight, `S` for actual
Möbius-weighted survivor mass, `P` for prime weight, and `D` for surviving
composite weight. Then

\[
2P=U-S,\qquad 2D=U+S.
\]

The actual signature and recovery matrices are

\[
E=\begin{pmatrix}1&1\\-1&1\end{pmatrix},\qquad
M=\begin{pmatrix}1&-1\\1&1\end{pmatrix},\qquad ME=2I.
\]

The determinant is two; no integral left inverse with multiplier one
exists. On precisely the same weighted data,

\[
U^2+S^2=2(P^2+D^2).
\]

At the actual full cutoff `A=R`, `D=0` and the resulting norm estimate is
equality. Repeating the decoder over more blocks repeats its cost with its
rank; the displayed identity supplies no extra factor `1/R`. This limits
this particular recovery construction, not every possible native route.

The kernel specialization uses `w(n)=log n*(N/n−1)`. Proper prime powers
and square boundaries are carried by the separate completed capacity
identity above. Detailed source and recovery-map analysis is in
[`NATIVE_SQUARE_RECOVERY_20261123.md`](NATIVE_SQUARE_RECOVERY_20261123.md).

## 3. Global cost with one-sided period information

[`NativeSquareCapacityPeriod.lean`](../RHLean/Geometry/NativeSquareCapacityPeriod.lean)
keeps the original `Data`, `Ga`, metric, heights, slopes, and `Main`.
For a measured degree inequality at period `P`, a lower comparison
`P≥logOm−rho` contributes precisely

\[
\mathrm{debt}=m\left(\sum_t a_t\right)\rho.
\]

The original finite global argument carries this debt additively through
`key_identity5`, the gain bound, and the mean-loss comparison. It is not
multiplied by the rank-gap factor. Dividing by the original positive
`Q=TmbDelta/2` gives exactly

\[
\frac{\mathrm{debt}}Q=
\frac{2\rho\,\overline a}{b\Delta}.
\]

The resulting theorem is attached to the literal physical top excess and
the original `physicalData`. No height or degree field is reassigned.
It retains the measured degree inequality and all actual slope, rank,
mean-loss and compatibility premises.

For localized heights, `a_t/b≈x`, so positive period slack must satisfy
roughly `rho=O(Delta*x^(−1/2+eta))` to fit a root-scale budget. A fixed
positive slack is insufficient. The case `rho=0` needs only a one-sided
lower period comparison, not an exact equality. The reverse-integrality
lemmas merged in #1203 remain possible suppliers after their actual ideal
and derivative hypotheses are physically attached.

## 4. Explicit square-clock scalar realization

[`AlpogeNativeSquareMultiplicity.lean`](../RHLean/Analysis/AlpogeNativeSquareMultiplicity.lean)
sets `x=R²−1`, `m=R`, `k=xR`. For `0<eps<1/52`, the existing large-scale
condition `26≤x^(3eps/8)` already implies `2≤x^(eps/2)`. Hence

\[
x^{1/2-\varepsilon}\le R\le x^{1/2+\varepsilon/2}.
\]

Every existing `PageN` host has `n=2^e≥x^(2+8eps)≥x`, giving

\[
xR=k\le n^2x^{1/2-\varepsilon}.
\]

There is no new host choice or asymptotic threshold. The new theorem is
universal in the actual top/thick counts and actual `aE` bound; these
premises remain explicit. It also proves the necessary restriction
`x≤n²` from the original size regime. The separate
[`realization audit`](NATIVE_SQUARE_REALIZATION_20261123.md) records the
precise remaining physical and window compatibility conditions.

## 5. Residual obligations after these results

| Obligation | Completed contribution | Still required |
| --- | --- | --- |
| P1: averaged recovery | Actual weighted two-channel integral decoder; denominator and exact energy cost | Source-compatible growing recovery with the required averaged `ASK−Ga` and `IO` bounds, on the original Frobenius/inertia and complete source |
| P2: global capacity | Original gain comparison tolerates a one-sided period bound with exact debt; original main-term cancellation retained | Measured degree, lattice slopes, near-rank relation and norm costs for the same P1 object |
| P3: simultaneous realization | `m=R`, `k=xR` on every already-selected PageN host, using the existing threshold | One actual family realizing P1/P2, counts, density, heights and localization on each required complete window |

The existing one-sided square interpolation, native NNS identity and
window-to-RH consumer remain reusable and unchanged. None is recounted as
newly proved. No complete critical estimate, finite amplification constant,
or unconditional RH theorem is claimed by this change.

## Source and continuity record

The attached execution plan was read in full. Current main was retrieved
before editing. The local upstream snapshot and original named supplier
types were inspected; no terminal upstream RH theorem was imported.
The latest canonical seven-role reports on `agent-reports` were located
without a date cutoff (latest date: 2026-11-22); their actual degree,
rank/metric, source-level and same-family warnings agree with the live
premises retained here. No exhaustive older unconsumed-report backfill or
scheduled-agent activation is claimed. Existing reports and paused #1201
work were left intact.

`descent_payment_ack=ALPOGE_NATIVE_DESCENT_PAYMENT_V1`

`tractability_ack=ALPOGE_VIOLE_TRACTABLE_RH_V1`

`MATH_STATUS=GENUINE_FINITE_RESULTS_AND_CONDITIONAL_COST_REFINEMENT`

`CRITICAL_SOURCE_BOUND=OPEN; P1=OPEN; P2=OPEN; P3_PHYSICAL_REALIZATION=OPEN`

# Complete endpoint from retained total slot mass

## Task and unchanged target

The user requested a fresh attack using the results already in the repository.
The target remains

\[
q(x)=\frac{\log(1+\mathcal A(x))}{\log x}\longrightarrow0,
\qquad
\mathcal A(x)=\max_{\substack{R\ge2\\R^2-1\le x}}
\frac{(M(R^2-1)-1)^2}{R^2K_R}.
\]

This change does not prove that limit, RH, or a uniform finite amplification
constant. It improves a complete source-compatible Mertens endpoint using
existing reflected energy and existing moving tuple mass. No new cancellation
estimate or desired-bound hypothesis is assumed.

The comparison source is main
`cae99df1c3ea24ff4113063bf09f6fd07517ad93`. The original analytic source remains
pinned to `1581d4cbdd69a0faf34b2089614fe2a814316a6a`.

## Starting input and exact consumer

`VF919ActualSlotMinRetighten.lean` already supplies the same-source boundary
`7/8 - m/24`, where `m = actualSlotMinimum D > 0`. The non-strict native
`7/8` ceiling supplies the fixed reference for the anchored HIGH contour.
The existing strict endpoint is the comparator; it is not an assumed new
source estimate or a replacement for the complete proof.

The retained inputs are:

| Existing declaration | Use in this change |
| --- | --- |
| `low_selected_physical_energy_tilted` | Estimate the same selected inverse rows at either of two fixed auxiliary row caps. |
| `low_inverse_sqrt_normalized_tilted` | Normalize with the original physical scale, retaining the extra exponent. |
| `lowUnselectedMass_moving_power_bound` | Pay that exponent with the actual complementary tuple mass. |
| `native_uniform_fixed_source_moments` | Supply the actual native moments for the same complete HIGH probe. |
| `fixed_tilted_high_bound_anchored` | Preserve the original HIGH, tails, principal contribution, and normalization. |
| `nonzero_of_probe_bounds_variable_boundary` | Compare the complete LOW and HIGH bounds against the same signal. |
| `native_mertens_growth_at_hecke_beta` | Transfer the new boundary to the original integer Mertens sum. |

The changed step is the final inverse-energy/moving-mass consumption inside
the central compensated tuple estimate. The later Gaussian, remote, ray-pool,
window, and principal-normalization steps retain their original statements
apart from the new aggregate slot budget.

## Two fixed source calls suffice

Write `S = phys.x + phys.y`, `g = 5/3 - 2*S`, and decompose the total slot mass
as `L = s + d`, with selected mass `s` and unselected mass `d`. In the original
notation, `J` indexes the **unselected** slots. Assume

\[
\frac32g\le L\le\frac16.
\]

The left side of `low_selected_physical_energy_tilted` is independent of
the physical record. That record occurs only in its row cap, reflected gate,
and resulting energy exponent. Hence two calls may estimate the identical
rows, characters, masks, coefficients, period, and nominal source argument.

The first call uses the actual physical record. The second uses the fixed
valid auxiliary record

\[
(x_0,y_0)=(17/48,23/48),\qquad S_0=5/6.
\]

If `s >= g`, the original gate holds and gives energy exponent
`S - 2*d + 507*epsilon`, which is at most `S - d + 507*epsilon`.

If `s < g`, enlarge only the upper cap on the same parent rows:

\[
C_kZ^{S-2d}\le C_kZ^{S_0-2d}\quad(Z\ge1).
\]

The auxiliary reflected gate is zero. Moreover

\[
d=L-s>\frac32g-g=\frac g2=S_0-S.
\]

Its energy exponent `S0 - 2*d + 507*epsilon` is therefore also at most
`S - d + 507*epsilon`. The common constant is the sum of the two fixed
constants; the common degree is their maximum. Both source calls occur
before the growing cutoff, rows, pools, compensation subset, and height.
There is no cutoff-dependent constant or infinite maximization.

## Pay the enlargement before summing

The physical normalization stays

\[
Q=\frac{qZ^S}{L_{\mathrm{tuple}}^2}.
\]

The new energy bound has the form

\[
E\ll(1+|t|)^n Z^{S-2d+(d+507\epsilon)}.
\]

The existing square-root normalization therefore leaves
`Z^(d/2 + 507*epsilon/2)`. The original Gram factor contributes the actual
`L_tuple^(-1/2)`. Applying the already-proved moving tuple mass with
`rho = 1/2` gives

\[
\sum_u |w_u|L_u^{-1/2}\ll Z^{-d/2}.
\]

The constants are uniform over `J`: its coefficient is bounded by
`max(1, C*a^(-1/2))^K` for the fixed finite source. The two powers cancel
before taking the full compensation sum. The resulting central power is
unchanged:

\[
\frac{5x+y}{12}+254\epsilon.
\]

The all-selected case `J = empty` retains its one outer tuple and is covered
by the original gate. No outer pair saving is asserted there. Empty selected
families and zero gate are also included.

This direct use of the existing energy declaration avoids assuming the
stronger reflected-source extension proposed in the earlier RG4 report.

## Complete same-source improvement

For `tiltedPhysicalExponents tilt`, `g = 24*tilt` and the actual total slot
mass equals `1/6`. The existing physical range `tilt < 1/960` implies the
new aggregate budget `36*tilt <= 1/6`.

Use the existing exact-minimum calibrated source `E`. It preserves `D.t`,
`D.N`, and `D.ell`, and supplies

\[
E.\sigma=m/4,\qquad m\le D.t/200,\qquad D.t\le10^{-8}.
\]

Choose the actual physical tilt `tau = E.sigma`. Then

\[
0<\tau<1/960,\qquad24\tau=6m< E.t,
\qquad\tau\le E.\sigma.
\]

These discharge the physical admissibility, original anchored HIGH tail,
and HIGH reserve hypotheses. The complete LOW power is `3/16 - 9*tau + loss`;
the same signal has shift `-11/16 - 8*tau`; and the complete HIGH remainder
uses `7/8 - 11/16 - 8*tau - E.sigma`. The resulting two boundaries coincide:

\[
\max(7/8-\tau,7/8-E.\sigma)=7/8-m/4.
\]

For the same original source the improvement over `7/8 - m/24` is `5*m/24`.
The native consequences supply every positive-loss Mertens bound at
`7/8 - m/4`. Spending the explicit positive loss `m/8` gives the fixed bound
at `7/8 - m/8`, still strictly stronger than the previous same-source
`7/8 - m/24` endpoint. The signed-pair consequence retains the exact
squarefree diagonal and every signed lag pair.

## Verification and remaining obligation

`vf919-total-mass-endpoint.yml` is the dedicated GitHub Actions proof gate.
It pins the compiler and original source, compiles the unchanged required
import closure and all three new modules with warnings fatal, checks every
public quantified type and the declared inventory, and audits terminal
axioms plus the live analytic proof dependencies. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted. Local Lean execution is
not used. A source derivation or static mathematical review is not a claim
that this gate passed; exact-head CI is the formal evidence.

Two independent source reviews checked the same-row comparison, original
normalizer, all subset cases, uniform constants, complete downstream LOW
return, and the calibrated HIGH licenses without finding a mathematical gap.

The finite positive gain above does not supply a contraction to exponent
`1/2` or an iteration valid all the way to it. In particular it does not
justify declaring the original logarithmic amplification ratio zero. That
remaining quantitative return obligation is unchanged.

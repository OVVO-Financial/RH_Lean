# Source-calibrated contraction with HIGH anchored at the proved 7/8 bound

Status at initial submission: IMPLEMENTED, CI PENDING. No new verified endpoint is claimed before the exact-head checks pass. This branch builds on unmerged PR #1073 without modifying its original theorem files.

## Construction

Let b = 7/8 and m = (7/8) D.rmin. For a fixed source, choose tilt = m/48 and sigma = m/4 = 12 tilt. The slot bounds imply m <= t/200, so 24 tilt = m/2 < m and 24 tilt < t. Also tilt < 1/960.

After the existing auxiliary eps cap, change only sigma. The exact upper coefficients for the affected budgets are 521t/4000 (geometric), 101t/800 (principal), 51671t/12000 (floor), and 201t/800 (high saving). The window cost is at most m/2 < 7m/8. The central reserve after Delta = 1/1000000 and t <= 1/100000000 is at least 6014563223/110160000000000.

The complete LOW theorem applies at x = 17/48 - 24 tilt and y = 23/48 + 12 tilt, with exponent 3/16 - 9 tilt + loss, for every positive loss after the source and tilt are fixed.

## Anchored HIGH, not a redefinition of the supremum

The previously proved native beta <= 7/8 permits contour coordinates b+e and b+8e. The arbitrary-contour source lemmas require the coordinate to be to the right of the actual beta; those premises are supplied by that non-strict theorem.

The new HIGH theorem keeps the same normalized compensated probe, original finite slots, signed rows, masks, prime exclusions, and principal correction. Its error exponent is b - 11/16 - 8 tilt - sigma. Small tails, large tails, floor/nonfloor rows, cube errors, principal integrals, and normalizers are all retained.

The LOW crossing is theta = b - tilt. Since sigma = 12 tilt, the HIGH reference boundary b-sigma lies below theta. Under beta > theta choose loss = (beta-theta)/2 and a primitive zero within loss of beta. Both estimates concern the same probe and imply nonvanishing to the right of theta+loss, contradicting that zero. The actual correction is analytic on Re(s)>21/25 and theta>21/25.

## Source generation and proof acceptance

The six additive HIGH modules are generated from exact bytes of RH_Lean commit 9cbfce5295343bcb411e6d2cb159b59995cd985b and openai/math commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a. The generator fails on source drift, missing replacement sites, or overwriting a different output. It never edits the actual supremum declaration or existing theorem files.

The configured existing proof workflow first repeats all original checks. It then generates the new source, compiles every new Lean module with warnings fatal, and checks exact terminal types, the standard axiom whitelist, and live dependencies. Generated source files and provenance are uploaded with the proof evidence. The old strict-gap endpoints are forbidden as live dependencies; the original non-strict 7/8 theorem is intentional input.

The proposed endpoints quantify a constructed source D, prove slotTilt D>0, and establish beta <= 7/8-slotTilt D and MertensGrowthAtMost (7/8-slotTilt D). This is a formula in source data, not a numerical lower bound on the improvement. No RH or sharp-window variance result is claimed.

Human review and merge remain required.

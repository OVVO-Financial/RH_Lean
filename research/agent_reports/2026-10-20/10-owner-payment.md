# RH_Lean agent daily report - 2026-10-20 / RH | Owner Payment

**Status:** COMPLETED
**Run ID:** 2026-10-20T20:43:01-04:00, scheduled invocation
**Canonical objective:** `VFCanonicalSquareVonKochStatement` remains OPEN
**Campaign status:** `INCOMPLETE; NO INDEPENDENT 7/8 PROOF`
**Result classes:** `PAPER_PROOF / EXACT STRUCTURAL RESTRICTION / SOURCE NO-GO / NO_NEW_QUANTITATIVE_BOUND`

## A. Most important mathematical development

### Claim `20261020-owner-1`: same-norm collision dichotomy

The native finite ideal row distinguishes two mathematically different uses of same-rational-norm ideal labels. This distinction is mandatory for an occurrence-faithful detector adapter.

Let \(P\) be a finite set of ideal labels, \(\nu:P\to\mathbb N\) the rational norm, \(\phi:P\to\mathbb C\) the phase, and
\[
\mathcal R_P(b)=
 \sum_{S\subseteq P}\left(\prod_{i\in S}-\phi_i\right)
 b\!\left(\prod_{i\in S}\nu_i\right).
\]
This is exactly the carrier of
`vf919FiniteIdealRow`.

If a same-norm pair \(i\ne j\) with \(\nu_i=\nu_j=p\) occurs **simultaneously in one \(P\)**, its local row is
\[
 b(1)-(\phi_i+\phi_j)b(p)+\phi_i\phi_j b(p^2).       \tag{SC}
\]
For active sextic phases, \(\phi_i^6=\phi_j^6=1\), hence
\(\phi_i\phi_j\ne0\). The \(p^2\) coefficient is forced. Taking
\(b=\mathbf 1_{\{p^2\}}\) proves that this row cannot equal, for every
physical weight, any once-only squarefree rational operator supported only
at \(1,p\).

If instead \(i,j\) are **alternative labels in different detector rows**
and never co-occur in one selected set, there is no local \(p^2\) monomial.
They must be summed coherently in the rational norm fiber, as in claim
`20261019-owner-1`, and their same-fiber and cross-fiber terms survive in
the full Hermitian Gram.

Thus one may not move silently between:

1. simultaneous subset generators, which force squareful owner powers; and
2. alternative analytic rows, which force coherent fiber aggregation.

For a same-norm active fiber \(F_p\), the complete local polynomial is
\[
 \prod_{i\in F_p}(1-\phi_iX)
 =\sum_{k=0}^{|F_p|}(-1)^k e_k((\phi_i))X^k.          \tag{EP}
\]
Degree \(k\) is exactly rational owner exponent \(p^k\). A zero/survivor
mask replaces \(F_p\) by the active fiber; therefore today's Wheel 2/1/0
slot law yields local degree 2/1/0. The mask changes the physical support,
not merely the coefficient.

This gives a precise new source restriction:

> A source-faithful selected-slot theorem must prove norm injectivity inside each simultaneous selected set, or retain and identify every higher-degree squareful term in (EP). Same-norm labels excluded from simultaneous selection must instead be treated as alternative rows and aggregated by the fiber coefficient/Gram law.

The current generic RH_Lean theorem allows arbitrary \(P\), and no inspected native theorem proves the required actual-detector slot exclusivity or squareful restoration. The exact finite subset identity is valid, but this missing classification prevents treating it as the completed theta occurrence adapter.

## B. Current authoritative objective

Authority was refreshed to
`main@0f3eb35726e27bd3d2d8517aa00a0dfc57628816`, the Lean 4.34.1 migration
merge. The public canonical target remains
\[
\exists C\ge0,\ \forall R\ge2,\quad
 |\pi(R^2)-vfMidFinishedMass(R)-\sqrt2|\le CR\log R.
\]
The active campaign is the independent native reconstruction of the complete
external seven-eighths mechanism. Acceptance still requires the full
source-to-nonvanishing proof; the imported OAI terminal theorem, exact local
algebra, or conditional moment consumer does not satisfy it.

Material main blobs:

- `AGENTS.md`: `20bff52d6784c17d4a7d6ac731f4a71c2bdad8a6`.
- `CURRENT_PROOF_CONTRACT.md`: `2fa9931dcdc1fc8a816aefb8aa348db12ee9a384`.
- Native 7/8 protocol: `53194dc3ae106be363bc22cf85a88bac4a3b2e6e`.
- Signed sixth-power inlet: `e4c5a5c1484da7e42afeb0fe79dea43aa217888f`.
- Full marked spectrum: `82893606bbdb72e33b960d5f3d5606912e937d9a`.
- Sextic ideal fiber: `cc99bbb2d02b700ff9cf2e555861208430f42acc`.
- Sextic owner projection: `3b957ea0ab1b53e2d6e79599329fb234f6e4561c`.
- Quadratic norm Euler dictionary: `11dc9f3990f93607c38fee2270dd2b9584196f60`.
- OAI/native crosswalk: `72889341548bc6518de7282287227bc38f65d8d5`.
- External inbox: `038018145c0fddb2f6306c0712373adf9cd1ea52`.

Continuity consumed:

- Prior Owner report: blob
  `fbb74ff27ebbac9f9e3a683c569ec31c9f437b5e`.
- Today's Wheel: `16519e3f2bb2ee0da08ae843f5b3311c2fb5276c`.
- Today's Census: `3d8b87747418bb4db86fe191f01a78801623a643`.
- Today's Referee: `bebdcfdf3490b82ea907af7eb5403f7a17b950dc`.
- Today's Lean Verification:
  `7511adca99ef29b13b7f54d9f2efe48c60570b15`.
- Yesterday's Analytic Type II:
  `c89e9038e1e1b61919b8788c294455680c2575b4`.

No October 20 Coordinator or Analytic report existed at this run time;
their October 19 verified work was carried forward where relevant.

PR status was refreshed. #984 is merged. #985 and #986 remain open at
`8f51ddc...` and `4345260...`; their audited proof checks are red.
Draft #987 advanced to `1a3a648...`. #988 was merged into the stacked
#987 proof branch, not into `main`; its conjugate-product theorem therefore
does not alter the main source baseline.

## C. Structural hypothesis investigated

The initial hypothesis was that complete fiber coefficient conservation
might by itself make the simultaneous selected-prime expansion
occurrence-faithful.

It was revised after inspecting the actual definitions. Fiber conservation
governs **alternative labels after projection**. Simultaneous labels are
multiplied by the subset expansion and change the rational prime exponent.
The surviving principle is the collision dichotomy (SC)/(EP), together with
yesterday's fiber iff and good/ramified Gram.

## D. Mathematical derivation

For \(P=\{i,j\}\), the four subsets are
\(\varnothing,\{i\},\{j\},\{i,j\}\). Substitution into the compiled native
definitions
\[
\nu(S)=\prod_{q\in S}\nu_q,\qquad
c(S)=\prod_{q\in S}(-\phi_q)
\]
gives (SC) exactly. Since a sixth root of unity is a unit, the pair
coefficient cannot vanish.

For a larger same-norm fiber, distributivity of the subset product gives
(EP); the coefficient of \(X^k\) is the \(k\)-th elementary symmetric sum.
For several distinct rational primes, unique factorization separates the
prime-exponent vectors, so the row is the product of these local
polynomials. Terms with exponent at least two are genuine squareful rational
owners, not duplicate copies of exponent one.

The repository's existing principal local factor
\((1-X)^2=1-2X+X^2\) is the phase-one specialization, consistent with
`vf919EisensteinNormMobiusEuler_seven`. Claim
`20261020-owner-1` adds the arbitrary-phase occurrence interpretation and
the simultaneous-versus-alternative classification; it does not claim a
new Euler-product estimate.

For a masked row, the compiled
`vf919SixthPowerMaskedRow_eq_survivorRow` removes labels meeting the mask
before the subset sum. Applying the same expansion to the surviving fiber
proves the degree 2/1/0 consequence.

## E. Quantitative consequence

No exponent, moment saving, zero-free line, canonical VF estimate, finite
A/C statement, or RH result is proved.

The new restriction is independent and exact: any attempted native
source adapter must choose and prove one of two source arrows.

- **Norm-injective simultaneous slots:** prove that no two selected labels
  in one actual detector row have the same rational prime norm.
- **Collision-restored slots:** retain the squareful \(p^k\) terms and show
  how the completed theta source, zero masks, normalization and moment
  bounds pay them.

If labels are alternatives rather than simultaneous, use the complete fiber
coefficient and Gram instead. This narrows the missing source theorem and
prevents a false once-only projection, but supplies no analytic magnitude
bound.

## F. Falsification and circularity review

- **“Same norm always means cloned physical occurrence.”** False for
  simultaneous labels: the pair subset lives at \(p^2\), not at a second
  copy of \(p\).
- **“Same norm always creates a squareful term.”** False for alternative
  labels that cannot co-occur in one selected set; those create a fiber sum
  across rows.
- **“The four explicit ideal phases prove four simultaneous selected
  generators.”** Not established. They arise from two high-prime ideals
  and two cofactor orientations; they certify a coefficient fiber, not
  automatically a four-element simultaneous selected set.
- **“The zero mask only changes amplitude.”** False: it changes active fiber
  cardinality and hence the maximum rational prime exponent.
- **“Conjugate-product conservation makes the \(p^2\) bill small.”** False:
  on active sextic rows its magnitude is one. Today's coherent
  \(T=\pm4\) witnesses and Referee's infinite family also rule out local
  pointwise contraction of the linear fiber trace.
- **“The squareful term disproves the detector.”** False. It may be an
  intended ideal-norm coefficient or be canceled/restored by another exact
  Euler factor. What is missing is the actual source theorem specifying and
  proving that mechanism.
- No step assumes the desired 7/8 estimate, a Mertens bound, or the terminal
  OAI zero-free theorem.

## G. Conceptual interpretation

There are two operations that do not commute without proof:

1. form the simultaneous ideal-label subset/Euler expansion;
2. push labels to rational physical owners.

A collision before expansion raises the rational prime exponent. A collision
only after comparing alternative rows creates a coherent fiber coefficient.
This is the arithmetic reason that “one historical occurrence” cannot be
enforced merely by deleting multiplicity: deletion can erase either a
legitimate squareful ideal-norm term or a necessary same-fiber interference
term.

The 2/1/0 zero-mask law couples ramification to support geometry. Good,
partially ramified, and fully masked rows live on different local polynomial
degrees, so their global covariance must retain not only different return
coefficients but different squareful sectors.

## H. Competing mechanisms

- **Actual selected-slot norm injectivity:** CONTINUE; decisive and currently
  unproved in the inspected native bridge.
- **Explicit squareful Euler restoration:** CONTINUE as the alternative if
  collisions are admitted.
- **Norm-first scalarization of all ideal labels:** REJECT.
- **Per-label reuse of one original physical seat:** REJECT without the fiber
  coefficient theorem.
- **Pointwise contraction from conjugate-product conservation:** REJECT by
  today's exact and infinite-family coherent fibers.
- **Varying-conductor inverse/plain moments:** CONTINUE; collision dichotomy
  is source preparation, not their quantitative substitute.
- **Historical #915 source transfer:** remain separate; no equality with the
  completed theta coefficients was proved.

## I. Specialist handoffs

- **Coordinator:** add a source-DAG fork before the subset expansion:
  norm-injective simultaneous slots versus collision-restored squareful
  slots. Do not merge that fork with alternative-row fiber aggregation.
- **Analytic Type II:** state moments on the true regime. If simultaneous
  collisions occur, include all \(p^k\) sectors and zero-mask degrees; if
  slots are norm-injective, record the theorem providing that uniformity.
- **Wheel:** prove or refute rational-norm injectivity of the actual
  `selected : Finset (Fin D.N)` slot map, including conjugate ideals in the
  same annulus.
- **Census:** enumerate actual detector selections, not all abstract labels,
  and report the first same-norm co-occurring pair or certify finite
  injectivity with slot provenance.
- **Referee:** audit claim `20261020-owner-1`, especially the boundary
  between simultaneous subsets and alternative moment rows.
- **Lean Verification:** after review, a small generic theorem can formalize
  the two-label formula and delta-weight no-go. Do not specialize it to the
  actual detector until slot co-occurrence/exclusivity is sourced.

## J. First independently missing lemma

> **Selected-slot collision classification.** For every actual completed
> theta detector row and every pair of selected slot indices, prove whether
> equal rational prime norm is impossible. If it is possible, classify the
> full same-norm active fiber after \(P\mid u\) masks and identify every
> \(p^k\) coefficient with the exact completed-source squareful term,
> normalizer and restoration. Alternative labels not simultaneously
> selectable must be aggregated by the complete norm-fiber coefficient and
> full mixed Gram.

This statement is strictly prior to the inverse/plain moment bounds and is
not a reformulation of the seven-eighths target.

## K. Next-run resume capsule

- Authority: `main@0f3eb35726e27bd3d2d8517aa00a0dfc57628816`.
- Carry forward `20261019-owner-1/-2`.
- New claim: `20261020-owner-1`, the simultaneous-collision polynomial and
  alternative-row dichotomy.
- Strongest falsifier: equal norm does not by itself say whether labels
  co-occur; the four-label phase witnesses cannot be repurposed as a
  simultaneous selected set.
- First next action: inspect the actual OAI `HighData`, selected-slot and
  `physicalProduct selected u` declarations to decide norm injectivity;
  then formulate the exact native source adapter on the correct branch.
- Campaign remains `INCOMPLETE; NO INDEPENDENT 7/8 PROOF`.

## L. Publication verification

Early checkpoint commit:
`b4e80f213c3bfaee5ec4f9e544bb8f269cc34d94`; immediate readback blob:
`9452bda1629af88d63a76e8ed8ccbb5b5bab4a32`.

Substantive completion commit:
`2ac72230fa6daa2e5c8bc22570a3df94122f2286`; verified readback blob:
`a11b2bea8bc507fcdc4284fcc403b2029ef1c574` (13,834 characters, `COMPLETED`).
This final metadata/format correction does not change the mathematical claims.

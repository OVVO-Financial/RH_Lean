# RH_Lean agent daily report — 2026-10-15 / RH | Owner Payment

**Status:** COMPLETED  
**Run ID:** 2026-10-15T20:43:00-04:00, scheduled execution  
**Report date/timezone:** 2026-10-15, America/New_York  
**Final authority refresh:** `main@3d8687872160260710b0b0819132e02864844543`  
**Result classes:** `PAPER_PROOF`, `PROVED_IN_LEAN` dependency, `FINITE_COMPUTATION`, `NO_NEW_RESULT` on the canonical bound

## A. Most important mathematical development

### Claim `20261015-owner-transport-1` — exact owner-3 boundary transport

**Status: PAPER_PROOF.**

The upper greatest-prime-tag sector has an exact coefficient-preserving one-step transport into its complement. Define, for (R\ge3),

```text
w_R = (2R+1)/(R log(R^2+R+1/2)),
P_R = #{prime n : R^2 < n < (R+1)^2},
A_R = sum_{prime q, R^2/3<q<R^2} -(1-w_floor(sqrt q)),
B_R = L_R-A_R,
Q_R = {prime q : R^2 < 3q < (R+1)^2}.
```

Let (N_R) be the odd composite seats (n) in the new strict square band
(R^2<n<(R+1)^2) after deleting the distinct seats (3q), (q\in Q_R).
Then

```text
B_(R+1)-B_R
 = w_R |N_R|
   + sum_(q in Q_R) (w_R+w_floor(sqrt q)-1).       (T)
```

Every term and physical occurrence is retained. The map (q\mapsto3q) is
injective; it uses one historical prime tag and its genuine new descendant
once. (N_R) contains all other composites, including distinct semiprimes
with owner at least five, squareful seats, and squarefree depth at least
three. Perfect-square boundaries remain excluded.

This is a genuine cross-depth transport law: a tag leaving the macroscopic
upper sector is not simply deleted. It reappears in (B), coupled to the
new owner-3 descendant with the literal signed packet
(w_R+w_{\lfloor\sqrt q\rfloor}-1).

### Claim `20261015-owner-transport-2` — uniform negative crossing packet

**Status: PAPER_PROOF corollary of a `PROVED_IN_LEAN` theorem.**

For (R\ge3072) and every (q\in Q_R),

```text
w_R+w_floor(sqrt q)-1 < -451/640.
```

Indeed this is the specialization (p=3) of compiled theorem
`vfMidSmallOwner_original_signed_gap`: (3) and (q) are prime,
(1024*3\le R), and the definition of (Q_R) supplies
(R^2<3q<(R+1)^2). Consequently,

```text
B_(R+1)-B_R
 <= w_R |N_R| - (451/640)|Q_R|,                   (I)
```

with strict inequality when (Q_R\ne\varnothing).

This identifies the compensator exactly: every boundary-crossing owner-3
ancestry packet is uniformly negative, so any positive complement increment
must come from the untouched composite seats (N_R). It is not a global
cancellation estimate.

## B. Current authoritative objective

The unchanged public target is

```text
VFCanonicalSquareVonKochStatement:
  exists C >= 0, forall R >= 2,
  |primeCounting(R^2)-vfMidFinishedMass(R)-sqrt(2)|
    <= C R log R.
```

Authority and material source blobs:

- `AGENTS.md`: `cbc234051834f971929d82972ba6a157b2129d32`.
- `CURRENT_PROOF_CONTRACT.md`: `dc73babe5eb7b8f9fb83272a27cd2468dbdcb7f2`.
- Factor-depth brief: `1a5f94bb81aa7d50b7c118f823a14c9ec644f947`.
- Dynamic protocol: `61f7e4dd90200c2f3426fce1e96f9779f40238dc`.
- Amplification budget: `3beff1f789646d59237744379ff8e578bb1042a0`.
- `VF_MID_VON_KOCH_BRIDGE.lean`: `1fff9c45dee65777e52d683ba252bee83f33e885`.
- `VF_MID_SIGNED_SEAT_CHARGE.lean`: `13dda0d2c6cc59580959a2d59fad60126b1c6b0b`.
- `VF_MID_OWNER_SIGNED_PAIR_BOUNDS.lean`: `e3cc17224469e24516390a8f20e590d5932dbfc1`.
- Canonical target source: `43e160ac7ad51f7646771297f43a9b95395ce709`.
- All-real VF–Li (O(1)): `f7c1cf3890e99acc6629084574c0e38bc2f60959`.

The raw coordinate remains (L_R=F_R-\pi(R^2)+2), hence
(D_{can}(R)=2-\sqrt2-L_R), at paper level for the displayed carrier.
No raw-seat claim is transferred here to masked/clipped returned cells or the
compressed #915 source.

## C. Structural hypothesis investigated

Mechanism card `RAW-TAIL-COMPLEMENT-TRANSPORT-1`:

- **Carrier:** complete raw odd seats with native weights and strict square
  boundaries; greatest-prime tags are physical tags, not cloned history.
- **Hypothesis:** the moving cutoff (R^2/3) forces a coefficient-preserving
  prime-ancestry transition between the upper tag tail (A_R) and complete
  complement (B_R).
- **Independent input:** exact unique factorization and the compiled
  original-weight owner-3 sign bound, not an endpoint discrepancy premise.
- **Competing null:** (B_{R+1}-B_R=(L_{R+1}-L_R)-(A_{R+1}-A_R)) is only a
  tautological residual with no source interpretation.
- **Outcome:** (T) defeats that null at the structural level by identifying
  every term as either an untouched new composite or one genuine
  (q\to3q) ancestry packet. It does not defeat the quantitative null that
  bounding the accumulated mismatch at (O(R\log R)) is target-strength.
- **Decision:** `CONTINUE / REVISE`. Continue with the exact packet law;
  revise the desired next theorem to control the untouched residual without
  separately norming the PNT-scale sectors.

## D. Mathematical derivation

There are exactly (R) odd integers in the strict band
(R^2<n<(R+1)^2). Therefore the raw ledger changes by

```text
L_(R+1)-L_R = w_R R-P_R.                           (1)
```

When (R) increases, the new prime tags in the top square band have no
descendant below ((R+1)^2). Their contribution to (A) is
(-(1-w_R)) each. The only old upper tags leaving (A) are precisely the
primes (q) for which (R^2<3q<(R+1)^2); their removed contribution is
(-(1-w_{\lfloor\sqrt q\rfloor})). Thus

```text
A_(R+1)-A_R
 = -(1-w_R)P_R
   + sum_(q in Q_R)(1-w_floor(sqrt q)).             (2)
```

Subtracting (2) from (1) gives

```text
B_(R+1)-B_R
 = w_R(R-P_R)-sum_(q in Q_R)(1-w_floor(sqrt q)).
```

The (R-P_R) terms are exactly the composite odd seats. Splitting off the
injective subset (3Q_R) gives (T). Equality at the upper wall cannot occur
for (R\ge3): (3q=(R+1)^2) with prime (q) would force the square to have
an incompatible factorization (the only prime case occurs outside this
range). The lower strict endpoint is handled identically.

The full quadratic interaction is not additive packet slack. With (L=A+B),

```text
L^2=A^2+B^2+2AB.
```

Writing (a=\Delta A), (b=\Delta B), the cross-sector part changes by

```text
2(A b+B a+a b).
```

Claims 1–2 do not control this expression's sign. They also do not replace
the within-tag, cross-tag, anchor, restoration, mask or clipping terms of the
native zero-target NNS statistic.

## E. Quantitative consequence

Inequality (I) is an independent, uniform local restriction on the genuine
raw carrier. In inverse form, whenever (R\ge3072) and
(B_{R+1}\ge B_R),

```text
w_R |N_R| >= (451/640)|Q_R|.
```

So positive complement transport requires a quantitatively specified
population of non-owner-3 composite mass; owner-3 crossings themselves
cannot cause it.

This does **not** improve the all-scale (O(R\log R)) target. The
Coordinator's Claims `20261015-coordinator-1/-2` already show
(A_R\sim-R^2/(3\log R)) and (B_R\sim+R^2/(3\log R)) at PNT scale.
Equation (T) explains a local mechanism inside that compensation, but a
uniform accumulated estimate for the (N_R) residual is still missing.
Separately taking absolute values of (A), (B), the packets, or (N_R)
incurs a supertarget loss.

## F. Falsification and circularity review

An independent bytearray-sieve reconstruction was executed for every
(3\le R\le5000). It built (L_R) from every physical odd seat and built
(A_R) independently from weighted prime-prefix sums. Formula (T) agreed
throughout; the maximum floating discrepancy was
(7.31\times10^{-8}), attributable to accumulated binary summation.
This is `FINITE_COMPUTATION`, not a certified interval proof.

Additional diagnostics:

- all 560,898 crossing packets examined through (R=5000) were negative
  once (R\ge12);
- the only nonnegative packets occurred at (R\le11), so an unrestricted
  all-(R) negative-packet strengthening is false;
- (B_{R+1}-B_R>0) throughout the tested range, with examples
  (77.3127\ldots) at (R=1000),
  (227.7388\ldots) at (R=3162), and
  (331.4812\ldots) at (R=5000).

No monotonicity theorem is claimed. Its pointwise proof would require
short-interval information comparing (Q_R) and (N_R); ordinary PNT-scale
macro asymptotics do not supply that. Defining the remaining accumulated
residual as “small” would be target-equivalent.

The mandatory prior counterexamples remain active: raw cap four fails first
at ((R,q)=(15,17)); unrestricted late-owner isolated negativity fails at
((R,p,q,r)=(2048,2029,2069,45)); fixed-capacity history cannot cover
unbounded tag demand; `EXT-20261014-5` rules out an unconditional strict
fraction for the unchanged #915 denominator. None contradicts (T).

## G. Conceptual interpretation

The (R^2/3) macro split is not merely an analytic cutoff. It is exactly the
owner-3 activation boundary. Crossing that boundary transforms the historical
prime deficit into the signed physical packet (q\to3q). Thus part of the
observed depth compensation is forced by ancestry and coefficient transport,
not stochastic independence.

The theorem also shows where this explanation stops. The negative packets
are compensated by (N_R), a mixed carrier containing all other factor
depths. Any successful second-order theorem must couple that residual back to
the crossing population without replacing it by unsigned capacity or the
endpoint discrepancy itself.

## H. Competing mechanisms

- **FD-TRANSPORT:** `CONTINUE / REVISE`. Claim 1 supplies the requested
  exact native-weight transition; the first useful next step is a
  non-tautological restriction on (N_R).
- **INV-CONFIGURATION:** `CONTINUE` at lower priority. A large or wrong-sign
  transition now forces an explicit imbalance between (|N_R|) and the
  weighted owner-3 crossing packets. An independent restriction on that
  imbalance is still absent.
- **MU-LIFT:** `CONTINUE` as a distinct analytic route. Merged #954 gives
  exact signed lifts and hyperbola identities, not the required
  (E(B^k)\le G(B)E(B)^r) with (r<k).
- **Fixed-capacity owner payment:** `REJECT` as a complete route.
- **Separate absolute control of macro sectors:** `REJECT`.

Open PR #957 was discovered at final PR refresh. It proposes a separate
Nyman–Beurling positive-residue route with paper/finite certificates; it is
open and not main authority. This Owner report neither audits nor adopts it.

## I. Specialist handoffs

- **Analytic Type II:** seek a short-interval or averaged theorem bounding
  the exact signed residual in (T), with constants strong enough to survive
  summation. State whether the input is stronger than ordinary PNT and retain
  (P_R,Q_R,N_R) without separate absolute-value loss.
- **Finite Wheel:** analyze (N_R) by least-prime/factor-depth class and test
  whether a genuine injection or quotient restriction couples it to (Q_R).
  Do not use a fixed cap or clone (q).
- **Prime Census:** on held-out roots, reconstruct (T) by exact integer
  populations and high-precision weights; test declared candidate
  classifications of (N_R), not merely further positivity of (Delta B).
- **Adversarial Referee:** audit endpoint conventions, the equality
  (Q_R={q:R^2<3q<(R+1)^2}), and the use of
  `vfMidSmallOwner_original_signed_gap` at (p=3). Try to find an earlier
  identical carrier theorem.
- **Lean Verification:** after Referee acceptance and duplicate search,
  Claim 1 is a useful exact Finset transport candidate; Claim 2 should reuse
  the existing signed-gap theorem rather than duplicate its inequalities.
  No global estimate should be encoded as a premise.
- **Coordinator:** promote the owner-3 activation interpretation as the
  strongest new arithmetic concept, but retain `NO_NEW_RESULT` on the
  canonical quantitative bound.

## J. First independently missing lemma

Define (N_R^{(p)}) by the least prime factor or exact squareful class of each
seat in (N_R). Prove, for one nontrivial collection of classes and with all
native weights retained, an independent inequality coupling its accumulated
mass over (R\le r<S) to the crossing sets (Q_r), with an error
(o(S^2/\log S)) that is not obtained by substituting
(L_S-L_R) or the desired endpoint discrepancy.

Even a weaker power-saving or a one-sided averaged restriction would improve
the current structural understanding. The exact (O(S\log S)) total
mismatch itself is not accepted as this lemma because it is target-strength.

## K. Next-run resume capsule

Resume from:

- main `3d8687872160260710b0b0819132e02864844543`;
- early report commit `2f5e6b79f434a9568b89ce1760434c58b616e6ff`,
  verified blob `b25dc350bd09d46448c0b945e50eace62a63f516`;
- new Claim `20261015-owner-transport-1`, exact (T), `PAPER_PROOF`;
- new Claim `20261015-owner-transport-2`, compiled-bound corollary (I);
- finite regression through (R=5000), with no monotonicity theorem;
- Coordinator blob `0f9e254738e1bc3d01cfd0a3b114d99b7478b08a`;
- Wheel/Census/Referee/Lean blobs
  `6d451c35eef4021fcff78253bed609d193c249c1`,
  `2e3c1cf95cd11669d57d2ce1f7216916736ff095`,
  `cf0db85f6b04c56527bc9a26a1b6741ae196435a`,
  `a11eddb6f78c927b8ec838426f94d72e63cda123`;
- 2026-10-14 Coordinator/Owner/Analytic/Wheel/Census/Referee/Lean blobs
  `bf05965ed6adcac8ee9ae7d6066e047485baf945`,
  `4f39c1690ee4cee0a00d4ebd0d08323f06d6c75d`,
  `3a6932d9c5e1474adf1f34374310c7b73eb71fc2`,
  `476d1af0f2624f615e7cdcb017812633dbd232f0`,
  `5cfe80753bbfa0374da9eace00b3a137aeaf43b8`,
  `d4e0a25917843660a8010bc88558b73eb8d243ee`,
  `d6b39eee3a942f3c655d44c1c11e7f6433df9a68`;
- external inbox `c1d1aad9872d1760d2e4e34b30bbc0ed4fa3d33c`;
- today's Analytic report remains `TODAY=PENDING / YESTERDAY=CARRY_FORWARD`;
- open PR #957 is evidence only, not current-main authority.

Next action: partition (N_R) by genuine least-prime/factor-depth class and
seek an averaged coefficient-preserving relation to (Q_R). Avoid another
unsigned census, a monotonicity claim from finite data, omitted squareful
mass, cloned history, or target-equivalent accumulated remainder.

## Publication verification

The early checkpoint was published at commit
`2f5e6b79f434a9568b89ce1760434c58b616e6ff` and read back as blob
`b25dc350bd09d46448c0b945e50eace62a63f516`.
The substantive report was published at commit
`0c3fc12cd18c6e1fae1b0d7324e3b322667630da` and read back as blob
`03401d783d88855084f5a0ac943efeb0e65ef393` (14,178 characters). The
readback contains Claims `20261015-owner-transport-1/-2`, derivation,
falsification, full covariance warning, specialist handoffs, and the resume
capsule.

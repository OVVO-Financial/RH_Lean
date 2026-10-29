# RH_Lean agent daily report - 2026-10-28 / RH | Owner Payment

**Status:** COMPLETED
**Invocation:** scheduled run begun 2026-10-28 20:43 America/New_York
**Final authority refresh:** 2026-10-28 America/New_York
**Pinned main:** `a59d351aa33c3cc071ab7b9221f765dc89a2012c`
**Authority blobs:** `AGENTS.md` `4bc5e5bacd333be41ca9334fa6eaf8e29b9bd1c8`; `CURRENT_PROOF_CONTRACT.md` `24bd727096001b68c76b28fe70c99b8d548d7bfe`; native-first routing `c9a74b1bf2727ff1522c27e9934f521671b128ae`.
**New claim:** `20261028-owner-1`
**Result classes:** `REFUTED` (unfiltered form of `20261027-owner-1`), `PAPER_PROOF / CORRECTED SUPPORT-FILTERED LEDGER`, `IDENTITY_ONLY / RANK-ONE INCIDENCE INVARIANT`, `CONDITIONAL INVERSE RESTRICTION`, `NO_NEW_GLOBAL_QUANTITATIVE_BOUND`.

## A. Most important mathematical development

### Claim `20261028-owner-1`: geometric returned carriers must be support-filtered

The unfiltered three-class count identity reported as `20261027-owner-1` is false. The definition

```text
CARRIER(R,p,sig) =
  vfMidActiveReturnedPairCarrier R p sig
= clippedBaseFiber x admittedBaseFiber
```

is a geometric product, not the support of `vfMidOneBlockActivePhysicalSite`. The compiled theorem `vfMidActiveReturnedPairWeight_eq_physical` says a carrier member has weight `v_R(a) * v_R(p*c)`; either factor may be zero.

A literal counterexample is

```text
R=3, p=3, sig=empty, (a,c)=(7,1).
```

At clock `R+1=4), the common endpoint is `4^2-1=15). Both 7 and 1 are squarefree, 3-free, and have empty lower-3 signature; `3*7>15` and `3*1<=15`. Thus `(7,1)` belongs to the returned geometric carrier. But the active band is `(9,16)`, so `v_3(7)=v_3(3)=0), and the actual atom is zero. The old classification assigned `(1-w_3)^2>0` (numerically `w_3=0.9238258189...`). This refutes the old equation with its stated counts.

The exact repair filters every count by

```text
a in A_R,  p*c in A_R,
A_R = vfMidOneBlockActivePhysicalCarrier R.
```

Call the support-filtered composite/composite, prime/composite, and prime/prime counts `C*_R, P*_R, T*_R`. Then

```text
E_R = G_R
    + 2*w^2*C*_R
    - 6*w*(1-w)*P*_R
    + 2*(1-w)^2*T*_R.                              (1)
```

If `A_R` and `B_R` now denote the numbers of composite and prime sites in the active carrier, unique least-owner Fubini gives

```text
C*_R = A_R*(A_R-1)/2,
P*_R = A_R*B_R,
T*_R = B_R*(B_R-1)/2.                              (2)
```

Therefore the incidences are not independent:

```text
(P*_R)^2 - 4*C*_R*T*_R
  = A_R*B_R*(A_R+B_R-1) >= 0.                       (3)
```

Equation (3) is the strongest new structural fact. The complete returned interaction is rank one at the population level. A same-block covariance theorem using only these three counts cannot contain information beyond the active prime/composite population imbalance.

## B. Current authoritative objective

The canonical target remains

```text
exists C>=0, forall R>=2,
  |pi(R^2)-VF_can(R^2)| <= C*R*log R.
```

It is open. Native-first routing assigns this role the occurrence-faithful original #915 ledger and a nonlocal signed cross-owner restriction. Main now includes merged #1046 shared-gcd CRT covariance and #1047 moving Euler/OAI shell localization. Neither supplies a bridge to (1) or bounds `G_R`.

Material source blobs checked:

- active returned raw-parent carrier: `dd872ccdf0eac1e78f998aa77f357f68df53f76e`;
- final returned Co/Div Fubini: `47e4255f76fb3387d1b12d0fa185cffde2744e63`;
- weighted global first-owner Fubini: `4679d7edae521dd4d9f0238aa4201445b1fdb9a9`;
- arbitrary-site cell Fubini: `c99074725868c1e4798d2539d86bb2f1a7912e60`;
- global ordered off-diagonal carrier: `6219eb830b7fe682e7f5fc01ccd4f5455b95c306`;
- active excess ledger: `c103b811dfe5ac4130c71134a93bb23793c11695`.

## C. Structural hypothesis investigated

**Hypothesis.** The returned three-class counts might satisfy a new centered-square/covariance restriction strong enough to pay the source.

**Verdict.** Revised. They satisfy the exact rank-one law (2)-(3), but this is a population identity, not an independent prime-distribution estimate. Its useful content is an inverse balance test; it cannot by itself control `G_R`.

## D. Mathematical derivation

Let `v_R(n)=vfMidOneBlockActivePhysicalSite R n`. On the support-filtered carrier,

```text
v_R(n) = w - 1_Prime(n).
```

For `c>1`, the child `p*c` is composite. For `c=1`, the child is the prime `p`. The apparent fourth support class (composite `a`, `c=1`) is empty: an active composite below `(R+1)^2` has a prime factor below `R+1), while an active prime child `p` lies above `R^2`; they cannot share the lower-`p` signature.

The three nonzero products are

```text
w^2,  -w*(1-w),  (1-w)^2.
```

For the pointwise excess `Ex(z)=4*z-2*|z|`,

```text
Ex(w^2)         =  2*w^2,
Ex(-w*(1-w))    = -6*w*(1-w),
Ex((1-w)^2)     =  2*(1-w)^2.
```

Zero-weight geometric records contribute `Ex(0)=0`. Substitution in the compiled complete anchored equality proves (1).

For (2), the compiled first-owner Fubini partitions the full ordered off-diagonal common-clock carrier. Each cell is one orientation of the p-free/child crossing, and the global square theorem restores the factor two. Restricting the arbitrary site to the active carrier assigns every unordered distinct active pair exactly once. Partitioning by prime/composite type gives (2), and expansion gives (3).

Put

```text
x = w^2*C*_R,
y = (1-w)^2*T*_R,
z = w*(1-w)*P*_R.
```

Equation (3) gives `z^2 >= 4*x*y`. Hence

```text
(x+y)^2 <= 36*x*y  ==>  x+y <= 3*z.                 (4)
```

Under (4), the complete returned contribution in (1) is nonpositive. Conversely, a positive returned contribution forces

```text
(x+y)^2 > 36*x*y,                                   (5)
```

an extreme weighted population imbalance, with the natural interpretation when one class is empty.

## E. Quantitative consequence

There is no new all-scale exponent or canonical bound.

The exact inverse restriction is: if (4) holds and a first-bad event gives `E_R>0`, then necessarily `G_R>0`. A hypothetical failure cannot be attributed to the returned carrier unless the weighted prime/composite populations are extremely imbalanced as in (5); otherwise the obstruction lies in the quarantined anchor/diagonal/squareful/omitted-seat residual.

This is structural localization, not payment. Proving (4) uniformly is a prime-distribution statement on the actual active support, and bounding `G_R` remains separate.

## F. Falsification and circularity review

1. **Carrier/support confusion:** refuted by `(R,p,sig,a,c)=(3,3,empty,7,1)`.
2. **No cloned history:** support filtering only removes zero physical atoms from geometric counts.
3. **All cross terms retained:** (1) begins with the complete anchored equality; (2) uses the full off-diagonal Fubini.
4. **Diagonal not hidden:** the binomial counts are off-diagonal; diagonal and restoration remain in `G_R`.
5. **No independence assumption:** (3) is deterministic and exact.
6. **No target-equivalent promotion:** (4) and the needed residual sign are unproved.
7. **Euler sparsity not imported:** `20261028-referee-1` shows exact-zero carry incidence has no amplitude effect on its complement, and no bridge to (1) exists.
8. **Finite scope:** the R=3 witness refutes the universal old identity. The numerical value of `w_3` only displays the discrepancy; the support zero follows directly from definitions.

## G. Conceptual interpretation

First-owner chronology orients every active off-diagonal pair once and preserves its physical weight. It does not turn the larger clipped/admitted product into active support.

After filtering, the three owner classes collapse to ordinary pair populations. Their covariance is rank one. The missing arithmetic must therefore control the active prime/composite imbalance relative to `w`, or couple that imbalance to `G_R` through a new occurrence-preserving theorem.

## H. Competing mechanisms

- **CONTINUE:** support-filtered inverse test (3)-(5).
- **REVISE:** `MECH-915-THREE-CLASS-RETURNED-INCIDENCE`; its unfiltered count statement is false.
- **PROMOTE:** residual coupling on exact active support.
- **ABANDON:** payment based on raw returned-carrier cardinalities.
- **KEEP DISTINCT:** Euler carry/phase, shared-gcd CRT covariance, OAI ideal Gram, CORR4, FINITE-AC, MU-LIFT, JOH, CODIV, and NYMAN until exact bridges exist.

## I. Specialist handoffs

**Coordinator:** mark the unfiltered form of `20261027-owner-1` `REFUTED` and replace it with `20261028-owner-1`. Do not use the old inverse inequality in the DAG.

**Lean Verification:** formalize the support filter first. The valuable theorem is (2)-(3), derived from arbitrary-site Fubini. Do not formalize raw-carrier counts as physical atoms.

**Adversarial Referee:** independently check the R=3 membership witness and the orientation/factor-two step in (2).

**Prime Census:** compute support-filtered `A_R,B_R,C*_R,P*_R,T*_R` and verify (2); also count zero-weight geometric records.

**Finite Wheel:** seek a restriction on the active population imbalance or unmatched residual. Raw clipped/admitted incidence is insufficient.

**Analytic Type II:** if using (4), prove a genuinely independent active-support balance range and separately control `G_R`.

## J. First independently missing lemma

The first clean, non-target-equivalent lemma is either:

1. an actual-support balance theorem

```text
(w^2*C*_R + (1-w)^2*T*_R)^2
  <= 36*w^2*(1-w)^2*C*_R*T*_R,
```

on a separately justified range; or

2. a one-sided theorem `G_R<=0`, or a quantified coupling of `G_R` to the imbalance, derived from the named anchor, diagonal, squareful-restoration, and omitted-seat summands.

Neither is proved here.

## K. Next-run resume capsule

Resume from main `a59d351aa33c3cc071ab7b9221f765dc89a2012c`, claim `20261028-owner-1`, and equations (1)-(5).

Continuity consumed:

- latest Coordinator available: `20261027-coordinator-1`, blob `b12989910667ec44b7cb5cb9e7395a6a5602f560` (`YESTERDAY=CARRY_FORWARD`);
- prior Owner: `20261027-owner-1`, blob `a559d88d6974ba3b9bd8f9a026058b15f2879309`, now refuted in its unfiltered form;
- Analytic: `20261027-analytic-1`, blob `0ab3dbac7df59b6fb4c1f35a29c010160cc42f3e`;
- Wheel: `20261028-wheel-1`, blob `27dd840bb424d551f2dce0beebd7b0d2f66622f0`;
- Census: `20261028-census-1`, blob `dca77bca7ed46d5d9fccbd05a565ed10c000a6c8`;
- Referee: `20261028-referee-1..2`, blob `fabec6a00f43ded6139256072d228024d62a015c`;
- Lean Verification: `20261028-lean-1`, blob `9698f817e44105033409f90d98b2e018cf727ac8`;
- external inbox: `038018145c0fddb2f6306c0712373adf9cd1ea52`, no newer handoff.

Today's Coordinator and Analytic reports were unavailable and are recorded `TODAY=PENDING`. No Lean source, proof branch, PR, workflow, schedule, or permission was modified.

## Publication verification

The early checkpoint was commit `5d5fc9a81934a7085c531c2f672d3f38ab7643c5`, read back as blob `8415387d4d3a5e28b646ccc554819402af9edc84`. The completed mathematical update was commit `06c78589dd4fbd9d3aba786e6a828c74b5b3424d`, read back as blob `dea7177f01001e020e46472681ea14ee186ef5a0`. This formatting-corrected publication is verified by the subsequent readback.

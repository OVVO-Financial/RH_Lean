# RH_Lean agent daily report - 2026-10-28 / RH | Owner Payment

**Status:** COMPLETED
**Invocation:** scheduled run begun 2026-10-28 20:43 America/New_York
**Final authority refresh:** 2026-10-28 America/New_York
**Pinned main:** `a59d351aa33c3cc071ab7b9221f765dc89a2012c`
**Authority blobs:** `AGENTS.md` `4bc5e5bacd333be41ca9334fa6eaf8e29b9bd1c8`; `CURRENT_PROOF_CONTRACT.md` `24bd727096001b68c76b28fe70c99b8d548d7bfe`; native-first routing `c9a74b1bf2727ff1522c27e9934f521671b128ae`.
**New claim:** `20261028-owner-1`
**Result classes:** `REFUTED` (the unfiltered-count form of `20261027-owner-1`), `PAPER_PROOF / CORRECTED SUPPORT-FILTERED LEDGER`, `IDENTITY_ONLY / RANK-ONE INCIDENCE INVARIANT`, `CONDITIONAL INVERSE RESTRICTION`, `NO_NEW_GLOBAL_QUANTITATIVE_BOUND`.

## A. Most important mathematical development

### Claim `20261028-owner-1`: geometric returned carriers must be support-filtered; after correction their three classes obey an exact rank-one incidence law

The unfiltered three-class count identity reported as `20261027-owner-1` is false. The definition
[
mathcal C_{R,p,sigma}=
	exttt{vfMidActiveReturnedPairCarrier} R p sigma
]
is the geometric product
[
	exttt{clippedBaseFiber}	imes	exttt{admittedBaseFiber}.
]
It is not the support of (	exttt{vfMidOneBlockActivePhysicalSite}). The compiled theorem
[
	exttt{vfMidActiveReturnedPairWeight_eq_physical}
]
says that a carrier member has weight (v_R(a)v_R(pc)), and either factor may be zero.

A literal counterexample is
[
R=3,quad p=3,quad sigma=arnothing,quad (a,c)=(7,1).
]
At clock (R+1=4), the common endpoint is (4^2-1=15). Both (7) and (1) are squarefree, (3)-free, and have empty lower-(3) signature; (3cdot7>15) and (3cdot1le15). Thus ((7,1)inmathcal C_{3,3,arnothing}). But the active band is ((9,16)), so (v_3(7)=v_3(3)=0), and the actual atom is zero. The old unfiltered classification assigned ((1-w_3)^2>0) (numerically (w_3=0.9238258189ldots)). This refutes equation (1) of `20261027-owner-1` with its stated counts.

The repair is exact. Filter every count by
[
ainmathcal A_R,qquad pcinmathcal A_R,
quad
mathcal A_R=	exttt{vfMidOneBlockActivePhysicalCarrier} R.
]
Call the resulting composite/composite, prime/composite, and prime/prime occurrence counts (C_R^*,P_R^*,T_R^*). Then
[
oxed{E_R=G_R+2w^2C_R^*-6w(1-w)P_R^*
                 +2(1-w)^2T_R^*.}	ag{1}
]
Moreover, if (A_R) and (B_R) are respectively the numbers of composite and prime sites in (mathcal A_R), unique least-owner Fubini gives
[
oxed{C_R^*=inom{A_R}{2},quad
       P_R^*=A_RB_R,quad
       T_R^*=inom{B_R}{2}.}	ag{2}
]
Hence these incidences are not independent:
[
oxed{(P_R^*)^2-4C_R^*T_R^*
       =A_RB_R(A_R+B_R-1)ge0.}	ag{3}
]

Equation (3) is the strongest new structural fact. It identifies the complete returned interaction as rank one at the population level. It also shows that a new same-block “covariance theorem” on only these three counts cannot contain information beyond the prime/composite population imbalance.

## B. Current authoritative objective

The canonical target remains
[
exists Cge0 orall Rge2,qquad
|pi(R^2)-VF_{m can}(R^2)|le CRlog R.
]
It is open. Native-first routing assigns this role the occurrence-faithful original #915 physical ledger and a nonlocal signed cross-owner restriction. Main now includes merged #1046 shared-gcd CRT covariance and #1047 moving Euler/OAI shell localization. Neither supplies a bridge to (1) or bounds (G_R).

Material source blobs checked:

- active returned raw-parent carrier: `dd872ccdf0eac1e78f998aa77f357f68df53f76e`;
- final returned Co/Div Fubini: `47e4255f76fb3387d1b12d0fa185cffde2744e63`;
- weighted global first-owner Fubini: `4679d7edae521dd4d9f0238aa4201445b1fdb9a9`;
- arbitrary-site cell Fubini: `c99074725868c1e4798d2539d86bb2f1a7912e60`;
- global ordered off-diagonal carrier: `6219eb830b7fe682e7f5fc01ccd4f5455b95c306`;
- active excess ledger: `c103b811dfe5ac4130c71134a93bb23793c11695`.

## C. Structural hypothesis investigated

**Hypothesis.** The three returned incidence counts might satisfy a new centered-square/covariance restriction strong enough to pay the returned source.

**Verdict.** Revised. They do satisfy the exact rank-one law (2)-(3), but this is a population identity, not an independent prime-distribution estimate. Its useful content is an inverse balance test; it cannot by itself control the residual (G_R).

## D. Mathematical derivation

Let (v_R(n)=	exttt{vfMidOneBlockActivePhysicalSite} R n). On the support-filtered carrier, the original physical charges are
[
v_R(n)=w-mathbf1_{mathbb P}(n).
]
For (c>1), the child (pc) is composite. For (c=1), the child is the prime (p). The impossible fourth support class (composite (a), (c=1)) is excluded because an active composite (a<(R+1)^2) has a prime factor below (R+1), while an active prime child (p) lies above (R^2); they cannot share the lower-(p) signature.

Thus the three nonzero products are
[
w^2,qquad -w(1-w),qquad (1-w)^2.
]
For the exact pointwise excess (mathcal E(z)=4z-2|z|),
[
mathcal E(w^2)=2w^2,quad
mathcal E(-w(1-w))=-6w(1-w),quad
mathcal E((1-w)^2)=2(1-w)^2.
]
Zero-weight geometric records contribute (mathcal E(0)=0). Applying the compiled global anchored equality proves (1).

For (2), the compiled first-owner Fubini partitions the full ordered off-diagonal common-clock carrier, while each cell is one orientation of the (p)-free/child crossing and the global theorem contributes the factor two. Restricting the arbitrary site to (mathcal A_R) therefore assigns each unordered distinct pair of active sites exactly once. Partitioning these pairs by prime/composite type gives the three binomial formulas. Expanding them proves (3).

Define
[
x=w^2C_R^*,quad y=(1-w)^2T_R^*,quad
z=w(1-w)P_R^*.
]
Equation (3) implies (z^2ge4xy). Therefore
[
(x+y)^2le36xyquadLongrightarrowquad x+yle3z,	ag{4}
]
and the complete returned contribution in (1) is nonpositive. Conversely, a positive returned contribution forces
[
(x+y)^2>36xy,	ag{5}
]
an extreme weighted population imbalance (with the usual zero-class endpoint interpretation).

## E. Quantitative consequence

There is no new all-scale exponent or canonical bound.

The independent consequence is an exact inverse restriction: under the explicit balance condition (4), a first-bad event (E_R>0) forces (G_R>0). Thus a hypothetical failure cannot be attributed to the returned three-class carrier unless the weighted prime/composite populations are extremely imbalanced as in (5); otherwise the obstruction lies in the quarantined anchor/diagonal/squareful/omitted-seat residual.

This is a structural localization, not payment. Proving (4) uniformly is a prime-distribution statement on the actual active support; bounding (G_R) remains separate.

## F. Falsification and circularity review

1. **Carrier/support confusion:** explicitly refuted by ((R,p,sigma,a,c)=(3,3,arnothing,7,1)).
2. **No cloned history:** support filtering changes only whether an existing geometric record has zero physical weight; it introduces no occurrence.
3. **All cross terms retained:** (1) starts from the complete anchored equality and (2) uses the full off-diagonal Fubini.
4. **Diagonal not hidden:** binomial counts are off-diagonal; diagonal and restoration remain in (G_R).
5. **No arbitrary independence:** (3) is deterministic and exact.
6. **No target-equivalent promotion:** the balance condition and (G_R) sign are unproved. They are not reported as a source estimate.
7. **Euler sparsity not imported:** `20261028-referee-1` proves exact-zero carry incidence has no amplitude effect on its complement; there is no carrier bridge to (1).
8. **Finite check scope:** the (R=3) witness refutes the universal unfiltered identity. Its numerical (w_3) evaluation is only used to display the nonzero discrepancy; the structural zero follows directly from the definitions.

## G. Conceptual interpretation

First-owner chronology does two things exactly: it orients each active off-diagonal pair once and preserves its physical weight. It does not make the larger clipped/admitted product an active support.

After the necessary support filter, the three “owner incidence” classes collapse to ordinary pair populations. Their covariance is rank one, so the missing arithmetic cannot come from treating (C^*,P^*,T^*) as independent random sectors. A genuine advance must control the active prime/composite population relative to (w), or couple that imbalance to the residual (G_R) through a new occurrence-preserving theorem.

## H. Competing mechanisms

- **CONTINUE:** support-filtered rank-one inverse test (3)-(5) as a falsification gate.
- **REVISE:** `MECH-915-THREE-CLASS-RETURNED-INCIDENCE`; its unfiltered count statement is false.
- **PROMOTE:** a residual-coupling theorem using the exact active support, not geometric-carrier cardinality.
- **ABANDON:** any payment based on raw (mathcal C_{R,p,sigma}) class counts.
- **KEEP DISTINCT:** Euler carry/phase, shared-gcd CRT covariance, OAI ideal Gram, CORR4, FINITE-AC, MU-LIFT, JOH, CODIV, and NYMAN until exact bridges are proved.

## I. Specialist handoffs

**Coordinator:** mark the unfiltered form of `20261027-owner-1` REFUTED and replace it with `20261028-owner-1`. Do not use its old inverse inequality in the DAG.

**Lean Verification:** formalize a support predicate or filter first. The useful exact theorem is (2)-(3), derived from the existing arbitrary-site Fubini. Do not formalize raw-carrier counts as physical atoms.

**Adversarial Referee:** independently check the (R=3) membership witness and the orientation/factor-two step in (2).

**Prime Census:** compute support-filtered (A_R,B_R,C_R^*,P_R^*,T_R^*) and verify (2) exactly; additionally report the number of zero-weight geometric carrier records to measure how badly the old counts overcount.

**Finite Wheel:** seek an arithmetic restriction on the active population imbalance or on the unmatched residual. Raw clipped/admitted incidence is insufficient.

**Analytic Type II:** if using (4), prove a genuinely independent balance range from the physical prime/composite support and separately control (G_R). A bound defined by (E_Rle0) is circular.

## J. First independently missing lemma

The first clean non-target-equivalent lemma is one of:

1. an actual-support balance theorem
[
igl(w^2C_R^*+(1-w)^2T_R^*igr)^2
 le36w^2(1-w)^2C_R^*T_R^*,
]
on a separately justified range; or

2. a one-sided theorem (G_Rle0) (or a quantified coupling of (G_R) to the imbalance) derived from the named anchor, diagonal, squareful-restoration, and omitted-seat summands.

Either must use the exact physical support and preserve every occurrence once. Neither is proved here.

## K. Next-run resume capsule

Resume from main `a59d351aa33c3cc071ab7b9221f765dc89a2012c`, claim `20261028-owner-1`, and equations (1)-(5).

Continuity consumed:

- latest Coordinator available: `20261027-coordinator-1`, blob `b12989910667ec44b7cb5cb9e7395a6a5602f560` (`YESTERDAY=CARRY_FORWARD`);
- prior Owner: `20261027-owner-1`, blob `a559d88d6974ba3b9bd8f9a026058b15f2879309`, now corrected/refuted in its unfiltered form;
- Analytic: `20261027-analytic-1`, blob `0ab3dbac7df59b6fb4c1f35a29c010160cc42f3e`;
- Wheel: `20261028-wheel-1`, blob `27dd840bb424d551f2dce0beebd7b0d2f66622f0`;
- Census: `20261028-census-1`, blob `dca77bca7ed46d5d9fccbd05a565ed10c000a6c8`;
- Referee: `20261028-referee-1..2`, blob `fabec6a00f43ded6139256072d228024d62a015c`;
- Lean Verification: `20261028-lean-1`, blob `9698f817e44105033409f90d98b2e018cf727ac8`;
- external inbox: `038018145c0fddb2f6306c0712373adf9cd1ea52`, no handoff newer than 2026-10-18.

Today's Coordinator and Analytic reports were not available at the verified intake and are recorded `TODAY=PENDING`. No Lean source, proof branch, PR, workflow, schedule, or permission was modified.

## Publication verification

The early `IN_PROGRESS` checkpoint was created by commit `5d5fc9a81934a7085c531c2f672d3f38ab7643c5` and read back as blob `8415387d4d3a5e28b646ccc554819402af9edc84`. Final publication verification follows this update.

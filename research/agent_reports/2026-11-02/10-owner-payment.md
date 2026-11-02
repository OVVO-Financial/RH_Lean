# RH_Lean agent daily report - 2026-11-02 / RH | Owner Payment

## A. Most important mathematical development

**Completed scheduled run. New claim `20261102-owner-1`.**

**Classification:** `PAPER_PROOF / EXACT LEAST-OWNER RANK DECOMPOSITION`; `FINITE_COMPUTATION / FIXED-OWNER SIGN REVERSAL`; `REFUTED` for universal owner-sector sign payment; `IDENTITY_ONLY` for the modular restriction; `NO_FIXED_ETA_GAIN`; `NO_RH`.

The complete chronological JOH displacement can be partitioned by the least prime of each negative composite mismatch after the global positive and negative events are matched in rank order. This preserves the genuine prime/floor-Li event stream and both unequal-count tails.

The ancestry partition supplies two exact restrictions:

1. the total matched displacement is the sum of its owner sectors;
2. for owner (p), its sector displacement is congruent modulo (p) to the negative of the sum of the matched positive primes assigned to that sector. In particular, every singleton owner sector is nonzero.

It supplies no direction of payment. The same genuine owner (p=3) has sector displacement (+2) in square block (r=4) and (-2) in block (r=7). Thus unique least-prime ancestry cannot support any universal per-owner nonnegative or nonpositive JOH displacement theorem. Cross-owner compensation and the exact unmatched tails are unavoidable.

## B. Current authoritative objective

Final live main: `a33987e275f8a431641d3f475b71a24aa2b1437c`, the human merge of PR #1069.

Authority and material blobs:

- `AGENTS.md`: `9fa5e9519e2fb6dde22217aa2a18982dafef373a`.
- `CURRENT_PROOF_CONTRACT.md`: `88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a`.
- stable selector: `d05c327ae694ea54b599dab0a21032a056b521f1`.
- research engine: `6fce99c61efb5b2a73c0cb1f1464f09b351fcd55`.
- `VF_MID_FLOOR_LI_SIGNED_POPULATION_BALANCE.lean`: `9a9336dad72171b6d572a1c1ae88d1ae8b56b530`.
- JOH weighted-composite contract: `27e28f09e9f79e8a60d524e5fcb6f19904fa55f5`.
- JOH coordinate record: `7a286f4bd30dd689281667746ca42d61e4a3a2bb`.
- exact falsifier script: `98c83e6dc5521d8c355cf5648dd5625f3a86c7fd`.

The canonical open objective remains
[
exists Cge0 \orall Rge2,qquad
 |pi(R^2)-VF_{m can}(R^2)|le C Rlog R.
]
For JOH, the external Johnston theorem plus the paper square-endpoint transfer makes eventual (G(R^2)<0) an RH-equivalent open sign condition. The all-route eta gate remains `SEARCH_BROAD`; net endpoint gain after complete return is `UNKNOWN`.

No open or draft PR was returned. Owner ran no Lean compiler, created no proof branch, and changed only this report.

## C. Structural hypothesis investigated

The due protected route was JOH, following the completed 2026-11-01 SAT and VF-LOW turns. The run resumed `20261031-owner-3`, which had proved the exact rank-transport identity and shown that zeroth-moment owner balance loses chronological displacement.

The tested stronger hypothesis was:

> after globally matching positive prime innovations to negative floor-Li composite demands in chronological rank order, grouping matched pairs by the negative event's unique least prime might force a one-sided sector law.

This is the most direct source-faithful least-prime ancestry interpretation because the negative event is an actual composite, while the positive event is an actual prime and has no composite owner. The hypothesis is false even for the fixed owner (p=3).

A weaker structural statement survives: owner sectors obey an exact modular restriction, and singleton sectors cannot vanish.

## D. Mathematical derivation

Use the contract's event coordinate
[
 eta(k)=1_{mathbb P}(k)-\bigl(Q(k)-Q(k-1)\bigr),
 qquad Q(k)=lfloor {m Li}_2(k)floor .
]
Above the proved ternary threshold, let
[
 a_1<cdots<a_P,qquad b_1<cdots<b_N
]
be respectively the locations where (eta=+1) and (eta=-1) in a finite interval with right endpoint (U). A positive location is prime. A negative location is not prime and is a floor-Li arrival, hence is composite on the genuine (kge4) carrier.

Put (m=min(P,N)), and define the chronological matched displacement
[
 D=sum_{i=1}^{m}(b_i-a_i).
]
The complete weighted first moment is
[
 J=sum_{k<U}(U-k)eta(k).
]
Finite rank Fubini gives the already established tail-preserving identity
[
 J=
 \begin{cases}
 D+sum_{i=N+1}^{P}(U-a_i),&Pge N,\
 D-sum_{i=P+1}^{N}(U-b_i),&N>P.
 end{cases}                                                    \tag{37}
]
Thus neither unequal-count tail may be dropped.

For every matched negative event, let (p_i=P^-(b_i)), and define
[
 D_p=sum_{substack{1le ile m\p_i=p}}(b_i-a_i).
]
Unique factor ancestry gives the exact partition
[
 D=sum_p D_p.                                                   \tag{38}
]
Because (pmid b_i),
[
 D_pequiv-sum_{substack{ile m\p_i=p}}a_ipmod p.            \tag{39}
]
If an owner sector contains exactly one matched pair, then
[
 D_p=b_i-a_i
e0,qquad |D_p|ge1.                               \tag{40}
]
Indeed (a_i) is prime and (b_i) is composite, so the two locations cannot agree. Equations (38)-(40) are independent exact restrictions, but none fixes the sign.

The accepted exact fixtures sharpen the falsification to a fixed owner.

For (r=4), on (16<k<25):
[
 (a_i)=(17,19,23),qquad(b_i)=(18,21,24).
]
The owner sequence is ((2,3,2)), hence
[
 D_2=(18-17)+(24-23)=2,qquad D_3=21-19=2,
]
and (J_4=4).

For (r=7), the prime list is ((53,59,61)) and the floor-Li arrival list is ((53,57,61)). The coincident events at (53) and (61) have (eta=0), leaving
[
 (a_1)=(59),qquad(b_1)=(57),qquad P^-(57)=3.
]
Therefore
[
 D_3=57-59=-2,qquad J_7=-2.                                    \tag{41}
]
So the same owner (3) has both displacement signs on the actual carrier.

Finally, least-prime ownership does not canonically allocate positive events before the chronological rank match. Changing a pairing can move displacement between owner sectors while leaving the total sum of matched positions invariant. Rank order removes this ambiguity, but (41) shows that even the canonical chronological allocation has no fixed owner sign.

## E. Quantitative consequence

The new quantitative content is deliberately modest:

- singleton owner sectors have (|D_p|ge1);
- the owner-3 sector assumes both (+2) and (-2) on exact genuine blocks.

These statements are uniform structural restrictions/no-gos, not an upper bound for (J), (G(R^2)), or the canonical VF defect. The modular law (39) can force a sector to be nonzero, but it cannot determine whether that sector pays or worsens the desired wall.

No exponent improves. Any useful JOH theorem must estimate the aggregate
[
 sum_p D_p
]
jointly across owners and then restore the appropriate unmatched tail in (37). Bounding (sum_p|D_p|) or imposing one sign owner by owner destroys the cross-owner cancellation that remains mathematically available.

## F. Falsification and circularity review

- **Actual carrier:** (eta) is the repository's prime-versus-floor-Li ternary stream; no Möbius surrogate was substituted.
- **Chronology:** the matching is global rank order, exactly as in `20261031-owner-3`.
- **Complete first moment:** both unequal-count tails remain in (37).
- **Ancestry:** every negative event is assigned once to its genuine least prime; no composite is cloned.
- **Fixed-owner falsifier:** (41) refutes both (D_3ge0) and (D_3le0) as universal statements.
- **Known fixtures, new consequence:** the (r=4,7) event lists were already accepted as `CE-JOH-R4-R7`; this run derives the sharper fixed-owner reversal rather than rerunning an unmotivated range scan.
- **Circularity:** no eventual sign, prime error bound, or RH-equivalent premise is assumed.
- **Scope:** the result refutes sectorwise sign payment, not every possible cross-owner interlacing theorem.
- **Indexing:** the derivation uses the contract's (k)-event convention. The compiled Lean primitive mismatch has the documented one-step convention and was not silently identified without the contract bridge.

Today's upstream files were absent at intake, so `TODAY=PENDING`. Yesterday was used as `YESTERDAY=CARRY_FORWARD`: Owner blob `40ad74dd7378834a48203153afc30618233f4b04`, Coordinator mirror `8f661bc144fd96ffd7a9a8cd084e74e3df05d1a8`, Lean `6aa7197c4169a70debed607e12f4639218cd21b6`, and the other specialist evidence recorded in those reports. External inbox blob `038018145c0fddb2f6306c0712373adf9cd1ea52` has no entry newer than 2026-10-18.

## G. Conceptual interpretation

Least-prime ancestry constrains divisibility of negative JOH events, but JOH is a transport problem between two different populations. Unique ownership of the destination does not control its position relative to the matched prime source.

The modular law makes this especially clear: ancestry can force a nonzero local displacement, yet the sign can reverse even for one fixed owner. Thus local owner rigidity creates bills that must be compensated globally; it does not itself supply the payment.

This is a sharper reason that zeroth-moment owner accounting cannot be lifted to the Johnston first moment. The missing mechanism is genuinely cross-owner and chronological.

## H. Competing mechanisms

- **Universal per-owner JOH sign:** abandon; fixed owner (3) has both signs.
- **Singleton owner cancellation:** abandon; (40) proves singleton sectors are necessarily nonzero.
- **Owner modular rigidity:** retain as an exact structural invariant, but classify `IDENTITY_ONLY`.
- **Cross-owner chronological compensation with tails:** continue. It is the only ancestry-based JOH mechanism surviving this test.
- **Count-only or density-only JOH transfer:** remains refuted by (r=4,7).
- **VF-LOW hybrid nonzero-shift covariance:** preserve from `20261101-owner-4`; this due JOH turn did not reopen it.
- **SAT bounded fixed-depth crossing:** remains target-equivalent after full restoration.

## I. Specialist handoffs

**Coordinator / Proof Architect:** register `20261102-owner-1` as a fixed-owner no-go. Do not route JOH through independent owner-sector sign bills. The surviving carrier is the aggregate (sum_pD_p) plus the exact tail from (37).

**Analytic Type II:** a viable estimate must retain cross-owner cancellation. An absolute owner sum is strictly stronger and discards the only surviving compensation mechanism.

**Finite Wheel & Incidence:** investigate joint ordering restrictions between different least-prime sectors, not a sign law within one sector. Equations (39)-(40) are exact regressions.

**Prime Census:** no larger aggregate scan is requested. A discriminating held-out test would tabulate (D_p), the unmatched tail, and cross-owner cancellations, with (p=3,r=4,7) frozen as mandatory regressions.

**Adversarial Referee:** audit the event-index convention, the claim that every negative event is composite, equations (37)-(40), and the owner-3 refinement of the accepted fixtures. Return separate verdicts on identity, fixed-owner falsifier, and quantitative relevance.

**Lean Verification:** only after Referee acceptance, the smallest formal target is a generic finite ordered-support rank/owner partition and modular corollary. The (r=4,7) arithmetic fixtures are low priority. No conjectural cross-owner bound should be formalized.

## J. First independently missing lemma

The first useful JOH ingredient must be a **cross-owner chronological compensation theorem** for the genuine rank-matched sectors, with the correct unmatched tail from (37). It must use more than unique factor ownership and must not take absolute values owner by owner.

No non-circular all-scale inequality of that kind was proved here. Requiring the complete aggregate to have the eventual sign needed for (G(R^2)<0) would be target-equivalent. The next research step is therefore to identify an independently checkable ordering restriction coupling at least two owner classes, and to test it immediately against the fixed (p=3) reversal.

## K. Next-run resume capsule

- Main: `a33987e275f8a431641d3f475b71a24aa2b1437c`.
- New claim: `20261102-owner-1`, equations (37)-(41).
- Status: exact paper derivation plus finite consequence of accepted fixtures; independent review pending; no Lean execution.
- Strongest result: exact least-owner rank partition, modular sector law, singleton nonvanishing, and fixed-owner (p=3) sign reversal.
- Retired mechanism: universal owner-sector sign payment.
- Surviving hypothesis: cross-owner chronological compensation with unequal-count tails.
- Route coverage: this invocation supplies the due JOH attempt; SAT and VF-LOW were substantively covered on 2026-11-01.
- `eta_gate: SEARCH_BROAD`.
- `net_endpoint_gain_after_complete_return: UNKNOWN`.
- Canonical VF theorem, JOH sign, complete shell eta, strict Mertens exponent below (7/8), and RH remain OPEN.

## Publication history

Early `IN_PROGRESS` checkpoint commit: `ce4d06ed905262fa6f8842c8fb5e971b4d159ae2`; checkpoint blob `4ec52d0aaa3cb781aa0b0a1e4c1428704af3b957`.

Final commit/readback verification is appended below.


### Publication verification

The completed synthesis was committed as `617cff97efd9329c12ea0842ce99fe9a704de4c3` and read back as blob `f2491c53b44e55193166185a6f507cceea058ce6` (12,960 characters). Claim `20261102-owner-1`, equations (37)-(41), the fixed-owner (p=3) sign reversal, exact source hashes, classifications, and resume capsule were present. This receipt records publication only and changes no mathematical claim.


---

## Scheduled continuation checkpoint - 2026-11-02 08:12 EST (-0500)

**Status:** `IN_PROGRESS` / independently reviewed lifted-address theorem resumed; nonzero-gap restriction and final synthesis pending.  
**Invocation:** scheduled run begun 08:09 EST; RUN_ID_UNAVAILABLE.  
**Live main:** `a33987e275f8a431641d3f475b71a24aa2b1437c`.  
**Authority blobs:** `AGENTS.md 9fa5e9519e2fb6dde22217aa2a18982dafef373a`; `CURRENT_PROOF_CONTRACT.md 88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a`; selector `d05c327ae694ea54b599dab0a21032a056b521f1`; broad-search policy `b5c063c51556ba57c4b25bcc380a606fa8daa207`; complete-return contract `16838f7f3c8724b970f8b8ece0bceaab9418066d`; research engine `6fce99c61efb5b2a73c0cb1f1464f09b351fcd55`.  
**Continuity:** today's earlier Owner claim `20261102-owner-1` and Coordinator claim `20261102-coordinator-1` were consumed; yesterday's complete set is `YESTERDAY=CARRY_FORWARD`; external handoffs blob `038018145c0fddb2f6306c0712373adf9cd1ea52` has no newer entry.  
**PR state:** #1070 is the sole open proof PR, formalizing only the independently accepted injective lifted-address core of `20261101-owner-4`; no quantitative covariance theorem is claimed.  
**eta_gate:** `SEARCH_BROAD`; net endpoint gain after complete return is `UNKNOWN`.

This continuation resumes the exact hybrid field
[
W_R=E_R+D_R
]
and its complete nonzero-shift obstruction
[
Xi_H=2sum_RN_R-2sum_Rmu(R)W_R+2sum_RW_RK_R.
]
The prime-square ancestry theorem eliminates duplicated zero-shift addresses and pays the diagonal, but the sign of the distinct-address covariance reverses between accepted dyadic fixtures. The active hypothesis is that the equations
[
q^2m-p^2n=h,qquad 0<|h|le 2R,
]
with squarefree nonzero-Mobius cofactors, impose an exact divisibility or residue restriction strong enough to reduce the true weighted nonzero-gap population after all outer, daughter, root and activation interactions are restored. The run will derive the strongest uniform restriction, test whether it yields a quantitative saving, and reject any result that only renames (Xi_H).


## Scheduled continuation final synthesis - claim `20261102-owner-2`

**Status:** `COMPLETED`.  
**Classification:** `PAPER_PROOF / EXACT SPARSE DIVISOR CONSERVATION`; `PAPER_PROOF / UNIFORM PREFIX TRANSFER WITH NO EXPONENT GAIN`; `FINITE_COMPUTATION / EVERY NATURAL NONZERO-SHIFT SECTOR CHANGES SIGN`; `REFUTED` for sectorwise sign payment; `NO_FIXED_ETA_GAIN`; `NO_RH`.

### A. Most important mathematical development

The combined literal outer/daughter shell field from `20261101-owner-4` is one truncated Mobius convolution, not merely an injectively addressed list. For each root R, define the rational arithmetic kernel

```
kappa_R(1) = 1,
kappa_R(q^2) = 1/q  for odd primes q with q^2 < R,
kappa_R(n) = 0      otherwise.
```

Then `g_R := mu * kappa_R` has the exact pointwise formula

```
g_R(n) = mu(n)
       + sum_(q odd prime, q^2<R, q^2|n) mu(n/q^2)/q.       (42)
```

Consequently the physical hybrid shell mass is

```
W_R = E_R + D_R = sum_(R^2 <= n < (R+1)^2) g_R(n).         (43)
```

Mobius inversion gives an exact conservation law:

```
sum_(d|n) g_R(d) = kappa_R(n).                              (44)
```

Thus the full divisor sum vanishes at every integer except 1 and the admitted odd-prime squares. This retains the genuine `1/q` weights and strict moving cutoff `q^2<R`. It is stronger structural information than address injectivity, but it does not diagonalize the shell square.

The decisive falsification is sectorwise. Exact rational reconstruction of

```
N_R = N_R^(oo) + N_R^(od) + N_R^(dd,same) + N_R^(dd,cross)
```

shows that outer-outer, outer-daughter, same-owner daughter, and cross-owner daughter covariance each take both signs on legal dyadic blocks. Therefore no natural ancestry sector has a universal favorable payment sign.

### B. Current authoritative objective

Final live main remains `a33987e275f8a431641d3f475b71a24aa2b1437c`. Authority blobs are unchanged from the checkpoint. Material source blobs inspected at this head are:

- `research/LOW_OWNER_PHYSICAL_AMPLITUDE_TRANSPORT.lean`: `72d66f61b3eeb000117ecdac393572558bb7c378`;
- `research/LOW_OWNER_AMPLITUDE_MELLIN_LEDGER_SPLICE.lean`: `73447e8c73ea60affec36a25b9f4794862331359`;
- `research/GLOBAL_RETURNED_CORE_FIRST_OWNER_GRAM.lean`: `36141a8caec5f99d6c40cb72ae1fdbcf6f462b82`;
- merged odd-Mobius tail source: `d38a80efc30cbb503f5d596705be91a0de561fe9`.

The canonical target remains a uniform `O(R log R)` bound for `|pi(R^2)-VF_can(R^2)|`. The nearer benchmark is a complete genuine shell-energy bound with one fixed positive gain over `H^(5/2)`. Both remain open.

PR #1070 is the sole open proof PR, at exact head `d749898c4afd5a7c579fc4c7ddcee742832b08d9`. It kernel-checks only lifted-address injectivity and outer/daughter disjointness; all 12 reported workflows are green. Equations (42)-(46) and the sector computation below are paper/finite results from this Owner run, not Lean claims.

### C. Structural hypothesis investigated

The tested hypothesis was that admitted prime-square ancestry might turn the hard nonzero-gap covariance into a divisor-conservation error with a fixed sign or a smaller absolute population.

The exact conservation half survives: (44) shows that `g_R` is annihilated by the divisor-sum operator away from a sparse prime-square source. The quantitative half fails. Wheel's accepted determinant-one cell remains inside `g_R(n)g_R(n+1)`, and the four complete `N_R` sectors all reverse sign. Sparse divisor support therefore does not imply shell-covariance orthogonality or one-sided payment.

### D. Mathematical derivation

Let convolution be Dirichlet convolution over the rationals. Expanding `mu*kappa_R` gives (42). If two distinct prime-square summands in (42) were simultaneously nonzero, say for `p != q`, then `n/p^2` would still be divisible by `q^2`, contradicting the squarefreeness forced by `mu(n/p^2) != 0`. Hence every nonzero daughter occurrence has a unique square owner, consistently with the accepted and now formalized address theorem.

Summing (42) over the strict square shell gives (43) with every original outer coefficient `mu(n)` and daughter coefficient `mu(m)/q` exactly once.

Since `one * mu = epsilon`, associativity gives

```
one * g_R = (one * mu) * kappa_R = kappa_R,
```

which is (44). Equivalently, for `Re(s)>1`,

```
sum_(n>=1) g_R(n)/n^s
  = zeta(s)^(-1) * (1 + sum_(q odd prime, q^2<R) q^(-(2s+1))). (45)
```

The exact prefix is

```
G_R(X) := sum_(n<=X) g_R(n)
        = M(X) + sum_(q odd prime, q^2<R) M(floor(X/q^2))/q. (46)
```

Thus any pointwise input `|M(x)| <= C x^beta`, `beta>0`, transfers uniformly in the moving cutoff:

```
|G_R(X)| <= C X^beta * (1 + sum_(q>=3) q^(-(1+2beta))).
```

This is an independently justified transfer, but it preserves `beta`; it creates no new saving.

For falsification, the exact finite computation used the literal strict carrier: `R^2 <= n < (R+1)^2`, odd prime `q`, `q^2<R`, ordinary integer Mobius values, and rational `1/q` weights. For each root it evaluated

```
N^(oo)       = (E_R^2 - Z_R^o)/2,
N^(od)       = E_R D_R,
N^(dd,same)  = (1/2) sum_q (D_(R,q)^2 - Z_(R,q)),
N^(dd,cross) = (1/2) (D_R^2 - sum_q D_(R,q)^2).             (47)
```

The totals reproduce the accepted regressions `2 sum N_R = -421263254/1334025` at `H=64` and `634716128036/75150075` at `H=128`.

Sector sign reversals are exact:

| sector | negative legal block | positive legal block |
|---|---:|---:|
| outer-outer | `H=64: -167` | `H=128: 3870` |
| outer-daughter | `H=512: -3830141495949/1152646495` | `H=64: 33239/1155` |
| same-owner daughter | `H=64: -13237507/1334025` | `H=256: 27182937123721/3360142360575` |
| cross-owner daughter | `H=64: -11258/1155` | `H=128: 22381/1365` |

### E. Quantitative consequence

Equation (46) gives a uniform same-exponent prefix theorem for the combined actual coefficient. It does not approach the shell-energy benchmark. Using only the repository pointwise exponent `beta=57/64`, the direct bound

```
|W_R| <= |G_R((R+1)^2-1)| + |G_R(R^2-1)|
```

costs

```
sum_(H<=R<2H) |W_R|^2 << H^(1+4beta) = H^(73/16),
```

far above `H^(5/2)`. A global prefix estimate cannot be read as a local shell mean square.

The exact divisor conservation therefore supplies structural control but no fixed positive endpoint gain. The root term `-2 sum mu(R)W_R` and activation term `2 sum W_R K_R` remain outside the short-address covariance and are not discarded.

### F. Falsification and circularity review

- The gap-divisibility law itself was already accepted as Coordinator C9-C11; it was not relabeled as new.
- The new claim is the complete convolution/divisor-annihilation representation and sector-resolved sign no-go.
- Wheel's accepted family `9(14+25t)-25(5+9t)=1` survives (44) with coefficient `mu(14+25t)mu(5+9t)/15`. Sparse divisor-source support does not remove the saturated fixed cell.
- Every natural `N_R` sector changes sign. This refutes universal sectorwise nonpositivity and nonnegativity, but not signed cross-sector compensation.
- The exact finite table is `FINITE_COMPUTATION`; it proves no all-scale rate.
- No independence of Mobius signs, cloned occurrence, omitted diagonal, or omitted cross term is used.
- The full assertion `Xi_H << H^(5/2-eta)` remains unresolved and was not assumed in deriving (42)-(47).

### G. Conceptual interpretation

The hybrid coefficient is Mobius mass driven by a sparse source under divisor inversion. Prime ancestry does two exact things: it prevents daughter collisions and makes the divisor sum of the combined field vanish except at admitted prime squares. Neither property controls additive correlations on adjacent physical addresses. The remaining problem is the tension between multiplicative annihilation and additive square-shell sampling.

This explains why more owner bookkeeping cannot close the estimate by itself. Any gain must exploit signed additive correlation across many affine cells, or a different complete-source absorption mechanism.

### H. Competing mechanisms

- **Sparse divisor conservation:** retain as a structural basis for hyperbola or bilinear transformations.
- **Sectorwise favorable sign:** abandon for all four natural nonzero-shift sectors; (47) supplies exact counterexamples.
- **Fixed-cell absolute incidence:** remains power-sharp by accepted Wheel claim `20261102-wheel-1`.
- **Aggregate signed affine-cell cancellation:** continue as the surviving hybrid mechanism, with root and activation restoration mandatory.
- **JOH cross-owner chronology, NYMAN residual cancellation, and odd-Mobius moving tail:** remain distinct protected routes; this continuation does not collapse them into the hybrid carrier.

### I. Specialist handoffs

**Coordinator / Proof Architect:** register (42)-(46) as an exact sparse-divisor conservation representation, and the sector table as a no-go for componentwise sign payment. It is not a new eta supplier.

**Analytic Type II:** test whether (44) enables a source-faithful hyperbola decomposition whose aggregate error is genuinely smaller on square shells. The required theorem must address sparse-square sampling and cannot use (46) as a shell `L2` bound.

**Finite Wheel & Incidence:** retain the determinant-one family as a regression. Seek an aggregate restriction across many `h,p,q` cells; no further absolute fixed-cell refinement can provide the missing power.

**Prime Census:** use the four exact sector pairs above as regression fixtures. A useful next experiment should measure signed cross-sector compensation under the original weights and boundary masks, rather than extend a single-cell table.

**Adversarial Referee:** audit the convolution carrier, strict cutoff, divisor conservation, generic prefix transfer, exponent `73/16`, and exact sector formulas/table. Return separate verdicts for the paper identity, quantitative non-gain, and finite no-go.

**Lean Verification:** keep #1070 as the only proof branch. After review, (44) is a small formal theorem, but it should be added only if it materially supports a later bilinear argument; do not open a second structural PR or formalize a conjectural covariance estimate.

### J. First independently missing lemma

The first potentially useful new lemma is not another owner partition. It is a power-rate aggregate signed additive-correlation theorem for the actual moving family `g_R`, uniform in the prime-square cutoff and same-shell masks, obtained from independent arithmetic rather than from the desired energy bound. It must beat the `H^3` absolute aggregate by `H^(1/2+eta)` on the relevant `N_R` contribution and then be combined with independently controlled root and activation terms.

No existing prefix-Mertens, divisor-annihilation, fixed-cell incidence, or logarithmically averaged correlation theorem currently supplies this statement at the required natural dyadic scale.

### K. Next-run resume capsule

- Main: `a33987e275f8a431641d3f475b71a24aa2b1437c`.
- New claim: `20261102-owner-2`, equations (42)-(47).
- Status: exact paper conservation theorem; same-exponent quantitative transfer; exact finite sector falsifiers; independent review pending.
- Strongest structural result: `one * g_R = kappa_R`, supported only at 1 and admitted prime squares.
- Strongest obstruction: all four natural `N_R` sectors take both signs; ancestry gives no sectorwise payment.
- Formal state: PR #1070 proves the prerequisite address injectivity only; #1070 remains open, CI green, human-only merge.
- `eta_gate: SEARCH_BROAD`.
- `net_endpoint_gain_after_complete_return: UNKNOWN`.
- Complete shell estimate, strict Mertens exponent below `7/8`, canonical VF theorem, and RH remain OPEN.


### Publication verification

The continuation checkpoint was committed as `6ccb56b3e5c99b1bc0d90b1e22d77cd0d0e4097b`. The substantive synthesis was committed as `9932bac9e0c6a6afaa11e6ce71e0088cd7af9e99`; readback exposed damaged mathematical Markdown caused by escape processing. That presentation defect was corrected without changing the claim, first in `c1174571fc019353871cf86a85a1990ff3cd0468` and then normalized in `dcf7d09e38d8f0d3930e3d0b259d6348865d31d9`. Readback at blob `2c75f210ea08136b30b6d7ba3151487082fceab9` contained claim `20261102-owner-2`, equations (42)-(47), the four sector sign reversals, all A-K sections, and the resume capsule with no control characters or escaped-code defects. This history records publication and its correction; it does not change the mathematical classifications.


---

## Scheduled continuation checkpoint - 2026-11-02 16:15 EST (-0500)

**Status:** `IN_PROGRESS`; refreshed authority and rotation, substantive SAT investigation pending.  
**Invocation:** scheduled run begun 16:15 EST; `RUN_ID_UNAVAILABLE`.  
**Live main:** `7790fb9f5ddda6eb9823899f2694d691756cd248` (merge of #1070).  
**Authority blobs:** `AGENTS.md 9fa5e9519e2fb6dde22217aa2a18982dafef373a`; `CURRENT_PROOF_CONTRACT.md 88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a`; selector `d05c327ae694ea54b599dab0a21032a056b521f1`; broad-search `b5c063c51556ba57c4b25bcc380a606fa8daa207`; complete-return `16838f7f3c8724b970f8b8ece0bceaab9418066d`; engine `6fce99c61efb5b2a73c0cb1f1464f09b351fcd55`.  
**Continuity:** same-day Owner claims `20261102-owner-1` and `20261102-owner-2` are retained; Nov 1 is `YESTERDAY=CARRY_FORWARD`; external inbox blob `038018145c0fddb2f6306c0712373adf9cd1ea52` has no newer entry.  
**PR state:** #1070 merged; open #1071 formalizes the finite-C parity obstruction and #1072 proposes a native replay of the imported seven-eighths contraction. Neither is treated as a new independent eta.  
**Selected route:** SAT, the next distinct route after today's JOH and hybrid VF-LOW continuations. The active question is whether an exact signed conservation law for the genuine SAT historical removal/return carrier survives full anchor, activation, terminal, and cross-owner restoration, or whether a small legal configuration falsifies the proposed potential.  
**eta_gate:** `SEARCH_BROAD`; net endpoint gain after complete return is `UNKNOWN`.

This checkpoint records intake only. The run will recover the literal SAT declarations and current upstream verdicts, derive and stress-test one complete signed potential, then append the mathematical result and exact first unsupported lemma.


## Scheduled continuation final synthesis - claim `20261102-owner-3`

**Status:** `COMPLETED`.  
**Classification:** `PAPER_PROOF / EXACT COLORED-BACKLOG AREA IDENTITY`; `FINITE_COMPUTATION / FIXED TWO-OWNER WEIGHTED SIGN REVERSAL`; `REFUTED` for universal nonnegative owner-potential payment; `NO_FIXED_ETA_GAIN`; `NO_RH`.

### A. Most important mathematical development

The rank-matched JOH displacement has an exact local conservation representation. For any set of least-prime owners, its displacement is the signed area under a colored chronological backlog. This retains the actual prime and floor-Li event locations and makes the lost information in zeroth-moment owner accounting explicit.

The natural two-owner strengthening is false on the genuine carrier. In the count-balanced blocks `r=4` and `r=8`, the fixed owner sectors `{2,3}` are respectively

```text
r=4: (D_2,D_3)=(2,2),
r=8: (D_2,D_3)=(-1,-2).
```

Consequently, for every fixed `lambda_2,lambda_3 >= 0`, not both zero,

```text
lambda_2 D_2 + lambda_3 D_3 > 0  at r=4,
lambda_2 D_2 + lambda_3 D_3 < 0  at r=8.
```

Thus no nonzero nonnegative least-owner potential, even restricted to the two smallest owners and even when the unmatched tail vanishes, has a universal favorable sign. A useful JOH mechanism must couple owner colors through more arithmetic than fixed owner weights.

### B. Current authoritative objective

Final live main is `7790fb9f5ddda6eb9823899f2694d691756cd248`, the human merge of #1070. Authority blobs are:

- `AGENTS.md 9fa5e9519e2fb6dde22217aa2a18982dafef373a`;
- `CURRENT_PROOF_CONTRACT.md 88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a`;
- selector `d05c327ae694ea54b599dab0a21032a056b521f1`;
- broad-search policy `b5c063c51556ba57c4b25bcc380a606fa8daa207`;
- complete-return contract `16838f7f3c8724b970f8b8ece0bceaab9418066d`;
- research engine `6fce99c61efb5b2a73c0cb1f1464f09b351fcd55`;
- compiled primitive event source `research/VF_MID_FLOOR_LI_SIGNED_POPULATION_BALANCE.lean`, blob `9a9336dad72171b6d572a1c1ae88d1ae8b56b530`;
- JOH weighted-composite contract, blob `27e28f09e9f79e8a60d524e5fcb6f19904fa55f5`;
- accepted falsifier script, blob `98c83e6dc5521d8c355cf5648dd5625f3a86c7fd`.

The canonical target remains a uniform `O(R log R)` bound for `|pi(R^2)-VF_can(R^2)|`. The eventual JOH square-endpoint sign is RH-equivalent under the stated Johnston input and remains open. The gate is `SEARCH_BROAD`; complete-return gain is `UNKNOWN`.

Open #1071 kernel-checks the finite-C parity obstruction. Draft #1072 replays the already established one-to-seven-eighths contraction through native moment dependencies. Neither is new independent arithmetic or a positive eta.

### C. Structural hypothesis investigated

The newest Coordinator synthesis `20261102-coordinator-2` requested a two-owner chronological invariant surviving the fixed owner-3 reversals. The checkpoint initially selected SAT from the rolling rotation, but this newer committed upstream assignment superseded that intake choice; the run continued JOH without repeating today's earlier sectorwise work.

The tested hypothesis was:

> after chronological rank matching, a fixed nonnegative weighting of the two smallest least-prime owner sectors may have a stable sign even though either owner separately can reverse.

This is materially stronger than a single-owner sign test and is the simplest cross-owner potential. It is refuted by `r=4,8`.

The exact colored-backlog identity survives and identifies the first information an improved theorem must control: the full time-dependent interlacing of selected prime sources and owner-colored composite demands.

### D. Mathematical derivation

In a finite interval `[L,U)`, let

```text
a_1 < ... < a_P
b_1 < ... < b_N
```

be the genuine `eta=+1` and `eta=-1` locations, and put `m=min(P,N)`. Match `a_i` with `b_i` in chronological rank order. Let `p_i=P^-(b_i)`, the unique least prime of the composite negative event.

For any owner set `S`, define

```text
D_S = sum_(1<=i<=m, p_i in S) (b_i-a_i)
C_S(t) = # {i<=m : p_i in S, a_i<=t}
       - # {i<=m : p_i in S, b_i<=t}.
```

Then the exact cut identity

```text
b_i-a_i = sum_(L<=t<U) (1_(a_i<=t)-1_(b_i<=t))
```

gives

```text
D_S = sum_(L<=t<U) C_S(t).                                 (48)
```

The backlog starts and ends at zero after all matched events have occurred. Equation (48) is a conservation law: owner displacement is not determined by owner counts or endpoints, but by signed chronological area.

Partitioning by all owners recovers the complete matched displacement `D=sum_p D_p`. The full weighted first moment remains

```text
J =
  D + sum_(i=N+1)^P (U-a_i),  if P>=N,
  D - sum_(i=P+1)^N (U-b_i),  if N>P.                      (49)
```

Thus the unequal-count tail is retained exactly. It happens to vanish in both decisive fixtures.

For `r=4`, on `16<k<25`,

```text
a=(17,19,23), b=(18,21,24),
(a_i,b_i,p_i,b_i-a_i)=
(17,18,2,1), (19,21,3,2), (23,24,2,1).
```

Hence `(D_2,D_3)=(2,2)`, `D=J=4`.

For `r=8`, on `64<k<81`,

```text
a=(67,71,79), b=(65,69,78),
(a_i,b_i,p_i,b_i-a_i)=
(67,65,5,-2), (71,69,3,-2), (79,78,2,-1).
```

Hence `(D_2,D_3,D_5)=(-1,-2,-2)`, `D=J=-5`, while the fixed pair `D_{2,3}=-3`.

The associated `{2,3}` colored backlog has area `4` at `r=4` and `-3` at `r=8`. Therefore every nonzero nonnegative weighting of owners 2 and 3 reverses sign exactly as stated above.

### E. Quantitative consequence

Equation (48) is an exact first-moment representation, not an upper bound. The finite fixtures prove a uniform no-go over the proposed class of fixed nonnegative two-owner potentials.

This rules out all inequalities whose only proposed favorable quantity is

```text
lambda_2 D_2 + lambda_3 D_3
```

with fixed nonnegative coefficients and a universal sign. It also shows that count balance `P=N` does not repair the mechanism: both counterexamples have zero unmatched tail.

No bound on `J`, `G(R^2)`, the canonical VF defect, or a shell energy is improved. Signed interaction with other owners or a time-dependent arithmetic weight remains possible.

### F. Falsification and circularity review

- **Original carrier:** the events are the compiled prime-minus-floor-Li primitive mismatch, not a random or Möbius surrogate.
- **Chronology:** pairs are the canonical global rank pairs.
- **Complete first moment:** (49) retains both possible unmatched tails.
- **No cloning:** each negative composite receives its unique least prime once.
- **Balanced decisive cases:** `P=N=3` at both `r=4` and `r=8`, so no omitted tail explains the reversal.
- **Numerical exactness class:** `r=4` is an accepted repository fixture. The new `r=8` floor values were recomputed with a 90-digit Decimal Ramanujan evaluation of `Li_2`; the nearest integer margin on `64<=n<=81` is approximately `0.01929275345`, far above the retained precision. The classification remains `FINITE_COMPUTATION`, not Lean proof.
- **Scope:** the result refutes fixed nonnegative owner weighting. It does not refute time-dependent weights, signed weights, multi-owner cross terms, or an analytic ordering theorem using more than least-prime labels.
- **Circularity:** no JOH sign, prime error estimate, or RH-equivalent premise is assumed.

Same-day Coordinator, Analytic, Wheel, Census, Referee, and Lean reports were consumed at their available blobs; Nov 1 remains `YESTERDAY=CARRY_FORWARD`. External inbox blob `038018145c0fddb2f6306c0712373adf9cd1ea52` has no entry newer than 2026-10-18.

### G. Conceptual interpretation

Least-prime ancestry colors the negative demand stream, but it does not order that stream relative to the prime innovation stream. The exact object is a colored backlog path, and JOH displacement is its area.

This exposes why endpoint owner counts and fixed owner prices fail. They see the final zero backlog but not whether the path spends more time above or below zero. The arithmetic missing from JOH is a restriction on the entire interlacing path, not a better static partition of its endpoints.

### H. Competing mechanisms

- **Single-owner sign payment:** abandoned by `20261102-owner-1`.
- **Fixed nonnegative two-owner potential:** abandon by the `r=4,8` weighted sign reversal.
- **Colored-backlog area representation:** retain as the exact chronological coordinate.
- **Time-dependent owner potential:** viable only if its variation and boundary terms are included and independently controlled.
- **Global cross-owner interlacing:** continue; it must use arithmetic beyond least-prime labels.
- **Sparse-divisor hybrid covariance:** remains distinct and subject to the complete-return obstructions in `20261102-owner-2` and Coordinator C16-C19.

### I. Specialist handoffs

**Coordinator / Proof Architect:** register (48)-(49) and the `r=4,8` two-owner weighted no-go. Do not assign JOH to any fixed nonnegative owner-price argument. The viable state variable is the full colored backlog path plus the exact unmatched tail.

**Analytic Type II:** a possible analytic input is a signed area estimate for `C_S(t)` jointly in owner cutoff and time. It must not be inferred from endpoint count balance.

**Finite Wheel & Incidence:** search for a genuine restriction on transitions or excursions of the colored backlog, not a fixed price for owner colors. The `r=4,8` paths are mandatory regressions.

**Prime Census:** freeze `r=4,8`. A decisive next test should compare candidate transition laws on held-out balanced blocks and record the whole `C_S(t)` path, not only `D_S`.

**Adversarial Referee:** audit (48), tail restoration (49), the exact `r=8` event list, the high-precision floor margin, and the quantifier “every nonzero nonnegative pair of fixed weights.”

**Lean Verification:** only after acceptance, (48) is a small generic finite ordered-support identity. The `r=8` numerical fixture is lower priority than accepted quantitative work. Do not formalize a conjectural interlacing estimate.

### J. First independently missing lemma

The next JOH lemma must constrain the signed area of a genuine colored backlog by an arithmetic feature not contained in fixed least-owner labels. A precise exploratory target is a transition-weighted identity or inequality for two owner classes in which every change of owner color and every unmatched endpoint contributes explicitly.

Before promotion, it must survive the `r=4,8` balanced paths and a held-out counterexample search. Requiring `sum_t C_S(t)` itself to have the eventual target sign is target-equivalent and is not an acceptable independent input.

### K. Next-run resume capsule

- main: `7790fb9f5ddda6eb9823899f2694d691756cd248`;
- new claim: `20261102-owner-3`, equations (48)-(49);
- structural result: exact colored-backlog area conservation;
- finite no-go: every nonzero fixed nonnegative weighting of owner sectors 2 and 3 reverses sign between balanced blocks `r=4` and `r=8`;
- formal status: paper identity plus finite high-precision computation; independent review pending; no Lean execution;
- retired mechanism: fixed nonnegative owner-potential payment;
- surviving mechanism: arithmetic control of the full cross-owner backlog path with tail restoration;
- route coverage: JOH received this continuation; SAT remains the next distinct protected route unless newer authority changes it;
- `eta_gate: SEARCH_BROAD`;
- `net_endpoint_gain_after_complete_return: UNKNOWN`;
- canonical VF theorem, JOH sign, complete shell eta, strict Mertens exponent below `7/8`, and RH remain OPEN.

# RH_Lean agent daily report - 2026-11-02 / RH | Finite Wheel & Incidence

## Scheduled invocation checkpoint - 2026-11-02 02:08 EST (-0500)

**Status:** IN_PROGRESS / due CORR4 rotation  
**Invocation:** RUN_ID_UNAVAILABLE; scheduled run invoked 2026-11-02 02:05 America/New_York  
**Live main:** `a33987e275f8a431641d3f475b71a24aa2b1437c`  
**deployment_ack:** selected Coordinator claim `20261101-coordinator-3`, C9-C11 and the fixed-shift hybrid daughter count; resumed after Wheel's completed 2026-11-01 CORR4/FINITE-AC/MU-LIFT rotation.  
**Authority blobs:** `AGENTS.md 9fa5e9519e2fb6dde22217aa2a18982dafef373a`; `CURRENT_PROOF_CONTRACT.md 88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a`; selector `d05c327ae694ea54b599dab0a21032a056b521f1`; complete-return contract `16838f7f3c8724b970f8b8ece0bceaab9418066d`; research engine `6fce99c61efb5b2a73c0cb1f1464f09b351fcd55`.  
**Material source blobs:** `LOW_OWNER_PHYSICAL_AMPLITUDE_TRANSPORT.lean 72d66f61b3eeb000117ecdac393572558bb7c378`; `PrimeWheelRunOthelloBoundary.lean 26ffb242dc294fe8f57c1d6b8985c5f70f4e3d43`; `GLOBAL_RETURNED_CORE_FIRST_OWNER_CELLS.lean 5ca177548e91dd8bc6535e9913b29dc81cdfccea`; `GLOBAL_RETURNED_CORE_FIRST_OWNER_GRAM.lean 36141a8caec5f99d6c40cb72ae1fdbcf6f462b82`.  
**Continuity:** today's Coordinator/Wheel/Census/Referee/Lean reports were absent at intake and are `TODAY=PENDING`; today's Owner and Analytic reports were consumed. Yesterday is `YESTERDAY=CARRY_FORWARD`, including Coordinator `8f661bc144fd96ffd7a9a8cd084e74e3df05d1a8`, Wheel `707a31ba0fa7b4a04266730236a9e79d4947e91a`, Referee `fbf6dfc995e7d38b1ec07754e4d368a91112ecec`, and Lean `6aa7197c4169a70debed607e12f4639218cd21b6`. External handoffs blob `038018145c0fddb2f6306c0712373adf9cd1ea52` has no entry newer than 2026-10-18.  
**PR state:** no open or draft pull request was returned. PRs #1068 and #1069 are merged; the latest main theorem remains an exact odd-Mobius telescope/truncated-tail interface, not a tail estimate.

### Active hypothesis and first new step

The due question is whether squarefreeness plus least fresh-prime chronology improves the Coordinator's fixed-shift absolute incidence bound on the literal hybrid daughter carrier.

A source-admitted obstruction has emerged already. For lifted owners (q=3,p=5), put

[
m_t=14+25t,qquad n_t=5+9t.
]

Then

[
9m_t-25n_t=1.
]

Whenever both (m_t,n_t) are squarefree, ((3,m_t)) and ((5,n_t)) are genuine nonzero daughter labels at consecutive physical addresses. Their cofactors have opposite parity for every (t), so their unique least fresh-prime owner is exactly (2). Thus neither squarefreeness nor first-owner partition disperses this fixed shift.

The run is now proving a quantified dyadic saturation statement. The intended proof uses the positive-density squarefree sieve for the two linear forms, excludes only (O(H)) square-boundary addresses from an (asymp H^2) dyadic population, and concludes that some root shell carries (Omega(R)) absolute weight in the single cell ((h,r,q,p)=(1,2,3,5)). This would show the Coordinator's (O(R)) fixed-shift absolute count is power-sharp and that any useful CORR4 gain must be signed, not incidence-only.

No density theorem, endpoint gain, signed cancellation, strict Mertens exponent improvement, canonical VF bound, or RH is claimed at this checkpoint. `eta_gate: SEARCH_BROAD`; complete-return gain UNKNOWN.


## Final synthesis - claim `20261102-wheel-1` - 2026-11-02 02:10 EST (-0500)

**Status:** COMPLETED / PAPER_PROOF_NEEDS_INDEPENDENT_REVIEW  
**Result classes:** `C9-C11 INDEPENDENTLY REDERIVED`; `EXACT FIXED-CELL PARAMETRIZATION`; `POSITIVE-DENSITY DYADIC SATURATION`; `REFUTED UNIFORM ABSOLUTE FIXED-SHIFT POWER SAVING`; `NO SIGNED COVARIANCE BOUND`; `NO FIXED ETA GAIN`; `NO RH`.

### A. Authoritative objective and source carrier

The canonical target remains

[
exists Cge0 orall Rge2,qquad
 |pi(R^2)-VF_{m can}(R^2)|le CRlog R.
]

The nearer benchmark is still a complete genuine shell estimate with a fixed positive saving. It is OPEN. The imported (7/8) Mertens result is available only at its compiled scope and is not recycled here.

For the literal hybrid shell carrier, let

[
I_R={(q,m):q {m odd prime}, q^2<R, R^2le q^2m<(R+1)^2, mu(m)
e0},
]

with physical address (q^2m) and coefficient (mu(m)/q). This is exactly the daughter label set in Owner claim `20261101-owner-4`; the present result concerns its daughter-daughter part of (N_R), hence one actual sector of the complete (Xi_H). It is not identified with the compiled single-daughter-prefix Gram.

### B. Independent audit of C9-C11

The Coordinator's structural claims are correct on the stated nonzero label sets.

1. **Distinct sign carriers.** Outer/outer is immediate. An outer carrier (a) cannot equal a daughter cofactor (m), since (age R^2) while (m<(R+1)^2/9<R^2) for (Rge56). If two daughter labels have the same cofactor (m) and (p>q), then
   [
   |p^2m-q^2m|=(p^2-q^2)m>2R,
   ]
   contradicting their membership in one square shell. Thus every distinct hybrid pair has distinct squarefree sign carriers.

2. **Fresh-owner/shift exclusion.** If the least fresh owner (r) divides the physical gap, reduction modulo (r) forces (r) to be one of the displayed lift primes unless it divides both sign carriers. The latter contradicts freshness. This gives exactly the outer/outer, outer/daughter and daughter/daughter alternatives in C10.

3. **Square-divisibility dichotomy.** For daughters,
   [
   q=piff q^2mid(q^2m-p^2n)iff p^2mid(q^2m-p^2n).
   ]
   If, for example, (q
e p) and (q^2) divides the gap, then (q^2mid n), impossible because (mu(n)
e0).

For fixed (q
e p) and fixed gap (h), CRT therefore puts the physical address in one residue class modulo (q^2p^2). The Coordinator's weighted absolute upper bound (O(R)) per fixed shift is valid. The new question was whether squarefreeness and first-owner chronology improve it by a power. They do not.

### C. Fixed-cell saturation theorem

For every integer (tge0), define

[
m_t=14+25t,qquad n_t=5+9t,
]
[
x_t=9m_t=126+225t,qquad y_t=25n_t=125+225t.
]

Then

[
oxed{x_t-y_t=1.} 	ag{42}
]

Whenever (m_t) and (n_t) are squarefree:

- ((3,m_t)) and ((5,n_t)) have nonzero genuine daughter coefficients;
- (m_t
e n_t);
- exactly one of (m_t,n_t) is even, since their parities are (t) and (t+1);
- hence their unique least fresh-prime owner is exactly (r=2);
- their unordered-pair coefficient has absolute value (1/(3cdot5)=1/15).

Thus every such (t) belongs to the single daughter-daughter cell

[
(h,r,q,p)=(1,2,3,5).                                      	ag{43}
]

This is stronger than merely observing that first-owner partition preserves total mass: all constructed pairs remain in one fixed chronological owner fibre.

### D. Positive-density proof

The two affine forms are linked by

[
9m_t-25n_t=1.                                               	ag{44}
]

For a prime (ell), let (ho(ell)) be the number of residue classes (tmodell^2) on which (ell^2mid m_tn_t). Direct calculation gives

[
ho(2)=2,qquad ho(3)=ho(5)=1,qquad
ho(ell)=2quad(ell
e2,3,5).                            	ag{45}
]

For the last assertion each affine form has one root modulo (ell^2), and the roots cannot coincide because (44) would then give (ell^2mid1). At (ell=3), (n_tequiv5pmod9); at (ell=5), (m_tequiv14pmod{25}).

Finite squarefree inclusion-exclusion, followed by the elementary large-square tail bound, gives

[
#{0le t<T:m_t,n_t {m squarefree}}
 =kappa T+o(T),                                            	ag{46}
]
where

[
oxed{
kappa=
left(1-rac24ight)
left(1-rac19ight)
left(1-rac1{25}ight)
prod_{ell
e2,3,5}
left(1-rac2{ell^2}ight)>0.
}                                                            	ag{47}
]

For completeness, the proof needs no prime-distribution hypothesis. Truncate square divisors at (z), apply CRT to the finitely many permitted residue classes, and then bound the discarded events by

[
Tsum_{ell>z}rac{2}{ell^2}+O(sqrt T).
]

Let (T	oinfty), then (z	oinfty). The product is positive because (sum_ellho(ell)/ell^2<infty) and every local factor is nonzero.

Now restrict to

[
H^2le x_t<4H^2.
]

The (t)-interval has (H^2/75+O(1)) elements, so (46) yields

[
rac{kappa}{75}H^2+o(H^2)                                	ag{48}
]

simultaneously squarefree pairs. The two consecutive addresses fail to lie in the same square shell only when (x_t) is itself a square. There are at most (H+1) such boundaries. For (H>25), every remaining pair satisfies the strict admissions (3^2<R) and (5^2<R) in its unique shell (Hle R<2H).

Therefore

[
oxed{
sum_{Hle R<2H}
 sum_{substack{{lambda,lambda'}subset I_R\
 h=1, r=2, {q,p}={3,5}}}
 |c_R(lambda)c_R(lambda')|
 ge rac{kappa}{1125}H^2+o(H^2).
}                                                            	ag{49}
]

By pigeonhole, for infinitely many roots (R) one single fixed cell has absolute mass (Omega(R)). Hence no uniform (O(R^{1-delta})), (delta>0), fixed-shift bound can follow from squarefreeness, shell geometry, CRT, or least-owner chronology alone. The Coordinator's (O(R)) fixed-shift incidence estimate is power-sharp.

### E. Exact finite regression

A separate deterministic integer regression enumerated the same (t)-family, evaluated (mu) by a linear sieve, removed square-boundary addresses, and bucketed by (R=lfloorsqrt{x_t}floor). It returned:

[
egin{array}{c|r|r|r|r}
H&	ext{admitted pairs}&	ext{best }R&	ext{best shell count}&
	ext{pairs}/H^2\ hline
64&21&68&1&0.00512695\
128&81&159&2&0.00494385\
256&343&461&3&0.00523376\
512&1340&986&5&0.00511169\
1024&5379&2010&10&0.00512981\
2048&21528&3775&16&0.00513268
end{array}
]

The partial Euler product gives (kappaapprox0.3847565), hence (kappa/75approx0.00513009), matching the regression. This computation is evidence only; equations (42)-(49) are the proof.

### F. Consequence for CORR4 and complete return

Claim (49) is an actual arithmetic inverse/no-go theorem, not an arbitrary-vector extremizer. It shows:

- squarefreeness does not thin fixed lifted congruence classes by any power;
- first-owner chronology need not disperse them across owners;
- even the smallest gap (h=1) can carry linear absolute mass in one shell;
- an absolute shift/owner count cannot provide the missing (H^{1/2+eta}) saving.

It does **not** show that the signed sum of these pairs is large. Their signs are (mu(m_t)mu(n_t)), and (46) deliberately forgets that product. A signed estimate for this two-linear-form correlation could still cancel. Nor does the theorem control outer-outer, outer-daughter, root, activation, or cross-shift terms in (Xi_H).

The source-faithful complete target remains a joint bound on

[
Xi_H=2sum_RN_R-2sum_Rmu(R)W_R+2sum_RW_RK_R,
]

or a proved absorption that restores all of its terms. Claim (49) rules out one unsigned route to that bound; it supplies no complete endpoint eta.

### G. Novelty, falsification, and no-circularity audit

- Repository search returned no occurrence of the affine family (42), the fixed cell (43), or a fixed-shift saturation theorem.
- The construction uses the literal strict daughter admission and actual coefficient (1/(qp)).
- Each physical occurrence is counted once; (t) is determined by (x_t), and the lifted-address injectivity prevents duplication.
- The least owner is genuinely (2), not one of the lift primes (3,5); this is compatible with C10 because (2
mid h=1).
- Square boundaries are explicitly removed rather than hidden in a real approximation.
- The result tests the strongest proposed absolute strengthening and disproves it by a legal infinite family.
- It assumes no Mertens estimate, signed covariance estimate, desired shell bound, canonical VF estimate, or RH-equivalent statement.
- It does not refute a signed two-linear-form correlation theorem. That is the surviving arithmetic possibility.
- Independent Referee review and Lean formalization are PENDING.

### H. Specialist handoffs

**Coordinator / Proof Architect:** accept C9-C11 at paper level pending Referee, but record (49) as a sharp no-go for absolute fixed-shift improvement. The hybrid owner sieve remains useful only if it retains the signed products.

**Owner Payment / Signed Arithmetic:** the exact complete (Xi_H) reconstruction remains mandatory. Do not replace its daughter-daughter sector by an unsigned sparse-incidence estimate; one fixed cell already saturates the linear scale.

**Analytic Type II:** the surviving subproblem is the signed affine correlation
[
sum_tmu(14+25t)mu(5+9t)
]
on dyadic (t)-intervals, together with the other complete (Xi_H) sectors. Squarefree density alone cannot help. Any imported shifted-Möbius theorem must match these growing sparse square-shell windows and original weights.

**Prime Census Laboratory:** freeze (42) as a regression family. A useful experiment should retain the sign product and compare its partial sums with the absolute count; another absolute population scan is unnecessary.

**Adversarial Referee:** audit (45), the squarefree-sieve passage (46), boundary removal, strict (q^2<R), the first-owner-(2) assertion, and the (1/15) weight in (49). Return separate verdicts on C9-C11, saturation, and quantitative relevance.

**Lean Verification:** only after independent acceptance, the finite algebraic core (42)-(45) and the exact label/owner admission are implementation-sized. The asymptotic density theorem may require infrastructure disproportionate to its no-go use; do not formalize a conjectural signed correlation or claim complete-source control.

### I. First independently missing inequality and resume capsule

The first useful CORR4 input is now unambiguously signed: a uniform cancellation theorem for the actual fixed-shift/owner cells, beginning with

[
sum_{substack{t {m in the relevant dyadic interval}\
m_t,n_t {m squarefree}}}
 mu(m_t)mu(n_t),
]

and then an aggregation theorem restoring all (h,r,q,p) cells plus outer, root, and activation terms. Taking absolute values cannot close this step.

- Main: `a33987e275f8a431641d3f475b71a24aa2b1437c`.
- New claim: `20261102-wheel-1`, equations (42)-(49).
- Strongest result: one legal fixed cell has dyadic absolute mass (Omega(H^2)) and shell mass (Omega(R)) along a sequence.
- Retired mechanism: any power saving based only on fixed-shift congruence population, squarefreeness, and least-owner partition.
- Surviving mechanism: signed two-linear-form cancellation inside the exact complete hybrid reconstruction.
- Route coverage: this invocation supplies the due CORR4 attempt; the previous Wheel day completed FINITE-AC and MU-LIFT turns.
- `eta_gate: SEARCH_BROAD`.
- `net_endpoint_gain_after_complete_return: UNKNOWN`.
- Complete shell estimate, strict Mertens exponent below (7/8), canonical VF theorem, and RH remain OPEN.


### Publication verification

The completed synthesis was committed as `cf3f40d1dbe61d6808bc8fb09d821f045dc4f6ab` and read back as blob `cb40cc7241097fa03f98ed166ae6416f2fc0434c` (14,786 characters). Claim `20261102-wheel-1`, equations (42)-(49), the fixed cell ((h,r,q,p)=(1,2,3,5)), exact authority/source hashes, classifications, and resume capsule were present. This receipt records publication only and changes no mathematical claim.


## Scheduled continuation checkpoint - 2026-11-02 10:12 EST (-0500)

**Status:** IN_PROGRESS / due FINITE-AC rotation  
**Invocation:** RUN_ID_UNAVAILABLE; scheduled run invoked 2026-11-02 10:12 America/New_York.  
**Live main:** `7790fb9f5ddda6eb9823899f2694d691756cd248`, human merge of PR #1070. Open/draft PR refresh returned none.  
**Continuity:** resumed after accepted Wheel claim `20261102-wheel-1`; consumed today's Coordinator `6b347ff997fa75eab2b445ed523eaa55e4c49e17`, Owner, Analytic, Census, Referee `45c702cf93b567b889a6122f10c9a16161991517`, Lean `7281b4359d9d596dc46a5ef1d82e2090fd3c95ed`, the 2026-11-01 carry-forward set, and external inbox `038018145c0fddb2f6306c0712373adf9cd1ea52`.  
**Authority:** `AGENTS.md 9fa5e9519e2fb6dde22217aa2a18982dafef373a`; contract `88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a`; selector `d05c327ae694ea54b599dab0a21032a056b521f1`; broad-search `b5c063c51556ba57c4b25bcc380a606fa8daa207`; complete-return `16838f7f3c8724b970f8b8ece0bceaab9418066d`; engine `6fce99c61efb5b2a73c0cb1f1464f09b351fcd55`.  
**Selected task:** FINITE-AC on the literal floor kernel `Q_R=2M(R-1)-M(R^2-1)`, resuming the first unsupported signed increment-energy estimate in `20261101-wheel-2`. The candidate new move is an exact parity-sector/binary incidence decomposition using the merged odd-Mobius divisor telescope, followed by a contraction audit. The run will determine whether the odd-odd sector yields a genuine lower-scale restriction or merely reconstructs the original endpoint through dyadic layers.

No contraction, finite-C bound, endpoint gain, strict Mertens exponent improvement, canonical VF theorem, or RH is claimed at this checkpoint. `eta_gate: SEARCH_BROAD`; complete-return gain `UNKNOWN`.


## Final synthesis - claim `20261102-wheel-2` - 2026-11-02 10:24 EST (-0500)

**Status:** COMPLETED / PAPER_PROOF_NEEDS_INDEPENDENT_REVIEW  
**Result classes:** `EXACT BINARY PARITY REASSEMBLY`; `NONNEGATIVE ODD-CORE PACKET WEIGHTS`; `EXACT ODD-ODD HALF-SCALE RESTORATION`; `R=5 SECTORWISE CONTRACTION COUNTEREXAMPLE`; `NO FINITE-C BOUND`; `NO FIXED ETA`; `NO RH`.

### J. Literal source and notation

For `R >= 2`, put
```text
X = R^2 - 1,  L = R - 1,  L0 = floor(L/2),
Q_R = sum_(1 <= a,b <= L) mu(a) mu(b) floor(X/(ab)).
```
Main proves `Q_R = 2M(L)-M(X)`; this is the literal finite-C source, not a surrogate.

For odd indices define the asymmetric kernel
```text
O(A,B;Y) =
  sum_(1 <= a <= A, 1 <= b <= B, a,b odd)
    mu(a) mu(b) floor(Y/(ab)).
```

Material source blobs at final main `7790fb9f5ddda6eb9823899f2694d691756cd248` are:

- `EULER_HYBRID_ABEL_GRAM_20261027.lean`: `2a94dd8fd56fc03e95f732fb44b778a8d4f83e26`;
- `EULER_SELF_DUAL_ENDPOINT_GATE_20261027.lean`: `e7ee8f77ffd59bccaa49dd6d74fbe0d7952c2d73`;
- `ODD_MOBIUS_FLOOR_TELESCOPE_20261101.lean`: `fbe472cca89f757c8f6f25e630a49847a2bd6ad0`;
- merged lifted-address source: `61f98a8997d86ddbb07404284d12aebd36a67955`.

The last source is formally proved on main but is not used to infer any estimate below.

### K. Exact binary second difference

Every nonzero even Möbius index is uniquely `2u` with `u` odd, and then `mu(2u)=-mu(u)`. Splitting both original indices into odd and once-even parts gives
```text
Q_R =
  O(L,L;X)
  - 2 O(L,L0; floor(X/2))
  + O(L0,L0; floor(X/4)).                         (50)
```
No occurrence is duplicated: the two mixed terms are the two orientations of exactly one even index. Terms divisible by `4` have Möbius coefficient zero.

Equivalently, group the four parity lifts by their unique odd cores. For odd `a,b <= L`, let
```text
N = floor(X/(ab)),
ea = 1_(a <= L0),  eb = 1_(b <= L0),
w_R(a,b) = N - (ea+eb) floor(N/2) + ea eb floor(N/4).
```
Then the complete source is
```text
Q_R = sum_(a,b <= L, a,b odd) mu(a) mu(b) w_R(a,b).          (51)
```
The packet weight is always nonnegative. If neither core has an even lift, it is `N`; if exactly one does, it is `N-floor(N/2)`; if both do, it is
```text
N - 2 floor(N/2) + floor(N/4) >= 0.
```
Thus unique factorization at the prime `2` supplies an exact occurrence-preserving four-corner packet. It does not supply a favorable sign for cross-core products `mu(a)mu(b)`.

### L. Odd telescope and the endpoint carried by one sector

Let
```text
S_o(Y) = sum_(n <= Y, n odd) mu(n),
P_2(Y) = #{j >= 0 : 2^j <= Y}.
```
Because `X=(R-1)(R+1)`, every pair with `ab <= X` has `a <= L` or `b <= L`. Inclusion-exclusion and the merged odd-Möbius floor telescope therefore give
```text
O(L,L;X) = 2 U_R - F_X,                                    (52)
U_R = sum_(a <= L, a odd) mu(a) P_2(floor(X/a))
    = sum_(j >= 0) S_o(min(L, floor(X/2^j))),
F_X = sum_(j >= 0) S_o(floor(X/2^j)).
```
All sums are finite after the quotient becomes zero.

The elementary once-even split is
```text
M(Y) = S_o(Y) - S_o(floor(Y/2)).
```
Consequently
```text
O(L,L;X) = -M(X) + R_o(R),                                  (53)
R_o(R) =
  2 sum_(j >= 0) S_o(min(L, floor(X/2^j)))
  - 2 S_o(floor(X/2))
  - sum_(j >= 2) S_o(floor(X/2^j)).
```
Every prefix in `R_o(R)` is at most `floor(X/2)`, since `L <= floor(X/2)`. This is an exact half-scale restoration, but not a contraction: the odd-odd block itself retains the full endpoint with coefficient `-1`.

### M. Exact counterexample to sectorwise payment

At `R=5`,
```text
X=24, L=4, L0=2,
O(4,4;24)=10,
O(4,2;12)=8,
O(2,2;6)=6.
```
Hence
```text
Q_5 = 10 - 2*8 + 6 = 0.
```
The endpoint identity independently gives `M(4)=-1`, `M(24)=-2`, and therefore `2M(4)-M(24)=0`.

Thus the genuine odd-odd sector has value `10` while the genuine mixed/even complement has value `-10`. In particular, no finite homogeneous comparison
```text
|O(L,L;X)| <= C |Q_R|
```
or its squared version can hold for all roots. The failure is arithmetic, not an arbitrary-vector model.

A deterministic exact regression verified (50)-(53) directly for every `2 <= R <= 100`. On `2 <= R <= 2000`, the first roots with `Q_R=0` but nonzero odd-odd block are
```text
R = 5, 9, 14, 33, 77, 133, 134, 330, 363, 467, ...
```
and at `R=493`, `Q_R=1` while the odd-odd block is `-144`. These finite checks are regressions; the universal falsifier already follows from the exact `R=5` calculation.

### N. Consequence for FINITE-AC

The binary decomposition exposes a genuine conservation law: parity lifts must be reassembled before taking absolute values. The merged odd-divisor telescope does not turn finite-C into a lower-scale estimate, because its odd-odd completion carries `-M(X)`, and the other parity sectors can cancel it exactly.

This retires the proposed route of bounding the odd-odd completion and truncated odd tail independently. It does not refute a joint signed theorem for the full packet (51). The surviving arithmetic question is a weighted odd-core covariance estimate that keeps all three terms of (50), or equivalently all four parity lifts in (51), intact.

The first unsupported inequality remains a uniform upper bound for that complete signed covariance at the historical-envelope scale:
```text
|sum_(a,b odd <= L) mu(a)mu(b)w_R(a,b)|
  <= C R sqrt(K_R).
```
This is exactly the finite-C obligation, so (50)-(53) are a structural representation and a scoped no-go, not an independently paid supplier. A useful next step would need an additional restriction coupling distinct odd cores, not another parity count or power-of-two telescope.

### O. Novelty, falsification, and scope audit

- Repository search found the merged one-variable odd telescope, but no statement of (50), the packet weight (51), the endpoint restoration (53), or the `R=5` sectorwise counterexample.
- The proof uses the original floor, strict cutoff `a,b<R`, and exact square endpoint `R^2-1`.
- Unique odd-core ownership preserves all multiplicities and coefficients.
- Floors are retained exactly; no real approximation or density input is used.
- The result neither assumes nor proves finite A, finite C, a Mertens exponent, the canonical VF estimate, or RH.
- Independent Referee review and Lean formalization are PENDING.
- The finite identities are implementation-sized, but formalization should wait for independent acceptance and a determination that the packet representation aids a quantitative attack.

### P. Routing check and handoff

- `eta_gate: SEARCH_BROAD`.
- Protected route: FINITE-AC / literal Euler self-dual floor kernel.
- New mathematics: exact binary second difference (50), nonnegative complete packet (51), half-scale endpoint restoration (53), and genuine `R=5` no-go.
- Exact unresolved step: signed cross-odd-core control of the complete packet at scale `R sqrt(K_R)`.
- Complete return: all parity sectors are restored in (50)-(51); no complement is discarded.
- Independent reviewer/formal evidence: PENDING; main's odd telescope and endpoint identity are compiled inputs only.
- Net endpoint gain: `UNKNOWN`.
- Rolling Wheel coverage: CORR4 `20261102-wheel-1`; FINITE-AC this claim; next distinct route due is MU-LIFT unless a review repair takes precedence.
- Complete shell estimate, strict exponent below `7/8`, canonical VF theorem, and RH remain OPEN.

**Referee request:** independently check the parity reindexing, floor nesting, nonnegativity of `w_R`, the coverage step in (52), the endpoint coefficient in (53), and the exact `R=5` witness. Return a separate verdict on structural correctness and quantitative relevance.

**Lean request:** no proof PR is requested yet. If accepted and judged useful, formalize the finite binary reassembly and `R=5` witness without adding a finite-C hypothesis.


### Publication verification

The completed FINITE-AC synthesis was committed as `e122f45aa57cf434eca6c1d352b9290c0094a895` and read back as blob `5ef32fc49e05d5907bc9cd30685ee464e4f281f9` (24,764 characters). Claim `20261102-wheel-2`, equations (50)-(53), the nonnegative odd-core packet, exact `R=5` counterexample, scope classifications, and resume capsule were present. Final main remained `7790fb9f5ddda6eb9823899f2694d691756cd248`; the open/draft PR refresh returned none. This receipt records publication only and changes no mathematical claim.


---

## Scheduled continuation final synthesis - claim `20261102-wheel-3` - 2026-11-02 18:12 EST (-0500)

**Status:** `COMPLETED / PAPER_PROOF_NEEDS_INDEPENDENT_REVIEW`.  
**Result classes:** `EXACT FIRST-OMITTED-SUPPORT RADIUS`; `SHARP COEFFICIENT BOUNDARY`; `EXACT FRESH-PRIME FACTORIAL COHERENCE`; `NO SUMMATORY RECURRENCE`; `NO FIXED ETA`; `NO RH`.

### Q. Authority, continuity, and selected route

Live main is `8e5d64ae689b39dabd2a4f6eb33efe4d5d192015`, the human merge of PRs #1071 and #1072. Authority blobs remain `AGENTS.md 9fa5e9519e2fb6dde22217aa2a18982dafef373a`, `CURRENT_PROOF_CONTRACT.md 88cddd9cd98c3b55f0b013998541e9b4e9dc9f2a`, selector `d05c327ae694ea54b599dab0a21032a056b521f1`, broad-search `b5c063c51556ba57c4b25bcc380a606fa8daa207`, complete-return `16838f7f3c8724b970f8b8ece0bceaab9418066d`, and engine `6fce99c61efb5b2a73c0cb1f1464f09b351fcd55`.

This is the due MU-LIFT turn after today's CORR4 claim `20261102-wheel-1` and FINITE-AC claim `20261102-wheel-2`. The latter is independently accepted by Referee claim `20261102-referee-2` and is now kernel-checked on main in `research/FINITE_C_BINARY_PARITY_OBSTRUCTION_20261102.lean`; it is retained as a regression, not reused as a recurrence.

Same-day report blobs consumed at final intake were Coordinator mirrors `1f8b6897897fc6e8d76fdc9a541bebea68ef52fc`, Owner `abfe546d72b151f4cd200fc61de3197efe23a65c`, Analytic `8e48b59611aa1d0bfa3577ed0a4a3bc0d0fcae73`, prior Wheel `4fcbd7ecc5ece2a08ea80b6477008e1c19d1d2c3`, Census `6e8070f78688c63824ed6586dc8bad78f04f1f11`, Referee `73a4e272393964d06a3fced63a1eea546ac9dd8d`, and Lean `f4616a722c6a2b79e253207ab2352a66751f4624`. The complete 2026-11-01 set is `YESTERDAY=CARRY_FORWARD`, including Wheel `707a31ba0fa7b4a04266730236a9e79d4947e91a`. External handoffs remain blob `038018145c0fddb2f6306c0712373adf9cd1ea52`, with no entry newer than 2026-10-18.

Open PR #1073 is a draft at head `6845fdbdcb12261bfaf26b7944ede53064cf80ee`. Its body explicitly leaves the complete perturbed low/high estimates open; it is not on main and is not used below.

Material main sources are:

- `research/MERTENS_FINITE_PREFIX_EXTENSION.lean`, blob `131e9af86207a42d4bf6488e3f64c9ce4f97e5df`;
- `research/MERTENS_HEATH_BROWN_SIGNED.lean`, blob `af69b4811cf9f523eb7c96fb0ca836b2cdbd1180`;
- `research/MERTENS_SIGNED_HYPERBOLA.lean`, blob `d199571f19346797229a25b0fa53c6e80499999f`;
- `docs/MERTENS_AMPLIFICATION_BUDGET.md`, blob `62bbe73c4755eaa64772ec2cc2731936c01b49cd`.

### R. First omitted nonzero support controls the exact radius

Fix `N >= 1`. Let `s > N` satisfy

```text
mu(s) != 0,
mu(n) = 0  for every N < n < s.                         (54)
```

Thus `s` is the first omitted nonzero Mobius coefficient after the stored prefix. Put

```text
a = mobiusPrefix N,
D = inverseDefect a = (mu-a) * 1,
L_k = heathBrownLift a k.
```

Then the prefix actually agrees with genuine Mobius below `s`, not merely below `N+1`:

```text
a(n)=mu(n)  for n<s.                                     (55)
```

The compiled support theorem therefore gives

```text
D(n)=0 for n<s,
D^k(n)=0 for n<s^k,
L_k(n)=mu(n) for n<s^k.                                  (56)
```

This radius is exact. At the first support point, divisor convolution gives

```text
D(s)=mu(s).                                               (57)
```

In a nonzero term of `D^k(s^k)`, all `k` factors are at least `s`. Since their product is `s^k`, every factor must equal `s`. Hence

```text
D^k(s^k)=mu(s)^k.                                        (58)
```

Every divisor `d>1` in `(mu*D^k)(s^k)` leaves a quotient strictly below `s^k`, where `D^k` vanishes. Using the compiled exact lift error therefore gives

```text
mu(s^k)-L_k(s^k) = mu(s)^k,
L_k(s^k) = mu(s^k)-mu(s)^k.                              (59)
```

For `k=1`, this says the stored prefix first fails at `s`. For every `k>=2`, `mu(s^k)=0` because `s>1` is squarefree, while `mu(s)^k` is `+/-1`; consequently

```text
L_k(s^k) = -mu(s)^k != 0 = mu(s^k).                      (60)
```

Thus the exact reconstruction interval is governed by the first omitted squarefree site and is sharp at its `k`th power. This strengthens the nominal `(N+1)^k` support radius whenever `N+1` and subsequent sites are squareful, but it supplies no norm contraction.

Concrete exact regressions are:

```text
N=3,  s=5:   L_2(25)=-1,  mu(25)=0;
N=7,  s=10:  L_2(100)=-1, mu(100)=0;
N=15, s=17:  L_3(4913)=1, mu(4913)=0.
```

Direct divisor-convolution evaluation reproduced (55)-(60) for `N in {3,7,8,15,24}` and `k in {1,2,3}`. These checks are regressions; the proof above is exact and general.

### S. Fresh-prime factorial coherence

There is a second sharpness phenomenon beyond the exact radius. Let `p_1,...,p_k` be distinct primes exceeding `N`, and put `P=product_i p_i`. Every nontrivial divisor `d` of `P` has no stored divisor other than `1`, so

```text
D(1)=0,  D(d)=-1 for every nontrivial d|P.                (61)
```

A nonzero ordered `k`-fold factorization of the squarefree `P` must give one prime to each factor. There are exactly `k!` such assignments, all with the same sign:

```text
D^k(P)=(-1)^k k!.                                        (62)
```

For every divisor `d>1`, `P/d` has fewer than `k` prime factors and cannot support `D^k`. Hence the exact error identity yields

```text
mu(P)-L_k(P)=(-1)^k k!,
L_k(P)=(-1)^k(1-k!).                                     (63)
```

The finite checks `(N,k,P)=(5,2,77),(5,3,1001),(10,4,46189)` gave lifted coefficients `-1,5,-23`, exactly as (63). Thus higher-order lifting has coherent, rather than random, fresh-prime multiplicity at this frontier.

### T. Quantitative and no-circularity audit

Equations (54)-(63) are structural consequences of the actual integer convolution carrier. They do not assume a Mertens bound, a finite-A/C statement, an envelope recurrence, a favorable sign, or any target-equivalent estimate.

The result has two precise uses and two limits:

1. A finite prefix through `N` may legitimately use the larger exact cutoff `s^k` when the intervening genuine Mobius coefficients vanish. The boundary `s^k` cannot be included.
2. Any coefficientwise absolute method that crosses the distinct-fresh-prime frontier pays at least `k!-1`. For fixed `k`, this is a fixed constant and has normalized loss `g=0`; it does not obstruct the accepted fixed-order MU-LIFT scheme. If `k=k(B)` grows and this loss is paid absolutely, subpower loss requires `log(k!)/log B -> 0`, equivalently `k log k=o(log B)` at this level.
3. A single boundary coefficient does not lower-bound a signed summatory output. Cancellation across different frontier products remains possible and is not estimated here.
4. Exact coefficient extension, even at the improved radius, does not bound the complete summatory lift on every `B<=X<B^k`. The required signed hyperbola rows and overlap remain unpaid.

Required MU-LIFT accounting:

- `k:` arbitrary fixed positive integer for (54)-(60); factorial frontier (61)-(63) uses exactly `k` distinct fresh primes.
- `r:` none obtained.
- `G:` none obtained; coefficientwise frontier cost is at least `k!-1` only for methods that take absolute values there.
- `g:` `0` for fixed `k`; variable-order absolute methods require `log(k!)/log B -> 0`.
- `interval/chain:` exact coefficient agreement on `n<s^k`, sharp failure at `s^k`; no whole-prefix summatory interval estimate.
- `fixed constants:` boundary error magnitude `1`; distinct-prime frontier magnitude `k!` in the error and `k!-1` in the lifted coefficient.
- `accumulated loss:` not converted to a recurrence.
- `independent arithmetic input:` least omitted nonzero Mobius support and unique factorization only.
- `evidence status:` paper proof plus exact finite divisor-convolution regressions; independent review and Lean formalization pending.

### U. First open inequality and handoff

The surviving MU-LIFT obligation is unchanged in kind: prove a genuine-Mobius whole-prefix estimate

```text
E(B^k) <= G(B) E(B)^r,
r<k,  log G(B)/log B -> 0,                               (64)
```

on one complete power-growing chain or an appropriately stronger all-`B` range, with every signed hyperbola row, overlap, boundary, and interpolation term retained. The new theorem says the coefficient support radius can be sharpened to the first omitted squarefree site and identifies the exact boundary failure; it does not supply (64). A viable next attempt should exploit arithmetic cancellation inside the complete signed hyperbola expansion, not assume coefficientwise contraction beyond the sharp support wall.

**Referee request:** independently audit (55), the equality case in (58), the single surviving divisor in (59), and the ordered-factorization count in (62). Return separate verdicts on the exact-radius theorem, factorial frontier, and quantitative relevance.

**Lean request:** after independent acceptance and utility review, (55)-(60) form a small implementation-sized package using existing `AgreeBelow`, `inverseDefect_zero_below`, `convolution_pow_zero_below`, and `heathBrownLift_error`. Do not formalize (64) as an assumed theorem or open a competing branch while draft #1073 is active.

### V. Resume capsule

- Main: `8e5d64ae689b39dabd2a4f6eb33efe4d5d192015`.
- New claim: `20261102-wheel-3`, equations (54)-(64).
- Strongest new theorem: the first omitted nonzero Mobius site `s` gives an exact and sharp lift radius `s^k`.
- Strongest new obstruction: distinct fresh primes produce factorial coherent defect multiplicity and opposite-sign lifted coefficients for every `k>=2`.
- Route coverage: today's three Wheel invocations cover CORR4, FINITE-AC, and MU-LIFT without restarting their workspaces.
- `eta_gate: SEARCH_BROAD`.
- `net_endpoint_gain_after_complete_return: UNKNOWN`.
- Complete shell estimate, strict Mertens exponent below `7/8`, canonical VF theorem, and RH remain OPEN.

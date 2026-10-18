# RH_Lean agent daily report - 2026-10-18 / RH | Finite Wheel & Incidence

**Status:** COMPLETED / DUPLICATE_SCHEDULE_TRIGGER_RECORDED  
**Run ID:** 2026-10-18T12:54:27-04:00, scheduled invocation  
**Canonical objective:** VFCanonicalSquareVonKochStatement remains OPEN  
**Result classes:** PAPER_PROOF (new exact triangular dyadic prime-incidence kernel and compensated divisor-profile conservation), FINITE_COMPUTATION, STRUCTURAL_NO_GO, NO_NEW_QUANTITATIVE_RESULT

## A. Bottom line

The current two-scale plan asks for a nonlocal arithmetically signed cofactor kernel after the within-shell outer-prime variable was shown to be rank one. This run supplies an exact candidate without changing the carrier.

For each dyadic shell block H <= r < 2H, aggregate a cofactor c only after it becomes legal, at r >= max(H,c). The complete local incidences then collapse to one exact prime interval. For H < c < 2H, the lower endpoint is pi(c), not a modeled square-root endpoint. This is the exact moving-cofactor boundary and it excludes p=c when c is prime.

After adding the existing smooth compensator, the resulting nonlocal coefficient E_H(c) preserves every divisor row:
the upper divisor-zeta transform of E_H is exactly the negative genuine Mobius mass of all corresponding physical shell multiples. In particular d=1 is not removed or made small: it is the full dyadic Mertens increment. Therefore this representation is source-exact and useful for analysis, but any estimate which deletes the d=1 row or norms cofactor bands before recombination is invalid.

No eta>0, shell-energy improvement, Mertens exponent improvement, canonical VF bound, or RH proof is claimed.

## B. Authority, continuity, and scheduling anomaly

Final authority refresh:

- main at 5ae5a524ca447d1936e351bbbe4b134c068a1a13, merge of PR #979.
- AGENTS.md blob 4c66a1d462df98c84deebf0069ad11f904039858.
- CURRENT_PROOF_CONTRACT.md blob 2fa9931dcdc1fc8a816aefb8aa348db12ee9a384.
- PNT-first contract blob e8acbeff24942d1f8ee0079f715afff2ddda2c33.
- Two-scale attack plan blob 0606d764ffebb4639cc0abb52ccbef30546b7764.
- Two-scale falsifier blob 20cd0af940e2b334d4b9a440e4aaa9cba7e4825f.
- External inbox blob 038018145c0fddb2f6306c0712373adf9cd1ea52.
- Source blobs: TwoABScaleTransfer.lean fae76878063583322a48a329810cc1cc7b037ee7; SquareRootMatchedTransport.lean e9ab3bff6b8819182c39721f92859679d250002e; SquareBlockSmoothTransportGram.lean 09f5e0108eb254a2f20fa2fd694d69cb455b2857; SquareRootSmoothRenewalInstantiation.lean 9a63c8c2f9e42a64c0010721a78101c1f56858b1.
- No open PR was returned at final refresh. PRs #975, #976, #978 and #979 are merged.

Today Coordinator is absent at its named path and is TODAY=PENDING. Today Owner blob 4655c4379f9a5d4b13a9f43c1c1c0addfe90d836, Analytic final readback blob ce59751e02ffde8f6711dd17f2e0da8f68c71c36, Census blob 08d80d6fe5f8114e210d6e50f5939603a511994e, Referee blob 096513f9a32d79bc6699719fcac3c997572b31f0, and the reported Lean blob 0ed62011c7a02051b634928b10ef670380033e34 were consumed. The complete October 17 reports were used as YESTERDAY=CARRY_FORWARD.

A prior same-day Wheel scheduled report existed as immutable blob 62da494755501409879e894779d026aed70835f8, although its named branch path was absent at intake and remained absent at publication. That artifact contains accepted claim 20261018-wheel-1, the strict-shell Boolean-antichain/two-prime sign-coherence theorem. Census and Referee independently consumed it; Referee accepted its exact local scope. This 12:54 scheduled invocation was therefore a duplicate schedule trigger relative to the stated one-run-per-day budget. I did not repeat its computation or claim it was missing. I performed only the newly requested post-#979 kernel audit and record the scheduling anomaly for human correction.

## C. Claim 20261018-wheel-2: exact triangular dyadic incidence kernel

Let H >= 2, 1 <= c < 2H, and

~~~
a_H(c) = max(H,c),
K_H(c) = pi(floor((4H^2-1)/c))
       - pi(floor(a_H(c)^2/c)).
~~~

Use the plan's exact strict-shell incidence

~~~
P_r(c) = pi(floor(((r+1)^2-1)/c)) - pi(floor(r^2/c)),
1 <= c <= r.
~~~

Then

~~~
sum_(a_H(c) <= r < 2H) P_r(c) = K_H(c).       (TDK)
~~~

More strongly, there is an occurrence bijection

~~~
{(r,p): a_H(c)<=r<2H, p prime, r^2<pc<(r+1)^2}
 <->
{p prime: a_H(c)^2 < pc < 4H^2},

(r,p) |-> p,       p |-> (floor(sqrt(pc)),p).
~~~

### Proof

The strict shells from a=a_H(c) through 2H-1 are disjoint and cover all nonsquares n with a^2<n<4H^2. If p is in the displayed prime interval, then p>a^2/c>=a>=c, so p does not divide c and pc is not a square. Hence r=floor(sqrt(pc)) is unique, a<=r<2H, and c<=r. Conversely every local occurrence lies in that prime interval. Counting primes gives (TDK).

The endpoint split is exact:

~~~
c <= H:       K_H(c)=pi(floor((4H^2-1)/c))-pi(floor(H^2/c));
H < c < 2H:  K_H(c)=pi(floor((4H^2-1)/c))-pi(c).
~~~

For prime c>H, the second formula excludes p=c exactly. Replacing the lower endpoint by pi(c-1), or beginning the shell sum before r=c, introduces the forbidden p=r boundary fibre.

Every counted site pc has p>r>=c. Thus p is coprime to c and is the unique prime factor of pc above the shell root. No prime-density approximation or short-interval theorem is used.

**Classification:** PAPER_PROOF / NEW EXACT NONLOCAL REPRESENTATION / ENDPOINT THEOREM.

## D. Claim 20261018-wheel-3: compensated divisor-profile conservation

Retain the plan's genuine smooth quantities in each shell:

~~~
B_r(d) = sum_(n in I_r, P+(n)<=r, d|n) mu(n),
a_r_inc(c) = sum_(k<=r/c) mu(k) B_r(kc),
e_r(c) = mu(c)P_r(c)-a_r_inc(c),
F_r(d) = sum_(n in I_r, d|n) mu(n).
~~~

The accepted finite Mobius inversion identity is

~~~
sum_(d|c, c<=r) e_r(c) = -F_r(d).             (ROW_r)
~~~

Define the aggregated smooth and compensated kernels for 1<=c<2H by

~~~
A_H(c) = sum_(a_H(c)<=r<2H) a_r_inc(c),
E_H(c) = mu(c)K_H(c)-A_H(c).
~~~

Then exactly

~~~
E_H(c) = sum_(a_H(c)<=r<2H) e_r(c),            (AGG)
~~~

and for every 1<=d<2H,

~~~
sum_(d|c, c<2H) E_H(c)
 = -sum_(max(H,d)<=r<2H) F_r(d).                (PROFILE)
~~~

### Proof

Equation (AGG) is (TDK) multiplied by mu(c), followed by the definition of A_H(c). For (PROFILE), interchange the finite c and r sums. At a fixed r, the active multiples are exactly d|c with c<=r, so (ROW_r) applies. Shells with r<d contain no legal c multiple of d, which gives the lower limit max(H,d).

At d=1 this becomes

~~~
sum_(1<=c<2H) E_H(c)
 = -sum_(H<=r<2H) delta_r
 = -(M(4H^2-1)-M(H^2)).
~~~

Thus the nonlocal kernel retains the complete d=1 signed mode. It does not solve it. For d>1, it retains the actual multiplicity, squareful zeros, strict shell walls, and smooth/high compensation without duplicating an occurrence.

**Classification:** PAPER_PROOF / NEW EXACT COMPENSATED INCIDENCE CONSERVATION / NO QUANTITATIVE SAVING.

## E. Structural consequences and physical pair geometry

1. **The outer-prime escape is genuinely across shells.** Analytic claim 20261018-analytic-1 proves the within-shell q operator is all-ones and rank one. The kernel K_H(c) removes that artificial q coordinate and leaves a real cofactor-dependent prime interval with exact moving lower wall.

2. **The d=1 obstruction is explicit.** A cofactor-band estimate is incomplete unless all bands reassemble to (PROFILE), including the band containing c=1. TAIL(Y) can pay high divisors, but (PROFILE) shows why it cannot erase the low-row signed source.

3. **Fixed-prime occurrences form monotone cofactor paths.** For a fixed high prime p, c<d implies floor(sqrt(pc)) <= floor(sqrt(pd)). If two such sites lie in one strict shell, then its cofactor interval has length (2r+1)/p<2, so the cofactors are consecutive. This recovers the accepted local adjacency restriction in its proper place. Cofactors with d>=2c are geometrically forbidden from sharing one shell and can interact only across blocks.

4. **No uniform pair sign exists.** On squarefree legal fibres, two occurrences with the same high prime have product sign mu(c)mu(d). The predeclared examples mu(2)mu(3)=+1 and mu(5)mu(6)=-1 remain exact countersectors; squareful cofactors give zero. Negative shared-prime contributions therefore couple opposite-parity cofactors along distinct shell locations (or the exceptional adjacent local pair), not a universally restorative owner edge.

5. **Native VF transfer remains separate.** Owner claims 20261018-owner-1/-2 show that Mobius-signed high-composite charge and positive native VF charge differ by the A/B/Z transfer cone with PNT-sized slack. Claims wheel-2/-3 are on the genuine unweighted Mobius shell and do not cross #915 masks, clips, native weights, historical anchor, global residual, or NNS denominator.

## F. Exact finite falsification

A fresh exact-integer checker independently built primality, pi, mu and largest-prime-factor tables.

- For every 2<=H<=79 and every 1<=c<2H, it checked (TDK), the full occurrence-set bijection, the moving c>H boundary, and the prime-c endpoint.
- For every 2<=H<=27, every shell H<=r<2H, and every divisor row 1<=d<2H, it reconstructed B_r, a_r_inc, e_r and F_r from physical integers and checked (ROW_r), (AGG), and (PROFILE).
- No random input, floating arithmetic, Li approximation, PNT asymptotic, or fitted exponent was used.
- Result: zero failures.

These finite checks test endpoints and implementation; the proofs above establish the all-scale identities.

## G. Novelty and no-circularity audit

Repository search found the local P_r(c) definition, the fixed-cofactor examples used by Owner, the outer q reindex, divisor compensation, and older reciprocal triangular transforms. It did not find the moving-cutoff formula with a_H(c)=max(H,c), its pi(c) lower branch, or the aggregated compensated PROFILE identity.

The new object is a representation, not a bound. Estimating the d=1 right side of (PROFILE) at RH scale is the original Mertens difficulty. The following are rejected:

- declaring K_H(c) small from ordinary PNT uniformly in c;
- replacing the exact lower wall by a symmetric approximate window;
- assigning a fixed negative sign to same-prime, coprime, or shared-factor pairs;
- bounding only c>1 and dropping the c=1 response;
- transferring unit Mobius weights directly to the native VF source;
- claiming a shell-energy exponent from TAIL(Y) without the enlarged low-divisor complement.

## H. Quantitative status and next missing lemma

Claims wheel-2/-3 expose a legitimate next analytic carrier:

~~~
sum_(c in a prescribed band) E_H(c)
 = sum_c mu(c)K_H(c) - sum_c A_H(c),
~~~

with K_H(c) an exact prime interval and A_H(c) the complete smooth companion. A useful independent theorem would give a power-saving estimate for a signed band or a joint family of divisor rows, then bound all complementary bands and retain d=1 until final reassembly. It must exploit arithmetic cancellation in mu(c) against the moving prime interval and smooth response; ordinary PNT, within-shell q dispersion, or absolute divisor counts do not suffice.

The most precise next experiment is to pre-register cofactor bands crossing c=H, compare the two exact lower branches, and measure the joint signed prime term, smooth term, and E_H(c), together with every divisor row. A candidate theorem should be falsified first on prime c just above H and on the known sign-reversal roots.

No new eta, no shell-energy bound, no Mertens gain, no finite A/C estimate, no canonical endpoint result, and no RH proof.

## I. Handoffs and resume capsule

- **Coordinator:** insert K_H/E_H after the rank-one gate. It is a true cross-shell cofactor operator, not a second outer-prime dispersion variable.
- **Owner:** any native bridge must add the transfer-cone slack and preserve masks, weights, anchor and residual. The raw E_H kernel is not admitted #915 source.
- **Analytic:** attack the exact two-branch kernel jointly with A_H(c); state conductor/range uniformity and retain c=1 and all bands.
- **Census:** test bands crossing c=H on fresh held-out H. Record prime, smooth and compensated pieces separately and verify (PROFILE) before any normalization.
- **Referee:** audit the p=c boundary, occurrence bijection, finite-sum interchange, d=1 conservation, and novelty against older reciprocal transforms.
- **Lean:** after independent acceptance, (TDK) and (PROFILE) are exact formalization candidates. Attach no quantitative consumer.

Resume from claims 20261018-wheel-2 and -3. The first missing mathematical input is an independent power-saving bound on a complete signed portion of E_H with a proved small complement. Claims 20261018-wheel-1, Census's t=3 refutation, Analytic's rank-one obstruction, Owner's transfer cone, and merged #978/#979 remain active constraints.

No RH proof claim.


## J. Publication verification

Substantive report commit 6a04f6c42d0e58f25351069af1d1ceb6ee5b77c1 was created on agent-reports. Immediate readback returned blob d3eadf14ed5478090a3b5c1d33fe9ffdbfaa4ce4, 12,769 characters, with COMPLETED status and both claim IDs present. Final main authority remained 5ae5a524ca447d1936e351bbbe4b134c068a1a13 and the open-PR search remained empty.


Post-publication workflow verification: PR #979 proof/document head 9c3535d9cadc7016f39071c00ed2e1cc344c4911 has four pull-request workflow runs, all completed successfully. PR #978 proof head ba89ca4e5fc6a341ca0422698ec40b4646480000 has ten returned pull-request workflow runs, all completed successfully, including the dedicated PNT-first Lambda hyperbola and anchor Lean job and Lean source audits. These workflows certify their respective merged heads; they do not certify claims wheel-2/-3, which remain PAPER_PROOF plus independent finite verification pending Referee/Lean review.

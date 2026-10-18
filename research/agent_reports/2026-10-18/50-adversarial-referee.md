# RH_Lean agent daily report - 2026-10-18 / RH | Adversarial Referee

**Status:** COMPLETED  
**Run ID:** 2026-10-18T03:34:01-04:00, scheduled invocation  
**Canonical objective:** `VFCanonicalSquareVonKochStatement` remains OPEN  
**Result classes:** `PAPER_PROOF / ACCEPT` (square-shell antichain and two-prime local no-go), `FINITE_EXACT_REFUTATION` (first-cancelling-depth mechanism), `PROVED_IN_LEAN_ON_PR_HEAD / SCOPE_ONLY` (#975), `NO_NEW_QUANTITATIVE_RESULT`

## A. Bottom line

I independently accept Wheel claim `20261018-wheel-1` at its exact stated scope: active divisor faces inside one strict square shell are antichains, and a two-prime Boolean orbit is sign-coherent. The proof is exact and source-faithful for the genuine unweighted Möbius shell. It yields a legitimate local-mechanism no-go, not a covariance estimate and not a #915 source bridge.

I also independently reproduced and strengthened the Census falsifier. The assertion that the first locally cancelling unshared-depth class `t=3` controls the sign of complete shell covariance already fails in the smallest shell found by exhaustive exact search:

```text
r=9, I_9={82,...,99}, nonzero sites
{82,83,85,86,87,89,91,93,94,95,97}.

D_9=11, Delta_9=5, C_9=(Delta_9^2-D_9)/2=7.
A_2=8, A_3=24, A_4=23.
```

Thus

```text
D_9 + 2(A_2-A_3) = -21,
D_9 + 2(A_2-A_3+A_4) = 25 = Delta_9^2.
```

The negative `t=3` cohort is not merely insufficient asymptotically: even the first-depth truncation ceases to be a nonnegative energy on genuine arithmetic, and the next even-depth cohort reverses the conclusion exactly. Any proposed proof that norms or signs the `t=3` class before restoring every higher-depth interaction is invalid.

No `kappa>0`, shell `5/2-kappa` estimate, weighted covariance theorem below `eps=3/8`, canonical endpoint bound, or RH proof is established.

## B. Authority, continuity, and live status

Final authority refresh:

- `main@5b218172f995afa8c10f062622c009d490d3b2b2`, merge of PR #974.
- `AGENTS.md` blob `aef9d6f7a7d3a091f947effd38e9ad42a63e8445`.
- `CURRENT_PROOF_CONTRACT.md` blob `873ec6f70525e1e9ba1defecf8b0951ebe155069`.
- Dynamic protocol blob `f070f8731ba560fe055045f7d5f6b0224afdda28`.
- Signed covariance contract blob `8d846d6ee5d559065687b2ed5144aeb7ca3e1850`.
- Merged ancestry/covariance Lean source blob `39ef1181fed1bf217fb4409c9ec3cdb96500ce18`.
- Companion paper blob `f61a337fb79e2f1d74da6f7094d256f8eb379b16`.
- Native ancestry-root source blob `1b1bc51a6561a192b9e6375ae8df7a36079c4c50`.
- External inbox blob `3cd80e68cec54cc9ce1e00a384cfe37a3a3babc0`.

The complete 2026-10-17 reports were consumed as `YESTERDAY=CARRY_FORWARD`: Coordinator `9a797b07dcd7c74147b6b0cdbc8f6a69024c3961`, Owner `6980422de5f7cc55b9dec32a2f0fe21f98ed7ff1`, Analytic `08e96ac308fc08f59f2e4f5c82a70ba7d901c97e`, Wheel `dbaefd4005c2cc93b894f9bb97c7a74c5f28dc49`, Census `9efa34cd7a2d3c021b20779889eaaf6a556020d3`, Referee `a3867e19b4e6e409c09ab69899a628d042f11a8d`, Lean `1a03815f26aa6ee145d94c9848ac37483b093033`.

At intake, today Coordinator/Owner/Analytic/Referee/Lean were `TODAY=PENDING`. Today's Wheel artifact was retrieved by immutable blob `62da494755501409879e894779d026aed70835f8`; its named path was absent at final fetch, so I rely on the immutable blob rather than infer branch history. Today's Census report is blob `08d80d6fe5f8114e210d6e50f5939603a511994e`.

PR status and exact-head CI:

- #968 is merged; proof head `4f88a1d2b88c3ee4a34b0619a114167d0218a964`; all 11 returned workflows succeeded.
- #969 has `merged=true` at merge commit `8fdb90d50b59c964eac142fc8b3d9fcd780af281`, but it was merged into its stacked feature base, not `main`. Its three changed files are absent from live `main`; proof head `f839a3ae41ab0f76a38df5f2ad0498c6105fde67` has five successful returned workflows. Status remains `PROVED_IN_LEAN_ON_NONMAIN_BRANCH / INTEGRATION_REQUIRED`.
- #973 is merged at `5aa5eb28c352882b8c8cd8d3e0714ddc5afcc555`.
- #974 is merged at current main; proof head `124c8c1b8084442ae2d1ca9f7bbd836517629e07`; all eleven returned workflows, including dedicated warning-fatal Lean, succeeded.
- #975 is the only open PR, draft at head `d3e0cdc1ab306c94ef4a04acdc20c513e72c31e5`; all eleven returned workflows succeeded. It remains unmerged.

## C. Claim `20261018-referee-1`: Wheel antichain verdict

**Statement reviewed.** For the strict shell
```text
I_r={n : r^2<n<(r+1)^2},
```
squarefree `Q), squarefree `m` coprime to `Q), and
```text
A_(r,Q)(m)={d : d|Q and md in I_r},
```
the active divisor face is an antichain. For `Q=pq` with distinct primes, every nonempty face is a singleton or `{p,q}`; therefore its Möbius signs are coherent and its absolute orbit sum equals its population.

**Independent proof reconstruction.** If `x<y` lie in `I_r`, then
```text
2x-y >= 2(r^2+1)-(r^2+2r)=(r-1)^2+1>0,
```
so `y<2x`. Distinct positive comparable divisors satisfy `e>=2d`; hence `md,me` cannot both lie in the shell. For squarefree `n), the map
```text
d=gcd(n,Q), m=n/d
```
is unique, has `d|Q`, and gives `gcd(m,Q)=1). Thus the orbit partition is once-only. In the two-prime divisor lattice, `{p,q}` is the only nonsingleton antichain; both have Möbius sign `-1`, so multiplication by the common `mu(m)` preserves sign coherence. The claimed `l1` equality follows orbit by orbit.

The sharpness witness `r=10,Q=42,m=17` is valid: active divisors `6,7` give sites `102,119` with opposite Möbius signs. The smaller reported witness `r=2,Q=30,m=1`, sites `5,6`, is also valid.

**Verdict:** `ACCEPT / PAPER_PROOF / EXACT STRUCTURAL NO-GO`.

**Scope:** this rules out internal cancellation in one- and two-prime Boolean orbits only. It does not rule out cross-base cancellation, at-least-three-prime faces, nonlocal owner response, the Hecke low-variation route, or the complete shell-energy theorem. It has no automatic bridge to #915 weights, masks, clipping, returned cells, anchors, or restoration.

**Lean nomination:** after this review, the nonduplicate formalization candidate is precisely the strict-shell subdoubling lemma, the divisor-face antichain theorem, and its two-prime sign-coherence/`l1` corollary. No quantitative consumer should be attached.

## D. Claim `20261018-referee-2`: first-depth control is refuted

For each genuine squarefree pair `a<b` in `I_r), let
```text
g=gcd(a,b), t=omega(a/g)+omega(b/g),
A_t(r)=#{a<b in I_r : mu(a)mu(b) != 0 and unshared depth=t}.
```
Squarefree parity gives the exact complete identity
```text
Delta_r^2=D_r+2 sum_(t>=2)(-1)^t A_t(r).
```

The `r=9` data above satisfy every hypothesis and yield the exact histogram
```text
t=2: 8,   t=3: 24,   t=4: 23.
```
Every pair is included: `8+24+23=55=binom(11,2)`. Direct signs give
```text
C_9=8-24+23=7.
```

**Verdicts:**

- “The first cancelling class `t=3` forces nonpositive complete shell covariance”: `REFUTED_THEOREM`.
- “Truncation through `t=3` is a valid nonnegative energy surrogate”: `REFUTED_THEOREM`.
- The all-depth parity partition itself: `ACCEPT / EXACT IDENTITY`.
- A uniform shell `5/2-kappa` gain: `UNRESOLVED`.

The independent enumerator used a linear Möbius sieve, exact gcds, exact factor depths, and every unordered nonzero-Möbius pair. It found no earlier `r>=2` with `A_3(r)>0` and `C_r>0`; this minimality is a finite exhaustive statement through `r=9`.

The smallest positive dyadic complete covariance in the checked powers of two is already
```text
H=8: sum D_r=118, sum Delta_r^2=176,
sum C_r=29, sum A_3(r)=339.
```
The larger Census values were independently reproduced exactly:
```text
H=64:  C=-167, A3=95234
H=128: C=+3870, A3=629718
H=256: C=-4650, A3=4221545
H=512: C=+4417, A3=28613104.
```
Hence neither single-shell nor dyadic sign is controlled by the magnitude or negativity of the first cancelling cohort.

## E. No-circularity and strongest surviving theorem

The honest surviving theorem is the complete alternating-depth identity, together with the two-prime orbit no-go. It says what a successful mechanism must preserve: all depths, all cross-base pairs, and exact shell boundaries.

A proposed “recurrence” for `A_t(H)` is genuine progress only if it is derived from independent arithmetic incidence and its tail estimate is proved before recombination. Merely assuming
```text
sum_t (-1)^t A_t(H)=O(H^(5/2-kappa+eta))
```
is the desired shell covariance estimate in new notation and is `TARGET_EQUIVALENT`. Bounding only `A_3`, or any fixed initial segment without a separately paid alternating tail, cannot imply the target; `r=9` is an exact source-faithful obstruction.

The useful next theorem is therefore narrower than the final shell bound but must involve at least one real cross-depth relation, for example a signed incidence map between `A_{2j+1}` and `A_{2j+2}` with once-only multiplicity and a quantified residual uniform in both `j` and dyadic `H`. A fixed-depth pairing is insufficient unless the remaining depths are paid uniformly.

## F. PR #975 scope gate

Live #975 proves, on its green but unmerged head, exact original-carrier algebra culminating in:
```text
VFMidActualPrimeFirstBadAt 2 (R+1), R>=64
  ==> 0 < vfMidActiveGlobalResidualExcess R.
```

**Verdict:** `PROVED_IN_LEAN_ON_PR_HEAD / FORMAL_SCOPE_ACCEPTED / NO_SIGNED_GAIN`.

The theorem is a necessary consequence at a hypothetical first bad. It neither rules out the first bad nor signs the boundary excess. The companion diagnostic itself computes the three-boundary residual as `E-G`, not by an independent raw-parent enumeration. Accordingly this blocks a boundary-only nonpositive-domination proof shape, but does not prove the canonical estimate, a covariance gain, child-run descent, or #974-to-#915 source admission sufficient for payment. Draft/unmerged status must be retained.

## G. Strategy decision and handoff

- **Two-prime within-orbit cancellation:** retire; Wheel theorem accepted.
- **Three-face-first mechanism:** retire as a sign-control principle; exact genuine counterexample at `r=9`.
- **Complete all-depth shell route:** continue only with an independent cross-depth or cross-base signed estimate.
- **Projection/second-centering identities:** retain as falsification coordinates, not achieved bounds.
- **Hecke low variation:** unaffected; merged high-side payment does not bound `V_low`.
- **#975:** useful obstruction on the original first-bad architecture, but not an arithmetic saving.

Next Referee action should attack any proposed adjacent-depth recurrence at its residual/tail quantifiers and search for a genuine arithmetic family defeating fixed-depth closure. Do not rerun the already reproduced dyadic bands without a new theorem-shaped discriminator.

No RH proof claim.

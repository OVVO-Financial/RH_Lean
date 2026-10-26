# RH_Lean agent daily report - 2026-10-26 / RH | Finite Wheel & Incidence

**Status:** COMPLETED  
**Invocation:** one scheduled run, 2026-10-26 00:09 America/New_York  
**Pinned main:** `06f488aca201f5806c8ac40923be9f73a917b1c3`  
**Primary route:** CORR4 signed first-owner Gram  
**Registry nodes:** `MECH-CORR4-SIGNED-FIRST-OWNER-GRAM`, `NOGO-CORR4-FRAME-ONLY`, `OPEN-CORR4-MIXED-TAIL-POWER`  
**Result classes:** `PAPER_PROOF_NEEDS_REVIEW / NEW EXACT LATTICE DEFECT`, `FINITE_COMPUTATION`, `NO_NEW_GLOBAL_QUANTITATIVE_BOUND`

## A. Main result

### Claim `20261026-wheel-1`: the genuine q2 daughter frame has an exact integral Lagrange defect

Fix `R`, let `Q_R=canonicalRoughLowQ2Owners R`, put
`X=R^2-1`, `Y_q=floor(X/q^2)`, and write

```text
d_q = M(Y_q) in Z,
s_R = sum_(q in Q_R) 1/q^2,
U_R = sum_(q in Q_R) d_q/q,
E_R = sum_(q in Q_R) d_q^2.
```

Then the ordinary Lagrange identity gives the exact arithmetic invariant

```text
s_R E_R - U_R^2
  = sum_{q<r in Q_R} (d_r/q - d_q/r)^2
  = sum_{q<r in Q_R} (r*d_r-q*d_q)^2/(q*r)^2.       (1)
```

This is stronger information than an arbitrary scalar frame. Every numerator
in the last sum is an integer.

Consequences:

1. Equality in the sharp actual-owner Cauchy frame holds iff `q*d_q` is
   one common integer `L` for every `q in Q_R`.
2. If one pair is misaligned, then `q^2<R` and `r^2<R` imply `q*r<R`,
   so
   ```text
   s_R E_R-U_R^2 > 1/R^2.                            (2)
   ```
3. For every `R>=290`, the aligned alternative is impossible unless
   every `d_q=0`. Hence every nonzero genuine daughter vector satisfies
   the strict quantitative defect (2).

The third point uses unique factorization, not real-vector algebra. If
`q*d_q=L` for all low owners, their product `P_R=prod_(q in Q_R) q`
divides `L`. Let `p` be the largest low owner and `p'` the next prime.
The trivial Mertens bound gives

```text
|L| = p |M(floor(X/p^2))| <= X/p.
```

At the base `p=17`,
`3*5*7*11*13*17=255255 > 16*17^3=78608`.
Bertrand gives `p'<2p`. Induction over consecutive primes preserves
`P_R>16p^3`, because after adjoining `p'` one has
`p^3>(p')^2` for `p>=17`. Since maximality of `p` gives
`R<=(p')^2`,

```text
X/p < (p')^4/p < 16p^3 < P_R.
```

Thus a multiple `L` of `P_R` with `|L|<P_R` must be zero.

**Scope.** This is a genuine all-scale arithmetic restriction for
`R>=290`: exact frame saturation is forbidden outside the zero daughter
vector. It does not supply a useful relative gap. Since `E_R` can be very
large, an absolute defect of order `R^-2` is many powers too small for
`OPEN-CORR4-MIXED-TAIL-POWER`. Near-saturation at the power scale remains
unexcluded. The result therefore supports, rather than overturns,
`NOGO-CORR4-FRAME-ONLY`.

## B. Exact relation to the live carrier

The main carrier is unchanged:

```text
C_R = M(R-1)-M(X),
B_R = C_R-U_R,
E_R = sum_q d_q^2.
```

Identity (1) retains every owner and every cross-owner product before taking a
bound. It concerns the genuine integer daughter coordinates used by
`lowOwnerReciprocalMertensColumnReal` and
`canonicalRoughLowQ2DaughterEnergy`; it does not replace the physical
remainder or its first-owner Gram.

The live mixed-tail source still contains the endpoint term and all prefix-tail
interactions. Main proves

```text
2 * PrefixTailMixed_R = Post789Remainder_R + PrefixDiagonal_R,
```

so a daughter-frame defect alone cannot pay it. Draft PR #1026, discovered
during the final live refresh, makes this obstruction even more explicit under
a record-energy hypothesis. Claim `20261026-wheel-1` is distinct: it is an
unconditional lattice identity on the daughter vector, while #1026 is a
conditional lower obstruction for the full mixed tail.

## C. Falsification and finite checks

An independent exact linear Möbius sieve checked (1), the endpoint split, and
the scale of the defect. The relevant values were:

| R | owners | s_R E_R-U_R^2 | nonzero pair defects | smallest nonzero pair term |
|---:|---:|---:|---:|---:|
| 56 | 3 | 0.924263038548753 | 3/3 | 0.003265306122449 |
| 317 | 6 | 60.6891595699243 | 15/15 | 0.034178377233246 |
| 1027 | 10 | 1582.84182942103 | 45/45 | 0.004668029782802 |
| 5561 | 20 | 24552.4301319454 | 189/190 | 0.000264147397698 |

The direct pair sum agreed with `s_R E_R-U_R^2` to displayed precision.
At `R=5561` one pair has equal scaled values `q*d_q=r*d_r`; this is a useful
falsifier for any claim that every pair is individually separated. The global
primorial argument, not pairwise distinctness, rules out complete nonzero
alignment.

The same sieve also reproduced the exact prefix/top split:

| R | M(R-1) | M(floor(X/9)) | M(X) | B_R | top-tail contribution M(floor(X/9))-M(X) |
|---:|---:|---:|---:|---:|---:|
| 56 | -2 | 2 | 6 | -8.323809523810 | -4 |
| 317 | -3 | -2 | -28 | 27.308260367084 | 26 |
| 1027 | -4 | 83 | 367 | -391.680017555430 | -284 |
| 5561 | 5 | -407 | -2544 | 2670.191365728089 | 2137 |

This confirms why the lattice defect does not control the complete bill:
large observed physical remainders contain a top tail invisible to every
low-q2 prefix.

## D. Novelty and no-circularity audit

The first candidate from this run was the support observation that every low
daughter ends by `floor(X/9)`. It is not new: the docstring of
`scripts/returned_core_site_probe.py` already records it, and
`GLOBAL_RETURNED_CORE_PREFIX_TAIL_MIXED_REMAINDER_IDENTITY.lean` proves the
stronger abstract prefix-tail/post-789 equivalence. Existing terminal
classification also gives stronger unmatched top-prime witnesses. That
candidate was rejected rather than promoted.

Repository searches found no existing reciprocal-frame Lagrange identity,
integer-numerator defect, or primorial exclusion of the aligned Mertens
daughter mode. Claim `20261026-wheel-1` is therefore classified as a new
paper theorem needing independent review, not as Lean-certified mathematics.

No target-equivalent estimate is assumed. The proof uses only finite algebra,
integrality of Mertens values, `|M(N)|<=N`, unique factorization of a product
of distinct primes, and Bertrand's theorem. It proves neither a fixed positive
relative frame gap nor a signed mixed-tail estimate.

## E. Authority and continuity

Final authority remained:

- main `06f488aca201f5806c8ac40923be9f73a917b1c3`;
- `AGENTS.md` blob `a99b2a3ea04cdebbdd124a8810a2c07a9522c214`;
- `CURRENT_PROOF_CONTRACT.md` blob
  `03c96af2cf4f7e678b7e0c050725e0e9891f5608`;
- previous Wheel report blob
  `414415d53bfedd14ae9b72ed3cc55f65c1477a21`;
- external handoff index blob
  `038018145c0fddb2f6306c0712373adf9cd1ea52`.

At intake no 2026-10-26 report directory existed, so `TODAY=PENDING`. The
complete 2026-10-25 set was consumed as `YESTERDAY=CARRY_FORWARD`:
Coordinator `20261025-coordinator-1`, Owner `20261025-owner-1`, Analytic
report, Wheel `20261025-wheel-1`, Census `20261025-census-1`, Referee
`20261025-referee-1`, and Lean Verification. No external handoff is newer
than 2026-10-18.

The canonical `VFCanonicalSquareVonKochStatement`, CORR4, finite A/C,
`OPEN-CORR4-MIXED-TAIL-POWER`, any exponent below imported 7/8, and RH all
remain OPEN.

## F. GitHub and CI audit

PRs #1021--#1024 are merged on main; #1021's conditional power equivalence is
proved, not its open premise. At final refresh a new draft PR #1026 existed at
head `5dba4b6cced298985659948f72ac7bcf20821e21`, base
`06f488aca201f5806c8ac40923be9f73a917b1c3`. Nine observed workflows were
successful and `Targeted Lean iteration` run `40267738497` was still in
progress. Therefore #1026 is `CI_PENDING / NOT PROMOTED` in this report.

This agent created no proof PR, changed no Lean source, reviewed no PR, and
performed no merge or auto-merge.

## G. Next action

The lattice restriction says exactly what a useful strengthening must add.
A future argument must control the sum in (1) at the natural energy scale, or
couple its nonzero defects to the endpoint/mixed-tail term. Merely knowing that
one integer numerator is nonzero yields only `R^-2`.

A decisive next hypothesis is a source-faithful lower bound of the form

```text
sum_{q<r} (r*d_r-q*d_q)^2/(q*r)^2 >= delta * E_R
```

on endpoint-excursion roots for one absolute `delta>0`, together with the
correct signed bridge to the full mixed tail. The immediate falsifier is a
genuine sequence of roots where the normalized lattice defect
`(s_R E_R-U_R^2)/E_R` tends to zero while the endpoint bill stays large.
This is a focused Census request, not a request for a larger undirected wheel.

## H. Resume capsule

Resume from main `06f488aca201f5806c8ac40923be9f73a917b1c3`, claim
`20261026-wheel-1`, and draft #1026 head
`5dba4b6cced298985659948f72ac7bcf20821e21`.

New exact structural fact:

```text
s_R E_R-U_R^2
 = sum_{q<r}(r M(Y_r)-q M(Y_q))^2/(qr)^2.
```

For `R>=290`, a nonzero daughter vector cannot saturate the actual sharp
frame, and its absolute defect exceeds `R^-2`. This is real arithmetic
rigidity but not a power-saving estimate. The complete signed mixed tail
remains the decisive blocker.

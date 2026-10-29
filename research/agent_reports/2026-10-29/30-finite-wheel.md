# RH_Lean agent daily report - 2026-10-29 / RH | Finite Wheel & Incidence

**Status:** COMPLETED
**Invocation:** scheduled run begun 2026-10-29 00:09 America/New_York
**Pinned and final-refreshed main:** `a59d351aa33c3cc071ab7b9221f765dc89a2012c`
**Main authority blobs:** `AGENTS.md` `4bc5e5bacd333be41ca9334fa6eaf8e29b9bd1c8`; `CURRENT_PROOF_CONTRACT.md` `24bd727096001b68c76b28fe70c99b8d548d7bfe`
**Material main blobs:** `research/EULER_FRACTIONAL_COUPLED_20261027.lean` `e6c4b1690e497760d366e36b28a1f7aa60e19f85`; `research/EULER_SQUARE_WINDOW_SHARED_GCD_20261028.md` `7ad1718d78a6afaac87f32ad9e1cc5a45f822164`; `research/OAI_PAIRED_SHARP_EULER_SQUARE_LOCALIZATION_20261028.lean` `1f5b2e57f24e44e5b7b5cea80d437ac8350365b0`
**External handoffs blob:** `038018145c0fddb2f6306c0712373adf9cd1ea52`
**New claim:** `20261029-wheel-1`
**Result classes:** `PAPER_PROOF_NEEDS_REVIEW / NEW PRIME-INCIDENCE PRINCIPAL OBSTRUCTION`, `PAPER_PROOF / COMPLETE-ORBIT ENERGY FLOOR`, `FINITE_COMPUTATION`, `NO_FIXED_ETA_GAIN`, `NO_RH`.

## A. Main result

### Claim `20261029-wheel-1`: the true first-prime square-clock row has a coherent principal debt and nonvanishing centered energy

For a prime `p`, retain the actual square-clock column and its literal root-residue mean from draft PR #1051:

```text
f_p(R) = ((R^2 - 1) mod p) / p,
m_p = (1/p) sum_(r mod p) f_p(r),
G_p(R) = f_p(R) - m_p.
```

The original symmetric `a=1,b=p` contribution to `2*eulerFractionOffQ(R)` is

```text
U_Q(R) = -2 sum_(p<=Q, prime) f_p(R)
       = U_Q^principal - 2 sum_(p<=Q, prime) G_p(R),
U_Q^principal = -2 sum_(p<=Q, prime) m_p.
```

Then:

1. **Uniform positive principal mean.**

   ```text
   m_2 = 1/4,
   m_p >= (p^2 - 1)/(8p^2) >= 1/9       for every odd prime p.       (1)
   ```

   Consequently, for every integer `Q>=2`,

   ```text
   U_Q^principal
     <= -1/2 - (2/9)*(pi(Q)-1).                                     (2)
   ```

   The prime-row principal frequency is therefore sign-coherent, negative, and unbounded. Centering is a valid nonprincipal decomposition, but it removes a compulsory original-source bill; it is not cancellation of that bill.

2. **Uniform variance floor.** Put

   ```text
   v_p = (1/p) sum_(r mod p) G_p(r)^2.
   ```

   Then

   ```text
   v_p >= 1/96                                                       (3)
   ```

   for every prime `p` (indeed `v_2=1/16`).

3. **Exact complete-orbit energy floor.** Let

   ```text
   P_Q = product_(p<=Q, prime) p.
   ```

   The coprime CRT covariance theorem at PR #1051 gives zero complete-orbit cross covariance for distinct primes. Hence

   ```text
   (1/P_Q) sum_(R mod P_Q)
     |-2 sum_(p<=Q, prime) G_p(R)|^2
       = 4 sum_(p<=Q, prime) v_p
       >= pi(Q)/24.                                                  (4)
   ```

Equation (2) is the main structural obstruction. Any source-faithful use of the new centered low-conductor moment must compensate this negative principal mode with composite-product principal modes, the diagonal/rank-one sector, or another explicitly retained original term. Equation (4) separately shows that even the nonprincipal first-prime sector is not a zero-energy coordinate artifact.

## B. Proof

For odd prime `p`, set

```text
y_r = (r^2 - 1) mod p in {0,...,p-1}.
```

The squaring map modulo `p` has exactly

```text
k = (p+1)/2
```

distinct values. Translation by `-1` preserves support size, so the multiset `{y_r:r mod p}` contains `k` distinct nonnegative integers. Therefore

```text
sum_(r mod p) y_r
  >= 0+1+...+(k-1)
  = k(k-1)/2.
```

Since `m_p=(sum_r y_r)/p^2`, this gives

```text
m_p >= k(k-1)/(2p^2) = (p^2-1)/(8p^2).
```

For `p>=3`, the right side is at least `1/9`. Direct evaluation gives `m_2=1/4`, proving (1)-(2).

For the variance, let `S_p` be the distinct support of the integers `y_r`. Dropping repeated observations can only decrease a sum of nonnegative squares, so

```text
v_p
 = (1/p) sum_r (y_r/p-m_p)^2
 >= (1/p^3) sum_(s in S_p) (s-p*m_p)^2.
```

For every set of `k` distinct integers and every real `c`,

```text
sum_(s in S) (s-c)^2 >= k(k^2-1)/12,                                (5)
```

because consecutive integers minimize the centered second moment. Thus, for odd `p`,

```text
v_p >= k(k^2-1)/(12p^3)
     = (p^3+3p^2-p-3)/(96p^3)
     > 1/96.
```

The direct `p=2` value is `1/16`. This proves (3). Expanding the square in (4), the exact CRT tensor identity kills every `p!=q` complete-orbit covariance, while the diagonal is `4 sum_p v_p). Equation (3) finishes (4).

The proof uses only the prime-square fibre cardinality, distinct-integer incidence, an elementary variance inequality, and exact CRT orthogonality. It uses no Mertens envelope, prime-density heuristic, OAI exponent, random signs, finite-C assumption, or RH.

## C. Relation to today's Analytic result

Today Analytic Type II claim `20261029-analytic-1`, report blob `0c0a7af4266e0b374ad40d36ddf01e0f0fbe25dc`, proves a new upper bound for the complete centered low-conductor off-diagonal source:

```text
sum_(H<=R<2H) |L_Q(R)|^2
  <= C_epsilon*(H*Q^(1+epsilon)+Q^(4+epsilon)),
```

where `L_Q(R)=2 sum_(d<=Q) alpha_d F_d(R)` and the exact product-incidence coefficient is

```text
alpha_d = mu(t)*2^(omega(t)-1)  if d=s^2*t, s,t squarefree, (s,t)=1, t>1,
alpha_d = 0                    otherwise.
```

For prime `d=p`, `alpha_p=-1`, so its first-prime subsector is exactly the carrier in this report. Claim `20261029-wheel-1` supplies two missing lower-side structural facts:

- the excluded principal mean is not small or sign-balanced within the prime row;
- the centered prime row has a complete-orbit energy floor, so CRT orthogonality is cancellation of cross terms, not annihilation of the source.

This does not contradict the Analytic upper bound. It identifies the precise principal compensation and diagonal scale that any full reconstruction must retain.

## D. Quantitative relevance and limitations

The result is independent and source-faithful, but it does not activate a terminal consumer.

It does **not** prove:

- a lower bound on every dyadic incomplete interval `H<=R<2H`; equation (4) is a complete `P_Q`-orbit identity;
- that composite-product principal modes fail to compensate (2);
- a bound for the high-conductor complement `ab>Q`;
- a mixed bound between centered low/high sectors;
- the required sharp shell estimate `sum |Delta_R|^2 << H^(5/2-eta+epsilon)`;
- finite A/C, a strict exponent below `7/8`, the canonical VF bound, or RH.

Nor may (2) be spent as a favorable negative contribution after a positive norm or absolute value. It is a signed principal mode that must be recombined with all original terms before estimation.

The structural consequence is a falsification gate:

> A proposed Euler low-conductor proof that centers the square-clock columns and then omits the principal reconstruction is not source-faithful. A proposed claim that pairwise coprime CRT orthogonality makes the centered prime row negligible is false on complete orbits by (4).

## E. Falsification, novelty, and finite checks

Repository search and the live PR #1051 paper blob `17fd5a56e16f8f9d8fd14a64acbebdfc6bce832d` found the definition of `m_p`, the exact coprime covariance zero, and the all-`H` upper bound. They did not state a uniform positive lower bound for `m_p`, the coherent principal debt (2), the variance lower bound (3), or the complete-orbit floor (4).

Exact rational verification tested every prime `p<=5000`:

- minimum observed mean was `m_3=2/9`, above the certified `1/9`;
- minimum observed variance was `v_2=1/16`, above `1/96`;
- all pointwise inequalities (1) and (3) passed.

Selected aggregate checks:

| Q | pi(Q) | U_Q principal | centered complete-orbit mean energy | certified principal upper bound | certified energy lower bound |
|---:|---:|---:|---:|---:|---:|
| 100 | 25 | -21.160869... | 8.907492... | -5.833333... | 1.041666... |
| 1000 | 168 | -160.156132... | 57.770774... | -37.611111... | 7 |
| 5000 | 669 | -655.796096... | 226.772664... | -148.944444... | 27.875 |

These computations are regression evidence only; Section B is the universal proof.

A possible stronger statement that the full cubefree principal bill has one sign is **not claimed**. Small exact partial sums of `2 sum_(d<=Q) alpha_d m_d` change sign, so prime-only coherence cannot be extrapolated through composite product moduli.

## F. Authority, continuity, and GitHub state

At final refresh, main remained `a59d351aa33c3cc071ab7b9221f765dc89a2012c`, the merge of #1047. Merged #1046 supplies the exact moving-square gate/shared-gcd infrastructure; merged #1047 supplies the genuine OAI sharp norm-fibre to moving Euler square-shell localization. Neither proves a signed local moment.

Today's upstream availability:

- Analytic Type II: blob `0c0a7af4266e0b374ad40d36ddf01e0f0fbe25dc`, claim `20261029-analytic-1`, consumed;
- Coordinator, Owner Payment, Prime Census, Adversarial Referee, Lean Verification: `TODAY=PENDING`;
- this Wheel report did not exist at intake and is the authorized current stage.

The complete 2026-10-28 continuity was consumed as `YESTERDAY=CARRY_FORWARD`:

- Coordinator `162f82242e8eb84f4ed21c1e59342edf3400b6cd`, claim `20261028-coordinator-1`;
- Owner `af67eace39fb00261953a92de1f7067489be7546`, corrected claim `20261028-owner-1`;
- Wheel `27dd840bb424d551f2dce0beebd7b0d2f66622f0`, claim `20261028-wheel-1`;
- Census `dca77bca7ed46d5d9fccbd05a565ed10c000a6c8`, claim `20261028-census-1`;
- Referee `fabec6a00f43ded6139256072d228024d62a015c`, claims `20261028-referee-1..2`;
- Lean Verification `9698f817e44105033409f90d98b2e018cf727ac8`, claim `20261028-lean-1`;
- no 2026-10-28 Analytic report existed, so its 2026-10-27 report remained its own carry-forward.

The external inbox has no item newer than 2026-10-18. `EXT-20261018-PNT-1/2/3` remain an exact direct-VF identity, finite falsifiers, and legal source no-gos; they neither imply nor conflict with this Euler principal theorem.

Open PR state at final refresh:

- #1048 head `179655dd3b80387af9955cf628d21cff6305b7c3`, open, non-draft, mergeable;
- #1049 head `24b6490c1ea65dc8340bcdbc1c2a83cc64edca21`, open, non-draft, mergeable;
- #1050 head `8930575b88813094ae44cfa87b4ff8c3faf20d1f`, open, non-draft, mergeable;
- #1051 head `3d687adfbfd080167e6eedbd5c0185640428f39f`, open draft, mergeable.

Green exact-head CI on these PRs certifies their stated declarations, not claim `20261029-wheel-1`, which is not formalized.

## G. Handoffs and next step

**Adversarial Referee:** verify the support-cardinality proof of (1), the distinct-integer variance inequality (5), and the normalization in (3)-(4). In particular, check that dropping repeated square residues is used only for a lower bound and that the factor `1/p^3` is correct.

**Analytic Type II:** restore the principal low-conductor bill

```text
2 sum_(d<=Q) alpha_d m_d
```

before combining the centered estimate with the high-conductor source. The prime subbill is forced negative by (2), while composite product modes can have either compensating sign. The next useful theorem is an exact principal decomposition by square part `s` and squarefree part `t`, followed by a bound that retains their interaction rather than taking absolute values prime by prime.

**Prime Census:** no large scan is requested. A decisive small exact experiment would classify the sign and size of the full principal partial sums by `s^2 t` incidence and identify the smallest composite compensation of the prime debt.

**Lean Verification:** formalize only after referee acceptance and dependency acceptance for #1051. The highest-value declarations are the prime mean lower bound and complete-orbit energy floor, not another copy of the CRT-zero theorem.

**Coordinator:** proposed node `NOGO-EULER-CENTERED-PRIME-PRINCIPAL-OMISSION`; logical status `PAPER_PROOF_NEEDS_REVIEW`, formal status `NOT_FORMALIZED`. This is a source-preservation obstruction and lower-side scale theorem, not a new edge to a fixed-`eta` consumer.

**Next Wheel run:** investigate the exact full principal sum by the unique factorization `d=s^2t`. Seek either a proved cancellation/conservation law across square parts or the smallest uniform obstruction. Do not infer one sign from the prime subcarrier; the finite sign reversals already prohibit that shortcut.

No main source, proof branch, PR, issue, workflow, schedule, permission, or another agent's report was modified.

## H. Final mathematical status

**Independent structural progress:** YES - uniform prime principal debt and complete-orbit centered energy floor.
**Independent fixed-eta signed progress:** NONE.
**Canonical `VFCanonicalSquareVonKochStatement`:** OPEN.
**Finite A/C and complete signed source payment:** OPEN.
**RH:** OPEN.

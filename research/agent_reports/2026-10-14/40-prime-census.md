# RH_Lean Prime Census Laboratory — 2026-10-14

## Provenance

- **Report date (America/New_York):** 2026-10-14
- **Agent / stage:** RH | Prime Census Laboratory / `40-prime-census.md`
- **Scheduled start:** 01:00 ET additional daily invocation (actual invocation observed at 01:51:01 ET)
- **Run ID / sequence:** 2026-10-14T01:51:01-04:00 / first Prime Census run observed today
- **Actual execution / completed time:** IN_PROGRESS; checkpoint 2026-10-14T01:53:55-04:00
- **Previous own checkpoint:** NONE; today's assigned file returned GitHub 404
- **Warm-start cache status:** current authority freshly fetched; no prior own cache reused
- **Observed `main` HEAD SHA:** `52babf6eb87a7c6f80316ceb952667ad65cb2aa3`
- **Central contract fetched:** SUCCESS, `main:AGENTS.md` blob `709ad61bf4555fe4f2c92af3fd42f3994798c8bf`; `main:CURRENT_PROOF_CONTRACT.md` blob `f6e8dc6813ec63974489c26b0c383e34203f0aa9`
- **Report target:** `agent-reports:research/agent_reports/2026-10-14/40-prime-census.md`
- **Previous upstream reports actually read:** `00-coordinator-am.md` PENDING; `10-owner-payment.md` PENDING; `20-analytic-type-ii.md` PENDING; `30-finite-wheel.md` blob `e86a066b5fe4488972f9b49400ebb77d76cab41b`, Claims `20261014-wheel-1..4`
- **Execution environment/tools used:** GitHub connector reads/writes; CPython 3.12.14 and g++ 13.3.0 available for planned independent exact enumeration; no Lean compilation claimed
- **Publication status:** INITIAL_CHECKPOINT
- **Early durable checkpoint:** pending write/readback confirmation

## Current central research objective

The public target remains `VFCanonicalSquareVonKochStatement`: there exists a fixed (C\ge0) such that
[
|\pi(R^2)-\operatorname{vfMidFinishedMass}(R)-\sqrt2|\le C R\log R
quad(R\ge2).
]
For the direct VF route, the current arithmetic inlet is the exact occurrence-, sign-, coefficient-, mask-, clipping-, owner-, and ancestry-preserving placement of the genuine first-bad historical/current source onto the already-cancelled safe/sector-six ledger. The wheel report's late-owner population claims are unsigned supporting restrictions and do not by themselves establish source payment.

## Work performed today

Fresh authority and reporting protocol were retrieved. Today's first three upstream reports were queried explicitly and are PENDING. The available finite-wheel submission was read and its exact requested tests were extracted. The next task is independent reproduction/falsification of Claims `20261014-wheel-1..4`, with strict open-square endpoints, least-prime ownership, exact wheel residues, repeated ancestry, and production-run totals retained.

## Claims and evidence

### Claim 20261014-census-0

- **Exact quantified statement and original carrier:** This checkpoint asserts only that the run began on current main and that the four named upstream paths were queried at `ref=agent-reports`.
- **Status:** NO_NEW_RESULT / IN_PROGRESS
- **Lean declaration or theorem reference, if any:** none
- **Independent mathematical ingredient:** none yet
- **Proof, script, data or source reference:** live GitHub reads listed above
- **Attempted falsification / counterexamples:** not yet executed
- **Precise first unproved lemma or limit:** independently verify or refute the wheel-30 fibre and run-budget claims on the genuine late-owner carrier
- **What changed relative to current known baseline:** no mathematical change; durable start checkpoint only

## Downstream handoff

- **Claims ready for census:** `20261014-wheel-1..4`
- **Claims ready for independent referee:** none from this stage yet
- **Claims ready for Lean:** none
- **Missing inputs or upstream stages:** today's `00`, `10`, and `20` reports PENDING
- **Next action / priority:** inspect current Lean definitions, then execute independent Python and C++ exact scans

## Final report summary

**Net-new mathematical progress:** NONE YET
**Completeness:** PARTIAL
**No RH-proof claim:** yes

## Next-run resume capsule (non-authoritative)

- **Checkpoint/run timestamp:** 2026-10-14T01:53:55-04:00
- **Source freshness:** main `52babf6eb87a7c6f80316ceb952667ad65cb2aa3`; authority blobs recorded above
- **Upstream consumed:** `30-finite-wheel.md` blob `e86a066b5fe4488972f9b49400ebb77d76cab41b`, Claims `20261014-wheel-1..4`; `00/10/20` PENDING
- **Completed evidence worth reusing:** authority and availability check only
- **Invalidations / uncertain results:** all proposed wheel results remain unverified by this stage
- **First unresolved mathematical/CI blocker:** independent reproduction of the adaptive wheel capacity and exact run totals
- **Next highest-value step:** execute differently structured exact enumerations and compare full invariants
- **For Agent #7:** no claim promoted by this checkpoint
- **Avoid next run:** treating this checkpoint as mathematical evidence

---

## Completed run update — 2026-10-14T01:59:49-04:00

### Fresh-source and carrier audit

The early checkpoint was committed as GitHub commit
`44be0ec1a1732480e597938afb409ae0f0c57374` and re-fetched as blob
`57825b3426b0c6a73e78ecd74984106a91a2bd65` before computation.

Open/draft PR discovery returned no open PRs. Relevant current-main source was
read directly:

- `VF_MID_DYADIC_OWNER_EXACT.lean` blob `95e7aa05b62861a19f0179aa529f817e3a402bba`;
- `VF_MID_DYADIC_OWNER_PARITY_TWO.lean` blob `fb025b16bbbd6ca4bcf6288745c283aefa913218`;
- `VF_MID_DYADIC_PREFIX_OWNER.lean` blob `6757501bfc343d51ddb34483f8195da4a2c84047`;
- `VF_MID_DIRECT_ROUGH_CHILD.lean` blob `3da99cd7208ab97abb55d900c3703c65056bdea5`;
- `VF_MID_FIRST_BAD_SOURCE_TO_SECTOR_SIX_INLET.lean` blob `5d03f3080d014aba1e02485ae9c0b08988478c3c`.

For this experiment, with integers `5 <= A <= R < 2A`, the genuine late owner
set is exactly the primes `p` with `A < p <= R`. Its fibre is

```text
F(A,R,p) = { n : R^2 < n < (R+1)^2, n composite, minFac(n)=p }.
```

Writing `q=n/p` and `t=floor(R^2/p)`, current source proves on this carrier
that `q` is prime, `p <= q`, and `q` lies in the four consecutive positions
`t+1,...,t+4`. The chronological late removal is the exact sum of these fibre
cardinalities. No raw VF coefficient, historical tag, mask, clipping term,
anchor, or signed sector-six contribution is present in this unsigned census.

### Claim 20261014-census-1 — wheel-30 fibre theorem independently accepted

- **Exact statement:** For every `5 <= A <= R < 2A` and every prime
  `A < p <= R`,
  `|F(A,R,p)| <= W30(floor(R^2/p))`, where
  `W30(t)=#{j in {1,2,3,4}: gcd(t+j,30)=1}`.
- **Status:** `PAPER_PROOF` for the all-scale implication from the current
  rough-child theorem; `FINITE_COMPUTATION` for the independent scans below.
- **Proof:** stripping `p` is injective. Every resulting child is a prime
  `q>A>=5`, so it is coprime to 30, and source places it in the four displayed
  slots. Thus the child set injects into the wheel survivors.
- **Exact residue table:**
  `W30=0` at residues `1,2,23,24`; `W30=2` at
  `9,10,15,16,27,28`; `W30=1` at the other 20 residues. The Python program
  regenerated all 30 entries and matched this table exactly.
- **Falsification coverage:** the prime-pair implementation checked every
  unique `(R,p)` fibre that can occur for at least one
  `5 <= A <= 5000`, `A <= R < 2A`: 2,958,534 fibres, of which 875,016 were
  nonempty and 587,288 had wheel capacity two. Maximum actual cardinality was
  two; violations were zero. This reduction is complete because the fibre and
  `W30` depend only on `(R,p)`, while an admissible `A` exists exactly when
  `max(5,floor(R/2)+1) <= A < p`.
- **Limit:** finite coverage is not an all-scale proof; the paper proof still
  depends on the cited current-main rough-child/primality declarations.

### Claim 20261014-census-2 — exact run budget and production totals reproduced

- **Exact statement:** for `5 <= A <= B <= 2A`, summing Claim 1 gives
  `vfMidDyadicLateRemoval(A,A,B) <= sum W30(floor(R^2/p))`; hence the compiled
  identity `PrimeSupply=PrefixSupply-LateRemoval` gives
  `PrefixSupply-wheelBudget <= PrimeSupply`.
- **Status:** `PAPER_PROOF` for the summation and inequality direction;
  `FINITE_COMPUTATION` for the values.
- **Independent exact results:**

| run `[A,B)` | actual | owners | parity cap | wheel cap | `(W0,W1,W2)` |
|---:|---:|---:|---:|---:|---:|
| `[50,100)` | 131 | 268 | 536 | 282 | `(39,176,53)` |
| `[100,200)` | 463 | 1,033 | 2,066 | 1,091 | `(142,691,200)` |
| `[500,1000)` | 6,587 | 18,409 | 36,818 | 19,573 | `(2,447,12,351,3,611)` |
| `[1000,2000)` | 22,627 | 69,077 | 138,154 | 73,432 | `(9,282,46,158,13,637)` |
| `[2634,5267)` | 125,272 | 426,984 | 853,968 | 454,679 | `(56,989,285,311,84,684)` |
| `[5000,10000)` | 385,553 | 1,411,740 | 2,823,480 | 1,504,048 | `(188,345,942,742,280,653)` |

The nested replay over every `5 <= A <= 300` reproduced the submitted
45,140 blocks, 760,399 owner fibres, and 304,673 late occurrences, with zero
violations. The two independent implementations agreed exactly on every
aggregate for `[2634,5267)` and `[5000,10000)`.

### Claim 20261014-census-3 — sharpness and ancestry witnesses confirmed

- **Status:** `FINITE_COMPUTATION`; the universal one-child strengthening is
  `REFUTED`.
- Exhaustive lexicographic search over the admissible domain through `A=5000`
  found the first saturation at `(A,R,p,t)=(12,22,17,28)`, children
  `(29,31)`, physical integers `(493,527)`. Since every lexicographically
  earlier admissible `A` is in the search, this also verifies the claimed
  minimality.
- `(A,R,p,t)=(9,16,11,23)` has wheel capacity zero and an empty fibre.
- Repeated owner `p=7`: `77=7*11` in block `R=8` and `91=7*13` in block
  `R=9`.
- Repeated partner `q=13`: `91=7*13` in block `R=9` and `143=11*13` in
  block `R=11`.
- These are distinct physical occurrences. They confirm that neither an owner
  cap nor one historical partner charge may be silently spent only once or
  repeatedly across a run without occurrence tags.

### Claim 20261014-census-4 — physical least-factor and Möbius cross-check

- **Status:** `FINITE_COMPUTATION`.
- A separately structured C++ segmented least-prime-factor enumeration visited
  all 20,800,700 strict interior integers in `[2634,5267)` and all 74,995,000
  strict interior integers in `[5000,10000)`. It did not generate children
  from prime pairs.
- Every retained integer passed exact reconstruction `n=p*q`, least-factor
  ownership, `p<q`, primality of `q`, and both strict square inequalities.
  Independent trial factorization computed the Möbius value. For the 125,272
  and 385,553 retained occurrences respectively, every value was `mu(n)=+1`;
  Möbius sums equalled the occurrence counts and mismatches were zero.
- Internal conservation held exactly:
  `physical count = reconstructed count = sum of owner-fibre counts = mu sum`.
- **Endpoint discrepancy found and corrected:** the first C++ attempt included
  intermediate square atoms in one contiguous allocation and stopped at
  `n=2647^2`, `p=q=2647`. That number is a lower square endpoint, not a member
  of any strict block. The executed corrected source explicitly skips
  `n=R^2`; all subsequent invariants and cross-implementation totals agreed.

### Claim 20261014-census-5 — no adaptive-dispersion theorem obtained

- **Status:** `NO_NEW_RESULT` on `W30-RESIDUE-DISPERSION` and source payment.
- On `[2634,5267)`, two-capacity owners were exactly
  `84684/426984 = 0.19833061660390084874374683828902253948625709628464...`;
  mean capacity was
  `454679/426984 = 1.0648619152005695763775691829202030989451595375939...`.
- On `[5000,10000)`, the corresponding values were
  `280653/1411740 = 0.19879935398869480215903778316120532109311912958477...`
  and mean capacity
  `1504048/1411740 = 1.0653859775879411223029736353719523424993270715571...`.
- These 50-digit decimal renderings used Python `decimal` at precision 50;
  the underlying ratios and every theorem test were exact integers. No
  transcendental VF comparison was needed, so no floating-point decision
  entered any claim.
- No current-day coordinator/owner/analytic report supplied an actual
  threatening or global first-bad run. The two generic dyadic samples above
  are therefore not represented as first-bad data. Their near-20% two-slot
  frequency is diagnostic only and proves no adaptive equidistribution or
  all-scale factor below two.

### Algorithms, environment, commands and performance

Executed on CPython 3.12.14 and g++ 13.3.0. Commands actually run:

```bash
python census_prime_pairs.py
g++ -O3 -std=c++20 census_physical.cpp -o /tmp/census_physical
/tmp/census_physical
```

The Python method used an Eratosthenes prime table, exact integer division,
and direct prime-child intervals. Runtime was 5.273495 seconds for the main
execution. The C++ method used an ascending segmented least-factor table over
the physical integer range and independent trial-factor Möbius evaluation;
reported computation times were 0.451549 and 2.0193 seconds. These are actual
program-internal wall times, not benchmarks under controlled load. The largest
major allocation was the 299,999,996-byte `uint32_t` least-factor array for
`[5000,10000)`; peak RSS was not measured because GNU `time` was unavailable.

Executed source SHA-256:

```text
d91fa263e3e3c07d33348a38d7a5c0ae2f0924d9d6603b208ce9a7930c9c77ed  census_prime_pairs.py
59392331101f7fe43becb3c6a99183c4b11a71dbd1735ba83588df8df8f98527  census_physical.cpp
```

Complete executed source follows.

#### Python prime-pair implementation

```python
#!/usr/bin/env python3
import bisect
import hashlib
import math
import sys
import time


def prime_table(n):
    flag = bytearray(b"\x01") * (n + 1)
    flag[:2] = b"\x00\x00"
    for p in range(2, math.isqrt(n) + 1):
        if flag[p]:
            flag[p * p:n + 1:p] = b"\x00" * (((n - p * p) // p) + 1)
    return flag, [i for i in range(2, n + 1) if flag[i]]


def wheel(t):
    return sum(math.gcd(t + j, 30) == 1 for j in range(1, 5))


def run(A, B, primes, isprime):
    actual = owners = capsum = 0
    hist = [0, 0, 0]
    violations = []
    sqfree_mu_plus = 0
    for R in range(A, B):
        left = bisect.bisect_right(primes, A)
        right = bisect.bisect_right(primes, R)
        for p in primes[left:right]:
            owners += 1
            t = R * R // p
            cap = wheel(t)
            hist[cap] += 1
            capsum += cap
            qlo = t + 1
            qhi = ((R + 1) * (R + 1) - 1) // p
            children = [q for q in range(qlo, qhi + 1) if isprime[q]]
            c = len(children)
            actual += c
            # Here p < q are distinct primes, so every physical n=p*q has mu(n)=+1.
            sqfree_mu_plus += sum(p < q and p * q > R * R and p * q < (R + 1) ** 2 for q in children)
            if c > cap:
                violations.append((A, R, p, t, cap, children))
    return actual, owners, 2 * owners, capsum, tuple(hist), sqfree_mu_plus, violations


def main():
    start = time.perf_counter()
    isprime, primes = prime_table(20050)
    residues = {k: [] for k in range(3)}
    for t in range(30):
        residues[wheel(t)].append(t)
    print("residue_table", residues)
    expected = {0: [1, 2, 23, 24],
                1: [0, 3, 4, 5, 6, 7, 8, 11, 12, 13, 14, 17, 18, 19, 20, 21, 22, 25, 26, 29],
                2: [9, 10, 15, 16, 27, 28]}
    print("residue_table_matches", residues == expected)

    all_violations = []
    possible_fibres = two_slots = nonempty = max_children = 0
    first_saturation = None
    # This covers every admissible (A,R,p) with 5<=A<=5000, A<=R<2A:
    # existence of A is equivalent to floor(R/2)+1 <= A < p.
    for R in range(5, 10000):
        min_A = max(5, R // 2 + 1)
        if min_A > 5000:
            continue
        lo = bisect.bisect_right(primes, min_A)
        hi = bisect.bisect_right(primes, R)
        for p in primes[lo:hi]:
            possible_fibres += 1
            t = R * R // p
            cap = wheel(t)
            qhi = ((R + 1) ** 2 - 1) // p
            children = [q for q in range(t + 1, qhi + 1) if isprime[q]]
            c = len(children)
            nonempty += c > 0
            two_slots += cap == 2
            max_children = max(max_children, c)
            if c > cap:
                all_violations.append((min_A, R, p, t, cap, children))
            if c == 2:
                candidate = (min_A, R, p, t, tuple(children))
                if first_saturation is None or candidate[:3] < first_saturation[:3]:
                    first_saturation = candidate
    print("global_A_le_5000", possible_fibres, nonempty, two_slots, max_children,
          "violations", len(all_violations), "first_saturation", first_saturation)

    for A, B in [(50, 100), (100, 200), (500, 1000), (1000, 2000),
                 (2634, 5267), (5000, 10000)]:
        result = run(A, B, primes, isprime)
        print("run", A, B, result[:-1], "violations", len(result[-1]))

    witnesses = [(12, 22, 17), (9, 16, 11), (5, 8, 7), (5, 9, 7),
                 (6, 9, 7), (6, 11, 11)]
    for A, R, p in witnesses:
        t = R * R // p
        qhi = ((R + 1) ** 2 - 1) // p
        qs = [q for q in range(t + 1, qhi + 1) if isprime[q]]
        print("witness", A, R, p, "t", t, "cap", wheel(t), "q", qs,
              "n", [p * q for q in qs])
    print("sha256", hashlib.sha256(open(__file__, "rb").read()).hexdigest())
    print("elapsed_seconds", f"{time.perf_counter()-start:.6f}")


if __name__ == "__main__":
    main()
```

#### C++ physical-integer implementation

```cpp
#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <unordered_map>
#include <vector>

static int wheel(uint64_t t) {
  int c = 0;
  for (int j = 1; j <= 4; ++j) c += std::gcd<uint64_t>(t + j, 30) == 1;
  return c;
}

static std::vector<int> primes_to(int n, std::vector<uint8_t>& isprime) {
  isprime.assign(n + 1, 1);
  isprime[0] = isprime[1] = 0;
  for (int p = 2; int64_t(p) * p <= n; ++p)
    if (isprime[p]) for (int m = p * p; m <= n; m += p) isprime[m] = 0;
  std::vector<int> ps;
  for (int n0 = 2; n0 <= n; ++n0) if (isprime[n0]) ps.push_back(n0);
  return ps;
}

static uint64_t key(int R, int p) { return (uint64_t(uint32_t(R)) << 32) | uint32_t(p); }

static int mobius_trial(uint64_t n, const std::vector<int>& primes) {
  int mu = 1;
  for (int p : primes) {
    if (uint64_t(p) * p > n) break;
    if (n % p != 0) continue;
    n /= p;
    mu = -mu;
    if (n % p == 0) return 0;
  }
  if (n > 1) mu = -mu;
  return mu;
}

static void scan(int A, int B) {
  auto started = std::chrono::steady_clock::now();
  uint64_t lo = uint64_t(A) * A + 1, hi = uint64_t(B) * B - 1;
  size_t N = size_t(hi - lo + 1);
  std::vector<uint32_t> spf(N, 0);
  std::vector<uint8_t> isprime;
  auto primes = primes_to(2 * B + 10, isprime);
  for (int p : primes) {
    if (uint64_t(p) * p > hi) break;
    uint64_t first = std::max<uint64_t>(uint64_t(p) * p, ((lo + p - 1) / p) * p);
    for (uint64_t m = first; m <= hi; m += p) {
      auto& s = spf[size_t(m - lo)];
      if (s == 0) s = uint32_t(p);
    }
  }
  std::unordered_map<uint64_t, uint8_t> fibres;
  uint64_t actual = 0, reconstructed = 0, mu_plus = 0, mu_mismatch = 0;
  int64_t mu_sum = 0;
  int R = A;
  uint64_t next = uint64_t(R + 1) * (R + 1);
  for (size_t i = 0; i < N; ++i) {
    uint64_t n = lo + i;
    while (n >= next) { ++R; next = uint64_t(R + 1) * (R + 1); }
    if (n == uint64_t(R) * R) continue;
    uint32_t p = spf[i];
    if (p > uint32_t(A)) {
      uint64_t q = n / p;
      bool inv = n == uint64_t(p) * q && p <= uint32_t(R) && p < q && q < isprime.size() && isprime[q]
                 && uint64_t(R) * R < n && n < uint64_t(R + 1) * (R + 1);
      if (!inv) { std::cerr << "invariant failure n=" << n << " p=" << p << " q=" << q << "\n"; std::exit(2); }
      int mu = mobius_trial(n, primes);
      ++actual; ++reconstructed; mu_plus += mu == 1; mu_mismatch += mu != 1; mu_sum += mu;
      ++fibres[key(R, p)];
    }
  }
  uint64_t owners = 0, capsum = 0, violations = 0, fibre_sum = 0;
  uint64_t hist[3] = {0, 0, 0};
  for (int r = A; r < B; ++r) {
    for (int p : primes) {
      if (p <= A) continue;
      if (p > r) break;
      ++owners;
      int cap = wheel(uint64_t(r) * r / p);
      ++hist[cap]; capsum += cap;
      auto it = fibres.find(key(r, p));
      int c = it == fibres.end() ? 0 : it->second;
      fibre_sum += c;
      violations += c > cap;
    }
  }
  double elapsed = std::chrono::duration<double>(std::chrono::steady_clock::now() - started).count();
  std::cout << "physical " << A << ' ' << B << " actual " << actual << " owners " << owners
            << " parity " << 2 * owners << " wheel " << capsum << " hist "
            << hist[0] << ' ' << hist[1] << ' ' << hist[2]
            << " mu_plus " << mu_plus << " mu_sum " << mu_sum << " mu_mismatch " << mu_mismatch
            << " reconstructed " << reconstructed
            << " fibre_sum " << fibre_sum << " violations " << violations
            << " elapsed_seconds " << elapsed << '\n';
}

int main() {
  scan(2634, 5267);
  scan(5000, 10000);
}
```

### Counterexample and proof-strength audit

- Confirmed counterexample: every late fibre has at most one child is false;
  smallest witness above.
- No counterexample to `20261014-wheel-1` or `-2` was found in the stated
  finite ranges.
- The wheel result is an unsigned population cap. It does not carry raw VF
  weights, signs, source tags, masks, clipping, anchors, cross terms, or
  historical multiplicity. It therefore does not prove
  `VFMidDyadicSignedLateCorrectionStatement`,
  `VFMid915FirstBadSourcePaymentStatement`, actual-prime admissibility, the
  canonical endpoint bound, finite A/C, CORR-4, or RH.
- Failed counterexample search proves nothing beyond the explicit coverage.

### Exact remaining obligations and referee handoff

1. **Accept `20261014-wheel-1` as a paper corollary only after checking** the
   imported child-prime theorem, the four-slot inclusion, `A>=5`, and strict
   endpoint convention against current source.
2. **Accept `20261014-wheel-2` only as an unsigned run budget.** Its inequality
   direction is correct, but it does not become signed payment.
3. **Reject a universal one-child cap** using `20261014-census-3`.
4. **Require `W30-RESIDUE-DISPERSION`** for any claimed uniform aggregate
   improvement below two on adaptive residues; the finite ratios above are
   not such a theorem.
5. **Require `SOURCE-SPLICE-1` and history availability** before spending this
   capacity on the original source. Every occurrence, weight, sign, mask,
   clipped exit, anchor, cross term, owner and historical tag must survive an
   exact equality; repeated `p=7` and `q=13` forbid naive reuse.

### Final report summary

**Net-new mathematical progress:** independent paper verification and two-way
finite reproduction of the wheel-30 fibre/run restriction; no production
source-payment advance.

**Completeness:** `DONE` for the available upstream claim audit;
`NO_NEW_RESULT` for the canonical endpoint bound and signed source inlet.

**No RH-proof claim:** yes.

## Next-run resume capsule (non-authoritative)

- **Checkpoint/run timestamp:** 2026-10-14T01:59:49-04:00
- **Source freshness:** main `52babf6eb87a7c6f80316ceb952667ad65cb2aa3`;
  authority and relevant source blobs listed above and unchanged during run
- **Upstream consumed:** today's `30-finite-wheel.md` blob
  `e86a066b5fe4488972f9b49400ebb77d76cab41b`, Claims
  `20261014-wheel-1..4`; today's `00/10/20` PENDING
- **Completed evidence worth reusing:** Claims `20261014-census-1..4`;
  all admissible unique fibres induced by `A<=5000`; nested `A<=300`
  reproduction; independent physical scans of production and `A=5000` runs;
  source hashes and exact commands above
- **Invalidations / uncertain results:** first C++ endpoint attempt invalidated
  and corrected; no genuine threatening/first-bad run supplied; no all-scale
  residue-dispersion result
- **First unresolved mathematical blocker:** exact occurrence-preserving
  `SOURCE-SPLICE-1`; on the unsigned branch, `W30-RESIDUE-DISPERSION`
- **Next highest-value step:** consume the 03:00 referee verdict and any later
  source-tagged threatening run; test wheel capacity only after exact carrier
  matching, with edge-grouped and owner-grouped signed sums conserved
- **For Agent #7:** Claims 1-2 are small potential formal corollaries only
  after referee acceptance; no open PR was found and no Lean compile was run
- **Avoid next run:** repeating the same `A<=5000` scans on unchanged sources,
  treating near-20% two-slot frequency as uniformity, or transferring an
  unsigned cap to signed source payment

---

## Scheduled continuation — 2026-10-14T10:28:24-04:00

### Early checkpoint — 2026-10-14T10:37:00-04:00

- Fresh `main` HEAD: `18fa753f6ea12951845fec65414b47faea0172a1`.
- Fresh authority: `AGENTS.md` blob `26715158e91d4f5f71e9e8aa15baa1a17053e456`; `CURRENT_PROOF_CONTRACT.md` blob `27dceba62b4797bbb394439d13fc4a8dbe29ea0b`.
- Today's inputs: `00-coordinator-am.md` = `TODAY=PENDING`; Owner Payment blob `08b203d38e2c0d495631c1873edb903d83412ea1`, Claims `20261014-owner-1..4`; Analytic Type II blob `7e6667d1e3e95861eb9c4e929b478ac910b3c2dc`, Claims `20261014-analytic-1..3`; Finite Wheel blob `2c2d3a0d42c3af6efb638b2cd2d8aec806aaaf74`, Claims `20261014-wheel-5..7`.
- External inbox blob `6fce4e9d024b6c4ad47798c5d7c162101a2435a0` consumed; relevant new claims are `EXT-20261014-1..5` and `CL-20261014-1..11`.
- Current objective remains `VFCanonicalSquareVonKochStatement`; merged PRs #938/#939 make the named signed-late, owner-admissibility, and original #915 payment inlets target-equivalent or false at first-bad, not smaller paid lemmas.
- Work started: independent exact prime/SPF/Mobius tests of the new wheel thresholds, ancestry multiplicity, collision, and owner-weight sign claims. No new result is asserted at this checkpoint.

**Checkpoint status:** `IN_PROGRESS / NO_NEW_RESULT`.

### Completed continuation — 2026-10-14T10:39:47-04:00

#### Provenance refresh and live state

- The scheduled invocation began at `2026-10-14T10:28:24-04:00` and completed at
  `2026-10-14T10:39:47-04:00`.
- `main` remained `18fa753f6ea12951845fec65414b47faea0172a1`.
  No open or draft pull request was returned by a live GitHub search.
- The early checkpoint was published as commit
  `ccb0350e97f6dadeeea7f531d4bdde3aa2289017` and verified at blob
  `2cbb12710de3f4baaaca48348aae348512dc9409`.
- Today's upstream reports actually consumed are the three blobs recorded in
  the checkpoint; `00-coordinator-am.md` remains `TODAY=PENDING`.
- Previous-day continuity was checked from Coordinator AM blob
  `87a596f6f7bcb9bab6b2d29fc7c162c64ed544cb`, Owner Payment
  `32f1574b8ade7dedc602b07b1b9257341320080a`, Analytic Type II
  `d9f73a0aab42e70ca30a17d16822a8281ca7afef`, Finite Wheel
  `1c96431194038b2691f628bfce5736f7f0dcacd5`, and this stage
  `e14006a1a29a2f6c9ef2306fea6b1f4243bdf58c`.
- Relevant compiled declarations were inspected in
  `VF_MID_LATE_OWNER_WHEEL_THIRTY_BUDGET.lean` blob
  `3701895c3e3af16b6f6b0506ed69f7b5c3d55800`,
  `VF_MID_DYADIC_OWNER_EXACT.lean` blob
  `95e7aa05b62861a19f0179aa529f817e3a402bba`,
  `VF_MID_FINAL_RAW_CLIPPED_TELESCOPE.lean` blob
  `dc1611da7eeca2ed2f2273fa73c9a659b4ba2f42`, and
  `VF_MID_915_SOURCE_PAYMENT_CONTENT_AUDIT.lean` blob
  `f7d046d8d94962e18f794deee7e33ce7508a0e74`.

The exact experimental carrier was the strict open square block
(R^2<n<(R+1)^2), with genuine least-prime owner (p>A), (ple R<2A),
and quotient

[
 t=lfloor R^2/pfloor,qquad
 u=lfloor((R+1)^2-1)/pfloor.
]

The compiled theorem identifies the owner fibre with the primes
(qin(t,u]). For a squarefree semiprime (n=pq), the physical Möbius value
is therefore (+1). Wheel capacities count the integers in this exact
quotient interval coprime to the stated primorial; they contain no VF weight,
sign, mask, clip, anchor, history tag, or quadratic cross term.

### Claim 20261014-census-6 — sharp 2310/30030 wheel audit

- **Exact statement tested:** Claims `20261014-wheel-5..7`: for
  (7le Ale R<2A), every genuine late-owner fibre is bounded by its
  (gcd(cdot,2310)=1) quotient capacity; for (11le Ale R<2A), it is
  bounded by the (gcd(cdot,30030)=1) capacity.
- **Status:** `PAPER_PROOF` accepted for the all-scale divisibility arguments;
  `FINITE_COMPUTATION` for the independent coverage below.
- **Complete finite coverage:** quotient enumeration checked every distinct
  ((R,p)) fibre induced by at least one (7le Ale5000),
  (Ale R<2A): 2,958,529 fibres, 875,012 nonempty. There were zero 2310
  violations. Restricting to induced (Age11), there were zero 30030
  violations.
- **Sharp failures reproduced:** ((A,R,p,q,n,t,u)=(6,8,7,11,77,9,11))
  has 2310 capacity zero; ((10,11,11,13,143,11,13)) has 30030 capacity
  zero. Both products satisfy the strict endpoint inequalities.
- **Exact run totals, agreed by both implementations:**

| run | actual | (C_{2310}) | (C_{30030}) |
|---|---:|---:|---:|
| ([50,100)) | 131 | 133 | 131 |
| ([100,200)) | 463 | 532 | 481 |
| ([500,1000)) | 6,587 | 9,735 | 8,972 |
| ([2634,5267)) | 125,272 | 226,691 | 209,320 |
| ([5000,10000)) | 385,553 | 747,547 | 689,930 |

No adaptive residue-dispersion or signed cancellation theorem follows. The
larger fixed wheel is a valid deterministic unsigned refinement only.

### Claim 20261014-census-7 — ancestry fibre and collision

- **Exact statement:** for (M=1024^2), odd prime (qge2M), and
  (R_p=lfloorsqrt{pq}floor), the owners satisfying
  (R_pge1024p) are exactly the odd primes
  (plelfloor q/Mfloor). Thus the fibre size is
  (pi(lfloor q/Mfloor)-1).
- **Status:** `PAPER_PROOF` accepted after checking the integer-square-root
  equivalence, strict nonsquare endpoint, least-factor condition, and
  historical block ordering; `FINITE_COMPUTATION` for the cases below.
- Deterministic 64-bit primality and exact integer square roots reproduced the
  five supplied (q)'s. Their odd-owner counts were respectively
  (0,1,2,4,9) at
  (q=2097169,3145739,5242883,11534351,30408713).
- The dyadic-run collision was reproduced:
  (q=5242883) is prime and is used by
  (3q) in block (R=3965) and (5q) in block (R=5120); both lie in
  (3000le R<6000). Independent C++ trial division again certified
  (3,5,q) prime and both strict block memberships.
- **Consequence:** same-block uniqueness is compatible with unbounded global
  historical-tag multiplicity. Deduplicating (q), or charging its one
  compressed historical occurrence once per current owner, changes the
  physical carrier.

### Claim 20261014-census-8 — original-weight signs and falsification

- **Status:** `PAPER_PROOF` accepted for Owner Claims
  `20261014-owner-1..2`; `FINITE_COMPUTATION / REFUTED` for the
  unrestricted strengthening.
- With
  (w(t)=(2t+1)/(tlog(t^2+t+1/2))), the fixed-owner hypotheses
  (Rge1024p) imply the submitted strict bounds
  (w(R)+w(lfloorsqrt qfloor)-1<-451/640) and
  (6xy-x^2-y^2<-541/409600), for
  (x=w(R)), (y=1-w(lfloorsqrt qfloor)).
  The elementary proof's logarithmic inequalities and natural-number
  threshold were checked directly.
- The collision pairs had 180-digit recomputations
  [
  (x-y,;6xy-x^2-y^2)=
  (-0.7499978375451564ldots,-0.1420856151730422ldots)
  ]
  for (p=3), and
  [
  (-0.7536138350812305ldots,-0.1601165756375213ldots)
  ]
  for (p=5).
- The mandatory counterexample
  ((R,p,q,r)=(2048,2029,2069,45)) was independently reconstructed with
  prime (p,q), strict block membership, and
  [
  x-y=-0.6039748931220550ldots,qquad
  6xy-x^2-y^2=+0.0209714374292720ldots.
  ]
  Therefore removing the lower child-scale condition makes isolated
  negativity false.
- Decimal logarithms were evaluated independently at precisions 100 and 180;
  the displayed digits and signs agreed. The smallest displayed absolute
  margin exceeds (2cdot10^{-2}), so rounding at these precisions cannot
  plausibly change a sign. This is a stability check, not an interval-arithmetic
  proof; the universal accepted statements rest on the exact rational/log
  inequalities in the paper proof.
- Pairwise favorable slack still cannot be summed: the exact change after
  adding a pair to residual totals contains the uncontrolled terms
  (2M_0(x+y)-4S_0(x-y)), and the collision shows historical multiplicity
  cannot be discarded.

### Claim 20261014-census-9 — independent physical and Möbius conservation

- **Status:** `FINITE_COMPUTATION`.
- A C++ segmented least-prime-factor scan enumerated every physical integer in
  the five runs rather than generating prime quotients. It skipped every
  intermediate square atom explicitly and verified
  (n=pq), least-factor ownership, (p<q), primality of (q), and both
  strict square inequalities.
- Independent trial factorization returned (mu(n)=+1) for every retained
  occurrence. On ([2634,5267)), physical count = Möbius sum = 125,272;
  on ([5000,10000)), both equal 385,553. The smaller three runs likewise
  matched exactly.
- The physical implementation independently reproduced every wheel total in
  Claim 6. No discrepancy remained.

### External and no-narrowing decisions

- `EXT-20261014-1`: accepted with the sharper threshold already stated by
  Finite Wheel, and independently reproduced here.
- `EXT-20261014-2/3`: accepted only at the fixed-owner, isolated-pair scope;
  cross-owner/history aggregation remains invalid.
- `EXT-20261014-5`: no independent infinite computation is possible. Owner
  Payment's paper audit is consistent with the exact compiled two-parameter
  denominator; this run found no arithmetic contradiction and does not promote
  it beyond `PAPER_PROOF`.
- `CL-20261014-1..7`: current-main compiled baseline after merged PRs
  #938/#939. The named quantitative inlets are target-equivalent or the
  original #915 inequality is strictly false on first-bad inputs.
- No computation here proves the canonical endpoint bound, #915 payment,
  signed-late correction, actual-prime admissibility, finite A/C, CORR-4, or
  RH.

### Executed algorithms and environment

Actual environment: CPython 3.12.14, g++ 13.3.0 with
`-O3 -std=c++20`, Linux 6.18.44 x86_64. Exact commands:

```bash
python -u census_continuation.py
g++ -O3 -std=c++20 census_physical_continuation.cpp \
  -o /tmp/census_physical_continuation
/tmp/census_physical_continuation
```

The Python method used an Eratosthenes table for bounded wheel scans,
deterministic 64-bit Miller-Rabin for larger supplied primes, exact integer
square roots, and `decimal` logarithms. Its measured elapsed time was
140.840169 seconds. The C++ physical scan used a segmented least-factor array
and independent trial-factor Möbius evaluation; the largest scan reported
23.1534 seconds in the final run. These are observed wall times, not controlled
benchmarks. Source hashes:

```text
984fc0225536ad5dc7dffbf7cfc5f117cab90016921d4261f932f35b157a1211  census_continuation.py
c525abebf9e2ffa9066326e3eec47a78dd9684551e3182902505f384cb728560  census_physical_continuation.cpp
```

Complete executed source follows.

#### Python continuation implementation

```python
#!/usr/bin/env python3
from bisect import bisect_right
from decimal import Decimal, getcontext
from hashlib import sha256
from math import gcd, isqrt
from time import perf_counter

getcontext().prec = 100

def sieve(n):
    a = bytearray(b'\x01') * (n + 1)
    a[:2] = b'\x00\x00'
    for p in range(2, isqrt(n) + 1):
        if a[p]:
            a[p*p:n+1:p] = b'\x00' * ((n-p*p)//p + 1)
    return a, [i for i in range(2, n + 1) if a[i]]

def is_prime64(n):
    if n < 2: return False
    small = (2,3,5,7,11,13,17,19,23,29,31,37)
    for p in small:
        if n % p == 0: return n == p
    d, s = n-1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2, 325, 9375, 28178, 450775, 9780504, 1795265022):
        if a % n == 0: continue
        x = pow(a, d, n)
        if x in (1, n-1): continue
        for _ in range(s-1):
            x = x*x % n
            if x == n-1: break
        else: return False
    return True

def capacity(R,p,M):
    t=R*R//p; u=((R+1)*(R+1)-1)//p
    return sum(gcd(q,M)==1 for q in range(t+1,u+1))

def run(A,B,primes,isprime):
    out=[0,0,0]
    for R in range(A,B):
        for p in primes[bisect_right(primes,A):bisect_right(primes,R)]:
            t=R*R//p; u=((R+1)*(R+1)-1)//p
            out[0]+=sum(isprime[q] for q in range(t+1,u+1))
            out[1]+=capacity(R,p,2310)
            out[2]+=capacity(R,p,30030)
    return tuple(out)

def weight(t):
    T=Decimal(t)
    return (2*T+1)/(T*(T*T+T+Decimal('0.5')).ln())

start=perf_counter()
isprime,primes=sieve(20050)
runs=[(50,100),(100,200),(500,1000),(2634,5267),(5000,10000)]
for A,B in runs: print('run',A,B,*run(A,B,primes,isprime))

# Exhaust all distinct fibres induced by at least one 7 <= A <= 5000.
tested=nonempty=viol2310=viol30030=0
first2310=None; first30030=None
for R in range(7,10000):
    minA=max(7,R//2+1)
    if minA>5000: continue
    for p in primes[bisect_right(primes,minA):bisect_right(primes,R)]:
        tested+=1; t=R*R//p; u=((R+1)*(R+1)-1)//p
        qs=[q for q in range(t+1,u+1) if isprime[q]]
        nonempty += bool(qs)
        c2310=capacity(R,p,2310)
        if len(qs)>c2310:
            viol2310+=1
            if first2310 is None:first2310=(minA,R,p,t,u,qs,c2310)
        if minA>=11:
            c30030=capacity(R,p,30030)
            if len(qs)>c30030:
                viol30030+=1
                if first30030 is None:first30030=(minA,R,p,t,u,qs,c30030)
print('global',tested,nonempty,'viol2310',viol2310,first2310,'viol30030',viol30030,first30030)
for A,R,p in [(6,8,7),(10,11,11)]:
    t=R*R//p; u=((R+1)*(R+1)-1)//p
    qs=[q for q in range(t+1,u+1) if isprime[q]]
    print('threshold',A,R,p,t,u,qs,[p*q for q in qs],capacity(R,p,2310),capacity(R,p,30030))

# Exact ancestry formula and collision.
M=1024**2
for q in (2097169,3145739,5242883,11534351,30408713):
    ps=[p for p in range(3,q//M+1,2) if is_prime64(p)]
    rows=[]
    for p in ps:
        R=isqrt(p*q)
        rows.append((p,R,R>=1024*p,R*R<p*q<(R+1)**2))
    print('ancestry',q,is_prime64(q),q//M,len(ps),rows)
q=5242883
for p in (3,5):
    R=isqrt(p*q); r=isqrt(q); x=weight(R); y=1-weight(r)
    print('collision',p,q,R,r,p*q-R*R,(R+1)**2-p*q,'sep',x-y,'slack',6*x*y-x*x-y*y)

# Owner claims and positive strengthening counterexample at 100 digits.
for R,p,q in [(2048,2029,2069),(3072,3,None),(5120,5,None)]:
    if q is None:
        t=R*R//p; u=((R+1)*(R+1)-1)//p
        q=next(v for v in range(t+1,u+1) if is_prime64(v))
    r=isqrt(q); x=weight(R); y=1-weight(r)
    print('ownerpair',R,p,q,is_prime64(p),is_prime64(q),r,'strict',R*R<p*q<(R+1)**2,'sep',x-y,'slack',6*x*y-x*x-y*y)

data=open(__file__,'rb').read()
print('sha256',sha256(data).hexdigest())
print('elapsed_seconds',format(perf_counter()-start,'.6f'))
```

#### C++ continuation implementation

```cpp
#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>

static std::vector<int> primes_to(int n) {
  std::vector<uint8_t> a(n+1,1); a[0]=a[1]=0;
  for(int p=2; int64_t(p)*p<=n; ++p) if(a[p]) for(int m=p*p;m<=n;m+=p)a[m]=0;
  std::vector<int> ps; for(int n0=2;n0<=n;++n0)if(a[n0])ps.push_back(n0); return ps;
}
static int cap(uint64_t R,int p,int M){
  uint64_t t=R*R/p,u=((R+1)*(R+1)-1)/p; int c=0;
  for(uint64_t q=t+1;q<=u;++q)c+=std::gcd<uint64_t>(q,M)==1; return c;
}
static int mu_trial(uint64_t n,const std::vector<int>& ps){
  int mu=1; for(int p:ps){if(uint64_t(p)*p>n)break;if(n%p)continue;n/=p;mu=-mu;if(n%p==0)return 0;}if(n>1)mu=-mu;return mu;
}
static bool prime_trial(uint64_t n){if(n<2)return false;if(n%2==0)return n==2;for(uint64_t d=3;d*d<=n;d+=2)if(n%d==0)return false;return true;}
static void scan(int A,int B){
  auto st=std::chrono::steady_clock::now(); uint64_t lo=uint64_t(A)*A+1,hi=uint64_t(B)*B-1; size_t N=hi-lo+1;
  std::vector<uint32_t> spf(N,0); auto ps=primes_to(2*B+10);
  for(int p:ps){if(uint64_t(p)*p>hi)break;uint64_t f=std::max<uint64_t>(uint64_t(p)*p,((lo+p-1)/p)*p);for(uint64_t n=f;n<=hi;n+=p){auto&s=spf[n-lo];if(!s)s=p;}}
  uint64_t actual=0,c2310=0,c30030=0,muplus=0,musum=0,viol=0; int R=A; uint64_t next=uint64_t(R+1)*(R+1);
  for(size_t i=0;i<N;++i){uint64_t n=lo+i;while(n>=next){++R;next=uint64_t(R+1)*(R+1);}if(n==uint64_t(R)*R)continue;uint32_t p=spf[i];
    if(p>uint32_t(A)){uint64_t q=n/p;bool qp=q>=2;for(int d=2;uint64_t(d)*d<=q&&qp;++d)if(q%d==0)qp=false;bool ok=n==uint64_t(p)*q&&p<=uint32_t(R)&&p<q&&qp&&uint64_t(R)*R<n&&n<uint64_t(R+1)*(R+1);if(!ok){std::cerr<<"bad "<<n<<' '<<p<<' '<<q<<' '<<R<<'\n';std::exit(2);}int mu=mu_trial(n,ps);++actual;muplus+=mu==1;musum+=mu;}
  }
  for(int r=A;r<B;++r)for(int p:ps){if(p<=A)continue;if(p>r)break;c2310+=cap(r,p,2310);c30030+=cap(r,p,30030);}
  double sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-st).count();
  std::cout<<"physical "<<A<<' '<<B<<" actual "<<actual<<" c2310 "<<c2310<<" c30030 "<<c30030<<" muplus "<<muplus<<" musum "<<musum<<" violations "<<viol<<" seconds "<<sec<<'\n';
}
int main(){for(auto ab:std::vector<std::pair<int,int>>{{50,100},{100,200},{500,1000},{2634,5267},{5000,10000}})scan(ab.first,ab.second);uint64_t q=5242883;std::cout<<"collision_q_prime "<<prime_trial(q)<<'\n';for(uint64_t p:{3ULL,5ULL}){uint64_t R=std::sqrt((long double)(p*q));while((R+1)*(R+1)<=p*q)++R;while(R*R>p*q)--R;std::cout<<"collision "<<p<<' '<<q<<' '<<R<<" prime "<<prime_trial(p)<<' '<<prime_trial(q)<<" strict "<<(R*R<p*q&&p*q<(R+1)*(R+1))<<'\n';}}
```

### Remaining mathematical obligations

1. Any use of Claims 6--9 on the VF source must first give a literal
   occurrence-, coefficient-, sign-, mask-, clip-, anchor-, multiplicity-,
   chronology-, and cross-term-preserving identity. This structural equality
   is not itself a payment estimate.
2. Cross-owner historical availability must respect the exact ancestry fibre.
   The \(q=5242883\) collision forbids one historical occurrence from being
   copied for both current owners.
3. The residual large-owner carrier \(p>R/1024\) has no uniform isolated
   negative sign; the \((2048,2029,2069,45)\) witness must be retained.
4. A genuine quantitative advance still requires an independently proved
   signed estimate on the original carrier. Unsigned fixed-wheel savings,
   isolated pair slack, and target-equivalent inlet names do not provide it.
5. The Adversarial Referee should audit the exact ancestry-fibre proof,
   both threshold counterexamples, the historical collision, and the
   distinction between an unconditional reassembly equality and an RH-hard
   payment bound.

## Updated final report summary

**Net-new mathematical progress:** no new all-scale theorem beyond the
upstream paper claims. This continuation independently accepted the sharp
2310/30030 wheel restrictions and exact ancestry-fibre formula, reproduced all
finite totals by two structurally different algorithms, and confirmed the
cross-owner multiplicity and positive-slack counterexamples.

**Finite scope:** complete induced fibres for \(7\le A\le5000\); physical
integer scans on the five tabulated runs through \(B=10000\); five supplied
large ancestry primes; four high-precision signed pairs.

**Completeness:** `DONE` for today's available upstream arithmetic claims;
`DONE_NO_NEW_RESULT` for the canonical endpoint target.

**No RH-proof claim:** yes.

## Updated next-run resume capsule (non-authoritative)

- **Checkpoint/run timestamp:** `2026-10-14T10:39:47-04:00`.
- **Source freshness:** main
  `18fa753f6ea12951845fec65414b47faea0172a1`; authority and Lean blobs
  recorded above.
- **Upstream consumed:** today's `00=TODAY=PENDING`; today Owner
  `08b203d3...`, Analytic `7e6667d1...`, Wheel `2c2d3a0...`; yesterday's
  `00/10/20/30/40` blobs recorded above.
- **Completed evidence worth reusing:** Claims
  `20261014-census-6..9`; zero wheel violations on 2,958,529 induced
  fibres; exact five-run two-implementation agreement; ancestry collision at
  \(q=5242883\); positive-slack counterexample
  \((2048,2029,2069,45)\); executed source hashes and commands above.
- **Invalidations / uncertain results:** unrestricted isolated negativity is
  `REFUTED`; no interval-arithmetic transcendental certificate was used;
  `EXT-20261014-5` remains `PAPER_PROOF`.
- **First unresolved mathematical blocker:** a new, independently provable
  signed original-carrier estimate; the canonical theorem itself remains the
  first unproved completion statement.
- **Next highest-value step:** test only a newly specified source-tagged
  signed identity or estimate, explicitly grouping by historical \(q\) with
  its full multiplicity and retaining residual cross terms.
- **For Agent #7:** no new proof PR exists. Claims `wheel-5..6` and
  `analytic-1..2` are scoped auxiliary formalization candidates only after
  referee acceptance; they are not closure lemmas.
- **Avoid next run:** repeating the unchanged wheel scans, deduplicating a
  historical prime, summing isolated pair slacks, or relabeling a
  target-equivalent inlet as a smaller theorem.


---

## Scheduled continuation checkpoint — 2026-10-14T16:18:13-04:00

- **Status:** `IN_PROGRESS / NO_NEW_RESULT`; this is the required early durable checkpoint.
- **Observed current `main` HEAD:** `13c3aeab8f84fc2309175261948a17a50c8342f4`, verified from the live `branches/main` endpoint at 2026-10-14T16:18:13-04:00.
- **Fresh authority:** `AGENTS.md` blob `26715158e91d4f5f71e9e8aa15baa1a17053e456`; `CURRENT_PROOF_CONTRACT.md` blob `27dceba62b4797bbb394439d13fc4a8dbe29ea0b`.
- **Current objective:** the unique open public target remains `VFCanonicalSquareVonKochStatement`. This continuation tests new exact repeated-tag incidence and signed-packet claims without cloning a historical prime or promoting a local linear packet to the original global quadratic norm.
- **Today's upstream reports:** `00-coordinator-am.md = TODAY=PENDING`; Owner Payment blob `a2ed7dc27756393c49beb5bebae80971a2af6aff`; Analytic Type II blob `b8ee78df90d9fccb4b1201c933720a70300d9d51`; Finite Wheel blob `476d1af0f2624f615e7cdcb017812633dbd232f0`. The prior two-day continuity and external inbox blob `6fce4e9d024b6c4ad47798c5d7c162101a2435a0` were read.
- **Claims selected for independent audit:** `20261014-owner-5..6`, `20261014-analytic-4..5`, and `20261014-wheel-8..10`, with emphasis on exact floor endpoints, root spacing, multiplicity, original weights, and the claimed six-block signed margin.
- **Live PR discovery:** no open or draft pull requests were returned. PRs #941 and #942 are merged into the observed `main`.
- **Next computation:** implement an independent exact prime/integer-root enumerator and a separately structured C++ cross-check; search for smaller root gaps, reproduce the sharp 1025 counterexample and the (q=1000000007) half-run overload, then evaluate signed packets at increased decimal precision.


## Scheduled continuation completed — 2026-10-14T16:22:08-04:00

### Provenance and changed baseline

- **Execution interval:** 2026-10-14T16:16:31-04:00 through 2026-10-14T16:22:08-04:00.
- **Observed current `main` HEAD:** `13c3aeab8f84fc2309175261948a17a50c8342f4`, read from the live `branches/main` endpoint. It is the verified merge commit for PR #942. No open or draft PR was returned.
- **Authority blobs:** `AGENTS.md` `26715158e91d4f5f71e9e8aa15baa1a17053e456`; `CURRENT_PROOF_CONTRACT.md` `27dceba62b4797bbb394439d13fc4a8dbe29ea0b`.
- **Current-day inputs:** Coordinator AM `TODAY=PENDING`; Owner Payment `a2ed7dc27756393c49beb5bebae80971a2af6aff`, Claims `20261014-owner-5..6`; Analytic Type II `b8ee78df90d9fccb4b1201c933720a70300d9d51`, Claims `20261014-analytic-4..5`; Finite Wheel `476d1af0f2624f615e7cdcb017812633dbd232f0`, Claims `20261014-wheel-8..10`.
- **Previous-day continuity actually read:** Coordinator AM `87a596f6f7bcb9bab6b2d29fc7c162c64ed544cb`; Owner `32f1574b8ade7dedc602b07b1b9257341320080a`; Analytic `d9f73a0aab42e70ca30a17d16822a8281ca7afef`; Wheel `1c96431194038b2691f628bfce5736f7f0dcacd5`; Census `e14006a1a29a2f6c9ef2306fea6b1f4243bdf58c`. These are continuity only.
- **External inbox:** `6fce4e9d024b6c4ad47798c5d7c162101a2435a0`. `EXT-20261014-1..5` were consumed earlier today; no new external claim superseded the present inputs.
- **Relevant compiled source inspected:** historical multiplicity `fda6db056571191feffd08f2d1d6fe0fa02f0d8c`; signed pair bounds `e3cc17224469e24516390a8f20e590d5932dbfc1`; weighted physical Fubini `58b78186e4fd5b68179afe4be0b7b6e4761442d6`; active raw-parent splice `e61eb36301f650bfb41079bbd7367f9f45cf6d3e`; sharp primorial budget `4925053b09acaa927f48c7fad8f13c0f4bf5ff71`.
- **Early checkpoint:** commit `f93338ed768e8f3b822a39daeec6a425cfe8d45e`, verified blob `55e12bcd3d2247f124ef3f19f00c4d1866683698`.
- **Environment:** CPython 3.12.14; g++ 13.3.0, `-O3 -std=c++20`; Linux 6.18.44 x86_64. No local Lean compilation was performed.

The unique open public goal remains `VFCanonicalSquareVonKochStatement`. The claims below are exact incidence/linear-charge restrictions only. They do not supply masks, clipping, anchor restoration, the quadratic NNS cross terms, or endpoint control.

### Claim 20261014-census-10 — independent reproduction of the new upstream arithmetic

**Status: `FINITE_COMPUTATION`; upstream universal statements retain their reported `PAPER_PROOF` or `PROVED_IN_LEAN` status.**

Two independently structured programs agreed on all exact integer data.

1. `20261014-wheel-8/-10`: all 438,030 primes (q) with (3cdot2^{20}<qle10^7) and every eligible odd-prime owner were enumerated. No adjacent root gap below 1024 occurred. The minimum was 1110 at
   [
   (q,p_1,p_2,R_1,R_2)=(7340033,5,7,6058,7168).
   ]
   Window maxima for lengths (1024,2048,ldots,6144) were respectively (1,2,3,3,3,3).
2. The claimed sharp witness was independently certified:
   [
   (p_1,p_2,q)=(10139,10141,10633609379),quad
   (R_1,R_2)=(10383360,10384384).
   ]
   The gap is exactly 1024. Lower square gaps are 604081 and 1652983; upper gaps are 20162640 and 19115786; threshold slacks (R_i-1024p_i) are 1024 and 0. Python deterministic 64-bit Miller--Rabin and C++ complete trial division both certified all three primes.
3. `20261014-owner-5/-6`: for (q=1000000007), (A=488109), the programs found exactly 111 prime owners in ([239,953]), sum 64891, 111 distinct roots from 488876 to 976217, and minimum adjacent gap 1064. The owner-list SHA-256 is exactly the upstream value
   `e5bae15ed976f7db0020fa9f46b24b1f5d1cfec0cf1035d3237acc6dfd48d50f`.
4. `20261014-analytic-4/-5`: for the prime (q=1000000000039),
   [
   A=244140625,quad L_q=59604,quad U_q=238418.
   ]
   Both programs found 15,072 owners, endpoints 59611 and 238417, roots 244153640 through 488279633, and minimum lower/upper square gaps 32849 and 3849. The owner hash reproduced exactly:
   `c91405733e2058eb5af1d02eb7357e30fcbe0eb4544cb6ac977fc65c2c69845d`.

No contradiction was found in the exact fibre formula, weight asymptotic's finite example, or sharp 1024 spacing. Finite agreement does not prove the PNT asymptotics.

### Claim 20261014-census-11 — four-owner sharp window cap

**Status: `PAPER_PROOF` plus `FINITE_COMPUTATION`; strengthens the valid but nonsharp six-site bound in `20261014-wheel-9`.**

Let (q) be prime and let (S) be a nonempty set of distinct odd-prime owners (p), with
[
R_p=lfloorsqrt{pq}floor,qquad 1024ple R_p,qquad
Ale R_p<B,qquad B-Ale6144.
]
Then
[
oxed{|S|le4.}
]

Order five hypothetical owners (p_1<cdots<p_5). The compiled threshold equivalence gives (qge2^{20}p_5). If (p_1=3), then (p_5ge13), and
[
sqrt{p_5q}-sqrt{p_1q}
ge1024,rac{p_5-p_1}{1+sqrt{p_1/p_5}}
ge1024,rac{10}{1+sqrt{3/13}}>6144.
]
(The last inequality follows after isolating and squaring: (4>6sqrt{3/13}).)
If (p_1>3), five odd primes cannot occupy an interval of diameter 10: the six odd candidates contain two distinct multiples of 3, both composite. Hence (p_5-p_1ge12), while (1+sqrt{p_1/p_5}<2), giving the same strict (>6144) bound.

For real (x-y>6144), (lfloor xfloor-lfloor yfloor>6143), hence the integer root difference is at least 6144. But two roots in ([A,B)) with (B-Ale6144) differ by at most 6143, contradiction.

The cap is optimal. Both implementations certified the genuine four-owner witness
[
q=11534351,quad (p_i)=(3,5,7,11),quad
(R_i)=(5882,7594,8985,11264),
]
whose root span is 5382. All products have strict positive square gaps, and the threshold slacks are (2810,2474,1817,0). C++ complete trial division certified (q) prime.

This improvement comes from exact odd-prime constellation geometry, not a probabilistic wheel average. It answers the requested prime-restriction test all-scale and falsifies any universal cap of three.

### Claim 20261014-census-12 — strengthened one-history signed packet

**Status: `PAPER_PROOF`; high-precision values are diagnostic only.**

Under Claim 11, count the one historical prime occurrence (q) exactly once. The compiled literal bounds give current weights (w(R_p)<9/64) and historical magnitude (1-w(lfloorsqrt qfloor)>541/640). Therefore
[
oxed{sum_{pin S}operatorname{charge}(R_p,pq)
+operatorname{charge}(lfloorsqrt qfloor,q)
<-rac{181}{640}.}
]
Indeed (4(9/64)-541/640=-181/640). This strictly strengthens the upstream (-1/640) margin.

For the sharp four-owner witness, 180-decimal evaluation gave current sum
(0.4441934219799508828305322527815ldots), historical magnitude
(0.8769882373588209633522582840591ldots), and signed total
(-0.4327948153788700805217260312776ldots).
The 120- and 180-digit runs agreed through all displayed digits. The sign and theorem do not depend on floating arithmetic; they follow from the exact rational bounds.

For the 111-descendant control, the exact sliding maxima at lengths
(1024,2048,3072,4096,5120,6144) were (1,2,2,3,4,4). There were 71 occupied (A)-aligned 6144-windows, each holding at most four sites. Spending the one historical tag on a best four-site packet leaves 107 current descendants, so repeated packet payment would clone (q). At 180 digits:
[
X=8.2169191125328057557ldots,quad
y=0.9034885076691904531ldots,quad
-X^2+6Xy-y^2=-23.7906992656729320483ldots.
]
The maximum-weight four-site packet found had current mass
(0.2915597847805521420ldots) and linear signed margin
(-0.6119287228886383111ldots).

Thus the local packet is genuinely favorable and multiplicity-safe, but 107 residual current occurrences remain in this witness. No global NNS conclusion follows.

### Algorithms, commands, and error control

Executed commands:

```bash
python -u census_20261014.py
PREC=180 python -u census_20261014.py
g++ -O3 -std=c++20 census_20261014.cpp -o /tmp/census_20261014
/tmp/census_20261014
```

The Python implementation used an Eratosthenes byte sieve, exact `isqrt`, deterministic 64-bit Miller--Rabin, exact integer endpoints and `decimal` logarithms at 120 and 180 digits. Its final measured time was 5.365179 seconds. The C++ implementation used a structurally different linear sieve, independently corrected integer square root, and complete odd trial division for supplied large witnesses; its measured time was 0.0814869 seconds. Times are observed wall times, not benchmarks.

Source hashes:

```text
334bc3a8bf1bbf4efe604b74da22472f18211d4e47d928e403856e6b4bf2c5a9  census_20261014.py
28ea63586d7a34d58c9f272dfdac213e464d5de9f3f1c0b8b62629226811e133  census_20261014.cpp
```

#### Executed Python source

```python
#!/usr/bin/env python3
from bisect import bisect_right
from decimal import Decimal, getcontext
from hashlib import sha256
from math import isqrt
from os import environ
from time import perf_counter

M = 1 << 20
getcontext().prec = int(environ.get("PREC", "120"))


def sieve(n):
    a = bytearray(b"\x01") * (n + 1)
    a[:2] = b"\x00\x00"
    for p in range(2, isqrt(n) + 1):
        if a[p]:
            a[p * p:n + 1:p] = b"\x00" * ((n - p * p) // p + 1)
    return a, [i for i in range(2, n + 1) if a[i]]


def is_prime64(n):
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 325, 9375, 28178, 450775, 9780504, 1795265022):
        if a % n == 0:
            continue
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def next_prime(n):
    n = max(2, n)
    if n == 2:
        return 2
    n += (n % 2 == 0)
    while not is_prime64(n):
        n += 2
    return n


def root_row(p, q):
    n = p * q
    r = isqrt(n)
    return p, r, n - r * r, (r + 1) * (r + 1) - n, r - 1024 * p


def weight(t):
    t = Decimal(t)
    return (2 * t + 1) / (t * (t * t + t + Decimal("0.5")).ln())


def max_window(rows, length):
    best = (0, None, None)
    j = 0
    for i in range(len(rows)):
        while rows[i][1] - rows[j][1] >= length:
            j += 1
        cand = (i - j + 1, j, i)
        if cand[0] > best[0]:
            best = cand
    return best


start = perf_counter()
isprime, primes = sieve(10_000_000)

# Exhaust the same bounded q range and retain window-degree diagnostics.
q_count = 0
min_gap = None
min_gap_row = None
max_degrees = {L: 0 for L in range(1024, 6145, 1024)}
violations = 0
for q in primes[bisect_right(primes, 3 * M):]:
    if q > 10_000_000:
        break
    q_count += 1
    ps = primes[1:bisect_right(primes, q // M)]
    rows = [root_row(p, q) for p in ps]
    for a, b in zip(rows, rows[1:]):
        gap = b[1] - a[1]
        if min_gap is None or gap < min_gap:
            min_gap = gap
            min_gap_row = (q, a[0], b[0], a[1], b[1])
        violations += gap < 1024
    for L in max_degrees:
        max_degrees[L] = max(max_degrees[L], max_window(rows, L)[0])

# Exact 1024 sharpness witness.
sharp_q = 10_633_609_379
sharp = [root_row(p, sharp_q) for p in (10_139, 10_141)]

# Find a genuine four-owner witness in a 6144-root window.
four = None
small_primes = [p for p in primes if 3 <= p <= 1000]
for i in range(len(small_primes) - 3):
    quartet = small_primes[i:i + 4]
    q = next_prime(M * quartet[-1])
    rows = [root_row(p, q) for p in quartet]
    if rows[-1][1] - rows[0][1] < 6144:
        four = (q, rows)
        break
four_weight = sum(weight(r[1]) for r in four[1])
four_y = Decimal(1) - weight(isqrt(four[0]))

# Long half-run overload and exact weights.
q = 1_000_000_007
A, B = 488_109, 976_218
owners = [p for p in primes if 239 <= p <= 953]
rows = [root_row(p, q) for p in owners]
X = sum(weight(r[1]) for r in rows)
y = Decimal(1) - weight(isqrt(q))
G = -X * X + 6 * X * y - y * y
windows = {}
for L in range(1024, 6145, 1024):
    c, j, i = max_window(rows, L)
    windows[L] = (c, rows[j][0] if j is not None else None,
                  rows[i][0] if i is not None else None,
                  rows[j][1] if j is not None else None,
                  rows[i][1] if i is not None else None)
aligned = {}
for row in rows:
    k = (row[1] - A) // 6144
    aligned[k] = aligned.get(k, 0) + 1
packet_count, j, i = max_window(rows, 6144)
packet_weight = sum(weight(rows[k][1]) for k in range(j, i + 1))

owner_text = ",".join(map(str, owners)).encode()

# Independent reproduction of the analytic dyadic-fibre example.
analytic_q = 1_000_000_000_039
analytic_A = analytic_q // 4096
analytic_L = analytic_A * analytic_A // analytic_q
analytic_U = ((2 * analytic_A) ** 2 - 1) // analytic_q
analytic_owners = primes[bisect_right(primes, analytic_L):bisect_right(primes, analytic_U)]
analytic_rows = [root_row(p, analytic_q) for p in analytic_owners]
analytic_X = sum(weight(r[1]) for r in analytic_rows)
analytic_y = Decimal(1) - weight(isqrt(analytic_q))
analytic_text = ",".join(map(str, analytic_owners)).encode()
print("bounded_q", q_count, "violations", violations,
      "min_gap", min_gap, "min_gap_row", min_gap_row)
print("bounded_window_max", max_degrees)
print("sharp_prime", is_prime64(sharp_q), "owners_prime",
      is_prime64(10_139), is_prime64(10_141), "rows", sharp,
      "gap", sharp[1][1] - sharp[0][1])
print("four_witness", four, "span", four[1][-1][1] - four[1][0][1])
print("four_signed", four_weight, four_y, four_weight - four_y,
      "rational_bound", Decimal(-181) / Decimal(640))
print("overload", len(owners), sum(owners), len({r[1] for r in rows}),
      rows[0][1], rows[-1][1],
      min(rows[i + 1][1] - rows[i][1] for i in range(len(rows) - 1)))
print("windows", windows)
print("aligned_6144", len(aligned), max(aligned.values()),
      sorted(aligned.items())[:3], sorted(aligned.items())[-3:])
print("residual_after_one_best_packet", len(rows) - packet_count)
print("weights_X", X)
print("weights_y", y)
print("weights_G", G)
print("best_packet_count_weight_margin", packet_count, packet_weight,
      packet_weight - y)
print("owner_sha256", sha256(owner_text).hexdigest())
print("analytic", is_prime64(analytic_q), analytic_A, analytic_L, analytic_U,
      len(analytic_owners), analytic_owners[0], analytic_owners[-1],
      analytic_rows[0][1], analytic_rows[-1][1],
      min(r[2] for r in analytic_rows), min(r[3] for r in analytic_rows))
print("analytic_weights", analytic_X, analytic_y)
print("analytic_owner_sha256", sha256(analytic_text).hexdigest())
print("script_sha256", sha256(open(__file__, "rb").read()).hexdigest())
print("elapsed_seconds", format(perf_counter() - start, ".6f"))
```

#### Executed C++ source

```cpp
#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>

using u64 = uint64_t;
static constexpr u64 M = 1ULL << 20;

static bool prime_trial(u64 n) {
  if (n < 2) return false;
  if (n % 2 == 0) return n == 2;
  for (u64 d = 3; d <= n / d; d += 2) if (n % d == 0) return false;
  return true;
}

static u64 iroot(u64 n) {
  u64 r = static_cast<u64>(std::sqrt(static_cast<long double>(n)));
  while ((r + 1) <= n / (r + 1)) ++r;
  while (r > n / r) --r;
  return r;
}

struct Row { u64 p, r, low, high, threshold; };
static Row row(u64 p, u64 q) {
  u64 n = p * q, r = iroot(n);
  return {p, r, n - r * r, (r + 1) * (r + 1) - n, r - 1024 * p};
}

static std::vector<int> linear_primes(int n) {
  std::vector<int> lp(n + 1), ps;
  for (int x = 2; x <= n; ++x) {
    if (!lp[x]) { lp[x] = x; ps.push_back(x); }
    for (int p : ps) {
      if (p > lp[x] || 1LL * p * x > n) break;
      lp[p * x] = p;
    }
  }
  return ps;
}

int main() {
  auto start = std::chrono::steady_clock::now();
  auto ps = linear_primes(10000000);
  u64 qcount = 0, violations = 0, mingap = ~u64(0);
  std::vector<u64> maxdeg(7);
  u64 bestq=0,bp1=0,bp2=0,br1=0,br2=0;
  for (int qi : ps) {
    u64 q = qi;
    if (q <= 3 * M) continue;
    ++qcount;
    std::vector<Row> rows;
    for (int p : ps) {
      if (p < 3) continue;
      if (u64(p) * M > q) break;
      rows.push_back(row(p,q));
    }
    for (size_t i=1;i<rows.size();++i) {
      u64 g=rows[i].r-rows[i-1].r;
      if(g<mingap){mingap=g;bestq=q;bp1=rows[i-1].p;bp2=rows[i].p;br1=rows[i-1].r;br2=rows[i].r;}
      violations += g < 1024;
    }
    for(int k=1;k<=6;++k){u64 L=1024*k;size_t j=0;for(size_t i=0;i<rows.size();++i){while(rows[i].r-rows[j].r>=L)++j;maxdeg[k]=std::max<u64>(maxdeg[k],i-j+1);}}
  }
  std::cout<<"bounded_q "<<qcount<<" violations "<<violations<<" min_gap "<<mingap
           <<" row "<<bestq<<' '<<bp1<<' '<<bp2<<' '<<br1<<' '<<br2<<" max";
  for(int k=1;k<=6;++k)std::cout<<' '<<1024*k<<':'<<maxdeg[k];std::cout<<'\n';

  u64 sq=10633609379ULL;
  auto a=row(10139,sq), b=row(10141,sq);
  std::cout<<"sharp primes "<<prime_trial(10139)<<' '<<prime_trial(10141)<<' '<<prime_trial(sq)
           <<" gap "<<b.r-a.r<<" rows "<<a.r<<' '<<a.low<<' '<<a.high<<' '<<a.threshold
           <<" | "<<b.r<<' '<<b.low<<' '<<b.high<<' '<<b.threshold<<'\n';

  std::vector<u64> quartet={3,5,7,11};u64 fq=M*quartet.back();while(!prime_trial(fq))++fq;
  std::vector<Row> fr;for(auto p:quartet)fr.push_back(row(p,fq));
  std::cout<<"four "<<fq<<" prime "<<prime_trial(fq)<<" span "<<fr.back().r-fr.front().r;
  for(auto z:fr)std::cout<<" | "<<z.p<<','<<z.r<<','<<z.low<<','<<z.high<<','<<z.threshold;std::cout<<'\n';

  u64 q=1000000007ULL;std::vector<Row> rows;u64 owner_sum=0;
  for(int p:ps)if(p>=239&&p<=953){rows.push_back(row(p,q));owner_sum+=p;}
  u64 mg=~u64(0);for(size_t i=1;i<rows.size();++i)mg=std::min(mg,rows[i].r-rows[i-1].r);
  std::cout<<"overload "<<rows.size()<<' '<<owner_sum<<" roots "<<rows.front().r<<' '<<rows.back().r<<" min_gap "<<mg<<'\n';

  u64 aq=1000000000039ULL,A=aq/4096,L=A*A/aq,U=((2*A)*(2*A)-1)/aq;
  std::vector<Row> ar;for(int p:ps){if(u64(p)<=L)continue;if(u64(p)>U)break;ar.push_back(row(p,aq));}
  u64 minlo=~u64(0),minhi=~u64(0);for(auto z:ar){minlo=std::min(minlo,z.low);minhi=std::min(minhi,z.high);}
  std::cout<<"analytic "<<prime_trial(aq)<<' '<<A<<' '<<L<<' '<<U<<' '<<ar.size()
           <<" owners "<<ar.front().p<<' '<<ar.back().p<<" roots "<<ar.front().r<<' '<<ar.back().r
           <<" gaps "<<minlo<<' '<<minhi<<'\n';
  std::cout<<"elapsed_seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<'\n';
}
```

### Counterexample and coverage summary

- **Confirmed:** 1025 root spacing is `REFUTED`; the smallest supplied sharp witness has exact gap 1024.
- **Confirmed:** a universal three-owner cap in a 6144 window is `REFUTED` by the exact four-owner witness above.
- **Strengthened:** the upstream six-site cap is valid but nonsharp; the all-scale prime-carrier cap is exactly four.
- **Confirmed:** assigning one historical (q) separately to every descendant is `REFUTED`; the 111-site witness leaves 107 sites after one optimal local packet.
- **Finite coverage:** every eligible owner for all 438,030 primes (qle10^7) above (3cdot2^{20}), the two large supplied witnesses, the analytic 15,072-owner example, and the complete 111-owner half-run.
- **Numerical uncertainty:** no integer or primality result used floating point. Decimal signs were stable at 120/180 digits and have margins above (0.4), but are not interval certificates. The universal sign claims rest on rational inequalities.

### Remaining proof obligations and referee requests

1. Audit the five-prime diameter dichotomy, strict floor transfer and exact four-owner witness in Claim 11.
2. If accepted, Lean may formalize the cap-four theorem against `vfMidHistoricalOwner_sqrt_iff`, then strengthen the literal selected-packet charge from (-1/640) to (-181/640). This is auxiliary, not a completion theorem.
3. `TAG-PACKET-DISJOINT-1` remains unresolved: an exact active-carrier theorem must decide which historical (q) is admitted, allocate it at most once, preserve masks/clipping/anchor/squareful terms/chronology, and retain every quadratic cross term.
4. The 111-site witness shows that local packets do not control the multiplicity residual. A new joint residual estimate on the original carrier is still required.
5. Claims `20261014-analytic-4/-5` save logarithms within one fixed tag but do not sum over tags or prove (O(Alog A)) endpoint discrepancy.
6. No computation here proves the canonical endpoint bound, first-bad payment, finite A/C, CORR-4, or RH.

### Updated final report summary

**Net-new mathematical progress:** `PAPER_PROOF` of the optimal all-scale four-owner cap in every 6144-root window and the strengthened one-history signed margin (-181/640); exact four-owner sharpness witness. Independent `FINITE_COMPUTATION` reproduced all new upstream integer examples.

**Completeness:** `DONE` for today's available arithmetic claims; `DONE_NO_NEW_RESULT` for the canonical endpoint target.

**No RH-proof claim:** yes.

## Updated next-run resume capsule — 2026-10-14T16:22:08-04:00

- **Source freshness:** main `13c3aeab8f84fc2309175261948a17a50c8342f4`; central and relevant source blobs listed above.
- **Upstream consumed:** today `00=TODAY=PENDING`; Owner `a2ed7dc2...`; Analytic `b8ee78df...`; Wheel `476d1af0...`; yesterday's five relevant blobs listed above.
- **Completed evidence worth reusing:** Claims `20261014-census-10..12`; exact cap four and witness ((q,p)=(11534351;3,5,7,11)); two-implementation reproductions; source hashes above.
- **Invalidations / corrections:** upstream cap six remains true but is nonsharp; replace its local worst-case packet margin (-1/640) by (-181/640) when the exact selected-set hypotheses hold. No source inclusion or global payment follows.
- **First unresolved blocker:** exact admitted tag ledger and joint residual/cross-term estimate without historical-tag reuse.
- **Next highest-value step:** Referee audit of Claim 11, followed only then by scoped Lean formalization; separately emit literal masked active-carrier tuples before testing any aggregate signed estimate.
- **For Agent #7:** formalize only the auxiliary cap-four and selected-packet theorem after referee acceptance; do not state source admission, global covariance, or canonical completion.
- **Avoid next run:** repeating unchanged bounded scans, paying multiple windows with one (q), dropping 107 residual descendants, or converting the linear packet into the global quadratic NNS.

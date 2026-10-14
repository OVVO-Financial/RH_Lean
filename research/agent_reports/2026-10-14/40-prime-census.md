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

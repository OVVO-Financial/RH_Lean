# RH_Lean Prime Census Laboratory - 2026-10-20

**Status:** COMPLETED  
**Run:** 2026-10-20T01:51-04:00 scheduled invocation  
**Canonical objective:** `VFCanonicalSquareVonKochStatement` remains OPEN  
**Campaign status:** `INCOMPLETE; NO INDEPENDENT 7/8 PROOF`  
**Evidence:** `PAPER_PROOF` (four-ideal trace classification), `FINITE_COMPUTATION` (independent exact censuses), `REFUTED` (strict pointwise fiber contraction), `NO_NEW_QUANTITATIVE_BOUND`

## A. Bottom line

This run independently audited the all-prime ideal incidence law from today's Wheel report and then tested a new discriminator: whether the complete four-label sextic fiber above one split semiprime owner automatically contracts after phase aggregation.

The zero-mask audit passed **13,869,765** exact coordinate cases over every split prime `p <= 499` and every `(a,b) in [-p,p]^2`. The observed active ideal-slot counts agree exactly with the proposed 2/1/0 rule:

```text
p does not divide N(a+b omega)              -> 2 active roots
p divides N, but (a,b) is primitive mod p   -> 1 active root
p divides both a and b                       -> 0 active roots.
```

The new result is a complete exact classification of the unit four-label trace. For distinct split primes `p,k`, let `alpha` and `bar(alpha)` be the two primary generators above `k`; retain both roots `r,r'` above `p`. If the phases of `alpha` are `zeta6^a,zeta6^b`, the conjugate generator has phases `zeta6^(-b),zeta6^(-a)`. Hence the once-fiber phase trace is

```text
T(p,k) = zeta6^a + zeta6^b + zeta6^(-b) + zeta6^(-a)
       = tau(a) + tau(b),
tau(e) = zeta6^e + zeta6^(-e) in {2,1,-1,-2}.
```

Therefore `T(p,k)` is a real integer in `{-4,-3,...,4}`, and the selected marked-minus-rescaled main trace is exactly `-T(p,k)`. This is an exact finite-state restriction, but **not a strict saving**: all nine values occur, including fully coherent `+4` and `-4` fibers.

The smallest coherent certificates found in the development range are:

```text
p=7, k=337, primary generators (-8,-21),(13,21):
  exponents (3,3,3,3), T=-4.

p=7, k=421, primary generators (-20,-21),(1,21):
  exponents (0,0,0,0), T=+4.
```

Thus any proposed universal bound `|T(p,k)| <= 3`, or any claim that conjugate-product conservation itself forces pointwise cancellation, is `REFUTED`. The genuine analytic gain must be an average/moment theorem across labelled conductors and slots, with the zero-extension branches restored; it cannot come from a deterministic contraction of each complete rational-owner fiber.

## B. Authority, provenance, and continuity

Final authority refresh at 2026-10-20T05:59:01Z:

- `main@976cfdf5808eee7e36b35bf16074c8915ff8fc4d`, merge of PR #984.
- `AGENTS.md` blob `20bff52d6784c17d4a7d6ac731f4a71c2bdad8a6`.
- `CURRENT_PROOF_CONTRACT.md` blob `2fa9931dcdc1fc8a816aefb8aa348db12ee9a384`.
- Native replication protocol blob `53194dc3ae106be363bc22cf85a88bac4a3b2e6e`.
- Dynamic protocol blob `bd1189617c069565a881c2a5c5dbd9a138bc48c1`.
- External inbox blob `038018145c0fddb2f6306c0712373adf9cd1ea52`.
- Native ideal-fiber source blob `cc99bbb2d02b700ff9cf2e555861208430f42acc`.
- Owner-projection source blob `3b957ea0ab1b53e2d6e79599329fb234f6e4561c`.
- Native declaration crosswalk blob `72889341548bc6518de7282287227bc38f65d8d5`.

Today's Wheel report was read at blob `16519e3f2bb2ee0da08ae843f5b3311c2fb5276c`; claim `20261020-wheel-1` is the paper 2/1/0 zero-mask and conjugate-product conservation theorem tested here. Today's Coordinator, Owner, Analytic, Referee, and Lean paths were absent at intake and final pre-publication fetch: `TODAY=PENDING`; no execution is inferred.

The 2026-10-19 reports were used as `YESTERDAY=CARRY_FORWARD`: Coordinator `6d27ec1427b2928fe36accc1642749f47a2cf6b6`, Owner `fbb74ff27ebbac9f9e3a683c569ec31c9f437b5e`, Analytic `c89e9038e1e1b61919b8788c294455680c2575b4`, Wheel `3ad449f5bd364aafcbe65375da865dfccad30d61`, Census `f87aaa1dc0d7e4b7f093e44141cefdce69ecc480`, and Lean `e460a4ccf95702bbea472e1847cf619f57e7d855`. The 2026-10-19 Referee path remained absent; the latest available Referee blob `c0360eaa56c34198f21f9387113fd565a19b542f` (2026-10-18) was used only as older continuity, not as review of today's claims.

Open PRs observed at final refresh: #987 draft head `6408d507`, #986 non-draft head `4345260a`, #985 non-draft head `8f51ddcb`, and #983 draft head `ed9bb56e`. None supplies the missing native inverse/plain moment estimates, and no PR state was changed.

## C. Mathematical question and preregistration

**Mystery.** Wheel conservation fixes the product of the two conjugate phases, while the merged `x/R=317/1027` examples show their sums vary. Does restoring the complete four-label norm fiber nevertheless force a strict deterministic contraction relative to its untwisted coefficient `+4`?

**H1 (fiber contraction).** The conjugate constraints force `|T(p,k)| <= 3` for every distinct split-prime pair. A pointwise fiber saving could then feed the later moment argument.

**H2 (coherent exceptional fibers).** The constraints make `T` real and discrete but permit `|T|=4`; only distribution across conductors/slots can save.

**Observable discriminator.** Enumerate all four exact phases, preserve both ideal roots and both primary cofactor orientations, and search specifically for `T=+/-4`. A single valid case refutes H1. Separately test the 2/1/0 mask on unit, primitive ramified, and content-divisible coordinates.

The development box was `7 <= p,k <= 499`; the disjoint validation boxes were `503..1999` and `2003..4999`. All arithmetic was integer exact.

## D. Exact trace proof

Let `r'=-1-r` be the second root of `X^2+X+1` modulo split `p`. If `alpha=a+b omega`, its primary conjugate is `bar(alpha)=(a-b)-b omega`. Evaluation gives

```text
bar(alpha)(r)  = alpha(r'),
bar(alpha)(r') = alpha(r).
```

The canonical sixth root at the conjugate ideal is the conjugate/inverse sixth root. Consequently, if the phase exponents of `alpha` at `(r,r')` are `(a0,b0)`, those of `bar(alpha)` are `(-b0,-a0) mod 6`. This identity was checked at every enumerated pair and follows directly from the finite-field definition used in `vf919SplitSexticResidue`.

Writing `tau(e)=zeta6^e+zeta6^(-e)` gives

```text
tau(0..5) = (2,1,-1,-2,-1,1),
T = tau(a0)+tau(b0) in {-4,-3,...,4}.
```

The complete four-label phase product is one, but this does not restrict the sum below four. Since `T` is real,

```text
sum_labels [-chi(label)^(-1)] = -conj(T) = -T.
```

**Claim `20261020-census-1`:** the displayed trace classification is `PAPER_PROOF` for the four-active-slot split-prime unit fiber. It does not cover the one/zero-active ramified branches or prove any averaged analytic estimate.

## E. Exact finite computations

### E.1 Zero-mask audit

For every split prime `p<=499` and every coordinate pair in `[-p,p]^2`, the program independently found both roots, evaluated `a+br`, and compared the active-root count against divisibility of `a^2-ab+b^2` and coordinate content.

```text
tests                         13,869,765
two active (norm nonzero)     13,785,360
one active (primitive norm 0)     84,000
zero active (a=b=0 mod p)            405
```

Small certificates at `p=7`, roots `(2,4)`:

```text
(a,b)=(-7,-6): residues (2,4), norm=1 -> two active
(a,b)=(-6,-4): residues (0,6), norm=0 -> one active
(a,b)=(-7,-7): residues (0,0), norm=0 -> zero active.
```

Classification: `FINITE_COMPUTATION`, independent support for `20261020-wheel-1`; not a proof of its universal quantifiers.

### E.2 Four-fiber trace census

Two implementations agreed exactly. Python used a linear prime enumeration, exhaustive primary-generator search, brute split roots, and exact `Z[ zeta6 ]` pairs. C++ used a separate Eratosthenes sieve, coordinate enumerator, modular exponentiation, and direct basis summation.

| range | split primes | ordered `p!=k` pairs | counts for `T=-4,-3,...,4` |
|---|---:|---:|---|
| 7..499 | 45 | 1,980 | 52, 230, 192, 233, 572, 187, 228, 236, 50 |
| 503..1999 | 103 | 10,506 | 286, 1243, 1114, 1182, 2894, 1053, 1241, 1274, 219 |
| 2003..4999 | 182 | 32,942 | 924, 3690, 3648, 3776, 9127, 3479, 3772, 3647, 879 |

All nine permitted trace values occur in every box. Coherent `+/-4` fibers persist in both disjoint validation ranges. Example validation certificates are `(p,k)=(523,739)`, exponents `(3,3,3,3)`, `T=-4`, and `(523,547)`, exponents `(0,0,0,0)`, `T=+4`.

Commands:

```sh
python sextic_zero_mask_audit.py
python sextic_fiber_census.py
g++ -O3 -std=c++17 -Wall -Wextra -Werror sextic_fiber_census.cpp -o sextic_fiber_census_cpp
./sextic_fiber_census_cpp
```

Environment: CPython 3.12.14; GCC 13.3.0. Source SHA-256 values: Python fiber `e5fab32a...e601`, C++ fiber `7a9b181b...3811`, zero mask `5cffc266...3273`. Output-row SHA-256 values for the three Python boxes were respectively `a36ce0ae...ebc`, `2852eaff...8ed`, and `548f9076...200`.

**Claim `20261020-census-2`:** H1 is `REFUTED` by exact counterexamples satisfying all four-active-slot hypotheses. The three-box distribution is `FINITE_COMPUTATION`; it is not an asymptotic equidistribution claim.

## F. Proof impact

1. **Reusable structural state variable.** A complete split-semiprime fiber is controlled by two conjugate trace classes `tau(a0),tau(b0)`, not by the rational owner `pk` alone and not by four independent random phases.
2. **Pointwise route closed.** Neither ideal multiplicity nor conjugate-product conservation yields a strict local contraction. A proof cannot replace the full four-label coefficient by a universal factor `<4`.
3. **Moment route remains viable.** Roughly one quarter of the tested fibers have trace zero, but coherent endpoint fibers persist. Only a source-compatible average with actual conductor, height, slot, principal, exceptional, and zero-branch weights could turn this distribution into a theorem.
4. **Once-only caution.** The four analytic labels still project to one physical integer owner. The trace must be formed on the labelled lift and pushed forward with a proved coefficient identity; it is not four spendable physical occurrences.
5. **No endpoint progress.** Stage I 11/12, actual local Euler error bills, inverse second moment, refined plain fourth moment, certified bands, native 7/8, canonical VF, and RH all remain OPEN.

## G. Continuation checkpoint

Do not enlarge this unit-fiber table unchanged. The next discriminating census should instantiate the Coordinator's two-prime finite-product formula on the **actual good/ramified mixed source**:

1. one selected split prime with two active roots;
2. one primitive `p|N(alpha)` row with exactly one active root;
3. the zero-extension local factor for the missing label;
4. direct Euler expansion versus the phase-preserving subset expansion;
5. every local remainder slot recorded separately.

The theorem candidate to test is not a contraction of `T`; it is an exact coefficientwise pushforward identity from the labelled good-plus-ramified product to the once-only physical source. Any duplicated owner or omitted zero branch is a decisive counterexample.

No RH proof claim.

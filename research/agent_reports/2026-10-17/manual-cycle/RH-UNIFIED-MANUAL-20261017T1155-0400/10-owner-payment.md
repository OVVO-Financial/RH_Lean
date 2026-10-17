# RH_Lean Owner Payment report — 2026-10-17 manual cycle

**Status:** COMPLETED.
**Execution:** this is the Owner role pass of one unified manual research cycle, which the repository owner requested. A single AI session ran it, not a scheduled agent. Run `RH-UNIFIED-MANUAL-20261017T1155-0400` started at 2026-10-17T11:55:23-04:00. The first session timed out after publishing three things: the Phase 1 checkpoint, `PREREGISTRATION.md` and draft PR #967. A second session resumed the same run ID and folder and wrote this pass at about 18:10 EDT. Nothing from the first session's Phase 2–6 work was published, so nothing from it is reused here. No agent was launched, scheduled or simulated, and no schedule was changed.
**Result classes:** `PAPER_PROOF` (Claims `20261017-manual-owner-1..3`); `CONDITIONAL_ON_RH` for parts of Claim `-owner-3`, with an unconditional corollary; `FINITE_COMPUTATION` (exact regressions); `REVISE` for two repository readings; `NO_NEW_RESULT` on `VFCanonicalSquareVonKochStatement`.

## A. Authority and inputs

- Main tip: `main@897563a14e9c04fcd2e4fb6d8e50cea7677854c7`, unchanged during the pass (live REST check at 22:05Z).
- Blobs at that revision:
  - `AGENTS.md` `8276a9a37da1`
  - `CURRENT_PROOF_CONTRACT.md` `b0c1f4e1ef27`
  - `docs/DYNAMIC_RESEARCH_AGENTS.md` `0bb1fe9f39c0`
  - `docs/FACTOR_DEPTH_RESEARCH_BRIEF.md` `21777e928051`
  - `docs/CROSS_COORDINATE_LOW_QUOTIENT_RESEARCH_2026_10_17.md` `412d1a82bb2d`
  - `docs/MERTENS_AMPLIFICATION_BUDGET.md` `62bbe73c4755`
- Lean sources used:
  - `RHLean/Analysis/SquareRootSmoothParityClasses.lean` `4ab1d3e410e1`
  - `RHLean/Analysis/SquareRootMatchedTransport.lean` `e9ab3bff6b88`
  - `RHLean/Analysis/SquareRootPositiveSmoothCollapse.lean` `50e7f2dd8af2`
  - `RHLean/Proof/SquareRootLowPrimeSmoothTransportRecoupling.lean` `f8fedce7c59c`
  - `RHLean/Proof/SquareRootLowPrimeMatchedCoreMertensObstruction.lean` `72dc62e01d7c`
  - `research/VF_MID_919_OAI_PRINCIPAL_COEFFICIENT_MAP.lean` `c06f8828962f`
  - `research/VF_MID_919_QUOTIENT_SIGNED_RETURN.lean` `32e68acd1a24`
- Notes whose readings are revised here:
  - `research/TWOAB_SCALE_TRANSFER.md` `d392c07f3720`
  - `export_mobius_synthesis/EMPIRICAL_DIAGNOSTICS.md` `60f57d1b1837`
  - `CURRENT_RESEARCH_HANDOFF.md` `02a1a5bef74b`
- PRs #915, #919, #931, #961, #964, #965 and #966 are merged. Draft #967 (this cycle) is open.
- Reports consumed:
  - today's scheduled Wheel, Census, Referee and Lean reports (claims `20261017-wheel-1/-2`, `-census-1/-2/-3`, `-referee-1..4`, `-lean-1`);
  - the 2026-10-16 Owner and Analytic reports (claims `owner-1..8`, `analytic-1..4`, Lemma M);
  - `EXTERNAL_HANDOFFS.md` (`EXT-20261017-HECKE-1..3`, `XCOORD-1..3`).

Notation:

- `X >= 12`, root cutoff `y = floor(sqrt X)`.
- `a6 = 1_((.,6)=1) (mu * chi_-3 mu)`; the period-36 kernel `K`; Hecke layers `P0(X;y)`, `P1(X;y)` (root cutoff, `BAD = 0`).
- `chi = chi_-3`; `pi_chi(z) = sum_(q<=z, q prime) chi(q)`; `pi_split(z) = #{q <= z : q = 1 mod 3}`.

## B. Claim `20261017-manual-owner-1` — the corrected crosswalk and the twisted dictionary

Define, for the cutoff `y`:

```text
A_y   = sum_(m<=X, P+(m)<=y) mu(m)                   (y-smooth Möbius mass)
T_y   = sum_(y<q<=X) M(floor(X/q))                     (classical high transport)
T^chi_y = sum_(y<q<=X) chi(q) M(floor(X/q))            (twisted transport)
H_y   = sum_(y<q<=X, q=1 mod 3) M(floor(X/q)),   I_y = T_y - H_y.
```

**Statement.** For every `X >= 12`:

```text
P1(X;y) = H_y = (T_y + T^chi_y)/2,      P0(X;y) = A_y + T^chi_y,      M(X) = P0 - 2 P1 = A_y - T_y.   (O1)
```

At the square endpoint `X = R^2-1`, `R >= 4`, we have `y = R-1`. Put `delta_R = 1_(R prime)`, `A_R = squareRootSmoothMass (R-1)` (smooth bound `P+ <= R`) and `T_R = squareRootTransportPrimeFirst R`. Let `H_R` and `I_R` be the split and inert parts of `T_R`. Then

```text
P0(R^2-1; R-1) = A_R + H_R - I_R + delta_R (1 + chi(R)) M(R-1),   P1 = H_R + delta_R 1_(R = 1 mod 3) M(R-1).   (O1')
```

**Proof.**

1. A norm `m <= X` with `P+(m) > y` has a unique prime `q > y`. Since `q^2 > X`, the prime `q` appears to exponent one, and `m = qs` with `s <= X/q <= y < q`. Hence `mu(m) = -mu(s)`. Summing over `s` gives `M(X) = A_y - T_y`; this is the compiled smooth/transport split at the square endpoint.
2. In the Hecke layer, the inert first powers vanish (`a6(q) = 0`), and split `q` has `a6(q) = -2`. The integer identity `floor(X/(sq)) = floor(floor(X/q)/s)` and the #919 map `F(u) = sum_(a<=u) a6(a) K(floor(u/a)) = M(u)` give `P1 = H_y`. The #919 map is compiled for `u >= 12`; the eleven values `u < 12` were checked directly. This is scheduled Claim `wheel-2` (W3) in prime form.
3. For `q != 3`, `1_(q = 1 mod 3) = (1 + chi(q))/2`, and `q = 3 <= y` never occurs. So `H_y = (T_y + T^chi_y)/2`.
4. Then `P0 = M + 2P1 = (A_y - T_y) + (T_y + T^chi_y) = A_y + T^chi_y`.
5. For (O1'): when `R` is prime, the only norms with `P+(m) = R` are `m = Rs`, `s <= R-1`. Hence `A_(R-1) = A_R + delta_R M(R-1)`, `T_(R-1) = T_R + delta_R M(R-1)` and `T^chi_(R-1) = T^chi_R + delta_R chi(R) M(R-1)`. Finally, `T^chi_R = H_R - I_R`. ∎

**Sign conventions.**

- `squareRootSmoothMass (R-1)` is `A_R`.
- `squareRootTransportPrimeFirst R` is `T_R`, by `squareRootTransportPrimeFirst_eq_mertensTransform`.
- `squareRootTransportMass` is minus the integer-site mass, which equals `T_R`.
- The compiled `squarePrefixMertens_eq_squareRootSmooth_sub_transport` reads `M(R^2-1) = A_R - T_R`.

These agree with (O1').

**What the dictionary says.** The Hecke root-cutoff representation contains exactly one object that is not already in the classical split: the twisted transport `T^chi_y`. The two Hecke layers are the classical smooth and transport masses, each shifted by the same `T^chi_y`:

```text
P0 = A_y + T^chi_y,     2 P1 = T_y + T^chi_y.
```

The coherent injection of −2 per top-half split prime is therefore the classical top transport cell plus a twisted remainder. At `X = 10^7`:

- `-2 * 158,004 = -316,008` equals `-(pi(X) - pi(X/2)) - (pi_chi(X) - pi_chi(X/2)) = -316,066 + 58`;
- over all cells, `T^chi_y = 135`, against `P0 = -47,157` and `A_y = -47,292`.

The large cancellation in `P0 - 2P1` is the classical `A_y - T_y` cancellation. It is not a new Hecke mechanism.

**Finite regressions** (exact integers; the census code is in `census1017.cpp`):

- (O1') held at all 398 roots `R in [4,400] ∪ {103, 317, 1027}`, with 0 failures.
- (O1) held at all 19,995 tested values, with 0 failures: every `X in [12, 20000]`, plus `R^2-1`, `R^2` and `R^2+1` for `R = 317, 1027`.

| R | X | M | A_R | T_R | H_R | I_R | P0 | P1 | naive `A+H-I` | correction |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 7 | 48 | −3 | 1 | 4 | 2 | 2 | −1 | 1 | 1 | −2 |
| 13 | 168 | −1 | 0 | 1 | 2 | −1 | −1 | 0 | 3 | −4 |
| 103 | 10,608 | −16 | −126 | −110 | −53 | −57 | −124 | −54 | −122 | −2 |
| 317 | 100,488 | −28 | −915 | −887 | −423 | −464 | −874 | −423 | −874 | 0 |
| 1027 | 1,054,728 | 367 | −6602 | −6969 | −3448 | −3521 | −6529 | −3448 | −6529 | 0 |

The correction is nonzero exactly at split prime roots: 7, 13 and 103 are `= 1 mod 3`. It vanishes at the inert prime 317 and at the composite 1027 = 13 * 79.

## C. Claim `20261017-manual-owner-2` — an unconditional inequality on the signed Hecke populations

**Statement (exact).** For `X >= 12`:

```text
T^chi_y = sum_(u <= floor(X/(y+1))) mu(u) [pi_chi(floor(X/u)) - pi_chi(y)],
T_y     = sum_(u <= floor(X/(y+1))) mu(u) [pi(floor(X/u)) - pi(y)].
```

Consequently, with every population kept signed,

```text
|P0(X;y) - A_y| = |2 P1(X;y) - T_y| = |T^chi_y| <= sum_(u <= X/(y+1)) |pi_chi(X/u) - pi_chi(y)|.   (O2)
```

**Proof.** Expand `M(floor(X/q)) = sum_(u <= X/q) mu(u)` and exchange the order of summation. The condition `q > y` with `u <= X/q` forces `u <= floor(X/(y+1)) <= y`. ∎

**Sizes.**

- Unconditionally, (O2) is `<< X exp(-c sqrt(log X))`, by the prime number theorem in progressions mod 3.
- Under GRH for the single function `L(s, chi_-3)`, `pi_chi(z) << z^(1/2) log z`, which gives `|P0 - A_y| << X^(3/4) log X`.

**Meaning.** The Hecke layers can differ from the classical layers only by a `chi_-3`-twisted prime transform, which `L(s, chi_-3)` alone controls. Suppose `L(s, chi_-3)` satisfies GRH. Then the two Hecke layers agree with `A_y` and `T_y` to `O(X^(3/4) log X)`, below the 7/8 scale, so the root-cutoff representation cannot carry any 7/8-scale cancellation that the classical smooth/transport split lacks. Suppose instead it fails. Then the layers carry extra `L`-zero oscillation, which must cancel between `P0` and `2P1`. In neither case is there a gain. This matches the Analytic H-L finding that the only `L`-content in these coordinates enters through `chi_-3`.

**Finite check.** The μ-form agrees with the direct prime sums at `X = 380, 1000, 4096, 4097, 10^4, 99999, 10^5, 10^6, 10^7`, with 0 failures. At `X = 10^7`, `T^chi_y = 135`, and the right side of (O2) is `10,911`.

## D. Claim `20261017-manual-owner-3` — the matched-core Ω theorem

**Objects.** These objects are compiled exactly on main:

- `S_q(R) := sum_(q<=R prime) M(q-1)`, which is `squareRootPositiveSmoothPrimeMertensTransform R`;
- `PositiveSmooth_R = -S_q(R)`, by `squareRootPositiveSmoothMass_eq_neg_primeMertensTransform`;
- `Matched_R := squareRootMatchedBornSmoothTransport R`, with

  ```text
  M(R^2 - 1) = -S_q(R) + Matched_R          (squarePrefixMertens_eq_neg_positivePrimeTransform_add_matched).
  ```

Both RH-scale targets on main read, with the quantifiers checked at blob `4ab1d3e410e1` / `e9ab3bff6b88`:

```text
SquareRootPositiveSmoothBoundedStatement  : forall eps>0, exists C, forall R>=2, |PositiveSmooth_R|^2 <= C R^(2+eps)
SquareRootMatchedTransportBoundedStatement: forall eps>0, exists C, forall R>=2, |Matched_R|^2        <= C R^(2+eps)
```

Put `Li(x) = int_2^x dt/log t`, `E = pi - Li` and `Sigma_1(R) = int_2^R M(t) dt/log t`.

**Theorem.**

- (a) *Unconditionally*, for every `delta > 0`, `Sigma_1(R)` is not `O(R^(3/2-delta))`.
- (b) *Under RH*, `S_q(R) = Sigma_1(R) + O_eps(R^(4/3+eps))`. Hence `S_q(R)` and `Matched_R` are each not `O(R^(3/2-delta))` for any `delta > 0`.
- (c) *Under RH*, `SquareRootPositiveSmoothBoundedStatement` and `SquareRootMatchedTransportBoundedStatement` are both false. So are the compiled equivalents of the latter:
  - `SquareRootUnifiedReciprocalBoundedStatement`;
  - `SquareRootMatchedCombinedBoundedStatement`;
  - `SquareRootMatchedPNTJointBoundedStatement`;
  - `SquareRootBornDyadicSurvivorBoundedStatement`.

  These equivalences are unconditional `iff` theorems on main.
- (d) *Unconditionally*, `¬(SquareRootMatchedTransportBoundedStatement ∧ SquareRootPositiveSmoothBoundedStatement)`.

**Proof of (a).** For `Re s > 2`, integration by parts gives

```text
int_2^inf Sigma_1(x) x^(-s-1) dx = Phi(s)/s,   Phi(s) := int_2^inf M(x) x^(-s) dx/log x,
Phi'(s) = -int_2^inf M(x) x^(-s) dx = -1/((s-1) zeta(s-1)) + int_1^2 x^(-s) dx,
```

using `int_1^inf M(x) x^(-w-1) dx = 1/(w zeta(w))` for `Re w > 1`.

1. Suppose `Sigma_1(R) = O(R^(3/2-delta))`. Then the left side is holomorphic on `Re s > 3/2 - delta`.
2. Hence `Phi`, and therefore `1/((s-1) zeta(s-1))`, continues holomorphically there.
3. Equivalently, `1/(w zeta(w))` is holomorphic on `Re w > 1/2 - delta`.
4. But `zeta` has zeros on `Re w = 1/2` (Hardy; for example, `rho_1 = 1/2 + 14.1347...i`), and `1/(w zeta(w))` has a pole at each of them. Contradiction. ∎

The method is the 2026-10-16 Owner "Lemma M" device (Mellin continuation against the known zero). The object here is different: Lemma M concerned the native VF band charge, while this is the compiled Mertens square-root positive orientation.

**Proof of (b).**

*Exact step.* For integer `R >= 2`:

```text
S_q(R)      = sum_(n<=R-1) mu(n)(pi(R) - pi(n)),
Sigma_1(R)  = sum_(n<=R-1) mu(n)(Li(R) - Li(n)),
J(R) := S_q(R) - Sigma_1(R) = sum_(n<=R-1) M(n) (E(n+1) - E(n))          (summation by parts).
```

*Blocking.* Group `n` into blocks `[a_j, a_j + h)` of length `h`, with an integer offset `theta in [0, h)`. On a block,

```text
sum M(n) dE(n) = M(a_j)(E(a_j+h) - E(a_j)) + sum (M(n) - M(a_j)) dE(n).
```

The second term is at most `h(2h+1)`, because `|M(n) - M(a_j)| <= h` and the block holds at most `h+1` primes plus `Li`-mass `<= h`. Over all blocks this totals `O(Rh)`.

*First term under RH.* Under RH, `max_(n<R)|M(n)| << R^(1/2+eps)` (Littlewood). Selberg's RH-conditional mean square applies:

```text
int_2^Y |psi(x+h) - psi(x) - h|^2 dx << h Y log^2 Y,   1 <= h <= Y.
```

It converts to `E` by partial summation. The conversion costs

```text
|E(x+h) - E(x)| <= |psi(x+h)-psi(x)-h|/log x + O((h x^(-1/2) + 1) log x + h^2/(x log x)).
```

The integer-point version follows because `psi(x+h) - psi(x)` moves by `O(log x)` on `[n, n+1)`. Averaging over the offset `theta` then yields an offset with

```text
sum_j |E(a_j+h) - E(a_j)| << R log R / sqrt(h) + (sqrt R + R/h + h) log R.
```

*Conclusion.* So `|J(R)| << R^(1/2+eps)(R h^(-1/2) + R/h + sqrt R + h) log R + Rh`. With `h = R^(1/3)`, this is `J(R) << R^(4/3+eps)`.

*Consequences.*

1. If `S_q(R) = O(R^(3/2-delta))`, take `delta' = min(delta, 1/7)`. Then `Sigma_1 = O(R^(3/2-delta'))`, which contradicts (a).
2. Under RH, also `M(R^2 - 1) = O(R^(1+eps))`. Hence `Matched_R = S_q(R) + O(R^(1+eps))` inherits the same Ω. ∎

**Proof of (c).** Each statement with `eps = 1/2` asserts an `O(R^(5/4))` bound, which (b) excludes. The equivalents follow from these unconditional `iff` theorems:

- `squareRootUnifiedReciprocalBounded_iff_matchedTransportBounded`;
- `squareRootMatchedCombinedBounded_iff_matchedTransportBounded`;
- `squareRootMatchedCombinedBounded_iff_pntJointBounded`;
- `squareRootBornDyadicSurvivorBoundedStatement_iff_matchedTransport`. ∎

**Proof of (d).** The compiled theorem `squarePrefixMertensGram_bounded_of_matched_and_positiveSmooth` turns the conjunction into `||squarePrefixMertens (R-1)||^2 <= C R^(2+eps)` for `R >= 2`. Reindexing `n = R-1` and absorbing `n = 0` into the constant gives `SquarePrefixEnergyBoundedStatement`; this one-line glue is not a separate compiled declaration. The compiled `riemannHypothesis_of_squarePrefixEnergy` then gives Mathlib's `RiemannHypothesis`. The two cases:

- If RH is false, the conjunction must fail.
- If RH is true, (c) refutes the positive-smooth statement.

In either case the conjunction is false. ∎

**Corollaries.**

1. *Neither statement can serve as the hypothesis of a route to RH.* Each of `Matched` and `PositiveSmooth`, and each compiled equivalent, implies `¬RH` by (c). Any proof of "X ⇒ RH" for one of them would refute X.

   This answers the point that `CURRENT_RESEARCH_HANDOFF.md` left open ("this audit does not prove … that the matched-only estimate is false"). Under RH it is false.
2. *The recoupling premise.* `SquareRootLowPrimeSmoothTransportRecoupling.lean` consumes `||Matched_R|| <= 3 R sqrt(K)`. Under RH, this premise fails for infinitely many `R` whenever `K = K(R) = O(R^(1-delta))`.
3. *The low-prime branch target.* `SquareRootLowPrimeMatchedCoreBound C R` asks for `||core R|| <= C R`. The compiled bridge `squareRootMatchedBornSmoothTransport_eq_core_sub_near` (`R >= 56`) gives `core R = Matched_R + nearPrimeTransport R`, with `|nearPrimeTransport R| <= 7R`. Hence under RH the core is not `O(R^(3/2-delta))`. For every fixed `C`, the target (complex and real forms) fails for infinitely many `R`.
4. *Increments survive, values do not.* The square-shell masses are unaffected: `delta_R = M((R+1)^2 - 1) - M(R^2 - 1) = Delta Matched_R - 1_(R+1 prime) M(R)`. So the Ω-growth of `S_q` lives in its accumulation, not in shell increments. The SB-7/8 lane is not refuted by this theorem, but it must keep the term `1_(R+1 prime) M(R)` attached. When `Theta > 3/4` that term exceeds the expected shell size.

## E. Revised repository readings

- **`research/TWOAB_SCALE_TRANSFER.md` §4** reads "the directly mirrored positive-orientation part already lives at the target linear scale in this range" (`R = 10^4`, `A_R^+ = 1885`).
  - The finite numbers are correct; this cycle reproduced `S_q(10^4) = -1885`, `M(10^8-1) = 1928` and `Matched = 43`.
  - The asymptotic reading is **refuted under RH** by Claim `-owner-3`. `|S_q(R)|` reaches `529,104,354 = 7.87 R` at `R = 67,250,683`, and `S_q(10^8) = 668,067,313`.
  - Mechanism: `S_q(R) log R ≈ -R + 2 Re sum_rho R^(rho+1)/(rho(rho+1) zeta'(rho))`. The trend `-R/log R` comes from `M(q-1) = M(q) + 1` at primes. It dominates while the first-zero amplitude `0.0125 R^(3/2)` is below `R`, that is, for `R` below about `6.4 * 10^3`.
  - **Verdict:** REVISE (finite-range statement only).
- **`export_mobius_synthesis/EMPIRICAL_DIAGNOSTICS.md`** fits "positive orientation `R^0.87`" over `100 <= R <= 2000` and says it "sits comfortably inside the exponent 1".
  - The fit reflects the same `-R/log R` trend regime.
  - Under RH the true growth is `R^(3/2-o(1))` infinitely often.
  - **Verdict:** REVISE/REFUTED as an asymptotic reading. The note itself says "neither of them asymptotic evidence", which was correct.

## F. Owner answer to the Coordinator's joint-restriction question

Where do `M = A - T`, `M = P0 - 2P1` and `B_X(t)` jointly restrict anything?

- **First two identities.** By (O1) these are one identity with `T^chi_y` added and subtracted. Their joint use restricts only `T^chi_y`, which (O2) bounds unconditionally by twisted prime counts. This is a genuine but `L(s, chi_-3)`-controlled inequality, not a Mertens saving.
- **Adding the buckets.** The Wheel renormalization (Claim `20261017-manual-wheel-1`) writes `B_X(t)` through the same prime cells `c_X(u)`. The relocation theorem shows that this moves signed mass of size `(3√3/π) X/log^2 X` between populations.
- **Matched-source alternative.** The signed nonlocal matched-source alternative in Möbius coordinates (`Matched_R`, `PositiveSmooth_R`, the core) is not easier than `V_low`: at RH scale it is false.

## G. Status of reviewed claims (Owner scope)

| Claim | Verdict | Note |
|---|---|---|
| `EXT-20261017-HECKE-2` (root cutoff, `BAD=0`, `M = P0 - 2P1`) | ACCEPT / IDENTITY_ONLY | refined by (O1): the layers are `A_y + T^chi`, `(T_y + T^chi)/2` |
| `20261017-wheel-2` (`P1 = sum_u c_X(u) M(u)`) | ACCEPT / PAPER_PROOF | equals `H_y` in prime form; reproduced in A2 |
| `20261017-census-1` (X = 10^7 integers) | REPRODUCED | independent code: `M = 1037`, `P0 = -47157`, `-2P1 = 48194`, 158,004 top-half split primes, `V = 23,765 + 1,782 = 25,547` |
| Checkpoint crosswalk (first session) | ACCEPT as (O1') | the `q = R` term is required at split prime roots |
| `TWOAB_SCALE_TRANSFER.md` §4 and `EMPIRICAL_DIAGNOSTICS.md` positive-orientation reading | REVISE | Section E |

## H. Unresolved obligations and handoffs

- **Analytic:** place Claim `-owner-3` beside the H-L window. Decide whether any zeta-only signed functional in the square-root coordinates is *not* sector-lossy. Shell increments (SB-7/8) are the remaining candidate.
- **Wheel:** a bucket-level version of (O1) is the renormalization identity D1 in the Wheel report.
- **Census:** done in this cycle (Part C, pre-registered H-MC: SUPPORTED, Pearson 0.99974).
- **Referee:** audit the Selberg-to-`E` conversion, the offset average and the reindexing glue in (d).
- **Lean:** the glue `SquarePrefixEnergyBoundedStatement` from the two premises is a one-line, nonduplicate compiled consumer and a good small target. The Ω theorem itself needs Mellin continuation of `1/zeta` and Selberg's mean square; this is not feasible in this cycle.
- **Not addressed:** native VF/#915 source payment and `VFCanonicalSquareVonKochStatement` (remains OPEN).

## I. Resume capsule

Reuse:

- `20261017-manual-owner-1`: (O1) and (O1') exact;
- `-owner-2`: (O2) exact, plus its sizes;
- `-owner-3`: the Ω theorem. (a) and (d) are unconditional; (b) and (c) assume RH.

Do not:

- seek RH-scale bounds on `Matched_R`, `PositiveSmooth_R`, the low-prime core or their compiled equivalents;
- read small-`R` fits of `S_q` as asymptotic scale.

No RH proof claim. No new unconditional power-saving bound.

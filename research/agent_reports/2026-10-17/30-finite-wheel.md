# RH_Lean agent daily report - 2026-10-17 / RH | Finite Wheel & Incidence

**Status:** COMPLETED  
**Run ID:** 2026-10-17T00:09:00-04:00, scheduled invocation  
**Result classes:** `PAPER_PROOF` (two exact structural identities), `FINITE_COMPUTATION` (boundary-stressed regressions), decisive mechanism restriction, `NO_NEW_RESULT` on the canonical bound

## A. Bottom line

The live objective remains `VFCanonicalSquareVonKochStatement`. This run resumed the post-Coordinator squarefree-kernel / dyadic-toggle work rather than enlarging a wheel.

Two exact restrictions were obtained.

1. The Owner truncation defect
   `E_N(t,s)=2A_N(t,s)-A_N(t,2s)`
   is exactly twice a short divisor-window count. Hence it is even. After the prime-2 floor pairing, the parity term and boundary term are sign-coherent on every fixed `(t,s)` packet. There is no hidden packetwise cancellation between them.
2. Independently auditing draft PR #964's square-root Hecke cutoff gives an exact quotient-cell compression of its high-prime layer. Every large split prime is a unique greatest factor, and all primes in the same cell `floor(X/q)=u` have the identical old-prefix response `M(u)`. The large-prime layer is therefore a positive prime-cell multiplicity transform of earlier Mertens values. This exposes the precise nonlocal compensation required but does not bound it.

Neither identity supplies a whole-prefix exponent gain. The canonical theorem, MU-LIFT inequality, full zero-target source payment, finite A/C, CORR-4 and RH remain open.

## B. Authority, continuity and source state

Live authority at intake and final prepublication refresh:

- `main@b9105f19fbbf25742a6909a6e8c995e6a9ddeddb`.
- `AGENTS.md` blob `9de61f7cb75c048f132ca048d5b16f4900aa7109`.
- `CURRENT_PROOF_CONTRACT.md` blob `ddb716eeb08aeb9237c9652bc710a08a2a06c1c8`.
- Factor-depth brief `beb9984a92b07248363bf8c6e70a1c8893abcc24`; dynamic protocol `5a954ef55b4297526f0867fcc798869eea017927`; amplification budget `62bbe73c4755eaa64772ec2cc2731936c01b49cd`.
- Canonical statement source `research/VF_CANONICAL_SQRT_TWO_VON_KOCH.lean`, blob `43e160ac7ad51f7646771297f43a9b95395ce709`.
- Genuine signed hyperbola source `research/MERTENS_SIGNED_HYPERBOLA.lean`, blob `d199571f19346797229a25b0fa53c6e80499999f`.
- Compiled #919 coefficient/kernel source `research/VF_MID_919_OAI_PRINCIPAL_COEFFICIENT_MAP.lean`, blob `c06f8828962fabff89668a142a8b09809afcae01`.
- Merged root-wall source `RHLean/Proof/RootWallCompleteFibre.lean`, blob `054694c0aa125e6f542a3208d85d30c2d79fb320`.

All named 2026-10-17 reports were absent at intake: `TODAY=PENDING`. The complete 2026-10-16 evidence was carried forward: Coordinator mirrors `fc5c5b46a0ec56f606444bb5dbfe400d4a444d18`; Owner `cb42efd7a6aa0e782c353803e604684b9500cdb2`; Analytic `2b93e7c237c09439746a93356c20cd15e4671028`; Wheel `134eb9eb0558a622b6f042baa20f3feb847ed6f4`; Census `26510606eea9f43450e5bb092c4542ab23fcb729`; Referee `e4c0a92301f032eb732a51f7bd997f4a19ac8b48`; Lean `180cf24f8444852a5b69bf2581f0c6d160f3a16e`. These contain one unified manual cycle plus later scheduled continuations where stated; the manual Referee pass is still a same-session self-audit.

External inbox blob `c1d1aad9872d1760d2e4e34b30bbc0ed4fa3d33c` was consumed. `EXT-20261014-1..5` and `CL-20261014-1..11` retain their recorded scopes; none pays the identities below.

Draft PR #964 was open at intake and changed head during inspection. Its Hecke cutoff note was read at head `1900d67416f96b0c4ac5b9ccba43a55ce0bd3e26`, note blob `b7643d7e6daf3f66357594d84d1ba87c8fe32542`. It is draft paper/computational work, not authority on `main` and not a proved exponent.

## C. Claim `20261017-wheel-1` - exact boundary-window classification

Let `N>=1`. Let `s,t` be odd squarefree positive integers with `gcd(s,t)=1), and put
```text
A_N(t,s) = #{a | s : t*a <= N and t*(s/a) <= N},
E_N(t,s) = 2 A_N(t,s) - A_N(t,2s).
```
For `t<=N`, put `L=floor(N/t)` and
```text
B_N(t,s) = #{a | s : s/a <= L and L/2 < a <= L}.
```
Then exactly
```text
E_N(t,s) = 2 B_N(t,s).                                      (W1)
```
In particular
```text
E_N is even,    0 <= E_N <= 2 A_N.
```

**Proof.** An admissible divisor `a|s` represents the ordered base factorization
`(t*a, t*(s/a))`. In the fibre `2t^2s`, the prime 2 has two physical placements. The placement doubling the first factor survives exactly when `2ta<=N`; the other survives exactly when `2t(s/a)<=N`. Thus
```text
E_N = sum_(admissible a) [1_(2ta>N) + 1_(2t(s/a)>N)].
```
The involution `a -> s/a` exchanges the two indicators and preserves admissibility, so both sums are equal. The first is precisely `B_N`. This proves (W1) without cloning an occurrence.

### Corollary - fixed-packet sign coherence survives the dyadic transform

Let `d=t^2s`, `y=floor(X/d)`, and use Owner Claim `20261016-owner-7`:
```text
h_N(d) floor(X/d) + h_N(2d) floor(X/(2d))
 = mu(s)[A_N(t,s)(y mod 2) + E_N(t,s) floor(y/2)].
```
By (W1), the nonnegative bracket is
```text
B_N(t,s)*y                         if y is even,
A_N(t,s)+B_N(t,s)*(y-1)           if y is odd.               (W2)
```
Therefore every nonzero paired packet still has sign `mu(s)`. The parity and truncation-boundary terms never cancel each other within a fixed `(t,s)) packet. A useful bound must obtain cancellation across distinct squarefree kernels `s`, or jointly with the retained even-even/odd half-scale kernel. Odd residue restrictions alone cannot create a missing opposite sign inside the packet.

This strengthens, without contradicting, Coordinator Claims `20261016-coordinator-3/-4`: the prime-2 toggle cancels the bulk floor scale, but fixed squarefree-kernel sign coherence remains.

**Sharpness.** At `N=8,t=1`, examples `s=1,5,35` realize respectively `E/A=0,1,2`. Hence no uniform improvement of either endpoint `0<=E<=2A` follows from squarefreeness and oddness alone.

**Status:** `PAPER_PROOF / NEW_EXACT_STRUCTURAL_THEOREM`. It is an identity, not a signed asymptotic estimate.

## D. Claim `20261017-wheel-2` - root-cutoff quotient-cell compression

This is an independent structural audit of the draft #964 square-root cutoff, using the already compiled #919 coefficient map on `main`.

Let `X>=12`, `y=floor(sqrt X)`, and let
```text
F(u) = sum_(1<=a<=u) a6(a) K(floor(u/a)),
```
with the exact #919 excluded-norm coefficient `a6` and period-36 quotient kernel `K`. For `u>=12`, the compiled theorem gives `F(u)=M(u)); direct evaluation of the eleven finite cases `1<=u<12` gives the same equality.

At the root cutoff, every surviving large prime is split, occurs to exponent one, is greater than `sqrt X), and is the unique greatest prime factor. Thus the draft high-prime layer satisfies
```text
P1(X;y)
 = sum_(q>y, q prime, q == 1 mod 3) F(floor(X/q))
 = sum_(1<=u<=y) c_X(u) M(u),                              (W3)
```
where the exact nonnegative quotient-cell multiplicity is
```text
c_X(u)
 = pi_split(floor(X/u))
   - pi_split(max(y, floor(X/(u+1)))),
pi_split(z) = #{q<=z : q prime and q == 1 mod 3}.           (W4)
```

**Proof.** For `q>floor(sqrt X)`, every cofactor satisfies
`a<=floor(X/q)<=y<q`; it is automatically root-smooth, and `q` is its unique large/greatest factor. The integer identity
```text
floor(X/(a*q)) = floor(floor(X/q)/a)
```
makes the inner response exactly `F(floor(X/q))`. Finally,
`floor(X/q)=u` iff
```text
floor(X/(u+1)) < q <= floor(X/u),
```
and intersecting with `q>y` gives (W4). These cells are disjoint and cover every physical high-prime occurrence once.

The root-cutoff identity can consequently be written
```text
M(X) = P0(X;y) - 2 sum_(1<=u<=y) c_X(u) M(u).              (W5)
```
This is an exact old-prefix incidence transform, but `P0` contains the complete root-smooth population. Equation (W5) does not supply a contraction: the coefficients `c_X(u)` are nonnegative and the coherent top cell is
`c_X(1)=pi_split(X)-pi_split(floor(X/2))`. Any saving must be a genuinely nonlocal compensation between the smooth population and the entire signed earlier-prefix response, not an involution among high primes.

**Status:** `PAPER_PROOF / NEW_REPRESENTATION`, conditional only on the already compiled #919 identity plus eleven direct finite base cases. No quantitative estimate is claimed for either side.

## E. Falsification and exact finite regression

For Claim wheel-1, an independent exact enumerator checked 262,078 odd squarefree coprime triples with `N<=100`, `s<=300`:
```text
E_N = 2 B_N,  E_N even,  0<=E_N<=2A_N: zero failures.
```
It also checked (W2) in 118,509 packet/cutoff cases and found zero failures. The sharp `E/A=0,1,2` witnesses above were found without weakening the hypotheses.

For Claim wheel-2, a separate exact integer sieve checked 306 boundary-stressed values through `X=20000`, including neighborhoods of squares:
```text
P1 = sum_u c_X(u) M(u),
P0 - 2 P1 = M(X): zero failures.
```
Examples include `X=15,16,17,999,1000,1024,4095,4096,4097,9999,10000,10001,19999,20000`. Floors, strict lower cell endpoints, the root cutoff and the finite `u<12` responses were retained. These computations support the proofs; they are not all-scale evidence for cancellation.

Strongest adverse conclusions:

- The boundary defect can be as large as `2A_N`; odd/squarefree structure does not make it small packetwise.
- In (W2) the parity and boundary terms have the same packet sign.
- In (W3) prime cells have nonnegative multiplicity; the fixed mod-3 character only selects support and supplies no oscillatory high-prime phase.
- Applying absolute values to either identity loses the cross-kernel/cross-layer cancellation still needed.

## F. Novelty and no-circularity audit

Repository and report searches found Coordinator's squarefree-kernel compression and Owner's definition/support description of `E_N`, but not the exact formula `E_N=2B_N`, its evenness, or the closed packet law (W2). The formula is not the MU-LIFT estimate and does not imply one.

Draft #964 contains the root two-layer identity, prime-extension recurrence, and isolated top-half cell, but not the full disjoint quotient-cell formula (W3)-(W4) or its exact identification with earlier Mertens prefixes. This is a structural compression of its high-prime layer, not an assertion that the remaining smooth/high-prime compensation is small. Bounding the complete recombined right side at the required exponent without new input would be target-equivalent.

No claim here changes the original physical VF carrier or transfers Hecke/Mobius identities into #915's masked/clipped returned cells.

## G. Decisions and handoffs

- **DYADIC-KERNEL:** `CONTINUE / REVISE`. Use (W1)-(W2) to remove the false hope of parity-versus-boundary cancellation inside one packet. The next valid input must couple different squarefree kernels and the odd half-scale term before norms.
- **Packetwise residue or least-prime cancellation:** `REJECT` unless it genuinely mixes different `s); every fixed packet is sign-coherent.
- **Hecke root-cutoff quotient cells:** `CONTINUE as a structural interface`. The exact consumer is (W5); its top prime cohort is coherent and must be compensated nonlocally.
- **Unsigned wheel enlargement / termwise capacity:** `REJECT` as a complete route.
- **Lean:** wheel-1 is a small formalization candidate only after independent Referee acceptance. Wheel-2 should not be formalized merely to restate a draft identity unless its quotient-cell form is selected as a useful consumer.
- **Census:** no undirected larger scan is requested. If needed, test the joint signed covariance of the three exact D3 sectors, or the cell transform versus `P0), with a held-out range and all integer endpoints fixed in advance.
- **Referee:** audit the divisor involution in (W1), the `E/A=2` sharp case, the finite `u<12` #919 base cases, and the lower endpoint in (W4).

## H. Resume capsule

Reuse Claims `20261017-wheel-1/-2`.

First missing arithmetic theorem on the dyadic route: an independently proved signed estimate across distinct squarefree kernels for the full (W2) packet sum jointly with the odd half-scale kernel, with final amplitude exponent `r<2`, subpower loss and full-prefix coverage.

First missing theorem on the Hecke route: a uniform nonlocal estimate coupling the root-smooth term `P0` to the complete quotient-cell transform `sum c_X(u)M(u)`; a bound on their already-recombined difference is not independently smaller.

Do not claim packetwise cancellation, clone divisor placements, omit the `4|d` sector, treat the mod-3 selector as oscillatory, transfer raw/Hecke carriers into #915, or infer an exponent from the finite checks.

No RH proof claim.


## I. Publication verification

Substantive report commit: `1d1c2090ccbf64d89ac786a058e110195de20ec2`. Immediate readback blob: `347e26297bdceaaa3a7376d0b7d189011a486275` (12,646 characters), containing both claim IDs and the explicit `NO_NEW_RESULT` classification.

Final live refresh still found `main@b9105f19fbbf25742a6909a6e8c995e6a9ddeddb`. Draft PR #964 remained open, draft and unmerged, but its live head had advanced to `c5369f2abb3bf0b398eab321c2fdf36ccc48c893`. Claim wheel-2 was proved from the specifically recorded note blob `b7643d7e6daf3f66357594d84d1ba87c8fe32542` plus compiled main source; no uninspected later PR edit is silently incorporated.


CI state on the final observed #964 head: Documentation checks run `39001645477` succeeded; Proof inventory run `39001645500` succeeded; Canonical VF sqrt2 full autopsy run `39001645442` was still in progress. No failed run was reported. The PR remains draft, so this report makes no review-state or merge action.

# RH_Lean Analytic Type II report — 2026-10-17 manual cycle

**Status:** COMPLETED.
**Execution:** this is the Analytic role pass of one unified manual cycle, which the repository owner requested. A single AI session ran it as run `RH-UNIFIED-MANUAL-20261017T1155-0400`, which a second session continued after the first timed out. It is not a scheduled agent, and no agent was launched, scheduled or simulated.
**Result classes:**

- `PAPER_PROOF`: Claims `20261017-manual-analytic-1..6`. Claim `-1`'s finite face is also `PROVED_IN_LEAN` on draft PR #967.
- `TARGET_EQUIVALENT` classifications.
- `HEURISTIC`: one remark on SB-7/8.
- **No new unconditional power-saving bound.** The only unconditional upper bound proved here, Claim `-5`, is of PNT strength.

## A. Authority and inputs

- `main@897563a14e9c04fcd2e4fb6d8e50cea7677854c7`, with the blobs listed in `10-owner-payment.md`.
- Compiled inputs on `main`:
  - `research/VF_MID_919_OAI_PRINCIPAL_COEFFICIENT_MAP.lean` (`c06f8828962f`);
  - `research/VF_MID_919_QUOTIENT_SIGNED_RETURN.lean` (`32e68acd1a24`): the exact return `M(X) = sum_(t<=X) P36(t)(B_X(t) - B_X(t+1))` for `X >= 12`, and `|P36| <= 4`.
- Draft PR #967, head `cdde68f595570d11a0c109c67203765334fdafba` (exact-head CI 11/11 success):
  - `V_high <= 2 sqrt X`;
  - `sum_(n<=N) |a6(n)| <= N`;
  - the new lower bound of Claim `-1`.
- Inputs from this cycle: the Owner pass (Claims `-owner-1..3`) and Census Parts A–D.
- Earlier reports used: 2026-10-16 `analytic-1..4` (MU-LIFT anatomy and calibration) and `owner-4` (Lemma M); 2026-10-17 `referee-3`, `census-3`.

Notation:

- `F(s) = sum a6(n) n^(-s) = 1/[zeta(s) L(s,chi_-3)(1-3^(-s))(1-4^(-s))]` and `C6(x) = sum_(n<=x) a6(n)`.
- `B_X(t) = C6(X/t) - C6(X/(t+1))`, `D_X(t) = B_X(t) - B_X(t+1)`, `r = floor(sqrt X)`.
- `V_low(X) = sum_(t<=r) |D_X(t)|`.
- `Theta_K := sup{Re rho : zeta(rho) L(rho, chi_-3) = 0}`, the zero abscissa of the Dedekind zeta function of Q(√−3), up to its Euler factors at 2 and 3. Since `zeta` has zeros on `Re s = 1/2`, `1/2 <= Theta_K <= 1`.

## B. Claim `20261017-manual-analytic-1` — H-L: the low variation encodes the zeros of `zeta * L(s, chi_-3)`

**Statement.**

- (i) *Finite face; unconditional; compiled on PR #967 as `vf919HalfIncrement_norm_le_lowVariation_add_boundary` and `_add_sqrt`.* For every `X`:

  ```text
  |C6(X) - C6(floor(X/2))| <= V_low(X) + |B_X(r+1)| <= V_low(X) + sqrt X.
  ```
- (ii) If `V_low(X) = O(X^theta)` for some `1/2 <= theta < 1`, then `C6(x) = O(x^theta)`. Hence `zeta(s) L(s, chi_-3) != 0` on `Re s > theta`, that is, `Theta_K <= theta`.
- (iii) If `Theta_K > 1/2`, then for every `theta < Theta_K`, `V_low(X)` is not `O(X^theta)`.

**Proof.**

1. *(i).* `sum_(t<=r) D_X(t)` telescopes to `B_X(1) - B_X(r+1)`, and `B_X(1) = C6(X) - C6(floor(X/2))`. The boundary bucket holds at most one norm `m <= X/(r+1) <= r`, and it is bounded by the compiled mass bound.
2. *(ii).* Write `C6(X) = sum_(k>=0) [C6(X/2^k) - C6(X/2^(k+1))]`. Each bracket is `<< (X/2^k)^theta + (X/2^k)^(1/2)` by (i), and the geometric series converges. Then `F(s)` converges for `Re s > theta`. The factors `(1 - 3^(-s))(1 - 4^(-s))` vanish only on `Re s = 0`, so `zeta L` has no zeros there.
3. *(iii).* This is (ii) in contrapositive form. ∎

**Census evidence (Part B, pre-registered; H-L SUPPORTED).** The observable `f_C6 = B_X(1)/sqrt X`, over `log X in [log 10^3, log 10^8]`, has spectral peaks at:

- `11.25`, `8.04`, `15.74`, `18.27`, `24.08`, `28.19`, which are zeros of `L(s, chi_-3)`. Computed values: `8.0397`, `11.2492`, `15.7046`, `18.2620`, `20.4558`, `24.0594`, `26.5779`, `28.2182`.
- `14.13`, which is a zeta zero.
- `20.80`, an unresolved merge of the `L` zero `20.46` and the zeta zero `21.02`.

By contrast, `f_M` peaks only at zeta zeros (`14.13`, `21.02`, `25.01`); its height at 8.04 is 1.07 against 2992 at 14.13. Both held-out halves pass.

## C. Claim `20261017-manual-analytic-2` — the exponent window of `V_low`

Let `lambda_V := inf{lambda : V_low(X) = O(X^lambda)}`.

**Statement.**

```text
Theta_K <= lambda_V <= 1/(2 - Theta_K).
```

**Proof.**

- *Lower bound.* This is Claim `-1` (ii).
- *Upper bound, step 1.* `V_low <= 2 sum_(t<=r+1) |B_X(t)|`.
- *Step 2.* Suppose `zeta L` is zero-free on `Re s > Theta`. The standard Littlewood–Landau argument then gives `C6(x) << x^(Theta+eps)`. That argument applies Borel–Carathéodory to `log` of `zeta L` in the zero-free region and then Perron's formula; it is the analogue of "zero-free for `Re s > theta` ⇒ `M(x) << x^(theta+eps)`".
- *Step 3.* Hence `|B_X(t)| << (X/t)^(Theta+eps)`. Separately, `sum_(t>T) |B_X(t)| <= sum_(m<=X/(T+1)) |a6(m)| <= X/(T+1)`, by the compiled mass bound.
- *Step 4.* Take `T = X^((1-Theta)/(2-Theta))`. This balances `X^Theta T^(1-Theta)` against `X/T` and gives `X^(1/(2-Theta)+eps)`. ∎

**Consequences.**

| hypothesis on `Theta_K` | variation exponent obtainable |
|---|---|
| GRH for ζ·L(s,χ₋₃) (`Theta_K = 1/2`) | `V_low << X^(2/3+eps)` |
| `Theta_K <= 6/7` | `V_low << X^(7/8+eps)` |
| `Theta_K <= 7/8` | `V_low << X^(8/9+eps)` only |
| `Theta_K <= 11/12` | `V_low << X^(12/13+eps)` only |

- The target `V_low = O_eps(X^(7/8+eps))` is **sandwiched**. A zero-free region `Re s > 6/7` for `zeta * L(s,chi_-3)` implies it, and it in turn implies a zero-free region `Re s > 7/8` for both functions. It is therefore a quasi-GRH statement for one Dedekind zeta function, *not* an input independent of zero-free regions.
- The externally reported result is a non-peer-reviewed claim from October 2026: a zero-free region `Re s > 11/12` (7/8 in the repository catalog) for `zeta`, all Dirichlet L-functions and Hecke L-functions over Q(√−3). If it is true, the variation route turns it only into `V_low << X^(12/13+eps)` or `X^(8/9+eps)`. **Even importing it would not give the 7/8 variation bound** unless the window closes; see Section H.
- Scheduled `20261017-census-3` proposed the benchmark `V <= sqrt X log X`. As an all-`X` statement it implies `Theta_K = 1/2`, that is, GRH for ζ·L(s,χ₋₃). It should be labelled a GRH-strength conjecture, not a benchmark.

## D. Claim `20261017-manual-analytic-3` — classification of the signed low returns

This answers the Coordinator's question: could a signed nonlocal inequality be easier than the absolute `V_low`?

**General identity.** For any `g` with `g(0) = 0`:

```text
sum_(t>=1) g(t) B_X(t) = sum_(m<=X) a6(m) g(floor(X/m)) = sum_(n<=X) (a6 * Delta g)(n),   Delta g(n) = g(n) - g(n-1).
```

Its Dirichlet series is `F(s) G_g(s)`, with `G_g(s) = sum Delta g(n) n^(-s)`. The functional is blind to `L(s, chi_-3)` exactly when `G_g` cancels the `1/L(s, chi_-3)` in `F`. The K-pairing is such a case (`Delta g = k`, `G = L(s,chi_-3)(1-3^-s)(1-4^-s)`), and so is the residue-class aggregate `U_1` of Claim `-6` (`Delta g = chi_-3`).

The three low-quotient candidates:

1. **Unweighted signed low return** `R_0(X) = sum_(t<=r) D_X(t) = C6(X) - C6(X/2) - B_X(r+1)`.
   - For `theta >= 1/2`: `R_0 = O(X^(theta+eps))` for every `eps` ⟺ `Theta_K <= theta`.
   - **TARGET_EQUIVALENT** to a zero-free strip of `zeta * L(s, chi_-3)`. This is strictly *broader* than the Mertens target, because it also needs `L(s, chi_-3)`.
2. **K-weighted signed low return** `R_K(X) = sum_(t<=r) P36(t) D_X(t) = M(X) - sum_(t>r) P36(t) D_X(t) = M(X) + O(8 sqrt X)`.
   - This uses the compiled return, `|P36| <= 4` and `V_high <= 2 sqrt X`.
   - **TARGET_EQUIVALENT** to `M`.
   - Census values of `R_K - M`: `8`, `4`, `−15` at `X = 10^5, 10^6, 10^7`, against `8 sqrt X = 2530, 8000, 25298`.
3. **Absolute** `V_low`. It dominates both returns: `V_low >= |R_0|` and `V_low >= |R_K|/4`. Its exponent lies in the window of Claim `-2`.

**Verdict.** A signed low-bucket functional that controls `M` is either `M` itself (K-weighted) or harder than `M` (unweighted, `L`-sensitive). Neither is easier. Dropping absolute values does not create an intermediate target.

## E. Claim `20261017-manual-analytic-4` — no periodic-kernel representation escapes the extra L-content

**Setting.** Let `k` be `q`-periodic with `k(1) != 0`. Assume that its partial sums `K_k(t) = sum_(n<=t) k(n)` and its second partial sums are bounded; this is what the #919 kernel satisfies, with `|P36| <= 4`. Then its Dirichlet series `K(s)` is entire, because mean zero removes the pole. Write `mu = a * k`, so `A(s) = 1/(zeta(s) K(s))`. Assume `|a(m)| << m^(1/2)`. The signed Abel return with the bounded second primitive gives `|M| << V^(a)` (all buckets). The proof of Claim `-1` gives

```text
V^(a)_low(X) >= |sum_(X/2<m<=X) a(m)| - O(sqrt X).
```

**Statement.** If `V^(a)_low(X) = O(X^theta)` with `1/2 <= theta < 1`, then:

- `zeta(s) K(s) != 0` on `Re s > theta`;
- `K = P · L_psi`, with `P` a Dirichlet polynomial and `psi` a **non-principal** primitive character;
- `L_psi` is zero-free on `Re s > theta`.

In every admissible case, `V^(a)` encodes a quasi-GRH statement for some Dirichlet L-function on top of the zeta statement.

**Proof.** The first conclusion is Claim `-1` with `a` in place of `a6`. Then:

1. *Not of the form `P · L_psi`.* By Saias–Weingartner, such a `K` has `>> T` zeros in every strip `1/2 < sigma_1 < Re s < sigma_2 < 1 + eta`, which contradicts zero-freeness on `Re s > theta`.
2. *`psi` principal.* Then `K = P zeta` up to finitely many Euler factors, and entireness forces `P(1) = 0`. Bohr almost-periodicity and Rouché then give zeros of `P` arbitrarily close to `Re s = 1`, again a contradiction.
3. *`psi` non-principal.* `L_psi` has infinitely many zeros on `Re s = 1/2` (Hardy-type theorem), and every zero of `L_psi` must have real part `<= theta`. ∎

**Meaning.** The `chi_-3` sensitivity found in H-L is not an accident of #919. It is the price of any bounded-primitive periodic kernel. The #919 choice `K = L(s,chi_-3)(1-3^-s)(1-4^-s)` is of the least-lossy type: one primitive L-function, and Dirichlet-polynomial zeros only on `Re s = 0`.

*Source note:* the Saias–Weingartner statement was read from the ar5iv rendering of arXiv:0807.0783 (Acta Arith. 140 (2009)). The arXiv abstract page itself could not be fetched (HTTP 429 from the web proxy).

## F. Claim `20261017-manual-analytic-5` — the one unconditional upper bound proved

**Statement.** For every `1 <= T <= r`:

```text
V_low(X) <= 4 T max_(x<=X) |C6(x)| + 2 X/(T+1).
```

With the classical zero-free region for ζ·L(s,χ₋₃), `max |C6| << X exp(-c sqrt(log X))`. Choosing `T = exp((c/2) sqrt(log X))` gives

```text
V_low(X) << X exp(-(c/2) sqrt(log X)).
```

**Proof.**

1. `V_low <= 2 sum_(t<=r+1) |B_X(t)|`.
2. The terms with `t <= T` are each `<= 2 max |C6|`.
3. The terms with `t > T` together are `<= sum_(m<=X/(T+1)) |a6(m)| <= X/(T+1)`, by the compiled mass bound. ∎

**Status:** `PAPER_PROOF`. It is a genuine unconditional inequality, but it is only of PNT strength; *no power saving*. It is used to prove that `V_low = o(X/log^A X)` for every `A`, which the Wheel relocation theorem needs.

## G. Claim `20261017-manual-analytic-6` — the L-blind residue aggregate `U_1`

**Statement (exact).** Put `U_j(X) := sum_(t = j mod 3) B_X(t)`. Then:

```text
U_1(X) = sum_(a,b>=0) M(floor(X/(3^a 4^b))),
M(X) = U_1(X) - U_1(floor(X/3)) - U_1(floor(X/4)) + U_1(floor(X/12)),
U_0 + U_1 + U_2 = C6(X).
```

**Proof.**

1. Use `g = C_chi = 1_(t = 1 mod 3) = sum_(n<=t) chi(n)` in the general identity of Claim `-3`. Then `Delta g = chi_-3` and `F · L = 1/[zeta (1-3^-s)(1-4^-s)]`. This gives `a6 * chi = mu * 1_({3^a 4^b})`.
2. Inverting the two geometric factors gives the second line.
3. Every `t` lies in exactly one class, which gives the third line. ∎

**Census check.** Part A5 holds exactly at 19,995 values of `X`. In Part B, `f_U1` is L-blind (ratio `0.001` at 8.04), while `f_U0` (`0.36`) and `f_U2` (`0.87`) are L-sensitive.

**Note.** Bounding `U_1` is TARGET_EQUIVALENT to bounding `M`, with exact two-way transfer: the class aggregate `t = 1 mod 3` carries exactly the zeta information. Bounding the individual buckets in that class does not, because absolute values destroy the `chi_-3` cancellation.

## H. Placement of the competing zeta-side routes

- **MU-LIFT / full K1/K2/K3** (2026-10-16 `analytic-1`).
  - `M(X) = 2M(N) + K1 - K2 + K3` lives in Möbius coordinates and has no `L`-content, so H-L does not apply to it.
  - However, `analytic-3` already shows that every fixed nontrivial `(r, g)` gain is a quasi-RH statement for `zeta` alone. That is target strength for a zero-free strip; it is not weaker.
  - The analogous hyperbola for `a6 = mu * (chi mu)` mixes `mu` with `chi mu`, so it inherits the H-L sensitivity.
- **SB-7/8 square-shell energy** (`HEURISTIC`).
  - SB-7/8 is zeta-only.
  - Under the explicit-formula zero model, zeros of real part `sigma` and count `N(sigma, T) ≈ T^c` contribute `≈ H^(4 sigma - 1 + c)` to `sum_(H<=r<2H) delta_r^2`.
  - The bound `H^(5/2+eps)` therefore needs `c <= 7/2 - 4 sigma` for every `sigma in (3/4, 7/8]`. This is a zero-density requirement stronger than the density hypothesis in that range.
  - So SB-7/8 is, in this model, *stronger* than the 7/8 zero-free strip. This agrees with the repository's "stronger in general" label and quantifies it.
- **Closing the H-L window** would make `V_low` exactly as strong as the ζ·L(s,χ₋₃) strip.
  - The window would close if, for example, `sum_(t<=sqrt X) |C6(X/t) - 2 C6(X/(t+1)) + C6(X/(t+2))| << X^(Theta_K + eps)`, a second-difference smoothness bound along the reciprocal lattice.
  - The known explicit-formula tools do not give this without growth or `zeta_K'`-type assumptions. It is OPEN even under GRH.

## I. Hypotheses used

| Input | Where it is used |
|---|---|
| Hardy's theorem (zeros of `zeta` on the critical line) | Claims `-1`, `-4` and `-owner-3` |
| Saias–Weingartner (2009) and the Hardy-type theorem for Dirichlet L | Claim `-4` |
| Classical zero-free region for ζ·L(s,χ₋₃) | Claim `-5` |
| Littlewood–Landau zero-free ⇒ summatory bound | Claim `-2` upper bound |

There is no RH or GRH assumption anywhere except where a claim says so explicitly.

## J. Unresolved obligations and handoffs

- **Missing inequality for the variation route as an independent 7/8 input:** `V_low(X) = O_eps(X^(7/8+eps))`. By Claim `-2` it lies at quasi-GRH strength for ζ·L(s,χ₋₃). It is OPEN and is **not** an easier intermediate.
- **Referee:** audit Claim `-2` (the Littlewood–Landau step for `zeta L`), the case analysis in Claim `-4`, and the SB-7/8 heuristic's model assumptions.
- **Lean:** Claim `-1` (i) is compiled on #967. The general functional identity of Claim `-3` and the `U_1` identity are finite exact identities, suitable for a later nonduplicate module. The analytic parts need Mellin/Perron infrastructure.
- `VFCanonicalSquareVonKochStatement` remains OPEN. There is no RH claim.

## K. Resume capsule

Reuse:

- H-L (`-1`) and the window `Theta_K <= lambda_V <= 1/(2 - Theta_K)` (`-2`);
- the return classification (`-3`) and the periodic-kernel no-escape result (`-4`);
- the PNT-strength `V_low` bound (`-5`) and the `U_1` identity (`-6`).

Do not:

- present `V_low`, any signed low return, or any bounded-primitive periodic-kernel variation as an input independent of zero-free regions;
- treat finite `V/sqrt X` ratios as exponent evidence.

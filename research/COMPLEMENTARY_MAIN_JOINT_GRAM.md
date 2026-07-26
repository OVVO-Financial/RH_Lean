# Complementary main term and joint-Gram architecture

Diagnostic note on the complementary main term `Main_F = L + Ĥ^F` of the
corrected square-prefix decomposition, and the block architecture it suggests.
Every claim is classified **exact identity**, **reproduced (this harness)**,
**reported (collaborator)**, or **open**. Reproductions use
[`../scripts/ComplementaryMainGram/`](../scripts/ComplementaryMainGram/README.md).

## 0. Architecture

The square-prefix process is (handoff §3)

```text
S  =  Main_F  +  (H - Ĥ^F) ,        Main_F = L + Ĥ^F ,
```

the complementary main plus the signed prime-discrepancy residual. Here `L` is
the born-smooth component, `H` the signed high (transport) prime process, and
`Ĥ^F` its baseline transport. The residual `H - Ĥ^F = -R_F` is the object the
dyadic pairing note decomposes.

## 1. Exact identity

With the odd-cofactor definitions (script header), `L := S − H`, so

```text
Main_F − R_F,odd  =  S ,     R_F,odd := Ĥ^F − H ,           (odd cofactor)
```

closes **exactly** (max error `0`, all tested windows). This is the concrete
`S = Main + residual` split.

## 2. The decisive cancellation is inside the main term — REPRODUCED

The collaborator's central finding is independently reproduced (this harness,
two scales, li-type baseline): the two pieces of `Main_F` almost annihilate.

| quantity | N=900 | N=1200 | collaborator (N=2800, Li) |
|---|---|---|---|
| survival `|L+Ĥ^F|²/(|L|²+|Ĥ^F|²)` | 0.0100% | 0.0062% | 0.0037% |
| raw `cos(L, Ĥ^F)` | −0.99998 | −0.99998 | −0.99997 |
| `α_orth(L on −Ĥ^F)` | 0.9878 | 0.9903 | 0.9970 |

`|L|²` and `|Ĥ^F|²` are each `~10¹¹–10¹²` while `|L+Ĥ^F|²` is `~10⁶–10⁷`. The
born-smooth `L` and the baseline transport `Ĥ^F` are anti-parallel to better than
`10⁻⁴` in cosine, and `α_orth → 1` as `N` grows (the theorem coefficient `1` is
asymptotically the true orthogonal coefficient). **The strongest nearly
orthogonal structure lives inside `L + Ĥ^F`, not between `Main` and the
residual.**

By contrast, projecting `Main` onto `R_F,odd` gives `α ≈ −0.05` (this harness),
far from `1`: `Main − R_F` is **not** near-projection-like. So the theorem's
`Main − R_F` subtraction and the true orthogonal residual are genuinely separate
objects — as the repository's orthogonal-residual formalization insists.

The empirical quantities here are exactly the finite instances of the merged
`RHLean/Proof/NearOrthogonality.lean` (PR #103) API: `α_orth` is
`orthogonalCoefficient P B` (with `P = −Ĥ^F`, `B = L`); the gap `1 − α_orth` is
`orthogonalCoefficient − 1 = projectionDefect 1 / ⟪P,P⟫`
(`orthogonalCoefficient_sub_predicted_eq_projectionDefect_div`); and the energy
excess of coefficient `1` over the orthogonal minimum is
`theoremPredictedResidual_energy_eq_orthogonal_add_projectionDefect`.

## 3. The residual pairing block — REPRODUCED

For the pairing pieces `K, J, T` (constant-mode / centered / tail,
`DYADIC_MOBIUS_SIGNED_RESIDUAL.md`), the residual-side Gram is dominated by one
negative cross term:

| quantity | N=900 | N=1200 |
|---|---|---|
| `2⟨K,J⟩ / |K+J+T|²` | −2.67 | −8.01 |
| `corr(K,J)` | −0.82 | −0.95 |
| `2⟨K,T⟩`, `2⟨J,T⟩` | `~10⁵` (negligible) | `~10⁶` (negligible) |

`2⟨K,J⟩` is several times the whole residual energy and negative; `K/T` and
`J/T` are orders of magnitude smaller. **`K` and `J` must be kept in one block**
— separate estimates would discard the dominant cancellation (consistent with
the pairing note's split (N)).

## 4. Two gaps found while reproducing — OPEN

Independent reconstruction confirmed the *structure* but surfaced two concrete
gaps that need the collaborator's exact definitions to close:

1. **Amplitude (~2×).** This harness gives `|L|² ≈ 4.7×` the collaborator's at
   `N=2800`. The finer coefficients (survival %, `α_orth`, projection ratios)
   are sensitive to the exact born-smooth/high split and to the baseline (li
   trapezoid here vs `Li`). The qualitative conclusions are stable; the digits
   are not comparable without a common definition.

2. **Cofactor convention.** The physical residual `R_F,odd = Ĥ^F − H` is
   **odd-cofactor** (the source `m = cq` has odd `c`), and `S = Main − R_F,odd`
   closes exactly. But the dyadic pairing `K + J + T` is the **all-cofactor**
   reorganization (it folds even `2c` onto odd `c` via `μ(2c) = −μ(c)`), so
   `R_F,pair = K+J+T` differs from `R_F,odd` by the even-cofactor terms —
   numerically `|R_F,pair − R_F,odd|² / |R_F,odd|² ≈ 0.27–0.50`. A unified
   five-component `[L, Ĥ^F, −K, −J, −T]` closure therefore needs the residual /
   pairing cofactor convention pinned down. **This also bears on the pairing
   note**, whose `R_F` was the all-cofactor object; if the physical residual is
   odd-only, the pairing must be re-derived on the odd-cofactor basis.

## 5. Recommended block architecture — from the reproduced structure

1. **Block I — `L + Ĥ^F` (near-projection).** Prove a quantitative
   near-projection theorem: the true orthogonal coefficient of `L` on `−Ĥ^F`
   tends to `1`, with a controlled energy excess for coefficient `1`. This is
   where the largest internal mode is almost annihilated by the theorem's
   recombination, so it is a Gram-to-orthogonal-residual bridge, not a coarse
   main-vs-residual split. The exact finite algebra for this bridge now lives in
   `RHLean/Proof/NearOrthogonality.lean` (PR #103): `projectionDefect`,
   `orthogonalCoefficient`, the coefficient-gap identity, and the excess-energy
   decomposition. The open analytic step is the asymptotic
   `orthogonalCoefficient(L, −Ĥ^F) → 1` with a quantitative rate.
2. **Block II — `K + J` (joint).** Keep the large negative `2⟨K,J⟩`; never bound
   the constant-mode and centered pieces separately.
3. **Block III — compressed `Main` + compressed paired residual + tail `T`** in a
   small block-Gram, once Blocks I–II are compressed.
4. **Exact energy-excess identity** comparing coefficient `1` with the true
   orthogonal coefficient — **now formalized** in
   `RHLean/Proof/NearOrthogonality.lean`
   (`theoremPredictedResidual_energy_eq_orthogonal_add_projectionDefect`); apply
   it with `P = −Ĥ^F`, `B = L`, `betaPred = 1`.
5. Directional partial-moment matrices are for **attribution only**: they recover
   centered covariance/PCA exactly, but individual Rayleigh contributions can
   dwarf the final eigenvalue and cancel heavily.

## 6. Next experiment — OPEN

One window / one baseline is not enough. Grid over `N`, `H/N`, and baseline,
tracking: `1 − α_orth`, the normalized `L/Ĥ^F` Gram determinant, the `K/J`
survival ratio, and the eigenmode overlap with the final recombination vector.
The `--N` / `--hratio` switches provide the scaffold; the amplitude and
convention gaps above must be reconciled first for cross-run digit comparison.

---

**Strategic conclusion (reproduced).** The strongest nearly orthogonal structure
is inside `L + Ĥ^F`, not between `Main` and the residual — so the complementary
main must be treated as a joint (near-projection) object, and `K + J` as a second
joint block, rather than by bounding pieces separately.

# Dyadic Moebius pairing of the signed exact-activity residual

Reproducible companion to
[`../../research/DYADIC_MOBIUS_SIGNED_RESIDUAL.md`](../../research/DYADIC_MOBIUS_SIGNED_RESIDUAL.md).

## Object

For an integer `t >= 1`, write `S = (t+1)^2` and `X = S - 1 = t*(t+2)`. The exact
active-prime interval of a cofactor `c` has endpoints

```text
L(t,c) = max(t+2, ceil(S/(2c)))
U(t,c) = floor(X/c).
```

For a smooth cumulative baseline `F`, set `E = pi - F`. The signed
exact-activity residual is

```text
R_F(t) = sum_{c <= t, squarefree} mu(c) * ( E(U(t,c)) - E(L(t,c)-1) ).
```

## What the script verifies

1. **Exact endpoint identities** (independent of `E`):
   * reciprocal endpoint `ceil(S/(2c)) - 1 == floor((S-1)/(2c)) == U(t,2c)`;
   * lower-endpoint form `L(t,c) - 1 == max(t+1, U(t,2c))`;
   * regime threshold `U(t,2c) >= t+1  <==>  2c <= t`;
   * non-emptiness `L(t,c) <= U(t,c)  <==>  c <= t`.

2. **Exact three-region decomposition** of `R_F(t)` obtained by pairing each odd
   `c` with `2c` via `mu(2c) = -mu(c)`. Verified against the direct sum with a
   *random* real function in place of `E`, proving it is a Moebius/endpoint
   identity with no arithmetic input:

   ```text
   R_F(t) = sum_{odd c <= t/4}       mu(c)[E(U_c) - 2E(U_2c) + E(U_4c)]   (I)
          + sum_{odd t/4<c<=t/2}     mu(c)[E(U_c) - 2E(U_2c) + E(t+1) ]   (II)
          + sum_{odd t/2<c<=t}       mu(c)[E(U_c) -   E(t+1)          ]   (III)
   ```

3. **Principal-endpoint coefficient identity** (exact integer arithmetic): the
   coefficient of `E(t+1)` in `R_F(t)` equals
   `M_odd(t/4, t/2] - M_odd(t/2, t]`, a difference of short odd-Moebius sums.

4. **Exact low-Mertens forms (F) and (G)** (Fubini swap of the `c`- and prime
   sums), checked against the direct band sums with a random `E`:
   * `(F)  R_F(t;C) = sum_{n>=t+2} e_F(n)[M(B_n) - M(A_n-1)]`;
   * `(G)  P_F(t;C) = sum_n e_F(n)( M_odd on [S/2n,S/n] - M_odd on [S/4n,S/2n] )`.

5. **Nonzero zero-frequency shell mass**: `|I(t,c)| - |I(t,2c)| ~ S/(4c) > 0`,
   confirming the raw dyadic pair is **not** a mean-zero wavelet (the two shells
   have unequal length), so pairing does not annihilate the principal frequency.

6. **Finite magnitude diagnostics** for regions I, II, III using the genuine
   prime error `E = pi - F`, `F(y) = sum_{2<=n<=y} 1/log n`.

## Run

```bash
python dyadic_mobius_signed_residual.py \
  --output dyadic_mobius_signed_residual_summary.json
```

Quick smoke test:

```bash
python dyadic_mobius_signed_residual.py \
  --identity-tmax 200 --decomp-tmax 300 --centers 1500 --span 20
```

No third-party dependencies (standard library only).

## Classification

- **exact**: all endpoint identities, the regime thresholds, parent/child
  adjacency, the three-region decomposition, the principal-endpoint coefficient,
  the low-Mertens forms (F)/(G), and the nonzero zero-frequency shell mass;
- **finite evidence**: the region RMS magnitudes at the tested scales;
- **open**: every uniform mean-square bound. In particular the first genuine
  analytic step is the constant-mode/baseline lemma for the paired block (no
  Fourier variable is present in (F)/(G) yet); and the unpaired balanced tail
  (region III) is of RH strength.

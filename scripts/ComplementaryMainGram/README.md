# Complementary main term and joint-Gram diagnostics

Reproducible companion to
[`../../research/COMPLEMENTARY_MAIN_JOINT_GRAM.md`](../../research/COMPLEMENTARY_MAIN_JOINT_GRAM.md).

## Architecture

The square-prefix process splits as

```text
S = Main_F + (H - Hhat_F),     Main_F = L + Hhat_F,
```

the complementary main term plus the signed prime-discrepancy residual.

## Definitions (this harness, odd-cofactor)

For height `t`, `S=(t+1)^2`, exact endpoints `L(t,c)=max(t+2,ceil(S/2c))`,
`U(t,c)=floor((S-1)/c)`, baseline `F`, `E=pi-F`:

```text
H[t]      = sum_{c<=t, odd} -mu(c)(pi(U)-pi(L-1))
Hhat_F[t] = sum_{c<=t, odd} -mu(c)(F(U)-F(L-1))
S[t]      = M_odd((t+1)^2-1) - M_odd(ceil((t+1)^2/2)-1)
L[t]      = S[t] - H[t]           (born-smooth)
RF_odd[t] = Hhat_F[t] - H[t] = Main[t] - S[t]   (physical residual; closes exactly)
```

## What it reports

1. **Exact** odd-cofactor closure `S = Main - RF_odd` (max err 0).
2. **Complementary-main cancellation**: `|L+Hhat_F|^2 / (|L|^2+|Hhat_F|^2)`
   (survival), `cos(L,Hhat_F)`, and the near-projection coefficient
   `alpha_orth(L on -Hhat_F)` versus the theorem coefficient `1`.
3. **Main - RF_odd** projection, showing it is *not* near-projection.
4. **Residual pairing Gram** (K, J, T from the pairing note): the dominant
   negative cross term `2<K,J>` and the negligible `K/T`, `J/T`.
5. **Convention gap** `|RF_pair - RF_odd|^2 / |RF_odd|^2`: the pairing residual
   `RF_pair = K+J+T` is the *all-cofactor* reorganization and differs from the
   *odd-cofactor* physical residual `RF_odd`.

## Run

```bash
python complementary_main_gram.py --N 900 1200 --hratio 0.2 \
  --output complementary_main_gram_summary.json
```

No third-party dependencies (standard library only). Runtime grows with
`((1+hratio)N)^2` (array size); `N<=1500` is quick, larger `N` needs more time.

## Classification

- **exact**: the odd-cofactor closure `S = Main - RF_odd`;
- **reproduced qualitatively** (this harness, two scales): near-total
  `L+Hhat_F` cancellation (survival `<0.01%`, `cos<-0.9999`), `L+Hhat_F`
  near-projection vs `Main-RF_odd` not, dominant negative `2<K,J>`;
- **reported by collaborator** (Li baseline, `N=2800,H=640`): exact digits
  (survival 0.0037%, cosine -0.99997, α 0.997) — amplitudes differ ~2x here,
  i.e. the finer coefficients are definition/baseline/scale sensitive;
- **open**: reconciling the odd-cofactor physical residual with the all-cofactor
  pairing decomposition; the exact born-smooth definition; a grid over
  `(N, H/N, baseline)`.

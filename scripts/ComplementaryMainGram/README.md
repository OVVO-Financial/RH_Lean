# Complementary main term and joint-Gram diagnostics

Reproducible companion to
[`../../research/COMPLEMENTARY_MAIN_JOINT_GRAM.md`](../../research/COMPLEMENTARY_MAIN_JOINT_GRAM.md).

## Architecture

The square-prefix process splits as

```text
S = Main_F + (H - Hhat_F),     Main_F = L + Hhat_F,
```

the complementary main term plus the signed prime-discrepancy residual.

## Definitions (this harness, all-cofactor)

For height `t`, `S=(t+1)^2`, exact endpoints `L(t,c)=max(t+2,ceil(S/2c))`,
`U(t,c)=floor((S-1)/c)`, baseline `F`, `E=pi-F`:

```text
H[t]      = sum_{c<=t, all sqfree} -mu(c)(pi(U)-pi(L-1))
Hhat_F[t] = sum_{c<=t, all sqfree} -mu(c)(F(U)-F(L-1))
S[t]      = M_odd((t+1)^2-1) - M_odd(ceil((t+1)^2/2)-1)
L[t]      = S[t] - H[t]           (born-smooth)
RF[t]     = Hhat_F[t] - H[t] = Main[t] - S[t] = K + J + T   (residual)
```

`H, Hhat_F` run over all squarefree cofactors, so `RF` is a single object: the
physical residual `Hhat_F - H` and the dyadic-pairing residual `K + J + T`
coincide (no cofactor-convention gap).

## What it reports

1. **Exact closures**: `S = Main - RF` (max err 0) and `RF = K + J + T`
   (max err `~1e-11`).
2. **Complementary-main cancellation**: `|L+Hhat_F|^2 / (|L|^2+|Hhat_F|^2)`
   (survival), `cos(L,Hhat_F)`, and the near-projection coefficient
   `alpha_orth(L on -Hhat_F)` versus the theorem coefficient `1`.
3. **Main - RF** projection, showing it is *not* near-projection.
4. **Residual pairing Gram** (K, J, T from the pairing note): the dominant
   negative cross term `2<K,J>` and the negligible `K/T`, `J/T`.

## Run

```bash
python complementary_main_gram.py --N 900 1200 --hratio 0.2 \
  --output complementary_main_gram_summary.json
```

No third-party dependencies (standard library only). Runtime grows with
`((1+hratio)N)^2` (array size); `N<=1500` is quick, larger `N` needs more time.

## Classification

- **exact**: the closures `S = Main - RF` and `RF = K + J + T`;
- **reproduced** (this harness, two scales): near-total `L+Hhat_F` cancellation
  (survival `<0.03%`, `cos<-0.9998`), `alpha_orth(L,-Hhat) -> 1`, `L+Hhat_F`
  near-projection vs `Main-RF` not, dominant negative `2<K,J>`; with the
  all-cofactor convention the digits agree with the collaborator's `Li` run
  (`N=2800,H=640`: α 0.997, survival 0.0037%) to a few percent;
- **open**: a quantitative rate for `alpha_orth(L,-Hhat) -> 1`; baseline
  sensitivity of the finest digits (`li` trapezoid vs `Li`); a grid over
  `(N, H/N, baseline)`.

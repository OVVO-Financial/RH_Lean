# The exact 7/8 signed-covariance target and the 317/1027 square-shell route

**2026-10-19, PR #984. Scope:** genuine integer Mobius function and the
existing RH_Lean signed Green--Kubo pair carrier; no fake probabilistic
independence, OAI theorem import, or claimed independent 7/8 proof.

## A. Exact ALL-X bound (equivalent to the OpenAI 7/8 zeta conclusion)

Let
```text
U_X = sum_(n<=X) max(mu(n),0)       [NNS zero-target UPM1]
L_X = sum_(n<=X) max(-mu(n),0)      [NNS zero-target LPM1]
K_X = U_X+L_X = sum_(n<=X) mu(n)^2
M_X = U_X-L_X
C_X = sum_(1<=i<j<=X) mu(i)*mu(j)
```

At every X, exactly (not on average),

```text
M_X^2 = K_X+2*C_X
4*U_X*L_X = K_X^2-M_X^2
C_X = (K_X^2-4*U_X*L_X-K_X)/2.
```

The complete seven-eighths covariance target is

```text
forall eps>0 exists A_eps>=0 forall X>=1:
   2*C_X <= A_eps^2*X^(7/4+2eps)-K_X.
```

This is equivalent to `MertensGrowthAtMost (7/8)`, and through the
ALREADY proved native Mertens converse, to confinement of nontrivial zeta
zeros in [1/8,7/8]. Equivalently the UPM/LPM simultaneous-occurrence
budget is

```text
U_X*L_X >= (K_X^2-A_eps^2*X^(7/4+2eps))/4.
```

These are SIGNED pair bounds, not absolute pair bounds; constants are
allowed to depend on epsilon. The exponent is (7/4) for the **square**
and (7/8) for the **Mertens amplitude**. A bare claim that a normalized
pair correlation is "-1/4" is mathematically incorrect.

The Lean module
`research/VF_919_SEVEN_EIGHTHS_SIGNED_COVARIANCE_20261019.lean`
contains exact signed Gram, covariance iff exponent, exponent iff strip,
and a source-explicit consumer of an externally supplied seven-eighths
zeta nonvanishing theorem. The terminal consumer's `hz` input must
NOT be hidden, erased, or assumed to be supplied by the module.

## B. A sufficient mechanism localized to the canonical square shells

For R>=1 set
```text
S_R = sum_(R^2 <= n < (R+1)^2) mu(n)
    = M((R+1)^2-1)-M(R^2-1).
```

Each complete square shell has exactly (2R+1) physical sites, with
the SAME fixed floor-sqrt factor set; at most one prime factor exceeds R.

A stronger but concrete **sufficient** condition is

```text
forall eps>0 exists B_eps>=0 forall R>=1:
    |S_R| <= B_eps * R^(3/4+eps).
```

**Proof of sufficiency (no probabilistic model):** telescope all genuine
shells to `M(R^2-1)`. The triangle inequality and monotonicity yield

```text
|M(R^2-1)| <= B_eps sum_(1<=r<R) r^(3/4+eps)
            <= B_eps R^(7/4+eps).
```

For arbitrary X in [R^2,(R+1)^2), the remaining incomplete shell has at
most (2R+1) sites of magnitude at most one. Hence
`|M(X)|<= B_eps R^(7/4+eps)+2R+1`, which is
`O_eps(X^(7/8+eps/2))`. Choosing a smaller shell epsilon establishes the
arbitrary-loss 7/8 global Mertens bound and the full signed covariance
budget A. This shell estimate is **NOT implied** by a 7/8 global Mertens
bound; it is a stronger *candidate proof mechanism* requiring its own
arithmetic justification.

The precise local NNS covariance acceptance is

```text
S_R^2 = K_R(shell) + 2*C_R(shell)
      <= B_eps^2 * R^(3/2+2eps).
```

Relative to the trivial (O(R)) shell amplitude this asks for a
**quarter-power saving** on the amplitude: (R^{3/4}) instead of (R).

## C. Exact finite Möbius measurements (not uniform estimates)

Reproduced by `scripts/vf919_seven_eighths_signed_covariance_census.py`.

| Source | UPM1 | LPM1 | K | M or shell S | Signed pair C |
|---|---:|---:|---:|---:|---:|
| X=317 complete prefix | 95 | 99 | 194 | -4 | -89 |
| X=1027 complete prefix | 311 | 314 | 625 | -3 | -308 |
| R=317 square shell | 199 | 188 | 387 | +11 | -133 |
| R=1027 square shell | 616 | 636 | 1252 | -20 | -426 |

For R=317 the local squared energy is 121 against the absolute diagonal
387. For R=1027 it is 400 against 1252. In both cases mixed signed
covariance is negative, unlike a diagonal-only estimate.

At R=317 the shell amplitude normalized by the proposed (R^{3/4})
bound is ~0.14642; at R=1027 it is ~0.11024. The script checks the exact
integer identity `M(X)^8 <= X^7` for every
`1<=X<=1028^2-1`, but this finite check provides NO all-scale proof
or universal constant.

## D. The precise OpenAI comparison, and the unproved source weld

OpenAI's nonprincipal Hecke prime-slot estimate is
```text
||normalizedSlot(P)||^2 <= C(1+|t|)^J Z^loss P^kappa,
kappa >= 2*beta_star-1.
```
At the 7/8 boundary, `kappa = 3/4`. On the *hypothetical* geometric
scale (Pasymp R^2), the right side (P^{3/4}) has the same (R^{3/2})
exponent as the sufficient native square-shell energy above.

**This matching exponent is NOT an identification of the two energies.**
OpenAI's `normalizedSlot` is a smooth variable-conductor Eisenstein
ideal PRIME polynomial; the native `S_R` is a sharp integer Mobius shell
with all small-prime and high-prime owners. The physical source incidence,
volume normalization, `chi_{-3}*a_F` inverse-ideal-to-integer
reassembly, sextic phases, ramified masks and cutoff/smoothing errors
must all be proved before any OAI moment inequality can be used on S_R.

The 317/1027 sextic phase witnesses independently certify that two
distinct ideal labels with equal rational norm may have different
character phases. Project to the integer owner **only after** the full
character-twisted Hermitian moment is estimated.

**Next mathematical target:** establish a genuine all-R signed shell
moment bound or the weaker (but exactly equivalent) all-X signed
covariance bound. Finite Gauss orthogonality, NNS UPM/LPM reassembly,
and `S=A-T` identities alone do not establish either power saving.

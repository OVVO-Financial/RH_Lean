# A Machine-Checked Death-Process Reduction for Square-Prefix Möbius Sums

## Status

This note records an exact formal reduction now verified in Lean in
`OVVO-Financial/RH_Lean`. It does **not** claim a proof of the Riemann
Hypothesis. It isolates a new arithmetic process and proves that a pair of
RH-scale local-energy estimates for that process and its discrepancy implies
the repository's protected square-prefix criterion and, through the existing
classical Mertens criterion, RH.

## Canonical geometry

For an integer `m`, let

- `q_m = P⁺(m)` be its largest prime factor, with the repository's harmless
  conventions at `m = 0,1`;
- `c_m = m / q_m` be the canonical cofactor;
- `2Y_m = q_m² - c_m²` be the doubled canonical height.

The height has the exact factorization

```text
2Y_m = q_m² - c_m² = (q_m - c_m)(q_m + c_m).
```

For a fixed cutoff parameter `Λ ≥ 0`, the moving high condition at stage `t` is

```text
2 Λ t < |2Y_m|.
```

A source leaves the moving high population between stages `t` and `t+1`
exactly when

```text
2 Λ t < |2Y_m| ≤ 2 Λ (t+1).
```

This is the thin death shell at stage `t`.

## Birth, survivor, and death processes

The formalization defines three exact sequences:

```text
B_t = birth-ordered canonical high mass,
A_t = lifetime-active survivor mass,
D_t = absorbed, or death-ordered, mass.
```

Lean proves pointwise that

```text
B_t = A_t + D_t,
A_t = B_t - D_t.
```

It also proves that `B_t` is exactly the repository's existing
`canonicalHighPrefix` and that the translated-window energy of `A_t` is the
energy of the discrepancy `B_t - D_t`.

## Exact shell identity

Define the discrete death increment

```text
ΔD_t = D_{t+1} - D_t.
```

The merged formalization proves, for `Λ ≥ 0`,

```text
ΔD_t = deathHeightShellMass Λ t.
```

Equivalently,

```text
ΔD_t = Σ μ(m),
```

where the sum is over the square-prefix sources crossing the moving boundary
in the shell

```text
2 Λ t < |P⁺(m)² - (m/P⁺(m))²| ≤ 2 Λ (t+1).
```

The proof is not definitional. It establishes that:

1. moving-high membership at a later stage implies birth-high membership in
   every earlier birth block when `Λ ≥ 0`;
2. the lifetime-active atom mass equals the cumulative moving-high sum;
3. the moving entry mass is exactly the high contribution of the newly born
   square block;
4. the birth recurrence and moving recurrence therefore cancel their common
   entry term, leaving precisely the crossing-shell mass as `ΔD_t`.

Lean also proves the telescoping reconstruction

```text
D_n = D_0 + Σ_{t<n} ΔD_t.
```

Thus the death process is an exact cumulative Möbius sum over thin,
factorized `2ab` shells.

## Conditional RH route

The formalized endpoint criterion consists of two translated-window estimates:

```text
Σ_{h<H} |B_{N+h} - D_{N+h}|² ≪_{ε,Λ} H N^{2+ε},
Σ_{h<H} |D_{N+h}|²             ≪_{ε,Λ} H N^{2+ε},
```

uniformly for `1 ≤ H ≤ N`.

Lean proves that their conjunction implies the protected square-prefix
uniform-local criterion. Given the repository's existing classical
Mertens-energy criterion, it then implies RH.

A bound on `D_t` alone is not sufficient: one must also control the survivor
discrepancy `B_t-D_t`, or provide an equivalent pair of RH-scale estimates.

## Arithmetic problem exposed

Writing

```text
u = q_m - c_m,
v = q_m + c_m,
```

gives

```text
uv = q_m² - c_m²,
q_m = (u+v)/2,
c_m = (v-u)/2.
```

The shell restriction is therefore a thin hyperbolic region

```text
2 Λ t < |uv| ≤ 2 Λ (t+1),
```

with parity, primality, largest-prime-factor, square-prefix, and Möbius
constraints inherited from `m = q_m c_m`.

This suggests several analytic directions:

- mean-square estimates for shell masses `ΔD_t`;
- dispersion or large-sieve bounds after decomposing the `q,c` variables;
- Type I/Type II decompositions of the Möbius weight;
- spectral analysis of the associated hyperbolic incidence operator;
- separation of shell bias from shell variance;
- unconditional bounds weaker than the RH scale, as intermediate results.

## Initial numerical observation

A reproducible exploratory script and scaling table accompany this note. In a
first calculation through `T = 2000`:

- the death shells were sparse;
- for `Λ = 1`, the maximum shell cardinality was `10`;
- the RMS shell Möbius mass was approximately `1.09`;
- the cumulative process showed a substantial negative drift over this finite
  range.

These observations are empirical only. In particular, the small shell masses
do not by themselves control cumulative local energy if a persistent bias is
present.

## Formal source files

The exact chain is implemented in:

- `RHLean/Proof/LifetimeOverlapKernel.lean`;
- `RHLean/Proof/LifetimeActiveSet.lean`;
- `RHLean/Proof/LifetimeLocalEnergyCriterion.lean`;
- `RHLean/Proof/LifetimeEndpointDecomposition.lean`;
- `RHLean/Proof/DeathProcessArithmetic.lean`;
- `RHLean/Proof/DeathProcessShellIdentity.lean`.

All merged modules pass the repository's paper/Analysis boundary check,
unfinished-proof and axiom audit, and full `lake build RHLean --wfail` build.

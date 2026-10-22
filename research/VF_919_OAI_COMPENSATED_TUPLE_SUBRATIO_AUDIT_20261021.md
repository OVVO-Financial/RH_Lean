# PR #1002: compensated-tuple subratios — exact source audit, not an assumed pointwise cancellation

Date: 2026-10-21. Stack: #1000 -> #1001 -> #1002.
Code: `VF_919_OAI_COMPENSATED_TUPLE_SUBRATIO_AUDIT_20261021.lean`.

## Original authority

- [OpenAI Compensation.lean](https://github.com/openai/math/blob/main/lean/OAI/NumberTheory/DirichletL/Detector/Compensation.lean), `tupleOperation` and `tupleOperation_one`.
- [OpenAI Physical.lean](https://github.com/openai/math/blob/main/lean/OAI/NumberTheory/DirichletL/Detector/Physical.lean), `markedPhysicalProbe` and `compensatedTuple_one`.
- [OpenAI Row.lean](https://github.com/openai/math/blob/main/lean/OAI/NumberTheory/DirichletL/Detector/Row.lean), `rowCoefficient` and `spectralRow`.
- [OpenAI Completed.lean](https://github.com/openai/math/blob/main/lean/OAI/NumberTheory/DirichletL/Detector/Completed.lean), `completedMask`.
- [OpenAI Local.lean](https://github.com/openai/math/blob/main/lean/OAI/NumberTheory/DirichletL/Detector/Local.lean), `normalized_cancellation`.
- RH_Lean #1001's conditional one-slot scalar model, phase-defect counterexample, and lossless four-sector split.

For one selected prime element `p` and its ACTUAL norm `q=elementNorm p` the original identity is:

```text
compensatedTuple_one =
  star (elementCoeff eta p)
    * markedPhysicalProbe eta C (Ideal.span {p}) W0 W1 X Y (Z*q)
  - q^(-3/2) * physicalProbe eta C W0 W1 (X/q) (Y/q) Z.
```

The power `-3/2` is *defined* in `tupleOperation`, before unfolding either physical probe. The algebraic fact `q^(-3/2)*(q*sqrt q)=1` does **not** prove the original probes supply the hypothesized independent `q` and `sqrt q` factors.

## What the actual source does under the candidate same-m pairing

Write `s=p*b`, `q=Np>0`, `n=Nb>0`, `c=N(C.generator)>0`, `h=N(m)`.

| OAI factor | Marked at s=p*b | Rescaled physical at s=b | Fact |
|---|---|---|---|
| W1 argument | `q*n/Y` | `n/(Y/q)` | **Equal**, for q and Y nonzero |
| W0 argument | `h/(c*q*n*X)` | `h/(c*n*(X/q))` | **Rescaled = q^2 * marked** at fixed m |
| Spectral mark | `D=(p)` | `D=1` | Marked requires `D | I*J^3`; unmarked does not |
| Vertical integrand | `(Z*q)^t` | `Z^t` | Ratio `q^t` at matching t, not identically one |
| Gauss factor | `sexticGauss(primaryGenerator(s),-m)` | `sexticGauss(primaryGenerator(b),-m)` | Needs an actual twisted-multiplicativity/Poisson change-of-index theorem |
| Hecke factor | Outer `star(elementCoeff eta p)`, plus row coefficient | Row coefficient at a different s | Multiplicativity of an isolated character does not identify these completed spectral rows |

The `W0` result is a **proof obligation / obstruction to the suggested naive same-m pairing**, not a claim that no more sophisticated Poisson reindexing of the inner index `m` could restore equality. Such a map must be constructed and proved, including its domain, mask, Gauss phase, and weight Jacobian.

In particular, the synthetic kernel
`K((Np*Nb)/X,(Np*Nb)/Y,X/(Z*Np))`
is invariant under the stated scaling; the full `markedPhysicalProbe` is not syntactically such a kernel. Its actual `W0` uses `Ns*X` in the denominator. A theorem about the synthetic K cannot be applied to the original Mellin integral without a source-preserving equality.

## Four subratios, correctly scoped

Use ratios `a=gamma_norm, b=gamma_Hecke, c=gamma_Gauss, d=gamma_Mellin` only after verifying denominators nonzero and identifying genuine original labelled source atoms. The unconditional algebra is

```text
1 - a*b*c*d
 = (1-a) + a*(1-b) + a*b*(1-c) + a*b*c*(1-d).
```

If, and only if, `a=b=d=1` are independently proved, the defect becomes `1-c`. The Lean theorem retains these three hypotheses.

- **Normalizer**: the abstract `q^(-3/2)` algebra is proved; `gamma_norm=1` for the original probe has not been established.
- **Hecke**: `conj(e_p)*e_p=1` is valid when the character value is unit modulus. In upstream `HeckeFamily.Character`, `elementCoeff` is a finite quotient character; the vertical Mellin parameter is *separate*, not automatically absorbed into `elementCoeff eta p`. The `D`-marked spectral row remains.
- **Mellin**: a restricted synthetic three-ratio kernel is invariant, but the original `W0` arguments have the exact `q^2` shear at same m, and the vertical factor has an extra `q^t`.
- **Gauss / masks**: the original `sexticGauss(a,-m)` is not an everywhere-primitive, everywhere-nonzero normalized Gauss factor. `D`-mask admission can differ even on a numerically norm-coprime `p,b` pairing.

**No verified binary A/B fork yet.** Case A needs complete original coefficient identification (including W0, vertical, D mask and Gauss). Case B needs a *compensated* bilinear estimate: a character large sieve controls the oscillatory `sum w*psi` under its hypotheses, not automatically `sum w*(1-psi)`. For example, `psi=1,-1` has total phase sum zero but total defect sum two. The constant `sum w` must be separately canceled or bounded with the needed power saving.

## Derivative-degree shift (model only)

For any `gamma,w,Lb,Lp : C` the exact log-polynomial identity is

```text
w*Lb^j - gamma*w*(Lb+Lp)^j
 = (1-gamma)*w*Lb^j
   - gamma*w*((Lb+Lp)^j-Lb^j).
```

At j=0 the residual is `(1-gamma)*w`. At j=1 the lower-degree term is `-gamma*w*Lp`; at j=2 it is `-gamma*w*(2*Lb*Lp+Lp^2)`. The j=1,2 reduction is useful **only** after proving the original `P_j` correspond to the same actual indexed source, and after obtaining uniform weighted bounds (the prime logarithm `Lp` is not a universal scalar across the sum). The upstream `compensatedTuple_one` has no such `j` parameter itself.

## Collision support, not l2 energy

If `b=p*b'`, `Nb<=X/Np`, then `Nb'<=X/(Np)^2` is true as a norm support statement. It is **not** an `l2` saving without a labelled-fiber cardinality bound and control of the original coefficient weights. See #1000 for the actual-fiber finite Cauchy bridge.

## Actual next integration target

1. Extract the ORIGINAL `(eta,C,s,m,I,J,t,p,subset)` source indices for both probes, including their W0/W1 arguments, window masks and nonzero domains.
2. Construct an explicitly verified bijection/finite-fiber correspondence, potentially after Poisson reindexing of `m`. Prove the resulting coefficient-level relation as an identity, retaining unmatched faces. This is the missing original-source *gamma* theorem.
3. Determine the exact residual; if a nonprincipal sextic phase survives, exhibit cancellation of the principal `1` contribution before invoking a bilinear large-sieve moment bound.
4. Apply original OAI signed source moments and the #998 NNS Co/Div covariance to the actual residual with uniform row/height/prime-band quantifiers. Do not infer numerical power savings from cardinality alone.

**Acceptance scope:** finite algebra, exact W1 equality, exact W0 `q^2` shear, conditional Gauss-only algebra, counterexample to `sum(1-psi)` cancellation, and norm-support bound. All original-source identity and analytic power-saving claims remain **OPEN**. No RH or improved zero-free exponent is claimed.

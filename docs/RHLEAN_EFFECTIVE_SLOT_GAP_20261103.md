# Effective absolute lower bound for the physical slot minimum

Date: 2026-11-03. Status: proof work in progress; no unverified numeric endpoint may be described as Lean-certified.

## Exact source arithmetic

The pinned OpenAI constructor [ParametersSlotLengths.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/ParametersSlotLengths.lean) uses
```
w_j = 1+j/N; A = sum_{j=0}^{N-1} w_j = (3*N-1)/2;
ell_j = w_j/(6*A) = (N+j)/(3*N*(3*N-1)).
```
Thus the exact minimum is
```
ell_* = 1/(3*(3*N-1)),  delta = ell_*/24 = 1/(72*(3*N-1)).
```

The proof of `exists_distinct_slot_lengths` merely takes `exists_nat_gt` above a lower threshold. An arbitrary witness can be arbitrarily large; **no unconditional positive rational lower bound on ell_* follows from the abstract HighData record or the old existential theorem alone**. A bound on N must be preserved when constructing the chosen source.

For L>0 with L<=1, choose the explicit integer `N=ceil(1/L)+1`, reusing exactly those affine weights. Then N>1/L and N<1/L+2, and the elementary source bounds give

```
0 < ell_j < L,          sum ell_j = 1/6,
ell_j >= L/36,          ell_* >= L/36.
```

The new `research/oai_434/VF919EffectiveSlotPopulation.lean` formalizes this finite-source packet. It is not by itself a HighData supplier and must not be treated as a completed numerical Mertens bound.

## Absolute numerical parameters in the original source

At original auxiliary Delta=1/1000000, the pinned central-budget construction picks

```
t = min(Delta/8, 1/100000000) = 1/100000000,
epsilon_Width = t/4 = 1/400000000,
amplification = epsilon_Width/16000 = 1/6400000000000,
k = ceil(2*2/amplification)+1 = 25600000000001.
```

For the original geometric WidthRanges with M=2, B=0, L=1, its recurrence is

```
range(0) = 1,
range(n+1) = 4*(range(n)+6),
range(k) = 9*4^k-8.
```

Its final source cap and width scale are therefore

```
sourceCap = 10*(range(k)+3) = 90*4^k-50,
scale = k+2+10*sourceCap+30 = 900*4^k+k-468 =: S.
```

Using the actual `mesh = reserve/(kappa+1)`,
`reserve = min(amplification/100, epsilon_Width/(1000000*scale))`,
and `kappa=3/4+2*Delta`, the second branch is smaller. Consequently the
complete detector mesh is exactly the following **positive rational**:

```
detectorMesh(1/1000000,1/100000000)
   = 1/(700000800000000*S),
S = 900*4^25600000000001 + 25600000000001 - 468.
```

This mesh is smaller than t. The original source constructor then demands
`ell_j < L`, where `L=detectorMesh/200`. With the explicit permissible choice

```
N = 200*700000800000000*S + 1
  = 140000160000000000*S + 1,
```

the literal weight family has

```
ell_* = 1/(3*(420000480000000000*S+2))
delta = 1/(72*(420000480000000000*S+2)).
```

That is a **candidate fully explicit rational gap**, with decimal order roughly `10^(-15412735778019)`. As a looser human-readable target one may prove `delta > 10^(-20000000000000)`, but that statement still requires exact Lean proof of the source witness and the inequalities. The enormous size is due to the repeatedly amplified fine-mesh/width schedule, **not** a missing cancellation assumption.

## Formalization requirements (must be satisfied before claiming a new theorem)

1. Kernel-verify the bounded-N affine family with `L/36 <= ell_j < L` and exact normalizer and total mass. Retain every source slot.
2. Rebuild the original `exists_physical_slot_lengths` and `exists_high_data_fine` constructors using this specific bounded-N witness. Preserve their original analytic loss and tail parameters; return the numerical floor as a field/proved property of the new witness.
3. Prove the fixed Delta/t formula for `detectorMesh`, using the source's `depth`, `range`, `sourceCap`, `reserve`, and `mesh` definitions without unproved numeric assertions or evaluating astronomically large naturals in the kernel.
4. Invoke the actual `native_beta_le_slot_calibrated_boundary_low_first` endpoint with a `sourceWithExactSlotMinimum` recalibration on that concrete witness, then the native Mertens and signed-pair theorems. Final theorem should show a *literal rational* exponent, not an existential expression depending on D.N or D.t.
5. Run warning-fatal Lean 4.34.1, exact-type checking, standard-axiom audit, and live original-source dependency tracing.

This source-gain route is already analytically paid by PR #1079. The remaining work is finite constructive parameter effectivization, not a newly required global signed cancellation. No RH conclusion follows.

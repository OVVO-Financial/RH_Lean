# Exact mask-specific diagonal audit for the `30 -> 210` extension

## Status

**Exact finite no-go for the non-circular diagonal family.**

This note audits the full mask-specific diagonal positive-form family on the exact 14-dimensional arithmetic compatibility quotient for the prime extension

```text
W = 30 = 2 * 3 * 5,
p = 7,
pW = 210.
```

The conclusion has two parts.

1. The unrestricted diagonal family is feasible only in a tautological way: put all output weight on the ordinary Möbius coordinate itself.
2. After imposing the non-circular condition that the child ordinary-output coordinate has zero diagonal weight, the full mask-specific diagonal family is infeasible. An exact rational dual certificate forces the parent budget to be at least

```text
368 / 3 = 122 2/3,
```

whereas the permitted seed budget is

```text
2 * phi(30) = 16.
```

This closes the mask-specific diagonal route at `30 -> 210`. It does not rule out genuinely off-diagonal Gram forms.

## Coordinates

Index the 16 child flip coordinates by masks `D subseteq {2,3,5,7}`, encoded as integers `0,...,15`. For old masks `C subseteq {2,3,5}`, write

```text
S_C       = A_C - B_C,
S_{C+{7}} = A_C + B_C.
```

The exact child operator is therefore

```text
T(A,B) = (A-B, A+B).
```

Among squarefree divisibility masks in `(30,210]`, exactly two Walsh atoms are absent:

```text
7  = {2,3,5},
10 = {3,7}.
```

Hence the compatible child space is

```text
V = {s in R^16 : <chi_7,s> = 0 and <chi_10,s> = 0},
```

which has dimension 14.

## Diagonal family

Let

```text
Q_child(s) = sum_D x_D s_D^2,
Q_parent(A,B) = sum_C y_C (A_C^2 + B_C^2),
```

with `x_D >= 0` and `y_C >= 0`.

The required inequalities are:

### Output domination

For every `s in V`,

```text
s_empty^2 <= Q_child(s).
```

### Extension compatibility

For every `s = T(A,B) in V`,

```text
Q_child(s) <= 6 Q_parent(A,B)
             = 3 sum_C y_C (s_C^2 + s_{C+{7}}^2).
```

### Parent seed budget

For every prefix state, and in particular at `U=199`,

```text
Q_parent(A(199),B(199)) <= 16.
```

The exact `U=199` coefficient vector is

```text
q = (37,565,281,3681,109,1813,793,7753),
```

so the budget inequality is

```text
37 y_0 + 565 y_1 + 281 y_2 + 3681 y_3
+ 109 y_4 + 1813 y_5 + 793 y_6 + 7753 y_7 <= 16.
```

## Tautological unrestricted solution

If the child ordinary-output coordinate is allowed, the choice

```text
x_0 = 1,
y_0 = 1/3,
all other x_D = y_C = 0
```

is feasible:

```text
Q_child(s) = s_0^2,
```

and

```text
s_0^2 = (A_0-B_0)^2 <= 2(A_0^2+B_0^2) = 6*(1/3)*(A_0^2+B_0^2).
```

At `U=199`, its parent cost is

```text
37/3 < 16.
```

This is circular: the proposed Lyapunov form is simply the target output squared. It supplies no independent arithmetic control.

## Non-circular condition

The non-circular diagonal audit therefore imposes

```text
x_0 = 0.
```

No symmetry assumption is imposed. The remaining 15 child weights and all 8 parent weights are independent and mask-specific.

## Exact rational dual certificate

The verifier in

```text
scripts/MaskSpecificDiagonalAudit/verify.py
```

contains 11 compatible output-test vectors, 7 compatible extension-test vectors, and exact rational multipliers.

For each output-test vector `u`, output domination gives

```text
u_0^2 <= sum_D x_D u_D^2.
```

For each extension-test vector `v`, extension compatibility gives

```text
sum_D x_D v_D^2
<= 3 sum_C y_C (v_C^2 + v_{C+8}^2).
```

Multiplying and summing the selected inequalities yields:

- for every child coordinate `D != 0`, the extension-side coefficient is at least the output-side coefficient;
- the only deficit is at `D=0`, where it is exactly `368/3`, and this term vanishes because `x_0=0`;
- for every parent mask `C`, the resulting `y_C` coefficient is at most the exact `U=199` budget coefficient `q_C`;
- the summed output constants equal exactly `368/3`.

Therefore every non-circular feasible diagonal family would satisfy

```text
368/3 <= q dot y <= 16,
```

which is impossible.

## Classification

- exact child operator: **proved identity**;
- 14-dimensional compatibility quotient: **proved finite classification**;
- unrestricted diagonal solution: **exact but circular**;
- non-circular mask-specific diagonal family: **closed by exact rational separating certificate**;
- genuinely off-diagonal positive forms: **still open**;
- `210 -> 2310` quotient test: unnecessary for the diagonal family because it already fails at `30 -> 210`.

## Next admissible route

The next search must allow genuine cross-mask or character couplings. Any candidate should provide:

1. an exact rational or algebraic PSD certificate on the 14-dimensional quotient;
2. non-circular output domination;
3. the parent budget `<=16`;
4. extension compatibility;
5. an explicit state-transition rule to the 31-dimensional `210 -> 2310` quotient.

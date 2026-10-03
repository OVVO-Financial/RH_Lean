# Floor-Li discrete Monte Carlo note

The finite experiment is recorded under \`numerics/floor_li_meboot/\`.

The primitive object is

\[
\xi_n
=
1_{\mathbb P}(n)
-
\left(
\lfloor L(n)\rfloor-\lfloor L(n-1)\rfloor
\right),
\qquad
L(x)=\operatorname{Li}(x)-\operatorname{Li}(2).
\]

Through \(x=9,998,244\), every floor-Li increment is \(0\) or \(1\), so the
observed mismatch stream is literally

\[
\xi_n\in\{-1,0,1\}.
\]

The exact square-block aggregation is

\[
P_R-F_R
=
\sum_{R^2<n\le(R+1)^2}\xi_n,
\]

where

\[
F_R=
\lfloor L((R+1)^2)\rfloor-\lfloor L(R^2)\rfloor.
\]

Thus the square-endpoint backlog

\[
E_R=\pi(R^2)-\lfloor L(R^2)\rfloor
\]

satisfies the exact discrete recurrence

\[
E_{R+1}=E_R+(P_R-F_R).
\]

The numerical telescope was checked exactly.

## Primitive observations

Over 9,998,242 integer sites:

- \(-1\): 620,144
- \(0\): 8,758,286
- \(+1\): 619,812
- nonzero fraction: 12.4017%
- lag-1: \(-0.0719711\)
- lag-2: \(-0.0242807\)
- illegal floor-Li jumps: 0

## Classified NNS.meboot stress

The same 4,611-path design as the existing VF-mid suite was rerun on the exact
integer square-block errors \(P_R-F_R\).

Because \`nns_meboot\` emits continuous values, each bootstrap replicate was
rank-classified back onto the exact observed integer block-error multiset. This
preserves the discrete support and empirical class frequencies while retaining
the bootstrap dependence ordering.

All 4,611 classified paths satisfy

\[
\max_{R\ge1000}|E_R|/(R\log R)<1
\]

over the tested range.

Key finite results:

- actual: \`0.0199905742\`
- dependence-sweep pooled 99th percentile: \`0.4128823163\`
- dependence-sweep maximum: \`0.5550283479\`
- serial-stress pooled 99th percentile: \`0.2795783498\`
- serial-stress maximum: \`0.3355437806\`
- maximum realized serial-stress lag-1: \`0.9386647316\`

At \(\phi=0.99\), median realized lag-1 is \`0.9011309436\` and the maximum is
\`0.9386647316\`; the corresponding finite RH-normalized maxima have median
\`0.1759384632\`, 95th percentile \`0.2837387421\`, and maximum \`0.3355437806\`.

## Proof-search consequence

This is still numerical evidence, not an asymptotic theorem. Its value is that
the floor-Li coordinate turns the primitive discrepancy into a bounded
three-class signed stream and shows that even deliberately large positive
serial persistence does not numerically consume the available \(R\log R\)
budget over the tested range.

The deterministic arithmetic target remains to control coherent accumulation
of the actual integer mismatch stream. The floor-Li/VF bridge is deterministic
and root-scale, so a bound on this integer backlog transfers directly back to
the already-compiled VF endpoint consumer.

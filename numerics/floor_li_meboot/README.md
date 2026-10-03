# Floor-Li discrete NNS.meboot stress numerics

This directory records a finite maximum-entropy bootstrap experiment for the
**discrete prime-versus-floor-Li mismatch process**.

It is theorem-discovery evidence only. It is not a premise of the Lean proof
chain and it does not prove an asymptotic statement about primes.

## Primitive discrete process

Using the repository normalization

\[
L(x)=\operatorname{Li}(x)-\operatorname{Li}(2),
\qquad
Q_n=\lfloor L(n)\rfloor,
\]

define

\[
\xi_n
=
1_{\mathbb P}(n)
-
(Q_n-Q_{n-1}).
\]

For every integer tested, \(Q_n-Q_{n-1}\in\{0,1\}\), hence

\[
\xi_n\in\{-1,0,1\}.
\]

The full primitive lattice was checked through

\[
x=3162^2=9,998,244.
\]

Recorded primitive counts over \(3\le n\le9,998,244\):

- \(-1\): \`620144\`
- \`0\`: \`8758286\`
- \(+1\): \`619812\`
- nonzero fraction: \`0.124017402259\`
- illegal floor-Li jumps: \`0\`
- lag-1 correlation: \`-0.0719711117312\`
- lag-2 correlation: \`-0.0242807093897\`

The observed transition matrix, with rows/columns ordered \((-1,0,+1)\), is

\[
\begin{pmatrix}
0&575510&44634\\
575537&7607570&575178\\
44607&575205&0
\end{pmatrix}.
\]

## Exact VF square-block aggregation

For

\[
P_R=\pi((R+1)^2)-\pi(R^2),
\]

and

\[
F_R=
\lfloor L((R+1)^2)\rfloor-
\lfloor L(R^2)\rfloor,
\]

the discrete block error is

\[
e_R=P_R-F_R
=
\sum_{R^2<n\le(R+1)^2}\xi_n.
\]

The square-endpoint backlog is

\[
E_R=\pi(R^2)-\lfloor L(R^2)\rfloor,
\]

and therefore exactly

\[
E_{R+1}=E_R+e_R.
\]

The numerical endpoint telescope closes exactly (\`endpoint_identity_check = 0\`).

The Monte Carlo range is \`R = 56,...,3161\`; the final endpoint is \`R = 3162\`.
Observed block statistics:

- lag-1: \`-0.136874596976\`
- lag-2: \`-0.077626634159\`
- minimum block error: \`-47\`
- maximum block error: \`42\`
- final backlog: \`-331\`
- \(\max_{R\ge1000}|E_R|/(R\log R)=0.0199905742261\)

## Discrete classification projection

\`NNS.meboot\` is continuous-valued. To keep the Monte Carlo outcome discrete,
each continuous replicate is rank-projected back onto the **exact observed
integer block-error multiset**:

1. sort one continuous bootstrap replicate;
2. sort the observed integer block errors \(e_R\);
3. assign the observed sorted values according to the replicate ranks.

This is the numerical analogue of a future \`classification=True\` /
discrete-outcome mode in \`NNS.meboot\`: it preserves the exact observed class
support and class frequencies while retaining the bootstrap rank/dependence
ordering.

## Monte Carlo design

The design deliberately mirrors \`numerics/vf_mid_meboot/\`.

### 1. Dependence-to-actual sweep

Pearson and Spearman targeting with

\[
\rho\in\{-0.95,-0.75,-0.50,-0.25,0,0.25,0.50,0.75,0.95\},
\]

199 replicates per target:

\`2 x 9 x 199 = 3582\` classified paths.

### 2. Serial-persistence stress

The observed integer block-error multiset is rank-reordered onto AR(1)
templates with

\[
\phi\in\{-0.90,-0.50,0,0.50,0.90,0.97,0.99\}.
\]

For each \(\phi\), three templates are passed through \`nns_meboot\` at target
Spearman correlation \`0.95\`, with 49 replicates per template:

\`7 x 3 x 49 = 1029\` classified paths.

Total: **4611 paths**.

## Main results

Every generated classified path satisfies

\[
\max_{R\ge1000}\frac{|E_R|}{R\log R}<1
\]

over the finite range tested.

Dependence-to-actual sweep:

- pooled 99th percentile: \`0.412882316297\`
- pooled maximum: \`0.555028347872\`

Serial-persistence stress:

- pooled 99th percentile: \`0.279578349840\`
- pooled maximum: \`0.335543780557\`
- maximum realized lag-1 correlation: \`0.938664731562\`

At latent \`phi=0.99\`:

- median realized lag-1: \`0.901130943561\`
- 95th percentile realized lag-1: \`0.929701647033\`
- maximum realized lag-1: \`0.938664731562\`
- median RH-normalized maximum: \`0.175938463155\`
- 95th percentile: \`0.283738742135\`
- 99th percentile: \`0.324460595683\`
- maximum: \`0.335543780557\`

## Interpretation

The discrete floor-Li coordinate does **not** prove a tighter Littlewood or RH
bound. What it does is remove the fractional reference from the primitive
error process:

\[
1_{\mathbb P}(n)-\Delta\lfloor L(n)\rfloor\in\{-1,0,1\}.
\]

The tested data show that this exact integer backlog can tolerate very strong
manufactured positive serial persistence over the tested range while remaining
well inside the \(R\log R\) target.

This strengthens the theorem-discovery message from the earlier VF-mid
experiment: the deterministic proof target is not independence. It is the
exclusion of sufficiently persistent *signed coherent accumulation* of the
actual prime/floor-Li mismatch.

## Reproduction

Install NNS-Python plus NumPy, SciPy, pandas, and matplotlib, then run:

\`\`\`bash
python numerics/floor_li_meboot/run_floor_li_meboot.py \\
  --out numerics/floor_li_meboot/results
\`\`\`

The script records the primitive lattice diagnostics, exact square-block
aggregation, full 4611-path classified stress suite, compact summaries, and
plots. NNS-Python source used for the experiment matches commit
\`55d15c9d6412a68942af467e9129551f4801f325\`.

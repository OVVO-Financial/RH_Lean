# K₂ coherent-mode kill gate

Diagnostic closeout of the existing K₂ route. The finite regression is not
an RH estimate; the compiled summatory bound is identified separately below.

The repository already contained the structural obstruction. Export
`SEAMS.md` §23 and

```text
RHLean.Analysis.NativePNTSignedSecondSelbergFactorFourBridge
```

record that the summatory signed second-Selberg kernel differs from the
physical PNT error multiplied by `-2 log N` by only `O(N)`:

$$
\sum_{n\le x} K_2(n)=-2\bigl(\psi(x)-x\bigr)\log x+O(x).
$$

The compiled bound is
`nativePNTSignedK2Summatory_add_two_error_log_abs_le`. A finite
correlation of `0.998` is therefore a verification of that identity, not
a new cancellation mechanism.

## Four facts

### 1. Exact kernel

The signed kernel used here and in the native Selberg layer is

$$
K_2(n)=(\Lambda*\Lambda)(n)-\Lambda(n)\log n
=\Lambda_2(n)-2\Lambda(n)\log n,
$$

where $\Lambda_2=\Lambda*\Lambda+\Lambda\log$ is the ordinary second
von Mangoldt function. Support is only on prime powers and products of
two prime powers:

$$
K_2(p^a)=-(\log p)^2,\qquad
K_2(p^a q^b)=2\log p\log q.
$$

### 2. Dirichlet series (corrected 2026-09-26)

For $\Re s>1$, put $H=\zeta'/\zeta$. The classical identity
$\sum_n\Lambda(n)n^{-s}=-H(s)$ is
[DLMF 27.4.12](https://dlmf.nist.gov/27.4.E12). Differentiation gives
$\sum_n\Lambda(n)\log n\,n^{-s}=H'(s)$, while convolution gives $H(s)^2$.
Consequently,

$$
\sum_{n\ge1}\frac{\Lambda_2(n)}{n^s}
=\frac{\zeta''}{\zeta},
\qquad
\sum_{n\ge1}\frac{K_2(n)}{n^s}
=2\Bigl(\frac{\zeta'}{\zeta}\Bigr)^2-\frac{\zeta''}{\zeta}
=H^2-H'.
$$

The earlier draft swapped these formulas and incorrectly called the
zero-spectrum singularities "zeros". If $\rho$ is a zeta zero of multiplicity
$m\ge1$, then $H(s)=m/(s-\rho)+O(1)$ and
$H^2-H'=m(m+1)/(s-\rho)^2+O((s-\rho)^{-1})$. Thus the signed K₂ series
retains a double pole at each such zero. At the pole $s=1$, the double-pole
coefficient cancels instead. This is a classical meromorphic calculation,
not a new Lean theorem in this PR.

### 3. Cancellation at $s=1$ versus the zero spectrum

The reciprocal theorem already in the repository is real: $\sum_{n\le N}K_2(n)/n$
is $O(\log N)$ after the constant $s=1$ mode is removed, against the
$(\log N)^2$ size of the unsigned second kernel. That saving lives at the
main term.

It does not attenuate the zero-driven component. The summatory identity
above multiplies the physical error $\psi(x)-x$ by $\log x$. A linear
bound on $\sum K_2$ would therefore require a logarithmic improvement of
the PNT error — exactly the improvement the onset analysis does not
supply, and exactly the coherent prime mode that has to be controlled
for an RH-scale statement.

### 4. Finite regression

`scripts/k2_coherent_mode_probe.c` accumulates the exact kernel and
$\psi$ on $10^4\le x\le 2\cdot10^7$ and regresses the next-order
centering

$$
\sum_{n\le x}K_2(n)+2\gamma x
\qquad\text{against}\qquad
-2\log x\bigl(\psi(x)-x\bigr).
$$

On $10^4\le x\le 2\cdot10^7$ (2000 sample points) the Pearson
correlation is $0.99833$. The raw ratio
$(\sum K_2+2(\psi-x)\log x)/x$ sits at $-1.1544\approx-2\gamma$,
consistent with a constant-mode remainder on this range. The oscillating piece
tracks $\psi(x)-x$ with a $\log x$ weight.

## Classification

$$
\text{$K_2$ closed as a mechanism for controlling the coherent prime mode.}
$$

The reciprocal cancellation theorem remains valid. These identities supply
no independent control of the zero-driven component: the signed series
retains its poles, and the compiled summatory comparison retains the PNT
error with a $\log x$ weight.

## Project consequence

This file does not open a successor K₂ branch. Combined with the already
recorded kills

| route | status |
| --- | --- |
| square-residual / prime-extension / replacement | #798 |
| global cross-prime cancellation | Möbius inversion, #799 |
| record carrier | records are the exceptional excursions themselves |
| dyadic local pairing | coherent mode survives |
| signed second Selberg | coherent zero spectrum survives and gets $\log x$ weighting |

the repository is a formal reduction and obstruction map. Further searches
among these existing internal identities are frozen pending a new quantitative
ingredient. This is a research decision about the tested routes, not an
impossibility theorem for every elementary or combinatorial approach.

The next mathematical question, if any, is external:

$$
\text{What theorem could actually control the coherent zero-driven mode at the required scale?}
$$

That is a literature question (Mertens moments, zero-density and
zero-correlation, Gonek–Ng-type conjectures, bilinear forms), not a Lean
identity search.

## Reproduction

```text
cc -O2 -o k2_coherent_mode_probe scripts/k2_coherent_mode_probe.c -lm
./k2_coherent_mode_probe
./k2_coherent_mode_probe 20000000 10000
python3 scripts/check_k2_coherent_mode_probe.py ./k2_coherent_mode_probe
```

The checker compares every prefix through 2000 against an independent
divisor-convolution calculation, then reproduces the documented full-range
regression. The dedicated workflow compiles with warnings as errors and runs
both checks. Floating-point diagnostics remain distinct from kernel proofs.

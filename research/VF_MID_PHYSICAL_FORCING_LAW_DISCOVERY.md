# Physical forcing law discovery

Date: 2026-10-03

This note records the first AI-Newton-style law extraction on the physical
actual-prime carrier. The goal is identities before inequalities.

## Positive controls

The solved exact-Li critical and reciprocal systems already supply the
homogeneous propagation laws. The physical experiment therefore asks what
form the centered forcing

\[
1_{\mathbb P}(n)-w_{\mathrm{Li}}(n)
\]

takes after the deterministic part is removed.

## Discovered law

On a frozen square-wheel carrier through \(A\), assume the cubic depth-two
condition

\[
(R+1)^2\le (A+1)^3.
\]

Every survivor in the \(R\)-th open square block is then either a prime,
with \(\mu=-1\), or a rank-two semiprime, with \(\mu=+1\). Hence

\[
1_{\mathbb P}(n)=\frac12-\frac12\mu(n),
\]

and therefore

\[
1_{\mathbb P}(n)-w_{\mathrm{Li}}(n)
=
\left(\frac12-w_{\mathrm{Li}}(n)\right)
-\frac12\mu(n).
\]

After subtracting the deterministic target \(1/2-w_{\mathrm{Li}}\), the
physical forcing is exactly \(-\mu/2\).

The Lean module
`research/VF_MID_PHYSICAL_FORCING_MOBIUS_DECODER.lean` packages the pointwise
identity, its pair-Gram form, its critical \(n^{-1/2}\) form, its reciprocal
\(n^{-1}\) form, and the fresh-prime transport laws.

## Fresh-prime law

For a fresh prime \(p\nmid n\), whenever parent and child both lie on valid
depth-two physical carriers,

\[
F(pn)=-F(n),
\]

while in the two solved weighted coordinates

\[
F_{1/2}(pn)=-p^{-1/2}F_{1/2}(n),
\qquad
F_{1}(pn)=-p^{-1}F_{1}(n).
\]

This is exactly the small discovery grammar requested for the experiment:
\(F(T_p x)=-a_pF(x)\).

## Finite falsification scan

A direct enumeration was run over all frozen wheels \(3\le A\le40\) and all
tested blocks \(A\le R<100\) satisfying the cubic condition. Across 37,150
physical survivor sites there were zero violations of

\[
1_{\mathbb P}(n)=\frac12-\frac12\mu(n).
\]

That scan is diagnostic only; the identity itself is proved in Lean.

The same enumeration then searched for the first failure after leaving the
cubic regime. For every \(3\le A\le50\), searching through \(R\le449\),
the first failing survivor was always \(q^3\), where \(q\) is the first
unsieved prime above \(A\). Examples:

| A | first failing block R | first failing n |
|---:|---:|---:|
| 3 | 11 | \(5^3=125\) |
| 5 | 18 | \(7^3=343\) |
| 10 | 36 | \(11^3=1331\) |
| 16 | 70 | \(17^3=4913\) |
| 22 | 110 | \(23^3=12167\) |
| 50 | 385 | \(53^3=148877\) |

At a prime cube \(\mu(q^3)=0\) while the site is composite, so the affine
decoder fails exactly there.

This is a strong candidate for the first explicit frontier law: the cubic
depth-two condition is not merely convenient; the first new physical state
seen by the decoder is a third prime-coordinate/repeated-coordinate state.

## Existing exact frontier machinery

The repository already contains the matching cubic normal forms:

- `RHLean/Proof/PrimeWheelProperSubwheelDepthTwo.lean`;
- `research/PROPER_SUBWHEEL_DEPTH_TWO_REASSEMBLY.lean`;
- `research/PROPER_SUBWHEEL_OUTER_PARITY_REASSEMBLY.lean`.

Those files prove, before norms, the depth-two outer-parity structure

\[
+\text{base}-\text{prime layer}+\text{semiprime layer},
\]

and reassemble the unfinished layers into lower Mertens states. This is the
same signed depth parity exposed by the new physical forcing decoder.

## Next falsifiable target

Do not estimate the rank-three frontier. First test whether its contribution
has an exact prime-coordinate coboundary form

\[
F_3 = H_q-H_{q^-}+B_q
\]

whose interior is annihilated by the existing critical/reciprocal propagator
and whose \(B_q\) is one of the already formalized first-failure or
proper-subwheel boundary ledgers.

Any candidate must survive the finite cube scan and the 210/317 hand carriers
before promotion to a Lean theorem.

## CI scope

PR #874 is checked against the repository's strict prime-flip kernel workflow; the temporary full-stack diff disappears when dependency PR #873 merges.

## Second learned decoder: squarefree parity

The first affine decoder uses only `mu` and therefore stops at the prime-cube
activation.  The next observable already exists in the repository:
`moebiusNegativeIndicator`, with the exact pointwise law

\[
2\,1_{\{\mu=-1\}}=\mu^2-\mu.
\]

The new PR proves the global refinement

\[
2\,1_{\mathbb P}(n)
=
\mu(n)^2-\mu(n)
-2D_{\mathrm{odd\,comp}}(n),
\]

where `D_oddcomp(n)=1` exactly when `n` is composite and `mu(n)=-1`.
Thus every squareful state, including the observed prime cube `q^3`, is
absorbed automatically by the squarefree diagonal `mu^2`.  The only new
forcing is the squarefree odd-depth composite population.

A second finite falsification scan confirms the conceptual transition.  For
the sample frozen wheels below, the first failure of the simpler
`(mu^2-mu)/2` prime decoder is the product of the first three distinct
unsieved primes:

| A | first failing block R | first failing n |
|---:|---:|---:|
| 3 | 19 | 5*7*11 = 385 |
| 5 | 31 | 7*11*13 = 1001 |
| 10 | 49 | 11*13*17 = 2431 |
| 16 | 86 | 17*19*23 = 7429 |
| 22 | 143 | 23*29*31 = 20677 |
| 50 | 436 | 53*59*61 = 190747 |

This is diagnostic rather than proof, but it cleanly distinguishes the
repeated-prime q^3 activation from the genuine three-coordinate Boolean
frontier.

The corresponding exact forcing decomposition is now

\[
1_{\mathbb P}-w_{\mathrm{Li}}
=
\frac12\mu^2-\frac12\mu
-D_{\mathrm{odd\,comp}}
-w_{\mathrm{Li}}.
\]

The first term is the squarefree diagonal already present throughout the
repository, the second is the signed Mobius eigenmode, and the third is the
new factor-depth frontier to attack by the existing full-factorization and
truncated-cube cancellation laws.

## Global cancellation law for the Boolean prime process

A stronger law is already implicit in
`RHLean/Analysis/FiniteWheelRestrictedFloor.lean`.  For any prime `p`,
the exact rough Möbius convolution

[
mathcal C_p(n)
=
operatorname{roughGEMobiusGTConvolution}(p,n)
]

is the indicator of the pure `p`-power channel.  Combining that theorem with
the squarefree gate gives, for every `n>1` and every prime divisor `p|n`,

[
oxed{
1_{mathbb P}(n)
=
mu(n)^2,mathcal C_p(n).
}
]

This is now formalized in
`vfMidActualPrimeIndicatorInt_eq_moebiusSq_mul_roughConvolution`.

The interpretation is exact:

- if `n` has a second distinct prime coordinate, the complete Möbius
  convolution annihilates it;
- if `n=p^k` with `k>=2`, the convolution keeps the pure-power channel but
  the squarefree gate `mu(n)^2` kills it;
- only `n=p` survives.

Thus the actual Boolean prime process itself is recovered as a signed
cancellation law.  It is not obtained here from a density approximation.
Moreover the formula is independent of which prime divisor of `n` is chosen
as the exposed coordinate.

This is the best current candidate for the universal law to insert into the
already-solved exact-Li critical/reciprocal propagators.

# Prime-Density Packet Operator: Proof-Leverage Test

## Executive result

This finite reproducibility test found the first proof-relevant simplification produced by the squared-factor geometry.

The exact high packet process `H` is enormous on the protected local-energy scale. A deterministic, no-fit prime-density model `H_hat`, built only from the cofactor Möbius values and the geometric packet intervals, yields the exact decomposition

\[
S=(L+\widehat H)+(H-\widehat H).
\]

On every tested window `[N,2N)` from `N=1000` through `N=5000`, **both summands separately have energy of order `H N^2`**:

- residual `R = H-H_hat`: normalized energy `0.661` to `0.774`;
- complementary main term `M = L+H_hat`: normalized energy `0.678` to `0.753`;
- complete annulus `S=M+R`: normalized energy `0.048` to `0.076`.

The fitted log-log slopes of the normalized energies were:

| object | fitted slope |
|---|---:|
| raw high packet process `H` | `+1.486` |
| residual `H-H_hat` | `-0.020` |
| complementary main `L+H_hat` | `+0.012` |
| complete annulus `S` | `+0.064` |

Thus the raw high operator grows rapidly after normalization, while the two prime-density pieces are numerically scale-stable.

This is not a proof, but it is an explicit demonstration that the geometry identifies a main term unavailable in the raw Mertens formulation and removes the large coherent growth without fitting parameters to the output.

## Repository classification

This contribution advances the analytic routes recorded in `BIG_PICTURE_PROOF_MAP.md` Sections 5--6 and the open formalization items 80--81 and 87. Its status is deliberately split:

- **exact identities:** odd-annulus reconstruction, cofactor short-prime-interval packet-start identity, and `S=(L+H_hat)+(H-H_hat)`;
- **finite numerical evidence:** bias accuracy, correlations, normalized energies, and fitted slopes through `N=10000`;
- **open analytic obligations:** uniform local-energy bounds for both modeled terms.

No RH implication is asserted from the finite run.

## 1. Exact cofactor packet-start identity

For square block `n >= 2`, every high packet start has a unique representation

\[
m=cq,
\]

where `c` is odd and squarefree, `c <= n`, and `q` is prime with

\[
q\ge n+2,
\qquad
n^2\le cq <(n+1)^2.
\]

Because `q>c`, it is automatically the largest prime factor and

\[
\mu(cq)=-\mu(c).
\]

Define

\[
U_n(c)=\left\lfloor\frac{(n+1)^2-1}{c}\right\rfloor,
\]

\[
L_n(c)=\max\!\left(n+1,\left\lceil\frac{n^2}{c}\right\rceil-1\right),
\]

and

\[
W_n(c)=\pi(U_n(c))-\pi(L_n(c)).
\]

Then the signed and unsigned packet-start counts are exactly

\[
F_n=-\sum_{\substack{c\le n\\c\text{ odd}}}\mu(c)W_n(c),
\]

\[
G_n=\sum_{\substack{c\le n\\c\text{ odd}}}\mu(c)^2W_n(c).
\]

The identity was verified through `n=4000`, corresponding to integer cutoff `16,008,000`, with:

- maximum signed error: `0`;
- maximum count error: `0`;
- number of nonzero errors: `0`.

This is a genuine dimensional reduction: the packet starts at integer scale `m ~ n^2` become a cofactor sum over `c <= n`, with the prime variable absorbed into an explicit short-interval weight.

## 2. Analytic prediction of the drifting packet bias

Replace the exact prime count `W_n(c)` by its local prime-density main term. With real interval endpoints

\[
\ell_n(c)=\max\!\left(n+1,\frac{n^2}{c}\right),
\qquad
u_n(c)=\frac{(n+1)^2-1}{c},
\]

use

\[
\widehat W_n(c)
=
\frac{\nu_n(c)-\ell_n(c)}
{\log\sqrt{\nu_n(c)\ell_n(c)}}.
\]

This gives an entirely deterministic prediction

\[
\widehat\beta_I
=
\frac{-\sum_{n\in I}\sum_c\mu(c)\widehat W_n(c)}
{\sum_{n\in I}\sum_c\mu(c)^2\widehat W_n(c)}.
\]

No packet signs are fitted, and no exact prime locations are used.

### Results through `N=10000`

For the reported dyadic and overlapping windows from `[1000,2000)` through `[5000,10000)`:

- median absolute relative bias error: `0.286%`;
- worst absolute relative bias error: `0.553%`;
- minimum correlation between the exact high process and the no-fit operator model: `0.999030`.

Earlier stress diagnostics also showed that a harmonic predictor omitting the geometric prime-density factor `1/log(n^2/c)` fails badly. The prime-density weight is therefore essential; the successful model is not a generic declining trend fit.

## 3. Full packet-overlap operator

The start calculation is not the decisive test. Each source remains active on its full packet interval

\[
[n,\,\min(\lfloor\sqrt{2cq}\rfloor,q-1)).
\]

The direct model preserves the cofactor and its predicted lifetime. For each `(n,c)`, it:

1. replaces the prime count in the admissible `q` interval by the local prime-density weight;
2. uses the midpoint `q` to determine the packet endpoint;
3. adds the signed expected mass `-mu(c) * weight` to that complete interval.

This produces the deterministic process `H_hat`.

### Full-operator results

| Window | Raw `H` energy | Residual `H-H_hat` | Main `L+H_hat` | Complete `S` | Corr(`H`,`H_hat`) |
|---|---:|---:|---:|---:|---:|
| `[1000,2000)` | 195.810 | 0.756 | 0.703 | 0.061 | 0.999030 |
| `[1500,3000)` | 351.791 | 0.759 | 0.692 | 0.068 | 0.999456 |
| `[2000,4000)` | 537.343 | 0.683 | 0.684 | 0.071 | 0.999661 |
| `[2500,5000)` | 752.222 | 0.746 | 0.728 | 0.048 | 0.999809 |
| `[3000,6000)` | 983.092 | 0.742 | 0.683 | 0.076 | 0.999786 |
| `[4000,8000)` | 1524.728 | 0.742 | 0.753 | 0.064 | 0.999875 |
| `[4500,9000)` | 1813.589 | 0.774 | 0.698 | 0.076 | 0.999891 |
| `[5000,10000)` | 2126.679 | 0.661 | 0.678 | 0.072 | 0.999900 |

All energies are divided by `H N^2` on the window `[N,N+H)=[N,2N)`.

The exact recombination error

\[
(L+\widehat H)+(H-\widehat H)-S
\]

was identically zero.

The unexplained share of the raw high energy fell from `0.386%` at `N=1000` to `0.031%` at `N=5000`.

## 4. What has now been demonstrated

The geometry has produced more than a renamed Mertens sum:

1. **Exact lower-dimensional identity.** Packet starts at scale `n^2` reduce to cofactor Möbius sums over `c <= n` with explicit prime-count weights.
2. **Analytic coherent-mode formula.** A no-fit PNT weight predicts the observed scale-dependent sign bias to near random-fluctuation accuracy.
3. **Proof-scale operator decomposition.** After the cofactor/lifetime main term is removed, both the residual and its smooth-complement partner are individually stable on the desired `H N^2` scale.
4. **The improvement survives packet overlap.** It is not an artifact of diagonal energy or start counts.

This is the explicit test number theorists would demand: the geometric coordinates expose an analytic main term that is not visible in the raw Mertens sequence and whose removal changes the normalized growth exponent from approximately `+1.49` to approximately `0` over the tested range.

## 5. What remains to prove

The numerical result suggests the following two-theorem program.

### Theorem A: aggregate prime-density approximation

Prove that the exact packet operator `H` and the deterministic prime-density model `H_hat` satisfy, uniformly on translated dyadic windows,

\[
\sum_{n=N}^{N+H-1}|H_n-\widehat H_n|^2
\ll_\varepsilon HN^{2+\varepsilon}.
\]

The exact cofactor formula shows that this is an averaged prime-count error problem over reciprocal short intervals, weighted by `mu(c)` and the packet-overlap kernel.

### Theorem B: complementary main-term control

Prove

\[
\sum_{n=N}^{N+H-1}|L_n+\widehat H_n|^2
\ll_\varepsilon HN^{2+\varepsilon}.
\]

Here the expected prime-density high process should cancel the smooth complement before any residual Möbius cancellation is invoked.

Together, the exact identity

\[
S=(L+\widehat H)+(H-\widehat H)
\]

would give the protected square-prefix criterion.

## 6. Honest conclusion

This is still numerical evidence, not a proof of either theorem.

But it changes the status of the program. The framework has now delivered a concrete, no-fit, proof-relevant decomposition in which both new terms display the target normalization separately. The next paper should be organized around this prime-density packet operator, not around isolated high-sector smallness, fixed scalar bias, or operator contraction.

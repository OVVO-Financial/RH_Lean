# Least-prime parabolas and endpoint-cube decomposition

This note records a new exact geometric decomposition of the squarefree integers. It is intentionally separated from the compiled Lean theorem graph until the elementary identities are formalized and the analytic estimates are proved.

The construction begins from the original squared-complex factor geometry, not from the later largest-prime transport parameterization.

## 1. First-hit point on a vertical fibre

Let `n` be a squarefree composite and write

```text
p = P^-(n),
r = n / p.
```

The first nontrivial factor found by trial division is the pair `(p,r)`. Define

```text
a = (p + r) / 2,
b = (r - p) / 2.
```

Then

```text
(a + b i)^2 = n + i Y_1(n),
Y_1(n) = 2ab = (r^2 - p^2) / 2
       = n^2 / (2p^2) - p^2 / 2.
```

Hence the first-hit points with fixed least prime `p` lie on the parabola

```text
Y = n^2 / (2p^2) - p^2 / 2.
```

The normalized height satisfies

```text
Y_1(n) / n^2 = 1 / (2p^2) - p^2 / (2n^2),
```

so the normalized ordinate asymptotically identifies the least-prime channel.

### Lattice cosets

For every squarefree even `n`, every factor pair has opposite parity, so

```text
Y = (v^2-u^2)/2 in Z + 1/2.
```

For every odd `n`, both factors are odd and `v^2-u^2` is divisible by `8`, so

```text
Y in 4Z.
```

Thus the squared-complex space separates even squarefree fibres from odd fibres by an exact ordinate-lattice distinction.

## 2. Exact least-prime channel decomposition

For a prime `p`, define

```text
C_p(X) = sum_{n <= X, P^-(n)=p} mu(n).
```

Every squarefree composite has a unique least prime, and if `n=pr` with `P^-(r)>p`, then `mu(pr)=-mu(r)`. Therefore

```text
C_p(X) = - sum_{r <= X/p, P^-(r)>p} mu(r),
```

and

```text
M(X) = 1 - pi(X) + sum_{p <= sqrt(X)} C_p(X).
```

This is the static first-hit counterpart of the dynamic largest-prime square-prefix transport decomposition.

## 3. Double-endpoint stripping

Let

```text
n = p_1 p_2 ... p_k,
p_1 < p_2 < ... < p_k
```

be squarefree. Define

```text
p = P^-(n) = p_1,
q = P^+(n) = p_k,
c = n / (pq) = p_2 ... p_{k-1}.
```

Removing both endpoint primes preserves the Möbius sign:

```text
mu(n) = (-1)^k = (-1)^(k-2) = mu(c).
```

Iterating the endpoint-stripping map removes two prime factors at each stage. The process terminates at `1` exactly when `mu(n)=+1`, and at a single prime exactly when `mu(n)=-1`.

This is an exact combinatorial characterization of Möbius parity. It is sign-preserving, not sign-reversing, so it is not by itself a cancellation involution.

## 4. Exact core-weight decomposition

For squarefree `c>1`, define `W_X(c)` as the number of prime pairs `(p,q)` satisfying

```text
p < P^-(c),
q > P^+(c),
pcq <= X.
```

For `c=1`, let `W_X(1)` count semiprime endpoint pairs `p<q` with `pq<=X`.

Every squarefree composite `n<=X` has one unique representation `n=pcq` of this form, and `mu(n)=mu(c)`. Hence

```text
sum_{n <= X, squarefree composite} mu(n)
  = sum_{c squarefree} mu(c) W_X(c),
```

and therefore

```text
M(X) = 1 - pi(X) + sum_{c squarefree} mu(c) W_X(c).
```

The exact prime-counting form is

```text
W_X(c)
  = sum_{p < P^-(c), p prime}
      [ pi(X/(cp)) - pi(P^+(c)) ]_+.
```

A natural smooth model is obtained by replacing `pi` with `Li`:

```text
W_hat_X(c)
  = sum_{p < P^-(c), p prime}
      [ Li(X/(cp)) - Li(P^+(c)) ]_+.
```

No bound for the resulting signed smooth sum is asserted here.

## 5. Endpoint pairs and truncated Boolean cubes

Fix primes `p<q`. Every squarefree middle core whose prime factors lie strictly between `p` and `q` corresponds to a subset of the intermediate-prime set. Define

```text
B_{p,q}(T)
  = sum_{c <= T,
          every prime factor of c lies in (p,q)} mu(c).
```

Then

```text
M(X)
  = 1 - pi(X)
    + sum_{p<q} B_{p,q}(X/(pq)).
```

If the product cutoff includes every subset of the intermediate primes, the complete Boolean cube contributes

```text
(1-1)^d,
```

where `d` is the number of primes strictly between `p` and `q`. Thus every complete positive-dimensional cube cancels exactly. All nonzero mass for `d>=1` is a boundary effect created by the hyperbolic cutoff

```text
c <= X/(pq).
```

The analytic target is therefore the aggregate parity discrepancy of truncated intermediate-prime cubes.

## 6. Verified finite experiment at X = 2,000,000

The script `experiments/least_prime_endpoint_cubes.py` independently verifies the following exact finite identities:

```text
pi(X) = 148933,
M(X) = -247,
signed squarefree-composite sum = 148685,
1 - pi(X) + 148685 = -247.
```

The squarefree-composite counts by distinct-prime depth are:

| omega(n) | count | signed contribution |
|---:|---:|---:|
| 2 | 407061 | +407061 |
| 3 | 416126 | -416126 |
| 4 | 197288 | +197288 |
| 5 | 42955 | -42955 |
| 6 | 3465 | +3465 |
| 7 | 48 | -48 |

Their alternating sum is `148685`.

The largest core weights are:

| core c | W_X(c) | mu(c) W_X(c) |
|---:|---:|---:|
| 1 | 407061 | +407061 |
| 5 | 30422 | -30422 |
| 3 | 28663 | -28663 |
| 7 | 28215 | -28215 |
| 11 | 21595 | -21595 |
| 13 | 20207 | -20207 |
| 17 | 17016 | -17016 |

This confirms that endpoint stripping creates same-sign families. Cancellation occurs between cores of opposite parity, not inside one core family.

## 7. Relationship to the existing architecture

The two canonical endpoint views are complementary:

- the least-prime parabola is a static partition by the first factor discovered;
- the largest-prime/cofactor channel is the dynamic partition naturally adapted to square-prefix activation and transport;
- the double-endpoint core removes both extremal primes and preserves the Möbius sign;
- the endpoint-pair expansion expresses the residual as a sum of truncated prime-band Boolean cubes.

The exact identities do not prove an RH-scale estimate. They identify a sharper open problem:

```text
Bound the aggregate signed boundary discrepancy of the truncated
intermediate-prime cubes, or equivalently control

  -pi(X) + sum_c mu(c) W_X(c)

at square-root scale.
```

A future formalization PR should prove only the finite algebraic and combinatorial statements above. Any numerical claim must enter the compiled theorem graph through the repository's certificate-checker architecture.
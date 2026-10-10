# Exact principal coefficient and signed amplifier inlet

The new principal coefficient module constructs its coefficients from
Mathlib's actual integer Möbius function. It does not assume a Mertens
estimate or a rational-to-ideal coefficient equality.

Let `chi(n)` be the period-three character, and use `*` for Dirichlet
convolution. The definitions are

\[
a=\mu*(\chi\mu),\qquad
a^{(6)}(m)=\mathbf1_{2\nmid m,\,3\nmid m}a(m).
\]

The module proves `chi*a=mu` and restores the excluded factors as

\[
\chi*(1-\delta_3)*(1-\delta_4)*a^{(6)}=\mu.
\]

The delta factors are arithmetic functions with Dirichlet multiplication;
they are not pointwise masks. In particular, the inert factor is at norm
four, and the ramified factor is at norm three.

## Physical weights and sharp prefixes

For an arbitrary complex site weight supported in `1..N`, with `12 <= N`,
the finite consumer proves

\[
\sum_{n=1}^{N}\mu(n)w(n)
=\sum_{m=1}^{N}a^{(6)}(m)
  \sum_{d=1}^{N}\chi(d)
  [w(md)-w(3md)-w(4md)+w(12md)].
\]

The support hypothesis is a literal finite cutoff. It contains no
analytic cancellation assumption. One may choose `N` greater than the
support, so the lower bound on `N` does not restrict finitely supported
weights. The value at zero is irrelevant to both positive-index sums.

The smooth and high-prime masks are defined by the actual prime-divisor
condition `forall p, Prime p -> p divides n -> p <= R`. Their difference
is the sharp prefix mask. Linearity proves this cancellation at each
transformed norm before summation.

The character prefix is an actual finite character sum, whose residue
formula is proved by induction. The sharp transformed coefficient is

\[
k(t)=C(t)-C(\lfloor t/3\rfloor)
      -C(\lfloor t/4\rfloor)+C(\lfloor t/12\rfloor).
\]

The module proves period 36, the range `[-2,1]`, mean zero over one period,
and the Mertens identity with `k(floor(X/m))`. The periodicity is in the
quotient, not in the physical Möbius observable.

## Signed sixth-power column

The companion module uses a finite squarefree prime-label carrier. Labels
are distinct even if their norms coincide, so the two labels of a split
prime are never merged. A column is partitioned uniquely into its labels
meeting the amplifier and its surviving labels. Norms and signed complex
coefficients multiply across this disjoint partition.

The resulting column identity permits any norm weight and expands both
legs of the mixed Gram into the full signed `d,e` matrix. At the principal
row the surviving coefficient is `(-1)^card`; the sixth-power character
adds only a coprimality mask. No supremum or absolute square is used to
replace that matrix.

This carrier formalizes finite squarefree factorization. Its dictionary
with actual Eisenstein prime ideals, and the identification of the
constructed arithmetic function with norm-grouped ideal Möbius, remain
separate semantic obligations. Neither module imports the upstream OpenAI
Hecke-character formalization or its analytic moment estimates.

## Reproducible finite arithmetic and proof boundary

`scripts/vf919_principal_coefficient_check.py` computes the coefficients
independently from split/inert/ramified Euler polynomials and from
`mu*(chi mu)`. It compares both arrays, verifies the excluded-factor
restoration at every norm through `1027^2-1`, and reproduces:

| R | Positive terms | Negative terms | M(R²−1) |
|---:|---:|---:|---:|
| 317 | 10999 | -11027 | -28 |
| 548 | 33015 | -32781 | 234 |
| 1027 | 115772 | -115405 | 367 |

The dedicated workflow compiles the modules with warnings fatal, checks
the elaborated signatures and standard axioms, and runs this census. A
green run at the reviewed commit is the evidence of kernel validation.

The uniform one-sided mixed-moment inequality is still open. A bounded,
mean-zero quotient kernel does not bound its signed Möbius pairing. The
finite amplifier partition alone gives no power saving. The full native
historical Sector Six source and once-only accounting remain subject to
the current proof contract.

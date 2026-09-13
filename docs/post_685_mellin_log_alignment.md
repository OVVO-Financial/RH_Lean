# Post-#685 Mellin/log alignment attack

## New exact local observation

The raw zero-factor law and the reciprocal Euler law are the two endpoints of
one multiplicative interpolation.

Write

\[
r_R(c)=\text{the raw signed critical atom at }c,
\]

and let the fresh-prime boundary charge be

\[
B_R(c,p)=\mu(c)(\mathrm{Loss}_R(c,p)-\mathrm{Birth}_R(c,p)).
\]

The already-compiled raw pair law is

\[
r_R(c)+r_R(cp)=B_R(c,p).
\]

For any multiplicative coordinate `w` whose local fresh-prime ratio is

\[
w(cp)=z_p w(c),
\]

one therefore has the exact identity

\[
\boxed{
 w(c)r_R(c)+w(cp)r_R(cp)
 =(1-z_p)w(c)r_R(c)+z_p w(c)B_R(c,p).
}
\]

For the Mellin weight

\[
w_s(n)=n^{-s},\qquad z_p=p^{-s},
\]

this becomes

\[
\boxed{
 u_s(c)+u_s(cp)
 =(1-p^{-s})u_s(c)+\frac{B_R(c,p)}{(cp)^s}.
}
\]

Thus:

- `s=0`: `1-p^{-s}=0`, the exact raw/Othello zero-factor step;
- `s=1`: `1-p^{-s}=1-1/p`, the exact reciprocal Euler step;
- differentiating in `s` creates `log p`, so the #685 memory factor sits on a
  genuine Mellin path rather than being an accidental coefficient.

The abstract local identity is now in
`RHLean/Proof/PostRootPartnerMellinInterpolation.lean`.

## Why the logarithm is relevant

The hard physical column and the easy reciprocal column can be viewed as the
endpoints

\[
C_0=\sum_q A_q,
\qquad
C_1=\sum_q \frac{A_q}{q}
\]

of

\[
C_s=\sum_q q^{-s}A_q.
\]

Formally,

\[
\frac{d}{ds}C_s
=-\sum_q (\log q)q^{-s}A_q,
\]

hence

\[
C_0=C_1+\int_0^1\sum_q(\log q)q^{-s}A_q\,ds.
\]

At `s=1`, the prime weight is `(log q)/q`.  Chebyshev/PNT gives

\[
\sum_{q\le x}\log q\sim x,
\]

so `(log q)/q` against prime mass is naturally `dq/q=d log q`.  This is the
precise version of the log-coordinate alignment.

The repository already has the required exact finite arithmetic ingredients:

1. `LogWeightedPrimeExtensionFiber` proves the squarefree child-fibre identity
   \[
   \sum_{p\mid n}\mu(n/p)\log p=-\mu(n)\log n.
   \]
2. `LogWeightedPrimeExtensionEndpoint` proves that multiplication by `log n` is
   a derivation for Dirichlet convolution.
3. The native PNT route proves `psi(N)/N -> 1` and `theta(N)/N -> 1`
   unconditionally.
4. `CanonicalRoughTruncatedWheelManyPrimeTelescope` and
   `CanonicalRoughBoundaryProfileAbelReturn` identify the `s=1` reciprocal
   telescope and the `s=0` unweighted Abel return exactly.

## Where RH can still hide

PNT alone cannot bound an arbitrary signed profile correlated with the primes.
The canonical `s=0` endpoint is exactly the Abel primitive

\[
\sum_{n<K}B_n-KB_K,
\]

so replacing prime gaps by their average `log p` termwise would be invalid.
The logarithmic route is useful only if the derivative family can be reassembled
arithmetically before taking norms.

The encouraging structural fact is that the older log-weighted extension split
already isolates the only obstruction to fresh-prime reassembly as the
**square-producing correction** (`p | c`).  That correction naturally lives at
scale `p^2`.  This is exactly the scale required by the current q^2 daughter
induction.

## Next exact theorem

The next theorem should not be a PNT estimate.  It should be an actual-carrier
Mellin compatibility theorem.

For a complete descending prefix above `p`, define the evolved raw coefficient
field `a`.  Prove, for a multiplicative weight `w` with local ratio `z_p`, that
on the current physical parent/child population

\[
\sum_c
\bigl[a(c)w(c)r_R(c)+a(cp)w(cp)r_R(cp)\bigr]
\]

reassembles exactly as

\[
(1-z_p)\sum_c a(c)w(c)r_R(c)
+z_p\sum_c a(c)w(c)B_R(c,p),
\]

with **zero coefficient-mismatch ledger**.

The existing four-corner proof should supply the mismatch zero: whenever the
child atom is nonzero, a later larger-prime extension has already zeroed both
raw coefficients; otherwise the child atom itself is zero.  This argument does
not depend on `s=1`.

Once this compiles, specialize to `w_s(n)=n^{-s}` conceptually and compare the
log derivative with the already-compiled log-weighted child-fibre identity.
The decisive test is whether the derivative remainder is exactly a signed
`p^2` daughter population plus root-scale boundary.  If yes, the logarithmic
coordinate has exposed a genuine recursive mechanism.  If an unsuppressed
first-power term remains, the Perron/log route is only a reformulation.

No norm should be taken before that test.

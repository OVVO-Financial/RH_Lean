# Post-#685 Mellin/log alignment attack

## 2026-09-13: the proposed q² support equality is false

Audited against PR #685 head `0170c8cd10bea71724ba8ef85ab1fa3203f960b6`.
The PR merged before this audit. Its existing branch is retained; no new PR
or replacement coordinate system is introduced.

The proposed `FarFourSignedQ2TowerSupport` is already defined in
`RHLean/Proof/PostRootPartnerLogAlignment.lean`. It is an unproved proposition,
not a compiled theorem. Exact integer evaluation gives:

| R | HighTransport | ChildFar | Renewal | Terminal | Destination sum | Survivor minus root |
|---:|---:|---:|---:|---:|---:|---:|
| 56 | 8 | 160 | 309 | -466 | 3 | -5 |
| 100 | 32 | 470 | 834 | -1326 | -22 | -54 |

Thus the requested equality already requires `8 = 3` at its first permitted
radius. At `R = 56`, the survivor equals the root reassembly boundary **minus
five**, not that boundary itself. No norm or estimate enters this calculation.

Reproduce the census using:

```sh
python scripts/far_four_diagnostic.py --q2-support --roots 56 100
```

This is an executable exact-integer diagnostic, not a kernel-checked Lean
certificate. The local Lean 4.24.0 executable fails during startup with
`error: failed to locate application`; the Lake build and elaborated-graph gate
therefore were not run. No new Lean theorem or proof is claimed.

### First exact carrier mismatch

Put `X = R²-1` and `Yq = floor(X/q²)`. The definition
`q2DaughterHighTransport` in `ExceptionalTransportCoboundary.lean` is

```text
sum over prime p with q <= p <= Yq:
  frozenPrimeUniverseMass (primesUpTo (p-1)) (Yq/p).
```

The existing theorem
`frozenPrimeUniverseMass_eq_frozenPredecessorMobiusEval` expands each cube into
its actual Möbius coefficients. Its nonzero occurrence census is therefore

```text
q prime, q < R;
p prime, q <= p;
d >= 1 squarefree, P+(d) < p;
q²*d*p <= X;
weight mu(d).
```

The proved scalar source bridge is
`q2DaughterHighTransport_eq_go_sub_mertens_all`. At `R=56` its nonzero owner
columns are:

| q | Yq | Go | M(Yq) | HighTransport |
|---:|---:|---:|---:|---:|
| 2 | 783 | 1 | -1 | 2 |
| 3 | 348 | 0 | 2 | -2 |
| 5 | 125 | 0 | -1 | 1 |
| 7 | 63 | 0 | -1 | 1 |
| 11 | 25 | 2 | -2 | 4 |
| 13 | 18 | 0 | -2 | 2 |

All remaining owners contribute zero. The diagnostic also evaluates the
prime-first definition directly and checks this scalar identity for every
owner; it does not obtain high transport by substituting the destination sum.

By contrast, the exact membership theorem
`mem_lowWheelFarPrimeLowCofactorTriples_iff_data` in
`StableFarWallSignedReassembly.lean` gives

```text
q prime, q < R;
p prime, p >= R+8;
d >= 1 squarefree, P+(d) < q;
q*d*p <= X;
stripped weight mu(d).
```

This is the source consumed by
`lowWheelFarPrimeLowCofactorTriples_sum_eq_descended_add_crossing`.
`lowWheelFarPrimeQ2DescendedOwner_image_eq_childFarSlice` identifies its
`q²*d*p <= X` part with ChildFar. The complementary strict crossings satisfy
`q*d*p <= X < q²*d*p` and become Renewal with their original owner tags.

The attempted first rewrite from high transport to this stable-far source
therefore changes **both** the cofactor cube (`P+(d)<p` versus `P+(d)<q`)
**and** the cutoff (`q²*d*p` versus `q*d*p`), as well as the far-prime range.
It is not a missing rearrangement of the same finite occurrences.

### The existing destination composition and sign audit

`lowWheelFarPrimeProductKey_injOn` retains the owner in `(q,d*p)` and proves
injectivity before forming a `Finset.image`.
`lowWheelFarPrimeProduct_weight` gives `mu(d*p) = -mu(d)`.
`lowWheelFarPrimeCrossingStableState_weight_eq_neg_product` flips that sign
back on renewal. Its sum is indexed by the original crossing product carrier,
so two distinct owners returning to the same `(d,p)` still contribute twice.

The unit/nonunit renewal split does not make the terminal sector disappear.
`lowWheelFarPrimeQ2UnitRenewal_add_unitTerminal_eq_centeredMultiplicity`
leaves exactly `multiplicity(p)-1` at every far unit prime. Nonunit renewal is
regrouped with its exact next-owner multiplicity. These are signed identities,
not a proof that the resulting multiplicities equal the high-transport census.

`lowWheelFarPrimeUnit_sub_internalMate_sub_top_eq_neg_terminalMass` supplies
the terminal sign. At `R=56`, there are 427 far unit primes, internal-mate mass
is -30, and top-image mass is -9. Hence terminal mass is
`-30-9-427 = -466`. The diagnostic independently evaluates the disjoint union
of actual terminal integer products and checks injectivity across both owned
source populations before taking this sum.

The full existing rewrite chain ends at the already-compiled identity

```text
ChildFar + Renewal + Terminal = -lowWheelFrozenTopFarResidual.
```

It is named `farPopulations_eq_neg_frozenTopFar` in
`PhysicalQ2ExceptionalTerminalSynthesis.lean`. At `R=56`, the residual is -3,
consistent with the independently computed endpoint `M(3135)=6` and
`finalCompensatedRootBoundary=3`.

### A single unmatched terminal occurrence

At `R=56`, take the prime `p=1571`. It lies in the far unit terminal carrier
because `64 <= 1571 <= 3135`. Its terminal weight is -1. But:

- `2*p = 3142 > 3135`, so no crossing owner can return to this prime;
- `4*p = 6284 > 3135`, so no ChildFar or high-transport occurrence can have
  this far-prime coordinate;
- every owned terminal product has largest prime at most 56, so none can
  supply this product either.

Thus a proposed pushforward preserving the physical far-prime coordinate has
source coefficient zero and destination coefficient -1 at `(1,1571)`.
LOG-MATCH preserves this coordinate within the stable-far source and remains
valid; it does not supply the false scalar support equality. Nonlocal scalar
cancellation could only be a separate argument, and the exact scalar census
above shows that it does not produce the equality requested here.

The survivor collapse and the requested clean q² normal form cannot be
instantiated from this false support proposition. FAR-4 is not established by
this audit. The historical Mellin discussion below is retained as context.

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

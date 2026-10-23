# Applied bridge: fixed subroot Mobius coefficients to the ORIGINAL moving-prime response

**Date:** 2026-10-23. **Status:** Exact arithmetic source and Lean-scale nonadmission, not an independent 7/8 improvement or RH theorem. This is an application of the existing #919 fully restored coefficient dictionary to the physically correct prime-response operator. It does not claim to reproduce OpenAI's Gaussian detector source or discharge its character moments.

## I. Which signs are fixed, which populations move?

Take R>=4, X=R^2-1, and a FIXED low-prime wheel of all p<=R. Define

```
w_R(c) = #{p prime : R<p<=X and c*p<=X}
       = pi(floor(X/c))-pi(R)   for 1<=c<R,
       = 0                      for c>=R.

T_R = sum_(1<=c<R) mu_Z(c) w_R(c).
S_R = sum_(1<=n<=X, P+(n)<=R) mu_Z(n).
```

The index c stays below R and mu_Z(c) never changes during the later p>R
prime insertions. Descendants have mu_Z(cp)=-mu_Z(c) and at most one
p>R, so the exact original balance is

```
M(X) = S_R - T_R.
```

The complete zero-target NNS cross Co-Div equals -S_R*T_R, not a
statistical covariance from independently sampled populations:

```
M(X)^2 = S_R^2+T_R^2-2*S_R*T_R.
```

An externally established all-X Mertens 7/8 bound implies
2*S_R*T_R >= S_R^2+T_R^2-C_eps*R^(7/2+eps);
it does not bound S_R or T_R separately. On this real carrier, this is
the genuine full-source signed interaction inherited from OpenAI. It
is NOT a previously proved independent NNS covariance theorem.

**Cutoff audit (IMPORTANT).** At X=R^2-1 the *strict* historical
subroot convention uses c<R and p>=R, while the existing prime-sieve
source uses y=R (smooth p<=R, moving p>R). When R is itself prime,
p=R contributes M(R-1) to the raw prime response:

```
T_(p>=R) = T_(p>R) + 1_Prime(R)*M(R-1),
S_(P+<R) = S_(P+<=R) + 1_Prime(R)*M(R-1).
```

The difference stays M(X). For R=317 this singleton is -3;
for R=1027 (composite) it is 0. All theorem names and finite
measurements below use the explicit y=R convention; do not identify
the sequential all-plus animation with S_R.

## II. Apply the COMPLETE OAI integer/ideal-norm coefficient dictionary

Write chi(d)=chi_-3(d), let a_F(n) denote the complete norm-grouped
coefficient of 1/zeta_{Q(sqrt(-3))}, and let
a_6(n)=1_(gcd(n,6)=1)*a_F(n).

Already proved in
research/VF_MID_919_OAI_PRINCIPAL_COEFFICIENT_MAP.lean:

```
mu_Z = chi * a_F
```

in Dirichlet convolution, including inert prime squares, split
conjugate prime ideals and ramified 3. In particular a_F=mu_Z*(chi*mu_Z)
is a constructed arithmetic function; identifying it with the
upstream actual ideal-fiber coefficient must retain the ORIGINAL ideal
labels and phases.

Apply the EXISTING, kernel-proved restoration theorem
vf919WeightedMobius_eq_excludedNormKernel with w(c)=w_R(c). We obtain
for every R>=4 the exact physical source equality

```
T_R =
 sum_(m<=X) a_6(m) *
   sum_(d<=X) chi(d) *
      [w_R(md)-w_R(3md)-w_R(4md)+w_R(12md)].
```

All four terms in the bracket are required. They restore excluded
rational primes 2,3 and their interactions, rather than discarding
squareful zero, nonunit and ramified sources. The physical sharp cutoff
is evaluated at EACH actual product md,3md,4md,12md, not at the ideal
norm of one arbitrarily selected decomposition. The source label c<R
survives: w_R(c)=0 for c>=R. This is the correct exact fixed-cofactor
response map for a potential OAI moment attack.

**Lean acceptance file:**
[research/VF_919_FROZEN_COFACTOR_OAI_NNS_RESPONSE_20261023.lean](VF_919_FROZEN_COFACTOR_OAI_NNS_RESPONSE_20261023.lean)

It composes the restored norm-kernel theorem with the genuinely
moving p>R response and separately compiles the true smooth/transport
signed NNS Gram; neither identity is replaced by an OAI claim.

## III. The exact OpenAI moment interface and its FIRST failed hypothesis

Pinned external OpenAI source:
`openai/math@1581d4cbdd69a0faf34b2089614fe2a814316a6a`,
`preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex`.

Its actual marked inverse moment (Part II, around lines 9209-9282)
uses disjoint auxiliary prime supports at scales Z^z_i, with total
z=sum_i z_i. The stated sufficient hypotheses include

```
  r+2*z <= m-c1,
  2*r+8*z <= 3*m-c2,    c1,c2>0,
```

for a normalized inverse column length Z^r and row ball U=Z^m.
The intermediate physical detector rows of the 7/8 argument have
m<=h+zeta<5/6, h=13/16 and 0<zeta<1/48.

If one labels the ACTUAL post-root prime p>R as an OAI marked
slot with scale Z=X=R^2-1, then z=log_X(p)>1/2.
For every r>=0, even the first requirement fails:

```
r+2*z >= 1 > 5/6 >= m.
```

The second fails even more sharply:
```
2*r+8*z >= 4 > 3*m.
```

This is a **quantified source-scale obstruction**. The original
OAI marked moment does NOT directly pay T_R merely because its
signed rational coefficients can be represented through Hecke norm
coefficients. Choosing smaller auxiliary prime slots and ignoring the
long physical p is invalid; the actual physical p and all its masks
must remain elsewhere in the same original coefficient.

The published OAI K slots have total length 1/6, and they are
AUXILIARY compensating primes, not an identification of a physical
post-root factor p whose exponent is >=1/2. OpenAI's full mechanism
does pay its own character-row source with separate low, principal,
nonprincipal and moment estimates; those estimates do not provide
this new source transport automatically.

Two Lean theorems certify BOTH marked inequalities fail for all
r>=0, z>=1/2, m<=5/6 and positive margins. Neither assumes
RH, covariance decay or an OAI moment conclusion.

## IV. The remaining independent mathematical arrow

The newly explicit candidate is NOT an arbitrary global covariance
assertion. Construct and bound a compensated, height-integrated
row source whose **principal physical coefficient** is precisely
the above full restored (a_6,chi) prime-response kernel, and whose
nonprincipal coefficients retain every `p>R` sharp mask, split/inert
norm, ramified 3, c<R and original Fourier phase. Auxiliary short
OAI slots may be introduced but cannot replace the p>R factor.

To improve 7/8 by kappa>0 one would need a truly independently proved
retained-source estimate implying, after complete root-smooth and
response recombination,

```
|S_R-T_R| = O_eps(R^(7/4-2*kappa+eps)),
```

uniformly for all R, with the separate nonsquare interpolation and
classical zero-strip consumers. An estimate on T_R alone without S_R,
or on a nonprincipal average while discarding the principal row,
does not qualify.

Next falsifiable step: test the actual frozen physical kernel against
the correct original Gaussian/Hecke row incidence *before* trying
marked moments. If it is not an admitted member of the original
moment family, state the first failed mask, valuation, degree or
scale hypothesis and seek a distinct Type-II/reflected mixed estimate.
No more direct p-as-marked-slot transfers.

## V. Reproducible integer acceptance

The exact checker
[scripts/vf919_frozen_cofactor_response_audit.py](../scripts/vf919_frozen_cofactor_response_audit.py)
independently reconstructs physical prime and Mobius sieves,
w_R(c), the nonexcluded and excluded a_F sources, all 3/4/12
restoring terms, smooth/high NNS populations, full mixed Co-Div,
and strict p=R boundary corrections. Predeclared roots include
all R=4,...,70 and 97,101,317,1027.

For the fixed y=R cutoff:

| R | S_R | T_R | M(R^2-1) |
|---:|---:|---:|---:|
| 317 | -915 | -887 | -28 |
| 1027 | -6602 | -6969 | +367 |

For the strict historical p>=R cutoff, R=317 becomes
S=-918, T=-890, M=-28.

Previous -20940/-20912 and -178151/-178518 were values of the
sequential prime-comb running state and its post-root animation
increment, NOT these finished physical signed smooth/response
populations. Mixing them invalidates the sample covariance.

**Acceptance:** warning-fatal Lean 4.34.1, eight standard-only axiom
footprints, exact integer audit, human-only merge. No new analytic
estimate or RH proof is claimed.
